//! Generate a sublonk

use std::collections::HashMap;
use std::iter;

use group::prime::PrimeCurveAffine;
use group::Curve;
use rand_core::RngCore;

use crate::arithmetic::{compute_inner_product, eval_polynomial, parallelize, CurveAffine};
use crate::plonk::circuit::{ConstraintSystemBack, VarBack};
use crate::plonk::lookup::prover::lookup_commit_permuted;
use crate::plonk::lookup::verifier::lookup_read_permuted_commitments;
use crate::plonk::permutation::prover::permutation_commit;
use crate::plonk::permutation::sublonk::permutation_read_product_commitments;
use crate::plonk::permutation::sublonk::{
    build_permutation_poly_coeffs, evaluate_permutation_commitments,
};
use crate::plonk::permutation::VerifyingKey as PermutationVerifyingKey;
use crate::plonk::prover::{AdviceSingle, InstanceSingle, Prover};
use crate::plonk::shuffle::prover::shuffle_commit_product;
use crate::plonk::shuffle::verifier::shuffle_read_product_commitment;
use crate::plonk::{
    lookup, permutation, shuffle, vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta,
    ChallengeX, ChallengeY, Error, Evaluator, ProvingKey, VerifyingKey,
};
use crate::poly::commitment::{ParamsProver, ParamsVerifier, Verifier};
use crate::poly::{
    commitment::{self, Blind, CommitmentScheme, Params},
    Coeff, EvaluationDomain, LagrangeCoeff, Polynomial, ProverQuery, VerificationStrategy,
    VerifierQuery,
};
use crate::transcript::{read_n_scalars, EncodedChallenge, TranscriptRead, TranscriptWrite};
use halo2_middleware::circuit::{Any, CompiledCircuit};
use halo2_middleware::ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_middleware::zal::impls::H2cEngine;
use halo2_middleware::zal::{impls::PlonkEngine, traits::MsmAccel};

pub fn commit_instances<'a, 'params, Scheme: CommitmentScheme, M: MsmAccel<Scheme::Curve>>(
    engine: PlonkEngine<Scheme::Curve, M>,
    params: &'params Scheme::ParamsProver,
    pk: &'a ProvingKey<Scheme::Curve>,
    circuit_instances: &[&[&[Scheme::Scalar]]],
) -> Result<
    Vec<Vec<<<<Scheme as CommitmentScheme>::Curve as CurveAffine>::CurveExt as Curve>::AffineRepr>>,
    Error,
>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let domain = &pk.vk.domain;
    let meta = &pk.vk.cs;
    let instances: Vec<InstanceSingle<Scheme::Curve>> = circuit_instances
        .iter()
        .map(|instance| -> Result<InstanceSingle<Scheme::Curve>, Error> {
            let instance_values = instance
                .iter()
                .map(|values| {
                    let mut poly = domain.empty_lagrange();
                    assert_eq!(poly.len(), params.n() as usize);
                    // Ensure there is enough space in the polynomial for the instance values.
                    if values.len() > (poly.len() - (meta.blinding_factors() + 1)) {
                        return Err(Error::InstanceTooLarge);
                    }
                    for (poly, value) in poly.iter_mut().zip(values.iter()) {
                        *poly = *value;
                    }
                    Ok(poly)
                })
                .collect::<Result<Vec<_>, _>>()?;

            // Convert from evaluation to coefficient form.

            let instance_polys: Vec<_> = instance_values
                .iter()
                .map(|poly| {
                    let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                    domain.lagrange_to_coeff(lagrange_vec)
                })
                .collect();

            Ok(InstanceSingle {
                instance_values,
                instance_polys,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let instance_poly_commitments: Vec<Vec<_>> = instances
        .iter()
        .map(|instance| {
            let instance_polys = instance.instance_polys.clone();
            let poly_commitments: Vec<_> = instance_polys
                .iter()
                .map(|poly| {
                    let blind = Blind::default(); // unused, only for API compatibility
                    params.commit(&engine.msm_backend, poly, blind).to_affine()
                })
                .collect();

            poly_commitments
        })
        .collect();

    Ok(instance_poly_commitments)
}

impl<
        'a,
        'params,
        Scheme: CommitmentScheme,
        P: commitment::Prover<'params, Scheme>,
        E: EncodedChallenge<Scheme::Curve>,
        R: RngCore,
        T: TranscriptWrite<Scheme::Curve, E>,
        M: MsmAccel<Scheme::Curve>,
    > Prover<'a, 'params, Scheme, P, E, R, T, M>
{
    /// Create a new prover object
    pub fn new_with_engine_sublonk(
        engine: PlonkEngine<Scheme::Curve, M>,
        params: &'params Scheme::ParamsProver,
        pk: &'a ProvingKey<Scheme::Curve>,
        // TODO: If this was a vector the usage would be simpler.
        // https://github.com/privacy-scaling-explorations/halo2/issues/265
        circuits_instances: &[&[&[Scheme::Scalar]]],
        // circuit_instance_commitments: Vec<
        //     Vec<<<Scheme::Curve as CurveAffine>::CurveExt as Curve>::AffineRepr>,
        // >,
        rng: R,
        transcript: &'a mut T,
    ) -> Result<Self, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        for instance in circuits_instances.iter() {
            if instance.len() != pk.vk.cs.num_instance_columns {
                return Err(Error::InvalidInstances);
            }
        }

        // Hash verification key into transcript [TRANSCRIPT-1]
        pk.vk.hash_into(transcript)?;

        let meta = &pk.vk.cs;
        let phases = meta.phases().collect();

        let domain = &pk.vk.domain;

        // commit_instance_fn is a helper function to return the polynomials (and its commitments) of
        // instance columns while updating the transcript.
        let mut commit_instance_fn =
            |instance: &[&[Scheme::Scalar]]| -> Result<InstanceSingle<Scheme::Curve>, Error> {
                // Create a lagrange polynomial for each instance column

                let instance_values = instance
                    .iter()
                    .map(|values| {
                        let mut poly = domain.empty_lagrange();
                        assert_eq!(poly.len(), params.n() as usize);
                        if values.len() > (poly.len() - (meta.blinding_factors() + 1)) {
                            return Err(Error::InstanceTooLarge);
                        }
                        for (poly, value) in poly.iter_mut().zip(values.iter()) {
                            if !P::QUERY_INSTANCE {
                                // Add to the transcript the instance polynomials lagrange value.
                                transcript.common_scalar(*value)?;
                            }
                            *poly = *value;
                        }
                        Ok(poly)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                if P::QUERY_INSTANCE {
                    // Add to the transcript the commitments of the instance lagrange polynomials

                    let instance_commitments_projective: Vec<_> = instance_values
                        .iter()
                        .map(|poly| {
                            params.commit_lagrange(&engine.msm_backend, poly, Blind::default())
                        })
                        .collect();
                    let mut instance_commitments =
                        vec![Scheme::Curve::identity(); instance_commitments_projective.len()];
                    <Scheme::Curve as CurveAffine>::CurveExt::batch_normalize(
                        &instance_commitments_projective,
                        &mut instance_commitments,
                    );
                    let instance_commitments = instance_commitments;
                    drop(instance_commitments_projective);

                    for commitment in &instance_commitments {
                        transcript.common_point(*commitment)?;
                    }
                }

                // Convert from evaluation to coefficient form.

                let instance_polys: Vec<_> = instance_values
                    .iter()
                    .map(|poly| {
                        let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                        domain.lagrange_to_coeff(lagrange_vec)
                    })
                    .collect();

                Ok(InstanceSingle {
                    instance_values,
                    instance_polys,
                })
            };

        // Commit the polynomials of all circuits instances
        // [TRANSCRIPT-2]

        let instances: Vec<InstanceSingle<Scheme::Curve>> = circuits_instances
            .iter()
            .map(|instance| commit_instance_fn(instance))
            .collect::<Result<Vec<_>, _>>()?;

        // Create a structure to hold the advice polynomials and its blinds, it will be filled later in the
        // [`commit_phase`].

        let advices = vec![
            AdviceSingle::<Scheme::Curve, LagrangeCoeff> {
                // Create vectors with empty polynomials to free space while they are not being used
                advice_polys: vec![
                    Polynomial::new_empty(0, Scheme::Scalar::ZERO);
                    meta.num_advice_columns
                ],
                advice_blinds: vec![Blind::default(); meta.num_advice_columns],
            };
            circuits_instances.len()
        ];

        // Challenges will be also filled later in the [`commit_phase`].

        let challenges = HashMap::<usize, Scheme::Scalar>::with_capacity(meta.num_challenges);

        Ok(Prover {
            engine,
            params,
            pk,
            phases,
            instances,
            rng,
            transcript,
            advices,
            challenges,
            next_phase_index: 0,
            _marker: std::marker::PhantomData {},
        })
    }

    pub fn create_sublonk_proof(mut self) -> Result<(), Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let params = self.params;
        let cs = &self.pk.vk.cs;
        let pk = self.pk;
        let domain = &self.pk.vk.domain;

        let mut rng = self.rng;

        let instances = std::mem::take(&mut self.instances);
        let advices = std::mem::take(&mut self.advices);
        let mut challenges = self.challenges;

        assert_eq!(challenges.len(), cs.num_challenges);
        // Extract the challenges in order of their indices and collect them into a vector
        let challenges = (0..cs.num_challenges)
            .map(|index| challenges.remove(&index).unwrap())
            .collect::<Vec<_>>();

        // 1. Generate commited ( added to transcript ) lookup polys  ---------------------------------------

        // Sample theta challenge for keeping lookup columns linearly independent
        // [TRANSCRIPT-5]

        let theta: ChallengeTheta<_> = self.transcript.squeeze_challenge_scalar();
        // 2. Get permuted lookup polys
        // [TRANSCRIPT-6]

        let mut lookups_fn =
            |instance: &InstanceSingle<Scheme::Curve>,
             advice: &AdviceSingle<Scheme::Curve, LagrangeCoeff>|
             -> Result<Vec<lookup::prover::Permuted<Scheme::Curve>>, Error> {
                cs.lookups
                    .iter()
                    .map(|lookup| {
                        lookup_commit_permuted(
                            &self.engine,
                            lookup,
                            pk,
                            params,
                            domain,
                            theta,
                            &advice.advice_polys,
                            &pk.fixed_values,
                            &instance.instance_values,
                            &challenges,
                            &mut rng,
                            self.transcript,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            };
        let permuted_lookups: Vec<Vec<lookup::prover::Permuted<Scheme::Curve>>> = instances
            .iter()
            .zip(advices.iter())
            .map(|(instance, advice)| -> Result<Vec<_>, Error> {
                // Construct and commit to permuted values for each lookup
                lookups_fn(instance, advice)
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Sample beta challenge
        // [TRANSCRIPT-7]
        let beta: ChallengeBeta<_> = self.transcript.squeeze_challenge_scalar();

        // Sample gamma challenge
        // [TRANSCRIPT-8]
        let gamma: ChallengeGamma<_> = self.transcript.squeeze_challenge_scalar();

        // 2. Generate commited permutation polys  -----------------------------------------
        // [TRANSCRIPT-9]
        let permutations_commited: Vec<permutation::prover::Committed<Scheme::Curve>> = instances
            .iter()
            .zip(advices.iter())
            .map(|(instance, advice)| {
                permutation_commit(
                    &self.engine,
                    &cs.permutation,
                    params,
                    pk,
                    &pk.permutation,
                    &advice.advice_polys,
                    &pk.fixed_values,
                    &instance.instance_values,
                    beta,
                    gamma,
                    &mut rng,
                    self.transcript,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // 3. Generate commited lookup polys ----------------------------------------------------------

        // [TRANSCRIPT-10]
        let lookups_commited: Vec<Vec<lookup::prover::Committed<Scheme::Curve>>> = permuted_lookups
            .into_iter()
            .map(|lookups| -> Result<Vec<_>, _> {
                // Construct and commit to products for each lookup
                lookups
                    .into_iter()
                    .map(|lookup| {
                        lookup.commit_product(
                            &self.engine,
                            pk,
                            params,
                            beta,
                            gamma,
                            &mut rng,
                            self.transcript,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        // 4. Generate commited shuffle polys  -------------------------------------------------------

        // [TRANSCRIPT-11]
        let shuffles_commited: Vec<Vec<shuffle::prover::Committed<Scheme::Curve>>> = instances
            .iter()
            .zip(advices.iter())
            .map(|(instance, advice)| -> Result<Vec<_>, _> {
                // Compress expressions for each shuffle
                cs.shuffles
                    .iter()
                    .map(|shuffle| {
                        shuffle_commit_product(
                            &self.engine,
                            shuffle,
                            pk,
                            params,
                            domain,
                            theta,
                            gamma,
                            &advice.advice_polys,
                            &pk.fixed_values,
                            &instance.instance_values,
                            &challenges,
                            &mut rng,
                            self.transcript,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        // 5. Commit to the vanishing argument's random polynomial for blinding h(x_3) -------------------
        // [TRANSCRIPT-12]
        let vanishing = vanishing::Argument::commit(
            &self.engine.msm_backend,
            params,
            domain,
            &mut rng,
            self.transcript,
        )?;

        // 6. Generate the advice polys ------------------------------------------------------------------

        let advice: Vec<AdviceSingle<Scheme::Curve, Coeff>> = advices
            .into_iter()
            .map(
                |AdviceSingle {
                     advice_polys,
                     advice_blinds,
                 }| {
                    AdviceSingle {
                        advice_polys: advice_polys
                            .into_iter()
                            .map(|poly| domain.lagrange_to_coeff(poly))
                            .collect::<Vec<_>>(),
                        advice_blinds,
                    }
                },
            )
            .collect();

        // 7. Evaluate the h(X) polynomial -----------------------------------------------------------

        // Obtain challenge for keeping all separate gates linearly independent
        // [TRANSCRIPT-13]
        let y: ChallengeY<_> = self.transcript.squeeze_challenge_scalar();

        let h_poly = pk.ev.evaluate_h(
            pk,
            &advice
                .iter()
                .map(|a| a.advice_polys.as_slice())
                .collect::<Vec<_>>(),
            &instances
                .iter()
                .map(|i| i.instance_polys.as_slice())
                .collect::<Vec<_>>(),
            &challenges,
            *y,
            *beta,
            *gamma,
            *theta,
            &lookups_commited,
            &shuffles_commited,
            &permutations_commited,
        );

        // 8. Construct the vanishing argument's h(X) commitments --------------------------------------
        // [TRANSCRIPT-14]
        let vanishing = vanishing.construct(
            &self.engine,
            params,
            domain,
            h_poly,
            &mut rng,
            self.transcript,
        )?;

        // 9. Compute x  --------------------------------------------------------------------------------
        // [TRANSCRIPT-15]
        let x: ChallengeX<_> = self.transcript.squeeze_challenge_scalar();

        let x_pow_n = x.pow([params.n()]);

        // [TRANSCRIPT-16]
        if P::QUERY_INSTANCE {
            // Compute and hash instance evals for the circuit instance
            for instance in instances.iter() {
                // Evaluate polynomials at omega^i x
                let instance_evals: Vec<_> = cs
                    .instance_queries
                    .iter()
                    .map(|&(column, at)| {
                        eval_polynomial(
                            &instance.instance_polys[column.index],
                            domain.rotate_omega(*x, at),
                        )
                    })
                    .collect();

                // Hash each instance column evaluation
                for eval in instance_evals.iter() {
                    self.transcript.write_scalar(*eval)?;
                }
            }
        }

        // 10. Compute and hash advice evals for the circuit instance ------------------------------------
        // [TRANSCRIPT-17]
        for advice in advice.iter() {
            // Evaluate polynomials at omega^i x
            let advice_evals: Vec<_> = cs
                .advice_queries
                .iter()
                .map(|&(column, at)| {
                    eval_polynomial(
                        &advice.advice_polys[column.index],
                        domain.rotate_omega(*x, at),
                    )
                })
                .collect();

            // Hash each advice column evaluation
            for eval in advice_evals.iter() {
                self.transcript.write_scalar(*eval)?;
            }
        }

        // 11. Compute and hash fixed evals -----------------------------------------------------------
        let fixed_evals: Vec<_> = cs
            .fixed_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(&pk.fixed_polys[column.index], domain.rotate_omega(*x, at))
            })
            .collect();

        // Hash each fixed column evaluation
        // [TRANSCRIPT-18]
        for eval in fixed_evals.iter() {
            self.transcript.write_scalar(*eval)?;
        }

        // [TRANSCRIPT-19]
        let vanishing = vanishing.evaluate(x, x_pow_n, domain, self.transcript)?;

        // 12. Evaluate permutation, lookups and shuffles at x -----------------------------------

        // Evaluate common permutation data
        // [TRANSCRIPT-20]
        pk.permutation.evaluate(x, self.transcript)?;

        // Evaluate the permutations, if any, at omega^i x.
        // [TRANSCRIPT-21]
        let permutations_evaluated: Vec<permutation::prover::Evaluated<Scheme::Curve>> =
            permutations_commited
                .into_iter()
                .map(|permutation| -> Result<_, _> { permutation.evaluate(pk, x, self.transcript) })
                .collect::<Result<Vec<_>, _>>()?;

        // Evaluate the lookups, if any, at omega^i x.
        // [TRANSCRIPT-22]
        let lookups_evaluated: Vec<Vec<lookup::prover::Evaluated<Scheme::Curve>>> =
            lookups_commited
                .into_iter()
                .map(|lookups| -> Result<Vec<_>, _> {
                    lookups
                        .into_iter()
                        .map(|p| p.evaluate(pk, x, self.transcript))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;

        // Evaluate the shuffles, if any, at omega^i x.
        // [TRANSCRIPT-23]
        let shuffles_evaluated: Vec<Vec<shuffle::prover::Evaluated<Scheme::Curve>>> =
            shuffles_commited
                .into_iter()
                .map(|shuffles| -> Result<Vec<_>, _> {
                    shuffles
                        .into_iter()
                        .map(|p| p.evaluate(pk, x, self.transcript))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;

        // 13. Generate all queries ([`ProverQuery`]) that needs to be sent to prover  --------------------

        let queries = instances
            // group the instance, advice, permutation, lookups and shuffles
            .iter()
            .zip(advice.iter())
            .zip(permutations_evaluated.iter())
            .zip(lookups_evaluated.iter())
            .zip(shuffles_evaluated.iter())
            .flat_map(|((((instance, advice), permutation), lookups), shuffles)| {
                // Build a (an iterator) over a set of ProverQueries for each instance, advice, permutatiom, lookup and shuffle
                iter::empty()
                    // Instances
                    .chain(
                        P::QUERY_INSTANCE
                            .then_some(cs.instance_queries.iter().map(move |&(column, at)| {
                                ProverQuery {
                                    point: domain.rotate_omega(*x, at),
                                    poly: &instance.instance_polys[column.index],
                                    blind: Blind::default(),
                                }
                            }))
                            .into_iter()
                            .flatten(),
                    )
                    // Advices
                    .chain(
                        cs.advice_queries
                            .iter()
                            .map(move |&(column, at)| ProverQuery {
                                point: domain.rotate_omega(*x, at),
                                poly: &advice.advice_polys[column.index],
                                blind: advice.advice_blinds[column.index],
                            }),
                    )
                    // Permutations
                    .chain(permutation.open(pk, x))
                    // Lookups
                    .chain(lookups.iter().flat_map(move |p| p.open(pk, x)))
                    // Shuffles
                    .chain(shuffles.iter().flat_map(move |p| p.open(pk, x)))
            })
            // Queries to fixed columns
            .chain(cs.fixed_queries.iter().map(|&(column, at)| ProverQuery {
                point: domain.rotate_omega(*x, at),
                poly: &pk.fixed_polys[column.index],
                blind: Blind::default(),
            }))
            // Copy constraints
            .chain(pk.permutation.open(x))
            // We query the h(X) polynomial at x
            .chain(vanishing.open(x));

        // 14. Send the queries to the [`Prover`]  ------------------------------------------------
        let prover = P::new(params);
        prover
            .create_proof_with_engine(&self.engine.msm_backend, rng, self.transcript, queries)
            .map_err(|_| Error::ConstraintSystemFailure)?;

        Ok(())
    }
}

/// Returns a boolean indicating whether the sublonk proof is valid
pub fn sublonk_verify_proof<
    'params,
    Scheme: CommitmentScheme,
    V: Verifier<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    T: TranscriptRead<Scheme::Curve, E>,
    Strategy: VerificationStrategy<'params, Scheme, V>,
>(
    params: &'params Scheme::ParamsVerifier,
    sublonk_vk: &SublonkVerifyingKey<Scheme::Curve>,
    strategy: Strategy,
    instances: &[&[&[Scheme::Scalar]]],
    transcript: &mut T,
    fixed_lookup_statements: &[Scheme::Curve],
    permutation_lookup_statements: &[Scheme::Curve],
) -> Result<Strategy::Output, Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    // ZAL: Verification is (supposedly) cheap, hence we don't use an accelerator engine
    let default_engine = H2cEngine::new();

    // Check that instances matches the expected number of instance columns
    for instances in instances.iter() {
        if instances.len() != sublonk_vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    // Check that the Scheme parameters support commitment to instance
    // if it is required by the verifier.
    assert!(
        !V::QUERY_INSTANCE
            || <Scheme::ParamsVerifier as ParamsVerifier<Scheme::Curve>>::COMMIT_INSTANCE
    );

    // 1. Get the commitments of the instance polynomials. ----------------------------------------

    let instance_commitments = if V::QUERY_INSTANCE {
        let mut instance_commitments = Vec::with_capacity(instances.len());

        let instances_projective = instances
            .iter()
            .map(|instance| {
                instance
                    .iter()
                    .map(|instance| {
                        if instance.len()
                            > params.n() as usize - (sublonk_vk.cs.blinding_factors() + 1)
                        {
                            return Err(Error::InstanceTooLarge);
                        }
                        let mut poly = instance.to_vec();
                        poly.resize(params.n() as usize, Scheme::Scalar::ZERO);
                        let poly = sublonk_vk.domain.lagrange_from_vec(poly);

                        Ok(params.commit_lagrange(&default_engine, &poly, Blind::default()))
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;

        for instance_projective in instances_projective {
            let mut affines =
                vec![<Scheme as CommitmentScheme>::Curve::identity(); instance_projective.len()];
            <<Scheme as CommitmentScheme>::Curve as CurveAffine>::CurveExt::batch_normalize(
                &instance_projective,
                &mut affines,
            );
            instance_commitments.push(affines);
        }
        instance_commitments
    } else {
        vec![vec![]; instances.len()]
    };

    let num_proofs = instance_commitments.len();

    // 2. Add hash of verification key and instances into transcript. -----------------------------
    // [TRANSCRIPT-1]
    let vk_to_hash = VerifyingKey::from_parts(
      sublonk_vk.domain.clone(),
        fixed_lookup_statements.to_vec(),
        PermutationVerifyingKey {
            commitments: permutation_lookup_statements.to_vec(),
        },
        sublonk_vk.cs.clone(),
    );
    vk_to_hash.hash_into(transcript)?;

    // 3. Add instance commitments into the transcript. --------------------------------------------
    // [TRANSCRIPT-2]

    if V::QUERY_INSTANCE {
        for instance_commitments in instance_commitments.iter() {
            // Hash the instance (external) commitments into the transcript
            for commitment in instance_commitments {
                transcript.common_point(*commitment)?
            }
        }
    } else {
        for instance in instances.iter() {
            for instance in instance.iter() {
                for value in instance.iter() {
                    transcript.common_scalar(*value)?;
                }
            }
        }
    }

    // 3. Hash the prover's advice commitments into the transcript and squeeze challenges ---------

    let (advice_commitments, challenges) = {
        let mut advice_commitments =
            vec![vec![Scheme::Curve::default(); sublonk_vk.cs.num_advice_columns]; num_proofs];
        let mut challenges = vec![Scheme::Scalar::ZERO; sublonk_vk.cs.num_challenges];

        for current_phase in sublonk_vk.cs.phases() {
            // [TRANSCRIPT-3]
            for advice_commitments in advice_commitments.iter_mut() {
                for (phase, commitment) in sublonk_vk
                    .cs
                    .advice_column_phase
                    .iter()
                    .zip(advice_commitments.iter_mut())
                {
                    if current_phase == *phase {
                        *commitment = transcript.read_point()?;
                    }
                }
            }

            // [TRANSCRIPT-4]
            for (phase, challenge) in sublonk_vk
                .cs
                .challenge_phase
                .iter()
                .zip(challenges.iter_mut())
            {
                if current_phase == *phase {
                    *challenge = *transcript.squeeze_challenge_scalar::<()>();
                }
            }
        }

        (advice_commitments, challenges)
    };

    // 4. Sample theta challenge for keeping lookup columns linearly independent ------------------
    // [TRANSCRIPT-5]

    let theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    // 5. Read lookup permuted commitments
    // [TRANSCRIPT-6]

    let lookups_permuted = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            // Hash each lookup permuted commitment
            sublonk_vk
                .cs
                .lookups
                .iter()
                .map(|_argument| lookup_read_permuted_commitments(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // 6. Sample beta and gamma challenges --------------------------------------------------------

    // Sample beta challenge
    // [TRANSCRIPT-7]
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    // [TRANSCRIPT-8]
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    // 7. Read commitments for permutation, lookups, and shuffles ---------------------------------

    // [TRANSCRIPT-9]
    let permutations_committed = (0..num_proofs)
        .map(|_| {
            // Hash each permutation product commitment
            permutation_read_product_commitments(
                &sublonk_vk.cs.permutation,
                sublonk_vk.cs_degree,
                transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    // [TRANSCRIPT-10]
    let lookups_committed = lookups_permuted
        .into_iter()
        .map(|lookups| {
            // Hash each lookup product commitment
            lookups
                .into_iter()
                .map(|lookup| lookup.read_product_commitment(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // [TRANSCRIPT-11]
    let shuffles_committed = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            // Hash each shuffle product commitment
            sublonk_vk
                .cs
                .shuffles
                .iter()
                .map(|_argument| shuffle_read_product_commitment(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // 8. Read vanishing argument (before y) ------------------------------------------------------
    // [TRANSCRIPT-12]
    let vanishing = vanishing::Argument::read_commitments_before_y(transcript)?;

    // 9. Sample y challenge, which keeps the gates linearly independent. -------------------------
    // [TRANSCRIPT-13]
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    // 10. Read vanishing argument (after y) ------------------------------------------------------
    // [TRANSCRIPT-14]
    let vanishing = vanishing.read_commitments_after_y_by_domain(&sublonk_vk.domain, transcript)?;

    // 11. Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability. -----------------------------------------------------------
    // [TRANSCRIPT-15]
    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();

    // 12. Get the instance evaluations
    let instance_evals = if V::QUERY_INSTANCE {
        // [TRANSCRIPT-16]
        (0..num_proofs)
            .map(|_| -> Result<Vec<_>, _> {
                read_n_scalars(transcript, sublonk_vk.cs.instance_queries.len())
            })
            .collect::<Result<Vec<_>, _>>()?
    } else {
        let xn = x.pow([params.n()]);
        let (min_rotation, max_rotation) =
            sublonk_vk
                .cs
                .instance_queries
                .iter()
                .fold((0, 0), |(min, max), (_, rotation)| {
                    if rotation.0 < min {
                        (rotation.0, max)
                    } else if rotation.0 > max {
                        (min, rotation.0)
                    } else {
                        (min, max)
                    }
                });
        let max_instance_len = instances
            .iter()
            .flat_map(|instance| instance.iter().map(|instance| instance.len()))
            .max_by(Ord::cmp)
            .unwrap_or_default();
        let l_i_s = &sublonk_vk.domain.l_i_range(
            *x,
            xn,
            -max_rotation..max_instance_len as i32 + min_rotation.abs(),
        );
        instances
            .iter()
            .map(|instances| {
                sublonk_vk
                    .cs
                    .instance_queries
                    .iter()
                    .map(|(column, rotation)| {
                        let instances = instances[column.index];
                        let offset = (max_rotation - rotation.0) as usize;
                        compute_inner_product(instances, &l_i_s[offset..offset + instances.len()])
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };

    // [TRANSCRIPT-17]
    let advice_evals = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            read_n_scalars(transcript, sublonk_vk.cs.advice_queries.len())
        })
        .collect::<Result<Vec<_>, _>>()?;

    // [TRANSCRIPT-18]
    let fixed_evals = read_n_scalars(transcript, sublonk_vk.cs.fixed_queries.len())?;

    // [TRANSCRIPT-19]
    let vanishing = vanishing.evaluate_after_x(transcript)?;

    // [TRANSCRIPT-20]
    let permutations_common =
        evaluate_permutation_commitments(&permutation_lookup_statements, transcript)?;

    // [TRANSCRIPT-21]
    let permutations_evaluated = permutations_committed
        .into_iter()
        .map(|permutation| permutation.evaluate(transcript))
        .collect::<Result<Vec<_>, _>>()?;

    // [TRANSCRIPT-22]
    let lookups_evaluated = lookups_committed
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|lookup| lookup.evaluate(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // [TRANSCRIPT-23]
    let shuffles_evaluated = shuffles_committed
        .into_iter()
        .map(|shuffles| -> Result<Vec<_>, _> {
            shuffles
                .into_iter()
                .map(|shuffle| shuffle.evaluate(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // This check ensures the circuit is satisfied so long as the polynomial
    // commitments open to the correct values.
    let vanishing = {
        // x^n
        let xn = x.pow([params.n()]);

        let blinding_factors = sublonk_vk.cs.blinding_factors();
        let l_evals = sublonk_vk
            .domain
            .l_i_range(*x, xn, (-((blinding_factors + 1) as i32))..=0);
        assert_eq!(l_evals.len(), 2 + blinding_factors);
        let l_last = l_evals[0];
        let l_blind: Scheme::Scalar = l_evals[1..(1 + blinding_factors)]
            .iter()
            .fold(Scheme::Scalar::ZERO, |acc, eval| acc + eval);
        let l_0 = l_evals[1 + blinding_factors];

        // Compute the expected value of h(x)
        let expressions = advice_evals
            .iter()
            .zip(instance_evals.iter())
            .zip(permutations_evaluated.iter())
            .zip(lookups_evaluated.iter())
            .zip(shuffles_evaluated.iter())
            .flat_map(
                |((((advice_evals, instance_evals), permutation), lookups), shuffles)| {
                    let challenges = &challenges;
                    let fixed_evals = &fixed_evals;
                    std::iter::empty()
                        // Evaluate the circuit using the custom gates provided
                        .chain(sublonk_vk.cs.gates.iter().map(move |gate| {
                            gate.poly.evaluate(
                                &|scalar| scalar,
                                &|var| match var {
                                    VarBack::Query(query) => match query.column_type {
                                        Any::Fixed => fixed_evals[query.index],
                                        Any::Advice => advice_evals[query.index],
                                        Any::Instance => instance_evals[query.index],
                                    },
                                    VarBack::Challenge(challenge) => challenges[challenge.index],
                                },
                                &|a| -a,
                                &|a, b| a + b,
                                &|a, b| a * b,
                            )
                        }))
                        .chain(permutation.sublonk_expressions(
                            sublonk_vk,
                            &sublonk_vk.cs.permutation,
                            &permutations_common,
                            advice_evals,
                            fixed_evals,
                            instance_evals,
                            l_0,
                            l_last,
                            l_blind,
                            beta,
                            gamma,
                            x,
                        ))
                        .chain(lookups.iter().zip(sublonk_vk.cs.lookups.iter()).flat_map(
                            move |(p, argument)| {
                                p.expressions(
                                    l_0,
                                    l_last,
                                    l_blind,
                                    argument,
                                    theta,
                                    beta,
                                    gamma,
                                    advice_evals,
                                    fixed_evals,
                                    instance_evals,
                                    challenges,
                                )
                            },
                        ))
                        .chain(shuffles.iter().zip(sublonk_vk.cs.shuffles.iter()).flat_map(
                            move |(p, argument)| {
                                p.expressions(
                                    l_0,
                                    l_last,
                                    l_blind,
                                    argument,
                                    theta,
                                    gamma,
                                    advice_evals,
                                    fixed_evals,
                                    instance_evals,
                                    challenges,
                                )
                            },
                        ))
                },
            );

        vanishing.verify(params, expressions, y, xn)
    };

    #[rustfmt::skip]
    let queries = instance_commitments
        .iter()
        .zip(instance_evals.iter())
        .zip(advice_commitments.iter())
        .zip(advice_evals.iter())
        .zip(permutations_evaluated.iter())
        .zip(lookups_evaluated.iter())
        .zip(shuffles_evaluated.iter())
        .flat_map(|((((((instance_commitments, instance_evals), advice_commitments),advice_evals),permutation),lookups),shuffles)| {
                iter::empty()
                    .chain(
                        V::QUERY_INSTANCE
                            .then_some(sublonk_vk.cs.instance_queries.iter().enumerate().map(
                                move |(query_index, &(column, at))| {
                                    VerifierQuery::new_commitment(
                                        &instance_commitments[column.index],
                                        sublonk_vk.domain.rotate_omega(*x, at),
                                        instance_evals[query_index],
                                    )
                                },
                            ))
                            .into_iter()
                            .flatten(),
                    )
                    .chain(sublonk_vk.cs.advice_queries.iter().enumerate().map(
                        move |(query_index, &(column, at))| {
                            VerifierQuery::new_commitment(
                                &advice_commitments[column.index],
                                sublonk_vk.domain.rotate_omega(*x, at),
                                advice_evals[query_index],
                            )
                        },
                    ))
                    .chain(permutation.sublonk_queries(sublonk_vk, x))
                    .chain(lookups.iter().flat_map(move |p| p.queries_with_domain(&sublonk_vk.domain, x)))
                    .chain(shuffles.iter().flat_map(move |p| p.queries_with_domain(&sublonk_vk.domain, x))) 
            },
        )
        .chain(
            sublonk_vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                .map(|(query_index, &(column, at))| {
                    VerifierQuery::new_commitment(
                        &fixed_lookup_statements[column.index],
                        sublonk_vk.domain.rotate_omega(*x, at),
                        fixed_evals[query_index],
                    )
                }),
        )
        .chain(permutations_common.sublonk_queries(&permutation_lookup_statements, x))
        .chain(vanishing.queries(x));

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.

    let verifier = V::new();
    strategy.process(|msm| {
        verifier
            .verify_proof(transcript, queries, msm)
            .map_err(|_| Error::Opening)
    })
}

/// Generate a `VerifyingKey` from an instance of `CompiledCircuit`.
pub fn keygen_vk<C, P>(
    params: &P,
    circuit: &CompiledCircuit<C::Scalar>,
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
    C::Scalar: FromUniformBytes<64>,
{
    let cs_mid = &circuit.cs;
    let cs: ConstraintSystemBack<C::Scalar> = cs_mid.clone().into();
    let domain = EvaluationDomain::new(cs.degree() as u32, params.k());

    if (params.n() as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }
    
    // println!("cs mid {:?}", cs_mid);
    // println!("cs {:?}", cs);

    // println!("cs mid permutations: {:?}", cs_mid.permutation);
    // println!(
    //     "preprocessing permutations: {:?}",
    //     circuit.preprocessing.permutation
    // );

    let permutation_vk = permutation::keygen::Assembly::new_from_assembly_mid(
        params.n() as usize,
        &cs_mid.permutation,
        &circuit.preprocessing.permutation,
    )?
    .sublonk_build_vk(params, &domain, &cs.permutation);

    // println!("permutation_vk: {:?}", permutation_vk);

    // println!(
    //     "fixed column field elements list: {:?}",
    //     circuit.preprocessing.fixed
    // );

    // for (i, fixed) in circuit.preprocessing.fixed.iter().enumerate() {
    //     println!("keygen fixed column {}: {:?}", i, fixed);
    // }

    // println!("constraint system gates: {:?}", cs.gates);

    let fixed_commitments = {
        let fixed_commitments_projective: Vec<C::CurveExt> = circuit
            .preprocessing
            .fixed
            .iter()
            .map(|poly| {
                params.commit_lagrange(
                    &H2cEngine::new(),
                    &Polynomial::new_lagrange_from_vec(poly.clone()),
                    Blind::default(),
                )
            })
            .collect();
        let mut fixed_commitments = vec![C::identity(); fixed_commitments_projective.len()];
        C::CurveExt::batch_normalize(&fixed_commitments_projective, &mut fixed_commitments);
        fixed_commitments
    };

    Ok(VerifyingKey::from_parts(
        domain,
        fixed_commitments,
        permutation_vk,
        cs,
    ))
}

pub fn keygen_pk<C, P>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &CompiledCircuit<C::Scalar>,
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
{
    let cs = &circuit.cs;

    if (params.n() as usize) < vk.cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    // Compute fixeds

    let fixed_polys: Vec<_> = circuit
        .preprocessing
        .fixed
        .iter()
        .map(|poly| {
            vk.domain
                .lagrange_to_coeff(Polynomial::new_lagrange_from_vec(poly.clone()))
        })
        .collect();

    let fixed_cosets = fixed_polys
        .iter()
        .map(|poly| vk.domain.coeff_to_extended(poly.clone()))
        .collect();

    let fixed_values = circuit
        .preprocessing
        .fixed
        .clone()
        .into_iter()
        .map(Polynomial::new_lagrange_from_vec)
        .collect();

    // Compute l_0(X)
    // TODO: this can be done more efficiently
    // https://github.com/privacy-scaling-explorations/halo2/issues/269
    let mut l0 = vk.domain.empty_lagrange();
    l0[0] = C::Scalar::ONE;
    let l0 = vk.domain.lagrange_to_coeff(l0);
    let l0 = vk.domain.coeff_to_extended(l0);

    // Compute l_blind(X) which evaluates to 1 for each blinding factor row
    // and 0 otherwise over the domain.
    let mut l_blind = vk.domain.empty_lagrange();
    for evaluation in l_blind[..].iter_mut().rev().take(vk.cs.blinding_factors()) {
        *evaluation = C::Scalar::ONE;
    }
    let l_blind = vk.domain.lagrange_to_coeff(l_blind);
    let l_blind = vk.domain.coeff_to_extended(l_blind);

    // Compute l_last(X) which evaluates to 1 on the first inactive row (just
    // before the blinding factors) and 0 otherwise over the domain
    let mut l_last = vk.domain.empty_lagrange();
    l_last[params.n() as usize - vk.cs.blinding_factors() - 1] = C::Scalar::ONE;
    let l_last = vk.domain.lagrange_to_coeff(l_last);
    let l_last = vk.domain.coeff_to_extended(l_last);

    // Compute l_active_row(X)
    let one = C::Scalar::ONE;
    let mut l_active_row = vk.domain.empty_extended();
    parallelize(&mut l_active_row, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = i + start;
            *value = one - (l_last[idx] + l_blind[idx]);
        }
    });

    // Compute the optimized evaluation data structure
    let ev = Evaluator::new(&vk.cs);

    // Compute the permutation proving key
    let permutation_pk = permutation::keygen::Assembly::new_from_assembly_mid(
        params.n() as usize,
        &cs.permutation,
        &circuit.preprocessing.permutation,
    )?
    .build_pk(params, &vk.domain, &cs.permutation.clone());

    Ok(ProvingKey {
        vk,
        l0,
        l_last,
        l_active_row,
        fixed_values,
        fixed_polys,
        fixed_cosets,
        permutation: permutation_pk,
        ev,
    })
}

impl<C: CurveAffine> ProvingKey<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    pub fn get_sublonk_vk(&self) -> SublonkVerifyingKey<C> {
        let original_vk = &self.vk;

        SublonkVerifyingKey {
            domain: original_vk.domain.clone(),
            cs: original_vk.cs.clone(),
            cs_degree: original_vk.cs.degree(),
            transcript_repr: C::Scalar::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SublonkVerifyingKey<C: CurveAffine> {
    /// Evaluation domain
    pub(crate) domain: EvaluationDomain<C::Scalar>,
    /// Constraint system
    pub(crate) cs: ConstraintSystemBack<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    pub(crate) cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: C::Scalar,
}

pub fn preprocessing_polynomial_coefficients<C, P>(
    params: &P,
    circuit: &CompiledCircuit<C::Scalar>,
) -> Result<(Vec<Vec<C::Scalar>>, Vec<Vec<C::Scalar>>), Error>
where
    C: CurveAffine,
    P: Params<C>,
    C::Scalar: FromUniformBytes<64>,
{
    let cs_mid = &circuit.cs;
    let cs: ConstraintSystemBack<C::Scalar> = cs_mid.clone().into();
    let domain = EvaluationDomain::new(cs.degree() as u32, params.k());

    if (params.n() as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    let fixed_poly_coeffs = circuit.preprocessing.fixed.clone();

    let assembly = permutation::keygen::Assembly::new_from_assembly_mid(
        params.n() as usize,
        &cs_mid.permutation,
        &circuit.preprocessing.permutation,
    )?;

    let permutation_poly_coeffs =
        build_permutation_poly_coeffs(params, &domain, &cs.permutation, |i, j| {
            assembly.mapping[i][j]
        });

    // for (i, fixed) in fixed_poly_coeffs.iter().enumerate() {
    //     println!("preprocessing fixed column {}: {:?}", i, fixed);
    // }

    Ok((fixed_poly_coeffs, permutation_poly_coeffs))
}
