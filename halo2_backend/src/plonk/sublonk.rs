//! Generate a sublonk

use std::collections::HashMap;
use std::iter;

use group::Curve;
use group::prime::PrimeCurveAffine;
use rand_core::RngCore;

use halo2_middleware::ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_middleware::zal::{
    impls::PlonkEngine,
    traits::MsmAccel,
};

use crate::arithmetic::{CurveAffine, eval_polynomial};
use crate::plonk::{ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error, lookup, permutation, ProvingKey, shuffle, vanishing};
use crate::plonk::lookup::prover::lookup_commit_permuted;
use crate::plonk::permutation::prover::permutation_commit;
use crate::plonk::prover::{AdviceSingle, InstanceSingle, Prover};
use crate::plonk::shuffle::prover::shuffle_commit_product;
use crate::poly::{Coeff, commitment::{self, Blind, CommitmentScheme, Params}, LagrangeCoeff, Polynomial, ProverQuery};
use crate::transcript::{EncodedChallenge, TranscriptWrite};

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
        rng: R,
        transcript: &'a mut T,
    ) -> Result<Self, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        // For each circuit, check if the number of instances is equal to the required number
        // of instances in verification key.
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
            |instance: &[&[Scheme::Scalar]]| -> Result<crate::plonk::prover::InstanceSingle<Scheme::Curve>, Error> {
                // Create a lagrange polynomial for each instance column

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
                            // Query instance or not, if not, add to transcript.
                            // For KZG commitment schemes (GWC and SHPLONK), it is false.
                            // if !P::QUERY_INSTANCE {
                            //     // Add to the transcript the instance polynomials lagrange value.
                            //     transcript.common_scalar(*value)?;
                            // }
                            transcript.common_scalar(*value)?;
                            *poly = *value;
                        }
                        Ok(poly)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                // if P::QUERY_INSTANCE {
                //     // Add to the transcript the commitments of the instance lagrange polynomials
                // 
                //     let instance_commitments_projective: Vec<_> = instance_values
                //         .iter()
                //         .map(|poly| {
                //             params.commit_lagrange(&engine.msm_backend, poly, Blind::default())
                //         })
                //         .collect();
                //     let mut instance_commitments =
                //         vec![Scheme::Curve::identity(); instance_commitments_projective.len()];
                //     <Scheme::Curve as CurveAffine>::CurveExt::batch_normalize(
                //         &instance_commitments_projective,
                //         &mut instance_commitments,
                //     );
                //     let instance_commitments = instance_commitments;
                //     drop(instance_commitments_projective);
                // 
                //     for commitment in &instance_commitments {
                //         transcript.common_point(*commitment)?;
                //     }
                // }

                // Convert from evaluation to coefficient form.

                let instance_polys: Vec<_> = instance_values
                    .iter()
                    .map(|poly| {
                        let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                        domain.lagrange_to_coeff(lagrange_vec)
                    })
                    .collect();

                Ok(crate::plonk::prover::InstanceSingle {
                    instance_values,
                    instance_polys,
                })
            };

        // Commit the polynomials of all circuits instances
        // [TRANSCRIPT-2]

        let instances: Vec<crate::plonk::prover::InstanceSingle<Scheme::Curve>> = circuits_instances
            .iter()
            .map(|instance| commit_instance_fn(instance))
            .collect::<Result<Vec<_>, _>>()?;

        // Create an structure to hold the advice polynomials and its blinds, it will be filled later in the
        // [`commit_phase`].

        let advices = vec![
            crate::plonk::prover::AdviceSingle::<Scheme::Curve, LagrangeCoeff> {
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