//! Generate a sublonk

use std::iter;

use group::prime::PrimeCurveAffine;
use group::Curve;

use crate::arithmetic::{compute_inner_product, CurveAffine};
use crate::plonk::circuit::VarBack;
use crate::plonk::lookup::verifier::lookup_read_permuted_commitments;
use crate::plonk::permutation::sublonk::evaluate_permutation_commitments;
use crate::plonk::permutation::sublonk::permutation_read_product_commitments;
use crate::plonk::permutation::VerifyingKey as PermutationVerifyingKey;
use crate::plonk::shuffle::verifier::shuffle_read_product_commitment;
use crate::plonk::sublonk_keygen::SublonkVerifyingKey;
use crate::plonk::{
    vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error,
    VerifyingKey,
};
use crate::poly::commitment::{ParamsProver, ParamsVerifier, Verifier};
use crate::poly::{
    commitment::{Blind, CommitmentScheme, Params},
    VerificationStrategy, VerifierQuery,
};
use crate::transcript::{read_n_scalars, EncodedChallenge, TranscriptRead};
use halo2_middleware::circuit::Any;
use halo2_middleware::ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_middleware::zal::impls::H2cEngine;
// pub fn commit_instances<'a, 'params, Scheme: CommitmentScheme, M: MsmAccel<Scheme::Curve>>(
//     engine: PlonkEngine<Scheme::Curve, M>,
//     params: &'params Scheme::ParamsProver,
//     pk: &'a ProvingKey<Scheme::Curve>,
//     circuit_instances: &[&[&[Scheme::Scalar]]],
// ) -> Result<
//     Vec<Vec<<<<Scheme as CommitmentScheme>::Curve as CurveAffine>::CurveExt as Curve>::AffineRepr>>,
//     Error,
// >
// where
//     Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
// {
//     let domain = &pk.vk.domain;
//     let meta = &pk.vk.cs;
//     let instances: Vec<InstanceSingle<Scheme::Curve>> = circuit_instances
//         .iter()
//         .map(|instance| -> Result<InstanceSingle<Scheme::Curve>, Error> {
//             let instance_values = instance
//                 .iter()
//                 .map(|values| {
//                     let mut poly = domain.empty_lagrange();
//                     assert_eq!(poly.len(), params.n() as usize);
//                     // Ensure there is enough space in the polynomial for the instance values.
//                     if values.len() > (poly.len() - (meta.blinding_factors() + 1)) {
//                         return Err(Error::InstanceTooLarge);
//                     }
//                     for (poly, value) in poly.iter_mut().zip(values.iter()) {
//                         *poly = *value;
//                     }
//                     Ok(poly)
//                 })
//                 .collect::<Result<Vec<_>, _>>()?;
//
//             // Convert from evaluation to coefficient form.
//
//             let instance_polys: Vec<_> = instance_values
//                 .iter()
//                 .map(|poly| {
//                     let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
//                     domain.lagrange_to_coeff(lagrange_vec)
//                 })
//                 .collect();
//
//             Ok(InstanceSingle {
//                 instance_values,
//                 instance_polys,
//             })
//         })
//         .collect::<Result<Vec<_>, _>>()?;
//
//     let instance_poly_commitments: Vec<Vec<_>> = instances
//         .iter()
//         .map(|instance| {
//             let instance_polys = instance.instance_polys.clone();
//             let poly_commitments: Vec<_> = instance_polys
//                 .iter()
//                 .map(|poly| {
//                     let blind = Blind::default(); // unused, only for API compatibility
//                     params.commit(&engine.msm_backend, poly, blind).to_affine()
//                 })
//                 .collect();
//
//             poly_commitments
//         })
//         .collect();
//
//     Ok(instance_poly_commitments)
// }

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
