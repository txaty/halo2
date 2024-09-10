use std::iter;
use crate::arithmetic::{parallelize, CurveAffine};
use crate::plonk::permutation::keygen::Assembly;
use crate::plonk::permutation::verifier::{Committed, CommonEvaluated, Evaluated};
use crate::plonk::permutation::{Argument, ProvingKey, VerifyingKey};
use crate::plonk::{ChallengeBeta, ChallengeGamma, ChallengeX, Error};
use crate::poly::commitment::{Blind, Params, MSM};
use crate::poly::{EvaluationDomain, VerifierQuery};
use crate::transcript::{EncodedChallenge, TranscriptRead};
use ff::{Field, PrimeField};
use group::Curve;
use halo2_middleware::circuit::Any;
use halo2_middleware::poly::Rotation;
use halo2_middleware::zal::impls::H2cEngine;
use crate::plonk::sublonk::SublonkVerifyingKey;

impl Assembly {
    pub(crate) fn sublonk_build_vk<C: CurveAffine, P: Params<C>>(
        self,
        params: &P,
        domain: &EvaluationDomain<C::Scalar>,
        p: &Argument,
    ) -> VerifyingKey<C> {
        sublonk_build_vk(params, domain, p, |i, j| self.mapping[i][j])
    }

    pub(crate) fn sublonk_build_pk<C: CurveAffine, P: Params<C>>(
        self,
        params: &P,
        domain: &EvaluationDomain<C::Scalar>,
        p: &Argument,
    ) -> ProvingKey<C> {
        sublonk_build_pk(params, domain, p, |i, j| self.mapping[i][j])
    }
}

pub(crate) fn sublonk_build_pk<C: CurveAffine, P: Params<C>>(
    params: &P,
    domain: &EvaluationDomain<C::Scalar>,
    p: &Argument,
    mapping: impl Fn(usize, usize) -> (usize, usize) + Sync,
) -> ProvingKey<C> {
    // Compute [omega^0, omega^1, ..., omega^{params.n - 1}]
    let mut omega_powers = vec![C::Scalar::ZERO; params.n() as usize];
    {
        let omega = domain.get_omega();
        parallelize(&mut omega_powers, |o, start| {
            let mut cur = omega.pow_vartime([start as u64]);
            for v in o.iter_mut() {
                *v = cur;
                cur *= &omega;
            }
        })
    }

    // Compute [omega_powers * \delta^0, omega_powers * \delta^1, ..., omega_powers * \delta^m]
    let mut deltaomega = vec![omega_powers; p.columns.len()];
    {
        parallelize(&mut deltaomega, |o, start| {
            let mut cur = C::Scalar::DELTA.pow_vartime([start as u64]);
            for omega_powers in o.iter_mut() {
                for v in omega_powers {
                    *v *= &cur;
                }
                cur *= &C::Scalar::DELTA;
            }
        });
    }

    // Compute permutation polynomials, convert to coset form.
    let mut permutations = vec![domain.empty_lagrange(); p.columns.len()];
    {
        parallelize(&mut permutations, |o, start| {
            for (x, permutation_poly) in o.iter_mut().enumerate() {
                let i = start + x;
                for (j, p) in permutation_poly.iter_mut().enumerate() {
                    let (permuted_i, permuted_j) = mapping(i, j);
                    *p = deltaomega[permuted_i][permuted_j];
                }
            }
        });
    }

    let mut polys = vec![domain.empty_coeff(); p.columns.len()];
    {
        parallelize(&mut polys, |o, start| {
            for (x, poly) in o.iter_mut().enumerate() {
                let i = start + x;
                let permutation_poly = permutations[i].clone();
                *poly = domain.lagrange_to_coeff(permutation_poly);
            }
        });
    }

    let mut cosets = vec![domain.empty_extended(); p.columns.len()];
    {
        parallelize(&mut cosets, |o, start| {
            for (x, coset) in o.iter_mut().enumerate() {
                let i = start + x;
                let poly = polys[i].clone();
                *coset = domain.coeff_to_extended(poly);
            }
        });
    }

    ProvingKey {
        permutations,
        polys,
        cosets,
    }
}

pub(crate) fn sublonk_build_vk<C: CurveAffine, P: Params<C>>(
    params: &P,
    domain: &EvaluationDomain<C::Scalar>,
    p: &Argument,
    mapping: impl Fn(usize, usize) -> (usize, usize) + Sync,
) -> VerifyingKey<C> {
    // Compute [omega^0, omega^1, ..., omega^{params.n - 1}]
    let mut omega_powers = vec![C::Scalar::ZERO; params.n() as usize];
    {
        let omega = domain.get_omega();
        parallelize(&mut omega_powers, |o, start| {
            let mut cur = omega.pow_vartime([start as u64]);
            for v in o.iter_mut() {
                *v = cur;
                cur *= &omega;
            }
        })
    }

    // Compute [omega_powers * \delta^0, omega_powers * \delta^1, ..., omega_powers * \delta^m]
    let mut deltaomega = vec![omega_powers; p.columns.len()];
    {
        parallelize(&mut deltaomega, |o, start| {
            let mut cur = C::Scalar::DELTA.pow_vartime([start as u64]);
            for omega_powers in o.iter_mut() {
                for v in omega_powers {
                    *v *= &cur;
                }
                cur *= &<C::Scalar as PrimeField>::DELTA;
            }
        });
    }

    // Computes the permutation polynomial based on the permutation
    // description in the assembly.
    let mut permutations = vec![domain.empty_lagrange(); p.columns.len()];
    {
        parallelize(&mut permutations, |o, start| {
            for (x, permutation_poly) in o.iter_mut().enumerate() {
                let i = start + x;
                for (j, p) in permutation_poly.iter_mut().enumerate() {
                    let (permuted_i, permuted_j) = mapping(i, j);
                    *p = deltaomega[permuted_i][permuted_j];
                }
            }
        });
    }

    // for permutation in &permutations {
    //     println!("permutation: {:?}", permutation.values);
    // }
    // println!("no. permutations: {}", permutations.len());

    // Pre-compute commitments for the URS.
    let commitments = {
        let mut commitments_projective = Vec::with_capacity(p.columns.len());
        for permutation in &permutations {
            // Compute commitment to permutation polynomial
            commitments_projective.push(params.commit_lagrange(
                &H2cEngine::new(),
                permutation,
                Blind::default(),
            ));
        }
        let mut commitments = vec![C::identity(); p.columns.len()];
        C::CurveExt::batch_normalize(&commitments_projective, &mut commitments);
        commitments
    };

    VerifyingKey { commitments }
}

pub(crate) fn build_permutation_poly_coeffs<C: CurveAffine, P: Params<C>>(
    params: &P,
    domain: &EvaluationDomain<C::Scalar>,
    p: &Argument,
    mapping: impl Fn(usize, usize) -> (usize, usize) + Sync,
) -> Vec<Vec<C::Scalar>> {
    // Compute [omega^0, omega^1, ..., omega^{params.n - 1}]
    let mut omega_powers = vec![C::Scalar::ZERO; params.n() as usize];
    {
        let omega = domain.get_omega();
        parallelize(&mut omega_powers, |o, start| {
            let mut cur = omega.pow_vartime([start as u64]);
            for v in o.iter_mut() {
                *v = cur;
                cur *= &omega;
            }
        })
    }

    // Compute [omega_powers * \delta^0, omega_powers * \delta^1, ..., omega_powers * \delta^m]
    let mut deltaomega = vec![omega_powers; p.columns.len()];
    {
        parallelize(&mut deltaomega, |o, start| {
            let mut cur = C::Scalar::DELTA.pow_vartime([start as u64]);
            for omega_powers in o.iter_mut() {
                for v in omega_powers {
                    *v *= &cur;
                }
                cur *= &<C::Scalar as PrimeField>::DELTA;
            }
        });
    }

    // Computes the permutation polynomial based on the permutation
    // description in the assembly.
    let mut permutations = vec![domain.empty_lagrange(); p.columns.len()];
    {
        parallelize(&mut permutations, |o, start| {
            for (x, permutation_poly) in o.iter_mut().enumerate() {
                let i = start + x;
                for (j, p) in permutation_poly.iter_mut().enumerate() {
                    let (permuted_i, permuted_j) = mapping(i, j);
                    *p = deltaomega[permuted_i][permuted_j];
                }
            }
        });
    }

    // for permutation in &permutations {
    //     println!("permutation: {:?}", permutation.values);
    // }
    // println!("no. permutations: {}", permutations.len());

    let permutation_poly_coeffs = permutations
        .iter()
        .map(|permutation| permutation.values.clone())
        .collect();

    permutation_poly_coeffs
}

pub(crate) fn permutation_read_product_commitments<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptRead<C, E>,
>(
    arg: &Argument,
    // vk: &plonk::VerifyingKey<C>,
    cs_degree: usize,
    transcript: &mut T,
) -> Result<Committed<C>, Error> {
    let chunk_len = cs_degree - 2;

    let permutation_product_commitments = arg
        .columns
        .chunks(chunk_len)
        .map(|_| transcript.read_point())
        .collect::<Result<Vec<_>, _>>()?;

    Ok(Committed {
        permutation_product_commitments,
    })
}

pub(in crate::plonk) fn evaluate_permutation_commitments<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptRead<C, E>,
>(
    // &self,
    permutation_commitments: &[C],
    transcript: &mut T,
) -> Result<CommonEvaluated<C>, Error> {
    let permutation_evals = permutation_commitments
        .iter()
        .map(|_| transcript.read_scalar())
        .collect::<Result<Vec<_>, _>>()?;

    Ok(CommonEvaluated { permutation_evals })
}

impl<C: CurveAffine> Evaluated<C> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn sublonk_expressions<'a>(
        &'a self,
        // vk: &'a plonk::VerifyingKey<C>,
        sublonk_vk: &'a SublonkVerifyingKey<C>,
        p: &'a Argument,
        common: &'a CommonEvaluated<C>,
        advice_evals: &'a [C::Scalar],
        fixed_evals: &'a [C::Scalar],
        instance_evals: &'a [C::Scalar],
        l_0: C::Scalar,
        l_last: C::Scalar,
        l_blind: C::Scalar,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item=C::Scalar> + 'a {
        let chunk_len = sublonk_vk.cs_degree - 2;
        iter::empty()
            // Enforce only for the first set.
            // l_0(X) * (1 - z_0(X)) = 0
            .chain(
                self.sets
                    .first()
                    .map(|first_set| l_0 * (C::Scalar::ONE - first_set.permutation_product_eval)),
            )
            // Enforce only for the last set.
            // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
            .chain(self.sets.last().map(|last_set| {
                (last_set.permutation_product_eval.square() - last_set.permutation_product_eval)
                    * l_last
            }))
            // Except for the first set, enforce.
            // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
            .chain(
                self.sets
                    .iter()
                    .skip(1)
                    .zip(self.sets.iter())
                    .map(|(set, last_set)| {
                        (
                            set.permutation_product_eval,
                            last_set.permutation_product_last_eval.unwrap(),
                        )
                    })
                    .map(move |(set, prev_last)| (set - prev_last) * l_0),
            )
            // And for all the sets we enforce:
            // (1 - (l_last(X) + l_blind(X))) * (
            //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
            // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
            // )
            .chain(
                self.sets
                    .iter()
                    .zip(p.columns.chunks(chunk_len))
                    .zip(common.permutation_evals.chunks(chunk_len))
                    .enumerate()
                    .map(move |(chunk_index, ((set, columns), permutation_evals))| {
                        let mut left = set.permutation_product_next_eval;
                        for (eval, permutation_eval) in columns
                            .iter()
                            .map(|&column| match column.column_type {
                                Any::Advice => {
                                    advice_evals[sublonk_vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                                Any::Fixed => {
                                    fixed_evals[sublonk_vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                                Any::Instance => {
                                    instance_evals
                                        [sublonk_vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                            })
                            .zip(permutation_evals.iter())
                        {
                            left *= eval + (*beta * permutation_eval) + *gamma;
                        }

                        let mut right = set.permutation_product_eval;
                        let mut current_delta = (*beta * *x)
                            * (<C::Scalar as PrimeField>::DELTA
                            .pow_vartime([(chunk_index * chunk_len) as u64]));
                        for eval in columns.iter().map(|&column| match column.column_type {
                            Any::Advice => {
                                advice_evals[sublonk_vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Fixed => {
                                fixed_evals[sublonk_vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Instance => {
                                instance_evals[sublonk_vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                        }) {
                            right *= eval + current_delta + *gamma;
                            current_delta *= &C::Scalar::DELTA;
                        }

                        (left - right) * (C::Scalar::ONE - (l_last + l_blind))
                    }),
            )
    }

    pub(in crate::plonk) fn sublonk_queries<'r, M: MSM<C> + 'r>(
        &'r self,
        vk: &'r SublonkVerifyingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let blinding_factors = vk.cs.blinding_factors();
        let x_next = vk.domain.rotate_omega(*x, Rotation::next());
        let x_last = vk
            .domain
            .rotate_omega(*x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(self.sets.iter().flat_map(move |set| {
                iter::empty()
                    // Open permutation product commitments at x and \omega^{-1} x
                    // Open permutation product commitments at x and \omega x
                    .chain(Some(VerifierQuery::new_commitment(
                        &set.permutation_product_commitment,
                        *x,
                        set.permutation_product_eval,
                    )))
                    .chain(Some(VerifierQuery::new_commitment(
                        &set.permutation_product_commitment,
                        x_next,
                        set.permutation_product_next_eval,
                    )))
            }))
            // Open it at \omega^{last} x for all but the last set
            .chain(self.sets.iter().rev().skip(1).flat_map(move |set| {
                Some(VerifierQuery::new_commitment(
                    &set.permutation_product_commitment,
                    x_last,
                    set.permutation_product_last_eval.unwrap(),
                ))
            }))
    }
}


impl<C: CurveAffine> CommonEvaluated<C> {
    pub(in crate::plonk) fn sublonk_queries<'r, M: MSM<C> + 'r>(
        &'r self,
        permutation_commitments: &'r [C],
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        // Open permutation commitments for each permutation argument at x
        permutation_commitments
            .iter()
            .zip(self.permutation_evals.iter())
            .map(move |(commitment, &eval)| VerifierQuery::new_commitment(commitment, *x, eval))
    }
}
