use crate::arithmetic::{parallelize, CurveAffine};
use crate::plonk::permutation::Argument;
use crate::poly::commitment::Params;
use crate::poly::EvaluationDomain;
use ff::{Field, PrimeField};

pub(crate) fn build_permutation_poly_coeff_list<C: CurveAffine, P: Params<C>>(
    params: &P,
    domain: &EvaluationDomain<C::Scalar>,
    omega: C::Scalar,
    p: &Argument,
    mapping: impl Fn(usize, usize) -> (usize, usize) + Sync,
) -> Vec<Vec<C::Scalar>> {
    // Compute [omega^0, omega^1, ..., omega^{params.n - 1}]
    let mut generator_pow_list = vec![C::Scalar::ZERO; params.n() as usize];
    {
        // let omega = domain.get_omega();
        parallelize(&mut generator_pow_list, |o, start| {
            let mut cur = omega.pow_vartime([start as u64]);
            for v in o.iter_mut() {
                *v = cur;
                cur *= &omega;
            }
        })
    }

    // Compute [omega_powers * \delta^0, omega_powers * \delta^1, ..., omega_powers * \delta^m]
    let mut deltaomega = vec![generator_pow_list; p.columns.len()];
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

