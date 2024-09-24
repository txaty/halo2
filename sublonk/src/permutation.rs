use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain};
use ark_segmentlookup::kzg::Kzg;
use ark_std::Zero;
use std::ops::Sub;

pub(crate) fn create_permutation_proof<P: Pairing>(
    g1_affine_srs: &[P::G1Affine],
    domain_v: &Radix2EvaluationDomain<P::ScalarField>,
    poly_u: &DensePolynomial<P::ScalarField>,
    poly_permutation_padding: &DensePolynomial<P::ScalarField>,
    poly_eval_list_permutation: &[P::ScalarField],
    poly_eval_list_adjusted_permutation: &[P::ScalarField],
) -> P::G1 {
    let poly_coeff_list_permutation = domain_v.ifft(poly_eval_list_permutation);
    let poly_permutation = DensePolynomial::from_coefficients_vec(poly_coeff_list_permutation);
    let poly_coeff_list_adjusted_permutation = domain_v.ifft(poly_eval_list_adjusted_permutation);
    let poly_adjusted_permutation =
        DensePolynomial::from_coefficients_vec(poly_coeff_list_adjusted_permutation);
    let mut poly_quotient = &poly_permutation * poly_u;
    poly_quotient += poly_permutation_padding;
    poly_quotient -= &poly_adjusted_permutation;
    let (poly_quotient, remainder) = poly_quotient.divide_by_vanishing_poly(*domain_v).unwrap();
    assert!(remainder.is_zero());

    let g1_quotient = Kzg::<<P as Pairing>::G1>::commit(g1_affine_srs, &poly_quotient);

    g1_quotient
}

pub(crate) fn verify_permutation_proof<P: Pairing>(
    g2_affine_u: P::G2Affine,
    permutation_statement: P::G1Affine,
    padded_permutation_statement: P::G1Affine,
    g1_affine_permutation_padding: P::G1Affine,
    permutation_proof: P::G1,
    g2_vanishing_poly_v: P::G2Affine,
) {
    let left_pairing = P::pairing(permutation_statement, g2_affine_u);

    let g2_one = P::G2Affine::generator();

    let permutation_subtracted = padded_permutation_statement
        .into_group()
        .sub(g1_affine_permutation_padding);

    let right_pairing = P::multi_pairing(
        &[permutation_proof, permutation_subtracted],
        &[g2_vanishing_poly_v, g2_one],
    );

    assert_eq!(left_pairing, right_pairing);
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Bn254;
    use ark_ec::{CurveGroup, Group};
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
    use ark_std::{One, UniformRand};
    use rand_core::OsRng;
    use std::iter;
    use std::ops::Mul;

    type ScalarField = <Bn254 as Pairing>::ScalarField;
    type G1Affine = <Bn254 as Pairing>::G1Affine;
    type G2Affine = <Bn254 as Pairing>::G2Affine;
    type G1 = <Bn254 as Pairing>::G1;
    type G2 = <Bn254 as Pairing>::G2;

    #[test]
    fn test_permutation_proof() {
        let domain = Radix2EvaluationDomain::<ScalarField>::new(32).unwrap();
        let roots_of_unity: Vec<ScalarField> = domain.elements().collect();
        let poly_coeff_list_u = domain.ifft(&roots_of_unity);
        let poly_u = DensePolynomial::from_coefficients_vec(poly_coeff_list_u);
        let mut permutation_witness_values = (0..24)
            .map(|i| ScalarField::from(i as u64))
            .collect::<Vec<_>>();
        permutation_witness_values.extend([ScalarField::zero(); 8]);

        let permutation_padding = (0..8)
            .map(|i| ScalarField::from(24 + i))
            .collect::<Vec<_>>();
        let adjusted_permutation_values = (0..32)
            .map(|i| ScalarField::from(i as u64))
            .collect::<Vec<_>>();
        let mut adjusted_permutation_values = adjusted_permutation_values
            .iter()
            .zip(roots_of_unity)
            .map(|(v, r)| *v * r)
            .collect::<Vec<_>>();
        adjusted_permutation_values[24..32].copy_from_slice(&permutation_padding);

        let mut poly_eval_list_permutation_padding = vec![ScalarField::zero(); 32];
        poly_eval_list_permutation_padding[24..32].copy_from_slice(&permutation_padding);
        let poly_permutation_padding = DensePolynomial::from_coefficients_vec(
            domain.ifft(&poly_eval_list_permutation_padding),
        );

        let tau = ScalarField::rand(&mut OsRng);
        let powers_of_tau_scalars: Vec<ScalarField> =
            iter::successors(Some(ScalarField::one()), |p| Some(*p * tau))
                .take(33)
                .collect();
        let powers_of_tau_g1: Vec<G1Affine> = powers_of_tau_scalars
            .iter()
            .map(|s| G1::generator().mul(*s).into_affine())
            .collect();
        let powers_of_tau_g2: Vec<G2Affine> = powers_of_tau_scalars
            .iter()
            .map(|s| G2::generator().mul(*s).into_affine())
            .collect();

        let permutation_proof = create_permutation_proof::<Bn254>(
            &powers_of_tau_g1,
            &domain,
            &poly_u,
            &poly_permutation_padding,
            &permutation_witness_values,
            &adjusted_permutation_values,
        );

        let g2_u = Kzg::<G2>::commit(&powers_of_tau_g2, &poly_u).into_affine();
        let poly_permutation =
            DensePolynomial::from_coefficients_vec(domain.ifft(&permutation_witness_values));
        let permutation_statement =
            Kzg::<G1>::commit(&powers_of_tau_g1, &poly_permutation).into_affine();
        let poly_adjusted_permutation =
            DensePolynomial::from_coefficients_vec(domain.ifft(&adjusted_permutation_values));
        let adjusted_permutation_statement =
            Kzg::<G1>::commit(&powers_of_tau_g1, &poly_adjusted_permutation).into_affine();
        let g1_affine_permutation_padding =
            Kzg::<G1>::commit(&powers_of_tau_g1, &poly_permutation_padding).into_affine();
        let vanishing_poly = domain.vanishing_polynomial().into();
        let g2_vanishing_poly_v =
            Kzg::<G2>::commit(&powers_of_tau_g2, &vanishing_poly).into_affine();

        verify_permutation_proof::<Bn254>(
            g2_u,
            permutation_statement,
            adjusted_permutation_statement,
            g1_affine_permutation_padding,
            permutation_proof,
            g2_vanishing_poly_v,
        );
    }
}
