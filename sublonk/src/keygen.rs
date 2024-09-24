use crate::bn254_convert::{ark_to_halo2_g1_affine, batch_ark_to_halo2_scalar_field};
use crate::config::{Config};
use crate::multi_row_circuit::WitnessCircuit64;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_segmentlookup::kzg::Kzg;
use ark_segmentlookup::public_parameters::PublicParameters;
use halo2_backend::plonk::permutation::VerifyingKey as PermutationVerifyingKey;
use halo2_backend::plonk::sublonk_keygen::SublonkVerifyingKey;
use halo2_backend::plonk::{ProvingKey, VerifyingKey};
use halo2_backend::poly::commitment::Params;
use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_middleware::circuit::ConstraintSystemMid;
use halo2_proofs::plonk::{sublonk_keygen_pk, sublonk_keygen_vk};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rayon::prelude::*;

pub(crate) fn generate_proving_key(
    config: &Config,
    halo2_params: &ParamsKZG<Bn256>,
    queried_circuit_indices: &[usize],
    fixed_statements: &[<Bn254 as Pairing>::G1Affine],
    permutation_statements: &[<Bn254 as Pairing>::G1Affine],
    fixed_witness_value_lists: &[Vec<<Bn254 as Pairing>::ScalarField>],
    permutation_witness_value_lists: &[Vec<<Bn254 as Pairing>::ScalarField>],
) -> ProvingKey<G1Affine> {
    let witness_circuit = WitnessCircuit64::new_empty(Some(queried_circuit_indices), config);
    let halo2_fixed_statements = fixed_statements
        .par_iter()
        .map(|statement| ark_to_halo2_g1_affine(statement))
        .collect::<Vec<_>>();

    let halo2_permutation_statements = permutation_statements
        .par_iter()
        .map(|statement| ark_to_halo2_g1_affine(statement))
        .collect::<Vec<_>>();

    let vk = sublonk_keygen_vk(
        halo2_params,
        &witness_circuit,
        &halo2_fixed_statements,
        &halo2_permutation_statements,
    )
    .unwrap();

    let halo2_fixed_witness_value_lists = fixed_witness_value_lists
        .par_iter()
        .map(|witness_value_list| batch_ark_to_halo2_scalar_field(witness_value_list))
        .collect::<Vec<_>>();

    let halo2_permutation_witness_value_lists = permutation_witness_value_lists
        .par_iter()
        .map(|witness_value_list| batch_ark_to_halo2_scalar_field(witness_value_list))
        .collect::<Vec<_>>();

    let pk = sublonk_keygen_pk(
        halo2_params,
        vk,
        &halo2_fixed_witness_value_lists,
        &halo2_permutation_witness_value_lists,
    )
    .unwrap();

    pk
}

pub(crate) fn permutation_padding(
    config: &Config,
    lookup_params: &PublicParameters<Bn254>,
    permutation_raw_value_lists: &[Vec<<Bn254 as Pairing>::ScalarField>],
    permutation_witness_value_paddings: &[Vec<<Bn254 as Pairing>::ScalarField>],
) -> (
    Vec<<Bn254 as Pairing>::G1Affine>,
    Vec<Vec<<Bn254 as Pairing>::ScalarField>>,
) {
    let witness_size = config.witness_size;
    let usable_witnesses_size = config.usable_witness_size;
    let roots_of_unity_k: Vec<<Bn254 as Pairing>::ScalarField> =
        lookup_params.domain_k.elements().collect();
    let segment_size = config.segment_size;
    let mut padded_permutation_witness_value_lists = permutation_raw_value_lists
        .par_iter()
        .map(|witness| {
            let mut modified_witness = witness.clone();
            for i in 0..witness_size {
                modified_witness[i] = witness[i] * roots_of_unity_k[i / segment_size];
            }
            modified_witness
        })
        .collect::<Vec<_>>();

    padded_permutation_witness_value_lists
        .par_iter_mut()
        .zip(permutation_witness_value_paddings.par_iter())
        .for_each(|(witness, padding)| {
            witness[usable_witnesses_size..witness_size].copy_from_slice(&padding);
        });

    let padded_permutation_witness_poly_coeff_list: Vec<_> = padded_permutation_witness_value_lists
        .par_iter()
        .map(|witness| lookup_params.domain_v.ifft(witness))
        .collect();

    let padded_permutation_statements: Vec<<Bn254 as Pairing>::G1Affine> =
        padded_permutation_witness_poly_coeff_list
            .par_iter()
            .map(|coeff_list| {
                let poly = DensePolynomial::from_coefficients_slice(coeff_list);

                Kzg::<<Bn254 as Pairing>::G1>::commit(&lookup_params.g1_affine_srs, &poly)
                    .into_affine()
            })
            .collect();

    (
        padded_permutation_statements,
        padded_permutation_witness_value_lists,
    )
}

pub(crate) fn generate_verification_key(
    halo2_params: &ParamsKZG<Bn256>,
    witness_cs: &ConstraintSystemMid<Fr>,
    fixed_statements: &[<Bn254 as Pairing>::G1Affine],
    padded_permutation_statements: &[<Bn254 as Pairing>::G1Affine],
) -> VerifyingKey<G1Affine> {
    let sublonk_vk = SublonkVerifyingKey::<G1Affine>::new(halo2_params.k(), witness_cs);

    let halo2_fixed_statements = fixed_statements
        .par_iter()
        .map(|statement| ark_to_halo2_g1_affine(statement))
        .collect::<Vec<_>>();

    let halo2_padded_permutation_statements = padded_permutation_statements
        .par_iter()
        .map(|statement| ark_to_halo2_g1_affine(statement))
        .collect::<Vec<_>>();

    let vk = VerifyingKey::from_parts(
        sublonk_vk.domain.clone(),
        halo2_fixed_statements,
        PermutationVerifyingKey {
            commitments: halo2_padded_permutation_statements,
        },
        sublonk_vk.cs.clone(),
    );

    vk
}
