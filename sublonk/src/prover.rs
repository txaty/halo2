use crate::bn254_convert::{ark_to_halo2_g1_affine, batch_ark_to_halo2_scalar_field};
use crate::config::{SEGMENT_SIZE, USABLE_WITNESSES_SIZE, WITNESS_SIZE};
use crate::multi_row_circuit::WitnessCircuit64;
use crate::permutation::{create_permutation_proof, PermutationProof};
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_segmentlookup::kzg::Kzg;
use ark_segmentlookup::prover::{prove, Proof};
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_segmentlookup::witness::Witness;
use halo2_backend::plonk::ProvingKey;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::ProverSHPLONK;
use halo2_backend::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
use halo2_frontend::circuit::Value;
use halo2_proofs::plonk::{create_proof, sublonk_keygen_pk, sublonk_keygen_vk};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;
use rayon::prelude::*;

pub(crate) fn generate_witnesses_and_statements(
    lookup_params: &PublicParameters<Bn254>,
    fixed_tables: &[Table<Bn254>],
    permutation_tables: &[Table<Bn254>],
    queried_circuit_indices: &[usize],
) -> (
    Vec<Witness<Bn254>>,
    Vec<Witness<Bn254>>,
    Vec<G1Affine>,
    Vec<G1Affine>,
) {
    let fixed_witnesses = generate_witnesses(lookup_params, fixed_tables, queried_circuit_indices);
    let permutation_witnesses =
        generate_witnesses(lookup_params, permutation_tables, queried_circuit_indices);
    let fix_statements = generate_statements(&fixed_witnesses, lookup_params);
    let permutation_statements = generate_statements(&permutation_witnesses, lookup_params);

    (
        fixed_witnesses,
        permutation_witnesses,
        fix_statements,
        permutation_statements,
    )
}

fn generate_witnesses(
    lookup_params: &PublicParameters<Bn254>,
    tables: &[Table<Bn254>],
    queried_circuit_indices: &[usize],
) -> Vec<Witness<Bn254>> {
    tables
        .par_iter()
        .map(|table| Witness::new(lookup_params, table, queried_circuit_indices).unwrap())
        .collect::<Vec<_>>()
}

fn generate_statements(
    witnesses: &[Witness<Bn254>],
    lookup_params: &PublicParameters<Bn254>,
) -> Vec<G1Affine> {
    witnesses
        .par_iter()
        .map(|witness| {
            let ark_statement = witness.generate_statement(&lookup_params.g1_affine_srs);
            ark_to_halo2_g1_affine(&ark_statement)
        })
        .collect::<Vec<_>>()
}

pub(crate) fn generate_proving_key(
    halo2_params: &ParamsKZG<Bn256>,
    queried_circuit_indices: &[usize],
    fixed_statements: &[G1Affine],
    adjusted_permutation_statements: &[G1Affine],
    fixed_witnesses: &[Witness<Bn254>],
    adjusted_permutation_witness_values: &[Vec<Fr>],
) -> ProvingKey<G1Affine> {
    let witness_circuit = WitnessCircuit64::new_empty(Some(queried_circuit_indices));
    let vk = sublonk_keygen_vk(
        halo2_params,
        &witness_circuit,
        &fixed_statements,
        &adjusted_permutation_statements,
    )
    .unwrap();

    let fixed_witness_values = fixed_witnesses
        .par_iter()
        .map(|witness| batch_ark_to_halo2_scalar_field(&witness.poly_eval_list_f))
        .collect::<Vec<_>>();

    let pk = sublonk_keygen_pk(
        halo2_params,
        vk,
        &fixed_witness_values,
        &adjusted_permutation_witness_values,
    )
    .unwrap();

    pk
}

pub(crate) fn sublonk_prove(
    halo2_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    left_values: &[Fr],
    right_values: &[Fr],
    public_inputs: &[Fr],
    queried_circuit_indices: &[usize],
    fixed_tables: &[Table<Bn254>],
    permutation_tables: &[Table<Bn254>],
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_witness_value_paddings: &[Vec<<Bn254 as Pairing>::ScalarField>],
    poly_u: &DensePolynomial<<Bn254 as Pairing>::ScalarField>,
    poly_permutation_padding_list: &[DensePolynomial<<Bn254 as Pairing>::ScalarField>],
) -> (
    Vec<u8>,
    Vec<Proof<Bn254>>,
    Vec<Proof<Bn254>>,
    Vec<G1Affine>,
    Vec<G1Affine>,
    Vec<G1Affine>,
    Vec<PermutationProof<Bn254>>,
) {
    let rng = OsRng;

    let curr_time = std::time::Instant::now();
    let left_values = left_values
        .iter()
        .map(|v| Value::known(*v))
        .collect::<Vec<_>>();
    let right_values = right_values
        .iter()
        .map(|v| Value::known(*v))
        .collect::<Vec<_>>();

    let (fixed_witnesses, permutation_witnesses, fixed_statements, permutation_statements) =
        generate_witnesses_and_statements(
            &lookup_params,
            &fixed_tables,
            &permutation_tables,
            &queried_circuit_indices,
        );

    let ark_permutation_witness_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> =
        permutation_witnesses
            .par_iter()
            .map(|witness| witness.poly_eval_list_f.clone())
            .collect::<Vec<_>>();

    let roots_of_unity_k: Vec<<Bn254 as Pairing>::ScalarField> =
        lookup_params.domain_k.elements().collect();
    let mut ark_adjusted_permutation_witness_values = ark_permutation_witness_values
        .par_iter()
        .map(|witness| {
            let mut modified_witness = witness.clone();
            for i in 0..WITNESS_SIZE {
                modified_witness[i] = witness[i] * roots_of_unity_k[i / SEGMENT_SIZE];
            }
            modified_witness
        })
        .collect::<Vec<_>>();

    ark_adjusted_permutation_witness_values
        .par_iter_mut()
        .zip(permutation_witness_value_paddings.par_iter())
        .for_each(|(witness, padding)| {
            witness[USABLE_WITNESSES_SIZE..WITNESS_SIZE].copy_from_slice(&padding);
        });

    let ark_adjusted_permutation_witness_poly_coeff_list: Vec<_> =
        ark_adjusted_permutation_witness_values
            .par_iter()
            .map(|witness| lookup_params.domain_v.ifft(witness))
            .collect();

    let adjusted_permutation_statements: Vec<G1Affine> =
        ark_adjusted_permutation_witness_poly_coeff_list
            .par_iter()
            .map(|coeff_list| {
                let poly = DensePolynomial::from_coefficients_slice(coeff_list);
                let ark_com =
                    Kzg::<<Bn254 as Pairing>::G1>::commit(&lookup_params.g1_affine_srs, &poly)
                        .into_affine();

                ark_to_halo2_g1_affine(&ark_com)
            })
            .collect();

    let adjusted_permutation_witness_values: Vec<_> = ark_adjusted_permutation_witness_values
        .par_iter()
        .map(|witness| batch_ark_to_halo2_scalar_field(witness))
        .collect();
    println!(
        "Proving: prepare witnesses and statements (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let curr_time = std::time::Instant::now();
    let pk = generate_proving_key(
        &halo2_params,
        &queried_circuit_indices,
        &fixed_statements,
        &adjusted_permutation_statements,
        &fixed_witnesses,
        &adjusted_permutation_witness_values,
    );
    println!(
        "Proving: generate proving key (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let curr_time = std::time::Instant::now();
    let witness_circuit =
        WitnessCircuit64::new(&left_values, &right_values, queried_circuit_indices);

    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);

    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        _,
    >(
        halo2_params,
        &pk,
        &[witness_circuit],
        &[&[&public_inputs]],
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    println!(
        "Proving: create plonk proof (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let curr_time = std::time::Instant::now();
    let fixed_lookup_proofs = batch_lookup_create_proof(
        lookup_params,
        fixed_tpp_list,
        fixed_tables,
        &fixed_witnesses,
    );

    let permutation_lookup_proofs = batch_lookup_create_proof(
        lookup_params,
        permutation_tpp_list,
        permutation_tables,
        &permutation_witnesses,
    );
    let permutation_proofs = poly_permutation_padding_list
        .par_iter()
        .zip(ark_permutation_witness_values)
        .zip(ark_adjusted_permutation_witness_values)
        .map(|((poly_permutation_padding, witness_values), adjusted_witness_values)| {
            create_permutation_proof(
                &lookup_params.g1_affine_srs,
                &lookup_params.domain_v,
                poly_u,
                poly_permutation_padding,
                &witness_values,
                &adjusted_witness_values,
            )
        })
        .collect();
    println!(
        "Proving: create lookup proofs (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    (
        transcript.finalize(),
        fixed_lookup_proofs,
        permutation_lookup_proofs,
        fixed_statements,
        permutation_statements,
        adjusted_permutation_statements,
        permutation_proofs,
    )
}

fn batch_lookup_create_proof(
    pp: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    tables: &[Table<Bn254>],
    witnesses: &[Witness<Bn254>],
) -> Vec<Proof<Bn254>> {
    let proofs: Vec<_> = tables
        .par_iter()
        .zip(tpp_list.par_iter())
        .zip(witnesses.par_iter())
        .map(|((table, tpp), witness)| prove(pp, table, tpp, witness, &mut OsRng).unwrap())
        .collect();

    proofs
}
