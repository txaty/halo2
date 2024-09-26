use crate::config::Config;
use crate::keygen::{generate_proving_key, permutation_padding};
use crate::lookup::{
    batch_lookup_create_proof, generate_witnesses_and_statements, get_raw_table_values,
    recover_statements, WitnessesAndStatements,
};
use crate::multi_row_circuit::WitnessCircuit64;
use crate::permutation::create_permutation_proof;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_poly::univariate::DensePolynomial;
use ark_segmentlookup::prover::Proof;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::ProverSHPLONK;
use halo2_backend::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
use halo2_frontend::circuit::Value;
use halo2_proofs::plonk::create_proof;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;
use rayon::prelude::*;

pub(crate) struct SublonkProof {
    pub(crate) halo2_proof: Vec<u8>,
    pub(crate) fixed_lookup_proofs: Vec<Proof<Bn254>>,
    pub(crate) permutation_lookup_proofs: Vec<Proof<Bn254>>,
    pub(crate) fixed_statements: Vec<<Bn254 as Pairing>::G1Affine>,
    pub(crate) permutation_statements: Vec<<Bn254 as Pairing>::G1Affine>,
    pub(crate) padded_permutation_statements: Vec<<Bn254 as Pairing>::G1Affine>,
    pub(crate) permutation_proofs: Vec<<Bn254 as Pairing>::G1>,
}

pub(crate) fn sublonk_prove(
    config: &Config,
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
) -> SublonkProof {
    let rng = OsRng;

    let curr_time = std::time::Instant::now();
    let left_values = left_values
        .par_iter()
        .map(|v| Value::known(*v))
        .collect::<Vec<_>>();
    let right_values = right_values
        .par_iter()
        .map(|v| Value::known(*v))
        .collect::<Vec<_>>();

    let WitnessesAndStatements {
        fixed_witnesses,
        permutation_witnesses,
        fixed_statements,
        permutation_statements,
    } = generate_witnesses_and_statements(
        &lookup_params,
        &fixed_tpp_list,
        &permutation_tpp_list,
        &queried_circuit_indices,
    );

    let fixed_raw_value_lists =
        get_raw_table_values(&lookup_params, &fixed_tables, &queried_circuit_indices);
    let recovered_fixed_statements = recover_statements(&fixed_statements, &fixed_tpp_list);
    let permutation_raw_value_lists = get_raw_table_values(
        &lookup_params,
        &permutation_tables,
        &queried_circuit_indices,
    );

    let (padded_permutation_statements, padded_permutation_witness_value_lists) =
        permutation_padding(
            config,
            &lookup_params,
            &permutation_raw_value_lists,
            &permutation_witness_value_paddings,
        );

    println!(
        "Proving: prepare witnesses and statements (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let curr_time = std::time::Instant::now();
    let pk = generate_proving_key(
        config,
        &halo2_params,
        &queried_circuit_indices,
        &recovered_fixed_statements,
        &padded_permutation_statements,
        &fixed_raw_value_lists,
        &padded_permutation_witness_value_lists,
    );
    println!(
        "Proving: generate proving key (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let curr_time = std::time::Instant::now();
    let witness_circuit =
        WitnessCircuit64::new(&left_values, &right_values, queried_circuit_indices, config);

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
        &fixed_witnesses,
        &fixed_statements,
    );

    let permutation_lookup_proofs = batch_lookup_create_proof(
        lookup_params,
        permutation_tpp_list,
        &permutation_witnesses,
        &permutation_statements,
    );
    let permutation_proofs = poly_permutation_padding_list
        .iter()
        .zip(permutation_raw_value_lists)
        .zip(padded_permutation_witness_value_lists)
        .map(
            |((poly_permutation_padding, witness_values), adjusted_witness_values)| {
                let curr_time = std::time::Instant::now();
                let result = create_permutation_proof::<Bn254>(
                    &lookup_params.g1_affine_srs,
                    &lookup_params.domain_v,
                    poly_u,
                    poly_permutation_padding,
                    &witness_values,
                    &adjusted_witness_values,
                );
                println!(
                    "Proving: create permutation proof (ms):\n{:?}",
                    curr_time.elapsed().as_millis()
                );

                result
            },
        )
        .collect();
    println!(
        "Proving: create lookup proofs (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    SublonkProof {
        halo2_proof: transcript.finalize(),
        fixed_lookup_proofs,
        permutation_lookup_proofs,
        fixed_statements,
        permutation_statements,
        padded_permutation_statements,
        permutation_proofs,
    }
}
