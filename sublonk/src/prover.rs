use crate::bn254_convert::{ark_to_halo2_g1_affine, batch_ark_to_halo2_scalar_field};
use crate::plonk_circuit::WitnessCircuit;
use ark_bn254::Bn254;
use ark_segmentlookup::prover::{prove, Proof};
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_segmentlookup::witness::Witness;
use halo2_backend::plonk::ProvingKey;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::ProverSHPLONK;
use halo2_backend::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
use halo2_frontend::circuit::Value;
use halo2_proofs::plonk::{
    sublonk_create_proof, sublonk_keygen_pk, sublonk_keygen_vk,
};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;

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
    let fixed_witnesses = fixed_tables
        .iter()
        .map(|table| Witness::new(lookup_params, table, queried_circuit_indices).unwrap())
        .collect::<Vec<_>>();
    let permutation_witnesses = permutation_tables
        .iter()
        .map(|table| Witness::new(lookup_params, table, queried_circuit_indices).unwrap())
        .collect::<Vec<_>>();
    let fix_statements = fixed_witnesses
        .iter()
        .map(|witness| {
            let ark_statement = witness.generate_statement(&lookup_params.g1_affine_srs);

            ark_to_halo2_g1_affine(&ark_statement)
        })
        .collect::<Vec<_>>();

    let permutation_statements = permutation_witnesses
        .iter()
        .map(|witness| {
            let ark_statement = witness.generate_statement(&lookup_params.g1_affine_srs);

            ark_to_halo2_g1_affine(&ark_statement)
        })
        .collect::<Vec<_>>();

    (
        fixed_witnesses,
        permutation_witnesses,
        fix_statements,
        permutation_statements,
    )
}

pub(crate) fn generate_proving_key(
    halo2_params: &ParamsKZG<Bn256>,
    queried_circuit_indices: &[usize],
    fixed_statements: &[G1Affine],
    adjusted_permutation_statements: &[G1Affine],
    fixed_witnesses: &[Witness<Bn254>],
    // permutation_witnesses: &[Witness<Bn254>],
    adjusted_permutation_witness_values: &[Vec<Fr>],
) -> ProvingKey<G1Affine> {
    let witness_circuit = WitnessCircuit::new_empty(Some(queried_circuit_indices));
    let vk = sublonk_keygen_vk(
        halo2_params,
        &witness_circuit,
        &fixed_statements,
        &adjusted_permutation_statements,
    )
    .unwrap();

    let fixed_witness_values = fixed_witnesses
        .iter()
        .map(|witness| batch_ark_to_halo2_scalar_field(&witness.poly_eval_list_f))
        .collect::<Vec<_>>();

    let pk = sublonk_keygen_pk(
        halo2_params,
        vk,
        &witness_circuit,
        &fixed_witness_values,
        &adjusted_permutation_witness_values,
    )
    .unwrap();

    pk
}

pub(crate) fn prover(
    halo2_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    pk: &ProvingKey<G1Affine>,
    left_values: &[Fr],
    right_values: &[Fr],
    public_inputs: &[Fr],
    queried_circuit_indices: &[usize],
    fixed_tables: &[Table<Bn254>],
    permutation_tables: &[Table<Bn254>],
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    fixed_witnesses: &[Witness<Bn254>],
    permutation_witnesses: &[Witness<Bn254>],
) -> (Vec<u8>, Vec<Proof<Bn254>>, Vec<Proof<Bn254>>) {
    let rng = OsRng;
    let left_values = left_values
        .iter()
        .map(|v| Value::known(*v))
        .collect::<Vec<_>>();
    let right_values = right_values
        .iter()
        .map(|v| Value::known(*v))
        .collect::<Vec<_>>();

    let witness_circuit = WitnessCircuit::new(&left_values, &right_values, queried_circuit_indices);
    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);

    sublonk_create_proof::<
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
        &[&[public_inputs]],
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");

    let fixed_lookup_proofs =
        batch_lookup_create_proof(lookup_params, fixed_tpp_list, fixed_tables, fixed_witnesses);

    let permutation_lookup_proofs = batch_lookup_create_proof(
        lookup_params,
        permutation_tpp_list,
        permutation_tables,
        permutation_witnesses,
    );

    (
        transcript.finalize(),
        fixed_lookup_proofs,
        permutation_lookup_proofs,
    )
}

fn batch_lookup_create_proof(
    pp: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    tables: &[Table<Bn254>],
    witnesses: &[Witness<Bn254>],
) -> Vec<Proof<Bn254>> {
    let proofs: Vec<_> = tables
        .iter()
        .zip(tpp_list.iter())
        .zip(witnesses.iter())
        .map(|((table, tpp), witness)| prove(pp, table, tpp, witness, &mut OsRng).unwrap())
        .collect();

    proofs
}
