use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_segmentlookup::prover::{prove, Proof};
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_segmentlookup::verifier::verify;
use ark_segmentlookup::witness::Witness;
use rand_core::OsRng;
use rayon::prelude::*;

pub(crate) struct WitnessesAndStatements {
    pub(crate) fixed_witnesses: Vec<Witness<Bn254>>,
    pub(crate) permutation_witnesses: Vec<Witness<Bn254>>,
    pub(crate) fixed_statements: Vec<<Bn254 as Pairing>::G1Affine>,
    pub(crate) permutation_statements: Vec<<Bn254 as Pairing>::G1Affine>,
}

pub(crate) fn generate_witnesses_and_statements(
    lookup_params: &PublicParameters<Bn254>,
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    queried_circuit_indices: &[usize],
) -> WitnessesAndStatements {
    let fixed_witnesses =
        generate_witnesses(lookup_params, fixed_tpp_list, queried_circuit_indices);
    let permutation_witnesses =
        generate_witnesses(lookup_params, permutation_tpp_list, queried_circuit_indices);

    let fixed_statements = generate_statements(&fixed_witnesses, lookup_params);
    let permutation_statements = generate_statements(&permutation_witnesses, lookup_params);

    WitnessesAndStatements {
        fixed_witnesses,
        permutation_witnesses,
        fixed_statements,
        permutation_statements,
    }
}

pub(crate) fn generate_witnesses(
    lookup_params: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    queried_circuit_indices: &[usize],
) -> Vec<Witness<Bn254>> {
    let witness_list = tpp_list
        .par_iter()
        .map(|tpp| {
            Witness::new(
                lookup_params,
                &tpp.adjusted_table_values,
                queried_circuit_indices,
            )
            .unwrap()
        })
        .collect::<Vec<_>>();

    witness_list
}

pub(crate) fn generate_statements(
    witnesses: &[Witness<Bn254>],
    lookup_params: &PublicParameters<Bn254>,
) -> Vec<<Bn254 as Pairing>::G1Affine> {
    witnesses
        .par_iter()
        .map(|witness| witness.generate_statement(&lookup_params.g1_affine_srs))
        .collect::<Vec<_>>()
}

pub(crate) fn get_raw_table_values(
    lookup_params: &PublicParameters<Bn254>,
    tables: &[Table<Bn254>],
    queried_circuit_indices: &[usize],
) -> Vec<Vec<<Bn254 as Pairing>::ScalarField>> {
    let segment_size = lookup_params.segment_size;

    tables
        .par_iter()
        .map(|table| {
            let witness_values = queried_circuit_indices
                .par_iter()
                .map(|&segment_index| {
                    let start_index = segment_index * segment_size;
                    let end_index = start_index + segment_size;
                    table.values[start_index..end_index].to_vec()
                })
                .flatten()
                .collect::<Vec<_>>();

            witness_values
        })
        .collect::<Vec<_>>()
}

pub(crate) fn recover_statements(
    statements: &[<Bn254 as Pairing>::G1Affine],
    tpp_list: &[TablePreprocessedParameters<Bn254>],
) -> Vec<<Bn254 as Pairing>::G1Affine> {
    let recovered_statements = statements
        .par_iter()
        .zip(tpp_list)
        .map(|(&statement, tpp)| {
            let recovered_statement = statement - tpp.g1_affine_d;

            recovered_statement
        })
        .collect::<Vec<_>>();

    <Bn254 as Pairing>::G1::normalize_batch(&recovered_statements)
}

pub(crate) fn batch_lookup_create_proof(
    pp: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    witnesses: &[Witness<Bn254>],
    statements: &[<Bn254 as Pairing>::G1Affine],
) -> Vec<Proof<Bn254>> {
    let proofs: Vec<_> = tpp_list
        .iter()
        .zip(witnesses.iter())
        .zip(statements)
        .map(|((tpp, witness), &statement)| {
            let curr_time = std::time::Instant::now();
            let result = prove(pp, tpp, witness, statement, &mut OsRng).unwrap();
            println!(
                "Proving: create single lookup proof (ms):\n{:?}",
                curr_time.elapsed().as_millis()
            );

            result
        })
        .collect();

    proofs
}

pub(crate) fn batch_lookup_verify(
    pp: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    proofs: &[Proof<Bn254>],
    statements: &[<Bn254 as Pairing>::G1Affine],
) {
    tpp_list
        .iter()
        .zip(proofs.iter())
        .zip(statements.iter())
        .for_each(|((tpp, proof), &statement)| {
            let curr_time = std::time::Instant::now();
            verify(pp, tpp, statement, proof, &mut OsRng).unwrap();
            println!(
                "Verification: single lookup proof verification (ms):\n{:?}",
                curr_time.elapsed().as_millis()
            );
        });
}
