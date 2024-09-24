mod bn254_convert;
mod config;
mod input;
mod keygen;
mod kzg_params;
mod lookup;
mod multi_row_circuit;
mod permutation;
mod plonk_circuit;
mod preprocess;
mod prover;
mod verifier;

use crate::config::{Config, NUM_TABLE_CIRCUITS, POW_NUM_TABLE_CIRCUIT, POW_SEGMENT_SIZE, SEGMENT_SIZE};
use crate::input::{generate_queried_circuit_indices, generate_sub_circuit_list};
use crate::multi_row_circuit::WitnessCircuit64;
use crate::preprocess::preprocess;
use crate::prover::{sublonk_prove, SublonkProof};
use crate::verifier::sublonk_verify;
use halo2_middleware::halo2curves::bn256::Fr;

fn main() {
    println!("Rayon Threads: {}", rayon::current_num_threads());

    let pow_num_witness_circuits_list = 10..=20;

    for pow_num_witness_circuits in pow_num_witness_circuits_list {
        let num_witness_circuits = 1 << pow_num_witness_circuits;
        let pow_witness_size: usize = pow_num_witness_circuits + POW_SEGMENT_SIZE;
        let valid_num_witness_circuits: usize = num_witness_circuits - 1;

        let config = Config {
            pow_num_witness_circuits,
            num_witness_circuits,
            pow_segment_size: POW_SEGMENT_SIZE,
            segment_size: SEGMENT_SIZE,
            pow_witness_size,
            witness_size: 1 << pow_witness_size,
            num_unusable_rows: SEGMENT_SIZE,
            usable_witnesses_size: 1 << pow_witness_size - SEGMENT_SIZE,
            valid_num_witness_circuits,
            pow_num_table_circuit: POW_NUM_TABLE_CIRCUIT,
            num_table_circuits: NUM_TABLE_CIRCUITS,
            num_different_segments: 4,
        };


        let circuits = generate_sub_circuit_list(NUM_TABLE_CIRCUITS);

        println!("NUM TABLE CIRCUITS: {}", NUM_TABLE_CIRCUITS);
        println!("NUM WITNESS CIRCUITS: {}", num_witness_circuits);
        println!("SEGMENT SIZE: {}", SEGMENT_SIZE);
        println!("NUM DIFFERENT SEGMENTS: {}", config.num_different_segments);

        let curr_time = std::time::Instant::now();
        let witness_circuit = WitnessCircuit64::new_empty(None, config.valid_num_witness_circuits);
        let (
            halo2_params,
            lookup_params,
            fixed_tables,
            permutation_tables,
            fixed_tpp_list,
            permutation_tpp_list,
            witness_cs,
            permutation_witness_value_paddings,
            poly_u,
            poly_permutation_padding_list,
            g2_u,
            g1_affine_list_permutation_padding,
        ) = preprocess(
            &config,
            &circuits,
            &witness_circuit,
        );
        println!(
            "Preprocess time (ms):\n{:?}",
            curr_time.elapsed().as_millis()
        );

        let queried_circuit_indices = generate_queried_circuit_indices(
            &config,
        );

        let left_values = vec![Fr::from(2); valid_num_witness_circuits];
        let right_values = vec![Fr::from(3); valid_num_witness_circuits];
        let public_inputs = (0..valid_num_witness_circuits)
            .flat_map(|i| match queried_circuit_indices[i] % 2 {
                0 => vec![left_values[i] + right_values[i]; SEGMENT_SIZE],
                1 => vec![left_values[i] * right_values[i]; SEGMENT_SIZE],
                _ => panic!("Invalid circuit index"),
            })
            .collect::<Vec<_>>();

        let curr_time = std::time::Instant::now();
        let SublonkProof {
            halo2_proof,
            fixed_lookup_proofs,
            permutation_lookup_proofs,
            fixed_statements,
            permutation_statements,
            padded_permutation_statements,
            permutation_proofs,
        } = sublonk_prove(
            &config,
            &halo2_params,
            &lookup_params,
            &left_values,
            &right_values,
            &public_inputs,
            &queried_circuit_indices,
            &fixed_tables,
            &permutation_tables,
            &fixed_tpp_list,
            &permutation_tpp_list,
            &permutation_witness_value_paddings,
            &poly_u,
            &poly_permutation_padding_list,
        );
        println!("Prove time (ms):\n{:?}", curr_time.elapsed().as_millis());

        let curr_time = std::time::Instant::now();
        sublonk_verify(
            &halo2_params,
            &lookup_params,
            &halo2_proof,
            &public_inputs,
            &witness_cs,
            &fixed_tpp_list,
            &permutation_tpp_list,
            &fixed_lookup_proofs,
            &permutation_lookup_proofs,
            &fixed_statements,
            &permutation_statements,
            &padded_permutation_statements,
            &g1_affine_list_permutation_padding,
            g2_u,
            &permutation_proofs,
        );
        println!("Verify time (ms):\n{:?}", curr_time.elapsed().as_millis());
    }
}
