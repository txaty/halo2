mod bench_config;
mod bn254_convert;
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

use crate::bench_config::{
    Config, DEFAULT_NUM_DIFFERENT_SEGMENTS, DEFAULT_POW_NUM_TABLE_CIRCUIT,
    DEFAULT_POW_NUM_WITNESS_CIRCUIT,
};
use crate::input::{generate_queried_circuit_indices, generate_sub_circuit_list};
use crate::multi_row_circuit::WitnessCircuit64;
use crate::preprocess::preprocess;
use crate::prover::{sublonk_prove, SublonkProof};
use crate::verifier::sublonk_verify;
use halo2_middleware::halo2curves::bn256::Fr;

fn main() {
    println!("Rayon Threads: {}", rayon::current_num_threads());

    let pow_segment_size_list = 5..=13;
    for pow_segment_size in pow_segment_size_list {
        let config = Config::new(
            DEFAULT_POW_NUM_WITNESS_CIRCUIT,
            pow_segment_size,
            DEFAULT_POW_NUM_TABLE_CIRCUIT,
            DEFAULT_NUM_DIFFERENT_SEGMENTS,
        );
        config.print_benchmark_info();

        let circuits = generate_sub_circuit_list(&config);

        let witness_circuit = WitnessCircuit64::new_empty(None, &config);
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
        ) = preprocess(&config, &circuits, &witness_circuit);

        let queried_circuit_indices = generate_queried_circuit_indices(&config);

        let left_values = vec![Fr::from(2); config.valid_num_witness_circuits];
        let right_values = vec![Fr::from(3); config.valid_num_witness_circuits];
        let public_inputs = (0..config.valid_num_witness_circuits)
            .flat_map(|i| match queried_circuit_indices[i] % 2 {
                0 => vec![left_values[i] + right_values[i]; config.segment_size],
                1 => vec![left_values[i] * right_values[i]; config.segment_size],
                _ => panic!("Invalid circuit index"),
            })
            .collect::<Vec<_>>();

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
    }
}
