mod bn254_convert;
mod config;
mod kzg_params;
mod multi_row_circuit;
mod permutation;
mod plonk_circuit;
mod preprocess;
mod prover;
mod verifier;

use crate::config::{
    NUM_WITNESS_CIRCUITS, POW_SEGMENT_SIZE, POW_WITNESS_SIZE, SEGMENT_SIZE,
    VALID_NUM_WITNESS_CIRCUITS,
};
use crate::multi_row_circuit::{AddCircuit64, CircuitEnum64, MulCircuit64, WitnessCircuit64};
use crate::preprocess::preprocess;
use crate::prover::sublonk_prove;
use crate::verifier::sublonk_verify;
use ark_std::rand::random;
use halo2_frontend::circuit::Value;
use halo2_middleware::halo2curves::bn256::Fr;
use rayon::ThreadPoolBuilder;

fn main() {
    ThreadPoolBuilder::new()
        .num_threads(1)
        .build_global()
        .unwrap();
    
    println!("Rayon Threads: {}", rayon::current_num_threads());

    let add_circuit64 = AddCircuit64 {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
    };
    let mul_circuit64 = MulCircuit64 {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
    };
    let circuit_size = 1 << 10;
    let mut circuits = Vec::with_capacity(circuit_size);
    for i in 0..circuit_size {
        if i % 2 == 0 {
            circuits.push(CircuitEnum64::Add(add_circuit64.clone()));
        } else {
            circuits.push(CircuitEnum64::Mul(mul_circuit64.clone()));
        }
    }
    circuits[circuit_size - 1] = CircuitEnum64::PlaceHolder;
    let witness_circuit = WitnessCircuit64::new_empty(None);

    println!("NUM TABLE CIRCUITS: {}", circuits.len());
    println!("NUM WITNESS CIRCUITS: {}", NUM_WITNESS_CIRCUITS);
    println!("SEGMENT SIZE: {}", SEGMENT_SIZE);

    let curr_time = std::time::Instant::now();
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
        circuits.len(),
        NUM_WITNESS_CIRCUITS,
        POW_WITNESS_SIZE as u32,
        POW_SEGMENT_SIZE as u32,
        &circuits,
        &witness_circuit,
    );
    println!(
        "Preprocess time (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let mut queried_circuit_indices = vec![0; VALID_NUM_WITNESS_CIRCUITS];
    for i in 0..VALID_NUM_WITNESS_CIRCUITS {
        queried_circuit_indices[i] = random::<usize>() % (circuits.len() - 1);
    }
    queried_circuit_indices.resize(NUM_WITNESS_CIRCUITS, circuits.len() - 1);

    let left_values = vec![Fr::from(2); VALID_NUM_WITNESS_CIRCUITS];
    let right_values = vec![Fr::from(3); VALID_NUM_WITNESS_CIRCUITS];
    let public_inputs = (0..VALID_NUM_WITNESS_CIRCUITS)
        .flat_map(|i| match queried_circuit_indices[i] % 2 {
            0 => vec![left_values[i] + right_values[i]; SEGMENT_SIZE],
            1 => vec![left_values[i] * right_values[i]; SEGMENT_SIZE],
            _ => panic!("Invalid circuit index"),
        })
        .collect::<Vec<_>>();

    let curr_time = std::time::Instant::now();
    let (
        proof,
        fixed_proofs,
        permutation_proofs,
        fixed_statements,
        permutation_statements,
        adjusted_permutation_statements,
        adjusted_permutation_proofs,
    ) = sublonk_prove(
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
        &proof,
        &public_inputs,
        &witness_cs,
        &fixed_tpp_list,
        &permutation_tpp_list,
        &fixed_proofs,
        &permutation_proofs,
        &fixed_statements,
        &permutation_statements,
        &adjusted_permutation_statements,
        &g1_affine_list_permutation_padding,
        g2_u,
        &adjusted_permutation_proofs,
    );
    println!("Verify time (ms):\n{:?}", curr_time.elapsed().as_millis());
}
