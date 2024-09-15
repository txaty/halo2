mod bn254_convert;
mod kzg_params;
mod parameters;
mod plonk_circuit;
mod preprocess;
mod prover;
mod verifier;

use crate::parameters::{NUM_USABLE_WITNESSES, NUM_WITNESSES, NUM_WITNESS_POWERS};
use crate::plonk_circuit::{AddCircuit, CircuitEnum, MulCircuit, WitnessCircuit};
use crate::preprocess::preprocess;
use crate::prover::sublonk_prove;
use crate::verifier::sublonk_verify;
use ark_std::rand::random;
use halo2_frontend::circuit::Value;
use halo2_middleware::halo2curves::bn256::Fr;

fn main() {
    println!("NUM_WITNESSES: {}", NUM_WITNESSES);
    println!("NUM_USABLE_WITNESSES: {}", NUM_USABLE_WITNESSES);
    println!("NUM_WITNESS_POWERS: {}", NUM_WITNESS_POWERS);

    let add_circuit = AddCircuit {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
    };
    let mul_circuit = MulCircuit {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
    };
    let circuits = vec![
        CircuitEnum::Add(add_circuit),
        CircuitEnum::Mul(mul_circuit),
        CircuitEnum::PlaceHolder,
        CircuitEnum::PlaceHolder,
    ];
    let witness_circuit = WitnessCircuit::new_empty(None);

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
    ) = preprocess(
        circuits.len(),
        NUM_WITNESSES,
        NUM_WITNESS_POWERS,
        0,
        &circuits,
        &witness_circuit,
    );
    println!(
        "Preprocess time (ms): {:?}",
        curr_time.elapsed().as_millis()
    );

    let mut queried_circuit_indices = vec![0; NUM_USABLE_WITNESSES];
    for i in 0..NUM_USABLE_WITNESSES {
        queried_circuit_indices[i] = random::<usize>() % 2;
    }
    queried_circuit_indices.resize(NUM_WITNESSES, circuits.len() - 1);

    let left_values = vec![Fr::from(2); NUM_USABLE_WITNESSES];
    let right_values = vec![Fr::from(3); NUM_USABLE_WITNESSES];
    let public_inputs = (0..NUM_USABLE_WITNESSES)
        .map(|i| match queried_circuit_indices[i] {
            0 => left_values[i] + right_values[i],
            1 => left_values[i] * right_values[i],
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
    );
    println!("Prove time (ms): {:?}", curr_time.elapsed().as_millis());

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
    );
}
