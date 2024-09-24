use crate::config::Config;
use crate::multi_row_circuit::{AddCircuit64, CircuitEnum64, MulCircuit64};
use halo2_frontend::circuit::Value;
use halo2curves::bn256::Fr;

pub(crate) fn generate_sub_circuit_list(config: &Config) -> Vec<CircuitEnum64<Fr>> {
    let add_circuit64 = AddCircuit64 {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
        segment_size: config.segment_size,
    };
    let mul_circuit64 = MulCircuit64 {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
        segment_size: config.segment_size,
    };
    let num_circuits = config.num_table_circuits;
    let mut circuits = Vec::with_capacity(num_circuits);
    for i in 0..num_circuits {
        if i % 2 == 0 {
            circuits.push(CircuitEnum64::Add(add_circuit64.clone()));
        } else {
            circuits.push(CircuitEnum64::Mul(mul_circuit64.clone()));
        }
    }
    circuits[num_circuits - 1] = CircuitEnum64::PlaceHolder;

    circuits
}

pub(crate) fn generate_queried_circuit_indices(config: &Config) -> Vec<usize> {
    let num_table_circuits = config.num_table_circuits;
    let num_witness_circuits = config.num_witness_circuits;
    let num_different_segments = config.num_different_segments;
    let different_indices = (0..num_different_segments).collect::<Vec<_>>();

    let mut queried_circuit_indices = vec![0; num_witness_circuits];
    for i in 0..num_witness_circuits {
        queried_circuit_indices[i] = different_indices[i % (num_different_segments)];
    }
    queried_circuit_indices[num_witness_circuits - 1] = num_table_circuits - 1;

    queried_circuit_indices
}
