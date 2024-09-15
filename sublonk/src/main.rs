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
    let curr_time = std::time::SystemTime::now();
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
        "Preprocess time: {} ms",
        curr_time.elapsed().unwrap().as_millis()
    );

    let mut queried_circuit_indices = vec![0; NUM_USABLE_WITNESSES];
    for i in 0..NUM_USABLE_WITNESSES {
        queried_circuit_indices[i] = random::<usize>() % 2;
    }
    queried_circuit_indices.resize(NUM_WITNESSES, circuits.len() - 1);

    let curr_time = std::time::SystemTime::now();
    // let (fixed_witnesses, permutation_witnesses, fixed_statements, permutation_statements) =
    //     generate_witnesses_and_statements(
    //         &lookup_params,
    //         &fixed_tables,
    //         &permutation_tables,
    //         &queried_circuit_indices,
    //     );
    //
    // let ark_omega = lookup_params.domain_v.group_gen;
    // let ark_one = <Bn254 as Pairing>::ScalarField::one();
    // let mut ark_omega_pow_list = vec![ark_one; NUM_WITNESSES];
    // for i in 1..NUM_WITNESSES {
    //     ark_omega_pow_list[i] = ark_omega_pow_list[i - 1] * ark_omega;
    // }
    // let ark_permutation_witness_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> =
    //     permutation_witnesses
    //         .iter()
    //         .map(|witness| witness.poly_eval_list_f.clone())
    //         .collect::<Vec<_>>();
    //
    // let mut ark_adjusted_permutation_witness_values = ark_permutation_witness_values
    //     .iter()
    //     .map(|witness| {
    //         let mut modified_witness = witness.clone();
    //         for i in 0..NUM_WITNESSES {
    //             modified_witness[i] = witness[i] * ark_omega_pow_list[i];
    //         }
    //         modified_witness
    //     })
    //     .collect::<Vec<_>>();
    //
    // for (i, witness) in ark_adjusted_permutation_witness_values
    //     .iter_mut()
    //     .enumerate()
    // {
    //     witness[NUM_USABLE_WITNESSES..NUM_WITNESSES]
    //         .copy_from_slice(&permutation_witness_value_paddings[i]);
    // }
    //
    // let ark_adjusted_permutation_witness_poly_coeff_list = ark_adjusted_permutation_witness_values
    //     .iter()
    //     .map(|witness| lookup_params.domain_v.ifft(witness))
    //     .collect::<Vec<_>>();
    //
    // let adjusted_permutation_statements = ark_adjusted_permutation_witness_poly_coeff_list
    //     .iter()
    //     .map(|coeff_list| {
    //         let poly = DensePolynomial::from_coefficients_slice(coeff_list);
    //         let ark_com =
    //             Kzg::<<Bn254 as Pairing>::G1>::commit(&lookup_params.g1_affine_srs, &poly)
    //                 .into_affine();
    //
    //         ark_to_halo2_g1_affine(&ark_com)
    //     })
    //     .collect::<Vec<_>>();
    //
    // let adjusted_permutation_witness_values = ark_adjusted_permutation_witness_values
    //     .iter()
    //     .map(|witness| batch_ark_to_halo2_scalar_field(witness))
    //     .collect::<Vec<_>>();
    //
    // let pk = generate_proving_key(
    //     &halo2_params,
    //     &queried_circuit_indices,
    //     &fixed_statements,
    //     &adjusted_permutation_statements,
    //     &fixed_witnesses,
    //     &adjusted_permutation_witness_values,
    // );
    // let halo2_omega = pk.get_vk().get_domain().get_omega();
    // assert_eq!(ark_to_halo2_scalar_field(&ark_omega), halo2_omega);

    let left_values = vec![Fr::from(2); NUM_USABLE_WITNESSES];
    let right_values = vec![Fr::from(3); NUM_USABLE_WITNESSES];
    let public_inputs = (0..NUM_USABLE_WITNESSES)
        .map(|i| match queried_circuit_indices[i] {
            0 => left_values[i] + right_values[i],
            1 => left_values[i] * right_values[i],
            _ => panic!("Invalid circuit index"),
        })
        .collect::<Vec<_>>();

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
    println!(
        "Prover time: {} ms",
        curr_time.elapsed().unwrap().as_millis()
    );

    let curr_time = std::time::SystemTime::now();
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
    println!(
        "Verifier time: {} ms",
        curr_time.elapsed().unwrap().as_millis()
    );
}
