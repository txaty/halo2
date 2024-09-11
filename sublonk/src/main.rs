mod bn254_convert;
mod kzg_params;
mod plonk_circuit;
mod preprocess;
mod prover;
mod verifier;

use crate::bn254_convert::ark_to_halo2_scalar_field;
use crate::kzg_params::halo2_kzg_params_from_tau;
use crate::plonk_circuit::{AddCircuit, CircuitEnum, MulCircuit, TwoFanInCircuit};
use crate::preprocess::build_segment_lookup_table;
use crate::prover::prover;
use crate::verifier::verifier;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_std::UniformRand;
use halo2_backend::plonk::ProvingKey;
use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_frontend::circuit::Value;
use halo2_middleware::halo2curves::bn256::{Bn256, Fr, G1Affine};
use halo2_proofs::plonk::{sublonk_keygen_pk, sublonk_keygen_vk};
use rand_core::OsRng;

fn keygen(
    k: u32,
    num_table_segments: usize,
    num_witness_segments: usize,
    circuits: &[CircuitEnum<Fr>],
) -> (
    ParamsKZG<Bn256>,
    PublicParameters<Bn254>,
    Vec<ProvingKey<G1Affine>>,
) {
    let ark_tau = <Bn254 as Pairing>::ScalarField::rand(&mut OsRng);
    let halo2_tau = ark_to_halo2_scalar_field(ark_tau);
    let params: ParamsKZG<Bn256> = halo2_kzg_params_from_tau(k, halo2_tau);

    let segment_size = 1 << k;
    let lookup_pp = PublicParameters::setup_with_tau(
        num_table_segments,
        num_witness_segments,
        segment_size,
        ark_tau,
    )
    .unwrap();

    let mut pk_list = Vec::with_capacity(circuits.len());
    for circuit in circuits {
        let vk = sublonk_keygen_vk(&params, circuit).unwrap();
        let pk = sublonk_keygen_pk(&params, vk, circuit).unwrap();
        pk_list.push(pk);
    }

    (params, lookup_pp, pk_list)
}

fn main() {
    let k: u32 = 3;

    let curr_time = std::time::SystemTime::now();
    let add_circuit = AddCircuit {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
        k,
    };
    let mul_circuit = MulCircuit {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
        k,
    };
    let circuits = vec![CircuitEnum::Add(add_circuit), CircuitEnum::Mul(mul_circuit)];

    let (kzg_params, lookup_pp, pk_list) = keygen(k, 2, 1, &circuits);

    let (fixed_lookup_tables, permutation_lookup_tables) =
        build_segment_lookup_table(&kzg_params, &lookup_pp, &circuits);
    let fixed_tpp_list = fixed_lookup_tables
        .iter()
        .map(|table| table.preprocess(&lookup_pp).unwrap())
        .collect::<Vec<_>>();
    let permutation_tpp_list = permutation_lookup_tables
        .iter()
        .map(|table| table.preprocess(&lookup_pp).unwrap())
        .collect::<Vec<_>>();
    println!(
        "Preprocessing Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );

    let a = Fr::from(3);
    let b = Fr::from(4);
    let public_input = Fr::from(7);

    println!("Add Circuit");
    let pk = &pk_list[0];
    let curr_time = std::time::SystemTime::now();
    let (proof, fixed_proofs, permutation_proofs, fixed_statements, permutation_statements) =
        prover::<AddCircuit<_>>(
            k,
            &kzg_params,
            &pk,
            a,
            b,
            public_input,
            &lookup_pp,
            &fixed_lookup_tables,
            &permutation_lookup_tables,
            &fixed_tpp_list,
            &permutation_tpp_list,
            0,
        );
    println!(
        "Proving Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );
    let curr_time = std::time::SystemTime::now();
    verifier(
        &kzg_params,
        &pk.get_sublonk_vk(),
        proof.as_ref(),
        public_input,
        &lookup_pp,
        &fixed_tpp_list,
        &permutation_tpp_list,
        &fixed_proofs,
        &permutation_proofs,
        &fixed_statements,
        &permutation_statements,
    );
    println!(
        "Verification Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );

    let a = Fr::from(2);
    let b = Fr::from(5);
    let public_input = Fr::from(10);

    println!("Mul Circuit");
    let pk = &pk_list[1];
    let curr_time = std::time::SystemTime::now();
    let (proof, fixed_proofs, permutation_proofs, fixed_statements, permutation_statements) =
        prover::<MulCircuit<_>>(
            k,
            &kzg_params,
            &pk,
            a,
            b,
            public_input,
            &lookup_pp,
            &fixed_lookup_tables,
            &permutation_lookup_tables,
            &fixed_tpp_list,
            &permutation_tpp_list,
            1,
        );
    println!(
        "Proving Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );

    let curr_time = std::time::SystemTime::now();
    verifier(
        &kzg_params,
        &pk.get_sublonk_vk(),
        proof.as_ref(),
        public_input,
        &lookup_pp,
        &fixed_tpp_list,
        &permutation_tpp_list,
        &fixed_proofs,
        &permutation_proofs,
        &fixed_statements,
        &permutation_statements,
    );
    println!(
        "Verification Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );
}
