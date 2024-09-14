use crate::bn254_convert::{
    ark_to_halo2_scalar_field, batch_halo2_to_ark_scalar, halo2_to_ark_scalar,
};
use crate::kzg_params::halo2_kzg_params_from_tau;
use crate::parameters::{NUM_USABLE_WITNESSES, NUM_WITNESSES};
use crate::plonk_circuit::{CircuitEnum, WitnessCircuit};
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_std::UniformRand;
use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_frontend::plonk::ConstraintSystem;
use halo2_frontend::sublonk::compile_witness_cs;
use halo2_middleware::circuit::ConstraintSystemMid;
use halo2_proofs::plonk::{keygen_pk, keygen_vk, sublonk_preprocess_poly_coeff_list};
use halo2curves::bn256::{Bn256, Fr};
use rand_core::OsRng;

pub fn preprocess(
    num_table_circuits: usize,
    num_witnesses: usize,
    k: u32,
    sub_circuit_k: u32,
    circuits: &[CircuitEnum<Fr>],
    witness_circuit: &WitnessCircuit<Fr>,
) -> (
    ParamsKZG<Bn256>,
    PublicParameters<Bn254>,
    Vec<Table<Bn254>>,
    Vec<Table<Bn254>>,
    Vec<TablePreprocessedParameters<Bn254>>,
    Vec<TablePreprocessedParameters<Bn254>>,
    ConstraintSystemMid<Fr>,
    Vec<Vec<<Bn254 as Pairing>::ScalarField>>,
) {
    let ark_tau = <Bn254 as Pairing>::ScalarField::rand(&mut OsRng);
    let halo2_tau = ark_to_halo2_scalar_field(&ark_tau);
    let halo2_params: ParamsKZG<Bn256> = halo2_kzg_params_from_tau(k, halo2_tau);

    let segment_size = 1 << sub_circuit_k;

    // TODO: Optimize this
    let vk = keygen_vk(&halo2_params, witness_circuit).unwrap();
    let pk = keygen_pk(&halo2_params, vk.clone(), witness_circuit).unwrap();
    let halo2_omega = vk.get_domain().get_omega();
    let ark_omega = halo2_to_ark_scalar(&halo2_omega);

    let lookup_params = PublicParameters::setup_with_tau_and_group_generator(
        num_table_circuits,
        num_witnesses,
        segment_size,
        ark_tau,
        ark_omega,
    )
    .unwrap();
    
    let witness_constraint_system = compile_witness_cs(k, witness_circuit).unwrap();

    let (fixed_lookup_tables, permutation_lookup_tables) = build_segment_lookup_table(
        sub_circuit_k,
        &halo2_params,
        &lookup_params,
        circuits,
        &witness_constraint_system,
    );

    let fixed_tpp_list = fixed_lookup_tables
        .iter()
        .map(|table| table.preprocess(&lookup_params).unwrap())
        .collect::<Vec<_>>();
    let permutation_tpp_list = permutation_lookup_tables
        .iter()
        .map(|table| table.preprocess(&lookup_params).unwrap())
        .collect::<Vec<_>>();

    let permutation_witness_value_paddings = pk
        .permutation
        .permutations
        .iter()
        .map(|poly| {
            let padding =
                batch_halo2_to_ark_scalar(&poly.values[NUM_USABLE_WITNESSES..NUM_WITNESSES]);

            padding
        })
        .collect::<Vec<_>>();

    (
        halo2_params,
        lookup_params,
        fixed_lookup_tables,
        permutation_lookup_tables,
        fixed_tpp_list,
        permutation_tpp_list,
        witness_constraint_system.into(),
        permutation_witness_value_paddings,
    )
}

pub(crate) fn build_segment_lookup_table(
    sub_circuit_k: u32,
    poly_commit_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    circuits: &[CircuitEnum<Fr>],
    cs: &ConstraintSystem<Fr>,
) -> (Vec<Table<Bn254>>, Vec<Table<Bn254>>) {
    if circuits.is_empty() {
        panic!("No circuits provided to build lookup table");
    }

    let (fixed_poly_coeff_list, permutation_poly_coeff_list): (Vec<_>, Vec<_>) = circuits
        .iter()
        .map(|circuit| match circuit {
            CircuitEnum::Add(circuit) => {
                sublonk_preprocess_poly_coeff_list(sub_circuit_k, poly_commit_params, circuit)
                    .unwrap()
            }
            CircuitEnum::Mul(circuit) => {
                sublonk_preprocess_poly_coeff_list(sub_circuit_k, poly_commit_params, circuit)
                    .unwrap()
            }
            CircuitEnum::PlaceHolder => (
                vec![vec![Fr::zero(); 1 << sub_circuit_k]; cs.num_fixed_columns()],
                vec![vec![Fr::zero(); 1 << sub_circuit_k]; cs.permutation.get_columns().len()], 
                // TODO: Optimize this
            ),
        })
        .unzip();

    let fixed_lookup_tables = batch_build_lookup_tables(&fixed_poly_coeff_list, &lookup_params);
    let permutation_lookup_tables =
        batch_build_lookup_tables(&permutation_poly_coeff_list, &lookup_params);

    (fixed_lookup_tables, permutation_lookup_tables)
}

fn batch_build_lookup_tables(
    poly_coeff_list: &[Vec<Vec<Fr>>],
    lookup_params: &PublicParameters<Bn254>,
) -> Vec<Table<Bn254>> {
    (0..poly_coeff_list[0].len())
        .map(|i| {
            let poly_coeff_segments: Vec<_> = poly_coeff_list
                .iter()
                .map(|coeff_list| coeff_list[i].clone())
                .collect();

            let ark_segment_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> = poly_coeff_segments
                .iter()
                .map(|coeffs| coeffs.iter().map(halo2_to_ark_scalar).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            let table = Table::new(lookup_params, ark_segment_values).unwrap();

            table
        })
        .collect()
}
