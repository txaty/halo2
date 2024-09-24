use crate::bn254_convert::{
    ark_to_halo2_scalar_field, batch_halo2_to_ark_scalar, halo2_to_ark_scalar,
};
use crate::config::{Config, NUM_UNUSABLE_ROWS, SEGMENT_SIZE};
use crate::kzg_params::halo2_kzg_params_from_tau;
use crate::multi_row_circuit::{CircuitEnum64, WitnessCircuit64};
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};
use ark_segmentlookup::kzg::Kzg;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_std::{test_rng, UniformRand, Zero};
use halo2_backend::plonk::keygen::{
    keygen_pk as backend_keygen_pk, keygen_vk as backend_keygen_vk,
};
use halo2_backend::poly::commitment::Params;
use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_frontend::circuit::compile_circuit;
use halo2_frontend::plonk::ConstraintSystem;
use halo2_middleware::circuit::ConstraintSystemMid;
use halo2_proofs::plonk::sublonk_preprocess_poly_coeff_list;
use halo2curves::bn256::{Bn256, Fr};
use rayon::prelude::*;

pub fn preprocess(
    config: &Config,
    circuits: &[CircuitEnum64<Fr>],
    witness_circuit: &WitnessCircuit64<Fr>,
) -> (
    ParamsKZG<Bn256>,
    PublicParameters<Bn254>,
    Vec<Table<Bn254>>,
    Vec<Table<Bn254>>,
    Vec<TablePreprocessedParameters<Bn254>>,
    Vec<TablePreprocessedParameters<Bn254>>,
    ConstraintSystemMid<Fr>,
    Vec<Vec<<Bn254 as Pairing>::ScalarField>>,
    DensePolynomial<<Bn254 as Pairing>::ScalarField>,
    Vec<DensePolynomial<<Bn254 as Pairing>::ScalarField>>,
    <Bn254 as Pairing>::G2Affine,
    Vec<<Bn254 as Pairing>::G1Affine>,
) {
    let mut rng = test_rng();
    let ark_tau = <Bn254 as Pairing>::ScalarField::rand(&mut rng);
    let halo2_tau = ark_to_halo2_scalar_field(&ark_tau);
    
    let k = config.pow_witness_size as u32;
    let halo2_params: ParamsKZG<Bn256> = halo2_kzg_params_from_tau(k, halo2_tau);

    let segment_size = config.segment_size;

    let (compiled_circuit, _, witness_cs) =
        compile_circuit(halo2_params.k(), witness_circuit, true).unwrap();
    let vk = backend_keygen_vk(&halo2_params, &compiled_circuit).unwrap();
    let pk = backend_keygen_pk(&halo2_params, vk.clone(), &compiled_circuit).unwrap();

    let halo2_omega = vk.get_domain().get_omega();
    let ark_omega = halo2_to_ark_scalar(&halo2_omega);

    let num_table_circuits = config.num_table_circuits;
    let num_witness_circuits = config.num_witness_circuits;
    
    let lookup_params = PublicParameters::builder()
        .num_table_segments(num_table_circuits)
        .num_witness_segments(num_witness_circuits)
        .segment_size(segment_size)
        .tau(ark_tau)
        .domain_generator_v(ark_omega)
        .build(&mut rng)
        .unwrap();

    let sub_circuit_k = config.pow_segment_size as u32;
    
    let (fixed_lookup_tables, permutation_lookup_tables) = build_segment_lookup_table(
        sub_circuit_k,
        &halo2_params,
        &lookup_params,
        circuits,
        &witness_cs,
    );

    let fixed_tpp_list = fixed_lookup_tables
        .par_iter()
        .map(|table| table.preprocess(&lookup_params).unwrap())
        .collect::<Vec<_>>();
    let permutation_tpp_list = permutation_lookup_tables
        .par_iter()
        .map(|table| table.preprocess(&lookup_params).unwrap())
        .collect::<Vec<_>>();

    let witness_size = config.witness_size;
    let usable_witnesses_size = witness_size - NUM_UNUSABLE_ROWS;

    let permutation_witness_value_paddings = pk
        .permutation
        .permutations
        .par_iter()
        .map(|poly| {
            let padding =
                batch_halo2_to_ark_scalar(&poly.values[usable_witnesses_size..witness_size]);

            padding
        })
        .collect::<Vec<_>>();

    let permutation_padding_poly_eval_list: Vec<Vec<<Bn254 as Pairing>::ScalarField>> =
        permutation_witness_value_paddings
            .par_iter()
            .map(|padding| {
                let mut eval_list = vec![<Bn254 as Pairing>::ScalarField::zero(); witness_size];
                eval_list[usable_witnesses_size..witness_size].copy_from_slice(padding);

                eval_list
            })
            .collect();

    let poly_permutation_padding_list = permutation_padding_poly_eval_list
        .par_iter()
        .map(|eval_list| {
            DensePolynomial::from_coefficients_vec(lookup_params.domain_v.ifft(eval_list))
        })
        .collect::<Vec<_>>();

    let g1_affine_list_permutation_padding = poly_permutation_padding_list
        .par_iter()
        .map(|poly| {
            let ark_com = Kzg::<<Bn254 as Pairing>::G1>::commit(&lookup_params.g1_affine_srs, poly)
                .into_affine();

            ark_com
        })
        .collect::<Vec<_>>();

    let poly_eval_list_u: Vec<<Bn254 as Pairing>::ScalarField> = lookup_params
        .domain_k
        .elements()
        .flat_map(|root_of_unity_k| std::iter::repeat(root_of_unity_k).take(SEGMENT_SIZE))
        .collect();
    let poly_coeff_list_u = lookup_params.domain_v.ifft(&poly_eval_list_u);
    let poly_u = DensePolynomial::from_coefficients_vec(poly_coeff_list_u);
    let g2_u =
        Kzg::<<Bn254 as Pairing>::G2>::commit(&lookup_params.g2_affine_srs, &poly_u).into_affine();

    (
        halo2_params,
        lookup_params,
        fixed_lookup_tables,
        permutation_lookup_tables,
        fixed_tpp_list,
        permutation_tpp_list,
        witness_cs.into(),
        permutation_witness_value_paddings,
        poly_u,
        poly_permutation_padding_list,
        g2_u,
        g1_affine_list_permutation_padding,
    )
}

pub(crate) fn build_segment_lookup_table(
    sub_circuit_k: u32,
    poly_commit_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    circuits: &[CircuitEnum64<Fr>],
    cs: &ConstraintSystem<Fr>,
) -> (Vec<Table<Bn254>>, Vec<Table<Bn254>>) {
    if circuits.is_empty() {
        panic!("No circuits provided to build lookup table");
    }

    let domain_v_generator = ark_to_halo2_scalar_field(&lookup_params.domain_v.group_gen);

    let (fixed_poly_coeff_list, permutation_poly_coeff_list): (Vec<_>, Vec<_>) = circuits
        .par_iter()
        .map(|circuit| match circuit {
            CircuitEnum64::Add(circuit) => sublonk_preprocess_poly_coeff_list(
                sub_circuit_k,
                poly_commit_params,
                domain_v_generator,
                circuit,
            )
            .unwrap(),
            CircuitEnum64::Mul(circuit) => sublonk_preprocess_poly_coeff_list(
                sub_circuit_k,
                poly_commit_params,
                domain_v_generator,
                circuit,
            )
            .unwrap(),
            CircuitEnum64::PlaceHolder => (
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
                .par_iter()
                .map(|coeff_list| coeff_list[i].clone())
                .collect();

            let ark_segment_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> = poly_coeff_segments
                .par_iter()
                .map(|coeff_list| {
                    coeff_list
                        .iter()
                        .map(halo2_to_ark_scalar)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            let table = Table::new(lookup_params, ark_segment_values).unwrap();

            table
        })
        .collect()
}
