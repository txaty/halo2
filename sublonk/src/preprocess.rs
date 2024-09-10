use crate::bn254_convert::halo2_to_ark_scalar;
use crate::plonk_circuit::CircuitEnum;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::Table;
use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_proofs::plonk::sublonk_preprocess_poly_coeffs;
use halo2curves::bn256::{Bn256, Fr};

pub(crate) fn build_segment_lookup_table(
    poly_commit_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    circuits: &[CircuitEnum<Fr>],
) -> (Vec<Table<Bn254>>, Vec<Table<Bn254>>) {
    if circuits.is_empty() {
        panic!("No circuits provided to build lookup table");
    }

    let mut fixed_poly_coeffs_list = Vec::new();
    let mut permutation_poly_coeffs_list = Vec::new();

    // let poly_coeffs_list: Vec<_> = circuits
    //     .iter()
    //     .map(|circuit| match circuit {
    //         CircuitEnum::Add(circuit) => {
    //             sublonk_preprocess_poly_coeffs(poly_commit_params, circuit).unwrap()
    //         }
    //         CircuitEnum::Mul(circuit) => {
    //             sublonk_preprocess_poly_coeffs(poly_commit_params, circuit).unwrap()
    //         }
    //     })
    //     .collect();

    for circuit in circuits {
        match circuit {
            CircuitEnum::Add(circuit) => {
                let (fixed_poly_coeffs, permutation_poly_coeffs) =
                    sublonk_preprocess_poly_coeffs(poly_commit_params, circuit).unwrap();
                fixed_poly_coeffs_list.push(fixed_poly_coeffs);
                permutation_poly_coeffs_list.push(permutation_poly_coeffs);
            }
            CircuitEnum::Mul(circuit) => {
                let (fixed_poly_coeffs, permutation_poly_coeffs) =
                    sublonk_preprocess_poly_coeffs(poly_commit_params, circuit).unwrap();
                fixed_poly_coeffs_list.push(fixed_poly_coeffs);
                permutation_poly_coeffs_list.push(permutation_poly_coeffs);
            }
        }
    }

    let num_fixed_tables = fixed_poly_coeffs_list[0].len();
    let mut fixed_lookup_tables: Vec<Table<Bn254>> = Vec::new();
    for i in 0..num_fixed_tables {
        let poly_coeff_segments: Vec<_> = fixed_poly_coeffs_list
            .iter()
            .map(|coeffs| coeffs[i].clone())
            .collect();

        let ark_segment_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> = poly_coeff_segments
            .iter()
            .map(|coeffs| {
                coeffs
                    .iter()
                    .map(|coeff| halo2_to_ark_scalar(coeff))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // println!("segment values len: {:?}", ark_segment_values.len());
        // for j in 0..ark_segment_values.len() {
        //     println!(
        //         "segment values[{}] len: {:?}",
        //         j,
        //         ark_segment_values[j].len()
        //     );
        //     for k in 0..ark_segment_values[j].len() {
        //         println!(
        //             "segment values[{}][{}]: {:?}",
        //             j, k, ark_segment_values[j][k]
        //         );
        //     }
        // }

        let table = Table::new(&lookup_params, ark_segment_values).unwrap();
        table.preprocess(&lookup_params).unwrap();
        fixed_lookup_tables.push(table);
    }

    let num_permutation_tables = permutation_poly_coeffs_list[0].len();
    let mut permutation_lookup_tables: Vec<Table<Bn254>> = Vec::new();
    for i in 0..num_permutation_tables {
        let poly_coeff_segments: Vec<_> = permutation_poly_coeffs_list
            .iter()
            .map(|coeffs| coeffs[i].clone())
            .collect();

        let ark_segment_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> = poly_coeff_segments
            .iter()
            .map(|coeffs| {
                coeffs
                    .iter()
                    .map(|coeff| halo2_to_ark_scalar(coeff))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let table = Table::new(&lookup_params, ark_segment_values).unwrap();
        table.preprocess(&lookup_params).unwrap();
        permutation_lookup_tables.push(table);
    }

    (fixed_lookup_tables, permutation_lookup_tables)
}
