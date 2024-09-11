use crate::bn254_convert::halo2_to_ark_scalar;
use crate::plonk_circuit::CircuitEnum;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::Table;
use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_proofs::plonk::sublonk_preprocess_poly_coeff_list;
use halo2curves::bn256::{Bn256, Fr};

pub(crate) fn build_segment_lookup_table(
    poly_commit_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    circuits: &[CircuitEnum<Fr>],
) -> (Vec<Table<Bn254>>, Vec<Table<Bn254>>) {
    if circuits.is_empty() {
        panic!("No circuits provided to build lookup table");
    }

    let mut fixed_poly_coeff_list = Vec::new();
    let mut permutation_poly_coeff_list = Vec::new();

    for circuit in circuits {
        match circuit {
            CircuitEnum::Add(circuit) => {
                let (fixed_poly_coeffs, permutation_poly_coeffs) =
                    sublonk_preprocess_poly_coeff_list(poly_commit_params, circuit).unwrap();
                fixed_poly_coeff_list.push(fixed_poly_coeffs);
                permutation_poly_coeff_list.push(permutation_poly_coeffs);
            }
            CircuitEnum::Mul(circuit) => {
                let (fixed_poly_coeffs, permutation_poly_coeffs) =
                    sublonk_preprocess_poly_coeff_list(poly_commit_params, circuit).unwrap();
                fixed_poly_coeff_list.push(fixed_poly_coeffs);
                permutation_poly_coeff_list.push(permutation_poly_coeffs);
            }
        }
    }

    let fixed_lookup_tables: Vec<Table<Bn254>> = (0..fixed_poly_coeff_list[0].len())
        .map(|i| {
            let poly_coeff_segments: Vec<_> = fixed_poly_coeff_list
                .iter()
                .map(|coeffs| coeffs[i].clone())
                .collect();

            let ark_segment_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> = poly_coeff_segments
                .iter()
                .map(|coeffs| coeffs.iter().map(halo2_to_ark_scalar).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            let mut table = Table::new(&lookup_params, ark_segment_values).unwrap();
            table.preprocess(&lookup_params).unwrap();
            table
        })
        .collect();

    let permutation_lookup_tables: Vec<Table<Bn254>> = (0..permutation_poly_coeff_list[0].len())
        .map(|i| {
            let poly_coeff_segments: Vec<_> = permutation_poly_coeff_list
                .iter()
                .map(|coeffs| coeffs[i].clone())
                .collect();

            let ark_segment_values: Vec<Vec<<Bn254 as Pairing>::ScalarField>> = poly_coeff_segments
                .iter()
                .map(|coeffs| coeffs.iter().map(halo2_to_ark_scalar).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            let mut table = Table::new(&lookup_params, ark_segment_values).unwrap();
            table.preprocess(&lookup_params).unwrap();
            table
        })
        .collect();

    (fixed_lookup_tables, permutation_lookup_tables)
}
