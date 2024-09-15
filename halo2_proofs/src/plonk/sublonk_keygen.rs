use crate::arithmetic::CurveAffine;
use crate::plonk::Error;

use halo2_backend::plonk::sublonk_keygen::{
    keygen_pk, keygen_vk, preprocessing_polynomial_coefficients,
};
use halo2_backend::plonk::{ProvingKey, VerifyingKey};
use halo2_backend::poly::commitment::Params;
use halo2_frontend::circuit::compile_circuit;
use halo2_frontend::plonk::Circuit;
use halo2_frontend::sublonk::compile_sub_circuit;
use halo2_middleware::ff::FromUniformBytes;

/// Generate a `VerifyingKey` from an instance of `Circuit`.
/// By default, selector compression is turned **ON**.
///
/// **NOTE**: This `keygen_vk` is legacy one, assuming that `compress_selector: true`.
/// Hence, it is HIGHLY recommended to pair this util with `keygen_pk`.
/// In addition, when using this for key generation, user MUST use `compress_selectors: true`.
pub fn sublonk_keygen_vk<C, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
    fixed_statements: &[C],
    adjusted_permutation_statements: &[C],
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>,
{
    sublonk_keygen_vk_custom(
        params,
        circuit,
        true,
        fixed_statements,
        adjusted_permutation_statements,
    )
}

/// Generate a `VerifyingKey` from an instance of `Circuit`.
///
/// The selector compression optimization is turned on only if `compress_selectors` is `true`.
///
/// **NOTE**: This `keygen_vk_custom` MUST share the same `compress_selectors` with
/// `ProvingKey` generation process.
/// Otherwise, the user could get unmatching pk/vk pair.
/// Hence, it is HIGHLY recommended to pair this util with `keygen_pk_custom`.
pub fn sublonk_keygen_vk_custom<C, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
    compress_selectors: bool,
    fixed_statements: &[C],
    permutation_statements: &[C],
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>,
{
    let (compiled_circuit, _, _) = compile_circuit(params.k(), circuit, compress_selectors)?;

    Ok(keygen_vk(
        params,
        &compiled_circuit,
        fixed_statements,
        permutation_statements,
    )?)
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `Circuit`.
/// By default, selector compression is turned **ON**.
///
/// **NOTE**: This `keygen_pk` is legacy one, assuming that `compress_selector: true`.
/// Hence, it is HIGHLY recommended to pair this util with `keygen_vk`.
/// In addition, when using this for key generation, user MUST use `compress_selectors: true`.
pub fn sublonk_keygen_pk<C, P>(
    params: &P,
    vk: VerifyingKey<C>,
    fixed_witnesses: &[Vec<C::Scalar>],
    permutation_witnesses: &[Vec<C::Scalar>],
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
{
    sublonk_keygen_pk_custom::<C, P>(params, vk, fixed_witnesses, permutation_witnesses)
}

/// Generate a `ProvingKey` from an instance of `Circuit`.
///
/// The selector compression optimization is turned on only if `compress_selectors` is `true`.
///
/// **NOTE**: This `keygen_pk_custom` MUST share the same `compress_selectors` with
/// `VerifyingKey` generation process.
/// Otherwise, the user could get unmatching pk/vk pair.
/// Hence, it is HIGHLY recommended to pair this util with `keygen_vk_custom`.
pub fn sublonk_keygen_pk_custom<C, P>(
    params: &P,
    vk: VerifyingKey<C>,
    fixed_witnesses: &[Vec<C::Scalar>],
    permutation_witnesses: &[Vec<C::Scalar>],
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
{
    Ok(keygen_pk(
        params,
        vk,
        fixed_witnesses,
        permutation_witnesses,
    )?)
}

/// Generate a list of polynomial coefficients from an instance of `Circuit`.
pub fn sublonk_preprocess_poly_coeff_list<C, P, ConcreteCircuit>(
    sub_circuit_k: u32,
    params: &P,
    circuit: &ConcreteCircuit,
) -> Result<(Vec<Vec<C::Scalar>>, Vec<Vec<C::Scalar>>), Error>
where
    C: CurveAffine,
    P: Params<C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>,
{
    let (compiled_circuit, _, _) = compile_sub_circuit(sub_circuit_k, circuit, true)?;

    let (fixed_poly_coeff_list, permutation_poly_coeff_list) =
        preprocessing_polynomial_coefficients(sub_circuit_k, params, &compiled_circuit)?;

    // println!("fixed_poly_coeff_list: {:?}", fixed_poly_coeff_list);
    // println!(
    //     "permutation_poly_coeff_list: {:?}",
    //     permutation_poly_coeff_list
    // );

    Ok((fixed_poly_coeff_list, permutation_poly_coeff_list))
}
