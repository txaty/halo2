use halo2_backend::poly::kzg::commitment::ParamsKZG;
use halo2_proofs::arithmetic::{parallelize, Field};
use halo2curves::bn256::{Bn256, Fr, G1Affine, G2Affine, G1};
use halo2curves::ff::PrimeField;
use halo2curves::group::prime::PrimeCurveAffine;
use halo2curves::group::{Curve, Group};

pub(crate) fn halo2_kzg_params_from_tau(k: u32, tau: Fr) -> ParamsKZG<Bn256> {
    // Largest root of unity exponent of the Engine is `2^E::Fr::S`, so we can
    // only support FFTs of polynomials below degree `2^E::Fr::S`.
    assert!(k <= Fr::S);
    let n: u64 = 1 << k;

    // Calculate g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1] in parallel.
    let g1 = G1Affine::generator();

    let mut g_projective = vec![G1::identity(); n as usize];
    parallelize(&mut g_projective, |g, start| {
        let mut current_g: G1 = g1.into();
        current_g *= tau.pow_vartime([start as u64]);
        for g in g.iter_mut() {
            *g = current_g;
            current_g *= tau;
        }
    });

    let g = {
        let mut g = vec![G1Affine::identity(); n as usize];
        parallelize(&mut g, |g, starts| {
            G1::batch_normalize(&g_projective[starts..(starts + g.len())], g);
        });
        g
    };

    let g2 = <G2Affine as PrimeCurveAffine>::generator();
    let s_g2 = (g2 * tau).into();

    ParamsKZG::<Bn256>::from_parts(k, g, None, g2, s_g2)
}
