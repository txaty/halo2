use ark_bn254::Bn254;
use ark_bn254::Fq2 as ArkFq2;
use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger256, Field};
use halo2_backend::arithmetic::CurveAffine;
use halo2curves::bn256::{Fq, Fq2, Fr, G1Affine, G2Affine};

pub fn ark_to_halo2_g1_affine(p: &<Bn254 as Pairing>::G1Affine) -> G1Affine {
    let halo2_fq_x = ark_to_halo2_base_field(p.x);
    let halo2_fq_y = ark_to_halo2_base_field(p.y);

    G1Affine::from_xy(halo2_fq_x, halo2_fq_y).unwrap()
}

pub fn ark_to_halo2_base_field(f: <Bn254 as Pairing>::BaseField) -> Fq {
    let bi: BigInteger256 = f.into();
    let u64_4 = bi.0;

    Fq::from_raw(u64_4)
}

pub fn ark_to_halo2_g2_affine(p: &<Bn254 as Pairing>::G2Affine) -> G2Affine {
    let halo2_fq_x_c0 = ark_to_halo2_base_field(p.x.c0);
    let halo2_fq_x_c1 = ark_to_halo2_base_field(p.x.c1);
    let halo2_fq2_x = Fq2::new(halo2_fq_x_c0, halo2_fq_x_c1);

    let halo2_fq_y_c0 = ark_to_halo2_base_field(p.y.c0);
    let halo2_fq_y_c1 = ark_to_halo2_base_field(p.y.c1);
    let halo2_fq2_y = Fq2::new(halo2_fq_y_c0, halo2_fq_y_c1);

    G2Affine::from_xy(halo2_fq2_x, halo2_fq2_y).unwrap()
}

pub fn ark_to_halo2_scalar_field(s: <Bn254 as Pairing>::ScalarField) -> Fr {
    let bi_s: BigInteger256 = s.into();
    let u64_4_s = bi_s.0;

    Fr::from_raw(u64_4_s)
}

pub fn halo2_to_ark_g1_affine(p: &G1Affine) -> <Bn254 as Pairing>::G1Affine {
    let fq_x = halo2_to_ark_base_field(p.x);
    let fq_y = halo2_to_ark_base_field(p.y);

    <Bn254 as Pairing>::G1Affine::new(fq_x, fq_y)
}

pub fn halo2_to_ark_base_field(f: Fq) -> <Bn254 as Pairing>::BaseField {
    let u8_32 = f.to_bytes();
    let u64_4 = u64_4_from_u8_32(&u8_32);
    let bi = BigInteger256::new(u64_4);

    <Bn254 as Pairing>::BaseField::new(bi)
}

fn u64_4_from_u8_32(v: &[u8; 32]) -> [u64; 4] {
    let mut result = [0u64; 4];
    for (i, chunk) in v.chunks(8).enumerate() {
        result[i] = u64::from_le_bytes(chunk.try_into().expect("slice with incorrect length"));
    }

    result
}

pub fn halo2_to_ark_g2_affine(p: &G2Affine) -> <Bn254 as Pairing>::G2Affine {
    let u8_64_x_c0 = p.x.to_bytes();
    let fq_x_c0 = <Bn254 as Pairing>::BaseField::from_random_bytes(&u8_64_x_c0).unwrap();

    let u8_32_x_c1 = p.x.c1.to_bytes();
    let fq_x_c1 = <Bn254 as Pairing>::BaseField::from_random_bytes(&u8_32_x_c1).unwrap();

    let fq2_x = ArkFq2::new(fq_x_c0, fq_x_c1);

    let u8_32_y_c0 = p.y.c0.to_bytes();
    let fq_y_c0 = <Bn254 as Pairing>::BaseField::from_random_bytes(&u8_32_y_c0).unwrap();

    let u8_32_y_c1 = p.y.c1.to_bytes();
    let fq_y_c1 = <Bn254 as Pairing>::BaseField::from_random_bytes(&u8_32_y_c1).unwrap();

    let fq2_y = ArkFq2::new(fq_y_c0, fq_y_c1);

    <Bn254 as Pairing>::G2Affine::new(fq2_x, fq2_y)
}

pub fn halo2_to_ark_scalar(s: Fr) -> <Bn254 as Pairing>::ScalarField {
    let u8_32_s = s.to_bytes();
    let u64_4_s = u64_4_from_u8_32(&u8_32_s);
    let bi_s = BigInteger256::new(u64_4_s);

    <Bn254 as Pairing>::ScalarField::new(bi_s)
}

#[cfg(test)]
mod tests {
    use std::ops::Mul;

    use ark_bn254::Bn254;
    use ark_ec::CurveGroup;
    use ark_ff::BigInteger;
    use ark_std::{test_rng, UniformRand};
    use halo2curves::bn256::Bn256;
    use halo2curves::ff::Field;
    use halo2curves::group::Curve;
    use halo2curves::pairing::Engine;

    use super::*;

    fn assert_eq_ark_and_halo2_g1_affine(p1: &<Bn254 as Pairing>::G1Affine, p2: &G1Affine) {
        let p1_x: BigInteger256 = p1.x.into();
        assert_eq!(p1_x.to_bytes_le(), p2.x.to_bytes());

        let p1_y: BigInteger256 = p1.y.into();
        assert_eq!(p1_y.to_bytes_le(), p2.y.to_bytes());
    }

    fn assert_eq_ark_and_halo2_g2_affine(p1: &<Bn254 as Pairing>::G2Affine, p2: &G2Affine) {
        let p1_x_c0: BigInteger256 = p1.x.c0.into();
        assert_eq!(p1_x_c0.to_bytes_le(), p2.x.c0.to_bytes());

        let p1_x_c1: BigInteger256 = p1.x.c1.into();
        assert_eq!(p1_x_c1.to_bytes_le(), p2.x.c1.to_bytes());

        let p1_y_c0: BigInteger256 = p1.y.c0.into();
        assert_eq!(p1_y_c0.to_bytes_le(), p2.y.c0.to_bytes());

        let p1_y_c1: BigInteger256 = p1.y.c1.into();
        assert_eq!(p1_y_c1.to_bytes_le(), p2.y.c1.to_bytes());
    }

    fn assert_eq_ark_and_halo2_scalars(s1: <Bn254 as Pairing>::ScalarField, s2: Fr) {
        let s1_bi: BigInteger256 = s1.into();
        assert_eq!(s1_bi.to_bytes_le(), s2.to_bytes());
    }

    #[test]
    fn test_ark_ec_bn254_to_halo2curve() {
        let mut rng = test_rng();
        let ark_g1_a: <Bn254 as Pairing>::G1 = UniformRand::rand(&mut rng);
        let ark_g1_b: <Bn254 as Pairing>::G2 = UniformRand::rand(&mut rng);
        let s: <Bn254 as Pairing>::ScalarField = UniformRand::rand(&mut rng);

        let a = ark_g1_a.into_affine();
        let b = ark_g1_b.into_affine();

        let sa = a.mul(s);
        let sb = b.mul(s);

        let pairing_result1 = <Bn254>::pairing(sa, b);
        let pairing_result2 = <Bn254>::pairing(a, sb);
        assert_eq!(pairing_result1, pairing_result2);

        let a_halo2_affine = ark_to_halo2_g1_affine(&a);
        let b_halo2_affine = ark_to_halo2_g2_affine(&b);
        let s_halo2_scalar = ark_to_halo2_scalar_field(s);

        let sa_halo2_affine = a_halo2_affine.mul(&s_halo2_scalar).to_affine();
        let sb_halo2_affine = b_halo2_affine.mul(&s_halo2_scalar).to_affine();

        assert_eq_ark_and_halo2_g1_affine(&a, &a_halo2_affine);
        assert_eq_ark_and_halo2_g2_affine(&b, &b_halo2_affine);
        assert_eq_ark_and_halo2_scalars(s, s_halo2_scalar);

        let halo2_pairing_result1 = Bn256::pairing(&sa_halo2_affine, &b_halo2_affine);
        let halo2_pairing_result2 = Bn256::pairing(&a_halo2_affine, &sb_halo2_affine);
        assert_eq!(halo2_pairing_result1, halo2_pairing_result2);
    }

    #[test]
    fn test_halo2curve_to_ark_ec_bn254() {
        let mut rng = test_rng();
        let a_halo2 = G1Affine::random(&mut rng);
        let b_halo2 = G2Affine::random(&mut rng);
        let s_halo2 = Fr::random(&mut rng);

        let a_ark = halo2_to_ark_g1_affine(&a_halo2);
        assert_eq_ark_and_halo2_g1_affine(&a_ark, &a_halo2);

        let b_ark = halo2_to_ark_g2_affine(&b_halo2);
        assert_eq_ark_and_halo2_g2_affine(&b_ark, &b_halo2);

        let s_ark = halo2_to_ark_scalar(s_halo2);
        assert_eq_ark_and_halo2_scalars(s_ark, s_halo2);
    }

    #[test]
    fn test_halo2curve_and_ark_ec_bn254_conversion() {
        let mut rng = test_rng();
        let a_ark: <Bn254 as Pairing>::G1 = UniformRand::rand(&mut rng);
        let b_ark: <Bn254 as Pairing>::G2 = UniformRand::rand(&mut rng);
        let s: <Bn254 as Pairing>::ScalarField = UniformRand::rand(&mut rng);

        let a_ark_affine = a_ark.into_affine();
        let b_ark_affine = b_ark.into_affine();

        let a_ark_back = halo2_to_ark_g1_affine(&ark_to_halo2_g1_affine(&a_ark_affine));
        assert_eq!(a_ark, a_ark_back);

        let b_ark_back = halo2_to_ark_g2_affine(&ark_to_halo2_g2_affine(&b_ark_affine));
        assert_eq!(b_ark_affine, b_ark_back);

        let s_back = halo2_to_ark_scalar(ark_to_halo2_scalar_field(s));
        assert_eq!(s, s_back);
    }
}
