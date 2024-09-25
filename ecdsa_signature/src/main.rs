use halo2wrong::curves::bn256::{Bn256, G1Affine};
use halo2wrong::halo2::plonk::ErrorFront;
use ecc::integer::{IntegerInstructions, Range};
use ecc::{EccConfig, GeneralEccChip};
use ecdsa::ecdsa::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
use halo2wrong::curves::bn256::Fr as BnScalar;
use halo2wrong::curves::ff::{Field, FromUniformBytes, PrimeField};
use halo2wrong::curves::group::{Curve, Group};
use halo2wrong::curves::secp256k1::Secp256k1Affine;
use halo2wrong::curves::CurveAffine;
use halo2wrong::halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2wrong::halo2::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, ProvingKey,
    VerifyingKey,
};
use halo2wrong::halo2::poly::commitment::ParamsProver;
use halo2wrong::halo2::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2wrong::halo2::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2wrong::halo2::poly::kzg::strategy::SingleStrategy;
use halo2wrong::halo2::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
};
use halo2wrong::utils::{big_to_fe, fe_to_big, mock_prover_verify};
use halo2wrong::RegionCtx;
use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};
use rand_core::OsRng;
use std::marker::PhantomData;

const BIT_LEN_LIMB: usize = 68;
const NUMBER_OF_LIMBS: usize = 4;

#[derive(Clone, Debug)]
struct TestCircuitEcdsaVerifyConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
}

impl TestCircuitEcdsaVerifyConfig {
    pub fn new<C: CurveAffine, N: PrimeField>(meta: &mut ConstraintSystem<N>) -> Self {
        let (rns_base, rns_scalar) = GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
        let main_gate_config = MainGate::<N>::configure(meta);
        let mut overflow_bit_lens: Vec<usize> = vec![];
        overflow_bit_lens.extend(rns_base.overflow_lengths());
        overflow_bit_lens.extend(rns_scalar.overflow_lengths());
        let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

        let range_config = RangeChip::<N>::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );
        TestCircuitEcdsaVerifyConfig {
            main_gate_config,
            range_config,
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn config_range<N: PrimeField>(
        &self,
        layouter: &mut impl Layouter<N>,
    ) -> Result<(), ErrorFront> {
        let range_chip = RangeChip::<N>::new(self.range_config.clone());
        range_chip.load_table(layouter)?;

        Ok(())
    }
}

#[derive(Default, Clone)]
struct TestCircuitEcdsaVerify<E: CurveAffine, N: PrimeField> {
    public_key: Value<E>,
    signature: Value<(E::Scalar, E::Scalar)>,
    msg_hash: Value<E::Scalar>,

    aux_generator: E,
    window_size: usize,
    _marker: PhantomData<N>,
}

impl<E: CurveAffine, N: PrimeField> Circuit<N> for TestCircuitEcdsaVerify<E, N> {
    type Config = TestCircuitEcdsaVerifyConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        TestCircuitEcdsaVerifyConfig::new::<E, N>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), ErrorFront> {
        let mut ecc_chip =
            GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(config.ecc_chip_config());

        layouter.assign_region(
            || "assign aux values",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                ecc_chip.assign_aux(ctx, self.window_size, 2)?;
                Ok(())
            },
        )?;

        let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
        let scalar_chip = ecc_chip.scalar_field_chip();

        layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                let r = self.signature.map(|signature| signature.0);
                let s = self.signature.map(|signature| signature.1);
                let integer_r = ecc_chip.new_unassigned_scalar(r);
                let integer_s = ecc_chip.new_unassigned_scalar(s);
                let msg_hash = ecc_chip.new_unassigned_scalar(self.msg_hash);

                let r_assigned = scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
                let s_assigned = scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
                let sig = AssignedEcdsaSig {
                    r: r_assigned,
                    s: s_assigned,
                };

                let pk_in_circuit = ecc_chip.assign_point(ctx, self.public_key)?;
                let pk_assigned = AssignedPublicKey {
                    point: pk_in_circuit,
                };
                let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;
                ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)
            },
        )?;

        config.config_range(&mut layouter)?;

        Ok(())
    }
}

fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
    let x_big = fe_to_big(x);
    big_to_fe(x_big)
}

fn run<C: CurveAffine, N: FromUniformBytes<64> + Ord>() {
    let g = C::generator();

    // Generate a key pair
    let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
    let public_key = (g * sk).to_affine();

    // Generate a valid signature
    // Suppose `m_hash` is the message hash
    let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

    // Draw arandomness
    let k = <C as CurveAffine>::ScalarExt::random(OsRng);
    let k_inv = k.invert().unwrap();

    // Calculate `r`
    let r_point = (g * k).to_affine().coordinates().unwrap();
    let x = r_point.x();
    let r = mod_n::<C>(*x);

    // Calculate `s`
    let s = k_inv * (msg_hash + (r * sk));

    // Sanity check. Ensure we construct a valid signature. So lets verify it
    {
        let s_inv = s.invert().unwrap();
        let u_1 = msg_hash * s_inv;
        let u_2 = r * s_inv;
        let r_point = ((g * u_1) + (public_key.clone() * u_2))
            .to_affine()
            .coordinates()
            .unwrap();
        let x_candidate = r_point.x();
        let r_candidate = mod_n::<C>(*x_candidate);
        assert_eq!(r, r_candidate);
    }

    let aux_generator = C::CurveExt::random(OsRng).to_affine();
    let circuit = TestCircuitEcdsaVerify::<C, N> {
        public_key: Value::known(public_key),
        signature: Value::known((r, s)),
        msg_hash: Value::known(msg_hash),
        aux_generator,
        window_size: 4,
        ..Default::default()
    };
    let instance = vec![vec![]];
    mock_prover_verify(&circuit, instance);
}

fn keygen(k: u32) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
    let params: ParamsKZG<Bn256> = ParamsKZG::<Bn256>::new(k);
    let aux_generator = <Secp256k1Affine as CurveAffine>::CurveExt::random(OsRng).to_affine();

    let empty_circuit: TestCircuitEcdsaVerify<Secp256k1Affine, BnScalar> = TestCircuitEcdsaVerify {
        public_key: Value::unknown(),
        signature: Value::unknown(),
        msg_hash: Value::unknown(),
        aux_generator,
        window_size: 4,
        ..Default::default()
    };
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    println!(
        "num fixed commitments: {:?}",
        pk.get_vk().fixed_commitments.len()
    );
    println!(
        "num permutation commitments: {:?}",
        pk.permutation.permutations.len()
    );
    (params, pk)
}

fn prover(params: &ParamsKZG<Bn256>, pk: &ProvingKey<G1Affine>) -> Vec<u8> {
    let rng = OsRng;

    let g = Secp256k1Affine::generator();

    // Generate a key pair
    let sk = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
    let public_key = (g * sk).to_affine();

    // Generate a valid signature
    // Suppose `m_hash` is the message hash
    let msg_hash = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);

    // Draw a randomness
    let k = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
    let k_inv = k.invert().unwrap();

    // Calculate `r`
    let r_point = (g * k).to_affine().coordinates().unwrap();
    let x = r_point.x();
    let r = mod_n::<Secp256k1Affine>(*x);

    // Calculate `s`
    let s = k_inv * (msg_hash + (r * sk));

    // Sanity check. Ensure we construct a valid signature. So lets verify it
    {
        let s_inv = s.invert().unwrap();
        let u_1 = msg_hash * s_inv;
        let u_2 = r * s_inv;
        let r_point = ((g * u_1) + (public_key.clone() * u_2))
            .to_affine()
            .coordinates()
            .unwrap();
        let x_candidate = r_point.x();
        let r_candidate = mod_n::<Secp256k1Affine>(*x_candidate);
        assert_eq!(r, r_candidate);
    }

    let aux_generator = <Secp256k1Affine as CurveAffine>::CurveExt::random(OsRng).to_affine();
    let circuit = TestCircuitEcdsaVerify::<Secp256k1Affine, BnScalar> {
        public_key: Value::known(public_key),
        signature: Value::known((r, s)),
        msg_hash: Value::known(msg_hash),
        aux_generator,
        window_size: 4,
        ..Default::default()
    };

    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        _,
    >(params, pk, &[circuit], &[&[&[]]], rng, &mut transcript)
    .expect("proof generation should not fail");

    transcript.finalize()
}

fn verifier(params: &ParamsKZG<Bn256>, vk: &VerifyingKey<G1Affine>, proof: &[u8]) {
    let params_verifier = params.verifier_params();
    let strategy = SingleStrategy::new(&params_verifier);
    let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(proof);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<Bn256>,
    >(&params_verifier, vk, strategy, &[&[&[]]], &mut transcript)
    .is_ok());
}

fn main() {
    let k = 18;
    let curr_time = std::time::Instant::now();
    let (params, pk) = keygen(k);
    println!("keygen time (ms): {:?}", curr_time.elapsed().as_millis());

    let curr_time = std::time::Instant::now();
    let proof = prover(&params, &pk);
    println!("prover time (ms): {:?}", curr_time.elapsed().as_millis());

    let curr_time = std::time::Instant::now();
    verifier(&params, &pk.get_vk(), &proof);
    println!("verifier time (ms): {:?}", curr_time.elapsed().as_millis());
}
