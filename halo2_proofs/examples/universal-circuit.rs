use ff::Field;
use halo2_backend::plonk::verifier::verify_proof;
use halo2_backend::plonk::{ProvingKey, VerifyingKey};
use halo2_backend::poly::commitment::ParamsProver;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_backend::poly::kzg::strategy::SingleStrategy;
use halo2_backend::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
};
use halo2_frontend::circuit::{Cell, Layouter, SimpleFloorPlanner, Value};
use halo2_frontend::plonk::{Advice, Assigned, Circuit, Column, ConstraintSystem, Fixed, Instance};
use halo2_middleware::poly::Rotation;
use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, ErrorFront};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;
use std::marker::PhantomData;

pub(crate) const POW_NUM_WITNESS_CIRCUIT: usize = 2;
pub(crate) const NUM_WITNESS_CIRCUITS: usize = 1 << POW_NUM_WITNESS_CIRCUIT;
pub(crate) const POW_SEGMENT_SIZE: usize = 4;
pub(crate) const SEGMENT_SIZE: usize = 1 << POW_SEGMENT_SIZE;
pub(crate) const POW_WITNESS_SIZE: usize = POW_NUM_WITNESS_CIRCUIT + POW_SEGMENT_SIZE;
pub(crate) const WITNESS_SIZE: usize = 1 << POW_WITNESS_SIZE;
pub(crate) const NUM_UNUSABLE_ROWS: usize = SEGMENT_SIZE;
pub(crate) const USABLE_WITNESSES_SIZE: usize = WITNESS_SIZE - NUM_UNUSABLE_ROWS;
pub(crate) const VALID_NUM_WITNESS_CIRCUITS: usize = NUM_WITNESS_CIRCUITS - 1;
pub(crate) const NUM_DUMMY_SELECTORS: usize = 1 << 15;

#[derive(Clone)]
pub(crate) struct PlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,

    dummy_selectors: [Column<Fixed>; NUM_DUMMY_SELECTORS],

    pub(crate) pi: Column<Instance>,
}

pub(crate) trait PlonkOperations<FF: Field> {
    fn multiply<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        f: F,
    ) -> Result<(Cell, Cell, Cell), ErrorFront>
    where
        F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>;

    fn add<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        f: F,
    ) -> Result<(Cell, Cell, Cell), ErrorFront>
    where
        F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>;

    fn copy(&self, layouter: &mut impl Layouter<FF>, a: Cell, b: Cell) -> Result<(), ErrorFront>;
}

pub(crate) struct Plonk<F: Field> {
    pub(crate) config: PlonkConfig,
    _marker: PhantomData<F>,
}

impl<FF: Field> Plonk<FF> {
    pub(crate) fn new(config: PlonkConfig) -> Self {
        Plonk {
            config,
            _marker: PhantomData,
        }
    }
}

impl<FF: Field> PlonkOperations<FF> for Plonk<FF> {
    fn multiply<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        mut f: F,
    ) -> Result<(Cell, Cell, Cell), ErrorFront>
    where
        F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>,
    {
        layouter.assign_region(
            || "mul",
            |mut region| {
                let mut value = None;
                let lhs = region.assign_advice(
                    || "lhs",
                    self.config.a,
                    0,
                    || {
                        value = Some(f());
                        value.unwrap().map(|v| v.0)
                    },
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    self.config.b,
                    0,
                    || value.unwrap().map(|v| v.1),
                )?;

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value.unwrap().map(|v| v.2),
                )?;

                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(FF::ZERO))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(FF::ZERO))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "m", self.config.sm, 0, || Value::known(FF::ONE))?;

                Ok((lhs.cell(), rhs.cell(), out.cell()))
            },
        )
    }

    fn add<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        mut f: F,
    ) -> Result<(Cell, Cell, Cell), ErrorFront>
    where
        F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>,
    {
        layouter.assign_region(
            || "add",
            |mut region| {
                let mut value = None;
                let lhs = region.assign_advice(
                    || "lhs",
                    self.config.a,
                    0,
                    || {
                        value = Some(f());
                        value.unwrap().map(|v| v.0)
                    },
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    self.config.b,
                    0,
                    || value.unwrap().map(|v| v.1),
                )?;
                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value.unwrap().map(|v| v.2),
                )?;

                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(FF::ONE))?;
                region.assign_fixed(|| "m", self.config.sm, 0, || Value::known(FF::ZERO))?;

                for i in 0..NUM_DUMMY_SELECTORS {
                    region.assign_fixed(
                        || "dummy_selector",
                        self.config.dummy_selectors[i],
                        0,
                        || Value::known(FF::ZERO),
                    )?;
                }

                Ok((lhs.cell(), rhs.cell(), out.cell()))
            },
        )
    }

    fn copy(
        &self,
        layouter: &mut impl Layouter<FF>,
        left: Cell,
        right: Cell,
    ) -> Result<(), ErrorFront> {
        layouter.assign_region(|| "copy", |mut region| region.constrain_equal(left, right))
    }
}

pub(crate) fn plonk_configure<F: Field>(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
    // meta.set_minimum_degree(5);

    let a = meta.advice_column();
    let b = meta.advice_column();
    let c = meta.advice_column();

    meta.enable_equality(a);
    meta.enable_equality(b);
    meta.enable_equality(c);

    let sa = meta.fixed_column();
    let sb = meta.fixed_column();
    let sc = meta.fixed_column();
    let sm = meta.fixed_column();

    let dummy_selectors = [meta.fixed_column(); NUM_DUMMY_SELECTORS];

    let pi = meta.instance_column();
    meta.enable_equality(pi);

    meta.create_gate("Two Fan-in Gate", |meta| {
        let a = meta.query_advice(a, Rotation::cur());
        let b = meta.query_advice(b, Rotation::cur());
        let c = meta.query_advice(c, Rotation::cur());

        let sa = meta.query_fixed(sa, Rotation::cur());
        let sb = meta.query_fixed(sb, Rotation::cur());
        let sc = meta.query_fixed(sc, Rotation::cur());
        let sm = meta.query_fixed(sm, Rotation::cur());

        // for i in 0..NUM_DUMMY_SELECTORS {
        //     let dummy_selector = meta.query_fixed(dummy_selectors[i], Rotation::cur());
        // }

        let dummy_selector0 = meta.query_fixed(dummy_selectors[0], Rotation::cur());
        let dummy_selector1 = meta.query_fixed(dummy_selectors[1], Rotation::cur());

        vec![a.clone() * sa + b.clone() * sb + a.clone() * b * sm - (c * sc) + a.clone() *
            dummy_selector0 + a.clone() * dummy_selector1]
    });

    PlonkConfig {
        a,
        b,
        c,
        sa,
        sb,
        sc,
        sm,
        dummy_selectors,
        pi,
    }
}

macro_rules! add_dummy_selectors_constraints {
    ($expressions:expr, $dummy_selectors:expr, $zero_val:expr) => {
        for selector in $dummy_selectors.iter() {
            // Enforce that each dummy selector is zero
            // This adds a constraint: selector * 0 = 0
            $expressions.push(selector.clone() * $zero_val.clone());
        }
    };
}

#[derive(Clone)]
pub(crate) struct AddCircuit64<F: Field> {
    pub(crate) a: Value<F>,
    pub(crate) b: Value<F>,
}

impl<F: Field> Circuit<F> for AddCircuit64<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            a: Value::unknown(),
            b: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        plonk_configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let cs = Plonk::new(config);

        for i in 0..SEGMENT_SIZE {
            let a: Value<Assigned<_>> = self.a.into();
            let b: Value<Assigned<_>> = self.b.into();
            let mut a_add_b = Value::unknown();
            let (_, _, c) = cs.add(&mut layouter, || {
                a_add_b = a + b;
                a.zip(b)
                    .zip(a_add_b)
                    .map(|((a, b), a_add_b)| (a, b, a_add_b))
            })?;

            layouter.constrain_instance(c, cs.config.pi, i)?;
        }

        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct MulCircuit64<F: Field> {
    pub(crate) a: Value<F>,
    pub(crate) b: Value<F>,
}

impl<F: Field> Circuit<F> for MulCircuit64<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            a: Value::unknown(),
            b: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        plonk_configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let cs = Plonk::new(config);

        for i in 0..SEGMENT_SIZE {
            let a: Value<Assigned<_>> = self.a.into();
            let b: Value<Assigned<_>> = self.b.into();
            let mut a_mul_b = Value::unknown();
            let (_, _, c) = cs.multiply(&mut layouter, || {
                a_mul_b = a * b;
                a.zip(b)
                    .zip(a_mul_b)
                    .map(|((a, b), a_mul_b)| (a, b, a_mul_b))
            })?;

            layouter.constrain_instance(c, cs.config.pi, i)?;
        }

        Ok(())
    }
}

pub(crate) struct WitnessCircuit64<F: Field> {
    left_values: Vec<Value<F>>,
    right_values: Vec<Value<F>>,
    queried_circuit_indices: Vec<usize>,
}

impl<F: Field> WitnessCircuit64<F> {
    pub(crate) fn new(
        left_values: &[Value<F>],
        right_values: &[Value<F>],
        queried_circuit_indices: &[usize],
    ) -> Self {
        Self {
            left_values: left_values.to_vec(),
            right_values: right_values.to_vec(),
            queried_circuit_indices: queried_circuit_indices.to_vec(),
        }
    }

    pub(crate) fn new_empty(queried_circuit_indices: Option<&[usize]>) -> Self {
        Self {
            left_values: vec![Value::unknown(); VALID_NUM_WITNESS_CIRCUITS],
            right_values: vec![Value::unknown(); VALID_NUM_WITNESS_CIRCUITS],
            queried_circuit_indices: queried_circuit_indices
                .unwrap_or_else(|| &[0; VALID_NUM_WITNESS_CIRCUITS])
                .to_vec(),
        }
    }
}

impl<F: Field> Circuit<F> for WitnessCircuit64<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            left_values: vec![Value::unknown(); VALID_NUM_WITNESS_CIRCUITS],
            right_values: vec![Value::unknown(); VALID_NUM_WITNESS_CIRCUITS],
            queried_circuit_indices: self.queried_circuit_indices.clone(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        // meta.set_minimum_degree(NUM_WITNESSES);
        plonk_configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let cs = Plonk::new(config);
        for i in 0..VALID_NUM_WITNESS_CIRCUITS {
            let a: Value<Assigned<_>> = self.left_values[i].into();
            let b: Value<Assigned<_>> = self.right_values[i].into();
            let mut res = Value::unknown();
            for j in 0..SEGMENT_SIZE {
                let (_, _, c) = match self.queried_circuit_indices[i] {
                    0 => cs.add(&mut layouter, || {
                        res = a + b;
                        a.zip(b).zip(res).map(|((a, b), res)| (a, b, res))
                    })?,
                    1 => cs.multiply(&mut layouter, || {
                        res = a * b;
                        a.zip(b).zip(res).map(|((a, b), res)| (a, b, res))
                    })?,
                    _ => panic!("Invalid circuit index"),
                };
                layouter.constrain_instance(c, cs.config.pi, i * SEGMENT_SIZE + j)?;
            }
        }

        Ok(())
    }
}

#[derive(Clone)]
pub(crate) enum CircuitEnum64<F: Field> {
    Add(AddCircuit64<F>),
    Mul(MulCircuit64<F>),
    PlaceHolder,
}

impl<F: Field> Circuit<F> for CircuitEnum64<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        match self {
            CircuitEnum64::Add(circuit) => CircuitEnum64::Add(circuit.without_witnesses()),
            CircuitEnum64::Mul(circuit) => CircuitEnum64::Mul(circuit.without_witnesses()),
            CircuitEnum64::PlaceHolder => panic!("Cannot call without_witnesses on PlaceHolder"),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        plonk_configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        match self {
            CircuitEnum64::Add(circuit) => circuit.synthesize(config, layouter),
            CircuitEnum64::Mul(circuit) => circuit.synthesize(config, layouter),
            CircuitEnum64::PlaceHolder => {
                panic!("Cannot synthesize PlaceHolder")
            }
        }
    }
}

fn keygen(k: u32) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
    let params: ParamsKZG<Bn256> = ParamsKZG::<Bn256>::new(k);

    let empty_circuit: AddCircuit64<Fr> = AddCircuit64 {
        a: Value::unknown(),
        b: Value::unknown(),
    };
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    (params, pk)
}

fn prover(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    a: Fr,
    b: Fr,
    public_inputs: &[Fr],
) -> Vec<u8> {
    let rng = OsRng;

    let circuit: AddCircuit64<Fr> = AddCircuit64 {
        a: Value::known(a),
        b: Value::known(b),
    };

    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        AddCircuit64<Fr>,
    >(
        params,
        pk,
        &[circuit],
        &[&[public_inputs]],
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");

    transcript.finalize()
}

fn verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    proof: &[u8],
    public_inputs: &[Fr],
) {
    let params_verifier = params.verifier_params();
    let strategy = SingleStrategy::new(&params_verifier);
    let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(proof);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<Bn256>,
    >(
        &params_verifier,
        vk,
        strategy,
        &[&[public_inputs]],
        &mut transcript
    )
    .is_ok());
}

// fn main() {
//     let (params, pk) = keygen(POW_WITNESS_SIZE as u32);
//     println!(
//         "no fixed columns: {:?}",
//         pk.get_vk().fixed_commitments.len()
//     );
//
//     let a = Fr::from(2);
//     let b = Fr::from(3);
//     let public_inputs = vec![Fr::from(5); SEGMENT_SIZE];
//
//     let proof = prover(&params, &pk, a, b, &public_inputs);
//     verifier(&params, pk.get_vk(), proof.as_ref(), &public_inputs);
// }

fn main() {
    let circuit: AddCircuit64<Fr> = AddCircuit64 {
        a: Value::unknown(),
        b: Value::unknown(),
    };
    // let circuit = WitnessCircuit64::<Fr>::new_empty(None);

    // Create the area you want to draw on.
    // Use SVGBackend if you want to render to .svg instead.
    use plotters::prelude::*;
    let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Example Circuit Layout", ("sans-serif", 60))
        .unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        // You can optionally render only a section of the circuit.
        .view_width(0..16)
        .view_height(0..32)
        // You can hide labels, which can be useful with smaller areas.
        .show_labels(true)
        .mark_equality_cells(true)
        .show_equality_constraints(true)
        // Render the circuit onto your area!
        // The first argument is the size parameter for the circuit.
        .render(5, &circuit, &root)
        .unwrap();
}
