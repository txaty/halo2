use crate::parameters::NUM_USABLE_WITNESSES;
use halo2_frontend::plonk::Instance;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Cell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Assigned, Circuit, Column, ConstraintSystem, ErrorFront, Fixed},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Clone)]
pub(crate) struct PlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,

    pi: Column<Instance>,
}

trait PlonkOperations<FF: Field> {
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

struct Plonk<F: Field> {
    config: PlonkConfig,
    _marker: PhantomData<F>,
}

impl<FF: Field> Plonk<FF> {
    fn new(config: PlonkConfig) -> Self {
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

fn plonk_configure<F: Field>(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
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

        vec![a.clone() * sa + b.clone() * sb + a * b * sm - (c * sc)]
    });

    PlonkConfig {
        a,
        b,
        c,
        sa,
        sb,
        sc,
        sm,
        pi,
    }
}

#[derive(Clone)]
pub(crate) enum CircuitEnum<F: Field> {
    Add(AddCircuit<F>),
    Mul(MulCircuit<F>),
    PlaceHolder,
}

// pub(crate) trait TwoFanInCircuit<F: Field>: Circuit<F> + Clone {
//     fn new(a: Value<F>, b: Value<F>) -> Self;
// }

impl<F: Field> Circuit<F> for CircuitEnum<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        match self {
            CircuitEnum::Add(circuit) => CircuitEnum::Add(circuit.without_witnesses()),
            CircuitEnum::Mul(circuit) => CircuitEnum::Mul(circuit.without_witnesses()),
            CircuitEnum::PlaceHolder => panic!("Cannot call without_witnesses on PlaceHolder"),
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
            CircuitEnum::Add(circuit) => circuit.synthesize(config, layouter),
            CircuitEnum::Mul(circuit) => circuit.synthesize(config, layouter),
            CircuitEnum::PlaceHolder => panic!("Cannot synthesize PlaceHolder"),
        }
    }
}

#[derive(Clone)]
pub(crate) struct AddCircuit<F: Field> {
    pub(crate) a: Value<F>,
    pub(crate) b: Value<F>,
}

// impl<F: Field> TwoFanInCircuit<F> for AddCircuit<F> {
//     fn new(a: Value<F>, b: Value<F>) -> Self {
//         Self { a, b }
//     }
// }

impl<F: Field> Circuit<F> for AddCircuit<F> {
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

        let a: Value<Assigned<_>> = self.a.into();
        let b: Value<Assigned<_>> = self.b.into();
        let mut a_add_b = Value::unknown();
        let (_, _, c) = cs.add(&mut layouter, || {
            a_add_b = a + b;
            a.zip(b)
                .zip(a_add_b)
                .map(|((a, b), a_add_b)| (a, b, a_add_b))
        })?;

        layouter.constrain_instance(c, cs.config.pi, 0)
    }
}

#[derive(Clone)]
pub(crate) struct MulCircuit<F: Field> {
    pub(crate) a: Value<F>,
    pub(crate) b: Value<F>,
}

// impl<F: Field> TwoFanInCircuit<F> for MulCircuit<F> {
//     fn new(a: Value<F>, b: Value<F>) -> Self {
//         Self { a, b }
//     }
// }

impl<F: Field> Circuit<F> for MulCircuit<F> {
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

        let a: Value<Assigned<_>> = self.a.into();
        let b: Value<Assigned<_>> = self.b.into();
        let mut a_mul_b = Value::unknown();
        let (_, _, c) = cs.multiply(&mut layouter, || {
            a_mul_b = a * b;
            a.zip(b)
                .zip(a_mul_b)
                .map(|((a, b), a_mul_b)| (a, b, a_mul_b))
        })?;

        layouter.constrain_instance(c, cs.config.pi, 0)
    }
}

pub(crate) struct WitnessCircuit<F: Field> {
    left_values: Vec<Value<F>>,
    right_values: Vec<Value<F>>,
    queried_circuit_indices: Vec<usize>,
}

impl<F: Field> WitnessCircuit<F> {
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
            left_values: vec![Value::unknown(); NUM_USABLE_WITNESSES],
            right_values: vec![Value::unknown(); NUM_USABLE_WITNESSES],
            queried_circuit_indices: queried_circuit_indices
                .unwrap_or_else(|| &[0; NUM_USABLE_WITNESSES])
                .to_vec(),
        }
    }
}

impl<F: Field> Circuit<F> for WitnessCircuit<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            left_values: vec![Value::unknown(); NUM_USABLE_WITNESSES],
            right_values: vec![Value::unknown(); NUM_USABLE_WITNESSES],
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
        for i in 0..NUM_USABLE_WITNESSES {
            let a: Value<Assigned<_>> = self.left_values[i].into();
            let b: Value<Assigned<_>> = self.right_values[i].into();
            let mut res = Value::unknown();
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
            layouter.constrain_instance(c, cs.config.pi, i)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parameters::NUM_WITNESS_POWERS;
    use halo2_backend::plonk::verifier::verify_proof;
    use halo2_backend::poly::commitment::ParamsProver;
    use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
    use halo2_backend::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
    use halo2_backend::poly::kzg::strategy::SingleStrategy;
    use halo2_backend::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    };
    use halo2_frontend::circuit::Value;
    use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk};
    use halo2curves::bn256::{Bn256, Fr, G1Affine};
    use rand_core::OsRng;

    #[test]
    fn test_witness_circuit() {
        let params = ParamsKZG::<Bn256>::new(NUM_WITNESS_POWERS);
        let queried_circuit_indices = vec![0; NUM_USABLE_WITNESSES];
        let witness_circuit = WitnessCircuit::<Fr>::new_empty(Some(&queried_circuit_indices));
        let vk = keygen_vk(&params, &witness_circuit).unwrap();
        let pk = keygen_pk(&params, vk.clone(), &witness_circuit).unwrap();

        let left_values = vec![Fr::from(2); NUM_USABLE_WITNESSES];
        let right_values = vec![Fr::from(3); NUM_USABLE_WITNESSES];
        let public_inputs = vec![Fr::from(5); NUM_USABLE_WITNESSES];
        let left_values = left_values
            .iter()
            .map(|v| Value::known(*v))
            .collect::<Vec<_>>();
        let right_values = right_values
            .iter()
            .map(|v| Value::known(*v))
            .collect::<Vec<_>>();

        let witness_circuit =
            WitnessCircuit::<Fr>::new(&left_values, &right_values, &queried_circuit_indices);

        let mut transcript =
            Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);
        let rng = OsRng;
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<Bn256>,
            Challenge255<G1Affine>,
            OsRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            _,
        >(
            &params,
            &pk,
            &[witness_circuit],
            &[&[&public_inputs]],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        let proof = transcript.finalize();

        let params_verifier = params.verifier_params();
        let strategy = SingleStrategy::new(&params_verifier);
        let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(&proof);

        verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<Bn256>,
        >(
            &params_verifier,
            &vk,
            strategy,
            &[&[&public_inputs]],
            &mut transcript,
        )
        .unwrap();
    }
}
