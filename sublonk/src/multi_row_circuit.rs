use crate::config::SEGMENT_SIZE;
use crate::plonk_circuit::{plonk_configure, Plonk, PlonkConfig, PlonkOperations};
use halo2_backend::arithmetic::Field;
use halo2_frontend::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_frontend::plonk::{Assigned, Circuit, ConstraintSystem};
use halo2_proofs::plonk::ErrorFront;

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
    valid_num_witness_circuits: usize,
}

impl<F: Field> WitnessCircuit64<F> {
    pub(crate) fn new(
        left_values: &[Value<F>],
        right_values: &[Value<F>],
        queried_circuit_indices: &[usize],
        valid_num_witness_circuits: usize,
    ) -> Self {
        Self {
            left_values: left_values.to_vec(),
            right_values: right_values.to_vec(),
            queried_circuit_indices: queried_circuit_indices.to_vec(),
            valid_num_witness_circuits,
        }
    }

    pub(crate) fn new_empty(
        queried_circuit_indices: Option<&[usize]>,
        valid_num_witness_circuits: usize,
    ) -> Self {
        Self {
            left_values: vec![Value::unknown(); valid_num_witness_circuits],
            right_values: vec![Value::unknown(); valid_num_witness_circuits],
            queried_circuit_indices: if let Some(indices) = queried_circuit_indices {
                indices.to_vec()
            } else {
                vec![0; valid_num_witness_circuits]
            },
            valid_num_witness_circuits,
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
            left_values: vec![Value::unknown(); self.valid_num_witness_circuits],
            right_values: vec![Value::unknown(); self.valid_num_witness_circuits],
            queried_circuit_indices: self.queried_circuit_indices.clone(),
            valid_num_witness_circuits: self.valid_num_witness_circuits,
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
        for i in 0..self.valid_num_witness_circuits {
            let a: Value<Assigned<_>> = self.left_values[i].into();
            let b: Value<Assigned<_>> = self.right_values[i].into();
            let mut res = Value::unknown();
            for j in 0..SEGMENT_SIZE {
                let (_, _, c) = match self.queried_circuit_indices[i] % 2 {
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
