use crate::plonk_circuit::plonk_configure;
use crate::plonk_circuit::Plonk;
use crate::plonk_circuit::PlonkConfig;
use crate::plonk_circuit::PlonkOperations;
use halo2_backend::arithmetic::Field;
use halo2_frontend::circuit::SimpleFloorPlanner;
use halo2_frontend::circuit::Value;
use halo2_frontend::plonk::Circuit;
use halo2_frontend::plonk::ConstraintSystem;
use halo2_frontend::plonk::Error;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::plonk::Assigned;

#[derive(Clone)]
pub(crate) struct BenchCircuit<F: Field> {
    pub(crate) a: Vec<Value<F>>,
    pub(crate) b: Vec<Value<F>>,
    pub(crate) num_rows: usize,
}

impl<F: Field> Circuit<F> for BenchCircuit<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            a: vec![Value::unknown(); self.num_rows],
            b: vec![Value::unknown(); self.num_rows],
            num_rows: self.num_rows,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        plonk_configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let cs = Plonk::new(config);

        for i in 0..self.num_rows {
            let a: Value<Assigned<_>> = self.a[i].into();
            let b: Value<Assigned<_>> = self.b[i].into();
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
