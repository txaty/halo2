use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Cell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Assigned, Circuit, Column, ConstraintSystem, ErrorFront, Fixed},
    poly::Rotation,
};

#[derive(Clone)]
pub(crate) struct PlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,
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

#[derive(Clone)]
pub(crate) struct MyCircuit<F: Field> {
    pub(crate) a: Value<F>,
    pub(crate) k: u32,
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

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            a: Value::unknown(),
            k: self.k,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        meta.set_minimum_degree(5);

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

        meta.create_gate("Combined add-mul", |meta| {
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
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let cs = Plonk::new(config);

        for _ in 0..((1 << (self.k - 1)) - 3) {
            let a: Value<Assigned<_>> = self.a.into();
            let mut a_squared = Value::unknown();
            let (a0, _, c0) = cs.multiply(&mut layouter, || {
                a_squared = a.square();
                a.zip(a_squared).map(|(a, a_squared)| (a, a, a_squared))
            })?;
            let (a1, b1, _) = cs.add(&mut layouter, || {
                let fin = a_squared + a;
                a.zip(a_squared)
                    .zip(fin)
                    .map(|((a, a_squared), fin)| (a, a_squared, fin))
            })?;
            cs.copy(&mut layouter, a0, a1)?;
            cs.copy(&mut layouter, b1, c0)?;
        }

        Ok(())
    }
}
