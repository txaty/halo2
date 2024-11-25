use halo2_frontend::plonk::Instance;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Cell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, ErrorFront, Fixed},
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