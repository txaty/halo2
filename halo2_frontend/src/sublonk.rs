use crate::circuit::batch_invert_assigned;
use crate::plonk;
use crate::plonk::{permutation, Circuit, ConstraintSystem, Error, FloorPlanner};
use ff::Field;
use halo2_middleware::circuit::{CompiledCircuit, Preprocessing};

#[allow(clippy::type_complexity)]
pub fn compile_witness_cs<F: Field, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
) -> Result<ConstraintSystem<F>, Error> {
    let n = 2usize.pow(k);

    let mut cs = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    ConcreteCircuit::configure_with_params(&mut cs, circuit.params());
    #[cfg(not(feature = "circuit-params"))]
    ConcreteCircuit::configure(&mut cs);
    let cs = cs;

    if n < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(k));
    }

    // println!("cs permutation {:?}", cs.permutation);

    Ok(cs)
}

#[allow(clippy::type_complexity)]
pub fn compile_sub_circuit<F: Field, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
    compress_selectors: bool,
) -> Result<
    (
        CompiledCircuit<F>,
        ConcreteCircuit::Config,
        ConstraintSystem<F>,
    ),
    Error,
> {
    let n = 2usize.pow(k);

    let mut cs = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut cs, circuit.params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut cs);
    let cs = cs;

    // if n < cs.minimum_rows() {
    //     return Err(Error::not_enough_rows_available(k));
    // }

    let mut assembly = plonk::keygen::Assembly {
        k,
        fixed: vec![vec![F::ZERO.into(); n]; cs.num_fixed_columns],
        permutation: permutation::Assembly::new(n, &cs.permutation),
        selectors: vec![vec![false; n]; cs.num_selectors],
        // usable_rows: 0..n - (cs.blinding_factors() + 1),
        usable_rows: 0..n,
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain URS
    ConcreteCircuit::FloorPlanner::synthesize(
        &mut assembly,
        circuit,
        config.clone(),
        cs.constants.clone(),
    )?;

    let mut fixed = batch_invert_assigned(assembly.fixed);
    let (cs, selector_polys) = if compress_selectors {
        cs.compress_selectors(assembly.selectors)
    } else {
        // After this, the ConstraintSystem should not have any selectors: `verify` does not need them, and `keygen_pk` regenerates `cs` from scratch anyways.
        let selectors = std::mem::take(&mut assembly.selectors);
        cs.directly_convert_selectors_to_fixed(selectors)
    };

    fixed.extend(selector_polys);

    // sort the "copies" for deterministic ordering
    #[cfg(feature = "thread-safe-region")]
    assembly.permutation.copies.sort();

    let preprocessing = Preprocessing {
        permutation: halo2_middleware::permutation::AssemblyMid {
            copies: assembly.permutation.copies,
        },
        fixed,
    };

    Ok((
        CompiledCircuit {
            cs: cs.clone().into(),
            preprocessing,
        },
        config,
        cs,
    ))
}
