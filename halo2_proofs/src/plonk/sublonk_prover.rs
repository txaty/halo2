use crate::plonk::{Error, ErrorBack};
use crate::poly::commitment::{self, CommitmentScheme, Params};
use crate::transcript::{EncodedChallenge, TranscriptWrite};
use halo2_backend::plonk::{prover::Prover, ProvingKey};
use halo2_frontend::circuit::WitnessCalculator;
use halo2_frontend::plonk::{Circuit, ConstraintSystem};
use halo2_middleware::ff::{FromUniformBytes, WithSmallOrderMulGroup};
use halo2_middleware::zal::{
    impls::{PlonkEngine, PlonkEngineConfig},
    traits::MsmAccel,
};
use rand_core::RngCore;
use std::collections::HashMap;
use group::Curve;
use crate::arithmetic::CurveAffine;

/// This creates a proof with sublonk configuration for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_sublonk_proof<
    'params,
    Scheme: CommitmentScheme,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
    instance_commitments: Vec<Vec<<<Scheme::Curve as CurveAffine>::CurveExt as Curve>::AffineRepr>>,
    rng: R,
    transcript: &mut T,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let engine = PlonkEngineConfig::build_default();
    create_sublonk_proof_with_engine::<Scheme, P, _, _, _, _, _>(
        engine, params, pk, circuits, instances, instance_commitments, rng, transcript,
    )
}

/// This creates a proof with sublonk config for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_sublonk_proof_with_engine<
    'params,
    Scheme: CommitmentScheme,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
    M: MsmAccel<Scheme::Curve>,
>(
    engine: PlonkEngine<Scheme::Curve, M>,
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
    instance_commitments: Vec<Vec<<<Scheme::Curve as CurveAffine>::CurveExt as Curve>::AffineRepr>>,
    rng: R,
    transcript: &mut T,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    // Since we may pass multiple circuits, we need to ensure that the number of circuits
    // matches the number of instances (public inputs) provided.
    if circuits.len() != instances.len() {
        return Err(Error::Backend(ErrorBack::InvalidInstances));
    }

    let mut cs = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut cs, circuits[0].params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut cs);
    let cs = cs;

    // Create a witness calculator for each circuit.
    let mut witness_calcs: Vec<_> = circuits
        .iter()
        .enumerate()
        .map(|(i, circuit)| WitnessCalculator::new(params.k(), circuit, &config, &cs, instances[i]))
        .collect();
    let mut prover = Prover::<Scheme, P, _, _, _, _>::new_with_engine_sublonk(
        engine, params, pk, instances, instance_commitments, rng, transcript,
    )?;
    
    
    let mut challenges = HashMap::new();
    let phases = prover.phases().to_vec();
    for phase in phases.iter() {
        let mut witnesses = Vec::with_capacity(circuits.len());
        for witness_calc in witness_calcs.iter_mut() {
            witnesses.push(witness_calc.calc(*phase, &challenges)?);
        }
        challenges = prover.commit_phase(*phase, witnesses).unwrap();
    }
    Ok(prover.create_sublonk_proof()?)
}