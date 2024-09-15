use crate::bn254_convert::halo2_to_ark_g1_affine;
use ark_bn254::Bn254;
use ark_segmentlookup::prover::Proof;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::TablePreprocessedParameters;
use ark_segmentlookup::verifier::verify;
use halo2_backend::plonk::permutation::VerifyingKey as PermutationVerifyingKey;
use halo2_backend::plonk::sublonk_keygen::SublonkVerifyingKey;
use halo2_backend::plonk::verifier::verify_proof;
use halo2_backend::plonk::VerifyingKey;
use halo2_backend::poly::commitment::Params;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::VerifierSHPLONK;
use halo2_backend::poly::kzg::strategy::SingleStrategy;
use halo2_backend::transcript::{Blake2bRead, Challenge255, TranscriptReadBuffer};
use halo2_middleware::circuit::ConstraintSystemMid;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;
use rayon::prelude::*;

pub(crate) fn sublonk_verify(
    halo2_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    proof: &[u8],
    public_inputs: &[Fr],
    witness_cs: &ConstraintSystemMid<Fr>,
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    fixed_proofs: &[Proof<Bn254>],
    permutation_proofs: &[Proof<Bn254>],
    fixed_statements: &[G1Affine],
    permutation_statements: &[G1Affine],
    adjusted_permutation_statements: &[G1Affine],
) {
    let curr_time = std::time::Instant::now();
    batch_lookup_verify(
        lookup_params,
        fixed_tpp_list,
        fixed_proofs,
        fixed_statements,
    );

    batch_lookup_verify(
        lookup_params,
        permutation_tpp_list,
        permutation_proofs,
        permutation_statements,
    );
    println!("Verification: lookup proof verification (ms): {:?}", curr_time.elapsed().as_millis());

    let curr_time = std::time::Instant::now();
    let sublonk_vk = SublonkVerifyingKey::<G1Affine>::new(halo2_params.k(), witness_cs);

    let vk = VerifyingKey::from_parts(
        sublonk_vk.domain.clone(),
        fixed_statements.to_vec(),
        PermutationVerifyingKey {
            commitments: adjusted_permutation_statements.to_vec(),
        },
        sublonk_vk.cs.clone(),
    );
    println!("Verification: vk creation (ms): {:?}", curr_time.elapsed().as_millis());
    
    let curr_time = std::time::Instant::now();
    let params_verifier = halo2_params.verifier_params();
    let strategy = SingleStrategy::new(&params_verifier);
    let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(proof);
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
        &[&[public_inputs]],
        &mut transcript,
    )
    .unwrap();
    println!("Verification: plonk proof verification (ms): {:?}", curr_time.elapsed().as_millis());
}

fn batch_lookup_verify(
    pp: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    proofs: &[Proof<Bn254>],
    statements: &[G1Affine],
) {
    tpp_list
        .par_iter()
        .zip(proofs.par_iter())
        .zip(statements.par_iter())
        .for_each(|((tpp, proof), statement)| {
            let ark_statement = halo2_to_ark_g1_affine(statement);
            verify(pp, tpp, ark_statement, proof, &mut OsRng).unwrap();
        });
}
