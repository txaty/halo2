use crate::keygen::generate_verification_key;
use crate::lookup::{batch_lookup_verify, recover_statements};
use crate::permutation::verify_permutation_proof;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::prover::Proof;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::TablePreprocessedParameters;
use halo2_backend::plonk::verifier::verify_proof;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::VerifierSHPLONK;
use halo2_backend::poly::kzg::strategy::SingleStrategy;
use halo2_backend::transcript::{Blake2bRead, Challenge255, TranscriptReadBuffer};
use halo2_middleware::circuit::ConstraintSystemMid;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rayon::prelude::*;

pub(crate) fn sublonk_verify(
    halo2_params: &ParamsKZG<Bn256>,
    lookup_params: &PublicParameters<Bn254>,
    proof: &[u8],
    public_inputs: &[Fr],
    witness_cs: &ConstraintSystemMid<Fr>,
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    fixed_lookup_proofs: &[Proof<Bn254>],
    permutation_lookup_proofs: &[Proof<Bn254>],
    fixed_statements: &[<Bn254 as Pairing>::G1Affine],
    permutation_statements: &[<Bn254 as Pairing>::G1Affine],
    padded_permutation_statements: &[<Bn254 as Pairing>::G1Affine],
    permutation_padding_commitments: &[<Bn254 as Pairing>::G1Affine],
    g2_affine_u: <Bn254 as Pairing>::G2Affine,
    permutation_proof: &[<Bn254 as Pairing>::G1],
) {
    let curr_time = std::time::Instant::now();
    batch_lookup_verify(
        lookup_params,
        fixed_tpp_list,
        fixed_lookup_proofs,
        fixed_statements,
    );

    batch_lookup_verify(
        lookup_params,
        permutation_tpp_list,
        permutation_lookup_proofs,
        permutation_statements,
    );

    let fixed_statements = recover_statements(fixed_statements, fixed_tpp_list);
    let permutation_statements = recover_statements(permutation_statements, permutation_tpp_list);

    permutation_statements
        .par_iter()
        .zip(padded_permutation_statements)
        .zip(permutation_padding_commitments)
        .zip(permutation_proof)
        .for_each(
            |(
                (
                    (&permutation_statement, &padded_permutation_statement),
                    &permutation_padding_commitment,
                ),
                &permutation_proof,
            )| {
                verify_permutation_proof::<Bn254>(
                    g2_affine_u,
                    permutation_statement,
                    padded_permutation_statement,
                    permutation_padding_commitment,
                    permutation_proof,
                    lookup_params.g2_affine_zv,
                );
            },
        );

    println!(
        "Verification: lookup proof verification (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );

    let curr_time = std::time::Instant::now();
    let vk = generate_verification_key(
        halo2_params,
        witness_cs,
        &fixed_statements,
        padded_permutation_statements,
    );
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
    println!(
        "Verification: plonk proof verification (ms):\n{:?}",
        curr_time.elapsed().as_millis()
    );
}
