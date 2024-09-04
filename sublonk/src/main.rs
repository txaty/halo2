mod plonk_circuit;
mod bn254_convert;

use crate::plonk_circuit::MyCircuit;
use halo2_backend::plonk::{ProvingKey, VerifyingKey};
use halo2_backend::poly::commitment::ParamsProver;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_backend::poly::kzg::strategy::SingleStrategy;
use halo2_backend::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
};
use halo2_frontend::circuit::Value;
use halo2_middleware::halo2curves::bn256::{Bn256, Fr, G1Affine};
use halo2_proofs::arithmetic::Field;
use halo2_proofs::plonk::{keygen_pk, sublonk_create_proof, sublonk_keygen_vk};
use rand_core::OsRng;
use halo2_backend::plonk::sublonk::sublonk_verify_proof;

fn keygen(k: u32) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
    let params: ParamsKZG<Bn256> = ParamsKZG::<Bn256>::new(k);

    let empty_circuit: MyCircuit<Fr> = MyCircuit {
        a: Value::unknown(),
        k,
    };
    let vk = sublonk_keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    (params, pk)
}

fn prover(k: u32, params: &ParamsKZG<Bn256>, pk: &ProvingKey<G1Affine>) -> Vec<u8> {
    let rng = OsRng;

    let circuit: MyCircuit<Fr> = MyCircuit {
        a: Value::known(Fr::random(rng)),
        k,
    };

    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);
    sublonk_create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        MyCircuit<Fr>,
    >(params, pk, &[circuit], &[&[]], rng, &mut transcript)
    .expect("proof generation should not fail");

    transcript.finalize()
}

fn verifier(params: &ParamsKZG<Bn256>, vk: &VerifyingKey<G1Affine>, proof: &[u8]) {
    let params_verifier = params.verifier_params();
    let strategy = SingleStrategy::new(&params_verifier);
    let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(proof);
    assert!(sublonk_verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<Bn256>,
    >(&params_verifier, vk, strategy, &[&[]], &mut transcript)
    .is_ok());
}

fn main() {
    let k: u32 = 3;
    let (params, pk) = keygen(k);
    let proof = prover(k, &params, &pk);
    verifier(&params, pk.get_vk(), proof.as_ref());
}
