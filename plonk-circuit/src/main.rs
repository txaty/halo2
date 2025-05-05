mod bench_circuit;
mod plonk_circuit;

use crate::bench_circuit::BenchCircuit;
use halo2_backend::arithmetic::Field;
use halo2_backend::plonk::verifier::verify_proof;
use halo2_backend::plonk::{ProvingKey, VerifyingKey};
use halo2_backend::poly::commitment::ParamsProver;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_backend::poly::kzg::strategy::SingleStrategy;
use halo2_backend::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
};
use halo2_frontend::circuit::Value;
use halo2_middleware::halo2curves::bn256::Fr;
use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk};
use halo2curves::bn256::{Bn256, G1Affine};
use rand_core::OsRng;

fn generate_inputs(num_rows: usize) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    let a: Vec<Fr> = (0..num_rows).map(|_| Fr::random(OsRng)).collect();
    let b: Vec<Fr> = (0..num_rows).map(|_| Fr::random(OsRng)).collect();
    let public_inputs: Vec<Fr> = (0..num_rows).map(|i| a[i] + b[i]).collect();

    (a, b, public_inputs)
}

fn keygen(k: u32, num_rows: usize) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
    let params: ParamsKZG<Bn256> = ParamsKZG::<Bn256>::new(k);
    let unknown_a_vec = vec![Value::unknown(); num_rows];
    let unknown_b_vec = vec![Value::unknown(); num_rows];
    let empty_circuit: BenchCircuit<Fr> = BenchCircuit {
        a: unknown_a_vec,
        b: unknown_b_vec,
        num_rows,
    };

    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    (params, pk)
}

fn prover(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    a: Vec<Fr>,
    b: Vec<Fr>,
    sum: Vec<Fr>,
    num_rows: usize,
) -> Vec<u8> {
    let rng = OsRng;

    let circuit: BenchCircuit<Fr> = BenchCircuit {
        a: a.iter().map(|x| Value::known(*x)).collect(),
        b: b.iter().map(|x| Value::known(*x)).collect(),
        num_rows,
    };

    let proving_time = std::time::Instant::now();
    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        BenchCircuit<Fr>,
    >(params, pk, &[circuit], &[&[&sum]], rng, &mut transcript)
    .expect("proof generation should not fail");

    let proof = transcript.finalize();
    log::info!("Proving time: {:?}", proving_time.elapsed());
    log::info!("Proof size: {} bytes", proof.len());

    proof
}

fn verifier(params: &ParamsKZG<Bn256>, vk: &VerifyingKey<G1Affine>, sum: Vec<Fr>, proof: &[u8]) {
    let params_verifier = params.verifier_params();
    let strategy = SingleStrategy::new(&params_verifier);
    let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(proof);

    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<Bn256>,
    >(&params_verifier, vk, strategy, &[&[&sum]], &mut transcript)
    .is_ok());
}

fn main() {
    env_logger::init();
    log::info!("Rayon Threads: {}", rayon::current_num_threads());

    let log_num_rows_per_tx_range = 4..23;
    const LOG_NUM_TX: usize = 10;

    for log_num_rows_per_tx in log_num_rows_per_tx_range {
        let k = (log_num_rows_per_tx + LOG_NUM_TX) as u32;
        log::info!("Running with k = {}", k);
        let num_rows = (1 << k) - (1 << log_num_rows_per_tx);
        log::info!("num_rows = {}", num_rows);
        let (a, b, public_inputs) = generate_inputs(num_rows);
        let (params, pk) = keygen(k, num_rows);
        let proof = prover(
            &params,
            &pk,
            a.clone(),
            b.clone(),
            public_inputs.clone(),
            num_rows,
        );
        let vk = pk.get_vk();
        verifier(&params, vk, public_inputs.clone(), &proof);
    }
}
