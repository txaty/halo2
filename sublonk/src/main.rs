mod bn254_convert;
mod kzg_params;
mod plonk_circuit;
mod preprocess;

use crate::bn254_convert::{
    ark_to_halo2_g1_affine, ark_to_halo2_scalar_field, halo2_to_ark_g1_affine,
};
use crate::kzg_params::halo2_kzg_params_from_tau;
use crate::plonk_circuit::{AddCircuit, CircuitEnum, MulCircuit, TwoFanInCircuit};
use crate::preprocess::build_segment_lookup_table;
use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::prover::{prove, Proof};
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_segmentlookup::verifier::verify;
use ark_segmentlookup::witness::Witness;
use ark_std::UniformRand;
use halo2_backend::plonk::sublonk::{sublonk_verify_proof, SublonkVerifyingKey};
use halo2_backend::plonk::ProvingKey;
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
use halo2_proofs::plonk::{sublonk_create_proof, sublonk_keygen_pk, sublonk_keygen_vk};
use rand_core::OsRng;

fn keygen(
    k: u32,
    num_table_segments: usize,
    num_witness_segments: usize,
    circuits: &[CircuitEnum<Fr>],
) -> (
    ParamsKZG<Bn256>,
    PublicParameters<Bn254>,
    Vec<ProvingKey<G1Affine>>,
) {
    let ark_tau = <Bn254 as Pairing>::ScalarField::rand(&mut OsRng);
    let halo2_tau = ark_to_halo2_scalar_field(ark_tau);
    let params: ParamsKZG<Bn256> = halo2_kzg_params_from_tau(k, halo2_tau);

    let segment_size = 1 << k;
    let lookup_pp = PublicParameters::setup_with_tau(
        num_table_segments,
        num_witness_segments,
        segment_size,
        ark_tau,
    )
    .unwrap();

    let mut pk_list = Vec::with_capacity(circuits.len());
    for circuit in circuits {
        let vk = sublonk_keygen_vk(&params, circuit).unwrap();
        let pk = sublonk_keygen_pk(&params, vk, circuit).unwrap();
        pk_list.push(pk);
    }

    (params, lookup_pp, pk_list)
}

fn prover<C>(
    k: u32,
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    a: Fr,
    b: Fr,
    public_input: Fr,
    pp: &PublicParameters<Bn254>,
    fixed_tables: &[Table<Bn254>],
    permutation_tables: &[Table<Bn254>],
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    table_index: usize,
) -> (
    Vec<u8>,
    Vec<Proof<Bn254>>,
    Vec<Proof<Bn254>>,
    Vec<G1Affine>,
    Vec<G1Affine>,
)
where
    C: TwoFanInCircuit<Fr>,
{
    let rng = OsRng;

    let circuit = C::new(Value::known(a), Value::known(b), k);

    let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<G1Affine>>::init(vec![]);
    sublonk_create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        OsRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        C,
    >(
        params,
        pk,
        &[circuit],
        &[&[&[public_input]]],
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");

    let fixed_lookup_witness = fixed_tables
        .iter()
        .map(|table| Witness::new(pp, table, &[table_index]).unwrap())
        .collect::<Vec<_>>();

    let fixed_lookup_statements = fixed_lookup_witness
        .iter()
        .map(|witness| {
            let ark_statement = witness.generate_statement(&pp.g1_affine_srs);

            ark_to_halo2_g1_affine(&ark_statement)
        })
        .collect::<Vec<_>>();

    let mut fixed_lookup_proofs = Vec::with_capacity(fixed_tables.len());
    for i in 0..fixed_tables.len() {
        let lookup_proof = prove(
            pp,
            &fixed_tables[i],
            &fixed_tpp_list[i],
            &fixed_lookup_witness[i],
            &mut OsRng,
        )
        .unwrap();
        fixed_lookup_proofs.push(lookup_proof);
    }

    let permutation_lookup_witness = permutation_tables
        .iter()
        .map(|table| Witness::new(pp, table, &[table_index]).unwrap())
        .collect::<Vec<_>>();

    let permutation_lookup_statements = permutation_lookup_witness
        .iter()
        .map(|witness| {
            let ark_statement = witness.generate_statement(&pp.g1_affine_srs);

            ark_to_halo2_g1_affine(&ark_statement)
        })
        .collect::<Vec<_>>();

    let mut permutation_lookup_proofs = Vec::with_capacity(permutation_tables.len());
    for i in 0..permutation_tables.len() {
        let lookup_proof = prove(
            pp,
            &permutation_tables[i],
            &permutation_tpp_list[i],
            &permutation_lookup_witness[i],
            &mut OsRng,
        )
        .unwrap();
        permutation_lookup_proofs.push(lookup_proof);
    }

    (
        transcript.finalize(),
        fixed_lookup_proofs,
        permutation_lookup_proofs,
        fixed_lookup_statements,
        permutation_lookup_statements,
    )
}

fn verifier(
    params: &ParamsKZG<Bn256>,
    sublonk_vk: &SublonkVerifyingKey<G1Affine>,
    proof: &[u8],
    public_input: Fr,
    pp: &PublicParameters<Bn254>,
    fixed_tpp_list: &[TablePreprocessedParameters<Bn254>],
    permutation_tpp_list: &[TablePreprocessedParameters<Bn254>],
    fixed_lookup_proofs: &[Proof<Bn254>],
    permutation_lookup_proofs: &[Proof<Bn254>],
    fixed_lookup_statements: &[G1Affine],
    permutation_lookup_statements: &[G1Affine],
) {
    // Segment Lookup Verification
    for ((tpp, proof), statement) in fixed_tpp_list
        .iter()
        .zip(fixed_lookup_proofs.iter())
        .zip(fixed_lookup_statements.iter())
    {
        let ark_statement = halo2_to_ark_g1_affine(statement);
        verify(pp, tpp, ark_statement, proof, &mut OsRng).unwrap();
    }

    for ((tpp, proof), statement) in permutation_tpp_list
        .iter()
        .zip(permutation_lookup_proofs.iter())
        .zip(permutation_lookup_statements.iter())
    {
        let ark_statement = halo2_to_ark_g1_affine(statement);
        verify(pp, tpp, ark_statement, proof, &mut OsRng).unwrap();
    }

    let params_verifier = params.verifier_params();
    let strategy = SingleStrategy::new(&params_verifier);
    let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<G1Affine>>::init(proof);
    sublonk_verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<Bn256>,
    >(
        &params_verifier,
        sublonk_vk,
        strategy,
        &[&[&[public_input]]],
        &mut transcript,
        fixed_lookup_statements,
        permutation_lookup_statements,
    )
    .unwrap();
}

fn main() {
    let k: u32 = 3;

    let curr_time = std::time::SystemTime::now();
    let add_circuit = AddCircuit {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
        k,
    };
    let mul_circuit = MulCircuit {
        a: Value::<Fr>::unknown(),
        b: Value::<Fr>::unknown(),
        k,
    };
    let circuits = vec![CircuitEnum::Add(add_circuit), CircuitEnum::Mul(mul_circuit)];

    let (kzg_params, lookup_pp, pk_list) = keygen(k, 2, 1, &circuits);

    let (fixed_lookup_tables, permutation_lookup_tables) =
        build_segment_lookup_table(&kzg_params, &lookup_pp, &circuits);
    let fixed_tpp_list = fixed_lookup_tables
        .iter()
        .map(|table| table.preprocess(&lookup_pp).unwrap())
        .collect::<Vec<_>>();
    let permutation_tpp_list = permutation_lookup_tables
        .iter()
        .map(|table| table.preprocess(&lookup_pp).unwrap())
        .collect::<Vec<_>>();
    println!(
        "Preprocessing Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );

    let a = Fr::from(3);
    let b = Fr::from(4);
    let public_input = Fr::from(7);

    println!("Add Circuit");
    let pk = &pk_list[0];
    let curr_time = std::time::SystemTime::now();
    let (proof, fixed_proofs, permutation_proofs, fixed_statements, permutation_statements) =
        prover::<AddCircuit<_>>(
            k,
            &kzg_params,
            &pk,
            a,
            b,
            public_input,
            &lookup_pp,
            &fixed_lookup_tables,
            &permutation_lookup_tables,
            &fixed_tpp_list,
            &permutation_tpp_list,
            0,
        );
    println!(
        "Proving Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );
    let curr_time = std::time::SystemTime::now();
    verifier(
        &kzg_params,
        &pk.get_sublonk_vk(),
        proof.as_ref(),
        public_input,
        &lookup_pp,
        &fixed_tpp_list,
        &permutation_tpp_list,
        &fixed_proofs,
        &permutation_proofs,
        &fixed_statements,
        &permutation_statements,
    );
    println!(
        "Verification Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );

    let a = Fr::from(2);
    let b = Fr::from(5);
    let public_input = Fr::from(10);

    println!("Mul Circuit");
    let pk = &pk_list[1];
    let curr_time = std::time::SystemTime::now();
    let (proof, fixed_proofs, permutation_proofs, fixed_statements, permutation_statements) =
        prover::<MulCircuit<_>>(
            k,
            &kzg_params,
            &pk,
            a,
            b,
            public_input,
            &lookup_pp,
            &fixed_lookup_tables,
            &permutation_lookup_tables,
            &fixed_tpp_list,
            &permutation_tpp_list,
            1,
        );
    println!(
        "Proving Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );

    let curr_time = std::time::SystemTime::now();
    verifier(
        &kzg_params,
        &pk.get_sublonk_vk(),
        proof.as_ref(),
        public_input,
        &lookup_pp,
        &fixed_tpp_list,
        &permutation_tpp_list,
        &fixed_proofs,
        &permutation_proofs,
        &fixed_statements,
        &permutation_statements,
    );
    println!(
        "Verification Time: {:?}",
        curr_time.elapsed().unwrap().as_millis()
    );
}
