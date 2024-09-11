use crate::bn254_convert::ark_to_halo2_g1_affine;
use crate::plonk_circuit::TwoFanInCircuit;
use ark_bn254::Bn254;
use ark_segmentlookup::prover::{prove, Proof};
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::{Table, TablePreprocessedParameters};
use ark_segmentlookup::witness::Witness;
use halo2_backend::plonk::ProvingKey;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::ProverSHPLONK;
use halo2_backend::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
use halo2_frontend::circuit::Value;
use halo2_proofs::plonk::sublonk_create_proof;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;

pub(crate) fn prover<C>(
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

    let (fixed_lookup_proofs, fixed_lookup_statements) =
        batch_lookup_create_proof(pp, fixed_tpp_list, fixed_tables, &[table_index]);

    let (permutation_lookup_proofs, permutation_lookup_statements) =
        batch_lookup_create_proof(pp, permutation_tpp_list, permutation_tables, &[table_index]);

    (
        transcript.finalize(),
        fixed_lookup_proofs,
        permutation_lookup_proofs,
        fixed_lookup_statements,
        permutation_lookup_statements,
    )
}

fn batch_lookup_create_proof(
    pp: &PublicParameters<Bn254>,
    tpp_list: &[TablePreprocessedParameters<Bn254>],
    tables: &[Table<Bn254>],
    queried_indices: &[usize],
) -> (Vec<Proof<Bn254>>, Vec<G1Affine>) {
    let witnesses = tables
        .iter()
        .map(|table| Witness::new(pp, table, queried_indices).unwrap())
        .collect::<Vec<_>>();

    let statements = witnesses
        .iter()
        .map(|witness| {
            let ark_statement = witness.generate_statement(&pp.g1_affine_srs);

            ark_to_halo2_g1_affine(&ark_statement)
        })
        .collect::<Vec<_>>();

    let proofs: Vec<_> = tables
        .iter()
        .zip(tpp_list.iter())
        .zip(witnesses.iter())
        .map(|((table, tpp), witness)| prove(pp, table, tpp, witness, &mut OsRng).unwrap())
        .collect();

    (proofs, statements)
}
