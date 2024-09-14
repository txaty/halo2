use crate::arithmetic::{parallelize, CurveAffine};
use crate::plonk::circuit::ConstraintSystemBack;
use crate::plonk::permutation::sublonk::build_permutation_poly_coeff_list;
use crate::plonk::permutation::ProvingKey as PermutationProvingKey;
use crate::plonk::{permutation, Error, Evaluator, ProvingKey, VerifyingKey};
use crate::poly::{commitment::Params, EvaluationDomain, Polynomial};
use halo2_middleware::circuit::{CompiledCircuit, ConstraintSystemMid};
use halo2_middleware::ff::{Field, FromUniformBytes};

/// Generate a `VerifyingKey` from an instance of `CompiledCircuit`.
pub fn keygen_vk<C, P>(
    params: &P,
    circuit: &CompiledCircuit<C::Scalar>,
    fixed_statements: &[C],
    permutation_statements: &[C],
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
    C::Scalar: FromUniformBytes<64>,
{
    let cs_mid = &circuit.cs;
    let cs: ConstraintSystemBack<C::Scalar> = cs_mid.clone().into();
    let domain = EvaluationDomain::new(cs.degree() as u32, params.k());

    if (params.n() as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    // println!("cs mid {:?}", cs_mid);
    // println!("cs {:?}", cs);

    // println!("cs mid permutations: {:?}", cs_mid.permutation);
    // println!(
    //     "preprocessing permutations: {:?}",
    //     circuit.preprocessing.permutation
    // );

    // let permutation_vk = permutation::keygen::Assembly::new_from_assembly_mid(
    //     params.n() as usize,
    //     &cs_mid.permutation,
    //     &circuit.preprocessing.permutation,
    // )?
    // .sublonk_build_vk(params, &domain, &cs.permutation);

    // println!("permutation_vk: {:?}", permutation_vk);

    // println!(
    //     "fixed column field elements list: {:?}",
    //     circuit.preprocessing.fixed
    // );

    // for (i, fixed) in circuit.preprocessing.fixed.iter().enumerate() {
    //     println!("keygen fixed column {}: {:?}", i, fixed);
    // }

    // println!("constraint system gates: {:?}", cs.gates);

    // let fixed_commitments = {
    //     let fixed_commitments_projective: Vec<C::CurveExt> = circuit
    //         .preprocessing
    //         .fixed
    //         .iter()
    //         .map(|poly| {
    //             params.commit_lagrange(
    //                 &H2cEngine::new(),
    //                 &Polynomial::new_lagrange_from_vec(poly.clone()),
    //                 Blind::default(),
    //             )
    //         })
    //         .collect();
    //     let mut fixed_commitments = vec![C::identity(); fixed_commitments_projective.len()];
    //     C::CurveExt::batch_normalize(&fixed_commitments_projective, &mut fixed_commitments);
    //     fixed_commitments
    // };

    // println!("fixed_commitments: {:?}", fixed_commitments);

    Ok(VerifyingKey::from_parts(
        domain,
        fixed_statements.to_vec(),
        permutation::VerifyingKey {
            commitments: permutation_statements.to_vec(),
        },
        cs,
    ))
}

pub fn create_domain<C, P>(
    params: &P,
    circuit: &CompiledCircuit<C::Scalar>,
) -> EvaluationDomain<C::Scalar>
where
    C: CurveAffine,
    P: Params<C>,
    C::Scalar: FromUniformBytes<64>,
{
    let cs_mid = &circuit.cs;
    let cs: ConstraintSystemBack<C::Scalar> = cs_mid.clone().into();
    let domain = EvaluationDomain::new(cs.degree() as u32, params.k());

    domain
}

pub fn keygen_pk<C, P>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &CompiledCircuit<C::Scalar>,
    fixed_witnesses: &[Vec<C::Scalar>],
    permutation_witnesses: &[Vec<C::Scalar>],
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<C>,
{
    // let cs = &circuit.cs;

    if (params.n() as usize) < vk.cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    // Compute fixeds

    // TODO: Debug purpose only, remove this later.
    assert_eq!(circuit.preprocessing.fixed, fixed_witnesses);

    let fixed_polys: Vec<_> = fixed_witnesses
        .iter()
        .map(|poly| {
            vk.domain
                .lagrange_to_coeff(Polynomial::new_lagrange_from_vec(poly.clone()))
        })
        .collect();

    let fixed_cosets = fixed_polys
        .iter()
        .map(|poly| vk.domain.coeff_to_extended(poly.clone()))
        .collect();

    let fixed_values = fixed_witnesses
        .to_vec()
        // .clone()
        .into_iter()
        .map(Polynomial::new_lagrange_from_vec)
        .collect();

    // Compute l_0(X)
    // TODO: this can be done more efficiently
    // https://github.com/privacy-scaling-explorations/halo2/issues/269
    let mut l0 = vk.domain.empty_lagrange();
    l0[0] = C::Scalar::ONE;
    let l0 = vk.domain.lagrange_to_coeff(l0);
    let l0 = vk.domain.coeff_to_extended(l0);

    // Compute l_blind(X) which evaluates to 1 for each blinding factor row
    // and 0 otherwise over the domain.
    let mut l_blind = vk.domain.empty_lagrange();
    for evaluation in l_blind[..].iter_mut().rev().take(vk.cs.blinding_factors()) {
        *evaluation = C::Scalar::ONE;
    }
    let l_blind = vk.domain.lagrange_to_coeff(l_blind);
    let l_blind = vk.domain.coeff_to_extended(l_blind);

    // Compute l_last(X) which evaluates to 1 on the first inactive row (just
    // before the blinding factors) and 0 otherwise over the domain
    let mut l_last = vk.domain.empty_lagrange();
    l_last[params.n() as usize - vk.cs.blinding_factors() - 1] = C::Scalar::ONE;
    let l_last = vk.domain.lagrange_to_coeff(l_last);
    let l_last = vk.domain.coeff_to_extended(l_last);

    // Compute l_active_row(X)
    let one = C::Scalar::ONE;
    let mut l_active_row = vk.domain.empty_extended();
    parallelize(&mut l_active_row, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = i + start;
            *value = one - (l_last[idx] + l_blind[idx]);
        }
    });

    // Compute the optimized evaluation data structure
    let ev = Evaluator::new(&vk.cs);

    // Compute the permutation proving key
    // TODO: Disable this.
    // let permutation_pk = permutation::keygen::Assembly::new_from_assembly_mid(
    //     params.n() as usize,
    //     &cs.permutation,
    //     &circuit.preprocessing.permutation,
    // )?
    // .build_pk(params, &vk.domain, &cs.permutation.clone());

    // The permutation proving key contains
    // 1. Permutation polynomials in Lagrange evaluation form
    // 2. Permutation polynomials in coefficient form
    // 3. Permutation polynomials in coset coefficient form
    // TODO: Enable this.
    let permutation_pk = create_permutation_pk(&vk.domain, permutation_witnesses);

    Ok(ProvingKey {
        vk,
        l0,
        l_last,
        l_active_row,
        fixed_values,
        fixed_polys,
        fixed_cosets,
        permutation: permutation_pk,
        ev,
    })
}

fn create_permutation_pk<C>(
    domain: &EvaluationDomain<C::Scalar>,
    permutation_witnesses: &[Vec<C::Scalar>],
) -> PermutationProvingKey<C>
where
    C: CurveAffine,
{
    let mut permutations = Vec::with_capacity(permutation_witnesses.len());
    for witness in permutation_witnesses.iter() {
        let poly = domain.lagrange_from_vec(witness.clone());
        permutations.push(poly);
    }

    let mut polys = vec![domain.empty_coeff(); permutation_witnesses.len()];
    {
        parallelize(&mut polys, |o, start| {
            for (x, poly) in o.iter_mut().enumerate() {
                let i = start + x;
                let permutation_poly = permutations[i].clone();
                *poly = domain.lagrange_to_coeff(permutation_poly);
            }
        });
    }

    let mut cosets = vec![domain.empty_extended(); permutation_witnesses.len()];
    {
        parallelize(&mut cosets, |o, start| {
            for (x, coset) in o.iter_mut().enumerate() {
                let i = start + x;
                let poly = polys[i].clone();
                *coset = domain.coeff_to_extended(poly);
            }
        });
    }

    PermutationProvingKey {
        permutations,
        polys,
        cosets,
    }
}

impl<C: CurveAffine> ProvingKey<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    pub fn get_sublonk_vk(&self) -> SublonkVerifyingKey<C> {
        let original_vk = &self.vk;

        SublonkVerifyingKey {
            domain: original_vk.domain.clone(),
            cs: original_vk.cs.clone(),
            cs_degree: original_vk.cs.degree(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SublonkVerifyingKey<C: CurveAffine> {
    /// Evaluation domain
    pub domain: EvaluationDomain<C::Scalar>,
    /// Constraint system
    pub cs: ConstraintSystemBack<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    pub cs_degree: usize,
}

impl<C: CurveAffine> SublonkVerifyingKey<C> {
    pub fn new(k: u32, cs_mid: &ConstraintSystemMid<C::Scalar>) -> Self {
        let cs: ConstraintSystemBack<C::Scalar> = cs_mid.clone().into();
        let cs_degree = cs.degree();
        let domain = EvaluationDomain::new(cs_degree as u32, k);
        Self {
            domain,
            cs,
            cs_degree,
        }
    }
}

pub fn preprocessing_polynomial_coefficients<C, P>(
    sub_circuit_k: u32,
    params: &P,
    circuit: &CompiledCircuit<C::Scalar>,
) -> Result<(Vec<Vec<C::Scalar>>, Vec<Vec<C::Scalar>>), Error>
where
    C: CurveAffine,
    P: Params<C>,
    C::Scalar: FromUniformBytes<64>,
{
    let cs_mid = &circuit.cs;
    let cs: ConstraintSystemBack<C::Scalar> = cs_mid.clone().into();
    let domain = EvaluationDomain::new(cs.degree() as u32, sub_circuit_k);

    // if (params.n() as usize) < cs.minimum_rows() {
    //     return Err(Error::not_enough_rows_available(params.k()));
    // }

    let fixed_poly_coeffs = circuit.preprocessing.fixed.clone();

    // println!("cs mid permutations: {:?}", cs_mid.permutation);

    let assembly = permutation::keygen::Assembly::new_from_assembly_mid(
        params.n() as usize,
        &cs_mid.permutation,
        &circuit.preprocessing.permutation,
    )?;

    // println!("assembly: {:?}", assembly);

    let permutation_poly_coeffs =
        build_permutation_poly_coeff_list(params, &domain, &cs.permutation, |i, j| {
            assembly.mapping[i][j]
        });

    // for (i, fixed) in fixed_poly_coeffs.iter().enumerate() {
    //     println!("preprocessing fixed column {}: {:?}", i, fixed);
    // }

    Ok((fixed_poly_coeffs, permutation_poly_coeffs))
}
