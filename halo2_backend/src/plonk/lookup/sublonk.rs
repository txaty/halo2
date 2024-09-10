use crate::arithmetic::CurveAffine;
use crate::plonk::lookup::verifier::Evaluated;
use crate::plonk::ChallengeX;
use crate::poly::commitment::MSM;
use crate::poly::{EvaluationDomain, VerifierQuery};
use halo2_middleware::poly::Rotation;
use std::iter;

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn queries_with_domain<'r, M: MSM<C> + 'r>(
        &'r self,
        domain: &EvaluationDomain<C::Scalar>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let x_inv = domain.rotate_omega(*x, Rotation::prev());
        let x_next = domain.rotate_omega(*x, Rotation::next());

        iter::empty()
            // Open lookup product commitment at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                *x,
                self.product_eval,
            )))
            // Open lookup input commitments at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.permuted.permuted_input_commitment,
                *x,
                self.permuted_input_eval,
            )))
            // Open lookup table commitments at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.permuted.permuted_table_commitment,
                *x,
                self.permuted_table_eval,
            )))
            // Open lookup input commitments at \omega^{-1} x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.permuted.permuted_input_commitment,
                x_inv,
                self.permuted_input_inv_eval,
            )))
            // Open lookup product commitment at \omega x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                x_next,
                self.product_next_eval,
            )))
    }
}
