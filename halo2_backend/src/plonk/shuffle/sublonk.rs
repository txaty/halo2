use std::iter;
use halo2_middleware::poly::Rotation;
use crate::arithmetic::CurveAffine;
use crate::plonk::ChallengeX;
use crate::plonk::shuffle::verifier::Evaluated;
use crate::poly::commitment::MSM;
use crate::poly::{EvaluationDomain, VerifierQuery};

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn queries_with_domain<'r, M: MSM<C> + 'r>(
        &'r self,
        domain: &EvaluationDomain<C::Scalar>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let x_next = domain.rotate_omega(*x, Rotation::next());

        iter::empty()
            // Open shuffle product commitment at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                *x,
                self.product_eval,
            )))
            // Open shuffle product commitment at \omega x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                x_next,
                self.product_next_eval,
            )))
    }
}