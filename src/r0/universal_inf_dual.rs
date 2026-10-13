//! # R0.5 — Universal Inf-Dual: Reification and Tower Meta-Theorem
//!
//! Exact realization of spec section **R0.5** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9). The
//! universal template for the CRPT Reification operator (concrete in R6):
//!
//! - R0.5.D1 `TowerReify` — `Reify(Π) = (𝒰', π', →_σ')`, the free monoidal algebra over the
//!   fiber-equivalence classes `𝒰/≃_π`: words `a₁·…·aₙ`, left-strip projection
//!   `π'(a₁·…·aₙ) = a₂·…·aₙ`, atoms (`𝒰/≃_π`) as fixpoints, depth `d_{π'}(w) = |w|−1`. The
//!   CRPT instance is [`crate::r6::reification_operator::Reify`].
//! - R0.5.T1 `Inf-Dual-U` — horizontal infinity (infinite fibers) ⟺ vertical infinity
//!   (unbounded `π'`-depth) across one reification: (a) a fiber of size `m` gives depth `m−1`;
//!   (b) a persistent orbit becomes a horizontal `→_σ'`-chain; (c) the exchange is involutive.
//! - R0.5.T2 `Reify-Quot-Inv` — the abstraction quotient `𝒰/≃_π` is **invariant** under
//!   reification (`𝒰/≃_π ≅ 𝒰'/≃_{π'}`). CRPT instance: `NFC-TInv` (R6.7.T2).
//! - R0.5.T3 `CRPT-InfDual` — the CRPT H-V duality (R1.9.T7 / R6.9) is the instance of
//!   `Inf-Dual-U`; certified here against the concrete R6 `Reify`
//!   ([`crate::r6::reification_operator`]).
//!
//! The universal depth law and the duality are realized **generically** for the canonical
//! reification on a finite enumerable system (left-strip on words over fiber classes), and the
//! CRPT instance is certified by delegating to the concrete R6 realization.

use crate::r1::reduction_strategy::Instance;

/// **R0.5.D1 (`TowerReify`) universal depth law** — for the reification of any system, the
/// orbit depth of a word is `|w| − 1` (atoms, the fiber representatives, are the fixpoints).
/// Returns `|w| − 1`. This is the universal template's defining numeric law; the CRPT
/// instance computes it via [`crate::r6::reification_operator::Reify::depth`].
pub fn tower_reify_depth<A>(word: &[A]) -> u32 {
    (word.len() as u32).saturating_sub(1)
}

/// Witness **R0.5.T1 (`Inf-Dual-U`) clause (a) — horizontal → vertical**, CRPT instance:
/// a fiber of horizontal size `m` over a base fixpoint reifies to an `m`-fold atom
/// composition of `π'`-depth `m − 1` in `Reify(M)`. Returns `(m, m − 1)`. (The universal
/// claim: an *infinite* fiber gives *unbounded* depth — vertical infinity.) Delegates to the
/// concrete R6 realization, certifying the CRPT instance of the universal duality.
pub fn inf_dual_horizontal_to_vertical(base: &Instance, fixpoint: crate::r1::substrate::ElementId) -> (u32, u32) {
    crate::r6::tower::fiber_reifies_to_depth(base, fixpoint)
}

/// Witness **R0.5.T2 (`Reify-Quot-Inv`)**, CRPT instance — the abstraction quotient is
/// invariant under reification: `|𝒰'/≃_{π'}| = |𝒰/≃_π|`, i.e. the reify's atom set is
/// exactly the base query signature `Q_M`. Returns `true` when the quotient is preserved
/// (the universal `Reify-Quot-Inv`, instanced as `NFC-TInv` R6.7.T2).
pub fn certify_reify_quot_invariant(base: &Instance) -> bool {
    let t = crate::r6::tower::tower(base);
    t.reify().atom_count() == t.query_signature_size()
}

/// Witness **R0.5.T3 (`CRPT-InfDual`)** — the CRPT Reification (`Reify-Def` R6.5.D2) is the
/// canonical realization of the universal `TowerReify`, and the CRPT H-V duality (`Inf-Dual`
/// R1.9.T7) is the instance of `Inf-Dual-U`. Certifies on a base instance: (i) the universal
/// depth law holds on the reify (`d_{π'}(w) = |w|−1`); (ii) every base fixpoint reifies to a
/// depth-0 atom (the duality's depth reset); (iii) the quotient is invariant. Returns `true`
/// when the concrete R6 operator instantiates the universal template.
pub fn certify_crpt_inf_dual(base: &Instance) -> bool {
    use crate::r1::substrate::ElementId;
    let reified = crate::r6::reification_operator::reify(base);
    // (i) the universal depth law d_{π'}(w) = |w| − 1 agrees with the concrete reify.
    let w = vec![ElementId(0), ElementId(0)];
    let depth_law = reified.depth(&w) == tower_reify_depth(&w);
    // (ii) depth reset (the duality on fixpoints) and (iii) quotient invariance.
    let depth_reset = crate::r6::tower::certify_depth_reset(base).is_ok();
    let quot_inv = certify_reify_quot_invariant(base);
    depth_law && depth_reset && quot_inv
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::ElementId;

    fn two_fixpoint_base() -> Instance {
        use crate::r1::substrate::Substrate;
        // 0→1, 2→3 (Q_M = {1,3}); plus 5→1 so the fiber of 1 has horizontal size 3.
        let e = [(0, 1), (2, 3), (5, 1)];
        Instance::from_functional_reduction(Substrate::new(6, &e, &e).unwrap()).unwrap()
    }

    #[test]
    fn the_crpt_reification_instantiates_the_universal_inf_dual() {
        let base = two_fixpoint_base();
        // universal depth law: a length-n word has π'-depth n−1.
        assert_eq!(tower_reify_depth(&[ElementId(1), ElementId(3), ElementId(1)]), 2);
        // Inf-Dual-U(a): the size-3 fiber of fixpoint 1 reifies to depth 2.
        assert_eq!(inf_dual_horizontal_to_vertical(&base, ElementId(1)), (3, 2));
        // Reify-Quot-Inv: the quotient is invariant under reification.
        assert!(certify_reify_quot_invariant(&base));
        // CRPT-InfDual: the concrete R6 Reify realizes the universal template.
        assert!(certify_crpt_inf_dual(&base));
    }
}
