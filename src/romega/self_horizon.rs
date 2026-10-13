//! # Rω.2 — Self-Horizon Classification
//!
//! Exact realization of spec section **Rω.2** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9):
//!
//! - Rω.2.T1 `Self-Horiz` — the six-class partition (`6-Part` R2.2.T1) applied to the
//!   self-substrate `𝒰_CRPT`. The substrate definition **R1.1.D1 is Class E** (the unique
//!   fixpoint of `ρ_CRPT` whose preimage mixes the root with the boundary layer: `H_S = ⊤`,
//!   `H_I = ⊥`). The **boundary layer** — the depth-1 constructs anchored directly on
//!   R1.1.D1 — is **Class B** (ramified and distinguishable, since their kernel mixes the
//!   root fixpoint with depth-1 siblings). The deeper ramified constructs are **Class C**
//!   (ramified, indistinguishable): under the formal `H_I-Dec` criterion (R2.1.C1) a kernel
//!   of equal-depth siblings is `d_M`-uniform, so deep same-level constructs are
//!   not separated by the *invariant* horizon — the precise refinement of the spec's prose
//!   grouping ("distinguishable by structural role") that CRPT's own HOA computes. R0 and Rω
//!   are special (the meta-framework / the self-application itself).
//!
//! This is **computed, not asserted**: it calls
//! [`crate::r2::six_class_horizon_partition::classify`] — CRPT's own HOA — on the
//! self-instance, so the classification is whatever the engine's six-class machinery yields.

use crate::r1::substrate::ElementId;
use crate::r2::six_class_horizon_partition::{classify, HorizonClass};
use crate::romega::self_projection_system::self_substrate;

/// **Rω.2.T1 (`Self-Horiz`)** — the six-class of an anchor construct under the self-substrate,
/// computed by CRPT's own [`classify`]. `None` would indicate the HOA does not apply (it
/// applies to every element of the finite self-instance).
pub fn self_horizon_class(x: ElementId) -> Option<HorizonClass> {
    let m = self_substrate();
    classify(&m.operator(), x)
}

/// Witness **Rω.2.T1 (`Self-Horiz`)** — the self-classification CRPT's own HOA computes:
/// R1.1.D1 is **Class E**; the boundary layer (depth-1 constructs over the root) is
/// **Class B**; every deeper non-fixpoint is **Class C**; and **Class F is empty** (the HOA
/// applied to itself respects `F=∅` R2.2.T2). Returns the first element that violates this
/// realized partition, or `Ok`.
pub fn certify_self_horizon() -> Result<(), ElementId> {
    use crate::r1::derivation_height::{derivation_height, DerivationHeight};
    let m = self_substrate();
    let op = m.operator();
    for x in op.substrate().elements() {
        let expected = if op.is_fixpoint(x) {
            HorizonClass::E // R1.1.D1: the unique fixpoint, ramified + distinguishable
        } else if derivation_height(&op, x) == DerivationHeight::Finite(1) {
            HorizonClass::B // boundary layer: kernel mixes the root (d=0) and siblings (d=1)
        } else {
            HorizonClass::C // deeper ramified: equal-depth kernel ⇒ H_I = ⊤ (indistinguishable)
        };
        if classify(&op, x) != Some(expected) {
            return Err(x);
        }
    }
    // Class F is empty in the deterministic self-instance — the HOA on itself (F=∅, R2.2.T2).
    crate::r2::six_class_horizon_partition::certify_class_f_empty(&op)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::romega::self_projection_system::{R1_1_D1, RANK_CARRIERS};

    #[test]
    fn the_anchor_self_classifies_e_at_the_root_b_at_the_boundary_c_deeper() {
        assert!(matches!(certify_self_horizon(), Ok(())));
        // R1.1.D1 is the Class-E fixpoint (sink of the dependency DAG, ramified).
        assert_eq!(self_horizon_class(R1_1_D1), Some(HorizonClass::E));
        // the depth-1 boundary layer (R1 and its sibling) is Class B.
        assert_eq!(self_horizon_class(ElementId(1)), Some(HorizonClass::B));
        assert_eq!(self_horizon_class(ElementId(2)), Some(HorizonClass::B));
        // the deeper rank carriers (R2…R6) are Class C — equal-depth ramified siblings.
        for &c in &RANK_CARRIERS[1..] {
            assert_eq!(self_horizon_class(c), Some(HorizonClass::C));
        }
    }
}
