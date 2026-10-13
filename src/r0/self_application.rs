//! # R0.10 — Self-Application and Meta-Consistency
//!
//! Exact realization of spec section **R0.10** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9) — the
//! universal HOA applied to itself:
//!
//! - R0.10.T1 `HOA-Self-Cons` — the universal HOA (R0.1–R0.9), treated as a projection system
//!   `Π_HOA` over its own constructs under the dependency projection, **terminates**:
//!   `Conv(π_HOA) = 𝒰_HOA`, `Fix(π_HOA) = {R0.1.D1}`, and R0.1.D1 (the projection-system
//!   definition) is **Class E** of its own HOA (a fixpoint with `H_S = ⊤`, `H_I = ⊥`). No
//!   infinite regress.
//! - R0.10.T2 `CRPT-Self-Cons` — the CRPT anchor, as the self-substrate under
//!   `→_{ρ_CRPT}`, satisfies all projection-system axioms with the level index as its rank.
//!   This is the universal-level template; the tower-level certificate is [`Rω.5`](crate::romega)
//!   (the ω-tower as a CRPT instance). Certified here by delegating to the Rω self-model.
//!
//! `HOA-Self-Cons` is realized concretely: the R0 sections R0.1–R0.10 form a dependency
//! instance whose unique root R0.1.D1 the engine's own six-class HOA classifies as Class E.

use crate::r1::reduction_strategy::Instance;
use crate::r1::substrate::{ElementId, Substrate};

/// `R0.1.D1` — the projection-system definition, the unique root / fixpoint of the HOA's own
/// dependency projection `π_HOA`.
pub const R0_1_D1: ElementId = ElementId(0);

/// **R0.10.T1 (`HOA-Self-Cons`)** — the universal HOA as a projection system `Π_HOA`: a
/// concrete dependency [`Instance`] over the R0 sections. R0.1.D1 (index 0) is the root that
/// every other section (R0.2…R0.10) depends on, so `Fix(π_HOA) = {R0.1.D1}` and every
/// section converges to it.
pub fn hoa_self_substrate() -> Instance {
    // R0.2 … R0.10 each depend directly on the projection-system definition R0.1.D1.
    let edges: Vec<(u32, u32)> = (1..10).map(|k| (k, 0)).collect();
    let substrate = Substrate::new(10, &edges, &edges).expect("HOA self-substrate is well-formed");
    Instance::from_functional_reduction(substrate).expect("the R0 dependency graph is functional")
}

/// Witness **R0.10.T1 (`HOA-Self-Cons`)** — the HOA applied to itself terminates, with
/// R0.1.D1 the unique fixpoint classified **Class E** by the engine's own six-class HOA, and
/// every section convergent (`Conv(π_HOA) = 𝒰_HOA`, no regress). Returns `true` when the HOA
/// self-classifies consistently.
pub fn certify_hoa_self_consistency() -> bool {
    let m = hoa_self_substrate();
    let op = m.operator();
    // Fix(π_HOA) = {R0.1.D1}.
    if op.fixpoints() != vec![R0_1_D1] {
        return false;
    }
    // R0.1.D1 is Class E of its own HOA (fixpoint, ramified, distinguishable).
    if crate::r2::six_class_horizon_partition::classify(&op, R0_1_D1)
        != Some(crate::r2::six_class_horizon_partition::HorizonClass::E)
    {
        return false;
    }
    // Conv(π_HOA) = 𝒰_HOA: every section reaches the root (no infinite regress).
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x) != Some(R0_1_D1) {
            return false;
        }
    }
    true
}

/// Witness **R0.10.T2 (`CRPT-Self-Cons`)** — the CRPT anchor is self-consistent: treated as
/// the self-substrate under `→_{ρ_CRPT}` it is a valid projection system with the level index
/// as rank. The universal template's tower-level certificate is Rω.5; this delegates to the
/// Rω self-model ([`crate::romega::self_projection_system::certify_self_model`]) and the
/// self-horizon recovery. Returns `true` when the anchor passes its own criteria.
pub fn certify_crpt_self_consistency() -> bool {
    crate::romega::self_projection_system::certify_self_model()
        && crate::romega::self_horizon::certify_self_horizon().is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_hoa_applied_to_itself_terminates_with_r0_1_d1_class_e() {
        assert!(certify_hoa_self_consistency()); // HOA-Self-Cons
        assert!(certify_crpt_self_consistency()); // CRPT-Self-Cons (delegates to Rω.5)
    }
}
