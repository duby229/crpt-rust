//! # L6.5 — Regime-Type Determinacy
//!
//! Exact realization of spec section **L6.5** (`CRPT_OMEGA_TOWER_L6.md`, v1.0.0-rc4):
//!
//! - L6.5.D1 `RTD` — a substrate's regime type (WF / NWF / Mixed) is an *objective
//!   structural consequence* of (𝒰_M, ρ_M), fixed by which elements' ρ_M-orbits reach
//!   `Fix(ρ_M)`. It is computed, never assumed.
//! - L6.5.T1 `RTD-Det` — the regime type is read off the substrate (the partition
//!   ↓_M ⊔ ∞_M is determined by ρ_M before any axiom is imposed).
//! - L6.5.T2 `RTD-Dec` — for a finite substrate the regime type is **decidable** by
//!   bounded orbit exploration (each orbit reaches `Fix` within `|𝒰_M|` steps or enters
//!   a fixpoint-free cycle). [`regime_type`] *is* that decision procedure.
//! - L6.5.T5 `RegType-Tri` — exactly three regime types exist; there is no fourth.
//!
//! (L6.5.T3 `RTD-Und` — undecidable for infinite substrates — and L6.5.T4 `RTD-NI` —
//! not internally expressible — are meta-level statements about the *limits* of this
//! decision procedure; they bound the finite engine rather than being realized in it.)

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::{is_convergent, is_persistent};

/// **L6.5.D1 (`RTD`)** — the regime type of a model. `==` compares the computed tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegimeType {
    /// **WF** — `∞_M = ∅`: every ρ_M-orbit reaches a fixpoint.
    WellFounded,
    /// **NWF** — `↓_M = ∅`: no ρ_M-orbit reaches a fixpoint (all persist).
    NonWellFounded,
    /// **Mixed** — both `↓_M ≠ ∅` and `∞_M ≠ ∅`.
    Mixed,
}

/// **L6.5.T2 (`RTD-Dec`)** — decide the regime type of a (finite) model by exhaustive
/// orbit exploration: WF iff `∞_M = ∅`, NWF iff `↓_M = ∅`, Mixed iff both non-empty.
///
/// Panics only on the empty universe (excluded: models have non-empty `𝒰_M`).
pub fn regime_type(op: &ProjectionOperator) -> RegimeType {
    let mut has_convergent = false;
    let mut has_persistent = false;
    for x in op.substrate().elements() {
        // L6.5.T2: ↓_M-membership is decided by bounded orbit exploration (≤ |𝒰_M| steps).
        if op.canonical_fixpoint(x).is_some() {
            has_convergent = true;
        } else {
            has_persistent = true;
        }
    }
    match (has_convergent, has_persistent) {
        (true, false) => RegimeType::WellFounded,
        (false, true) => RegimeType::NonWellFounded,
        (true, true) => RegimeType::Mixed,
        (false, false) => unreachable!("a model has a non-empty universe (L6.5.T5)"),
    }
}

/// Witness **L6.5.T5 (`RegType-Tri`)** / **L2.2.T3 (`Part`)** — the element-level
/// dichotomy `↓_M ⊔ ∞_M = 𝒰_M`: every element is convergent *xor* persistent (so the
/// three model-level regime types are exhaustive). Returns the first element that is
/// neither or both, or `Ok`.
pub fn certify_regime_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_convergent(op, x) == is_persistent(op, x) {
            return Err(x); // neither (both false) or both (both true) — impossible
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;
    use crate::l2::projection::Model;

    fn regime_of(edges: &[(u32, u32)], n: u32) -> RegimeType {
        let m = Model::from_functional_reduction(Substrate::new(n, edges, edges).unwrap()).unwrap();
        regime_type(&m.operator())
    }

    #[test]
    fn well_founded_when_all_orbits_terminate() {
        // 0→1, 1 ∈ NF: ∞_M = ∅.
        assert_eq!(regime_of(&[(0, 1)], 2), RegimeType::WellFounded);
    }

    #[test]
    fn non_well_founded_when_no_orbit_terminates() {
        // 0⇄1: a pure cycle, no fixpoint, ↓_M = ∅.
        assert_eq!(regime_of(&[(0, 1), (1, 0)], 2), RegimeType::NonWellFounded);
    }

    #[test]
    fn mixed_when_both_regimes_present() {
        // 0⇄1 (∞_M) and 2→3, 3 ∈ NF (↓_M).
        let edges = [(0, 1), (1, 0), (2, 3)];
        let m = Model::from_functional_reduction(Substrate::new(4, &edges, &edges).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(regime_type(&op), RegimeType::Mixed);
        // the element-level partition is exhaustive and disjoint.
        assert!(matches!(certify_regime_partition(&op), Ok(())));
    }
}
