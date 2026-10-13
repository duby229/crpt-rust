//! # R5.5 — Aspect-Type Determinacy
//!
//! Exact realization of spec section **R5.5** (`CRPT_OMEGA_TOWER_R5.md`, v1.0.0-rc9):
//!
//! - R5.5.D1 `ATD` — a substrate's aspect type (WF / NWF / Mixed) is an *objective
//!   structural consequence* of (𝒰_M, ρ_M), fixed by which elements' ρ_M-orbits reach
//!   `Fix(ρ_M)`. It is computed, never assumed.
//! - R5.5.T1 `ATD-Det` — the aspect type is read off the substrate (the partition
//!   ↓_M ⊔ ∞_M is determined by ρ_M before any axiom is imposed).
//! - R5.5.T2 `ATD-Dec` — for a finite substrate the aspect type is **decidable** by
//!   bounded orbit exploration (each orbit reaches `Fix` within `|𝒰_M|` steps or enters
//!   a fixpoint-free cycle). [`aspect_type`] *is* that decision procedure.
//! - R5.5.T5 `AspType-Tri` — exactly three aspect types exist; there is no fourth.
//!
//! (R5.5.T3 `ATD-Und` — undecidable for infinite substrates — and R5.5.T4 `ATD-NI` —
//! not internally expressible — are meta-level statements about the *limits* of this
//! decision procedure; they bound the finite engine rather than being realized in it.)

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::{is_convergent, is_persistent};

/// **R5.5.D1 (`ATD`)** — the aspect type of an instance. `==` compares the computed tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AspectType {
    /// **WF** — `∞_M = ∅`: every ρ_M-orbit reaches a fixpoint.
    WellFounded,
    /// **NWF** — `↓_M = ∅`: no ρ_M-orbit reaches a fixpoint (all persist).
    NonWellFounded,
    /// **Mixed** — both `↓_M ≠ ∅` and `∞_M ≠ ∅`.
    Mixed,
}

/// **R5.5.T2 (`ATD-Dec`)** — decide the aspect type of a (finite) instance by exhaustive
/// orbit exploration: WF iff `∞_M = ∅`, NWF iff `↓_M = ∅`, Mixed iff both non-empty.
///
/// Panics only on the empty universe (excluded: instances have non-empty `𝒰_M`).
pub fn aspect_type(op: &ProjectionOperator) -> AspectType {
    let mut has_convergent = false;
    let mut has_persistent = false;
    for x in op.substrate().elements() {
        // R5.5.T2: ↓_M-membership is decided by bounded orbit exploration (≤ |𝒰_M| steps).
        if op.canonical_fixpoint(x).is_some() {
            has_convergent = true;
        } else {
            has_persistent = true;
        }
    }
    match (has_convergent, has_persistent) {
        (true, false) => AspectType::WellFounded,
        (false, true) => AspectType::NonWellFounded,
        (true, true) => AspectType::Mixed,
        (false, false) => unreachable!("an instance has a non-empty universe (R5.5.T5)"),
    }
}

/// Witness **R5.5.T5 (`AspType-Tri`)** / **R1.9.T3 (`Part`)** — the element-level
/// dichotomy `↓_M ⊔ ∞_M = 𝒰_M`: every element is convergent *xor* persistent (so the
/// three instance-level aspect types are exhaustive). Returns the first element that is
/// neither or both, or `Ok`.
pub fn certify_aspect_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
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
    use crate::r1::substrate::Substrate;
    use crate::r1::reduction_strategy::Instance;

    fn aspect_of(edges: &[(u32, u32)], n: u32) -> AspectType {
        let m = Instance::from_functional_reduction(Substrate::new(n, edges, edges).unwrap()).unwrap();
        aspect_type(&m.operator())
    }

    #[test]
    fn well_founded_when_all_orbits_terminate() {
        // 0→1, 1 ∈ NF: ∞_M = ∅.
        assert_eq!(aspect_of(&[(0, 1)], 2), AspectType::WellFounded);
    }

    #[test]
    fn non_well_founded_when_no_orbit_terminates() {
        // 0⇄1: a pure cycle, no fixpoint, ↓_M = ∅.
        assert_eq!(aspect_of(&[(0, 1), (1, 0)], 2), AspectType::NonWellFounded);
    }

    #[test]
    fn mixed_when_both_aspects_present() {
        // 0⇄1 (∞_M) and 2→3, 3 ∈ NF (↓_M).
        let edges = [(0, 1), (1, 0), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &edges, &edges).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(aspect_type(&op), AspectType::Mixed);
        // the element-level partition is exhaustive and disjoint.
        assert!(matches!(certify_aspect_partition(&op), Ok(())));
    }
}
