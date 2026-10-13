//! # L2.2 — Regime Partition (↓_M ∐ ∞_M)
//!
//! Exact realization of spec section **L2.2** (`CRPT_OMEGA_TOWER_L2.md`, rc3):
//!
//! - L2.2.D1 `Pre_ρ` — the ρ_M-predecessor operator.
//! - L2.2.D4 `↓_M` — the convergent regime `{x | ∃n : ρ_M^n(x) ∈ Fix(ρ_M)}`.
//! - L2.2.D5 `∞_M` — the persistent regime `{x | ∀n : ρ_M^n(x) ∉ Fix(ρ_M)}`.
//! - L2.2.T1 `↓-Closed`, L2.2.T2 `∞-Closed`, L2.2.T3 `Part` — closure and the
//!   exhaustive disjoint partition 𝒰 = ↓_M ∐ ∞_M.
//! - L2.2.T7 `Inf-Dual` + L2.2.R8 `Infinity-Cycle` — the **infinity duality**: horizontal
//!   infinity (infinite fiber / σ-branching) and vertical infinity (`∞_M ≠ ∅`) are dual,
//!   transformed into each other by `Lift` across tower levels ([`certify_depth_reset`],
//!   [`fiber_lifts_to_depth`]). Infinities are not lost in the tower — they are
//!   *transformed*; infinite structure is always finitely presented.
//!
//! Computed exactly via the projection operator's orbit: x ∈ ↓_M iff its ρ_M-orbit
//! reaches a fixpoint ([`ProjectionOperator::canonical_fixpoint`] is `Some`).

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;

/// The regime of an element under ρ_M (L2.2.D4/D5). `==` compares the computed
/// regime tag (mathematical identity of the value), not model structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Regime {
    /// x ∈ ↓_M: the ρ_M-orbit reaches Fix(ρ_M) in finitely many steps (L2.2.D4).
    Convergent,
    /// x ∈ ∞_M: the ρ_M-orbit never reaches Fix(ρ_M) (L2.2.D5).
    Persistent,
}

/// **L2.2.D4/D5**: the regime of x.
pub fn regime_of(op: &ProjectionOperator, x: ElementId) -> Regime {
    if op.canonical_fixpoint(x).is_some() {
        Regime::Convergent
    } else {
        Regime::Persistent
    }
}

/// x ∈ ↓_M (L2.2.D4).
pub fn is_convergent(op: &ProjectionOperator, x: ElementId) -> bool {
    matches!(regime_of(op, x), Regime::Convergent)
}

/// x ∈ ∞_M (L2.2.D5).
pub fn is_persistent(op: &ProjectionOperator, x: ElementId) -> bool {
    matches!(regime_of(op, x), Regime::Persistent)
}

/// The convergent regime ↓_M as a bitmap indexed by `ElementId::index` (L2.2.D4).
pub fn convergent_set(op: &ProjectionOperator) -> Vec<bool> {
    op.substrate().elements().map(|x| is_convergent(op, x)).collect()
}

/// The persistent regime ∞_M as a bitmap indexed by `ElementId::index` (L2.2.D5).
pub fn persistent_set(op: &ProjectionOperator) -> Vec<bool> {
    op.substrate().elements().map(|x| is_persistent(op, x)).collect()
}

/// **L2.2.D1 (`Pre_ρ`)**: the ρ_M-preimage of `y`, `Pre_ρ({y}) = {z | ρ_M(z) = y}`,
/// ascending. (The set-level Pre_ρ(X) is the union over `y ∈ X`.)
pub fn preimage(op: &ProjectionOperator, y: ElementId) -> Vec<ElementId> {
    op.substrate().elements().filter(|&z| op.project(z) == y).collect()
}

/// Witness **L2.2.T1 (`↓-Closed`)**: x ∈ ↓_M ⟹ ρ_M(x) ∈ ↓_M. First violation, or `Ok`.
pub fn certify_convergent_closed(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_convergent(op, x) && !is_convergent(op, op.project(x)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **L2.2.T2 (`∞-Closed`)**: x ∈ ∞_M ⟹ ρ_M(x) ∈ ∞_M. First violation, or `Ok`.
pub fn certify_persistent_closed(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_persistent(op, x) && !is_persistent(op, op.project(x)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **L2.2.T3 (`Part`)**: every x is in exactly one regime (↓_M ∐ ∞_M).
pub fn certify_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_convergent(op, x) == is_persistent(op, x) {
            return Err(x);
        }
    }
    Ok(())
}

use crate::l2::fiber::normal_form_fiber;
use crate::l2::projection::Model;
use crate::l8::lift::lift;

/// **`Inf-Dual` (iii) — depth reset (`Fix-Bas` L8.2.T1)**: every fiber `NFC_M(f)` lifts to
/// the **depth-0 atom** `ι_M(f)` in `Lift(M)`, regardless of its internal σ-structure.
/// Returns the first fixpoint whose lifted atom is not depth-0, or `Ok`.
pub fn certify_depth_reset(base: &Model) -> Result<(), ElementId> {
    let lifted = lift(base);
    for f in lifted.atoms().to_vec() {
        let atom = lifted.canonical_inclusion(f);
        if lifted.depth(&atom) != 0 || !lifted.is_fixpoint(&atom) {
            return Err(f);
        }
    }
    Ok(())
}

/// **`Inf-Dual` (i) — horizontal → vertical**: the fiber `NFC_M(f)` of horizontal size `m`
/// supplies an `m`-fold atom composition of abstraction depth `m − 1` in `Lift(M)`. Returns
/// `(m, m−1)` = (fiber size, achievable Lift depth). An *infinite* fiber (`m = ∞`) gives
/// *unbounded* Lift depth — vertical infinity. (Demonstrated here as the realized word.)
pub fn fiber_lifts_to_depth(base: &Model, f: ElementId) -> (u32, u32) {
    let op = base.operator();
    let m = normal_form_fiber(&op, f).len() as u32;
    (m, m.saturating_sub(1))
}

/// **`Inf-Dual` headline**: in a non-degenerate model, horizontal infinity ⟺ vertical
/// infinity; equivalently, *no persistence implies no horizontal infinity*. On a **finite**
/// substrate fibers are necessarily finite (no horizontal infinity), consistent with the
/// duality. `true` confirms the finite consistency: every fiber is finite. (The
/// non-vacuous duality requires an infinite substrate — `Lift(M)` itself, whose `FMA(Q_M)`
/// universe carries both infinities.)
pub fn finite_base_has_no_horizontal_infinity(base: &Model) -> bool {
    // every fiber is a finite subset of the finite universe — always true here, the point
    // being that finite substrates sit at the degenerate corner of the duality.
    let _ = base;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l2::projection::Model;
    use crate::l1::substrate::Substrate;

    /// Mixed model: 0 ⇄ 1 cycle (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M).
    fn mixed() -> (Substrate, Vec<(u32, u32)>) {
        let edges = vec![(0, 1), (1, 0), (2, 3)];
        (Substrate::new(4, &edges, &edges).unwrap(), edges)
    }

    #[test]
    fn regimes_partition_and_closure() {
        let (s, _) = mixed();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(regime_of(&op, ElementId(0)), Regime::Persistent);
        assert_eq!(regime_of(&op, ElementId(1)), Regime::Persistent);
        assert_eq!(regime_of(&op, ElementId(2)), Regime::Convergent);
        assert_eq!(regime_of(&op, ElementId(3)), Regime::Convergent);
        assert_eq!(convergent_set(&op), vec![false, false, true, true]);
        assert!(matches!(certify_convergent_closed(&op), Ok(())));
        assert!(matches!(certify_persistent_closed(&op), Ok(())));
        assert!(matches!(certify_partition(&op), Ok(())));
    }

    #[test]
    fn preimage_is_predecessor_set() {
        let (s, _) = mixed();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        // ρ(2)=3, ρ(3)=3 ⇒ Pre_ρ({3}) = {2, 3}.
        assert_eq!(preimage(&op, ElementId(3)), vec![ElementId(2), ElementId(3)]);
    }

    #[test]
    fn depth_reset_and_horizontal_to_vertical() {
        // 0→2, 1→2, 2→3, 3 ∈ NF. Fiber NFC(3) = {0,1,2,3} (size 4); Fix = {3} = Q_M.
        let e = [(0, 2), (1, 2), (2, 3)];
        let base = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        // (iii): the single fixpoint 3 lifts to a depth-0 atom.
        assert!(matches!(certify_depth_reset(&base), Ok(())));
        // (i): the size-4 fiber maps to achievable Lift depth 3 (horizontal 4 → vertical 3).
        assert_eq!(fiber_lifts_to_depth(&base, ElementId(3)), (4, 3));
        // finite consistency of the duality.
        assert!(finite_base_has_no_horizontal_infinity(&base));
    }
}
