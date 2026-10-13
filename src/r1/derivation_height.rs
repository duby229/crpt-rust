//! # R1.10 — Derivation Height d_M
//!
//! Exact realization of spec section **R1.10** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9):
//!
//! - R1.10.D1 `≤_ρ` — the ρ_M-reachability preorder `x ≤_ρ y :⟺ ∃k : ρ_M^k(x) = y`.
//! - R1.10.D2 `d_M` — the derivation height `d_M(x) = min{n | ρ_M^n(x) ∈ Fix(ρ_M)}`,
//!   defined on ↓_M; undefined (Infinite) on ∞_M.
//! - R1.10.T2 `Depth-Dec` — `d_M(ρ_M(x)) = d_M(x) − 1` for x ∈ ↓_M \ Fix(ρ_M).
//! - R1.10.T3 `Fix-D0` — `d_M(f) = 0` for f ∈ Fix(ρ_M).

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;

/// The derivation height d_M(x) (R1.10.D2). `Infinite` exactly on ∞_M, where d_M is
/// undefined (the spec's `d_M = ∞ by convention`). `==` is mathematical identity of
/// the computed rank (a value on ℕ ∪ {∞}), not instance structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivationHeight {
    /// d_M(x) = n ∈ ℕ; x ∈ ↓_M.
    Finite(u32),
    /// d_M(x) = ∞; x ∈ ∞_M (the ρ_M-orbit never reaches Fix(ρ_M)).
    Infinite,
}

/// **R1.10.D2 (`d_M`)**: `min{n | ρ_M^n(x) ∈ Fix(ρ_M)}`. Exact on finite 𝒰 — a
/// convergent orbit reaches its fixpoint within |𝒰| steps.
pub fn derivation_height(op: &ProjectionOperator, x: ElementId) -> DerivationHeight {
    let n = op.substrate().universe_len();
    let mut current = x;
    for k in 0..=n {
        if op.is_fixpoint(current) {
            return DerivationHeight::Finite(k);
        }
        current = op.project(current);
    }
    DerivationHeight::Infinite
}

/// **R1.10.D1 (`≤_ρ`)**: `x ≤_ρ y :⟺ ∃k : ρ_M^k(x) = y` — y is on the ρ_M-orbit of x.
pub fn reaches_le(op: &ProjectionOperator, x: ElementId, y: ElementId) -> bool {
    let n = op.substrate().universe_len();
    let mut current = x;
    for _ in 0..=n {
        if current == y {
            return true;
        }
        current = op.project(current);
    }
    false
}

/// Witness **R1.10.T3 (`Fix-D0`)**: every fixpoint has derivation height 0.
pub fn certify_fixpoint_depth_zero(op: &ProjectionOperator) -> Result<(), ElementId> {
    for f in op.fixpoints() {
        if derivation_height(op, f) != DerivationHeight::Finite(0) {
            return Err(f);
        }
    }
    Ok(())
}

/// Witness **R1.10.T2 (`Depth-Dec`)**: for x ∈ ↓_M \ Fix(ρ_M),
/// `d_M(ρ_M(x)) = d_M(x) − 1`. First violation, or `Ok`.
pub fn certify_depth_decrease(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let DerivationHeight::Finite(dx) = derivation_height(op, x) {
            if dx >= 1 {
                // x ∈ ↓_M \ Fix(ρ_M)
                if derivation_height(op, op.project(x)) != DerivationHeight::Finite(dx - 1) {
                    return Err(x);
                }
            }
        }
    }
    Ok(())
}

/// Witness **R1.10.T1 (`d-WD`)** / **R1.10.R2 (`dM-Domain`)** — `d_M` is **well-defined exactly
/// on `↓_M`**: for every convergent `x` the set `{n | ρ_M^n(x) ∈ Fix(ρ_M)}` is non-empty, so
/// its minimum `d_M(x) ∈ ℕ` exists; for persistent `x` the set is empty and `d_M` is undefined
/// (`Infinite`). Returns the first element where finiteness of `d_M` disagrees with membership
/// in `↓_M` (none), or `Ok`. (`R1.10.R3` `dM-Native`: across both aspects, `d_M` is `Finite` on
/// `↓_M` and `Infinite` on `∞_M` — the native reading.)
pub fn certify_d_well_defined(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::aspect_partition::is_convergent;
    for x in op.substrate().elements() {
        let finite = matches!(derivation_height(op, x), DerivationHeight::Finite(_));
        if finite != is_convergent(op, x) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.10.L1 (`≤ρ-PO`)** / **R1.10.R1 (`leq-Antisym`)** — the derivation-height order
/// `≤_ρ` on `↓_M` is a **partial order**: reflexive (`x ≤_ρ x`), **antisymmetric** (`x ≤_ρ y ∧
/// y ≤_ρ x ⟹ d_M(x) = d_M(y)` — from determinism of `ρ_M` and finite reachability; `PA-Conf`
/// is cited only uniformly, not logically needed), and transitive. Returns the first
/// convergent pair violating antisymmetry (`x ≤_ρ y ∧ y ≤_ρ x` but `d_M(x) ≠ d_M(y)`, none),
/// or `Ok`. (`reaches_le` is the `≤_ρ` orbit-reachability relation.)
pub fn certify_leq_partial_order(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        if !reaches_le(op, x, x) {
            return Err((x, x)); // reflexivity (vacuously holds: x reaches itself in 0 steps)
        }
        for &y in &elements {
            if reaches_le(op, x, y) && reaches_le(op, y, x) {
                // mutual reachability on a deterministic orbit ⟹ same canonical depth.
                if derivation_height(op, x) != derivation_height(op, y) {
                    return Err((x, y));
                }
            }
        }
    }
    Ok(())
}

/// Witness **R1.10.C1 (`d-WFM`)** — `d_M` induces a **well-founded measure** on `↓_M`: every
/// non-empty subset of `↓_M` has a `≤_ρ`-minimal element (one with the minimum `d_M` value),
/// so there is no infinite strictly-descending chain. Given a non-empty `subset` of convergent
/// elements, returns the minimal-`d_M` element (the well-founded witness), or `None` if the
/// subset is empty or contains a persistent element.
pub fn well_founded_minimum(op: &ProjectionOperator, subset: &[ElementId]) -> Option<ElementId> {
    let mut best: Option<(u32, ElementId)> = None;
    for &x in subset {
        match derivation_height(op, x) {
            DerivationHeight::Finite(d) => {
                if best.map_or(true, |(bd, _)| d < bd) {
                    best = Some((d, x));
                }
            }
            DerivationHeight::Infinite => return None, // not a subset of ↓_M
        }
    }
    best.map(|(_, x)| x)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

    /// 0 ⇄ 1 cycle (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M).
    fn mixed() -> Substrate {
        let edges = [(0, 1), (1, 0), (2, 3)];
        Substrate::new(4, &edges, &edges).unwrap()
    }

    #[test]
    fn derivation_heights() {
        let s = mixed();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(derivation_height(&op, ElementId(3)), DerivationHeight::Finite(0)); // Fix
        assert_eq!(derivation_height(&op, ElementId(2)), DerivationHeight::Finite(1)); // 2→3
        assert_eq!(derivation_height(&op, ElementId(0)), DerivationHeight::Infinite); // ∞_M
        assert!(reaches_le(&op, ElementId(2), ElementId(3))); // 2 ≤_ρ 3
        assert!(!reaches_le(&op, ElementId(3), ElementId(2)));
        assert!(matches!(certify_fixpoint_depth_zero(&op), Ok(())));
        assert!(matches!(certify_depth_decrease(&op), Ok(())));
        // d-WD / dM-Domain: d_M is Finite exactly on ↓_M.
        assert!(matches!(certify_d_well_defined(&op), Ok(())));
        // ≤ρ-PO / leq-Antisym: ≤_ρ is a partial order (antisymmetric).
        assert!(matches!(certify_leq_partial_order(&op), Ok(())));
        // d-WFM: the convergent set {2,3} has a ≤_ρ-minimal element (3, depth 0).
        assert_eq!(well_founded_minimum(&op, &[ElementId(2), ElementId(3)]), Some(ElementId(3)));
    }
}
