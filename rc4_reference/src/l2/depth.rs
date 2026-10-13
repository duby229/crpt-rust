//! # L2.3 — Derivation Height d_M
//!
//! Exact realization of spec section **L2.3** (`CRPT_OMEGA_TOWER_L2.md`, rc3):
//!
//! - L2.3.D1 `≤_ρ` — the ρ_M-reachability preorder `x ≤_ρ y :⟺ ∃k : ρ_M^k(x) = y`.
//! - L2.3.D2 `d_M` — the derivation height `d_M(x) = min{n | ρ_M^n(x) ∈ Fix(ρ_M)}`,
//!   defined on ↓_M; undefined (Infinite) on ∞_M.
//! - L2.3.T2 `Depth-Dec` — `d_M(ρ_M(x)) = d_M(x) − 1` for x ∈ ↓_M \ Fix(ρ_M).
//! - L2.3.T3 `Fix-D0` — `d_M(f) = 0` for f ∈ Fix(ρ_M).

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;

/// The derivation height d_M(x) (L2.3.D2). `Infinite` exactly on ∞_M, where d_M is
/// undefined (the spec's `d_M = ∞ by convention`). `==` is mathematical identity of
/// the computed rank (a value on ℕ ∪ {∞}), not model structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivationHeight {
    /// d_M(x) = n ∈ ℕ; x ∈ ↓_M.
    Finite(u32),
    /// d_M(x) = ∞; x ∈ ∞_M (the ρ_M-orbit never reaches Fix(ρ_M)).
    Infinite,
}

/// **L2.3.D2 (`d_M`)**: `min{n | ρ_M^n(x) ∈ Fix(ρ_M)}`. Exact on finite 𝒰 — a
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

/// **L2.3.D1 (`≤_ρ`)**: `x ≤_ρ y :⟺ ∃k : ρ_M^k(x) = y` — y is on the ρ_M-orbit of x.
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

/// Witness **L2.3.T3 (`Fix-D0`)**: every fixpoint has derivation height 0.
pub fn certify_fixpoint_depth_zero(op: &ProjectionOperator) -> Result<(), ElementId> {
    for f in op.fixpoints() {
        if derivation_height(op, f) != DerivationHeight::Finite(0) {
            return Err(f);
        }
    }
    Ok(())
}

/// Witness **L2.3.T2 (`Depth-Dec`)**: for x ∈ ↓_M \ Fix(ρ_M),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l2::projection::Model;
    use crate::l1::substrate::Substrate;

    /// 0 ⇄ 1 cycle (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M).
    fn mixed() -> Substrate {
        let edges = [(0, 1), (1, 0), (2, 3)];
        Substrate::new(4, &edges, &edges).unwrap()
    }

    #[test]
    fn derivation_heights() {
        let s = mixed();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(derivation_height(&op, ElementId(3)), DerivationHeight::Finite(0)); // Fix
        assert_eq!(derivation_height(&op, ElementId(2)), DerivationHeight::Finite(1)); // 2→3
        assert_eq!(derivation_height(&op, ElementId(0)), DerivationHeight::Infinite); // ∞_M
        assert!(reaches_le(&op, ElementId(2), ElementId(3))); // 2 ≤_ρ 3
        assert!(!reaches_le(&op, ElementId(3), ElementId(2)));
        assert!(matches!(certify_fixpoint_depth_zero(&op), Ok(())));
        assert!(matches!(certify_depth_decrease(&op), Ok(())));
    }
}
