//! # L4.2 — Gateway and Regime Reachability
//!
//! Exact realization of spec section **L4.2** (`CRPT_OMEGA_TOWER_L4.md`, rc3):
//!
//! - L4.2.D1 `GW` — the gateway predicate: a convergent element with a →_σ-step to
//!   a persistent element. (Gateways are the →_σ passage points between ↓_M and ∞_M.)
//! - Gateway Reachability (GR) — the model-level →_σ property
//!   `∀x ∈ ↓_M \ Fix(ρ_M) : ∃y ∈ ∞_M : x →_σ* y`. GR is a property of →_σ, not a
//!   PA-* axiom; it is *checked*, not assumed. (Non-vacuous only when ∞_M ≠ ∅.)

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::{is_convergent, is_persistent};

/// **L4.2.D1 (`GW`)**: x is a gateway iff x ∈ ↓_M and there is a →_σ-step from x to
/// some persistent element (`∃y ∈ ∞_M : x →_σ y`).
pub fn is_gateway(op: &ProjectionOperator, x: ElementId) -> bool {
    is_convergent(op, x)
        && op
            .substrate()
            .structural_successors(x)
            .iter()
            .any(|&y| is_persistent(op, y))
}

/// The gateways of the model, ascending.
pub fn gateways(op: &ProjectionOperator) -> Vec<ElementId> {
    op.substrate().elements().filter(|&x| is_gateway(op, x)).collect()
}

/// Check **Gateway Reachability (GR)**: `∀x ∈ ↓_M \ Fix(ρ_M) : ∃y ∈ ∞_M : x →_σ* y`.
/// Returns the first non-fixpoint convergent element with no →_σ*-path to ∞_M, or
/// `Ok`. (GR is a model property, not always true; with ∞_M = ∅ it cannot hold for
/// any non-fixpoint convergent element.)
pub fn certify_gateway_reachability(op: &ProjectionOperator) -> Result<(), ElementId> {
    let substrate = op.substrate();
    for x in substrate.elements() {
        if is_convergent(op, x) && !op.is_fixpoint(x) {
            let reaches_persistent = substrate
                .elements()
                .any(|y| is_persistent(op, y) && substrate.structural_reachable(x, y));
            if !reaches_persistent {
                return Err(x);
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

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn gateway_to_persistent() {
        // ↓_M: 0→1, 1 ∈ NF.  ∞_M: 2 ⇄ 3.  Structural bridge 0 →_σ 2 (not a →_ρ edge).
        let reduction = [(0, 1), (2, 3), (3, 2)];
        let structural = [(0, 1), (2, 3), (3, 2), (0, 2)];
        let s = Substrate::new(4, &reduction, &structural).unwrap();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert!(is_gateway(&op, id(0))); // 0 ∈ ↓_M, 0 →_σ 2 ∈ ∞_M
        assert!(!is_gateway(&op, id(1))); // 1 is a fixpoint with no →_σ to ∞_M
        assert!(!is_gateway(&op, id(2))); // 2 ∈ ∞_M, not a gateway (must be convergent)
        assert_eq!(gateways(&op), vec![id(0)]);
        // GR holds: the only non-fixpoint convergent element, 0, →_σ*-reaches ∞_M.
        assert!(matches!(certify_gateway_reachability(&op), Ok(())));
    }
}
