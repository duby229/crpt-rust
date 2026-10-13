//! # L2.4 — Canonical Normal Form Map CNF_M
//!
//! Realizes L2.4 incl. L2.4.D2 `Abs-L0` (the abstraction is the L0 fiber map, l0::projection_system). Exact realization of spec section **L2.4** (`CRPT_OMEGA_TOWER_L2.md`, rc3):
//!
//! - L2.4.D1 `CFix-NM` — the canonical form map `CNF_M(x) = CFix(ρ_M)(x)`, which on
//!   ↓_M is `ρ_M^{d_M(x)}(x)` (the fixpoint the orbit reaches). The same object as
//!   the recursive projection L2.1.D4; this is the "map" view.
//! - L2.4.T1 `CNF-Ex` — `CNF_M(x) ∈ Fix(ρ_M)` for x ∈ ↓_M.
//! - L2.4.T3 `CNF-Stab` — `CNF_M(CNF_M(x)) = CNF_M(x)` (idempotence).
//!
//! On ∞_M the canonical form is the topological limit (L2.4.D1, second branch),
//! which requires the topology / PA-WN_top; in the finite WF core ∞_M elements
//! have no finitary canonical form, returned as `None`. (Their asymptotic
//! canonical invariant is L3.3.)

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;

/// **L2.4.D1 (`CNF_M` = `CFix(ρ_M)`)**: the canonical form of x — the fixpoint its
/// ρ_M-orbit reaches. `Some(f)` on ↓_M (unique by `UF` L2.1.L2); `None` on ∞_M.
pub fn canonical_form(op: &ProjectionOperator, x: ElementId) -> Option<ElementId> {
    op.canonical_fixpoint(x)
}

/// Witness **L2.4.T1 (`CNF-Ex`)**: for x ∈ ↓_M, `CNF_M(x) ∈ Fix(ρ_M)`. First
/// convergent element whose canonical form is not a fixpoint, or `Ok`.
pub fn certify_cnf_is_fixpoint(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(c) = canonical_form(op, x) {
            if !op.is_fixpoint(c) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **L2.4.T3 (`CNF-Stab`)**: `CNF_M(CNF_M(x)) = CNF_M(x)`. First violation, or `Ok`.
pub fn certify_cnf_stable(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(c) = canonical_form(op, x) {
            if canonical_form(op, c) != Some(c) {
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

    #[test]
    fn canonical_form_and_witnesses() {
        // 0 ⇄ 1 (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M).
        let edges = [(0, 1), (1, 0), (2, 3)];
        let s = Substrate::new(4, &edges, &edges).unwrap();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(canonical_form(&op, ElementId(2)), Some(ElementId(3)));
        assert_eq!(canonical_form(&op, ElementId(3)), Some(ElementId(3)));
        assert_eq!(canonical_form(&op, ElementId(0)), None); // ∞_M: no finitary CNF
        assert!(matches!(certify_cnf_is_fixpoint(&op), Ok(())));
        assert!(matches!(certify_cnf_stable(&op), Ok(())));
    }
}
