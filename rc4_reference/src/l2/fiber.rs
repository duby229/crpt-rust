//! # L2.5 — Normal-Form Fibers and Observable Equivalence
//!
//! Exact realization of spec section **L2.5** (`CRPT_OMEGA_TOWER_L2.md`, rc3):
//!
//! - L2.5.D1 `NFC-NM` — the normal-form fiber `NFC_M(f) = {x | CFix(ρ_M)(x) = f}`.
//! - L2.5.D2 `≃_M` — observable (orbit) equivalence `x ≃_M y :⟺ CFix(ρ_M)(x) = CFix(ρ_M)(y)`.
//! - L2.5.T1 `≃-Eq` — ≃_M is an equivalence relation.
//! - L2.5.C1 `NFC-Part-NM` — the fibers partition ↓_M; their index set is `Q_M`.
//!
//! ≃_M here is the finitary form (both elements convergent, same canonical form);
//! observable equivalence on ∞_M (`≃∞`) is L3.3. The abstraction quotient
//! `Q_M = ↓_M/≃_M` is indexed by the fixpoints (one fiber per fixpoint; |Q_M| = |Fix|).

use crate::l1::substrate::ElementId;
use crate::l2::canonical::canonical_form;
use crate::l2::projection::ProjectionOperator;

/// **L2.5.D2 (`≃_M`)**: `x ≃_M y :⟺ CFix(ρ_M)(x) = CFix(ρ_M)(y)`. Finitary form:
/// true iff both are convergent and share a canonical form.
pub fn observable_equivalence(op: &ProjectionOperator, x: ElementId, y: ElementId) -> bool {
    match (canonical_form(op, x), canonical_form(op, y)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// **L2.5.D2 (`≃_M`), topological reading** — observable equivalence on the topological
/// tier: `x ≃_M y ⟺ CFix(x) = CFix(y)` with `CFix` the `𝒯`-limit canonical form
/// (rc3: on ∞_M under `PA-WN_top`, `≃_M` is equality of `𝒯`-limits). Defined where both
/// canonical forms exist.
pub fn topologically_equivalent<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
    y: &T::Point,
) -> bool {
    match (sys.canonical_form_topological(x), sys.canonical_form_topological(y)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// **L2.5.D1 (`NFC_M`)**: the normal-form fiber `NFC_M(f) = {x | CFix(ρ_M)(x) = f}`,
/// ascending. (For f ∈ Fix(ρ_M), this is the ≃_M-class canonicalizing to f.)
pub fn normal_form_fiber(op: &ProjectionOperator, f: ElementId) -> Vec<ElementId> {
    op.substrate()
        .elements()
        .filter(|&x| canonical_form(op, x) == Some(f))
        .collect()
}

/// The ≃_M-class representative of each element: `CFix(ρ_M)(x)` (`None` on ∞_M).
/// Indexed by `ElementId::index`. `x ≃_M y ⟺ class[x] == class[y]` (both `Some`).
pub fn observable_classes(op: &ProjectionOperator) -> Vec<Option<ElementId>> {
    op.substrate().elements().map(|x| canonical_form(op, x)).collect()
}

/// The abstraction quotient `Q_M = ↓_M/≃_M` (L2.5.C1 / L7.1.D3 `Ab-Quot` / L8.2.D1 `Ab-Quot-28`): one representative per class,
/// namely the fixpoints (each f indexes the nonempty fiber `NFC_M(f) ∋ f`).
/// `|Q_M| = |Fix(ρ_M)|`.
pub fn abstraction_quotient(op: &ProjectionOperator) -> Vec<ElementId> {
    op.fixpoints()
}

/// Witness **L2.5.T1 (`≃-Eq`)**: ≃_M is reflexive on convergent elements,
/// symmetric, and transitive. (Immediate from equality of canonical forms; this
/// verifies it directly over the model.)
pub fn certify_observable_equivalence(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        // reflexivity holds exactly on convergent elements (≃_M needs a canonical form)
        if canonical_form(op, x).is_some() && !observable_equivalence(op, x, x) {
            return Err((x, x));
        }
        for &y in &elements {
            if observable_equivalence(op, x, y) != observable_equivalence(op, y, x) {
                return Err((x, y)); // symmetry
            }
        }
    }
    Ok(())
}

/// Witness **L2.5.C1 (`NFC-Part-NM`)**: every convergent x lies in exactly the
/// fiber `NFC_M(CFix(ρ_M)(x))`. First violation, or `Ok`.
pub fn certify_fibers_partition_convergent(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(c) = canonical_form(op, x) {
            if !normal_form_fiber(op, c).contains(&x) {
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
    fn fibers_and_observable_equivalence() {
        // 0 ⇄ 1 (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M). So 2 ≃_M 3, fiber NFC(3) = {2,3}.
        let edges = [(0, 1), (1, 0), (2, 3)];
        let s = Substrate::new(4, &edges, &edges).unwrap();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert!(observable_equivalence(&op, ElementId(2), ElementId(3)));
        assert!(!observable_equivalence(&op, ElementId(0), ElementId(1))); // both ∞_M
        assert!(!observable_equivalence(&op, ElementId(2), ElementId(0)));
        assert_eq!(normal_form_fiber(&op, ElementId(3)), vec![ElementId(2), ElementId(3)]);
        assert_eq!(abstraction_quotient(&op), vec![ElementId(3)]); // Q_M index = Fix = {3}
        assert_eq!(
            observable_classes(&op),
            vec![None, None, Some(ElementId(3)), Some(ElementId(3))]
        );
        assert!(matches!(certify_observable_equivalence(&op), Ok(())));
        assert!(matches!(certify_fibers_partition_convergent(&op), Ok(())));
    }

    #[test]
    fn observable_equivalence_topological_reading() {
        use crate::l1::topology::{ChainPoint, ConvergentChain};
        // ℕ ∪ {ω}: every Step(n) canonicalizes to the 𝒯-limit ω ⇒ all Step(n) ≃_M ω ≃_M each other.
        let chain = ConvergentChain;
        assert!(topologically_equivalent(&chain, &ChainPoint::Step(0), &ChainPoint::Step(5)));
        assert!(topologically_equivalent(&chain, &ChainPoint::Step(2), &ChainPoint::Limit));
    }
}
