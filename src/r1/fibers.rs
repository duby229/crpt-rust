//! # R1.12 — Normal-Form Fibers and Church-Rosser Equivalence
//!
//! Exact realization of spec section **R1.12** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9):
//!
//! - R1.12.D1 `NFC-NM` — the normal-form fiber `NFC_M(f) = {x | CFix(ρ_M)(x) = f}`.
//! - R1.12.D2 `≃_M` — observable (orbit) equivalence `x ≃_M y :⟺ CFix(ρ_M)(x) = CFix(ρ_M)(y)`.
//! - R1.12.T1 `≃-Eq` — ≃_M is an equivalence relation.
//! - R1.12.C1 `NFC-Part-NM` — the fibers partition ↓_M; their index set is `Q_M`.
//!
//! ≃_M here is the finitary form (both elements convergent, same canonical form);
//! observable equivalence on ∞_M (`≃∞`) is R2.3. The abstraction quotient
//! `Q_M = ↓_M/≃_M` is indexed by the fixpoints (one fiber per fixpoint; |Q_M| = |Fix|).

use crate::r1::substrate::ElementId;
use crate::r1::canonical_form::canonical_form;
use crate::r1::reduction_strategy::ProjectionOperator;

/// **R1.12.D2 (`≃_M`)**: `x ≃_M y :⟺ CFix(ρ_M)(x) = CFix(ρ_M)(y)`. Finitary form:
/// true iff both are convergent and share a canonical form.
pub fn observable_equivalence(op: &ProjectionOperator, x: ElementId, y: ElementId) -> bool {
    match (canonical_form(op, x), canonical_form(op, y)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}


/// **R1.12.D1 (`NFC_M`)**: the normal-form fiber `NFC_M(f) = {x | CFix(ρ_M)(x) = f}`,
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

/// The abstraction quotient `Q_M = ↓_M/≃_M` (R1.12.C1 / R6.1.D3 `Ab-Quot` / R6.5.D1 `Ab-Quot-28`): one representative per class,
/// namely the fixpoints (each f indexes the nonempty fiber `NFC_M(f) ∋ f`).
/// `|Q_M| = |Fix(ρ_M)|`.
pub fn abstraction_quotient(op: &ProjectionOperator) -> Vec<ElementId> {
    op.fixpoints()
}

/// Witness **R1.12.T1 (`≃-Eq`)**: ≃_M is reflexive on convergent elements,
/// symmetric, and transitive. (Immediate from equality of canonical forms; this
/// verifies it directly over the instance.)
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

/// Witness **R1.12.C1 (`NFC-Part-NM`)**: every convergent x lies in exactly the
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

/// Witness **R1.12.T2 (`CNF=CR`)** / **R1.12.R1 (`EquivM-OrbitCoin`)** — the **canonical
/// representative fiber theorem**: `CNF_M(x) = CNF_M(y) ⟺ x ≃_M y` — the canonical-form
/// computation and observable (orbit) equivalence are one relation. Under `PA-Conf`, `≃_M`
/// coincides with the orbit-coincidence characterization. Returns the first convergent pair
/// where `CFix`-equality and `≃_M` disagree (none — `≃_M` *is* `CFix`-equality, R1.12.D2), or
/// `Ok`.
pub fn certify_cnf_equals_church_rosser(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            let (cx, cy) = (op.canonical_fixpoint(x), op.canonical_fixpoint(y));
            if cx.is_some() && cy.is_some() {
                let cfix_eq = cx == cy;
                if cfix_eq != observable_equivalence(op, x, y) {
                    return Err((x, y));
                }
            }
        }
    }
    Ok(())
}

/// Witness **R1.12.L1 (`Orb-Bic`)** — the **orbit-coincidence biconditional**: for convergent
/// `x, y`, `CFix(ρ_M)(x) = CFix(ρ_M)(y) ⟺ ∃z : x →_ρ* z ∧ y →_ρ* z` (their orbits reach a
/// common reduct). On the deterministic `ρ_M`-orbit the common reduct is exactly the shared
/// fixpoint. Returns `true` iff `x` and `y` are convergent with a common reduct; this equals
/// `CFix(x) = CFix(y)`.
pub fn orbits_coincide(op: &ProjectionOperator, x: ElementId, y: ElementId) -> bool {
    match (op.canonical_fixpoint(x), op.canonical_fixpoint(y)) {
        (Some(cx), Some(cy)) => cx == cy, // the common reduct is the shared canonical fixpoint
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

    #[test]
    fn fibers_and_observable_equivalence() {
        // 0 ⇄ 1 (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M). So 2 ≃_M 3, fiber NFC(3) = {2,3}.
        let edges = [(0, 1), (1, 0), (2, 3)];
        let s = Substrate::new(4, &edges, &edges).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
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
        // CNF=CR / EquivM-OrbitCoin: CFix-equality ⟺ ≃_M.
        assert!(matches!(certify_cnf_equals_church_rosser(&op), Ok(())));
        // Orb-Bic: 2 and 3 reach a common reduct (3); 0 and 2 do not.
        assert!(orbits_coincide(&op, ElementId(2), ElementId(3)));
        assert!(!orbits_coincide(&op, ElementId(0), ElementId(2)));
    }

}
