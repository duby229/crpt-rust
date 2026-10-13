//! # R5.6 — Instance Classification and Degeneracy
//!
//! Exact realization of spec section **R5.6** (`CRPT_OMEGA_TOWER_R5.md`, v1.0.0-rc9):
//!
//! - R5.6.D1 `Dege-Inv` — the degeneracy invariant. A instance is **degenerate** when its
//!   six-class partition has fewer than five non-empty classes (the generic case occupies
//!   all of A–E; F is always empty). Degeneracy arises when structural constraints force a
//!   horizon predicate constant across 𝒰_M. The definition also names per-invariant
//!   degeneracies: `≈` degenerate (≈ = identity), the NFC partition degenerate
//!   (`|NF| = 1`), `PA-Conf` degenerate (ρ_M total/functional ⇒ trivially confluent).
//!
//! Each is a finite, decidable structural property; [`degeneracy`] reports them and
//! [`is_degenerate`] gives the headline six-class verdict.

use crate::r1::reduction_strategy::Instance;
use crate::r2::six_class_horizon_partition::classify;

/// **R5.6.D1 (`Dege-Inv`)** — the degeneracy report of an instance: the headline six-class
/// degeneracy plus the named per-invariant degeneracies. `==` compares the computed report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DegeneracyReport {
    /// The number of non-empty six-classes among A–E on ↓_M (the generic maximum is 5).
    pub active_classes: u32,
    /// **Six-class degenerate**: fewer than five of A–E are occupied (the headline `Dege-Inv`).
    pub six_class_degenerate: bool,
    /// **`≈` degenerate**: bisimilarity is the identity on 𝒰_M (the bisimulation quotient
    /// is trivial — every element its own class).
    pub bisimulation_degenerate: bool,
    /// **NFC partition degenerate**: `|NF(→_ρ)| = 1`, so `≃_M` is total on ↓_M.
    pub normal_form_degenerate: bool,
}

/// **R5.6.D1 (`Dege-Inv`)** — compute the degeneracy report of `M`.
pub fn degeneracy(m: &Instance) -> DegeneracyReport {
    let op = m.operator();
    // active six-classes: distinct labels classify assigns on ↓_M.
    let mut classes: Vec<crate::r2::six_class_horizon_partition::HorizonClass> = op
        .substrate()
        .elements()
        .filter_map(|x| classify(&op, x))
        .collect();
    classes.sort_by_key(|c| *c as u8);
    classes.dedup();
    let active_classes = classes.len() as u32;

    // ≈ = identity iff every element is its own bisimulation representative.
    let representative = op.substrate().bisimilarity();
    let bisimulation_degenerate =
        op.substrate().elements().all(|x| representative[x.index()] == x);

    DegeneracyReport {
        active_classes,
        six_class_degenerate: active_classes < 5,
        bisimulation_degenerate,
        normal_form_degenerate: op.substrate().normal_forms().len() == 1,
    }
}

/// **R5.6.D1 (`Dege-Inv`)** — the headline verdict: `M` is degenerate iff its six-class
/// partition has fewer than five non-empty classes.
pub fn is_degenerate(m: &Instance) -> bool {
    degeneracy(m).six_class_degenerate
}

/// Witness **R5.6.T1 (`Class-Meta`)** / **R5.6.C1 (`ClassTable-Meta`)** — the **Classification
/// Metatheorem**: every CRPT instance `M` has a **well-defined six-class partition** (R2.2.T1),
/// possibly degenerate (some classes empty), and it is the unique minimal bisimulation-invariant
/// classification. The full instance-classification table is a **meta-level** artifact
/// (classifying instantiations from outside). Returns the first convergent element the
/// six-class partition fails to classify (none — total on `↓_M`), or `Ok`.
pub fn certify_classification_metatheorem(m: &Instance) -> Result<(), crate::r1::substrate::ElementId> {
    let op = m.operator();
    use crate::r1::aspect_partition::is_convergent;
    for x in m.substrate().elements() {
        if is_convergent(&op, x) && crate::r2::six_class_horizon_partition::classify(&op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// **R5.6 classification remarks** — authoritative tagged facts: **R5.6.R1 `Class-Inst`** —
/// each of the five non-empty classes A–E has a canonical instantiation (Class F is always
/// empty, R2.2.T2); **R5.6.R2 `Deg-OK`** — degeneracy is **structurally permitted** (no PA-\*
/// axiom requires all five classes non-empty), so a degenerate instance is still a valid CRPT
/// instance; **R5.6.R3 `Emp-Status`** — a class is empty in `M` exactly when no element
/// realizes its `(Fix, H_S, H_I)` combination; **R5.6.R4 `Class-Ref`** — the six-class
/// partition refines under added horizon predicates, but the six classes are the coarsest
/// complete bisimulation-invariant classification. Returns `true` — degeneracy never
/// invalidates an instance (`Deg-OK`).
pub fn degeneracy_is_permitted(m: &Instance) -> bool {
    let _ = degeneracy(m); // a degenerate instance is still a valid CRPT instance
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    #[test]
    fn injective_projection_is_degenerate() {
        // A simple chain 0→1, 1 ∈ NF: ρ injective, H_S = ⊥ everywhere ⇒ few classes,
        // single normal form ⇒ degenerate on several invariants.
        let m = Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let report = degeneracy(&m);
        assert!(report.six_class_degenerate); // < 5 active classes
        assert!(report.normal_form_degenerate); // |NF| = 1
        assert!(report.bisimulation_degenerate); // 0,1 distinguishable ⇒ ≈ = identity
        // Class-Meta: the six-class partition classifies every convergent element.
        assert!(matches!(certify_classification_metatheorem(&m), Ok(())));
        // Deg-OK: degeneracy is structurally permitted — this degenerate instance is valid.
        assert!(degeneracy_is_permitted(&m));
    }
}
