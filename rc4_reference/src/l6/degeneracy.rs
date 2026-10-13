//! # L6.6 — Model Classification and Degeneracy
//!
//! Exact realization of spec section **L6.6** (`CRPT_OMEGA_TOWER_L6.md`, v1.0.0-rc4):
//!
//! - L6.6.D1 `Dege-Inv` — the degeneracy invariant. A model is **degenerate** when its
//!   six-class partition has fewer than five non-empty classes (the generic case occupies
//!   all of A–E; F is always empty). Degeneracy arises when structural constraints force a
//!   horizon predicate constant across 𝒰_M. The definition also names per-invariant
//!   degeneracies: `≈` degenerate (≈ = identity), the NFC partition degenerate
//!   (`|NF| = 1`), `PA-Conf` degenerate (ρ_M total/functional ⇒ trivially confluent).
//!
//! Each is a finite, decidable structural property; [`degeneracy`] reports them and
//! [`is_degenerate`] gives the headline six-class verdict.

use crate::l2::projection::Model;
use crate::l3::classification::classify;

/// **L6.6.D1 (`Dege-Inv`)** — the degeneracy report of a model: the headline six-class
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

/// **L6.6.D1 (`Dege-Inv`)** — compute the degeneracy report of `M`.
pub fn degeneracy(m: &Model) -> DegeneracyReport {
    let op = m.operator();
    // active six-classes: distinct labels classify assigns on ↓_M.
    let mut classes: Vec<crate::l3::classification::HorizonClass> = op
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

/// **L6.6.D1 (`Dege-Inv`)** — the headline verdict: `M` is degenerate iff its six-class
/// partition has fewer than five non-empty classes.
pub fn is_degenerate(m: &Model) -> bool {
    degeneracy(m).six_class_degenerate
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;

    #[test]
    fn injective_projection_is_degenerate() {
        // A simple chain 0→1, 1 ∈ NF: ρ injective, H_S = ⊥ everywhere ⇒ few classes,
        // single normal form ⇒ degenerate on several invariants.
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let report = degeneracy(&m);
        assert!(report.six_class_degenerate); // < 5 active classes
        assert!(report.normal_form_degenerate); // |NF| = 1
        assert!(report.bisimulation_degenerate); // 0,1 distinguishable ⇒ ≈ = identity
    }
}
