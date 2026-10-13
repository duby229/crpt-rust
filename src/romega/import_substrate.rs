//! # Rω.9 — Internalizing the Imports
//!
//! Exact realization of spec section **Rω.9** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9) —
//! resolving the off-document support of `Spec-Sub`'s primitives by adjoining the external
//! axiomatic sources as explicit substrate primitives:
//!
//! - Rω.9.D1 `Imp-Sub` — the import substrate `𝒰_spec⁺ = 𝒰_spec ⊔ 𝒜_ext` with an extended
//!   anchor `ρ_spec⁺` that **fixes** each external source (`𝒜_ext ⊆ Fix(ρ_spec⁺)`) and sends
//!   each Imported construct to the axiom it transports. The off-document roots acquire
//!   explicit anchors one rank below the document.
//! - Rω.9.D2 `Ax-Map` — `χ_imp : Imp → 𝒜_ext`, each Imported construct to its external axiom;
//!   **many-to-one**, with fiber `χ_imp⁻¹(a)` the **footprint** of axiom `a`. A construct
//!   inherits `a` iff its `ρ_spec⁺`-orbit terminates at `a`: `CNF_{spec⁺}(c) = a`.
//! - Rω.9.T1 `Imp-Track` — the footprints **partition** the Imported constructs and are
//!   computable from the Source lines (the import payload is measured, not assumed).
//! - Rω.9.T2 `Imp-Reify` — Reification carries the import structure **naturally** (up to the
//!   canonical inclusion `ι`, not invariantly): since `𝒜_ext ⊆ Fix(ρ_spec⁺)`, by `Fix-Bas`
//!   (R6.5.T1) every external axiom reifies to a **one-atom word** — the imported invariants
//!   become the atoms of the reified tower.
//!
//! Realized as a concrete pure-WF [`Instance`]: the external axioms are the fixpoints, the
//! Imported constructs reduce to them, and the existing R6 [`reify`] is applied directly.

use crate::r1::reduction_strategy::Instance;
use crate::r1::substrate::{ElementId, Substrate};
use crate::r6::reification_operator::reify;

/// **Rω.9.D1 (`Imp-Sub`)** — the import-extended substrate `𝒰_spec⁺`. Modelled with two
/// external axioms `a₁ = 0`, `a₂ = 1` (the adjoined primitives, `𝒜_ext ⊆ Fix(ρ_spec⁺)`) and
/// three Imported constructs `c₁ = 2 → a₁`, `c₂ = 3 → a₁`, `c₃ = 4 → a₂` (each transporting
/// one external axiom). Pure-WF: every Imported construct's anchor chain terminates at its
/// external axiom.
pub fn import_substrate() -> Instance {
    // edges c →_ρ a (Imported construct to the external axiom it transports).
    let edges = [(2, 0), (3, 0), (4, 1)];
    let substrate = Substrate::new(5, &edges, &edges).expect("import substrate is well-formed");
    Instance::from_functional_reduction(substrate).expect("imports anchor on external axioms")
}

/// **Rω.9.D1 (`Imp-Sub`)** — the external axiomatic sources `𝒜_ext` adjoined as primitives
/// (the fixpoints of `ρ_spec⁺`), ascending. Here `{a₁, a₂} = {0, 1}`.
pub fn external_axioms() -> Vec<ElementId> {
    import_substrate().operator().fixpoints()
}

/// **Rω.9.D2 (`Ax-Map`)** — `χ_imp(c)`: the external axiom an Imported construct transports —
/// the axiom its `ρ_spec⁺`-orbit terminates at (`CNF_{spec⁺}(c)`). `None` on the external
/// axioms themselves (they are not Imported constructs but their own anchors).
pub fn ax_map(c: ElementId) -> Option<ElementId> {
    let m = import_substrate();
    let op = m.operator();
    if op.is_fixpoint(c) {
        return None; // an external axiom, not an Imported construct
    }
    op.canonical_fixpoint(c) // CNF_{spec⁺}(c) = the axiom it inherits
}

/// **Rω.9.D2 (`Ax-Map`) footprint** — `χ_imp⁻¹(a)`: the **footprint** of external axiom `a`,
/// every Imported construct that transports it, ascending.
pub fn import_footprint(a: ElementId) -> Vec<ElementId> {
    let m = import_substrate();
    m.substrate().elements().filter(|&c| ax_map(c) == Some(a)).collect()
}

/// Witness **Rω.9.T1 (`Imp-Track`)** — the footprints `{χ_imp⁻¹(a) : a ∈ 𝒜_ext}` **partition**
/// the Imported constructs: every Imported construct lands in exactly one footprint, and the
/// footprints are disjoint and exhaust the Imported constructs. The import payload is thereby
/// computable, not assumed. Returns the first Imported construct that is mis-covered (none),
/// or `Ok`.
pub fn certify_imp_track() -> Result<(), ElementId> {
    let m = import_substrate();
    let op = m.operator();
    let axioms = external_axioms();
    for c in m.substrate().elements() {
        if op.is_fixpoint(c) {
            continue; // external axioms are the leaves, not part of the tracked domain
        }
        // exactly one footprint contains c.
        let memberships = axioms.iter().filter(|&&a| import_footprint(a).contains(&c)).count();
        if memberships != 1 {
            return Err(c);
        }
    }
    Ok(())
}

/// Witness **Rω.9.T2 (`Imp-Reify`)** — Reification carries imports **naturally, up to `ι`**:
/// the import substrate is pure-WF, so `Reify` applies, and by `Fix-Bas` (R6.5.T1) every
/// external axiom `a ∈ 𝒜_ext ⊆ Fix(ρ_spec⁺)` reifies to the one-atom word `ι(a)` — a depth-0
/// atom of `Reify(Imp-Sub)`. The imported invariants become the atoms of the reified tower.
/// Returns `true` when every external axiom reifies to its canonical atom.
pub fn certify_imp_reify() -> bool {
    let base = import_substrate();
    let reified = reify(&base);
    // the reify's atoms are exactly 𝒜_ext (the fixpoints of ρ_spec⁺).
    if reified.atoms() != external_axioms().as_slice() {
        return false;
    }
    // Fix-Bas: each external axiom maps to a one-atom word ι(a), which is a depth-0 atom.
    external_axioms().iter().all(|&a| {
        let atom = reified.canonical_inclusion(a);
        reified.is_fixpoint(&atom) && reified.depth(&atom) == 0
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imports_are_tracked_as_footprints_and_reify_to_atoms() {
        // Imp-Sub: 𝒜_ext = {0, 1} are the adjoined primitives (fixpoints).
        assert_eq!(external_axioms(), vec![ElementId(0), ElementId(1)]);
        // Ax-Map: c₁, c₂ transport a₁ = 0; c₃ transports a₂ = 1.
        assert_eq!(ax_map(ElementId(2)), Some(ElementId(0)));
        assert_eq!(ax_map(ElementId(4)), Some(ElementId(1)));
        // footprint of a₁ is {c₁, c₂}; of a₂ is {c₃}.
        assert_eq!(import_footprint(ElementId(0)), vec![ElementId(2), ElementId(3)]);
        assert_eq!(import_footprint(ElementId(1)), vec![ElementId(4)]);
        // Imp-Track: the footprints partition the Imported constructs.
        assert!(matches!(certify_imp_track(), Ok(())));
        // Imp-Reify: external axioms become the atoms of Reify(Imp-Sub).
        assert!(certify_imp_reify());
    }
}
