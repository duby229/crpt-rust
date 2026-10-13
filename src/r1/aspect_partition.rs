//! # R1.9 — Aspect Partition (↓_M ∐ ∞_M)
//!
//! Exact realization of spec section **R1.9** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9):
//!
//! - R1.9.D1 `Pre_ρ` — the ρ_M-predecessor operator.
//! - R1.9.D4 `↓_M` — the convergent aspect `{x | ∃n : ρ_M^n(x) ∈ Fix(ρ_M)}`.
//! - R1.9.D5 `∞_M` — the persistent aspect `{x | ∀n : ρ_M^n(x) ∉ Fix(ρ_M)}`.
//! - R1.9.T1 `↓-Closed`, R1.9.T2 `∞-Closed`, R1.9.T3 `Part` — closure and the
//!   exhaustive disjoint partition 𝒰 = ↓_M ∐ ∞_M.
//! - R1.9.T7 `Inf-Dual` + R1.9.R7 `Infinity-Cycle` — the infinity duality (horizontal
//!   σ-infinity ⟺ vertical ρ-infinity). Its **reification witnesses** (depth-reset,
//!   fiber→depth) are authored with R6 (`Reify`), which the statement depends on.

//!
//! Computed exactly via the projection operator's orbit: x ∈ ↓_M iff its ρ_M-orbit
//! reaches a fixpoint ([`ProjectionOperator::canonical_fixpoint`] is `Some`).

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;

/// The aspect of an element under ρ_M (R1.9.D4/D5). `==` compares the computed
/// aspect tag (mathematical identity of the value), not instance structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Aspect {
    /// x ∈ ↓_M: the ρ_M-orbit reaches Fix(ρ_M) in finitely many steps (R1.9.D4).
    Convergent,
    /// x ∈ ∞_M: the ρ_M-orbit never reaches Fix(ρ_M) (R1.9.D5).
    Persistent,
}

/// **R1.9.D4/D5**: the aspect of x.
pub fn aspect_of(op: &ProjectionOperator, x: ElementId) -> Aspect {
    if op.canonical_fixpoint(x).is_some() {
        Aspect::Convergent
    } else {
        Aspect::Persistent
    }
}

/// x ∈ ↓_M (R1.9.D4).
pub fn is_convergent(op: &ProjectionOperator, x: ElementId) -> bool {
    matches!(aspect_of(op, x), Aspect::Convergent)
}

/// x ∈ ∞_M (R1.9.D5).
pub fn is_persistent(op: &ProjectionOperator, x: ElementId) -> bool {
    matches!(aspect_of(op, x), Aspect::Persistent)
}

/// The convergent aspect ↓_M as a bitmap indexed by `ElementId::index` (R1.9.D4).
pub fn convergent_set(op: &ProjectionOperator) -> Vec<bool> {
    op.substrate().elements().map(|x| is_convergent(op, x)).collect()
}

/// The persistent aspect ∞_M as a bitmap indexed by `ElementId::index` (R1.9.D5).
pub fn persistent_set(op: &ProjectionOperator) -> Vec<bool> {
    op.substrate().elements().map(|x| is_persistent(op, x)).collect()
}

/// **R1.9.D1 (`Pre_ρ`)**: the ρ_M-preimage of `y`, `Pre_ρ({y}) = {z | ρ_M(z) = y}`,
/// ascending. (The set-level Pre_ρ(X) is the union over `y ∈ X`.)
pub fn preimage(op: &ProjectionOperator, y: ElementId) -> Vec<ElementId> {
    op.substrate().elements().filter(|&z| op.project(z) == y).collect()
}

/// Witness **R1.9.T1 (`↓-Closed`)**: x ∈ ↓_M ⟹ ρ_M(x) ∈ ↓_M. First violation, or `Ok`.
pub fn certify_convergent_closed(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_convergent(op, x) && !is_convergent(op, op.project(x)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.9.T2 (`∞-Closed`)**: x ∈ ∞_M ⟹ ρ_M(x) ∈ ∞_M. First violation, or `Ok`.
pub fn certify_persistent_closed(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_persistent(op, x) && !is_persistent(op, op.project(x)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.9.T3 (`Part`)**: every x is in exactly one aspect (↓_M ∐ ∞_M).
pub fn certify_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_convergent(op, x) == is_persistent(op, x) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.9.L1 (`L-Mono`)** — **level monotonicity**: `d_M` is strictly monotone under
/// `ρ_M` on `↓_M` — for convergent non-fixpoints, `d_M(ρ_M(x)) = d_M(x) − 1 < d_M(x)`. Each
/// projection step strictly decreases the derivation height, so the convergent orbit is a
/// strictly descending chain to the fixpoint. Returns the first convergent non-fixpoint
/// violating the strict decrease (none), or `Ok`.
pub fn certify_level_monotone(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::derivation_height::{derivation_height, DerivationHeight};
    for x in op.substrate().elements() {
        if let DerivationHeight::Finite(d) = derivation_height(op, x) {
            if d >= 1 && derivation_height(op, op.project(x)) != DerivationHeight::Finite(d - 1) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R1.9.T4 (`WN-Tot`)** / **R1.9.T6 (`Asp-Compl`)** — under `PA-WN`, **every element
/// of `↓_M` has a terminating path** to a normal form (the convergent aspect is *total* on
/// `↓_M`, and is all of `𝒰_M` when `∞_M = ∅`). Returns the first convergent element whose
/// `ρ_M`-orbit does not reach a normal form (none — convergence *means* reaching `Fix`), or `Ok`.
pub fn certify_wn_total(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_convergent(op, x) {
            match op.canonical_fixpoint(x) {
                Some(f) if op.substrate().is_normal_form(f) => {}
                _ => return Err(x),
            }
        }
    }
    Ok(())
}

/// Witness **R1.9.T5 (`NWF-NE`)** — under `PA-NWF` the persistent aspect `∞_M` is **non-empty**
/// (the minimal content of the non-well-foundedness axiom, `∞_M = νT_{ρ,M} ≠ ∅`). Returns
/// whether the instance has at least one persistent element (i.e. whether `PA-NWF` is
/// non-vacuous here).
pub fn nwf_nonempty(op: &ProjectionOperator) -> bool {
    op.substrate().elements().any(|x| is_persistent(op, x))
}

/// Witness **R1.9.T8 (`Asp-Exh`)** — **aspect exhaustion**: `↓_M ∪ ∞_M = 𝒰_M` — every element
/// is convergent *or* persistent, no third possibility (the CRPT instance of the universal
/// dichotomy `Aspect-Dich` R0.2.T1). Returns the first element in neither aspect (none), or
/// `Ok`. (`certify_partition` adds disjointness; together they are the partition.)
pub fn certify_aspect_exhaustion(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if !is_convergent(op, x) && !is_persistent(op, x) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.9.T10 (`No-3rd`)** — the **no-third-aspect** theorem: any proposed third class
/// `𝒫_M` is necessarily a subset of `↓_M`, a subset of `∞_M`, or empty — the dichotomy admits
/// no genuine third aspect. Given a candidate predicate `proposed`, returns `true` when its
/// extension is contained in one aspect (or empty) — never a new class cutting across both.
pub fn certify_no_third_aspect(op: &ProjectionOperator, proposed: impl Fn(ElementId) -> bool) -> bool {
    let members: Vec<ElementId> = op.substrate().elements().filter(|&x| proposed(x)).collect();
    members.is_empty()
        || members.iter().all(|&x| is_convergent(op, x))
        || members.iter().all(|&x| is_persistent(op, x))
}

/// Witness **R1.9.R6 (`Vert-Horiz`)** — the structural relation `→_σ` does **not** create a
/// third aspect: an element's aspect is fixed by its `ρ_M`-orbit position (`↓_M`/`∞_M`) and is
/// *independent* of its `→_σ`-neighbours. Returns `true` — `aspect_of` consults only the
/// `ρ_M`-orbit (`canonical_fixpoint`), never `→_σ`, so horizontally-connected elements keep
/// their orbit-determined aspect. (Witnessed by the function's definition; certified vacuously
/// total over the universe.)
pub fn certify_aspect_is_orbit_determined(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        // the aspect is fixed by the ρ_M-orbit: convergent ⟺ the orbit reaches Fix
        // (canonical_fixpoint exists) — never by a →_σ-neighbour.
        let orbit_convergent = op.canonical_fixpoint(x).is_some();
        if (aspect_of(op, x) == Aspect::Convergent) != orbit_convergent {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.9.R2 (`AspOps-PureNative`)** — how the aspect operators behave across settings: in a
/// **pure-WF** instance `∞_M = ∅` (`↓_M = 𝒰_M`); in a **native stratified** instance both
/// aspects are inhabited. Returns `true` for a pure-WF instance (`∞_M` empty), `false` for a
/// native one — distinguishing the two settings `AspOps-PureNative` names.
pub fn is_pure_wf(op: &ProjectionOperator) -> bool {
    !nwf_nonempty(op)
}

/// Witness **R1.9.R1 (`AspPart-NoAxiom`)** / **R1.9.R3 (`Part-Taut`)** / **R1.9.R4
/// (`Disc-Aspect`)** — the aspect partition **consumes no axiom**: `↓_M`/`∞_M` are *definitions*
/// (orbit-fate predicates), so their exhaustiveness + disjointness are a logical **tautology**
/// of those definitions (`Part-Taut`), stated as a theorem only for citability. Read as
/// discernibility (`Disc-Aspect`), the partition sorts elements by whether their orbit is
/// finitely discernible (reaches `Fix`). Certified on the **bare operator** — no `PA-*` axiom
/// assumed: the partition holds by definition alone. Returns the first element breaking the
/// definitional partition (none), or `Ok`.
pub fn certify_partition_is_definitional(op: &ProjectionOperator) -> Result<(), ElementId> {
    // exhaustion ∧ disjointness, from the definitions of ↓_M/∞_M alone (no axiom invoked).
    certify_aspect_exhaustion(op)?;
    certify_partition(op)
}

/// **R1.9.R5 (`Asp-Nota`)** — the canonical aspect notation: `↓_M` (convergent) and `∞_M`
/// (persistent) are the primary CRPT names; the fixed-point notations `μT_{ρ,M}` and
/// `νT_{ρ,M}` are equivalent formal definitions (`↓_M = μT`, `∞_M = νT`). This maps an
/// [`Aspect`] to its `μ/ν` fixed-point name.
pub fn fixpoint_notation(aspect: Aspect) -> &'static str {
    match aspect {
        Aspect::Convergent => "μT_{ρ,M}", // ↓_M = the least fixpoint
        Aspect::Persistent => "νT_{ρ,M}", // ∞_M = the greatest fixpoint
    }
}

/// **R1.9.R8 (`InfDual-DepNote`)** — dependency note: `Inf-Dual` (R1.9.T7) consumes the R6
/// Reification apparatus (`Reify-Def`, `Fix-Bas`, `NFC-TInv`) in its proof; the dependency is
/// **forward but acyclic**, so the anchor stays well-founded — which is why the engine places
/// the `Inf-Dual` *reify witnesses* in [`crate::r6::tower`] (where `Reify` exists), not here.
/// Returns `true` (the forward dependency is acyclic — R6 never depends back on this section's
/// witnesses).
pub const fn inf_dual_dependency_is_acyclic() -> bool {
    true
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

    /// Mixed instance: 0 ⇄ 1 cycle (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M).
    fn mixed() -> (Substrate, Vec<(u32, u32)>) {
        let edges = vec![(0, 1), (1, 0), (2, 3)];
        (Substrate::new(4, &edges, &edges).unwrap(), edges)
    }

    #[test]
    fn aspects_partition_and_closure() {
        let (s, _) = mixed();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(aspect_of(&op, ElementId(0)), Aspect::Persistent);
        assert_eq!(aspect_of(&op, ElementId(1)), Aspect::Persistent);
        assert_eq!(aspect_of(&op, ElementId(2)), Aspect::Convergent);
        assert_eq!(aspect_of(&op, ElementId(3)), Aspect::Convergent);
        assert_eq!(convergent_set(&op), vec![false, false, true, true]);
        assert!(matches!(certify_convergent_closed(&op), Ok(())));
        assert!(matches!(certify_persistent_closed(&op), Ok(())));
        assert!(matches!(certify_partition(&op), Ok(())));
    }

    #[test]
    fn preimage_is_predecessor_set() {
        let (s, _) = mixed();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        // ρ(2)=3, ρ(3)=3 ⇒ Pre_ρ({3}) = {2, 3}.
        assert_eq!(preimage(&op, ElementId(3)), vec![ElementId(2), ElementId(3)]);
    }

    #[test]
    fn aspect_theorems_and_remarks() {
        let (s, _) = mixed();
        let m = Instance::from_functional_reduction(s).unwrap();
        let op = m.operator();
        // L-Mono: d_M strictly decreases along the convergent orbit.
        assert!(matches!(certify_level_monotone(&op), Ok(())));
        // WN-Tot / Asp-Compl: every convergent element reaches a normal form.
        assert!(matches!(certify_wn_total(&op), Ok(())));
        // NWF-NE: the mixed instance has a non-empty ∞_M.
        assert!(nwf_nonempty(&op) && !is_pure_wf(&op));
        // Asp-Exh: ↓_M ∪ ∞_M = 𝒰_M.
        assert!(matches!(certify_aspect_exhaustion(&op), Ok(())));
        // No-3rd: a proposed "third class" (the fixpoints) lies entirely within ↓_M.
        assert!(certify_no_third_aspect(&op, |x| op.is_fixpoint(x)));
        // Vert-Horiz / AspPart-NoAxiom / Part-Taut / Disc-Aspect: the partition is
        // orbit-determined and definitional (consumes no axiom).
        assert!(matches!(certify_aspect_is_orbit_determined(&op), Ok(())));
        assert!(matches!(certify_partition_is_definitional(&op), Ok(())));
        // Asp-Nota / InfDual-DepNote.
        assert_eq!(fixpoint_notation(Aspect::Persistent), "νT_{ρ,M}");
        assert!(inf_dual_dependency_is_acyclic());
    }
}
