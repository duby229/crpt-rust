//! # R3.7 — Coherent Perturbation
//!
//! Exact realization of the current spec section **R3.7**
//! (`CRPT_OMEGA_TOWER_R3.md`):
//!
//! - R3.7.D1 `Perturb` — a perturbation of the projection operator is a second projection
//!   operator on the same substrate that agrees with the original outside a finite support.
//!   On a finite substrate this is realized as a second [`Instance`] over the same substrate,
//!   with the projection operator allowed to differ at finitely many points.
//! - R3.7.D2 `CPEP` — the coherent perturbation existence property: every convergent
//!   non-fixpoint admits a coherent perturbation into the persistent aspect whose persistent
//!   canonical invariant `CNF∞` matches the convergent canonical form `CFix`.
//!
//! The full `CPEP` property is an existential statement over all perturbations (`∃ρ'_M`), and
//! `CPEP-Ind` (R3.7.T1) is an independence meta-theorem: neither `CPEP` nor `¬CPEP` follows
//! from the PA-* axioms. The finite engine here evaluates the concrete witness conditions for a
//! given instance and a given perturbation.

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::Instance;
use crate::r1::aspect_partition::is_persistent;
use crate::r2::canonical_orbit_invariant::omega_limit_classes;

/// **R3.7.D3 (`Refl-Abs-D`)** — whether the substrate is **reflective**: every convergent
/// non-fixpoint `x` admits a coherent perturbation into the persistent aspect whose persistent
/// canonical form `CNF∞(x')` matches `[CFix(x)]_≈`. The finite engine checks this through the
/// persistent canonical invariant of a reachable persistent witness. (Vacuously true if there are
/// no convergent non-fixpoints.)
///
/// **Combinatorial degeneracy.** `[CFix(x)]_≈` is a *convergent* ≈-class while `CNF∞(x')`
/// (the recurrence-realization ω-limit) is a set of *persistent* ≈-classes — and bisimilar
/// elements share a aspect, so the two can never match on a bare finite substrate. So a
/// finite combinatorial substrate is reflective only vacuously; the non-degenerate
/// reflective case lives in the **topological tier** (where `CNF∞` is a topological limit
/// that can be a convergent class — cf. the `ℕ ∪ (0,1]` witness). The predicate is exact;
/// its value is just degenerate here, like Class F = ∅.
pub fn is_reflective(m: &Instance) -> bool {
    let op = m.operator();
    let representative = op.substrate().bisimilarity();
    for x in op.substrate().elements() {
        match op.canonical_fixpoint(x) {
            Some(canonical) if !op.is_fixpoint(x) => {
                let target = vec![representative[canonical.index()]]; // {[CFix(x)]_≈}
                let matched = op.substrate().elements().any(|x_prime| {
                    is_persistent(&op, x_prime)
                        && op.substrate().structural_reachable(x, x_prime)
                        && omega_limit_classes(&op, x_prime) == target
                });
                if !matched {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

/// **R3.7.D3 (`Refl-Abs-D`)** — whether the substrate is **absorbing**: no convergent
/// non-fixpoint admits a coherent perturbation matching its convergent canonical form (the dual
/// of the reflective witness). On a bare finite substrate this holds whenever a convergent
/// non-fixpoint exists (see the degeneracy note on [`is_reflective`]).
pub fn is_absorbing(m: &Instance) -> bool {
    let op = m.operator();
    let representative = op.substrate().bisimilarity();
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        if let Some(canonical) = op.canonical_fixpoint(x) {
            if op.is_fixpoint(x) {
                continue;
            }
            let target = vec![representative[canonical.index()]];
            let matched = elements.iter().any(|&x_prime| {
                is_persistent(&op, x_prime)
                    && op.substrate().structural_reachable(x, x_prime)
                    && omega_limit_classes(&op, x_prime) == target
            });
            if matched {
                return false; // a match exists ⇒ not absorbing
            }
        }
    }
    true
}

/// **R3.7.D1 (`Perturb`)** — whether `perturbed` is a perturbation of `base`: a second
/// instance over the **same substrate** (same universe, reduction/structural relations, and
/// observation labeling), so the strategies differ at finitely many points — automatic on a
/// finite substrate. Both being [`Instance`]s, each already satisfies C1/C2.
pub fn is_perturbation(base: &Instance, perturbed: &Instance) -> bool {
    let base_substrate = base.substrate();
    let perturbed_substrate = perturbed.substrate();
    if base_substrate.universe_len() != perturbed_substrate.universe_len() {
        return false;
    }
    base_substrate.elements().all(|x| {
        base_substrate.reduction_successors(x) == perturbed_substrate.reduction_successors(x)
            && base_substrate.structural_successors(x) == perturbed_substrate.structural_successors(x)
            && base_substrate.observation(x) == perturbed_substrate.observation(x)
    })
}

/// The points at which a perturbation changes the strategy: `{x | ρ'_M(x) ≠ ρ_M(x)}`
/// (R3.7.D1). Ascending.
pub fn perturbation_support(base: &Instance, perturbed: &Instance) -> Vec<ElementId> {
    let base_op = base.operator();
    let perturbed_op = perturbed.operator();
    base.substrate()
        .elements()
        .filter(|&x| base_op.project(x) != perturbed_op.project(x))
        .collect()
}

/// **R3.7.D2 (`CPEP`)** — whether the perturbation changes the persistent canonical orbit
/// invariant at `x`: the concrete finite check for whether the persistent tail witness changes
/// under the perturbed projection operator. `false` means the perturbation leaves the persistent
/// canonical invariant of `x` unchanged. The spec's persistent canonical invariant is the
/// bisimulation-quotient ω-limit cycle [`omega_limit_classes`], so we compare that quotient
/// invariant rather than the raw orbit elements.
pub fn persistent_canonical_invariant_changes(
    base: &Instance,
    perturbed: &Instance,
    x: ElementId,
) -> bool {
    omega_limit_classes(&base.operator(), x) != omega_limit_classes(&perturbed.operator(), x)
}

/// Backward-compatible wrapper for the concrete invariant-change check.
pub fn persistent_detectable(base: &Instance, perturbed: &Instance, x: ElementId) -> bool {
    persistent_canonical_invariant_changes(base, perturbed, x)
}

/// **R3.7.T2 (`Refl-Abs-T`)** — the coherent perturbation classification an instance's
/// substrate yields. `==` compares the verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpepVerdict {
    /// A **reflective** substrate satisfies CPEP (perturbations stay coherently detectable).
    Satisfies,
    /// An **absorbing** substrate fails CPEP (perturbations are absorbed, undetectable).
    Fails,
    /// A **mixed** substrate satisfies CPEP only partially.
    Partial,
}

/// Witness **R3.7.T2 (`Refl-Abs-T`)** — the **reflective/absorbing dichotomy determines CPEP**:
/// a reflective substrate **satisfies** the coherent perturbation existence property, an absorbing
/// substrate **fails** it, and mixed substrates satisfy only partial CPEP. Returns the instance's
/// coherent-perturbation verdict, read from its reflective/absorbing character.
pub fn coherent_perturbation_classification(m: &Instance) -> CpepVerdict {
    match (is_reflective(m), is_absorbing(m)) {
        (true, false) => CpepVerdict::Satisfies,
        (false, true) => CpepVerdict::Fails,
        _ => CpepVerdict::Partial,
    }
}

/// Backward-compatible wrapper for the coherent-perturbation classification.
pub fn cpep_verdict(m: &Instance) -> CpepVerdict {
    coherent_perturbation_classification(m)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn bare_substrate_is_absorbing_not_reflective() {
        // 0→1→2, 2 ∈ NF: convergent non-fixpoints (0,1) cannot perturb to a persistent
        // element whose ω-limit is a convergent class ⇒ absorbing, not reflective
        // (the combinatorial degeneracy: reflective is a topological-tier phenomenon).
        let e = [(0, 1), (1, 2)];
        let m = Instance::from_functional_reduction(Substrate::new(3, &e, &e).unwrap()).unwrap();
        assert!(is_absorbing(&m));
        assert!(!is_reflective(&m));
        // Refl-Abs-T: an absorbing substrate yields the CPEP-Fails verdict.
        assert_eq!(cpep_verdict(&m), CpepVerdict::Fails);
        // a pure-fixpoint instance (no convergent non-fixpoints) is vacuously reflective.
        let one = Instance::from_functional_reduction(Substrate::new(1, &[], &[]).unwrap()).unwrap();
        assert!(is_reflective(&one));
    }

    #[test]
    fn perturbation_requires_same_substrate() {
        let base_substrate = Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap();
        let other_substrate = Substrate::new(2, &[], &[]).unwrap();
        let base = Instance::from_functional_reduction(base_substrate).unwrap();
        let perturbed = Instance::from_functional_reduction(other_substrate).unwrap();
        assert!(!is_perturbation(&base, &perturbed));
    }

    #[test]
    fn perturbation_support_and_detectability() {
        // Substrate with a branch at 0: 0→1, 0→2, then 1⇄... actually two cycles reachable.
        // base ρ(0)=1 routes 0 into cycle {1,2}; perturbed ρ(0)=3 routes it into cycle {3,4}.
        // 1⇄2 and 3⇄4 are obs-distinct persistent cycles.
        let red = [(0, 1), (0, 3), (1, 2), (2, 1), (3, 4), (4, 3)];
        let s = Substrate::with_observation(5, &red, &red, &[9, 10, 11, 12, 13]).unwrap();
        // base: ρ(0)=1 (into {1,2}); perturbed: ρ(0)=3 (into {3,4}).
        let base = Instance::new(s, vec![id(1), id(2), id(1), id(4), id(3)]).unwrap();
        let s2 = Substrate::with_observation(5, &red, &red, &[9, 10, 11, 12, 13]).unwrap();
        let perturbed = Instance::new(s2, vec![id(3), id(2), id(1), id(4), id(3)]).unwrap();
        assert!(is_perturbation(&base, &perturbed));
        // they differ only at 0.
        assert_eq!(perturbation_support(&base, &perturbed), vec![id(0)]);
        // 0 is persistent in both but reaches different cycles ⇒ detectable at 0.
        assert!(persistent_canonical_invariant_changes(&base, &perturbed, id(0)));
        // a cycle element (1) is unaffected ⇒ the invariant does not change there.
        assert!(!persistent_canonical_invariant_changes(&base, &perturbed, id(1)));
    }

    #[test]
    fn persistent_invariant_change_uses_bisimulation_quotient_not_raw_elements() {
        // A branching reduction graph where the projection may take a transient branch or jump
        // directly to the same eventual fixpoint. The quotient invariant should remain unchanged,
        // even though the raw orbit witness differs.
        let red = [(0, 1), (0, 2), (1, 2)];
        let s = Substrate::with_observation(3, &red, &red, &[9, 10, 11]).unwrap();
        let base = Instance::new(s, vec![id(1), id(2), id(2)]).unwrap();
        let s2 = Substrate::with_observation(3, &red, &red, &[9, 10, 11]).unwrap();
        let perturbed = Instance::new(s2, vec![id(2), id(2), id(2)]).unwrap();

        assert!(is_perturbation(&base, &perturbed));
        assert!(!persistent_canonical_invariant_changes(&base, &perturbed, id(0)));
    }
}
