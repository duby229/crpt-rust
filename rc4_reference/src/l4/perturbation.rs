//! # L4.7 — Coherent Perturbation
//!
//! Exact realization of the finite definitional core of spec section **L4.7**
//! (`CRPT_OMEGA_TOWER_L4.md`, v1.0.0-rc4):
//!
//! - L4.7.D1 `Perturb` — a perturbation of `ρ_M` is another strategy `ρ'_M` satisfying
//!   C1/C2 that differs from `ρ_M` at finitely many points (automatic on a finite
//!   substrate). Realized as a second [`Model`] over the *same* substrate.
//! - L4.7.D2 `CPEP` — detectability: a perturbation is **persistent-detectable** at `x` if
//!   it changes the persistent canonical orbit invariant `CNF∞` (the ω-limit class,
//!   L3.3.D1) of `x`. [`persistent_detectable`] decides this for a *given* perturbation.
//!
//! **Out of finite per-instance scope** (noted, not faked): the full `CPEP` property
//! quantifies over **all** perturbations (`∀ρ'_M`), and `CPEP-Ind` (L4.7.T1) is an
//! *independence* meta-theorem — neither `CPEP` nor `¬CPEP` follows from PA-* — witnessed
//! by **infinite** countermodels (`M_cohere` over `ℕ⁺ ∪ {ω·n}`, `M_absorb`). Those are
//! universal/meta statements, not a single finite model's computation; this module decides
//! detectability for each concrete perturbation instead.

use crate::l1::substrate::ElementId;
use crate::l2::projection::Model;
use crate::l2::regime::is_persistent;
use crate::l3::persistent::{omega_limit_classes, omega_limit_set};

/// **L4.7.D3 (`Refl-Abs-D`)** — whether the substrate is **reflective**: every convergent
/// non-fixpoint `x` admits a structural perturbation `x →_σ* x' ∈ ∞_M` whose persistent
/// canonical form `CNF∞(x')` equals `[CFix(x)]_≈`. (Vacuously true if there are no
/// convergent non-fixpoints.)
///
/// **Combinatorial degeneracy.** `[CFix(x)]_≈` is a *convergent* ≈-class while `CNF∞(x')`
/// (the recurrence-realization ω-limit) is a set of *persistent* ≈-classes — and bisimilar
/// elements share a regime, so the two can never match on a bare finite substrate. So a
/// finite combinatorial substrate is reflective only vacuously; the non-degenerate
/// reflective case lives in the **topological tier** (where `CNF∞` is a topological limit
/// that can be a convergent class — cf. the `ℕ ∪ (0,1]` witness). The predicate is exact;
/// its value is just degenerate here, like Class F = ∅.
pub fn is_reflective(m: &Model) -> bool {
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

/// **L4.7.D3 (`Refl-Abs-D`)** — whether the substrate is **absorbing**: *no* convergent
/// non-fixpoint admits a perturbation matching its convergent canonical form (the dual of
/// [`is_reflective`]). On a bare finite substrate this holds whenever a convergent
/// non-fixpoint exists (see the degeneracy note on [`is_reflective`]).
pub fn is_absorbing(m: &Model) -> bool {
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

/// **L4.7.D1 (`Perturb`)** — whether `perturbed` is a perturbation of `base`: a model over
/// the same-size universe (so the strategies differ at finitely many points — automatic on
/// a finite substrate). Both being [`Model`]s, each already satisfies C1/C2.
pub fn is_perturbation(base: &Model, perturbed: &Model) -> bool {
    base.substrate().universe_len() == perturbed.substrate().universe_len()
}

/// The points at which a perturbation changes the strategy: `{x | ρ'_M(x) ≠ ρ_M(x)}`
/// (L4.7.D1). Ascending.
pub fn perturbation_support(base: &Model, perturbed: &Model) -> Vec<ElementId> {
    let base_op = base.operator();
    let perturbed_op = perturbed.operator();
    base.substrate()
        .elements()
        .filter(|&x| base_op.project(x) != perturbed_op.project(x))
        .collect()
}

/// **L4.7.D2 (`CPEP`)** — whether the perturbation is **persistent-detectable** at `x`: it
/// changes `CNF∞(x)` (the ω-limit class). `false` means the perturbation is undetectable in
/// `x`'s persistent tail (the coherence condition of CPEP at `x`). Compares the ω-limit set
/// of `x` under each strategy (the substrate, hence `≈`, is shared).
pub fn persistent_detectable(base: &Model, perturbed: &Model, x: ElementId) -> bool {
    omega_limit_set(&base.operator(), x) != omega_limit_set(&perturbed.operator(), x)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn bare_substrate_is_absorbing_not_reflective() {
        // 0→1→2, 2 ∈ NF: convergent non-fixpoints (0,1) cannot perturb to a persistent
        // element whose ω-limit is a convergent class ⇒ absorbing, not reflective
        // (the combinatorial degeneracy: reflective is a topological-tier phenomenon).
        let e = [(0, 1), (1, 2)];
        let m = Model::from_functional_reduction(Substrate::new(3, &e, &e).unwrap()).unwrap();
        assert!(is_absorbing(&m));
        assert!(!is_reflective(&m));
        // a pure-fixpoint model (no convergent non-fixpoints) is vacuously reflective.
        let one = Model::from_functional_reduction(Substrate::new(1, &[], &[]).unwrap()).unwrap();
        assert!(is_reflective(&one));
    }

    #[test]
    fn perturbation_support_and_detectability() {
        // Substrate with a branch at 0: 0→1, 0→2, then 1⇄... actually two cycles reachable.
        // base ρ(0)=1 routes 0 into cycle {1,2}; perturbed ρ(0)=3 routes it into cycle {3,4}.
        // 1⇄2 and 3⇄4 are obs-distinct persistent cycles.
        let red = [(0, 1), (0, 3), (1, 2), (2, 1), (3, 4), (4, 3)];
        let s = Substrate::with_observation(5, &red, &red, &[9, 10, 11, 12, 13]).unwrap();
        // base: ρ(0)=1 (into {1,2}); perturbed: ρ(0)=3 (into {3,4}).
        let base = Model::new(s, vec![id(1), id(2), id(1), id(4), id(3)]).unwrap();
        let s2 = Substrate::with_observation(5, &red, &red, &[9, 10, 11, 12, 13]).unwrap();
        let perturbed = Model::new(s2, vec![id(3), id(2), id(1), id(4), id(3)]).unwrap();
        assert!(is_perturbation(&base, &perturbed));
        // they differ only at 0.
        assert_eq!(perturbation_support(&base, &perturbed), vec![id(0)]);
        // 0 is persistent in both but reaches different cycles ⇒ detectable at 0.
        assert!(persistent_detectable(&base, &perturbed, id(0)));
        // a cycle element (1) is unaffected ⇒ not detectable there.
        assert!(!persistent_detectable(&base, &perturbed, id(1)));
    }
}
