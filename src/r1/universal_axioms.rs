//! # R1.3 — Universal Axioms
//!
//! Exact realization of spec section **R1.3** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9). This
//! section's membership criterion: the **aspect-universal orbit
//! axioms** — constraints on the *whole* `ρ_M`-orbit (its asymptotics), not a single step.
//!
//! - R1.3.Ax1 `PA-Bisim` (≈) — Bisimulation Congruence: `∀x,y : x ≈ y ⟹ x ≃_M y`, with
//!   `≃_M` read aspect-aware as the hybrid semantic class `π_sem` (R2.3.D9): `CFix`-equality
//!   on `↓_M`, persistent orbit equivalence `≃∞` on `∞_M` ([`pa_bisim`]).
//! - R1.3.Ax2 `PA-Reach` (meaning form) — every persistent orbit has a **canonically
//!   representable asymptotic destination** `ω_≈(x)`: (R1) non-empty, (R2) finite and
//!   `ρ_M`-closed, (R3) attracting; with `CPer_M(x)` its canonical representative
//!   ([`pa_reach`]). *How* it is reached is realization theory, not the axiom.
//! - R1.3.D1 `CPer` — the canonical persistent representative `ρ_M^{n_M(x)}(x)`
//!   ([`canonical_persistent_representative`]).
//! - R1.3.T2 `Reach-Fin` / R1.3.T3 `Reach-Top` / R1.3.T4 `Reach-Decomp` — the recurrence,
//!   convergence, and decomposition realizations
//!   ([`certify_reach_fin`]/[`certify_reach_top`]/[`certify_reach_decomp`]).
//! - R1.3.R2 `Reach-Indep` — `PA-Reach` is independent of the other eight (the `M_Reach`
//!   countermodel: a persistent orbit with `ω_≈ = ∅`).

use crate::r1::aspect_partition::is_convergent;
use crate::r1::reduction_strategy::{Instance, ProjectionOperator};
use crate::r1::substrate::ElementId;
use crate::r2::canonical_orbit_invariant::{
    n_reach, omega_limit_classes, semantic_projection,
};

/// **R1.3.Ax1 (`PA-Bisim`)** — Bisimulation Congruence: `∀x,y : x ≈ y ⟹ x ≃_M y`, with
/// `≃_M` read **aspect-aware** as the hybrid semantic class `π_sem` (R2.3.D9):
/// `CFix`-equality on `↓_M`, persistent orbit equivalence `≃∞` (equal ω-limit class,
/// R2.3.D7) on `∞_M`. So this checks `x ≈ y ⟹ π_sem(x) = π_sem(y)`. Non-vacuous because
/// `≈` is the labelled bisimulation (R1.1.D7) that keeps distinct normal forms apart.
/// Returns the first bisimilar pair with distinct semantic class, or `Ok`.
pub fn pa_bisim(instance: &Instance) -> Result<(), (ElementId, ElementId)> {
    let op = instance.operator();
    let substrate = instance.substrate();
    let representative = substrate.bisimilarity();
    let elements: Vec<ElementId> = substrate.elements().collect();
    for &x in &elements {
        for &y in &elements {
            if representative[x.index()] == representative[y.index()] // x ≈ y
                && semantic_projection(&op, x) != semantic_projection(&op, y)
            {
                return Err((x, y));
            }
        }
    }
    Ok(())
}

/// **R1.3.Ax2 (`PA-Reach`, meaning form)** — every persistent orbit has a **canonically
/// representable asymptotic destination**: for all `x ∈ ∞_M`,
/// - **(R1)** `ω_≈(x) ≠ ∅` — the destination exists;
/// - **(R2)** `ω_≈(x)` is finite and `ρ_M`-closed — a finite `ρ̄_M`-cycle of classes;
/// - **(R3)** the orbit is attracted to it — a tail of the class orbit lies in it;
///
/// with `CPer_M(x)` the destination's canonical representative. *How* it is reached is not
/// part of the axiom — the mechanisms are realization theorems (`Reach-Fin` R1.3.T2,
/// `Reach-Top` R1.3.T3, `Reach-Decomp` R1.3.T4: never a third). Checked exactly on the
/// finite substrate.
pub fn pa_reach(instance: &Instance) -> bool {
    let op = instance.operator();
    let representative = instance.substrate().bisimilarity();
    instance.substrate().elements().all(|x| {
        if is_convergent(&op, x) {
            return true;
        }
        let destination = omega_limit_classes(&op, x); // ω_≈(x)
        // (R2) ρ_M-closed: every ω-limit ≈-class steps into the destination set.
        let closed = destination.iter().all(|&class_repr| {
            let next_class = representative[op.project(class_repr).index()];
            destination.contains(&next_class)
        });
        // (R3) attracting: a tail of the class orbit lies in the set.
        let mut current = x;
        for _ in 0..instance.substrate().universe_len() {
            current = op.project(current);
        }
        let attracted = destination.contains(&representative[current.index()]);
        !destination.is_empty() && closed && attracted // (R1) ∧ (R2) ∧ (R3)
    })
}

/// **R1.3.D1 (`CPer`)** — the **canonical persistent representative**
/// `CPer_M(x) := ρ_M^{n_M(x)}(x)`: the point on x's orbit where its `≈`-class sequence
/// enters its recurrent cycle (`n-Reach` R2.3.D10). `PA-Reach` guarantees `n_M(x)` exists,
/// making `CPer_M(x)` the canonical *finite* descriptor of the infinite element x. `None`
/// on `↓_M` (where `CFix` is the canonical form).
pub fn canonical_persistent_representative(op: &ProjectionOperator, x: ElementId) -> Option<ElementId> {
    let n = n_reach(op, x)?;
    let mut current = x;
    for _ in 0..n {
        current = op.project(current);
    }
    Some(current)
}

/// Witness **R1.3.R1 (`Reach-Role`)** — what `PA-Reach` *is*: not a **connectivity** axiom
/// (it never requires elements be reachable from one another) but a **recursive-projection**
/// axiom constraining the long-run behaviour of `ρ_M` on persistent orbits. Realized by
/// confirming the role: every persistent element has a canonically-representable asymptotic
/// **destination** (`CPer`), independent of any structural reachability between elements.
/// Returns the first persistent element lacking a recursive-projection destination (none when
/// `PA-Reach` holds), or `Ok`.
pub fn certify_reach_role(instance: &Instance) -> Result<(), ElementId> {
    let op = instance.operator();
    for x in instance.substrate().elements() {
        // the axiom's content is about ρ_M's asymptotics (the destination CPer), not about
        // →_σ-connectivity: on ∞_M, CPer must exist.
        if !is_convergent(&op, x) && canonical_persistent_representative(&op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.3.T1 (`Reach-ObsExt`)** — the **Observer Extraction Principle**: `PA-Reach`
/// closes the reachability gap between finite observers and infinite orbits — the canonical
/// representative `CPer_M(x)` is reached at **finite observational cost** (`≤ |𝒰|` steps),
/// so a finite observer can extract a canonical finite summary of a persistent (infinite)
/// object. Returns the first persistent element whose `CPer` is not reached within `|𝒰|`
/// steps (none — the `≈`-class orbit enters its cycle within `|𝒰|`), or `Ok`.
pub fn certify_observer_extraction(instance: &Instance) -> Result<(), ElementId> {
    let op = instance.operator();
    let bound = instance.substrate().universe_len() as u64;
    for x in instance.substrate().elements() {
        if is_convergent(&op, x) {
            continue;
        }
        // CPer = ρ_M^{n_M(x)}(x); the finite observational cost is n_M(x) ≤ |𝒰|.
        match crate::r2::canonical_orbit_invariant::n_reach(&op, x) {
            Some(n) if n <= bound => {}
            _ => return Err(x), // no finite extraction — the observer could not summarize x
        }
    }
    Ok(())
}

/// Witness **R1.3.T2 (`Reach-Fin`)** — the **recurrence realization**: where the
/// destination is *visited* (on a finite substrate: every persistent orbit), the
/// `≈`-class orbit is eventually periodic; `ω_≈(x)` is exactly the recurrent cycle,
/// entered at depth `n_M(x)` with `CPer_M(x)` its entry point — the NWF mirror of `PA-WN`'s
/// reach of `Fix` at `d_M`. Returns the first violating persistent element, or `Ok`.
pub fn certify_reach_fin(instance: &Instance) -> Result<(), ElementId> {
    let op = instance.operator();
    let representative = instance.substrate().bisimilarity();
    for x in instance.substrate().elements() {
        if is_convergent(&op, x) {
            continue;
        }
        let destination = omega_limit_classes(&op, x);
        let Some(cper) = canonical_persistent_representative(&op, x) else {
            return Err(x); // n_M must be total on the recurrence face
        };
        if !destination.contains(&representative[cper.index()]) {
            return Err(x); // CPer's class must lie in the destination cycle
        }
    }
    Ok(())
}

/// Witness **R1.3.T3 (`Reach-Top`)** — the **convergence realization** on the topological
/// tier: if the orbit of persistent `x` `𝒯`-converges to `L`, then `L` is a fixpoint
/// (continuity turns "limit of the orbit" into "fixpoint of the operator"), unique by
/// Hausdorff separation (`TopSep-Uniq` R1.7.T1). `Some(true)` when certified, `Some(false)`
/// if the limit exists but is not a fixpoint, `None` off the `PA-WN_top` sub-class.
pub fn certify_reach_top<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    if sys.projection_depth(x).is_some() {
        return None; // convergent — out of the persistent reach face
    }
    let limit = sys.topological_limit(x)?;
    Some(sys.is_fixpoint(&limit))
}

/// Witness **R1.3.T4 (`Reach-Decomp`)** — every realization decomposes into the two
/// mechanisms: **(i)** the destination `ω_≈(x)` is a *single* finite `ρ̄_M`-cycle of
/// classes; **(ii)** on the finite substrate the reach face is recurrence — a tail of the
/// class orbit lies in the cycle. No third mechanism. Returns the first violating
/// persistent element, or `Ok`.
pub fn certify_reach_decomp(instance: &Instance) -> Result<(), ElementId> {
    let op = instance.operator();
    let representative = instance.substrate().bisimilarity();
    for x in instance.substrate().elements() {
        if is_convergent(&op, x) {
            continue;
        }
        let destination = omega_limit_classes(&op, x);
        // (i) ρ̄_M maps the destination onto itself through one cycle.
        let mut visited: Vec<ElementId> = Vec::new();
        for &class_repr in &destination {
            let next_class = representative[op.project(class_repr).index()];
            if !destination.contains(&next_class) {
                return Err(x);
            }
            if !visited.contains(&next_class) {
                visited.push(next_class);
            }
        }
        visited.sort_by_key(|e| e.0);
        if visited != destination {
            return Err(x); // not a single onto cycle of classes
        }
        // (ii) recurrence face: a tail of the class orbit lies in the destination.
        let mut current = x;
        for _ in 0..instance.substrate().universe_len() {
            current = op.project(current);
        }
        if !destination.contains(&representative[current.index()]) {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    #[test]
    fn pa_reach_meaning_form_with_realizations() {
        // 0→1 (↓_M); 2⇄3 obs-distinct (∞_M). The destination ω_≈ is the two-class cycle:
        // R1 ✓ R2 (ρ̄-closed) ✓ R3 (attracting) ✓; the recurrence realization + decomposition
        // certify. PA-Bisim holds (no bisimilar pair splits π_sem).
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Instance::new(s, vec![ElementId(1), ElementId(1), ElementId(3), ElementId(2)]).unwrap();
        assert!(pa_reach(&m));
        assert!(matches!(pa_bisim(&m), Ok(())));
        assert!(matches!(certify_reach_fin(&m), Ok(())));
        assert!(matches!(certify_reach_decomp(&m), Ok(())));
        // Reach-Role: PA-Reach gives a recursive-projection destination (not connectivity).
        assert!(matches!(certify_reach_role(&m), Ok(())));
        // Reach-ObsExt: the observer extracts CPer at finite cost (≤ |𝒰|).
        assert!(matches!(certify_observer_extraction(&m), Ok(())));
        // CPer enters the cycle: from 2, n_M = 0 (already on the cycle), CPer(2) = 2.
        let op = m.operator();
        assert_eq!(canonical_persistent_representative(&op, ElementId(2)), Some(ElementId(2)));
        // the convergence realization on the topological tier: the chain's limit ω is a fixpoint.
        use crate::r1::topology::{ChainPoint, ConvergentChain};
        assert_eq!(certify_reach_top(&ConvergentChain, &ChainPoint::Step(0)), Some(true));
        assert_eq!(certify_reach_top(&ConvergentChain, &ChainPoint::Limit), None);
    }

    #[test]
    fn pa_reach_uses_bisimulation_classes_for_closure() {
        // 0⇄1 with distinct observations: the persistent ω-limit is a singleton ≈-class
        // though the raw ω-cycle contains two elements. PA-Reach and Reach-Decomp should
        // hold on the quotient-level destination.
        let e = [(0, 1), (1, 0)];
        let s = crate::r1::substrate::Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Instance::new(s, vec![ElementId(1), ElementId(0)]).unwrap();
        assert!(pa_reach(&m));
        assert!(matches!(certify_reach_decomp(&m), Ok(())));
    }

    /// **R1.3.R2 (`Reach-Indep`) — the `M_Reach` countermodel**: a persistent orbit
    /// visiting pairwise-distinct `≈`-classes, each once, with a discrete topology (no
    /// `𝒯`-accumulation) — `ω_≈ = ∅` violates (R1). `PA-Reach` is independent of the rest.
    struct MReach;

    impl crate::r0::projection_systems_and_fibers::ProjectionSystem for MReach {
        type Point = u64;
        fn projection(&self, x: &u64) -> u64 {
            x + 1 // sₙ →_ρ sₙ₊₁: never repeats, never reaches a fixpoint
        }
        fn projection_depth(&self, x: &u64) -> Option<u32> {
            let _ = x;
            None // persistent
        }
    }
    impl crate::r1::topology::TopologicalProjectionSystem for MReach {
        fn topological_limit(&self, x: &u64) -> Option<u64> {
            let _ = x;
            None // discrete topology: no 𝒯-accumulation, no convergence face
        }
        fn observation(&self, x: &u64) -> u32 {
            *x as u32 // pairwise-distinct observables: every class is its own
        }
    }

    #[test]
    fn m_reach_witnesses_independence() {
        // no convergence face anywhere on the orbit ⇒ ω_≈(s₀) = ∅, (R1) fails: PA-Reach is
        // not derivable from the other eight axioms.
        let witness = MReach;
        assert_eq!(certify_reach_top(&witness, &0u64), None);
    }
}
