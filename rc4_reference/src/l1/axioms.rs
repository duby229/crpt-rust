//! # L1.2 / L1.3 — The Projection Axiom System (the nine PA-* axioms)
//!
//! Exact realization of the projection axioms from spec sections **L1.2** and **L1.3**
//! (v1.0.0-rc4). These are the constraints that make a substrate-plus-strategy an actual
//! *CRPT model* — **strictly stronger** than the L2.1 operator conditions C1/C2. A
//! [`Model`] validates C1/C2 at construction; the PA-* axioms are checked here, and a
//! C1/C2-valid model can still violate them (see the module tests).
//!
//! Functions are named by the axiom's **exact spec tag** (`PA-WN` → [`pa_wn`], etc.),
//! not a paraphrase. The nine axioms (L1.2.R1 `PA-NS`):
//!
//! | Tag | Label | Here |
//! |---|---|---|
//! | `PA-WN`     | L1.2.Ax1 | [`pa_wn`] |
//! | `PA-Conf`   | L1.2.Ax2 | [`pa_conf`] |
//! | `PA-Fix`    | L1.2.Ax3 | [`pa_fix`] |
//! | `PA-NWF`    | L1.2.Ax4 | [`pa_nwf`] |
//! | `PA-CoInd`  | L1.2.Ax5 | second-order (Park's lemma); not a finite predicate — derivable from `PA-NWF` (L1.6.T1) |
//! | `PA-Prod`   | L1.2.Ax6 | [`pa_prod`] (given the model's Observable Contract `(O_M, 0)`) |
//! | `PA-WN_top` | L1.2.Ax7 | the topological tier ([`crate::l1::topology`]); finite form vacuous/fails |
//! | `PA-Bisim`  | L1.3.Ax1 | [`pa_bisim`] (regime-aware `≃_M`: `CFix` on ↓_M, `≃∞` on ∞_M) |
//! | `PA-Reach`  | L1.3.Ax2 | [`pa_reach`] — **meaning form** (rc4: R1/R2/R3 on `ω_≈`; realizations [`certify_pa_reach_fin`]/[`certify_pa_reach_top`], decomposition [`certify_pa_reach_decomp`]) |
//!
//! **Resolved in rc3 (was a post-rc2 engine finding).** With a *bare* `(𝒰, →_ρ)`
//! bisimulation, every two distinct normal forms are bisimilar (no →_ρ-successors), so
//! `PA-Bisim` (`x ≈ y ⟹ x ≃_M y`) would force a unique normal form, contradicting a
//! multi-element `Q_M`. rc3 makes `≈` a **labelled** bisimulation (L1.1.D6: `obs ↾ NF`
//! injective — distinct NFs are distinct observables), so `PA-Bisim` is non-vacuous, and
//! reads its conclusion regime-aware (`CFix` on ↓_M, `≃∞` on ∞_M). [`pa_bisim`] and
//! [`crate::l1::substrate::Substrate::bisimilarity`] implement this directly.

use crate::l1::substrate::{ElementId, Substrate};
use crate::l2::projection::Model;
use crate::l3::persistent::semantic_projection;

/// The →_ρ* descendants of `x` (reflexive-transitive closure), ascending.
fn reduction_closure(s: &Substrate, x: ElementId) -> Vec<ElementId> {
    let mut seen = vec![false; s.universe_len() as usize];
    let mut stack = vec![x];
    seen[x.index()] = true;
    let mut out = Vec::new();
    while let Some(u) = stack.pop() {
        out.push(u);
        for &v in s.reduction_successors(u) {
            if !seen[v.index()] {
                seen[v.index()] = true;
                stack.push(v);
            }
        }
    }
    out.sort_by_key(|e| e.0);
    out
}

/// **`PA-WN`** (L1.2.Ax1) — Weak Normalisation: `∀x ∃n,y : x →_ρⁿ y ∧ NF(y)`. Every
/// element has *some* terminating →_ρ-path to a normal form. (Global in pure-WF models;
/// `Scoped(↓_M)` in native models, where persistent elements have no terminating path.)
/// Returns the first element with no reachable normal form, or `Ok`.
pub fn pa_wn(m: &Model) -> Result<(), ElementId> {
    let s = m.substrate();
    for x in s.elements() {
        if !reduction_closure(s, x).iter().any(|&y| s.is_normal_form(y)) {
            return Err(x);
        }
    }
    Ok(())
}

/// **`PA-Conf`** (L1.2.Ax2) — Confluence (Church–Rosser): `x →_ρ* y₁ ∧ x →_ρ* y₂ ⟹
/// ∃z : y₁ →_ρ* z ∧ y₂ →_ρ* z`. Returns the first diverging triple `(x, y₁, y₂)` with no
/// common descendant, or `Ok`.
pub fn pa_conf(m: &Model) -> Result<(), (ElementId, ElementId, ElementId)> {
    let s = m.substrate();
    for x in s.elements() {
        let reach = reduction_closure(s, x);
        for &y1 in &reach {
            let from_y1 = reduction_closure(s, y1);
            for &y2 in &reach {
                let common = reduction_closure(s, y2).iter().any(|z| from_y1.contains(z));
                if !common {
                    return Err((x, y1, y2));
                }
            }
        }
    }
    Ok(())
}

/// **`PA-Fix`** (L1.2.Ax3) — Fixpoint Stratification: `∀x : ρ_M(x) = x ↔ NF(x)`, i.e.
/// `Fix(ρ_M) = NF(→_ρ)`. Returns the first element where the two disagree, or `Ok`.
pub fn pa_fix(m: &Model) -> Result<(), ElementId> {
    let op = m.operator();
    let s = m.substrate();
    for x in s.elements() {
        if op.is_fixpoint(x) != s.is_normal_form(x) {
            return Err(x);
        }
    }
    Ok(())
}

/// **`PA-NWF`** (L1.2.Ax4) — Non-Well-Foundedness: `∃x ∀n : ρ_M^n(x) ∉ Fix(ρ_M)`, i.e.
/// `∞_M ≠ ∅`. `true` iff the model has a persistent element (false in pure-WF models).
pub fn pa_nwf(m: &Model) -> bool {
    let op = m.operator();
    m.substrate().elements().any(|x| op.canonical_fixpoint(x).is_none())
}

/// **`PA-Prod`** (L1.2.Ax6, rc4 contract form) — Productivity:
/// `∀x : x ∉ Fix(ρ_M) ⟹ Observable(ρ_M(x)) ≠ 0`, where the model's **Observable
/// Contract** supplies `Observable : 𝒰_M → (O_M, 0)` — a *pointed set of observable
/// contents* with `0` the distinguished "no content" value (the two-element instance
/// `O_M = {⊤, ⊥}`, `0 = ⊥`, is the minimal form, recovering the predicate reading).
/// This is the contract data that grounds the derived observation labelling
/// (`Obs-Lab` L1.1.D8): no non-fixpoint is silent (`Obs-Lab-WD` L1.1.T1(iii)).
/// Returns the first non-fixpoint whose projection step emits no content, or `Ok`.
pub fn pa_prod<O: Fn(ElementId) -> u32>(m: &Model, observable: O) -> Result<(), ElementId> {
    let op = m.operator();
    for x in m.substrate().elements() {
        if !op.is_fixpoint(x) && observable(op.project(x)) == 0 {
            return Err(x);
        }
    }
    Ok(())
}

/// **`PA-Bisim`** (L1.3.Ax1) — Bisimulation Congruence: `∀x,y : x ≈ y ⟹ x ≃_M y`, with
/// `≃_M` read **regime-aware** per rc3 (L2.5.D2 / L1.3.Ax1): `CFix`-equality on ↓_M, and
/// persistent orbit equivalence `≃∞` (equal ω-limit class, L3.3.D7) on ∞_M where
/// `PA-WN_top` is absent. Both are the hybrid semantic class `π_sem` (L3.3.D9), so this checks
/// `x ≈ y ⟹ π_sem(x) = π_sem(y)`. Non-vacuous now that `≈` is the labelled bisimulation
/// (L1.1.D6 rc3) that keeps distinct normal forms apart. Returns the first bisimilar pair
/// with distinct semantic class, or `Ok`.
pub fn pa_bisim(m: &Model) -> Result<(), (ElementId, ElementId)> {
    let op = m.operator();
    let s = m.substrate();
    let representative = s.bisimilarity();
    let elements: Vec<ElementId> = s.elements().collect();
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

/// **`PA-Reach`** (L1.3.Ax2, rc4 **meaning form**) — every persistent orbit has a
/// **canonically representable asymptotic destination**: for all `x ∈ ∞_M`,
/// - **(R1)** `ω_≈(x) ≠ ∅` — the destination exists;
/// - **(R2)** `ω_≈(x)` is finite and `ρ_M`-closed — a finite ρ̄_M-cycle of classes;
/// - **(R3)** the orbit is attracted to it — a tail of the class orbit lies in it;
///
/// with `CPer_M(x)` the destination's canonical representative. *How* the destination is
/// reached is not part of the axiom — the mechanisms are realization theorems
/// (`PA-Reach-Fin` L1.3.T2 recurrence, `PA-Reach-Top` L1.3.T3 convergence,
/// `PA-Reach-Decomp` L1.3.T4: never a third). Checked exactly on the finite substrate.
pub fn pa_reach(m: &Model) -> bool {
    let op = m.operator();
    let representative = m.substrate().bisimilarity();
    m.substrate().elements().all(|x| {
        if crate::l2::regime::is_convergent(&op, x) {
            return true;
        }
        let destination = crate::l3::persistent::omega_limit_classes(&op, x); // ω_≈(x)
        // (R1) non-empty; (R2) finite (it is) and ρ_M-closed: each member class steps
        // into the set; (R3) attracting: a tail of the class orbit lies in the set.
        let closed = crate::l3::persistent::omega_limit_set(&op, x)
            .iter()
            .all(|&y| destination.contains(&representative[op.project(y).index()]));
        let mut current = x;
        for _ in 0..m.substrate().universe_len() {
            current = op.project(current);
        }
        let attracted = destination.contains(&representative[current.index()]);
        !destination.is_empty() && closed && attracted
    })
}

/// Witness **`PA-Reach-Fin`** (L1.3.T2) — the **recurrence realization**: where the
/// destination is *visited* (on a finite substrate: every persistent orbit), the ≈-class
/// orbit is eventually periodic — `∃n, p ≥ 1 : ∀j : ρ^{n+j+p}(x) ≈ ρ^{n+j}(x)` —
/// eventual periodicity *derived* (PA-Bisim equivariance: one recurrence in a
/// function-generated class orbit forces the replay); `ω_≈(x)` is exactly the recurrent
/// cycle, entered at depth `n_M(x)` with `CPer_M(x) = ρ^{n_M(x)}(x)` its entry point —
/// the NWF mirror of PA-WN's reach of Fix at `d_M`. Returns the first violating
/// persistent element, or `Ok`.
pub fn certify_pa_reach_fin(m: &Model) -> Result<(), ElementId> {
    let op = m.operator();
    for x in m.substrate().elements() {
        if crate::l2::regime::is_convergent(&op, x) {
            continue;
        }
        // ω_≈(x) = the recurrent cycle's class set, and CPer enters it at n_M.
        let destination = crate::l3::persistent::omega_limit_classes(&op, x);
        let Some(cper) = canonical_persistent_representative(&op, x) else {
            return Err(x); // n_M must be total on the recurrence face
        };
        let representative = m.substrate().bisimilarity();
        if !destination.contains(&representative[cper.index()]) {
            return Err(x); // the entry point's class must lie in the destination
        }
    }
    Ok(())
}

/// Witness **`PA-Reach-Top`** (L1.3.T3) — the **convergence realization** on the
/// topological tier: if the orbit of persistent `x` `𝒯`-converges to `L`, then `L` is a
/// fixpoint (continuity turns "limit of the orbit" into "fixpoint of the operator") —
/// the destination is the singleton class of `L = CFix(x)`, unique by Hausdorff
/// separation (`TopSep-Uniq` L1.2.T1). Returns `Some(true)` when certified at `x`,
/// `Some(false)` if the limit exists but is not a fixpoint, `None` off the
/// `PA-WN_top` sub-class.
pub fn certify_pa_reach_top<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    if !sys.is_persistent(x) {
        return None;
    }
    let limit = sys.topological_limit(x)?;
    Some(sys.is_projection_fixpoint(&limit))
}

/// Witness **`PA-Reach-Decomp`** (L1.3.T4) — every realization decomposes into the two
/// mechanisms: **(i)** the destination `ω_≈(x)` is a *single* finite ρ̄_M-cycle of
/// classes (ρ̄_M maps it onto itself, and it is one orbit-cycle); **(ii)** on the finite
/// substrate the reach face is recurrence — every tail class lies in the cycle
/// (`PA-Reach-Fin`); the convergence and composite faces live on the topological tier.
/// There is no third mechanism. Returns the first violating persistent element, or `Ok`.
pub fn certify_pa_reach_decomp(m: &Model) -> Result<(), ElementId> {
    let op = m.operator();
    let representative = m.substrate().bisimilarity();
    for x in m.substrate().elements() {
        if crate::l2::regime::is_convergent(&op, x) {
            continue;
        }
        let destination = crate::l3::persistent::omega_limit_classes(&op, x);
        let cycle = crate::l3::persistent::omega_limit_set(&op, x);
        // (i) ρ̄_M maps the destination onto itself, through one cycle: stepping every
        // member of the ω-limit set stays in the set and visits every class.
        let mut visited: Vec<ElementId> = Vec::new();
        for &y in &cycle {
            let class = representative[op.project(y).index()];
            if !destination.contains(&class) {
                return Err(x);
            }
            if !visited.contains(&class) {
                visited.push(class);
            }
        }
        visited.sort_by_key(|e| e.0);
        if visited != destination {
            return Err(x); // not a single onto cycle of classes
        }
        // (ii) recurrence face: a tail of the class orbit lies in the destination.
        let mut current = x;
        for _ in 0..m.substrate().universe_len() {
            current = op.project(current);
        }
        if !destination.contains(&representative[current.index()]) {
            return Err(x);
        }
    }
    Ok(())
}

/// **L1.3.D1 (`CPer`)** — the **canonical persistent representative**
/// `CPer_M(x) := ρ_M^{n_M(x)}(x)`: the point on x's orbit where the orbit signature first
/// stabilises (`n-Reach` L3.3.D10). PA-Reach guarantees `n_M(x)` exists, making `CPer_M(x)`
/// the canonical *finite* descriptor of the infinite element x — the observer extraction
/// principle: the object is infinite, but the observable signature is finitary and
/// recursively determined. `None` on `↓_M` (where `CFix` is the canonical form).
pub fn canonical_persistent_representative(
    op: &crate::l2::projection::ProjectionOperator,
    x: crate::l1::substrate::ElementId,
) -> Option<crate::l1::substrate::ElementId> {
    let n = crate::l3::persistent::n_reach(op, x)?;
    let mut current = x;
    for _ in 0..n {
        current = op.project(current);
    }
    Some(current)
}

/// The decidable PA-* axiom profile of a model (`PA-CoInd`, `PA-WN_top`, and the full
/// `PA-Reach` are excluded — see the module docs). `pa_prod` uses the default Observable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AxiomProfile {
    /// `PA-WN` (L1.2.Ax1), global form.
    pub pa_wn: bool,
    /// `PA-Conf` (L1.2.Ax2).
    pub pa_conf: bool,
    /// `PA-Fix` (L1.2.Ax3).
    pub pa_fix: bool,
    /// `PA-NWF` (L1.2.Ax4).
    pub pa_nwf: bool,
    /// `PA-Prod` (L1.2.Ax6) under the default Observable.
    pub pa_prod: bool,
    /// `PA-Bisim` (L1.3.Ax1), convergent part (exact `≃_M`).
    pub pa_bisim: bool,
}

/// Compute the decidable [`AxiomProfile`] of a model.
pub fn axiom_profile(m: &Model) -> AxiomProfile {
    AxiomProfile {
        pa_wn: pa_wn(m).is_ok(),
        pa_conf: pa_conf(m).is_ok(),
        pa_fix: pa_fix(m).is_ok(),
        pa_nwf: pa_nwf(m),
        pa_prod: pa_prod(m, |_| 1).is_ok(), // minimal contract: O_M = {1, 0}, all content
        pa_bisim: pa_bisim(m).is_ok(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn pure_wf_chain_satisfies_the_convergent_axioms() {
        // 0 →_ρ 1, 1 ∈ NF (functional, non-branching).
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let profile = axiom_profile(&m);
        assert!(profile.pa_wn); // PA-WN
        assert!(profile.pa_conf); // PA-Conf (trivial: no branching)
        assert!(profile.pa_fix); // PA-Fix
        assert!(!profile.pa_nwf); // PA-NWF false (pure WF)
        assert!(profile.pa_prod); // PA-Prod (default Observable)
        assert!(profile.pa_bisim); // PA-Bisim (one NF; nothing forced)
    }

    #[test]
    fn branching_confluent_model_satisfies_wn_and_confluence() {
        // Branching →_ρ: 0→1, 0→2, 1→2, 2 ∈ NF. ρ_M strategy ρ(0)=1, ρ(1)=2, ρ(2)=2.
        // 0,1,2 are pairwise non-bisimilar (distinct successor structure), so C2 holds.
        let s = Substrate::new(3, &[(0, 1), (0, 2), (1, 2)], &[(0, 1), (0, 2), (1, 2)]).unwrap();
        let m = Model::new(s, vec![id(1), id(2), id(2)]).unwrap();
        assert!(matches!(pa_wn(&m), Ok(()))); // PA-WN
        assert!(matches!(pa_conf(&m), Ok(()))); // PA-Conf: 0's two paths both reach NF 2
        assert!(matches!(pa_bisim(&m), Ok(()))); // PA-Bisim
    }

    #[test]
    fn c1_c2_valid_model_can_violate_pa_conf() {
        // A *valid* model (C1/C2 hold) that is NOT a CRPT model — it violates an axiom.
        // 0→1, 0→2, with 1 ∈ NF and 2 ∈ NF: two distinct normal forms reachable from 0.
        // ρ_M strategy ρ(0)=1, ρ(1)=1, ρ(2)=2. Construction succeeds (C1/C2 hold):
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(2)]).unwrap();
        // PA-Conf fails: 0 reaches NFs 1 and 2 with no common descendant.
        assert!(matches!(pa_conf(&m), Err((x, _, _)) if x == id(0)));
        // The point: C1/C2 is necessary but NOT sufficient — the PA-* axioms define a CRPT model.
        // (Under rc3's labelled ≈, 1 ≉ 2 — distinct NFs are distinct observables — so this
        // model now *satisfies* PA-Bisim; it fails to be a CRPT model via PA-Conf alone.)
        assert!(matches!(pa_bisim(&m), Ok(())));
    }

    #[test]
    fn pa_reach_full_form_and_cper() {
        // transient 0 → obs-distinguished cycle (1 ⇄ 2): n_M(0) = 1 (the AOI stabilises on
        // entering the cycle), so CPer(0) = ρ(0) = 1 — the canonical finite descriptor of
        // the infinite element. PA-Reach (full form): n_M total on ∞_M.
        let e = [(0, 1), (1, 2), (2, 1)];
        let s = Substrate::with_observation(3, &e, &e, &[5, 10, 11]).unwrap();
        let m = Model::new(s, vec![ElementId(1), ElementId(2), ElementId(1)]).unwrap();
        assert!(pa_reach(&m));
        let op = m.operator();
        assert_eq!(
            canonical_persistent_representative(&op, ElementId(0)),
            Some(ElementId(1))
        );
        // on the cycle the signature is already stable: CPer(1) = 1.
        assert_eq!(
            canonical_persistent_representative(&op, ElementId(1)),
            Some(ElementId(1))
        );
        // n-Reach is the d_M dual: None on ↓_M (where CFix is the canonical form).
        let e2 = [(0, 1)];
        let s2 = Substrate::new(2, &e2, &e2).unwrap();
        let m2 = Model::from_functional_reduction(s2).unwrap();
        assert!(pa_reach(&m2)); // vacuous on pure-WF
        assert_eq!(canonical_persistent_representative(&m2.operator(), ElementId(0)), None);
    }

    #[test]
    fn pa_reach_meaning_form_with_realizations() {
        // mixed model: 0→1 (↓_M); 2⇄3 obs-distinct (∞_M). The destination ω_≈ is the
        // two-class cycle: R1 ✓ R2 (ρ̄-closed cycle) ✓ R3 (attracting) ✓; the recurrence
        // realization (PA-Reach-Fin) and the decomposition (PA-Reach-Decomp) certify.
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Model::new(s, vec![ElementId(1), ElementId(1), ElementId(3), ElementId(2)]).unwrap();
        assert!(pa_reach(&m));
        assert!(matches!(certify_pa_reach_fin(&m), Ok(())));
        assert!(matches!(certify_pa_reach_decomp(&m), Ok(())));
        // the convergence realization (PA-Reach-Top) on the topological tier: the chain's
        // limit ω is a fixpoint — the destination is the singleton class of CFix.
        use crate::l1::topology::{ChainPoint, ConvergentChain};
        assert_eq!(
            certify_pa_reach_top(&ConvergentChain, &ChainPoint::Step(0)),
            Some(true)
        );
        assert_eq!(certify_pa_reach_top(&ConvergentChain, &ChainPoint::Limit), None);
    }

    /// **`PA-Reach-Indep` (L1.3.R2) — the M_Reach countermodel**, symbolic realization:
    /// a persistent orbit visiting pairwise-distinct classes, each exactly once, with a
    /// discrete topology (no 𝒯-accumulation) — ω_≈ = ∅ violates (R1). PA-Reach is
    /// independent of the other eight axioms.
    struct MReach;

    impl crate::l0::projection_system::ProjectionSystem for MReach {
        type Point = u64;

        fn projection(&self, x: &u64) -> u64 {
            x + 1 // s_n →_ρ s_{n+1}: never repeats, never reaches a fixpoint
        }

        fn projection_depth(&self, x: &u64) -> Option<u32> {
            let _ = x;
            None // persistent
        }
    }

    impl crate::l1::topology::TopologicalProjectionSystem for MReach {
        fn topological_limit(&self, x: &u64) -> Option<u64> {
            let _ = x;
            None // discrete topology: no 𝒯-accumulation — no convergence face
        }

        fn observation(&self, x: &u64) -> u32 {
            *x as u32 // pairwise-distinct observables: every class is its own
        }
    }

    #[test]
    fn m_reach_violates_r1_witnessing_independence() {
        use crate::l6::orbit_type::certify_aperiodic_prefix;
        let witness = MReach;
        // no recurrence face: the class orbit is pairwise-distinct at every depth …
        assert!(certify_aperiodic_prefix(&witness, &0, |x: &u64| *x, 128));
        // … and no convergence face: no 𝒯-limit anywhere on the orbit.
        assert_eq!(certify_pa_reach_top(&witness, &0), None);
        // hence ω_≈(s₀) = ∅ — (R1) fails: PA-Reach is not derivable from the rest.
    }
}
