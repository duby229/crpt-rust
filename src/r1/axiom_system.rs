//! # R1.2 — The Axiom System (the aspect-local step axioms)
//!
//! Exact realization of spec section **R1.2** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9). This
//! section's membership criterion: the **aspect-local step axioms** —
//! constraints on a *single* `→_ρ`/`ρ_M` step or its finite iteration. (The
//! aspect-universal *orbit* axioms `PA-Bisim`/`PA-Reach` are R1.3; `PA-WN_top` is R1.7.)
//!
//! - R1.2.Ax1 `PA-WN` (≅) — Weak Normalisation: every element has a terminating
//!   `→_ρ`-path to a normal form ([`pa_wn`]).
//! - R1.2.Ax2 `PA-Conf` (≅) — Confluence (Church–Rosser) of `→_ρ` ([`pa_conf`]).
//! - R1.2.Ax3 `PA-Fix` — Fixpoint Stratification: `Fix(ρ_M) = NF(→_ρ)` ([`pa_fix`]).
//! - R1.2.Ax4 `PA-NWF` (≅) — Non-Well-Foundedness: `∞_M ≠ ∅` ([`pa_nwf`]).
//! - R1.2.Ax5 `PA-CoInd` (≅) — coinduction (Park's lemma): second-order, derivable from
//!   `PA-NWF`; not a finite single-step predicate (no checker — it is a proof principle).
//! - R1.2.Ax6 `PA-Prod` — Productivity: every non-fixpoint's projection step emits
//!   non-`0` observable content, via the Observable Contract `(O_M, 0)` ([`pa_prod`]).
//!
//! These are checked exactly over a finite [`Instance`]: a C1/C2/C3-valid instance can
//! still violate them (they are strictly stronger than the operator conditions).

use crate::r1::reduction_strategy::Instance;
use crate::r1::substrate::{ElementId, Substrate};

/// The `→_ρ*` descendants of `x` (reflexive-transitive closure), ascending.
fn reduction_closure(substrate: &Substrate, x: ElementId) -> Vec<ElementId> {
    let mut seen = vec![false; substrate.universe_len() as usize];
    let mut stack = vec![x];
    seen[x.index()] = true;
    let mut out = Vec::new();
    while let Some(u) = stack.pop() {
        out.push(u);
        for &v in substrate.reduction_successors(u) {
            if !seen[v.index()] {
                seen[v.index()] = true;
                stack.push(v);
            }
        }
    }
    out.sort_by_key(|e| e.0);
    out
}

/// **R1.2.Ax1 (`PA-WN`)** — Weak Normalisation: `∀x ∃n,y : x →_ρⁿ y ∧ NF(y)`. Every
/// element has *some* terminating `→_ρ`-path to a normal form. (Global in pure-WF
/// instances; `Scoped(↓_M)` in native instances, where persistent elements have no
/// terminating path.) Returns the first element with no reachable normal form, or `Ok`.
pub fn pa_wn(instance: &Instance) -> Result<(), ElementId> {
    let substrate = instance.substrate();
    for x in substrate.elements() {
        if !reduction_closure(substrate, x).iter().any(|&y| substrate.is_normal_form(y)) {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.2.Ax2 (`PA-Conf`)** — Confluence (Church–Rosser): `x →_ρ* y₁ ∧ x →_ρ* y₂ ⟹
/// ∃z : y₁ →_ρ* z ∧ y₂ →_ρ* z`. Returns the first diverging triple `(x, y₁, y₂)` with no
/// common descendant, or `Ok`.
pub fn pa_conf(instance: &Instance) -> Result<(), (ElementId, ElementId, ElementId)> {
    let substrate = instance.substrate();
    for x in substrate.elements() {
        let reach = reduction_closure(substrate, x);
        for &y1 in &reach {
            let from_y1 = reduction_closure(substrate, y1);
            for &y2 in &reach {
                let common = reduction_closure(substrate, y2).iter().any(|z| from_y1.contains(z));
                if !common {
                    return Err((x, y1, y2));
                }
            }
        }
    }
    Ok(())
}

/// **R1.2.Ax3 (`PA-Fix`)** — Fixpoint Stratification: `∀x : ρ_M(x) = x ↔ NF(x)`, i.e.
/// `Fix(ρ_M) = NF(→_ρ)`. Returns the first element where the two disagree, or `Ok`.
pub fn pa_fix(instance: &Instance) -> Result<(), ElementId> {
    let op = instance.operator();
    let substrate = instance.substrate();
    for x in substrate.elements() {
        if op.is_fixpoint(x) != substrate.is_normal_form(x) {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.2.Ax4 (`PA-NWF`)** — Non-Well-Foundedness: `∃x ∀n : ρ_M^n(x) ∉ Fix(ρ_M)`, i.e.
/// `∞_M ≠ ∅`. `true` iff the instance has a persistent element (false in pure-WF instances).
pub fn pa_nwf(instance: &Instance) -> bool {
    let op = instance.operator();
    instance.substrate().elements().any(|x| op.canonical_fixpoint(x).is_none())
}

/// **R1.2.Ax6 (`PA-Prod`)** — Productivity: `∀x : x ∉ Fix(ρ_M) ⟹ Observable(ρ_M(x)) ≠ 0`,
/// where the instance's **Observable Contract** supplies `Observable : 𝒰_M → (O_M, 0)` —
/// a *pointed set of observable contents* with `0` the distinguished "no content" value
/// (the two-element instance `O_M = {⊤, ⊥}`, `0 = ⊥`, is the minimal form, recovering the
/// predicate reading). This contract grounds the derived observation labelling
/// (`Obs-Lab` R1.1.D8): no non-fixpoint is silent (`Obs-Lab-WD` R1.1.T1(iii)). Returns the
/// first non-fixpoint whose projection step emits no content, or `Ok`.
pub fn pa_prod<O: Fn(ElementId) -> u32>(instance: &Instance, observable: O) -> Result<(), ElementId> {
    let op = instance.operator();
    for x in instance.substrate().elements() {
        if !op.is_fixpoint(x) && observable(op.project(x)) == 0 {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.2.R2 (`Ax-NS`)** — the **PA-\* namespace discipline**: exactly **nine** projection
/// axioms reserve the `PA-` prefix; nothing else may begin with `PA-`. WF-side
/// canonicalization (`WF-Canon`) is a *theorem* and existential richness (`LA-Rich`) an
/// *instance-local axiom*, so neither occupies a PA-* slot.
pub const PA_AXIOMS: [&str; 9] =
    ["PA-WN", "PA-Conf", "PA-Fix", "PA-NWF", "PA-CoInd", "PA-Prod", "PA-WN_top", "PA-Bisim", "PA-Reach"];

/// Witness **R1.2.R2 (`Ax-NS`)** — the namespace holds exactly nine axioms, with no
/// duplicates, and the two deliberately-excluded constructs (`WF-Canon`, `LA-Rich`) are
/// **not** in it. Returns `true` when the discipline is intact.
pub fn certify_pa_namespace() -> bool {
    let mut sorted = PA_AXIOMS.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    sorted.len() == 9 && !PA_AXIOMS.contains(&"WF-Canon") && !PA_AXIOMS.contains(&"LA-Rich")
}

/// Witness **R1.2.R1 (`WN-vs-SN`)** — `PA-WN` asserts the *existence* of a terminating
/// `→_ρ`-path (weak normalisation), **not** strong normalisation (that *all* `→_ρ`-paths
/// terminate). Aspect membership and `d_M` are defined via the deterministic `ρ_M`-orbit, not
/// over all `→_σ`-branches. Realized as: `PA-WN` is decided on the `ρ_M`-orbit — a convergent
/// element passes even when its substrate has other non-terminating branches. Returns `true`
/// when the orbit-based `PA-WN` certifies the given `x` (its `ρ_M`-orbit reaches a normal form).
pub fn wn_is_orbit_existence(instance: &Instance, x: ElementId) -> bool {
    instance.operator().canonical_fixpoint(x).is_some()
}

/// Witness **R1.2.R4 (`Prod-SingleStep`)** — the **single-step** formulation of `PA-Prod` is
/// the canonical global statement: on `↓_M \ Fix(ρ_M)` the reduction terminates at normal
/// forms (`Fix=NF` R1.8.T2), so no longer `→_ρ`-path exists — the one-step emission already
/// covers the whole convergent orbit. (`R1.2.R3` `Obs-Contract`: `OC-1` makes `PA-Prod`
/// non-trivial one step from a fixpoint, `OC-2` ties `Observable` to the `PV` component —
/// both carried by [`pa_prod`]'s contract argument.) Returns the first convergent non-fixpoint
/// whose single-step emission is silent (none — termination makes single-step canonical), or
/// `Ok`.
pub fn certify_prod_single_step<O: Fn(ElementId) -> u32>(
    instance: &Instance,
    observable: O,
) -> Result<(), ElementId> {
    let op = instance.operator();
    for x in instance.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() && !op.is_fixpoint(x) && observable(op.project(x)) == 0 {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_axioms_on_a_pure_wf_instance() {
        // 0→1, 1→1 (NF 1) ; 2→3, 3→3 (NF 3): WN holds, confluent, Fix=NF, no ∞_M.
        let e = [(0, 1), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert!(matches!(pa_wn(&m), Ok(())));
        assert!(matches!(pa_conf(&m), Ok(())));
        assert!(matches!(pa_fix(&m), Ok(())));
        assert!(!pa_nwf(&m)); // pure-WF: no persistent element
        assert!(matches!(pa_prod(&m, |_| 1), Ok(()))); // minimal contract: all content non-0
        // Ax-NS: the PA-* namespace holds exactly the nine axioms.
        assert!(certify_pa_namespace());
        assert_eq!(PA_AXIOMS.len(), 9);
        // WN-vs-SN: PA-WN is orbit-existence — the convergent 0 passes.
        assert!(wn_is_orbit_existence(&m, ElementId(0)));
        // Prod-SingleStep: single-step productivity covers the convergent orbit.
        assert!(matches!(certify_prod_single_step(&m, |_| 1), Ok(())));
    }

    #[test]
    fn pa_nwf_holds_with_a_persistent_element() {
        // 0⇄1 cycle (∞_M) ; 2→3 (↓_M). PA-NWF ⊤; PA-WN fails on the cycle.
        let e = [(0, 1), (1, 0), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert!(pa_nwf(&m));
        assert_eq!(pa_wn(&m), Err(ElementId(0))); // 0 has no terminating →_ρ path
    }

    #[test]
    fn pa_fix_catches_a_non_normal_self_loop() {
        // 0→0 self-loop: 0 is a ρ_M-fixpoint but NOT a normal form ⇒ PA-Fix violated.
        let loop_e = [(0, 0)];
        let m = Instance::from_functional_reduction(Substrate::new(1, &loop_e, &loop_e).unwrap()).unwrap();
        assert_eq!(pa_fix(&m), Err(ElementId(0)));
    }
}
