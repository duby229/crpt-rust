//! # L1.5 — Model Axiom Profiles (the PA-* scope system)
//!
//! Exact realization of spec section **L1.5** (`CRPT_OMEGA_TOWER_L1.md`, v1.0.0-rc4):
//!
//! - L1.5.D1 `PA-Scope` — each PA-* axiom applies to a model with a four-valued **scope**:
//!   `Global` (holds for all of 𝒰_M), `Scoped(S)` (holds precisely on a definable subset
//!   `S ⊊ 𝒰_M`), `Vacuous` (antecedent never triggered — no constraint, no tension), or
//!   `Fails` (actively false).
//! - L1.5.D2 `LA_M` — the model-local axiom schema: the extension point for
//!   domain-specific axiomatizations ([`LocalAxiom`], [`local_axioms_hold`]).
//! - L1.5.D5 `SC-Orb` + L1.5.T2 `Scope-Suf` — scoped (ρ_M-orbit) confluence: strictly
//!   weaker than PA-Conf yet sufficient for the L2–L8 results ([`sc_orb`]).
//! - L1.5.R1 `Scope-Status` / L1.5.R2 `Conv-Form` — `Scoped(S)` is **not** a weakening of
//!   `Global` but a precise falsifiable statement; and the `Vacuous` vs `Fails` distinction
//!   is mathematically significant (a `Vacuous` axiom adds nothing; a `Fails` axiom is false).
//!
//! This refines the boolean [`crate::l1::axioms::AxiomProfile`] / [`crate::l5::conformance`]
//! verdict into the spec's scope declarations — e.g. `PA-WN` is `Global` on a pure-WF
//! model but `Scoped(↓_M)` on a native one; `PA-NWF` is `Vacuous` on pure-WF; `PA-WN_top`
//! is `Vacuous` on pure-WF but `Fails` on genuine persistence (discrete topology).

use crate::l1::axioms::{pa_bisim, pa_conf, pa_fix};
use crate::l2::projection::Model;

/// **L1.5.D1 (`PA-Scope`)** — a definable subset of 𝒰_M over which an axiom holds, when its
/// scope is `Scoped`. (Named scopes the spec uses; the engine identifies the subset.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeSet {
    /// `↓_M` — the convergent regime.
    ConvergentRegime,
    /// `∞_M` — the persistent regime.
    PersistentRegime,
    /// the `ρ_M`-orbits (PA-Conf's orbit-level scope, L1.5.R1): each deterministic orbit
    /// is confluent even when →_ρ is not globally confluent.
    ReductionOrbits,
}

/// **L1.5.D1 (`PA-Scope`)** — the four-valued scope of a PA-* axiom in a model. `==`
/// compares the computed scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    /// Holds for all `x ∈ 𝒰_M`.
    Global,
    /// Holds precisely on the definable subset `S ⊊ 𝒰_M`.
    Scoped(ScopeSet),
    /// The antecedent is never triggered — the axiom holds with no constraint (≠ `Fails`).
    Vacuous,
    /// Actively false in the model.
    Fails,
}

/// **L1.5.D1 (`PA-Scope`) / L1.5.D3 (`PA-Profile`)** — the scope declaration of each PA-* axiom for a model (the model axiom profile object).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AxiomScopeProfile {
    /// `PA-WN` (L1.2.Ax1): `Global` (pure-WF) / `Scoped(↓_M)` (native) / `Fails` (pure-NWF).
    pub pa_wn: Scope,
    /// `PA-Conf` (L1.2.Ax2): `Global` (confluent) / `Scoped(ρ_M-orbits)` (orbit-confluent only).
    pub pa_conf: Scope,
    /// `PA-Fix` (L1.2.Ax3): `Global` / `Fails`.
    pub pa_fix: Scope,
    /// `PA-NWF` (L1.2.Ax4): `Global` (`∞_M ≠ ∅`) / `Vacuous` (pure-WF).
    pub pa_nwf: Scope,
    /// `PA-CoInd` (L1.2.Ax5): `Global` (the finite coinduction schema, `FOL-Fin`).
    pub pa_coind: Scope,
    /// `PA-Prod` (L1.2.Ax6, default Observable): `Global` / `Vacuous` (all fixpoints).
    pub pa_prod: Scope,
    /// `PA-WN_top` (L1.2.Ax7, discrete topology): `Vacuous` (pure-WF) / `Fails` (persistence).
    pub pa_wn_top: Scope,
    /// `PA-Bisim` (L1.3.Ax1): `Global` / `Fails`.
    pub pa_bisim: Scope,
    /// `PA-Reach` (L1.3.Ax2, reachability skeleton): `Vacuous` (pure-WF) / `Global` (pure-NWF)
    /// / `Scoped(∞_M)` (mixed). Full signature-stabilization awaits `sig_M-NM` (L3.1.D5).
    pub pa_reach: Scope,
}

/// **L1.5.D1 (`PA-Scope`)** — compute a model's PA-* scope profile.
pub fn axiom_scope_profile(m: &Model) -> AxiomScopeProfile {
    let op = m.operator();
    let n = m.substrate().universe_len();
    let convergent = m.substrate().elements().filter(|&x| op.canonical_fixpoint(x).is_some()).count() as u32;
    let persistent = n - convergent;
    let has_non_fixpoint = m.substrate().elements().any(|x| !op.is_fixpoint(x));

    // PA-WN holds exactly on ↓_M (every convergent element reaches its NF).
    let pa_wn = if convergent == n {
        Scope::Global
    } else if convergent == 0 {
        Scope::Fails
    } else {
        Scope::Scoped(ScopeSet::ConvergentRegime)
    };

    // PA-Conf: globally confluent ⇒ Global; else the deterministic ρ_M-orbits are still
    // confluent (single path each) ⇒ Scoped(ρ_M-orbits).
    let pa_conf = if pa_conf(m).is_ok() {
        Scope::Global
    } else {
        Scope::Scoped(ScopeSet::ReductionOrbits)
    };

    let pa_fix = if pa_fix(m).is_ok() { Scope::Global } else { Scope::Fails };

    // PA-NWF (∞_M ≠ ∅): Global if some persistent element exists, else Vacuous (pure-WF).
    let pa_nwf = if persistent > 0 { Scope::Global } else { Scope::Vacuous };

    let pa_prod = if has_non_fixpoint { Scope::Global } else { Scope::Vacuous };

    // PA-WN_top (discrete topology): a discrete sequence converges iff eventually constant,
    // so no ∞_M element has a limit. Vacuous if ∞_M = ∅; Fails on genuine persistence.
    let pa_wn_top = if persistent == 0 { Scope::Vacuous } else { Scope::Fails };

    let pa_bisim = if pa_bisim(m).is_ok() { Scope::Global } else { Scope::Fails };

    // PA-Reach (skeleton) is about ∞_M only.
    let pa_reach = if persistent == 0 {
        Scope::Vacuous
    } else if persistent == n {
        Scope::Global
    } else {
        Scope::Scoped(ScopeSet::PersistentRegime)
    };

    AxiomScopeProfile {
        pa_wn,
        pa_conf,
        pa_fix,
        pa_nwf,
        pa_coind: Scope::Global, // finite coinduction schema (FOL-Fin)
        pa_prod,
        pa_wn_top,
        pa_bisim,
        pa_reach,
    }
}


/// **L1.5.D2 (`LA_M`)** — a model-local axiom: a named sentence over the extended
/// signature `Σ_M = (𝒰_M, →_ρ, →_σ, ρ_M, …)` that holds in M but is not a consequence of
/// the nine PA-* axioms — the extension point for domain-specific structure
/// (non-deterministic choice operators, context-dependence, observable-specific
/// predicates). `LA_M = ∅` is the standard case for the foundational models, which is
/// exactly why Φ_LA (L5.2.D1) is vacuous there.
pub struct LocalAxiom {
    /// The axiom's name (`LA_M^i`).
    pub name: &'static str,
    /// The sentence, as a decidable predicate over the model.
    pub sentence: fn(&Model) -> bool,
}

/// **L1.5.D2 (`LA_M`)** — check the declared schema `LA_M = {LA_M^1, LA_M^2, …}` against
/// M. Returns the name of the first failing local axiom, or `Ok` (trivially `Ok` for the
/// standard `LA_M = ∅`).
pub fn local_axioms_hold(m: &Model, la_m: &[LocalAxiom]) -> Result<(), &'static str> {
    for axiom in la_m {
        if !(axiom.sentence)(m) {
            return Err(axiom.name);
        }
    }
    Ok(())
}

/// **L1.5.D5 (`SC-Orb`)** — `Scoped(ρ_M-orbits)`: for every `x`, the ρ_M-orbit meets
/// `NF(→_ρ)` in **at most one** element —
/// `∀x ∀n,m : ρ_M^n(x) ∈ NF ∧ ρ_M^m(x) ∈ NF ⟹ ρ_M^n(x) = ρ_M^m(x)`. Strictly weaker
/// than PA-Conf (L1.2.Ax2), yet sufficient for every L2–L8 theorem that cites it
/// (`Scope-Suf` L1.5.T2): CFix uniqueness needs only orbit-level confluence. Returns the
/// first element whose orbit reaches two distinct normal forms, or `Ok`.
pub fn sc_orb(m: &Model) -> Result<(), crate::l1::substrate::ElementId> {
    let op = m.operator();
    let s = m.substrate();
    for x in s.elements() {
        // walk the orbit to its cycle, collecting the normal forms it meets.
        let mut seen = vec![false; s.universe_len() as usize];
        let mut normal_form: Option<crate::l1::substrate::ElementId> = None;
        let mut current = x;
        while !seen[current.index()] {
            seen[current.index()] = true;
            if s.is_normal_form(current) {
                match normal_form {
                    Some(first) if first != current => return Err(x),
                    _ => normal_form = Some(current),
                }
            }
            current = op.project(current);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::{ElementId, Substrate};

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn pure_wf_profile() {
        // 0→1, 1 ∈ NF: pure WF. PA-WN Global; PA-NWF/PA-WN_top Vacuous.
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let p = axiom_scope_profile(&m);
        assert_eq!(p.pa_wn, Scope::Global);
        assert_eq!(p.pa_nwf, Scope::Vacuous);
        assert_eq!(p.pa_wn_top, Scope::Vacuous);
        assert_eq!(p.pa_fix, Scope::Global);
        assert_eq!(p.pa_bisim, Scope::Global);
        assert_eq!(p.pa_reach, Scope::Vacuous);
    }

    #[test]
    fn native_mixed_profile() {
        // 0→1 (↓_M) and 2⇄3 distinct obs (∞_M): native Mixed.
        // PA-WN Scoped(↓_M); PA-NWF Global; PA-WN_top Fails; PA-Reach Scoped(∞_M).
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let p = axiom_scope_profile(&m);
        assert_eq!(p.pa_wn, Scope::Scoped(ScopeSet::ConvergentRegime));
        assert_eq!(p.pa_nwf, Scope::Global);
        assert_eq!(p.pa_wn_top, Scope::Fails);
        assert_eq!(p.pa_reach, Scope::Scoped(ScopeSet::PersistentRegime));
        assert_eq!(p.pa_bisim, Scope::Global);
    }

    #[test]
    fn non_confluent_is_orbit_scoped() {
        // 0→1, 0→2 (both NF): →_ρ not globally confluent, but ρ_M-orbits are.
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(2)]).unwrap();
        assert_eq!(
            axiom_scope_profile(&m).pa_conf,
            Scope::Scoped(ScopeSet::ReductionOrbits)
        );
    }

    #[test]
    fn la_m_schema_and_empty_default() {
        let e = [(0, 1)];
        let m = Model::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        // LA_M = ∅ — the standard case: holds trivially (and Φ_LA is vacuous).
        assert!(matches!(local_axioms_hold(&m, &[]), Ok(())));
        // a model-specific sentence over Σ_M: "the model has a normal form".
        fn has_normal_form(m: &Model) -> bool {
            m.substrate().elements().any(|x| m.substrate().is_normal_form(x))
        }
        fn is_pure_nwf(m: &Model) -> bool {
            m.substrate().elements().all(|x| !m.substrate().is_normal_form(x))
        }
        let la_m = [
            LocalAxiom { name: "LA_M^1: has a normal form", sentence: has_normal_form },
            LocalAxiom { name: "LA_M^2: pure NWF", sentence: is_pure_nwf },
        ];
        // the first holds, the second fails — reported by name.
        assert_eq!(local_axioms_hold(&m, &la_m), Err("LA_M^2: pure NWF"));
    }

    #[test]
    fn sc_orb_holds_where_pa_conf_fails() {
        // Scope-Suf (L1.5.T2) realized: branching →_ρ with TWO distinct normal forms
        // (0→1, 0→2; NF 1, NF 2) breaks global confluence — but the ρ_M-ORBIT (the
        // strategy: ρ(0)=1) meets NF exactly once. SC-Orb ⊤ while PA-Conf ⊥.
        let e = [(0, 1), (0, 2)];
        let s = Substrate::new(3, &e, &e).unwrap();
        let m = Model::new(s, vec![ElementId(1), ElementId(1), ElementId(2)]).unwrap();
        assert!(crate::l1::axioms::pa_conf(&m).is_err()); // global confluence fails
        assert!(matches!(sc_orb(&m), Ok(())));            // orbit-scoped confluence holds
    }
}
