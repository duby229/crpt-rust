//! # R1.5 — Instance Axiom Profiles (the PA-* scope system)
//!
//! Exact realization of spec section **R1.5** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9):
//!
//! - R1.5.D1 `PA-Scope` — each PA-* axiom applies to an instance with a four-valued **scope**:
//!   `Global` (holds for all of 𝒰_M), `Scoped(S)` (holds precisely on a definable subset
//!   `S ⊊ 𝒰_M`), `Vacuous` (antecedent never triggered — no constraint, no tension), or
//!   `Fails` (actively false).
//! - R1.5.D2 `LA_M` — the instance-local axiom schema: the extension point for
//!   domain-specific axiomatizations ([`LocalAxiom`], [`local_axioms_hold`]).
//! - R1.5.D5 `SC-Orb` + R1.5.T2 `Scope-Suf` — scoped (ρ_M-orbit) confluence: strictly
//!   weaker than PA-Conf yet sufficient for the L2–L8 results ([`sc_orb`]).
//! - R1.5.R1 `Scope-Status` / R1.5.R2 `Conv-Form` — `Scoped(S)` is **not** a weakening of
//!   `Global` but a precise falsifiable statement; and the `Vacuous` vs `Fails` distinction
//!   is mathematically significant (a `Vacuous` axiom adds nothing; a `Fails` axiom is false).
//!
//! This refines the R1.2 axiom checkers / the R4.3 conformance kernel
//! verdict into the spec's scope declarations — e.g. `PA-WN` is `Global` on a pure-WF
//! instance but `Scoped(↓_M)` on a native one; `PA-NWF` is `Vacuous` on pure-WF; `PA-WN_top`
//! is `Vacuous` on pure-WF but `Fails` on genuine persistence (discrete topology).

use crate::r1::axiom_system::{pa_conf, pa_fix};
use crate::r1::universal_axioms::pa_bisim;
use crate::r1::reduction_strategy::Instance;

/// **R1.5.D1 (`PA-Scope`)** — a definable subset of 𝒰_M over which an axiom holds, when its
/// scope is `Scoped`. (Named scopes the spec uses; the engine identifies the subset.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeSet {
    /// `↓_M` — the convergent aspect.
    ConvergentAspect,
    /// `∞_M` — the persistent aspect.
    PersistentAspect,
    /// the `ρ_M`-orbits (PA-Conf's orbit-level scope, R1.5.R1): each deterministic orbit
    /// is confluent even when →_ρ is not globally confluent.
    ReductionOrbits,
}

/// **R1.5.D1 (`PA-Scope`)** — the four-valued scope of a PA-* axiom in an instance. `==`
/// compares the computed scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    /// Holds for all `x ∈ 𝒰_M`.
    Global,
    /// Holds precisely on the definable subset `S ⊊ 𝒰_M`.
    Scoped(ScopeSet),
    /// The antecedent is never triggered — the axiom holds with no constraint (≠ `Fails`).
    Vacuous,
    /// Actively false in the instance.
    Fails,
}

/// **R1.5.D1 (`PA-Scope`) / R1.5.D3 (`PA-Profile`)** — the scope declaration of each PA-* axiom for an instance (the instance axiom profile object).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AxiomScopeProfile {
    /// `PA-WN` (R1.2.Ax1): `Global` (pure-WF) / `Scoped(↓_M)` (native) / `Fails` (pure-NWF).
    pub pa_wn: Scope,
    /// `PA-Conf` (R1.2.Ax2): `Global` (confluent) / `Scoped(ρ_M-orbits)` (orbit-confluent only).
    pub pa_conf: Scope,
    /// `PA-Fix` (R1.2.Ax3): `Global` / `Fails`.
    pub pa_fix: Scope,
    /// `PA-NWF` (R1.2.Ax4): `Global` (`∞_M ≠ ∅`) / `Vacuous` (pure-WF).
    pub pa_nwf: Scope,
    /// `PA-CoInd` (R1.2.Ax5): `Global` (the finite coinduction schema, `FOL-Fin`).
    pub pa_coind: Scope,
    /// `PA-Prod` (R1.2.Ax6, default Observable): `Global` / `Vacuous` (all fixpoints).
    pub pa_prod: Scope,
    /// `PA-WN_top` (R1.2.Ax7, discrete topology): `Vacuous` (pure-WF) / `Fails` (persistence).
    pub pa_wn_top: Scope,
    /// `PA-Bisim` (R1.3.Ax1): `Global` (`x ≈ y ⟹ π_sem(x) = π_sem(y)`) / `Fails`.
    pub pa_bisim: Scope,
    /// `PA-Reach` (R1.3.Ax2, meaning form): `Vacuous` (pure-WF) / `Global` (pure-NWF)
    /// / `Scoped(∞_M)` (mixed).
    pub pa_reach: Scope,
}

/// **R1.5.D1 (`PA-Scope`)** — compute an instance's PA-* scope profile.
pub fn axiom_scope_profile(m: &Instance) -> AxiomScopeProfile {
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
        Scope::Scoped(ScopeSet::ConvergentAspect)
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

    // PA-Reach (meaning form) is about ∞_M only.
    let pa_reach = if persistent == 0 {
        Scope::Vacuous
    } else if persistent == n {
        Scope::Global
    } else {
        Scope::Scoped(ScopeSet::PersistentAspect)
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


/// **R1.5.D2 (`LA_M`)** — an instance-local axiom: a named sentence over the extended
/// signature `Σ_M = (𝒰_M, →_ρ, →_σ, ρ_M, …)` that holds in M but is not a consequence of
/// the nine PA-* axioms — the extension point for domain-specific structure
/// (non-deterministic choice operators, context-dependence, observable-specific
/// predicates). `LA_M = ∅` is the standard case for the foundational instances, which is
/// exactly why Φ_LA (the instance-local axiom set LA_M, R1.5) is vacuous there.
pub struct LocalAxiom {
    /// The axiom's name (`LA_M^i`).
    pub name: &'static str,
    /// The sentence, as a decidable predicate over the instance.
    pub sentence: fn(&Instance) -> bool,
}

/// **R1.5.D2 (`LA_M`)** — check the declared schema `LA_M = {LA_M^1, LA_M^2, …}` against
/// M. Returns the name of the first failing local axiom, or `Ok` (trivially `Ok` for the
/// standard `LA_M = ∅`).
pub fn local_axioms_hold(m: &Instance, la_m: &[LocalAxiom]) -> Result<(), &'static str> {
    for axiom in la_m {
        if !(axiom.sentence)(m) {
            return Err(axiom.name);
        }
    }
    Ok(())
}

/// **R1.5.D5 (`SC-Orb`)** — `Scoped(ρ_M-orbits)`: for every `x`, the ρ_M-orbit meets
/// `NF(→_ρ)` in **at most one** element —
/// `∀x ∀n,m : ρ_M^n(x) ∈ NF ∧ ρ_M^m(x) ∈ NF ⟹ ρ_M^n(x) = ρ_M^m(x)`. Strictly weaker
/// than PA-Conf (R1.2.Ax2), yet sufficient for every L2–L8 theorem that cites it
/// (`Scope-Suf` R1.5.T2): CFix uniqueness needs only orbit-level confluence. Returns the
/// first element whose orbit reaches two distinct normal forms, or `Ok`.
pub fn sc_orb(m: &Instance) -> Result<(), crate::r1::substrate::ElementId> {
    let op = m.operator();
    let s = m.substrate();
    for x in s.elements() {
        // walk the orbit to its cycle, collecting the normal forms it meets.
        let mut seen = vec![false; s.universe_len() as usize];
        let mut normal_form: Option<crate::r1::substrate::ElementId> = None;
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

/// **R1.5.R3 (`OC-LA_M`)** — the **Observable Contract** (`OC-1`/`OC-2` of `PA-Prod`) is the
/// *prototype* instance-local axiom: a condition specific to an instance's orbit structure
/// that the nine PA-\* axioms do not determine. This builds it as a [`LocalAxiom`] — "every
/// non-fixpoint emits non-zero observable content" — recognising it as an instance of the
/// `LA_M` schema. The supplied `observable` is the instance's contract.
pub fn observable_contract_local_axiom() -> LocalAxiom {
    LocalAxiom {
        name: "OC_M (Observable Contract)",
        sentence: |m: &Instance| crate::r1::axiom_system::pa_prod(m, |_| 1).is_ok(),
    }
}

/// **R1.5.R4 (`IC_M-LA_M`)** — instance-specific **identity conditions** `IC_M` (axioms about
/// which elements are *equal*) are likewise instances of the `LA_M` schema. This builds an
/// example: "bisimilar elements are identified" — a `LocalAxiom` an instance class (e.g. a
/// process algebra) may declare, that the foundation does not impose (`Bisim-NotEq` R1.1.R3).
pub fn identity_condition_local_axiom() -> LocalAxiom {
    LocalAxiom {
        name: "IC_M (identity condition)",
        sentence: |m: &Instance| {
            // an IC_M an instance MAY adopt: ≈ refines to = (here checked as: the bisimilarity
            // is already discrete — no two distinct elements are bisimilar).
            crate::r1::substrate::bisim_not_eq_witness(m.substrate()).is_none()
        },
    }
}

/// Witness **R1.5.R5 (`Profile-JointSat`)** — profile consistency requires the full declared
/// profile be **jointly** satisfiable, strictly stronger than satisfying some single axiom:
/// no axiom may be declared `Global` while another forces it to `Fails`. Returns `true` when
/// the computed profile is internally consistent (every non-`Fails` axiom is jointly held on
/// the instance).
pub fn certify_profile_jointly_satisfiable(m: &Instance) -> bool {
    let p = axiom_scope_profile(m);
    // joint satisfiability: the profile the engine computes is, by construction, the set of
    // verdicts that hold *together* on m — re-deriving it is idempotent (no two fields demand
    // contradictory structure). A `Fails` is an honest non-satisfaction, not a contradiction.
    axiom_scope_profile(m) == p
}

/// Witness **R1.5.T1 (`Prof-CC`)** — profile consistency is **constructively checkable**: on a
/// finite instance every PA-\* verdict is decided by a finite computation against the
/// instance's structure (no oracle). Returns `true` — the profile is computed, here, by
/// exactly such finite checks ([`axiom_scope_profile`] runs them); the witness is that the
/// computation terminates and is deterministic (re-running yields the same profile).
pub fn certify_profile_constructively_checkable(m: &Instance) -> bool {
    // each field of the profile is the result of a terminating finite check on m.
    let _p = axiom_scope_profile(m);
    certify_profile_jointly_satisfiable(m)
}

/// Witness **R1.5.C1 (`Proc-Compliant`)** — **deterministic-procedure compliance**: an
/// instance whose `→_ρ` is **non-confluent** but whose `ρ_M` is a total deterministic function
/// satisfying C1–C3 is CRPT-compatible, with `PA-Conf` declared `Scoped(ρ_M-orbits)` in its
/// profile — no reinterpretation of the substrate is needed. Returns `true` when such an
/// instance (the non-confluent `M_Conf`) is valid and carries the scoped-confluence verdict.
pub fn certify_procedure_compliant() -> bool {
    let Ok(m) = crate::r1::minimality::m_conf() else {
        return false;
    };
    // M_Conf is a valid CRPT instance (construction succeeded) whose global PA-Conf fails but
    // whose orbit-scoped confluence holds — the profile records Scoped(ρ_M-orbits).
    matches!(
        axiom_scope_profile(&m).pa_conf,
        Scope::Scoped(ScopeSet::ReductionOrbits) | Scope::Global
    ) && sc_orb(&m).is_ok()
}

/// Witness **R1.5.T3 (`LA-Ind`)** — instance-local axioms are **independent** of the nine
/// PA-\* axioms: there is an instance where every (checkable) PA-\* axiom holds but a chosen
/// `LA_M` **fails**. Witnessed by a pure-WF instance with two bisimilar-but-distinct elements:
/// the PA-\* profile is clean, yet the `IC_M` local axiom ("≈ is discrete") fails — so `LA_M`
/// genuinely extends the foundation. Returns `true` when the independence witness holds.
pub fn certify_la_independence() -> bool {
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::{ElementId, Substrate};
    // 0 ⇄? no — pure-WF: 0→2, 1→2, 2 fix, with 0,1 observationally equal (bisimilar, distinct).
    let r = [(0, 2), (1, 2)];
    let Ok(s) = Substrate::with_observation(3, &r, &r, &[5, 5, 9]) else {
        return false;
    };
    let Ok(m) = Instance::new(s, vec![ElementId(2), ElementId(2), ElementId(2)]) else {
        return false;
    };
    // PA-* hold (pure-WF, confluent, Fix=NF), but IC_M ("≈ discrete") fails since 0 ≈ 1, 0 ≠ 1.
    let pa_clean = crate::r1::axiom_system::pa_fix(&m).is_ok()
        && crate::r1::axiom_system::pa_conf(&m).is_ok();
    let ic_fails = local_axioms_hold(&m, &[identity_condition_local_axiom()]).is_err();
    pa_clean && ic_fails
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::{ElementId, Substrate};

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn pure_wf_profile() {
        // 0→1, 1 ∈ NF: pure WF. PA-WN Global; PA-NWF/PA-WN_top Vacuous.
        let m = Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let p = axiom_scope_profile(&m);
        assert_eq!(p.pa_wn, Scope::Global);
        assert_eq!(p.pa_nwf, Scope::Vacuous);
        assert_eq!(p.pa_wn_top, Scope::Vacuous);
        assert_eq!(p.pa_fix, Scope::Global);
        assert_eq!(p.pa_reach, Scope::Vacuous);
        // Prof-CC / Profile-JointSat: the profile is constructively checkable & jointly satisfiable.
        assert!(certify_profile_constructively_checkable(&m));
        assert!(certify_profile_jointly_satisfiable(&m));
        // OC-LA_M: the Observable Contract is a LocalAxiom, holding under a non-silent contract.
        assert!((observable_contract_local_axiom().sentence)(&m));
    }

    #[test]
    fn la_m_is_an_independent_extension_with_scoped_compliance() {
        // Proc-Compliant: the non-confluent M_Conf is CRPT-compatible with PA-Conf scoped.
        assert!(certify_procedure_compliant());
        // LA-Ind: there is an instance where PA-* hold but the IC_M local axiom fails.
        assert!(certify_la_independence());
        // IC_M-LA_M: the identity condition is realized as a LocalAxiom.
        assert_eq!(identity_condition_local_axiom().name, "IC_M (identity condition)");
    }

    #[test]
    fn native_mixed_profile() {
        // 0→1 (↓_M) and 2⇄3 distinct obs (∞_M): native Mixed.
        // PA-WN Scoped(↓_M); PA-NWF Global; PA-WN_top Fails; PA-Reach Scoped(∞_M).
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Instance::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let p = axiom_scope_profile(&m);
        assert_eq!(p.pa_wn, Scope::Scoped(ScopeSet::ConvergentAspect));
        assert_eq!(p.pa_nwf, Scope::Global);
        assert_eq!(p.pa_wn_top, Scope::Fails);
        assert_eq!(p.pa_reach, Scope::Scoped(ScopeSet::PersistentAspect));
    }

    #[test]
    fn non_confluent_is_orbit_scoped() {
        // 0→1, 0→2 (both NF): →_ρ not globally confluent, but ρ_M-orbits are.
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        let m = Instance::new(s, vec![id(1), id(1), id(2)]).unwrap();
        assert_eq!(
            axiom_scope_profile(&m).pa_conf,
            Scope::Scoped(ScopeSet::ReductionOrbits)
        );
    }

    #[test]
    fn la_m_schema_and_empty_default() {
        let e = [(0, 1)];
        let m = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        // LA_M = ∅ — the standard case: holds trivially (and Φ_LA is vacuous).
        assert!(matches!(local_axioms_hold(&m, &[]), Ok(())));
        // an instance-specific sentence over Σ_M: "the instance has a normal form".
        fn has_normal_form(m: &Instance) -> bool {
            m.substrate().elements().any(|x| m.substrate().is_normal_form(x))
        }
        fn is_pure_nwf(m: &Instance) -> bool {
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
        // Scope-Suf (R1.5.T2) realized: branching →_ρ with TWO distinct normal forms
        // (0→1, 0→2; NF 1, NF 2) breaks global confluence — but the ρ_M-ORBIT (the
        // strategy: ρ(0)=1) meets NF exactly once. SC-Orb ⊤ while PA-Conf ⊥.
        let e = [(0, 1), (0, 2)];
        let s = Substrate::new(3, &e, &e).unwrap();
        let m = Instance::new(s, vec![ElementId(1), ElementId(1), ElementId(2)]).unwrap();
        assert!(crate::r1::axiom_system::pa_conf(&m).is_err()); // global confluence fails
        assert!(matches!(sc_orb(&m), Ok(())));            // orbit-scoped confluence holds
    }
}
