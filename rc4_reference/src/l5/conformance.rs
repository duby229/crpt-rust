//! # L5.3 — `T_CRPT` Conformance (is this model a CRPT model?)
//!
//! Exact realization of the model-correspondence content of spec section **L5.3**
//! (`CRPT_OMEGA_TOWER_L5.md`, v1.0.0-rc4):
//!
//! - L5.3.D11 `T_CRPT` — the CRPT theory: the Σ_CRPT-sentences true in all CRPT models,
//!   over the signature `Σ_CRPT` (L5.3.D10), axiomatized by the substrate/operator sentences (S-Inc, S-Fix, S-TopSep, S-rho-Cont,
//!   C1, C2) and the nine PA-* axioms (plus model-local LA_M).
//! - L5.3.T1 `Mod-Corr` — a finite Σ_CRPT-structure `M ⊧ T_CRPT` **iff** it is a CRPT
//!   model (`Mod_CRPT`); satisfaction *is* model-hood.
//! - L5.3.T4 `FOL-Fin` — on **finite** models `T_CRPT` collapses to its first-order
//!   fragment, so a finite model is a CRPT model iff it satisfies `T_CRPT^FOL`. The
//!   second-order sentences (C2/`≈`, PA-CoInd) reduce to finite schemas — and `≈` is
//!   computed exactly here — so [`is_crpt_model`] is an **exact, complete** verdict.
//!
//! This module is the consolidation of [`crate::l1::axioms`] into the L5.3 frame: it
//! reports `M ⊧ T_CRPT^FOL` sentence-by-sentence and returns the model-hood verdict.
//!
//! **The Tarski kernel (the model-theory scaffolding, now realized):**
//!
//! - L5.3.D2 `L-Str` — the [`Model`] **is** the Σ_CRPT-structure (L5.3.D10): carrier
//!   `U^M = 𝒰_M`, `ρ^M` = the projection operator, `→_ρ^M`/`→_σ^M` = the substrate
//!   relations, `Fix^M(x) ⟺ ρ(x) = x`, `Observable^M` = the default observable (OC-1).
//!   (The `Open` sort is the discrete topology's; `In` is eliminable there.)
//! - L5.3.D3 `L-Th` — sentences are closed [`Formula`]s; a theory is a set of them
//!   ([`satisfies_theory`]).
//! - L5.3.D4 `⊧` — Tarski satisfaction ([`satisfies`]): the standard recursion, exactly
//!   decidable on the finite universe (`FOL-Fin`).
//! - L5.3.D7 `Rel-Sent` — relativization `φ|_S` ([`satisfies_relativized`]): quantifiers
//!   restricted to a definable subset — implemented as the translation's semantics.
//! - L5.3.D12 `Scope-Sat` — scope-aware satisfaction `M ⊧_S PA-X`
//!   ([`scope_aware_satisfaction`]), returning the four-valued
//!   [`Scope`](crate::l1::profile::Scope) of `PA-Scope` (L1.5.D1).
//! - L5.3.D8 `L-Hom` — the L-homomorphism checker ([`is_l_homomorphism`]): strict
//!   preservation of `ρ`, `→_ρ`, `→_σ`, `Fix`. L5.3.D14 `CRPT-Hom`: a CRPT model
//!   homomorphism (`Hom` L5.2.D1) is equivalently a CNF-preserving L-Hom.
//! - L5.3.D9 `L-ModCat` / D13 `CRPT-Mod-L5.3` / D15 `Mod_CRPT-L5.3` — the category
//!   `Mod(Σ_CRPT, T_CRPT)`: objects = structures satisfying the theory (= CRPT models,
//!   `Mod-Corr`), morphisms = L-homs; identities/composition are
//!   [`crate::l5::homomorphism::Homomorphism`]'s. D13/D15 are the formal-theory
//!   restatements of `CRPT-Mod-18` (L5.1.D1) and `Mod_CRPT-Cat` (L5.5.D1).
//!
//! The capstone certificate ([`certify_tarski_agrees_with_native`]) makes `Mod-Corr`
//! executable: the Tarski `⊧` of a `T_CRPT` axiom rendered as a [`Formula`] agrees with
//! the engine's native checker, model by model.
//!
//! **Topology on the finite substrate.** With the discrete topology (module docs of
//! [`crate::l1::substrate`]): **S-TopSep holds** (distinct points are separated by their
//! singleton open sets — T₂), and **S-rho-Cont holds** (every map on a discrete space is
//! continuous). The only topological sentence that can fail is **PA-WN_top** — a discrete
//! sequence converges iff eventually constant, i.e. iff the orbit reaches a fixpoint — so
//! PA-WN_top is *vacuous* when `∞_M = ∅` and *fails* on genuine persistence. PA-WN_top and
//! PA-NWF are **profile markers** (which of WF/NWF/Mixed the model is), not model-hood
//! requirements.

use crate::l1::axioms::{pa_bisim, pa_conf, pa_fix, pa_nwf, pa_prod};
use crate::l1::substrate::ElementId;
use crate::l2::projection::Model;

/// A sentence-by-sentence report of `M ⊧ T_CRPT^FOL` (L5.3.D11 / L5.3.T4). Each field is
/// the truth of the corresponding `T_CRPT` sentence on the (finite, discrete-topology) model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Conformance {
    /// `S-Inc` (L5.3.2.1) — inclusion →_ρ ⊆ →_σ. Always holds (a [`Model`]'s substrate
    /// enforces it at construction, L1.1.D1).
    pub s_inc: bool,
    /// `S-Fix` (L5.3.2.1) — `Fix(x) ↔ ρ(x)=x`, i.e. `PA-Fix` (Fix = NF).
    pub s_fix: bool,
    /// `S-TopSep` (L5.3.2.1) — Hausdorff separation. Holds (discrete topology is T₂).
    pub s_topsep: bool,
    /// `S-rho-Cont` (L5.3.2.1) — continuity of ρ. Holds (every map is continuous on a
    /// discrete space).
    pub s_rho_cont: bool,
    /// `C1` (Step-or-Fix, L2.1.D1). Always holds (validated at [`Model`] construction).
    pub c1: bool,
    /// `C2` (Bisimulation Equivariance, L2.1.D1). Always holds (validated at construction;
    /// `≈` computed exactly, the `FOL-Fin` finite reduction of the second-order sentence).
    pub c2: bool,
    /// `PA-WN` (L1.2.Ax1) on its validity scope ↓_M: every convergent element reaches a NF.
    pub pa_wn: bool,
    /// `PA-Conf` (L1.2.Ax2).
    pub pa_conf: bool,
    /// `PA-Prod` (L1.2.Ax6) under the default Observable.
    pub pa_prod: bool,
    /// `PA-Bisim` (L1.3.Ax1).
    pub pa_bisim: bool,
    /// `PA-CoInd` (L1.2.Ax5). Holds — realized not as a check over all predicate
    /// transformers but as the **correctness of the greatest-fixpoint combinator**
    /// ([`crate::l0::sol_necessity::greatest_fixpoint`], Knaster–Tarski): Park's lemma *is* that
    /// combinator instantiated. The finite reduction is `FOL-Fin` (L5.3.T4); also
    /// derivable from `PA-NWF` (L1.6.T1). See [`crate::l0::sol_necessity`].
    pub pa_coind: bool,
    /// `PA-NWF` (L1.2.Ax4) — **profile marker**: `∞_M ≠ ∅` (not a model-hood requirement).
    pub pa_nwf: bool,
    /// `PA-WN_top` (L1.2.Ax7) — **profile marker**: holds (vacuously) iff `∞_M = ∅` on the
    /// discrete topology; fails on genuine persistence. Not a model-hood requirement.
    pub pa_wn_top: bool,
}

/// **L5.3.D4 (`⊧`) / L5.3.T4 (`FOL-Fin`)** — the satisfaction relation: report `M ⊧ T_CRPT^FOL` sentence-by-sentence.
pub fn conforms(m: &Model) -> Conformance {
    let op = m.operator();
    // PA-WN on validity scope ↓_M: every convergent element's canonical fixpoint is a NF
    // (vacuous on persistent elements, which are out of PA-WN's scope in native models).
    let pa_wn_scoped = m.substrate().elements().all(|x| match op.canonical_fixpoint(x) {
        Some(f) => m.substrate().is_normal_form(f),
        None => true,
    });
    let nwf = pa_nwf(m);
    Conformance {
        s_inc: true,       // Substrate invariant (L1.1.D1)
        s_fix: pa_fix(m).is_ok(),
        s_topsep: true,    // discrete topology is T₂
        s_rho_cont: true,  // every map continuous on a discrete space
        c1: true,          // Model invariant (validated at construction)
        c2: true,          // Model invariant (validated at construction)
        pa_wn: pa_wn_scoped,
        pa_conf: pa_conf(m).is_ok(),
        pa_prod: pa_prod(m, |_| 1).is_ok(), // minimal contract: O_M = {1, 0}, all content
        pa_bisim: pa_bisim(m).is_ok(),
        pa_coind: true,    // finite coinduction schema (FOL-Fin)
        pa_nwf: nwf,
        pa_wn_top: !nwf,   // holds vacuously iff ∞_M = ∅ (discrete topology)
    }
}

/// **L5.3.D5 (`L-Mod`) / L5.3.T1 (`Mod-Corr`) / L5.3.T4 (`FOL-Fin`)** — the model-hood verdict: `true` iff
/// `M ⊧ T_CRPT^FOL`, i.e. `M` **is a CRPT model**. Requires the model-hood sentences
/// (S-Inc, S-Fix, S-TopSep, S-rho-Cont, C1, C2, PA-WN on ↓_M, PA-Conf, PA-Prod, PA-Bisim,
/// PA-CoInd); the profile markers PA-NWF and PA-WN_top are **not** required (a pure-WF and
/// a native model are both genuine CRPT models, in different profiles).
pub fn is_crpt_model(m: &Model) -> bool {
    let c = conforms(m);
    c.s_inc
        && c.s_fix
        && c.s_topsep
        && c.s_rho_cont
        && c.c1
        && c.c2
        && c.pa_wn
        && c.pa_conf
        && c.pa_prod
        && c.pa_bisim
        && c.pa_coind
}


/// **L5.3.D10 (`Σ_CRPT`) — terms of sort `U`**: variables (de Bruijn indices into the
/// quantifier environment — `Variable(0)` is the innermost binder) and applications of
/// the projection function symbol `ρ`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SigmaTerm {
    /// A bound variable (de Bruijn index).
    Variable(u32),
    /// `ρ(t)` — the projection function symbol applied.
    Rho(Box<SigmaTerm>),
}

/// **L5.3.D3 (`L-Th`) — formulas over `Σ_CRPT`** (L5.3.D10): atomic formulas for the
/// signature's relation symbols and equality, boolean connectives, and quantifiers over
/// the universe sort (de Bruijn binding). A **sentence** is a closed formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    /// `t₁ →_ρ t₂` — the reduction relation symbol.
    Reduction(SigmaTerm, SigmaTerm),
    /// `t₁ →_σ t₂` — the structural relation symbol.
    Structural(SigmaTerm, SigmaTerm),
    /// `Fix(t)` — the fixpoint predicate (`Fix(x) ⟺ ρ(x) = x`).
    Fix(SigmaTerm),
    /// `Observable(t)` — the observable-content atom (rc4: `Σ_CRPT` carries the sort `O`
    /// and retypes `Observable : U → O` with the pointed codomain `(O_M, 0)`). The
    /// predicate reading is "the derived obs at `t` is non-silent" — obs is
    /// Σ_CRPT-definable (`Obs-Lab-WD` L1.1.T1(iv)), so the atom reads derived structure
    /// only, and `Mod-Corr` is well-posed for PA-Bisim over the unextended signature.
    Observable(SigmaTerm),
    /// `t₁ = t₂` — equality.
    Equal(SigmaTerm, SigmaTerm),
    /// `¬φ`.
    Not(Box<Formula>),
    /// `φ ∧ ψ`.
    And(Box<Formula>, Box<Formula>),
    /// `φ ∨ ψ`.
    Or(Box<Formula>, Box<Formula>),
    /// `φ → ψ`.
    Implies(Box<Formula>, Box<Formula>),
    /// `φ ↔ ψ`.
    Iff(Box<Formula>, Box<Formula>),
    /// `∀x φ` — binds a new innermost variable of sort `U`.
    ForAll(Box<Formula>),
    /// `∃x φ` — binds a new innermost variable of sort `U`.
    Exists(Box<Formula>),
}

/// **L5.3.D2 (`L-Str`)** — the term interpretation `⟦t⟧^M` under an environment
/// (innermost binder last).
fn term_value(m: &Model, t: &SigmaTerm, environment: &[ElementId]) -> ElementId {
    match t {
        SigmaTerm::Variable(i) => environment[environment.len() - 1 - *i as usize],
        SigmaTerm::Rho(inner) => m.operator().project(term_value(m, inner, environment)),
    }
}

fn satisfies_in(
    m: &Model,
    phi: &Formula,
    environment: &mut Vec<ElementId>,
    scope: Option<&[bool]>,
) -> bool {
    let in_scope = |x: ElementId| scope.map_or(true, |s| s[x.index()]);
    match phi {
        Formula::Reduction(t1, t2) => {
            let (a, b) = (term_value(m, t1, environment), term_value(m, t2, environment));
            m.substrate().reduction_successors(a).contains(&b)
        }
        Formula::Structural(t1, t2) => {
            let (a, b) = (term_value(m, t1, environment), term_value(m, t2, environment));
            m.substrate().structural_successors(a).contains(&b)
        }
        Formula::Fix(t) => {
            let a = term_value(m, t, environment);
            m.operator().project(a) == a
        }
        Formula::Observable(t) => {
            // rc4 (Obs-Lab L1.1.D8): a normal form is its own (non-silent) atomic
            // observable; a non-fixpoint's obs is the contract content of its projection
            // step, stored as the derived labelling — non-silent ⟺ ≠ 0 (PA-Prod).
            let a = term_value(m, t, environment);
            m.substrate().is_normal_form(a) || m.substrate().observation(a) != 0
        }
        Formula::Equal(t1, t2) => {
            term_value(m, t1, environment) == term_value(m, t2, environment)
        }
        Formula::Not(inner) => !satisfies_in(m, inner, environment, scope),
        Formula::And(a, b) => {
            satisfies_in(m, a, environment, scope) && satisfies_in(m, b, environment, scope)
        }
        Formula::Or(a, b) => {
            satisfies_in(m, a, environment, scope) || satisfies_in(m, b, environment, scope)
        }
        Formula::Implies(a, b) => {
            !satisfies_in(m, a, environment, scope) || satisfies_in(m, b, environment, scope)
        }
        Formula::Iff(a, b) => {
            satisfies_in(m, a, environment, scope) == satisfies_in(m, b, environment, scope)
        }
        Formula::ForAll(body) => m.substrate().elements().all(|u| {
            !in_scope(u) || {
                environment.push(u);
                let holds = satisfies_in(m, body, environment, scope);
                environment.pop();
                holds
            }
        }),
        Formula::Exists(body) => m.substrate().elements().any(|u| {
            in_scope(u) && {
                environment.push(u);
                let holds = satisfies_in(m, body, environment, scope);
                environment.pop();
                holds
            }
        }),
    }
}

/// **L5.3.D4 (`⊧`)** — Tarski satisfaction `M ⊧ φ` for a sentence over the Σ_CRPT
/// structure that the [`Model`] *is* (`L-Str` L5.3.D2). The standard recursion, exactly
/// decidable on the finite universe (`FOL-Fin` L5.3.T4).
pub fn satisfies(m: &Model, sentence: &Formula) -> bool {
    satisfies_in(m, sentence, &mut Vec::new(), None)
}

/// **L5.3.D3 (`L-Th`)** — `M ⊧ T` for a theory (a set of sentences). Returns the index
/// of the first failing sentence, or `Ok`.
pub fn satisfies_theory(m: &Model, theory: &[Formula]) -> Result<(), usize> {
    for (i, sentence) in theory.iter().enumerate() {
        if !satisfies(m, sentence) {
            return Err(i);
        }
    }
    Ok(())
}

/// **L5.3.D7 (`Rel-Sent`)** — relativized satisfaction `M ⊧ φ|_S`: every quantifier
/// restricted to the definable subset `S` (`∀x φ ↦ ∀x (x∈S → φ^S)`,
/// `∃x φ ↦ ∃x (x∈S ∧ φ^S)`) — the translation implemented by its semantics.
pub fn satisfies_relativized(m: &Model, sentence: &Formula, scope: &[bool]) -> bool {
    satisfies_in(m, sentence, &mut Vec::new(), Some(scope))
}

/// **L5.3.D12 (`Scope-Sat`)** — scope-aware satisfaction `M ⊧_S PA-X`, returning the
/// four-valued [`Scope`](crate::l1::profile::Scope) of `PA-Scope` (L1.5.D1):
/// `Global` if `M ⊧ φ` outright; `Vacuous` if the scope is empty; `Scoped(S)` if
/// `M ⊧ φ|_S` (`Rel-Sent` L5.3.D7); else `Fails`.
pub fn scope_aware_satisfaction(
    m: &Model,
    sentence: &Formula,
    scope_set: crate::l1::profile::ScopeSet,
    scope: &[bool],
) -> crate::l1::profile::Scope {
    use crate::l1::profile::Scope;
    if satisfies(m, sentence) {
        Scope::Global
    } else if scope.iter().all(|&b| !b) {
        Scope::Vacuous
    } else if satisfies_relativized(m, sentence, scope) {
        Scope::Scoped(scope_set)
    } else {
        Scope::Fails
    }
}

/// **L5.3.D8 (`L-Hom`)** — whether `h` is an **L-homomorphism** of Σ_CRPT-structures:
/// strict preservation of every function and relation symbol —
/// `h(ρ(x)) = ρ(h(x))`, `x →_ρ y ⟹ h(x) →_ρ h(y)`, `x →_σ y ⟹ h(x) →_σ h(y)`,
/// `Fix(x) ⟹ Fix(h(x))`. (`CRPT-Hom` L5.3.D14: a CRPT model homomorphism `Hom` L5.2.D1
/// is equivalently a CNF-preserving L-Hom — L-Hom is *stricter* on `ρ` (on-the-nose,
/// not up to ≃) and looser on CNF, the two meeting exactly at CNF preservation.)
pub fn is_l_homomorphism(source: &Model, target: &Model, h: &[ElementId]) -> bool {
    let (s1, s2) = (source.substrate(), target.substrate());
    if h.len() != s1.universe_len() as usize {
        return false;
    }
    let (op1, op2) = (source.operator(), target.operator());
    s1.elements().all(|x| {
        let hx = h[x.index()];
        h[op1.project(x).index()] == op2.project(hx) // ρ strictly
            && s1.reduction_successors(x).iter().all(|&y| s2.reduction_successors(hx).contains(&h[y.index()]))
            && s1.structural_successors(x).iter().all(|&y| s2.structural_successors(hx).contains(&h[y.index()]))
            && (op1.project(x) != x || op2.project(hx) == hx) // Fix preserved
    })
}

/// **`T_CRPT` axioms as Σ_CRPT sentences** — `PA-Fix` (L1.2.Ax3):
/// `∀x ( Fix(x) ↔ ¬∃y (x →_ρ y) )` (fixpoints are exactly the normal forms).
pub fn pa_fix_sentence() -> Formula {
    Formula::ForAll(Box::new(Formula::Iff(
        Box::new(Formula::Fix(SigmaTerm::Variable(0))),
        Box::new(Formula::Not(Box::new(Formula::Exists(Box::new(Formula::Reduction(
            SigmaTerm::Variable(1),
            SigmaTerm::Variable(0),
        )))))),
    )))
}

/// **`T_CRPT` axioms as Σ_CRPT sentences** — the operator condition `C1`:
/// `∀x ( ∃y (x →_ρ y) → x →_ρ ρ(x) )` (off normal forms, the strategy follows →_ρ).
pub fn c1_sentence() -> Formula {
    Formula::ForAll(Box::new(Formula::Implies(
        Box::new(Formula::Exists(Box::new(Formula::Reduction(
            SigmaTerm::Variable(1),
            SigmaTerm::Variable(0),
        )))),
        Box::new(Formula::Reduction(
            SigmaTerm::Variable(0),
            SigmaTerm::Rho(Box::new(SigmaTerm::Variable(0))),
        )),
    )))
}

/// Witness **L5.3.T1 (`Mod-Corr`) / L5.3.T4 (`FOL-Fin`), executable form** — the Tarski
/// `⊧` of the `T_CRPT` axioms rendered as Σ_CRPT sentences agrees with the engine's
/// native checkers on this model: `M ⊧ pa_fix_sentence ⟺ pa_fix(M)` and
/// `M ⊧ c1_sentence` (C1 is enforced at `Model` construction, so it must hold).
/// Returns the name of the first disagreeing sentence, or `Ok`.
pub fn certify_tarski_agrees_with_native(m: &Model) -> Result<(), &'static str> {
    if satisfies(m, &pa_fix_sentence()) != crate::l1::axioms::pa_fix(m).is_ok() {
        return Err("PA-Fix");
    }
    if !satisfies(m, &c1_sentence()) {
        return Err("C1");
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
    fn pure_wf_chain_is_a_crpt_model() {
        // 0→1, 1 ∈ NF: a pure-WF CRPT model (PA-NWF false, PA-WN_top vacuous — both fine).
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let c = conforms(&m);
        assert!(is_crpt_model(&m));
        assert!(!c.pa_nwf); // pure WF
        assert!(c.pa_wn_top); // vacuous (∞_M = ∅)
        assert!(c.s_topsep && c.s_rho_cont); // discrete topology
    }

    #[test]
    fn native_nwf_model_is_a_crpt_model() {
        // 0→1, 1 ∈ NF (↓_M) and 2⇄3 with distinct obs (∞_M): a Mixed CRPT model.
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let c = conforms(&m);
        assert!(is_crpt_model(&m)); // a genuine CRPT model in the native (Mixed) profile
        assert!(c.pa_nwf); // ∞_M ≠ ∅
        assert!(!c.pa_wn_top); // PA-WN_top fails on the discrete topology (genuine persistence)
        assert!(c.pa_wn); // PA-WN still holds on its scope ↓_M
    }

    #[test]
    fn non_confluent_structure_is_not_a_crpt_model() {
        // 0→1, 0→2, both NF: C1/C2 hold but PA-Conf fails ⇒ NOT a CRPT model (FOL-Fin verdict).
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(2)]).unwrap();
        let c = conforms(&m);
        assert!(!c.pa_conf);
        assert!(!is_crpt_model(&m));
    }

    #[test]
    fn tarski_satisfaction_agrees_with_native_checkers() {
        // a conforming model: PA-Fix holds both natively and by Tarski ⊧ (Mod-Corr).
        let e = [(0, 1), (2, 3)];
        let m = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert!(satisfies(&m, &pa_fix_sentence()));
        assert!(matches!(certify_tarski_agrees_with_native(&m), Ok(())));
        // a PA-Fix violator: the self-loop 0→0 makes 0 a ρ-fixpoint that is NOT a normal
        // form — native pa_fix errs and the Tarski ⊧ of the same sentence is false.
        let loop_e = [(0, 0)];
        let bad = Model::from_functional_reduction(Substrate::new(1, &loop_e, &loop_e).unwrap()).unwrap();
        assert!(!satisfies(&bad, &pa_fix_sentence()));
        assert!(crate::l1::axioms::pa_fix(&bad).is_err());
        assert!(matches!(certify_tarski_agrees_with_native(&bad), Ok(()))); // they AGREE
        // theory satisfaction reports the failing sentence by index.
        assert_eq!(satisfies_theory(&bad, &[c1_sentence(), pa_fix_sentence()]), Err(1));
    }

    #[test]
    fn relativization_realizes_the_four_valued_scope_semantics() {
        use crate::l1::profile::{Scope, ScopeSet};
        // mixed model: 0 ⇄ 1 (∞_M), 2 → 3 (↓_M, 3 ∈ NF).
        let e = [(0, 1), (1, 0), (2, 3)];
        let m = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        // "every element has a →_ρ-successor": fails globally (3 is NF), holds on ∞_M.
        let productive = Formula::ForAll(Box::new(Formula::Exists(Box::new(
            Formula::Reduction(SigmaTerm::Variable(1), SigmaTerm::Variable(0)),
        ))));
        let persistent = [true, true, false, false]; // ∞_M = {0, 1}
        assert!(!satisfies(&m, &productive));
        assert!(satisfies_relativized(&m, &productive, &persistent));
        assert_eq!(
            scope_aware_satisfaction(&m, &productive, ScopeSet::PersistentRegime, &persistent),
            Scope::Scoped(ScopeSet::PersistentRegime)
        );
        // Vacuous on the empty scope; Fails when false even relativized (∀x Fix(x) on ∞_M).
        assert_eq!(
            scope_aware_satisfaction(&m, &productive, ScopeSet::PersistentRegime, &[false; 4]),
            Scope::Vacuous
        );
        let all_fix = Formula::ForAll(Box::new(Formula::Fix(SigmaTerm::Variable(0))));
        assert_eq!(
            scope_aware_satisfaction(&m, &all_fix, ScopeSet::PersistentRegime, &persistent),
            Scope::Fails
        );
        // L-Hom (L5.3.D8): the identity is an L-homomorphism; collapsing ∞_M onto the NF
        // breaks strict ρ-preservation and is rejected.
        let identity: Vec<ElementId> = m.substrate().elements().collect();
        assert!(is_l_homomorphism(&m, &m, &identity));
        // (3 is a fixpoint, so strict ρ-preservation holds for the constant map; →_ρ
        // preservation fails: 0 →_ρ 1 but 3 →_ρ 3 is not an edge.)
        let collapse_all = vec![ElementId(3); 4];
        assert!(!is_l_homomorphism(&m, &m, &collapse_all));
    }
}
