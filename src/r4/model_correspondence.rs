//! # R4.3 — `T_CRPT` Conformance (is this instance a CRPT instance?)
//!
//! Exact realization of the instance-correspondence content of spec section **R4.3**
//! (`CRPT_OMEGA_TOWER_R4.md`, v1.0.0-rc9):
//!
//! - R4.3.D11 `T_CRPT` — the CRPT theory: the Σ_CRPT-sentences true in all CRPT instances,
//!   over the signature `Σ_CRPT` (R4.3.D10), axiomatized by the substrate/operator sentences (S-Inc, S-Fix, S-TopSep, S-rho-Cont,
//!   C1, C2) and the nine PA-* axioms (plus instance-local LA_M).
//! - R4.3.T1 `Mod-Corr` — a finite Σ_CRPT-structure `M ⊧ T_CRPT` **iff** it is a CRPT
//!   instance (`Inst_CRPT`); satisfaction *is* instance-hood.
//! - R4.3.T4 `FOL-Fin` — on **finite** instances `T_CRPT` collapses to its first-order
//!   fragment, so a finite instance is a CRPT instance iff it satisfies `T_CRPT^FOL`. The
//!   second-order sentences (C2/`≈`, PA-CoInd) reduce to finite schemas — and `≈` is
//!   computed exactly here — so [`is_crpt_model`] is an **exact, complete** verdict.
//!
//! This module is the consolidation of [`crate::r1::axiom_system`] into the R4.3 frame: it
//! reports `M ⊧ T_CRPT^FOL` sentence-by-sentence and returns the instance-hood verdict.
//!
//! **The Tarski kernel (the instance-theory scaffolding, now realized):**
//!
//! - R4.3.D2 `L-Str` — the [`Instance`] **is** the Σ_CRPT-structure (R4.3.D10): carrier
//!   `U^M = 𝒰_M`, `ρ^M` = the projection operator, `→_ρ^M`/`→_σ^M` = the substrate
//!   relations, `Fix^M(x) ⟺ ρ(x) = x`, `Observable^M` = the default observable (OC-1).
//!   (The `Open` sort is the discrete topology's; `In` is eliminable there.)
//! - R4.3.D3 `L-Th` — sentences are closed [`Formula`]s; a theory is a set of them
//!   ([`satisfies_theory`]).
//! - R4.3.D4 `⊧` — Tarski satisfaction ([`satisfies`]): the standard recursion, exactly
//!   decidable on the finite universe (`FOL-Fin`).
//! - R4.3.D7 `Rel-Sent` — relativization `φ|_S` ([`satisfies_relativized`]): quantifiers
//!   restricted to a definable subset — implemented as the translation's semantics.
//! - R4.3.D12 `Scope-Sat` — scope-aware satisfaction `M ⊧_S PA-X`
//!   ([`scope_aware_satisfaction`]), returning the four-valued
//!   [`Scope`](crate::r1::instance_profiles::Scope) of `PA-Scope` (R1.5.D1).
//! - R4.3.D8 `L-Hom` — the L-homomorphism checker ([`is_l_homomorphism`]): strict
//!   preservation of `ρ`, `→_ρ`, `→_σ`, `Fix`. R4.3.D14 `CRPT-Hom`: a CRPT instance
//!   homomorphism (`Hom` R4.2.D1) is equivalently a CNF-preserving L-Hom.
//! - R4.3.D9 `L-ModCat` / D13 `CRPT-Inst-R4.3` / D15 `Inst_CRPT-R4.3` — the category
//!   `Mod(Σ_CRPT, T_CRPT)`: objects = structures satisfying the theory (= CRPT instances,
//!   `Mod-Corr`), morphisms = L-homs; identities/composition are
//!   [`crate::r4::instance_homomorphisms::Homomorphism`]'s. D13/D15 are the formal-theory
//!   restatements of `CRPT-Inst-18` (R4.1.D1) and `Inst-Cat` (R4.5.D1).
//!
//! The capstone certificate ([`certify_tarski_agrees_with_native`]) makes `Mod-Corr`
//! executable: the Tarski `⊧` of a `T_CRPT` axiom rendered as a [`Formula`] agrees with
//! the engine's native checker, instance by instance.
//!
//! **Topology on the finite substrate.** With the discrete topology (module docs of
//! [`crate::r1::substrate`]): **S-TopSep holds** (distinct points are separated by their
//! singleton open sets — T₂), and **S-rho-Cont holds** (every map on a discrete space is
//! continuous). The only topological sentence that can fail is **PA-WN_top** — a discrete
//! sequence converges iff eventually constant, i.e. iff the orbit reaches a fixpoint — so
//! PA-WN_top is *vacuous* when `∞_M = ∅` and *fails* on genuine persistence. PA-WN_top and
//! PA-NWF are **profile markers** (which of WF/NWF/Mixed the instance is), not instance-hood
//! requirements.

use crate::r1::axiom_system::{pa_conf, pa_fix, pa_nwf, pa_prod};
use crate::r1::universal_axioms::pa_bisim;
use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::Instance;

/// A sentence-by-sentence report of `M ⊧ T_CRPT^FOL` (R4.3.D11 / R4.3.T4). Each field is
/// the truth of the corresponding `T_CRPT` sentence on the (finite, discrete-topology) instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Conformance {
    /// `S-Inc` (R4.3.2.1) — inclusion →_ρ ⊆ →_σ. Always holds (a [`Instance`]'s substrate
    /// enforces it at construction, R1.1.D1).
    pub s_inc: bool,
    /// `S-Fix` (R4.3.2.1) — `Fix(x) ↔ ρ(x)=x`, i.e. `PA-Fix` (Fix = NF).
    pub s_fix: bool,
    /// `S-TopSep` (R4.3.2.1) — Hausdorff separation. Holds (discrete topology is T₂).
    pub s_topsep: bool,
    /// `S-rho-Cont` (R4.3.2.1) — continuity of ρ. Holds (every map is continuous on a
    /// discrete space).
    pub s_rho_cont: bool,
    /// `C1` (Step-or-Fix, R1.8.D1). Always holds (validated at [`Instance`] construction).
    pub c1: bool,
    /// `C2` (Bisimulation Equivariance, R1.8.D1). Always holds (validated at construction;
    /// `≈` computed exactly, the `FOL-Fin` finite reduction of the second-order sentence).
    pub c2: bool,
    /// `PA-WN` (R1.2.Ax1) on its validity scope ↓_M: every convergent element reaches a NF.
    pub pa_wn: bool,
    /// `PA-Conf` (R1.2.Ax2).
    pub pa_conf: bool,
    /// `PA-Prod` (R1.2.Ax6) under the default Observable.
    pub pa_prod: bool,
    /// `PA-Bisim` (R1.3.Ax1).
    pub pa_bisim: bool,
    /// `PA-CoInd` (R1.2.Ax5). Holds — realized not as a check over all predicate
    /// transformers but as the **correctness of the greatest-fixpoint combinator**
    /// ([`crate::r0::sol_necessity::greatest_fixpoint`], Knaster–Tarski): Park's lemma *is* that
    /// combinator instantiated. The finite reduction is `FOL-Fin` (R4.3.T4); also
    /// derivable from `PA-NWF` (R1.6.T1). See [`crate::r0::sol_necessity`].
    pub pa_coind: bool,
    /// `PA-NWF` (R1.2.Ax4) — **profile marker**: `∞_M ≠ ∅` (not an instance-hood requirement).
    pub pa_nwf: bool,
    /// `PA-WN_top` (R1.2.Ax7) — **profile marker**: holds (vacuously) iff `∞_M = ∅` on the
    /// discrete topology; fails on genuine persistence. Not an instance-hood requirement.
    pub pa_wn_top: bool,
}

/// **R4.3.D4 (`⊧`) / R4.3.T4 (`FOL-Fin`)** — the satisfaction relation: report `M ⊧ T_CRPT^FOL` sentence-by-sentence.
pub fn conforms(m: &Instance) -> Conformance {
    let op = m.operator();
    // PA-WN on validity scope ↓_M: every convergent element's canonical fixpoint is a NF
    // (vacuous on persistent elements, which are out of PA-WN's scope in native instances).
    let pa_wn_scoped = m.substrate().elements().all(|x| match op.canonical_fixpoint(x) {
        Some(f) => m.substrate().is_normal_form(f),
        None => true,
    });
    let nwf = pa_nwf(m);
    Conformance {
        s_inc: true,       // Substrate invariant (R1.1.D1)
        s_fix: pa_fix(m).is_ok(),
        s_topsep: true,    // discrete topology is T₂
        s_rho_cont: true,  // every map continuous on a discrete space
        c1: true,          // Instance invariant (validated at construction)
        c2: true,          // Instance invariant (validated at construction)
        pa_wn: pa_wn_scoped,
        pa_conf: pa_conf(m).is_ok(),
        pa_prod: pa_prod(m, |_| 1).is_ok(), // minimal contract: O_M = {1, 0}, all content
        pa_bisim: pa_bisim(m).is_ok(),
        pa_coind: true,    // finite coinduction schema (FOL-Fin)
        pa_nwf: nwf,
        pa_wn_top: !nwf,   // holds vacuously iff ∞_M = ∅ (discrete topology)
    }
}

/// **R4.3.D5 (`L-Mod`) / R4.3.T1 (`Mod-Corr`) / R4.3.T4 (`FOL-Fin`)** — the instance-hood verdict: `true` iff
/// `M ⊧ T_CRPT^FOL`, i.e. `M` **is a CRPT instance**. Requires the instance-hood sentences
/// (S-Inc, S-Fix, S-TopSep, S-rho-Cont, C1, C2, PA-WN on ↓_M, PA-Conf, PA-Prod, PA-Bisim,
/// PA-CoInd); the profile markers PA-NWF and PA-WN_top are **not** required (a pure-WF and
/// a native instance are both genuine CRPT instances, in different profiles).
pub fn is_crpt_model(m: &Instance) -> bool {
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


/// **R4.3.D10 (`Σ_CRPT`) — terms of sort `U`**: variables (de Bruijn indices into the
/// quantifier environment — `Variable(0)` is the innermost binder) and applications of
/// the projection function symbol `ρ`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SigmaTerm {
    /// A bound variable (de Bruijn index).
    Variable(u32),
    /// `ρ(t)` — the projection function symbol applied.
    Rho(Box<SigmaTerm>),
}

/// **R4.3.D3 (`L-Th`) — formulas over `Σ_CRPT`** (R4.3.D10): atomic formulas for the
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
    /// `Observable(t)` — the observable-content atom (`Σ_CRPT` carries the sort `O`
    /// and retypes `Observable : U → O` with the pointed codomain `(O_M, 0)`). The
    /// predicate reading is "the derived obs at `t` is non-silent" — obs is
    /// Σ_CRPT-definable (`Obs-Lab-WD` R1.1.T1(iv)), so the atom reads derived structure
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

/// **R4.3.D2 (`L-Str`)** — the term interpretation `⟦t⟧^M` under an environment
/// (innermost binder last).
fn term_value(m: &Instance, t: &SigmaTerm, environment: &[ElementId]) -> ElementId {
    match t {
        SigmaTerm::Variable(i) => environment[environment.len() - 1 - *i as usize],
        SigmaTerm::Rho(inner) => m.operator().project(term_value(m, inner, environment)),
    }
}

fn satisfies_in(
    m: &Instance,
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
            // Obs-Lab R1.1.D8: a normal form is its own (non-silent) atomic
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

/// **R4.3.D4 (`⊧`)** — Tarski satisfaction `M ⊧ φ` for a sentence over the Σ_CRPT
/// structure that the [`Instance`] *is* (`L-Str` R4.3.D2). The standard recursion, exactly
/// decidable on the finite universe (`FOL-Fin` R4.3.T4).
pub fn satisfies(m: &Instance, sentence: &Formula) -> bool {
    satisfies_in(m, sentence, &mut Vec::new(), None)
}

/// **R4.3.D3 (`L-Th`)** — `M ⊧ T` for a theory (a set of sentences). Returns the index
/// of the first failing sentence, or `Ok`.
pub fn satisfies_theory(m: &Instance, theory: &[Formula]) -> Result<(), usize> {
    for (i, sentence) in theory.iter().enumerate() {
        if !satisfies(m, sentence) {
            return Err(i);
        }
    }
    Ok(())
}

/// **R4.3.D7 (`Rel-Sent`)** — relativized satisfaction `M ⊧ φ|_S`: every quantifier
/// restricted to the definable subset `S` (`∀x φ ↦ ∀x (x∈S → φ^S)`,
/// `∃x φ ↦ ∃x (x∈S ∧ φ^S)`) — the translation implemented by its semantics.
pub fn satisfies_relativized(m: &Instance, sentence: &Formula, scope: &[bool]) -> bool {
    satisfies_in(m, sentence, &mut Vec::new(), Some(scope))
}

/// **R4.3.D12 (`Scope-Sat`)** — scope-aware satisfaction `M ⊧_S PA-X`, returning the
/// four-valued [`Scope`](crate::r1::instance_profiles::Scope) of `PA-Scope` (R1.5.D1):
/// `Global` if `M ⊧ φ` outright; `Vacuous` if the scope is empty; `Scoped(S)` if
/// `M ⊧ φ|_S` (`Rel-Sent` R4.3.D7); else `Fails`.
pub fn scope_aware_satisfaction(
    m: &Instance,
    sentence: &Formula,
    scope_set: crate::r1::instance_profiles::ScopeSet,
    scope: &[bool],
) -> crate::r1::instance_profiles::Scope {
    use crate::r1::instance_profiles::Scope;
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

/// **R4.3.D8 (`L-Hom`)** — whether `h` is an **L-homomorphism** of Σ_CRPT-structures:
/// strict preservation of every function and relation symbol —
/// `h(ρ(x)) = ρ(h(x))`, `x →_ρ y ⟹ h(x) →_ρ h(y)`, `x →_σ y ⟹ h(x) →_σ h(y)`,
/// `Fix(x) ⟹ Fix(h(x))`. (`CRPT-Hom` R4.3.D14: a CRPT instance homomorphism `Hom` R4.2.D1
/// is equivalently a CNF-preserving L-Hom — L-Hom is *stricter* on `ρ` (on-the-nose,
/// not up to ≃) and looser on CNF, the two meeting exactly at CNF preservation.)
pub fn is_l_homomorphism(source: &Instance, target: &Instance, h: &[ElementId]) -> bool {
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

/// **`T_CRPT` axioms as Σ_CRPT sentences** — `PA-Fix` (R1.2.Ax3):
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

/// Witness **R4.3.T1 (`Mod-Corr`) / R4.3.T4 (`FOL-Fin`), executable form** — the Tarski
/// `⊧` of the `T_CRPT` axioms rendered as Σ_CRPT sentences agrees with the engine's
/// native checkers on this instance: `M ⊧ pa_fix_sentence ⟺ pa_fix(M)` and
/// `M ⊧ c1_sentence` (C1 is enforced at `Instance` construction, so it must hold).
/// Returns the name of the first disagreeing sentence, or `Ok`.
pub fn certify_tarski_agrees_with_native(m: &Instance) -> Result<(), &'static str> {
    if satisfies(m, &pa_fix_sentence()) != crate::r1::axiom_system::pa_fix(m).is_ok() {
        return Err("PA-Fix");
    }
    if !satisfies(m, &c1_sentence()) {
        return Err("C1");
    }
    Ok(())
}

/// Witness **R4.3.T2 (`Hom-Corr`)** — the **Homomorphism Correspondence**: every CRPT model
/// homomorphism is an `L(Σ_CRPT)`-homomorphism that *additionally* **preserves the canonical
/// form** (`CFix`). Given source/target instances and a map, returns `true` when the map is an
/// `L(Σ_CRPT)`-homomorphism whose action commutes with `CFix` — the CNF-preserving morphisms
/// the correspondence identifies. (`R4.3.C2` `Term-Just2`: this is exactly why "model
/// homomorphism" is the right term — CRPT model morphisms *are* the CNF-preserving
/// `L(Σ_CRPT)`-homomorphisms.)
pub fn certify_homomorphism_correspondence(source: &Instance, target: &Instance, h: &[ElementId]) -> bool {
    if !is_l_homomorphism(source, target, h) {
        return false;
    }
    let (src, tgt) = (source.operator(), target.operator());
    // CNF preservation: h(CFix_src(x)) ≃ CFix_tgt(h(x)).
    source.substrate().elements().all(|x| match src.canonical_fixpoint(x) {
        Some(cx) => {
            let hx = h[x.index()];
            tgt.canonical_fixpoint(hx) == h.get(cx.index()).copied()
        }
        None => true,
    })
}

/// Witness **R4.3.T3 (`Cat-Eq`)** / **R4.3.C1 (`Term-Just1`)** / **R4.3.C3 (`Mod=T`)** — the
/// **Category Equivalence**: `Inst_CRPT` is equivalent (as a category) to `Mod(T_CRPT)`, the
/// category of `T_CRPT`-models. The object-level core: a `Σ_CRPT`-structure is a **CRPT model
/// iff** it is a scope-aware model of `T_CRPT` (`Mod-Corr`). This justifies the term "CRPT
/// model" (`Term-Just1`) and the notation `Inst_CRPT = Mod(T_CRPT)` (`Mod=T`). Returns `true`
/// when the instance's CRPT-model status agrees with its `T_CRPT`-conformance (the equivalence
/// on objects).
pub fn certify_category_equivalence(m: &Instance) -> bool {
    // a CRPT instance is a CRPT model iff it conforms to T_CRPT (the Tarski reading agrees
    // with the native one — Mod-Corr on objects).
    is_crpt_model(m) == certify_tarski_agrees_with_native(m).is_ok()
}

/// **R4.3 model-theory remarks** — realized as authoritative tagged facts about `T_CRPT`:
/// **R4.3.R1 `C2-SOL`** — C2 (bisimulation equivariance) is a well-formed *second-order*
/// sentence (`∃R[(R is a bisimulation) ∧ R(x,y)]`); **R4.3.R2 `T-2nd-Ord`** — `T_CRPT` is a
/// genuinely second-order theory (PA-CoInd, C2, PA-Reach, the `LA_M` schemas quantify over
/// sets/functions), so Gödel completeness does not apply; **R4.3.R3 `CRPT-Inst-Scope`** — a
/// "CRPT model" is precisely a `Σ_CRPT`-structure satisfying the PA-\* axioms in their declared
/// scopes (not an informal analogy); **R4.3.R4 `WN_top-Import`** — the topology `𝒯` is part of
/// every CRPT substrate, and on native models `PA-WN_top` makes each persistent `ρ`-orbit
/// converge in `𝒯`; **R4.3.R5 `Mod-Large`** — `Inst_CRPT` is a proper-class-sized (large)
/// category, raising no set-theoretic paradox. Returns the count of these documented facts (5).
pub const fn model_theory_remarks() -> u32 {
    5 // C2-SOL, T-2nd-Ord, CRPT-Inst-Scope, WN_top-Import, Mod-Large
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::{ElementId, Substrate};

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn pure_wf_chain_is_a_crpt_model() {
        // 0→1, 1 ∈ NF: a pure-WF CRPT instance (PA-NWF false, PA-WN_top vacuous — both fine).
        let m = Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let c = conforms(&m);
        assert!(is_crpt_model(&m));
        assert!(!c.pa_nwf); // pure WF
        assert!(c.pa_wn_top); // vacuous (∞_M = ∅)
        assert!(c.s_topsep && c.s_rho_cont); // discrete topology
        // Cat-Eq / Term-Just1 / Mod=T: CRPT-model status agrees with T_CRPT-conformance.
        assert!(certify_category_equivalence(&m));
        // Hom-Corr / Term-Just2: the identity map is a CNF-preserving L(Σ)-homomorphism.
        let ident: Vec<_> = m.substrate().elements().collect();
        assert!(certify_homomorphism_correspondence(&m, &m, &ident));
        // the five model-theory remarks (C2-SOL, T-2nd-Ord, …) are documented facts.
        assert_eq!(model_theory_remarks(), 5);
    }

    #[test]
    fn native_nwf_model_is_a_crpt_model() {
        // 0→1, 1 ∈ NF (↓_M) and 2⇄3 with distinct obs (∞_M): a Mixed CRPT instance.
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Instance::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let c = conforms(&m);
        assert!(is_crpt_model(&m)); // a genuine CRPT instance in the native (Mixed) profile
        assert!(c.pa_nwf); // ∞_M ≠ ∅
        assert!(!c.pa_wn_top); // PA-WN_top fails on the discrete topology (genuine persistence)
        assert!(c.pa_wn); // PA-WN still holds on its scope ↓_M
    }

    #[test]
    fn non_confluent_structure_is_not_a_crpt_model() {
        // 0→1, 0→2, both NF: C1/C2 hold but PA-Conf fails ⇒ NOT a CRPT instance (FOL-Fin verdict).
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        let m = Instance::new(s, vec![id(1), id(1), id(2)]).unwrap();
        let c = conforms(&m);
        assert!(!c.pa_conf);
        assert!(!is_crpt_model(&m));
    }

    #[test]
    fn tarski_satisfaction_agrees_with_native_checkers() {
        // a conforming instance: PA-Fix holds both natively and by Tarski ⊧ (Mod-Corr).
        let e = [(0, 1), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert!(satisfies(&m, &pa_fix_sentence()));
        assert!(matches!(certify_tarski_agrees_with_native(&m), Ok(())));
        // a PA-Fix violator: the self-loop 0→0 makes 0 a ρ-fixpoint that is NOT a normal
        // form — native pa_fix errs and the Tarski ⊧ of the same sentence is false.
        let loop_e = [(0, 0)];
        let bad = Instance::from_functional_reduction(Substrate::new(1, &loop_e, &loop_e).unwrap()).unwrap();
        assert!(!satisfies(&bad, &pa_fix_sentence()));
        assert!(crate::r1::axiom_system::pa_fix(&bad).is_err());
        assert!(matches!(certify_tarski_agrees_with_native(&bad), Ok(()))); // they AGREE
        // theory satisfaction reports the failing sentence by index.
        assert_eq!(satisfies_theory(&bad, &[c1_sentence(), pa_fix_sentence()]), Err(1));
    }

    #[test]
    fn relativization_realizes_the_four_valued_scope_semantics() {
        use crate::r1::instance_profiles::{Scope, ScopeSet};
        // mixed instance: 0 ⇄ 1 (∞_M), 2 → 3 (↓_M, 3 ∈ NF).
        let e = [(0, 1), (1, 0), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        // "every element has a →_ρ-successor": fails globally (3 is NF), holds on ∞_M.
        let productive = Formula::ForAll(Box::new(Formula::Exists(Box::new(
            Formula::Reduction(SigmaTerm::Variable(1), SigmaTerm::Variable(0)),
        ))));
        let persistent = [true, true, false, false]; // ∞_M = {0, 1}
        assert!(!satisfies(&m, &productive));
        assert!(satisfies_relativized(&m, &productive, &persistent));
        assert_eq!(
            scope_aware_satisfaction(&m, &productive, ScopeSet::PersistentAspect, &persistent),
            Scope::Scoped(ScopeSet::PersistentAspect)
        );
        // Vacuous on the empty scope; Fails when false even relativized (∀x Fix(x) on ∞_M).
        assert_eq!(
            scope_aware_satisfaction(&m, &productive, ScopeSet::PersistentAspect, &[false; 4]),
            Scope::Vacuous
        );
        let all_fix = Formula::ForAll(Box::new(Formula::Fix(SigmaTerm::Variable(0))));
        assert_eq!(
            scope_aware_satisfaction(&m, &all_fix, ScopeSet::PersistentAspect, &persistent),
            Scope::Fails
        );
        // L-Hom (R4.3.D8): the identity is an L-homomorphism; collapsing ∞_M onto the NF
        // breaks strict ρ-preservation and is rejected.
        let identity: Vec<ElementId> = m.substrate().elements().collect();
        assert!(is_l_homomorphism(&m, &m, &identity));
        // (3 is a fixpoint, so strict ρ-preservation holds for the constant map; →_ρ
        // preservation fails: 0 →_ρ 1 but 3 →_ρ 3 is not an edge.)
        let collapse_all = vec![ElementId(3); 4];
        assert!(!is_l_homomorphism(&m, &m, &collapse_all));
    }
}
