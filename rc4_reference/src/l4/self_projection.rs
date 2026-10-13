//! # L4.6 — Self-Projection
//!
//! Exact realization of the finite core of spec section **L4.6**
//! (`CRPT_OMEGA_TOWER_L4.md`, v1.0.0-rc4):
//!
//! - L4.6.T2 `SP2` (Self-Projection Fixpoint) — the canonical projection is a fixed point
//!   of itself: `proj(proj(x)) ≈ proj(x)`. On the convergent regime, with `proj = CFix`,
//!   this is `CFix(CFix(x)) = CFix(x)` — the abstraction map is **idempotent**, so the
//!   observer framework applied to its own output reproduces it. This is CRPT's first
//!   self-referential closure, the precursor to the Lω self-conformance test
//!   ([`crate::lomega`]).
//!
//! - L4.6.D1 `Enc` — the **admissible encoding** interface, now realized:
//!   [`Term`] = `Terms(CRPT)` (variables, ρ_M, composition, fixpoint constructor) with
//!   exact denotations; [`AdmissibleEncoding`] is the model-supplied map
//!   `Enc : Terms(CRPT) × 𝒰_M → 𝒰_M`; and the four admissibility conditions are exact
//!   certificates ([`certify_enc_injective`] Enc-1, [`certify_enc_wf_faithful`] Enc-2,
//!   [`certify_enc_nwf_faithful`] Enc-3, [`certify_enc_compositional`] Enc-4). Enc-1's
//!   `t₁ = t₂` is **denotational** term equality ([`denotationally_equal`], decidable on
//!   finite substrates) — canonical in rc4.
//!   The PA-* axioms do not *supply* an encoding (rich Gödel numberings are model-phase);
//!   the interface and its admissibility checks are the engine's.
//!
//! **Out of single-model finite scope** (noted, not faked): L4.6.T1 `SP1` (composition
//! closure) is about composing projection operators *across different models* (four
//! WF/NWF cases); L4.6.T3 `SP3` (conditional universality) is now stateable *against* the
//! realized [`AdmissibleEncoding`] interface, holding conditionally on it.

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;

/// Witness **L4.6.T2 (`SP2`)** — the self-projection fixpoint: on the convergent regime the
/// canonical projection `CFix` satisfies `CFix(CFix(x)) = CFix(x)` (idempotence). Returns
/// the first convergent element where it fails (never), or `Ok`.
pub fn certify_self_projection_fixpoint(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(canonical) = op.canonical_fixpoint(x) {
            // proj(proj(x)) = CFix(CFix(x)) must equal proj(x) = CFix(x).
            if op.canonical_fixpoint(canonical) != Some(canonical) {
                return Err(x);
            }
        }
    }
    Ok(())
}


/// **L4.6.D1 (`Enc`) — `Terms(CRPT)`**: the CRPT-computable terms, built from variables,
/// `ρ_M`, composition, and the fixpoint constructor. `==` is syntactic; the admissibility
/// conditions use *denotational* equality ([`denotationally_equal`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// The variable `x` (the encoding's second argument).
    Var,
    /// `ρ_M(t)` — one projection step applied to a term.
    Projection(Box<Term>),
    /// `t₁ ∘ t₂` — composition.
    Composition(Box<Term>, Box<Term>),
    /// `CFix(t)` — the fixpoint (recursive-projection) constructor (`Rec-Proj` L2.1.D4).
    CanonicalForm(Box<Term>),
}

/// The denotation of `t` at `x` — the element the term computes. `None` exactly where the
/// fixpoint constructor is applied on `∞_M` (no finitary `CFix`).
pub fn term_denotation(op: &ProjectionOperator, t: &Term, x: ElementId) -> Option<ElementId> {
    match t {
        Term::Var => Some(x),
        Term::Projection(inner) => term_denotation(op, inner, x).map(|v| op.project(v)),
        Term::Composition(outer, inner) => {
            let v = term_denotation(op, inner, x)?;
            term_denotation(op, outer, v)
        }
        Term::CanonicalForm(inner) => op.canonical_fixpoint(term_denotation(op, inner, x)?),
    }
}

/// **Denotational term equality** — `t₁ = t₂ ⟺ ∀x ∈ 𝒰_M : ⟦t₁⟧(x) = ⟦t₂⟧(x)`: CRPT's
/// own mathematical identity, pointwise over the finite universe (decidable by
/// `Finite-Collapse`). This is the consistent reading of Enc-1's conclusion.
pub fn denotationally_equal(op: &ProjectionOperator, t1: &Term, t2: &Term) -> bool {
    op.substrate().elements().all(|x| term_denotation(op, t1, x) == term_denotation(op, t2, x))
}

/// **L4.6.D1 (`Enc`)** — a model-supplied **admissible encoding**
/// `Enc : Terms(CRPT) × 𝒰_M → 𝒰_M`, representing CRPT-computable terms as substrate
/// elements. Admissibility = the four conditions Enc-1..Enc-4, checked exactly by the
/// `certify_enc_*` certificates over a finite term family.
pub trait AdmissibleEncoding {
    /// `Enc(t, x)` — the code of term `t` at argument `x`.
    fn enc(&self, op: &ProjectionOperator, t: &Term, x: ElementId) -> ElementId;
}

/// **(Enc-1) Injectivity on terms**: `Enc(t₁,x) ≃_M Enc(t₂,x) ⟹ t₁ = t₂`
/// (denotational `=`; `≃_M` regime-aware via `π_sem`). Checked over the given finite term
/// family and points. Returns the first violating `(t₁ index, t₂ index, x)`, or `Ok`.
pub fn certify_enc_injective<E: AdmissibleEncoding>(
    op: &ProjectionOperator,
    encoding: &E,
    terms: &[Term],
    points: &[ElementId],
) -> Result<(), (usize, usize, ElementId)> {
    use crate::l3::persistent::semantic_projection;
    for (i, t1) in terms.iter().enumerate() {
        for (j, t2) in terms.iter().enumerate() {
            for &x in points {
                let equivalent = semantic_projection(op, encoding.enc(op, t1, x))
                    == semantic_projection(op, encoding.enc(op, t2, x));
                if equivalent && !denotationally_equal(op, t1, t2) {
                    return Err((i, j, x));
                }
            }
        }
    }
    Ok(())
}

/// **(Enc-2) WF faithfulness**: for a term computing `proj` (denotationally equal to
/// `CFix(Var)`, RP-1) and convergent `x`: `Enc(t,x)` reduces to a normal form
/// `y ≃_M proj(x)` — i.e. `CFix(Enc(t,x)) = CFix(x)`. Returns the first violating
/// `(t index, x)`, or `Ok`.
pub fn certify_enc_wf_faithful<E: AdmissibleEncoding>(
    op: &ProjectionOperator,
    encoding: &E,
    terms: &[Term],
    points: &[ElementId],
) -> Result<(), (usize, ElementId)> {
    let proj = Term::CanonicalForm(Box::new(Term::Var));
    for (i, t) in terms.iter().enumerate() {
        if !denotationally_equal(op, t, &proj) {
            continue; // Enc-2 constrains the proj-computing terms (RP-1)
        }
        for &x in points {
            if op.canonical_fixpoint(x).is_none() {
                continue; // WF clause: x ∈ μT
            }
            if op.canonical_fixpoint(encoding.enc(op, t, x)) != op.canonical_fixpoint(x) {
                return Err((i, x));
            }
        }
    }
    Ok(())
}

/// **(Enc-3) NWF faithfulness**: for persistent `x` and a term with a total persistent
/// denotation `d` (CP-1: no finitary `CFix` inside): the infinite path from `Enc(t,x)`
/// satisfies `zₙ ≃_M proj|ₙ(x)` — stepwise `π_sem`-equivalence of the orbits of
/// `Enc(t,x)` and `d`, checked to the exact bound `(|𝒰|+1)²` (the pair-orbit in `𝒰 × 𝒰`
/// is eventually periodic within it, so prefix equality there is equality forever).
/// Returns the first violating `(t index, x, n)`, or `Ok`.
pub fn certify_enc_nwf_faithful<E: AdmissibleEncoding>(
    op: &ProjectionOperator,
    encoding: &E,
    terms: &[Term],
    points: &[ElementId],
) -> Result<(), (usize, ElementId, u32)> {
    use crate::l3::persistent::semantic_projection;
    let n = op.substrate().universe_len() + 1;
    let bound = n * n;
    for (i, t) in terms.iter().enumerate() {
        for &x in points {
            if op.canonical_fixpoint(x).is_some() {
                continue; // NWF clause: x ∈ νT
            }
            let Some(denoted) = term_denotation(op, t, x) else {
                continue; // CFix inside t undefined on ∞_M — not a CP-1 term here
            };
            let mut z = encoding.enc(op, t, x);
            let mut target = denoted;
            for step in 0..bound {
                if semantic_projection(op, z) != semantic_projection(op, target) {
                    return Err((i, x, step));
                }
                z = op.project(z);
                target = op.project(target);
            }
        }
    }
    Ok(())
}

/// **(Enc-4) Compositionality**: `Enc(t₁ ∘ t₂, x) ≃_M Enc(t₁, Enc(t₂, x))` (regime-aware
/// `≃_M` via `π_sem`), over all pairs from the family. Returns the first violating
/// `(t₁ index, t₂ index, x)`, or `Ok`.
pub fn certify_enc_compositional<E: AdmissibleEncoding>(
    op: &ProjectionOperator,
    encoding: &E,
    terms: &[Term],
    points: &[ElementId],
) -> Result<(), (usize, usize, ElementId)> {
    use crate::l3::persistent::semantic_projection;
    for (i, t1) in terms.iter().enumerate() {
        for (j, t2) in terms.iter().enumerate() {
            let composed = Term::Composition(Box::new(t1.clone()), Box::new(t2.clone()));
            for &x in points {
                let left = encoding.enc(op, &composed, x);
                let right = encoding.enc(op, t1, encoding.enc(op, t2, x));
                if semantic_projection(op, left) != semantic_projection(op, right) {
                    return Err((i, j, x));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;
    use crate::l2::projection::Model;

    #[test]
    fn canonical_projection_is_self_fixpoint() {
        // 0→2, 1→2, 2→3, 3 ∈ NF: CFix everywhere is 3; CFix(3) = 3.
        let e = [(0, 2), (1, 2), (2, 3)];
        let m = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert!(matches!(certify_self_projection_fixpoint(&op), Ok(())));
    }

    /// The tautological encoding `Enc(t, x) := ⟦t⟧(x)` (falling back to `x` where the
    /// denotation is undefined) — compositional and faithful by construction; injective
    /// only where the substrate separates denotations.
    struct Tautological;
    impl AdmissibleEncoding for Tautological {
        fn enc(&self, op: &ProjectionOperator, t: &Term, x: ElementId) -> ElementId {
            term_denotation(op, t, x).unwrap_or(x)
        }
    }

    #[test]
    fn admissible_encoding_on_a_separating_substrate() {
        // discrete substrate (all NF): every term denotes the identity, so denotational
        // term equality holds across the family and Enc-1..Enc-4 all certify.
        let s = Substrate::new(2, &[], &[]).unwrap();
        let m = crate::l2::projection::Model::from_functional_reduction(s).unwrap();
        let op = m.operator();
        let family = [
            Term::Var,
            Term::Projection(Box::new(Term::Var)),
            Term::CanonicalForm(Box::new(Term::Var)),
        ];
        let points = [ElementId(0), ElementId(1)];
        assert!(matches!(certify_enc_injective(&op, &Tautological, &family, &points), Ok(())));
        assert!(matches!(certify_enc_wf_faithful(&op, &Tautological, &family, &points), Ok(())));
        assert!(matches!(certify_enc_nwf_faithful(&op, &Tautological, &family, &points), Ok(())));
        assert!(matches!(certify_enc_compositional(&op, &Tautological, &family, &points), Ok(())));
    }

    #[test]
    fn enc_1_certificate_catches_non_injective_encodings() {
        // chain 0→1 (NF 1): Var and ρ(Var) denote 0 and 1 — distinct denotations in the
        // SAME fiber, so the tautological codes are ≃_M-equal: Enc-1 is violated and the
        // certificate reports it exactly.
        let e = [(0, 1)];
        let s = Substrate::new(2, &e, &e).unwrap();
        let m = crate::l2::projection::Model::from_functional_reduction(s).unwrap();
        let op = m.operator();
        let family = [Term::Var, Term::Projection(Box::new(Term::Var))];
        assert_eq!(
            certify_enc_injective(&op, &Tautological, &family, &[ElementId(0)]),
            Err((0, 1, ElementId(0)))
        );
    }

    #[test]
    fn enc_3_traces_the_persistent_path_stepwise() {
        // pure cycle 0 ⇄ 1: Enc-3's infinite path zₙ ≃ proj|ₙ(x), certified stepwise to
        // the exact pair-orbit bound.
        let e = [(0, 1), (1, 0)];
        let s = Substrate::new(2, &e, &e).unwrap();
        let m = crate::l2::projection::Model::from_functional_reduction(s).unwrap();
        let op = m.operator();
        let family = [Term::Var, Term::Projection(Box::new(Term::Var))];
        let points = [ElementId(0), ElementId(1)];
        assert!(matches!(certify_enc_nwf_faithful(&op, &Tautological, &family, &points), Ok(())));
        // and the fixpoint constructor is honestly partial on ∞_M:
        let cfix = Term::CanonicalForm(Box::new(Term::Var));
        assert_eq!(term_denotation(&op, &cfix, ElementId(0)), None);
    }
}
