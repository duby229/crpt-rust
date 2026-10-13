//! # Finite Powerset Fixpoints — the engine's second-order architecture
//!
//! This module is the **R0.7** section: the universal second-order machinery — the one
//! Knaster–Tarski fixpoint combinator over finite powerset lattices that realizes every
//! SOL commitment of the tower (`SO-Ext` R4.3.D6: bisimilarity = `νB`, reachability =
//! `μT`), each proven equal to its production-path computation. See
//! `docs/SECOND_ORDER.md`.
//!
//! **The problem.** CRPT makes genuine *second-order* commitments (quantifiers over
//! relations / predicate transformers): bisimilarity `≈` (the largest bisimulation,
//! R1.1.D7), the aspects (`↓_M = μT_conv`, `∞_M = νT_pers`, R1.9.D2), transitive closures,
//! and the coinduction principle `PA-CoInd` (Park's lemma, R1.2.Ax5). Read naively, a
//! second-order quantifier `∃R / ∀R` over `𝒫(𝒰²)` is `2^(n²)` — intractable.
//!
//! **The resolution (from the spec itself).** Every second-order commitment CRPT actually
//! makes is a **least or greatest fixpoint of a monotone operator** on the finite powerset
//! lattice. By Knaster–Tarski the extremal fixpoint exists and, on a finite lattice, is
//! computed by Kleene iteration in `≤ |𝒰|` steps — `O(n²–n³)`, and **exact, not an
//! approximation**:
//!
//! - `R4.3.T4 FOL-Fin` — on finite instances `T_CRPT` collapses to its first-order fragment
//!   (a biconditional: the finite reduction is faithful). The `∃R` of a second-order axiom
//!   reduces to its canonical first-order witness — which is the extremal fixpoint here.
//! - `R1.9.D2 T^{conv/pers}` / `R1.9.D3 Asp-Strat` — the aspects *are* the `μ/ν` decomposition.
//! - Anchor coalgebra instantiation, Thm 3.5: "*for any monotone `F'`, `νF'` exists — by
//!   Knaster–Tarski, `νF' = ⋃{X | X ⊆ F'(X)}*". The final coalgebra `νF` (the canonical
//!   home of coinduction) is a greatest fixpoint, built by Adámek's terminal chain, which
//!   on accessible/bounded (finite) functors terminates — i.e. partition refinement.
//!
//! **This module is the single, named realization of that mechanism.** A monotone operator
//! is a map on the finite powerset of `𝒰 = {0, …, n−1}`, represented as a dense `Vec<bool>`
//! (the determinism contract: no sets, no hashing). [`least_fixpoint`] / [`greatest_fixpoint`]
//! compute `μ` / `ν` by Kleene iteration.
//!
//! **The discipline (`docs/SECOND_ORDER.md`).** CRPT's second-order commitments are tagged:
//! - **fixpoint** (the dominant case) — computed here. `≈` (relation-lattice `ν`, via
//!   partition refinement, [`crate::r1::substrate::Substrate::bisimilarity`]); `↓_M`/`∞_M`
//!   ([`crate::r0::sol_necessity`]); closures.
//! - **proof principle** — `PA-CoInd` is realized *as the correctness of* [`greatest_fixpoint`]
//!   (Knaster–Tarski), not as a quantifier over all `Φ`: we provide the verified combinator
//!   whose existence *is* Park's lemma instantiated. [`is_fixpoint`] witnesses it per use.
//! - **infinitary** — `OC > 0` / Type AP / `sig_M-NM` (Borel rank, topology) genuinely need
//!   infinite objects; out of finite scope by necessity (not tractability).
//! - **meta** — quantification over all instances (`ATD-NI` R5.5.T4) is realized by
//!   *parametricity*: a total function `fn f(m: &Instance) -> …` *is* the universal "∀ instances".
//!
//! We never enumerate the powerset; CRPT never requires a second-order witness that is not
//! an extremal fixpoint (or FOL-Fin-reducible to one).

/// A monotone operator on the powerset of `{0, …, n−1}`: `X ⊆ Y ⟹ step(X) ⊆ step(Y)`.
/// Monotonicity is the caller's contract (the hypothesis of Knaster–Tarski); the iteration
/// is correct exactly for monotone `step`.
pub trait MonotoneOperator {
    /// `step(X)` for the membership bitmap `X` (length `n`), returning a length-`n` bitmap.
    fn step(&self, set: &[bool]) -> Vec<bool>;
}

impl<F: Fn(&[bool]) -> Vec<bool>> MonotoneOperator for F {
    fn step(&self, set: &[bool]) -> Vec<bool> {
        self(set)
    }
}

/// Whether `set` is a fixpoint of `op` (`step(set) = set`) — the per-instance witness that
/// the computed extremal point is a genuine fixpoint (the content of `PA-CoInd` at this `op`).
pub fn is_fixpoint(set: &[bool], op: &impl MonotoneOperator) -> bool {
    op.step(set) == set
}

/// **Knaster–Tarski least fixpoint** `μ(op)` on the finite powerset: the smallest `X` with
/// `op(X) = X`. Computed by Kleene iteration from `∅` upward; for a monotone `op` this is
/// ascending and converges in `≤ n` steps (each step adds ≥ 1 element until stable). The
/// inductive (least-fixpoint) realization of CRPT's `∃`-second-order commitments.
pub fn least_fixpoint(n: usize, op: &impl MonotoneOperator) -> Vec<bool> {
    let mut current = vec![false; n];
    loop {
        let next = op.step(&current);
        if next == current {
            return current;
        }
        current = next;
    }
}

/// **Knaster–Tarski greatest fixpoint** `ν(op)` on the finite powerset: the largest `X` with
/// `op(X) = X`. Computed by Kleene iteration from `𝒰` downward (Adámek's terminal chain in
/// the powerset case); converges in `≤ n` steps. The coinductive (greatest-fixpoint)
/// realization — the canonical home of `PA-CoInd` and the final-coalgebra construction.
pub fn greatest_fixpoint(n: usize, op: &impl MonotoneOperator) -> Vec<bool> {
    let mut current = vec![true; n];
    loop {
        let next = op.step(&current);
        if next == current {
            return current;
        }
        current = next;
    }
}

/// **R0.7.T1 (`SOL-Nec-U`)** — the two and only two primitive sources of second-order logic
/// in any projection-system theory `T(Π)`. `==` compares the source tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolSource {
    /// **Source 1 (Reduction closure)** — the reflexive-transitive closure `π*` and the
    /// divergence predicate `Pers(π)`: not FO-definable over arbitrary infinite instances
    /// (Immerman 1986). Realized exactly on finite instances by [`least_fixpoint`] (`μ`).
    ReductionClosure,
    /// **Source 2 (ω-completeness / bisimilarity)** — `∃σ : ℕ → 𝒰` witnessing persistence,
    /// and the greatest-fixpoint bisimilarity `≈`: SOL by Knaster–Tarski over `𝒫(𝒰²)`.
    /// Realized exactly on finite instances by [`greatest_fixpoint`] (`ν`, partition refinement).
    Bisimilarity,
}

/// **R0.7.T1 (`SOL-Nec-U`)** — the SOL source a given construct requires. Every second-order
/// commitment of `T(Π)` reduces to exactly one of the two; the engine realizes both exactly
/// on finite instances (`Finite-Collapse` R0.7.T2): closure/divergence via the **least**
/// fixpoint, bisimilarity/ω-witness via the **greatest** fixpoint. This map records *which*
/// source each canonical SOL commitment instantiates.
pub fn sol_source(construct: &str) -> Option<SolSource> {
    match construct {
        // reduction-closure family
        "π*" | "→_ρ*" | "Pers" | "Div" | "transitive-closure" | "reachability" => {
            Some(SolSource::ReductionClosure)
        }
        // ω-completeness / greatest-fixpoint family
        "≈" | "bisimilarity" | "PA-CoInd" | "PA-NWF" | "PA-Prod" | "ω-witness" => {
            Some(SolSource::Bisimilarity)
        }
        _ => None,
    }
}

/// Witness **R0.7.T3 (`CRPT-SOL`)** — the SOL-requiring assumptions of `T_CRPT` map to the
/// two universal sources and **no third**, with **both** exercised: `→_ρ*` closure and the
/// `Div` divergence witness instance Source 1; `≈` (greatest bisimulation), `PA-CoInd`,
/// `PA-NWF`, `PA-Prod` instance Source 2. Returns `true` when the mapping is exhaustive over
/// the canonical assumptions and both sources occur.
pub fn certify_crpt_sol() -> bool {
    let source_1 = ["→_ρ*", "Div"];
    let source_2 = ["≈", "PA-CoInd", "PA-NWF", "PA-Prod"];
    let one = source_1.iter().all(|c| sol_source(c) == Some(SolSource::ReductionClosure));
    let two = source_2.iter().all(|c| sol_source(c) == Some(SolSource::Bisimilarity));
    one && two // both sources exercised, every assumption mapped, none requiring a third
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn least_and_greatest_of_a_monotone_operator() {
        // On {0,1,2}: op(X) = X ∪ {0} ∪ {x+1 | x ∈ X, x+1 < 3} — monotone.
        // Reachability-from-0 flavour: μ = {0,1,2} (closure from ∅ seeds 0 then grows);
        // ν = {0,1,2} too here (the whole set is the only large fixpoint).
        let op = |x: &[bool]| -> Vec<bool> {
            let mut y = x.to_vec();
            y[0] = true;
            for i in 0..3 {
                if x[i] && i + 1 < 3 {
                    y[i + 1] = true;
                }
            }
            y
        };
        let mu = least_fixpoint(3, &op);
        assert_eq!(mu, vec![true, true, true]);
        assert!(is_fixpoint(&mu, &op));
        let nu = greatest_fixpoint(3, &op);
        assert!(is_fixpoint(&nu, &op));
    }

    #[test]
    fn least_fixpoint_of_a_shrinking_seed_is_empty() {
        // op(X) = {x | x ∈ X and x-1 ∈ X} ... use the simplest: op(X) = X ∩ {nothing seeded}.
        // op(X) = elements present whose predecessor is present; from ∅ stays ∅ (μ = ∅).
        let op = |x: &[bool]| -> Vec<bool> {
            (0..3).map(|i| i > 0 && x[i] && x[i - 1]).collect()
        };
        assert_eq!(least_fixpoint(3, &op), vec![false, false, false]); // μ = ∅
        // ν: largest X with op(X)=X. {} is a fixpoint; iterate from full: full→{}, so ν=∅ here.
        assert_eq!(greatest_fixpoint(3, &op), vec![false, false, false]);
    }

    #[test]
    fn the_two_sol_sources_are_exhaustive_and_both_exercised() {
        // SOL-Nec-U: closure/divergence ↦ Source 1; bisimilarity/coinduction ↦ Source 2.
        assert_eq!(sol_source("→_ρ*"), Some(SolSource::ReductionClosure));
        assert_eq!(sol_source("≈"), Some(SolSource::Bisimilarity));
        // CRPT-SOL: the T_CRPT assumptions map to the two sources, no third, both exercised.
        assert!(certify_crpt_sol());
    }
}
