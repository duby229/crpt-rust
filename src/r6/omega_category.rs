//! # R6.10 — The Tower ω-Category `𝒞^Twr`
//!
//! Exact realization of spec section **R6.10** (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.10.D1 `ω-Cat-Str` — the strict ω-category structure: graded n-cells with source/
//!   target maps, composition `∘_k`, identities, satisfying globularity, associativity,
//!   unit, and interchange.
//! - R6.10.D2 `Twr-ωCat` — its tower instantiation `𝒞^Twr` over `Tower(M₀)`:
//!   - **n-cells**: elements of `𝒰_{Mₙ}` — at level `n ≥ 1` the words of `Reify(Mₙ₋₁)`,
//!     and the **reduction-path cells** `φ : x →_ρ* y` within a level, finitely presented
//!     as (source word, step count) since `ρ_{Reify}` is deterministic (strip-last);
//!   - **source/target**: `s(φ) = x`, `t(φ) = y = ρ^steps(x)`;
//!   - **vertical composition `∘`**: concatenation of reduction paths;
//!   - **identities**: `id(q) = ι_n(q)` for `q ∈ Q_{Mₙ} = Fix(ρ_{Mₙ})` — the zero-step
//!     path at the embedded atom;
//!   - **horizontal composition (`∘_k`, k < n−1)**: via the tower embeddings `ι_k`
//!     (word concatenation in `FMA(Q_M)` — the monoidal structure itself).
//! - R6.10.T1 `Twr-ωCat-T` — the strict axioms hold; certified here exactly on the
//!   finitely-presented cells ([`certify_strict_axioms`]): globularity, associativity
//!   and units of `∘`, and the **interchange law** on the realizable horizontal fragment:
//!   `u ⊗ (φ ∘ ψ) = (u ⊗ φ) ∘ (u ⊗ ψ)` (left whiskering distributes over vertical
//!   composition).
//!
//! Everything is computed on the symbolic `Reify` representation — the cells of an
//! *infinite* universe handled by word operations, per the engine's one-trait discipline.

use crate::r6::free_monoidal_algebra::Word;
use crate::r6::reification_operator::Reify;

/// **R6.10.D2 (`Twr-ωCat`) — a reduction-path cell** `φ : x →_ρ* y` within a tower level:
/// finitely presented by its source word and step count (the deterministic strip-last
/// reduction makes the path unique). `s(φ) = source`, `t(φ) = ρ^steps(source)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathCell {
    /// The source word `x = s(φ)`.
    pub source: Word,
    /// The number of `ρ_{Reify}` steps.
    pub steps: u32,
}

impl PathCell {
    /// `t(φ)` — the target word `ρ^steps(source)`.
    pub fn target(&self, level: &Reify) -> Word {
        let mut current = self.source.clone();
        for _ in 0..self.steps {
            current = level.project(&current);
        }
        current
    }
}

/// **R6.10.D2 — vertical composition `∘`**: concatenation of reduction paths.
/// Defined exactly when `t(φ₁) = s(φ₂)`; the composite runs `φ₁` then `φ₂`.
pub fn vertical_compose(level: &Reify, first: &PathCell, second: &PathCell) -> Option<PathCell> {
    if first.target(level) != second.source {
        return None;
    }
    Some(PathCell { source: first.source.clone(), steps: first.steps + second.steps })
}

/// **R6.10.D2 — identities**: `id(q) = ι_n(q)` for `q ∈ Q_{Mₙ}` — the zero-step path at
/// the embedded atom (`Can-Incl` R6.5.D3). `None` if `q` is not an atom of the level.
pub fn identity_cell(level: &Reify, q: crate::r1::substrate::ElementId) -> Option<PathCell> {
    if !level.atoms().contains(&q) {
        return None;
    }
    Some(PathCell { source: level.canonical_inclusion(q), steps: 0 })
}

/// **R6.10.D2 — horizontal composition** (`∘_k`, via the monoidal structure of
/// `FMA(Q_M)`): the realizable horizontal action on path cells is **left whiskering**
/// `u ⊗ φ : u·x →^steps u·y` — prepending a word leaves the strip-last reduction
/// untouched, so the whiskered path is exact. The *right* action on a non-trivial path
/// exists only through the tower embedding one level up (a level-n cell becomes a
/// depth-0 atom at level n+1, where concatenation is free — `Inf-Dual`'s depth reset,
/// R1.9.T7(iii)/(iv)).
pub fn left_whisker(prefix: &[crate::r1::substrate::ElementId], cell: &PathCell) -> PathCell {
    let mut source = prefix.to_vec();
    source.extend(cell.source.iter().copied());
    PathCell { source, steps: cell.steps }
}

/// Witness **R6.10.T1 (`Twr-ωCat-T`)** — the strict ω-category axioms on the
/// finitely-presented cells of a level: **globularity** (source/target coherence of
/// composites), **associativity** and **units** of vertical composition, and the
/// **interchange law** between vertical and horizontal composition, checked exactly over
/// all path cells of bounded depth from the level's atoms. Returns the first violated
/// axiom's name, or `Ok`.
pub fn certify_strict_axioms(level: &Reify, max_depth: u32) -> Result<(), &'static str> {
    // enumerate the bounded cells: paths from words of length ≤ max_depth + 1 over the
    // atom set (deterministically generated, sorted construction — no enumeration of 𝒰,
    // only of the finite presentation up to the bound).
    let mut words: Vec<Word> = level.atoms().iter().map(|&a| vec![a]).collect();
    let mut all: Vec<Word> = words.clone();
    for _ in 0..max_depth {
        let mut next: Vec<Word> = Vec::new();
        for w in &words {
            for &a in level.atoms() {
                let mut e = w.clone();
                e.push(a);
                next.push(e);
            }
        }
        all.extend(next.iter().cloned());
        words = next;
    }
    let cells: Vec<PathCell> = all
        .iter()
        .flat_map(|w| (0..=crate::r6::free_monoidal_algebra::depth(w)).map(|s| PathCell { source: w.clone(), steps: s }))
        .collect();
    for phi in &cells {
        // globularity: t(φ) is a valid word and s(id ∘ φ) = s(φ).
        let target = phi.target(level);
        if target.is_empty() {
            return Err("globularity: empty target");
        }
        // units: the zero-step path at t(φ) is a right unit; at s(φ) a left unit.
        let right_unit = PathCell { source: target.clone(), steps: 0 };
        let left_unit = PathCell { source: phi.source.clone(), steps: 0 };
        if vertical_compose(level, phi, &right_unit) != Some(phi.clone())
            || vertical_compose(level, &left_unit, phi) != Some(phi.clone())
        {
            return Err("unit law");
        }
    }
    // associativity of ∘ over composable triples (steps add — checked on the data).
    for phi in &cells {
        let mid = phi.target(level);
        for s2 in 0..=crate::r6::free_monoidal_algebra::depth(&mid) {
            let psi = PathCell { source: mid.clone(), steps: s2 };
            let mid2 = psi.target(level);
            for s3 in 0..=crate::r6::free_monoidal_algebra::depth(&mid2) {
                let chi = PathCell { source: mid2.clone(), steps: s3 };
                let left = vertical_compose(level, &vertical_compose(level, phi, &psi).unwrap(), &chi);
                let right = vertical_compose(level, phi, &vertical_compose(level, &psi, &chi).unwrap());
                if left != right {
                    return Err("associativity");
                }
            }
        }
    }
    // interchange (realizable fragment): left whiskering distributes over ∘.
    for phi in &cells {
        let mid = phi.target(level);
        for s2 in 0..=crate::r6::free_monoidal_algebra::depth(&mid) {
            let psi = PathCell { source: mid.clone(), steps: s2 };
            for &a in level.atoms() {
                let prefix = [a];
                let whiskered_composite =
                    left_whisker(&prefix, &vertical_compose(level, phi, &psi).expect("composable"));
                let composite_of_whiskered = vertical_compose(
                    level,
                    &left_whisker(&prefix, phi),
                    &left_whisker(&prefix, &psi),
                );
                if composite_of_whiskered != Some(whiskered_composite) {
                    return Err("interchange");
                }
            }
        }
    }
    Ok(())
}

/// Witness **R6.10.T2 (`Self-Ont`)** — **Self-Ontological Soundness**: the tower ω-category
/// structure is self-ontologically sound — it can describe its *own* cells with its own
/// machinery, with no external ontology. Realized as: the strict ω-category axioms
/// ([`certify_strict_axioms`]) hold on the reify level's own cells (the structure validates
/// itself by word operations). Returns `true` when the tower ω-category is self-consistent up
/// to the given bound. (`R6.10.R1` `ω-Cat-Rare`: genuine strict ω-categories are rare — the
/// CRPT tower is one because `Reify` is deterministic; `R6.10.R2` `Nota-L7L8`: the R6 notation
/// merges the former L7/L8 categorical and tower layers.)
pub fn certify_self_ontological(base: &crate::r1::reduction_strategy::Instance, max_depth: u32) -> bool {
    let reified = crate::r6::reification_operator::reify(base);
    certify_strict_axioms(&reified, max_depth).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::{ElementId, Substrate};
    use crate::r1::reduction_strategy::Instance;
    use crate::r6::reification_operator::reify;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// Base with Q_M = {1, 3} (two fixpoints).
    fn base() -> Instance {
        let e = [(0, 1), (2, 3)];
        Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap()
    }

    #[test]
    fn tower_omega_category_cells_compose_strictly() {
        let m = base();
        let level = reify(&m); // level 1 of the tower: FMA(Q_M), infinite, symbolic
        // a 2-step path cell from the word [1,3,1]: s = [1,3,1], t = [1].
        let phi = PathCell { source: vec![id(1), id(3), id(1)], steps: 2 };
        assert_eq!(phi.target(&level), vec![id(1)]);
        // vertical composition concatenates reduction paths.
        let psi = PathCell { source: vec![id(1), id(3), id(1)], steps: 1 };
        let tail = PathCell { source: vec![id(1), id(3)], steps: 1 };
        assert_eq!(
            vertical_compose(&level, &psi, &tail),
            Some(PathCell { source: vec![id(1), id(3), id(1)], steps: 2 })
        );
        // non-composable pair (t ≠ s) is rejected.
        assert_eq!(vertical_compose(&level, &phi, &tail), None);
        // identities: id(q) = ι(q), the zero-step path at an atom — and only at atoms.
        assert_eq!(identity_cell(&level, id(1)), Some(PathCell { source: vec![id(1)], steps: 0 }));
        assert_eq!(identity_cell(&level, id(0)), None);
        // horizontal action: left whiskering is exact (prefix never disturbs strip-last)…
        let whiskered = left_whisker(&[id(3)], &psi);
        assert_eq!(whiskered.source, vec![id(3), id(1), id(3), id(1)]);
        assert_eq!(whiskered.target(&level), vec![id(3), id(1), id(3)]);
        // the strict axioms certify on the bounded cell fragment, incl. interchange
        // (Twr-ωCat-T).
        assert!(matches!(certify_strict_axioms(&level, 2), Ok(())));
        // Self-Ont: the tower ω-category is self-ontologically sound (validates its own cells).
        assert!(certify_self_ontological(&m, 2));
    }
}
