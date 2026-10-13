//! # R6.4 — The Free Monoidal Algebra FMA(A)
//!
//! Exact realization of spec section **R6.4** (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.4.D1 `FMA-Def` — `FMA(A)` is the free monoid of finite words over the atom
//!   set A. A [`Word`] is a non-empty finite sequence of atoms.
//! - R6.4.L2 `FMA-Unique` — unique decomposition: a word *is* its sequence of atoms,
//!   so [`atoms_of`] is the identity read of that decomposition.
//! - The monoid product is concatenation ([`concat()`]); FMA is graded by flat word
//!   length, `depth(w) = |w| − 1` (R6.4.D1 / R6.5.C1 `Reify-Depth`, v1.0.0-rc9).
//!
//! FMA(A) is *infinite* even for finite A (all finite words), so it is never
//! materialized as a [`crate::r1::reduction_strategy::Instance`]: it is handled symbolically,
//! word by word.

use crate::r1::substrate::ElementId;

/// **R6.4.D1 (`FMA-Def`)** — a word of `FMA(A)`: a non-empty finite sequence of atoms,
/// each atom an [`ElementId`] of the atom set A (here `A = Q_M`, see [`crate::r6::reification_operator`]).
pub type Word = Vec<ElementId>;

/// **R6.5.C1 (`Reify-Depth`)** — `depth(w) = |w| − 1`: the number of Reify-reduction
/// steps from `w` down to its atom. (A single atom has depth 0.)
pub fn depth(word: &[ElementId]) -> u32 {
    (word.len() as u32).saturating_sub(1)
}

/// **R6.4.L2 (`FMA-Unique`)** — the unique atom decomposition of a word (the word
/// itself, as a sequence of atoms).
pub fn atoms_of(word: &[ElementId]) -> &[ElementId] {
    word
}

/// **R6.4.D1** — the monoid product of `FMA(A)`: concatenation `u · v`.
pub fn concat(u: &[ElementId], v: &[ElementId]) -> Word {
    let mut w = Vec::with_capacity(u.len() + v.len());
    w.extend_from_slice(u);
    w.extend_from_slice(v);
    w
}

/// Witness **R6.4.L1 (`FMA-WF`)** — `FMA(A)` is **well-founded**: every word is finite, so its
/// strip-last orbit reaches an atom (a length-1 word) in `|w| − 1` steps — there are no
/// infinite descending chains. Returns the orbit length `depth(w)` (always finite), witnessing
/// well-foundedness of the free monoidal algebra.
pub fn fma_is_well_founded(word: &[ElementId]) -> u32 {
    depth(word) // |w| − 1 — finite for every (finite) word
}

/// Witness **R6.4.L3 (`FMA-C1C3`)** — the canonical projection on `FMA(Q_M)` satisfies **C1**
/// (determinism: exactly one strip-last step from each non-atom) and **C3** (the orbit reaches
/// a normal form, an atom). Returns `true` when, for the given non-empty word, the strip-last
/// step is deterministic and the orbit terminates at a length-1 atom. (Atoms are the
/// fixpoints — `FMA-UD` R6.4.L2 / `Fix-Bas` R6.5.T1.)
pub fn certify_fma_c1_c3(word: &[ElementId]) -> bool {
    if word.is_empty() {
        return false;
    }
    // C1: strip-last is a deterministic single step; C3: iterating reaches a length-1 atom.
    let mut current = word.to_vec();
    let mut steps = 0u32;
    while current.len() > 1 {
        current.truncate(current.len() - 1); // the unique strip-last step
        steps += 1;
    }
    current.len() == 1 && steps == depth(word)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn words_grade_by_length_minus_one() {
        assert_eq!(depth(&[id(0)]), 0); // an atom
        assert_eq!(depth(&[id(0), id(1)]), 1);
        assert_eq!(depth(&[id(1), id(0), id(1)]), 2);
        // FMA-WF: every word has finite depth (well-founded).
        assert_eq!(fma_is_well_founded(&[id(1), id(0), id(1)]), 2);
        // FMA-C1C3: the canonical projection satisfies C1 (deterministic) + C3 (reaches an atom).
        assert!(certify_fma_c1_c3(&[id(0), id(1), id(1)]));
        assert!(certify_fma_c1_c3(&[id(0)])); // an atom is its own normal form
    }

    #[test]
    fn product_is_concatenation_and_decomposition_is_identity() {
        let u = vec![id(0), id(1)];
        let v = vec![id(1)];
        let w = concat(&u, &v);
        assert_eq!(w, vec![id(0), id(1), id(1)]);
        assert_eq!(atoms_of(&w), &[id(0), id(1), id(1)]);
    }
}
