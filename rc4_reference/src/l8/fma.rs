//! # L8.1 — The Free Monoidal Algebra FMA(A)
//!
//! Exact realization of spec section **L8.1** (`CRPT_OMEGA_TOWER_L8.md`, v1.0.0-rc4):
//!
//! - L8.1.D1 `FMA-Def` — `FMA(A)` is the free monoid of finite words over the atom
//!   set A. A [`Word`] is a non-empty finite sequence of atoms.
//! - L8.1.L2 `FMA-Unique` — unique decomposition: a word *is* its sequence of atoms,
//!   so [`atoms_of`] is the identity read of that decomposition.
//! - The monoid product is concatenation ([`concat()`]); FMA is graded by flat word
//!   length, `depth(w) = |w| − 1` (L8.1.D1 / L8.2.C1 `Lift-Depth`, rc3).
//!
//! FMA(A) is *infinite* even for finite A (all finite words), so it is never
//! materialized as a [`crate::l2::projection::Model`]: it is handled symbolically,
//! word by word.

use crate::l1::substrate::ElementId;

/// **L8.1.D1 (`FMA-Def`)** — a word of `FMA(A)`: a non-empty finite sequence of atoms,
/// each atom an [`ElementId`] of the atom set A (here `A = Q_M`, see [`crate::l8::lift`]).
pub type Word = Vec<ElementId>;

/// **L8.2.C1 (`Lift-Depth`)** — `depth(w) = |w| − 1`: the number of Lift-reduction
/// steps from `w` down to its atom. (A single atom has depth 0.)
pub fn depth(word: &[ElementId]) -> u32 {
    (word.len() as u32).saturating_sub(1)
}

/// **L8.1.L2 (`FMA-Unique`)** — the unique atom decomposition of a word (the word
/// itself, as a sequence of atoms).
pub fn atoms_of(word: &[ElementId]) -> &[ElementId] {
    word
}

/// **L8.1.D1** — the monoid product of `FMA(A)`: concatenation `u · v`.
pub fn concat(u: &[ElementId], v: &[ElementId]) -> Word {
    let mut w = Vec::with_capacity(u.len() + v.len());
    w.extend_from_slice(u);
    w.extend_from_slice(v);
    w
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
