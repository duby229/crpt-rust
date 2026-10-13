//! # L8.2 — The Lift Operator
//!
//! Exact realization of spec section **L8.2** (`CRPT_OMEGA_TOWER_L8.md`, v1.0.0-rc4):
//!
//! - L8.2.D1/D2 `Lift-Def` — `Lift(M) := (FMA(Q_M), →_ρ^{Lift}, →_σ^{Lift}, ρ_{Lift(M)})`,
//!   the free lift of M. Its atom set is `Q_M` (the abstraction quotient = the
//!   fixpoints reached, L2.5/L8.2), and its universe `FMA(Q_M)` is infinite — so
//!   `Lift(M)` is represented **symbolically** (operations on words), not materialized.
//! - L8.1.D2 `FMA-Proj` (rc3 convention) — `ρ_{Lift(M)}` strips the **last atom** each
//!   step; the orbit shrinks the word to its **first atom**, the canonical form.
//! - L8.2.T1 `Fix-Bas` — `Fix(ρ_{Lift(M)})` = the atoms (length-1 words) = `Q_M`
//!   (fixpoints-to-basics).
//! - L8.2.C1 `Lift-Depth` — `d_{Lift(M)}(w) = |w| − 1`.
//! - L8.10.C2 `Lift-Pure-WF` — every `Lift(M)` is **pure-WF**: every word reaches its
//!   atom in `|w|−1` steps, so `∞_{Lift(M)} = ∅`.

use crate::l1::substrate::ElementId;
use crate::l2::projection::Model;
use crate::l8::fma::{depth, Word};

/// **L8.2.D2 (`Lift-Def`)** — the free lift `Lift(M)`. Holds the atom set `Q_M` (the
/// fixpoints reached by ρ_M); its universe `FMA(Q_M)` is the infinite set of words
/// over those atoms, handled symbolically.
pub struct Lift {
    atoms: Vec<ElementId>, // Q_M = the base model's fixpoints (ascending)
}

/// **L8.2.D2 (`Lift-Def`)**: `Lift(M)` — extract the atom set `Q_M = Fix(ρ_M)` of the
/// base model. (For a WF model the reachable fixpoints are exactly `Fix(ρ_M)`.)
pub fn lift(base: &Model) -> Lift {
    Lift { atoms: base.operator().fixpoints() }
}

impl Lift {
    /// The atom set `Q_M` of the lift (the base model's fixpoints), ascending.
    pub fn atoms(&self) -> &[ElementId] {
        &self.atoms
    }

    /// `|Q_M|` — the number of atoms (the query-signature size, invariant up the tower).
    pub fn atom_count(&self) -> u32 {
        self.atoms.len() as u32
    }

    /// Whether `a` is an atom of the lift (a ∈ `Q_M`).
    pub fn is_atom(&self, a: ElementId) -> bool {
        self.atoms.binary_search_by_key(&a.0, |e| e.0).is_ok()
    }

    /// **L8.1.D2 (`FMA-Proj`)** — `ρ_{Lift(M)}(w)`: strip the rightmost atom. An atom
    /// (length-1 word) is a fixpoint and maps to itself.
    pub fn project(&self, word: &[ElementId]) -> Word {
        if word.len() <= 1 {
            word.to_vec()
        } else {
            word[..word.len() - 1].to_vec()
        }
    }

    /// **L8.2.D3 (`Can-Incl`)** — the canonical inclusion `ι_M : Q_M ↪ FMA(Q_M)`, sending
    /// each abstraction class `q ∈ Q_M` to the one-atom word `atom(q)`. Injective (`FMA-UD`
    /// L8.1.L2); it embeds M's canonical observables as the atoms of `Lift(M)`.
    pub fn canonical_inclusion(&self, q: ElementId) -> Word {
        vec![q]
    }

    /// **L8.2.T1 (`Fix-Bas`)** — whether `w ∈ Fix(ρ_{Lift(M)})`, i.e. `w` is an atom
    /// (a length-1 word). Fix(ρ_{Lift(M)}) ≅ `Q_M`.
    pub fn is_fixpoint(&self, word: &[ElementId]) -> bool {
        word.len() == 1
    }

    /// **L8.1.D2 / Rec-Proj** — `CFix(w)`: the canonical form the orbit reaches — the
    /// word's **first atom** (stripping rightmost atoms down to `w[0]`).
    pub fn canonical_form(&self, word: &[ElementId]) -> Word {
        vec![word[0]]
    }

    /// **L8.2.C1 (`Lift-Depth`)** — `d_{Lift(M)}(w) = |w| − 1`.
    pub fn depth(&self, word: &[ElementId]) -> u32 {
        depth(word)
    }

    /// Witness **L8.10.C2 (`Lift-Pure-WF`)** on a word: the ρ_{Lift(M)}-orbit of `w`
    /// terminates at an atom (length-1 word) in exactly `|w|−1` steps — so `w ∈ ↓`.
    /// Returns the canonical atom reached.
    pub fn certify_converges(&self, word: &[ElementId]) -> Word {
        let mut current = word.to_vec();
        let mut steps = 0u32;
        while !self.is_fixpoint(&current) {
            current = self.project(&current);
            steps += 1;
        }
        debug_assert_eq!(steps, depth(word));
        current
    }
}

/// **L0.5.D1 (`TowerLift`) — the lift of a projection system *is* a projection system**:
/// `Lift(Π) = (𝒰', π', →_σ')`. `Lift(M)` implements the *same*
/// [`ProjectionSystem`](crate::l0::projection_system::ProjectionSystem) trait as the finite
/// operator `ρ_M` — one notion, recursed one level up (`Mₙ₊₁ := Lift(Mₙ)`, L8.4.D1). Its
/// universe `FMA(Q_M)` is infinite, yet `π'`, `Fix`, `d_π`, `CFix`, and the structural
/// horizon are all computed by **operations on words** — never enumeration: every word
/// converges (pure-WF), and the π'-kernel of `w` is `{w·a : a ∈ Q_M}`, finitely presented.
impl crate::l0::projection_system::ProjectionSystem for Lift {
    type Point = Word;

    fn projection(&self, x: &Word) -> Word {
        Lift::project(self, x) // π' = ρ_{Lift(M)}: strip the last atom
    }

    fn projection_depth(&self, x: &Word) -> Option<u32> {
        Some(Lift::depth(self, x)) // d_{π'}(a₁·…·aₙ) = n − 1 (L0.5.D1); every word converges
    }

    fn preimage_size(&self, y: &Word) -> Option<u32> {
        // π'⁻¹(y) = {y·a : a ∈ Q_M} (strip-last is inverse-append), plus y itself when y is
        // an atom (a π'-fixpoint). Finite — |Q_M| (+1) — though the universe is infinite.
        Some(self.atom_count() + if Lift::is_fixpoint(self, y) { 1 } else { 0 })
    }

    fn is_projection_fixpoint(&self, x: &Word) -> bool {
        Lift::is_fixpoint(self, x) // Fix(π') = the atoms 𝒰/≃_π (L0.5.D1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;
    use crate::l0::projection_system::ProjectionSystem;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// Base model with two fixpoints: 0→1 (1 ∈ NF), 2→3 (3 ∈ NF). Q_M = {1,3}.
    fn two_fixpoint_base() -> Model {
        let e = [(0, 1), (2, 3)];
        Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap()
    }

    #[test]
    fn lift_atoms_are_the_base_fixpoints() {
        let l = lift(&two_fixpoint_base());
        assert_eq!(l.atoms(), &[id(1), id(3)]); // Q_M
        assert_eq!(l.atom_count(), 2);
        assert!(l.is_atom(id(1)) && l.is_atom(id(3)) && !l.is_atom(id(0)));
    }

    #[test]
    fn projection_strips_to_the_first_atom() {
        let l = lift(&two_fixpoint_base());
        let w = vec![id(1), id(3), id(1)]; // a word over Q_M
        assert_eq!(l.depth(&w), 2);
        assert!(!l.is_fixpoint(&w));
        // ρ strips the rightmost atom: [1,3,1] → [1,3] → [1] (fixpoint).
        assert_eq!(l.project(&w), vec![id(1), id(3)]);
        assert_eq!(l.project(&l.project(&w)), vec![id(1)]);
        assert!(l.is_fixpoint(&l.project(&l.project(&w))));
        // CFix is the first atom.
        assert_eq!(l.canonical_form(&w), vec![id(1)]);
        // pure-WF: the orbit terminates at that atom in depth(w) steps.
        assert_eq!(l.certify_converges(&w), vec![id(1)]);
    }

    #[test]
    fn the_lift_of_a_projection_system_is_a_projection_system() {
        // TowerLift (L0.5.D1): Lift(M) over Q_M = {1,3} is an instance of the SAME
        // ProjectionSystem trait as ρ_M itself. Its universe FMA(Q_M) is INFINITE; every
        // construct below is computed by word operations, never by enumeration.
        let l = lift(&two_fixpoint_base());
        let w = vec![id(1), id(3), id(1)]; // a word
        // π' = strip-last; d_π'(w) = |w| − 1; CFix = the recursive projection (Rec-Proj).
        assert_eq!(l.projection(&w), vec![id(1), id(3)]);
        assert_eq!(l.projection_depth(&w), Some(2));
        assert!(ProjectionSystem::is_convergent(&l, &w));
        assert!(!ProjectionSystem::is_persistent(&l, &w));
        assert_eq!(ProjectionSystem::canonical_form(&l, &w), Some(vec![id(1)]));
        // the π'-kernel is finitely presented: |π'⁻¹([1,3])| = |Q_M| = 2 (the words
        // [1,3,1] and [1,3,3]) — computed without listing the infinitely many words.
        assert_eq!(l.preimage_size(&vec![id(1), id(3)]), Some(2));
        // the structural horizon, computed symbolically on the infinite substrate.
        assert_eq!(ProjectionSystem::structural_horizon(&l, &w), Some(true));
    }

    #[test]
    fn atoms_are_fixpoints() {
        let l = lift(&two_fixpoint_base());
        let atom = vec![id(3)];
        assert!(l.is_fixpoint(&atom));
        assert_eq!(l.depth(&atom), 0);
        assert_eq!(l.project(&atom), atom);
        assert_eq!(l.canonical_form(&atom), atom);
    }
}
