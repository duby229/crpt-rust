//! # R6.5 — The Reify Operator
//!
//! Exact realization of spec section **R6.5** (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.5.D1/D2 `Reify-Def` — `Reify(M) := (FMA(Q_M), →_ρ^{Reify}, →_σ^{Reify}, ρ_{Reify(M)})`,
//!   the free reify of M. Its atom set is `Q_M` (the abstraction quotient = the
//!   fixpoints reached, R1.12/R6.5), and its universe `FMA(Q_M)` is infinite — so
//!   `Reify(M)` is represented **symbolically** (operations on words), not materialized.
//! - R6.4.D2 `FMA-Proj` — `ρ_{Reify(M)}` strips the **last atom** each
//!   step; the orbit shrinks the word to its **first atom**, the canonical form.
//! - R6.5.T1 `Fix-Bas` — `Fix(ρ_{Reify(M)})` = the atoms (length-1 words) = `Q_M`
//!   (fixpoints-to-basics).
//! - R6.5.C1 `Reify-Depth` — `d_{Reify(M)}(w) = |w| − 1`.
//! - R6.13.C2 `Reify-Pure-WF` — every `Reify(M)` is **pure-WF**: every word reaches its
//!   atom in `|w|−1` steps, so `∞_{Reify(M)} = ∅`.

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::Instance;
use crate::r6::free_monoidal_algebra::{depth, Word};

/// **R6.5.D2 (`Reify-Def`)** — the free reify `Reify(M)`. Holds the atom set `Q_M` (the
/// fixpoints reached by ρ_M); its universe `FMA(Q_M)` is the infinite set of words
/// over those atoms, handled symbolically.
pub struct Reify {
    atoms: Vec<ElementId>, // Q_M = the base instance's fixpoints (ascending)
}

/// **R6.5.D2 (`Reify-Def`)**: `Reify(M)` — extract the atom set `Q_M = Fix(ρ_M)` of the
/// base instance. (For a WF instance the reachable fixpoints are exactly `Fix(ρ_M)`.)
pub fn reify(base: &Instance) -> Reify {
    Reify { atoms: base.operator().fixpoints() }
}

impl Reify {
    /// The atom set `Q_M` of the reify (the base instance's fixpoints), ascending.
    pub fn atoms(&self) -> &[ElementId] {
        &self.atoms
    }

    /// `|Q_M|` — the number of atoms (the query-signature size, invariant up the tower).
    pub fn atom_count(&self) -> u32 {
        self.atoms.len() as u32
    }

    /// Whether `a` is an atom of the reify (a ∈ `Q_M`).
    pub fn is_atom(&self, a: ElementId) -> bool {
        self.atoms.binary_search_by_key(&a.0, |e| e.0).is_ok()
    }

    /// **R6.4.D2 (`FMA-Proj`)** — `ρ_{Reify(M)}(w)`: strip the rightmost atom. An atom
    /// (length-1 word) is a fixpoint and maps to itself.
    pub fn project(&self, word: &[ElementId]) -> Word {
        if word.len() <= 1 {
            word.to_vec()
        } else {
            word[..word.len() - 1].to_vec()
        }
    }

    /// **R6.5.D3 (`Can-Incl`)** — the canonical inclusion `ι_M : Q_M ↪ FMA(Q_M)`, sending
    /// each abstraction class `q ∈ Q_M` to the one-atom word `atom(q)`. Injective (`FMA-UD`
    /// R6.4.L2); it embeds M's canonical observables as the atoms of `Reify(M)`.
    pub fn canonical_inclusion(&self, q: ElementId) -> Word {
        vec![q]
    }

    /// **R6.5.T1 (`Fix-Bas`)** — whether `w ∈ Fix(ρ_{Reify(M)})`, i.e. `w` is an atom
    /// (a length-1 word). Fix(ρ_{Reify(M)}) ≅ `Q_M`.
    pub fn is_fixpoint(&self, word: &[ElementId]) -> bool {
        word.len() == 1
    }

    /// **R6.4.D2 / Rec-Proj** — `CFix(w)`: the canonical form the orbit reaches — the
    /// word's **first atom** (stripping rightmost atoms down to `w[0]`).
    pub fn canonical_form(&self, word: &[ElementId]) -> Word {
        vec![word[0]]
    }

    /// **R6.5.C1 (`Reify-Depth`)** — `d_{Reify(M)}(w) = |w| − 1`.
    pub fn depth(&self, word: &[ElementId]) -> u32 {
        depth(word)
    }

    /// Witness **R6.13.C2 (`Reify-Pure-WF`)** on a word: the ρ_{Reify(M)}-orbit of `w`
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

/// **R0.5.D1 (`TowerReify`) — the reification of a projection system *is* a projection system**:
/// `Reify(Π) = (𝒰', π', →_σ')`. `Reify(M)` implements the *same*
/// [`ProjectionSystem`](crate::r0::projection_systems_and_fibers::ProjectionSystem) trait as the finite
/// operator `ρ_M` — one notion, recursed one level up (`Mₙ₊₁ := Reify(Mₙ)`, R6.7.D1). Its
/// universe `FMA(Q_M)` is infinite, yet `π'`, `Fix`, `d_π`, `CFix`, and the structural
/// horizon are all computed by **operations on words** — never enumeration: every word
/// converges (pure-WF), and the π'-kernel of `w` is `{w·a : a ∈ Q_M}`, finitely presented.
impl crate::r0::projection_systems_and_fibers::ProjectionSystem for Reify {
    type Point = Word;

    fn projection(&self, x: &Word) -> Word {
        Reify::project(self, x) // π' = ρ_{Reify(M)}: strip the last atom
    }

    fn projection_depth(&self, x: &Word) -> Option<u32> {
        Some(Reify::depth(self, x)) // d_{π'}(a₁·…·aₙ) = n − 1 (R0.5.D1); every word converges
    }

    fn is_fixpoint(&self, x: &Word) -> bool {
        Reify::is_fixpoint(self, x) // Fix(π') = the atoms 𝒰/≃_π (R0.5.D1)
    }
}

impl Reify {
    /// Witness **R6.5.T2 (`Hor-Reify`)** — **Horizon Inheritance under Reify**: the horizon
    /// class of a word `w ∈ Reify(M)` is determined by the word's structure — an **atom**
    /// (length-1 word) is a fixpoint of `ρ_{Reify(M)}` (the `H_O`/boundary data lives at depth
    /// `|w|−1`), and the structural horizon of `w` is read off its strip-last kernel
    /// `{w·a : a ∈ Q_M}`. Returns `(is_atom, depth)` — the inherited horizon datum of `w`.
    /// (`R6.5.R1` `Fix-Bas-Int`: the fixpoints-to-basics identity is internal to `FMA`;
    /// `R6.5.R2` `Disc-Reify`: each strip-last step discards one atom of horizontal content;
    /// `R6.5.R3` `Reify-Earned`: "reification" is earned because the imported invariants become
    /// the atoms; `R6.5.R4` `HI-Irrev`: the depth reset makes within-fiber `H_I` structure
    /// irreversible one level up.)
    pub fn horizon_inheritance(&self, word: &[ElementId]) -> (bool, u32) {
        (self.is_fixpoint(word), self.depth(word))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;
    use crate::r0::projection_systems_and_fibers::ProjectionSystem;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// Base instance with two fixpoints: 0→1 (1 ∈ NF), 2→3 (3 ∈ NF). Q_M = {1,3}.
    fn two_fixpoint_base() -> Instance {
        let e = [(0, 1), (2, 3)];
        Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap()
    }

    #[test]
    fn lift_atoms_are_the_base_fixpoints() {
        let l = reify(&two_fixpoint_base());
        assert_eq!(l.atoms(), &[id(1), id(3)]); // Q_M
        assert_eq!(l.atom_count(), 2);
        assert!(l.is_atom(id(1)) && l.is_atom(id(3)) && !l.is_atom(id(0)));
    }

    #[test]
    fn projection_strips_to_the_first_atom() {
        let l = reify(&two_fixpoint_base());
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
    fn the_reify_of_a_projection_system_is_a_projection_system() {
        // TowerReify (R0.5.D1): Reify(M) over Q_M = {1,3} is an instance of the SAME
        // ProjectionSystem trait as ρ_M itself. Its universe FMA(Q_M) is INFINITE; every
        // construct below is computed by word operations, never by enumeration.
        let l = reify(&two_fixpoint_base());
        let w = vec![id(1), id(3), id(1)]; // a word
        // π' = strip-last; d_π'(w) = |w| − 1; CFix = the recursive projection (Rec-Proj).
        assert_eq!(ProjectionSystem::projection(&l, &w), vec![id(1), id(3)]);
        assert_eq!(l.projection_depth(&w), Some(2));
        // every word converges (pure-WF), via the R0.2 aspect-fate predicate over the trait.
        assert!(crate::r0::orbit_fate::is_convergent(&l, &w));
        assert!(!crate::r0::orbit_fate::is_persistent(&l, &w));
        assert_eq!(ProjectionSystem::canonical_form(&l, &w), Some(vec![id(1)])); // Rec-Proj = first atom
    }

    #[test]
    fn atoms_are_fixpoints() {
        let l = reify(&two_fixpoint_base());
        let atom = vec![id(3)];
        assert!(l.is_fixpoint(&atom));
        assert_eq!(l.depth(&atom), 0);
        assert_eq!(l.project(&atom), atom);
        assert_eq!(l.canonical_form(&atom), atom);
        // Hor-Reify: the horizon datum of a word is (is_atom, depth).
        assert_eq!(l.horizon_inheritance(&atom), (true, 0)); // an atom: fixpoint, depth 0
        assert_eq!(l.horizon_inheritance(&[id(1), id(3)]), (false, 1)); // a two-atom word
    }
}
