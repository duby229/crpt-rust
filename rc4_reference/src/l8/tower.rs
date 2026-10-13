//! # L8.4 / L8.9 / L8.10 — The Tower, Invariance, Fractality, Infiniteness
//!
//! Exact realization of spec sections **L8.4, L8.9, L8.10** (`CRPT_OMEGA_TOWER_L8.md`,
//! v1.0.0-rc4):
//!
//! - L8.4.D1 `Tower-Def` — `Tower(M)` is the sequence `M₀ = M`, `M_{n+1} = Lift(M_n)`.
//! - L8.4.T2 `NFC-TInv` — the query signature is tower-invariant: `Q_{M_n} ≅ Q_{M₀}`
//!   for all n. So `|Q|` is a single number carried up the whole tower.
//! - L8.9.D1 `Twr-Tail` / L8.9.D2 `CRPT-Fractal` (`Tower-Frac`) — fractal self-similarity: since `Q` is invariant, every level
//!   `n ≥ 1` is the free monoid over `Q_{M₀}` — `Lift(M_n)` depends only on `|Q|`, so
//!   the tail `M₁, M₂, …` is self-similar (all lifts of a `|Q|`-atom signature).
//! - L8.10.T2 `Tower-Inf` — the tower is **strictly infinite** (no two levels
//!   isomorphic) iff `|Q_M| ≥ 2`; for `|Q_M| = 1` it is **degenerate** (`Lift` ≅
//!   ℕ-with-successor, L8.10.R2), and the empty signature `|Q_M| = 0` cannot arise on
//!   a non-trivial model.
//! - L8.10.C2 `Lift-Pure-WF` — every level `n ≥ 1` is pure-WF (see [`crate::l8::lift`]).

use crate::l2::projection::Model;
use crate::l8::lift::{lift, Lift};

/// **L8.4.D1 (`Tower-Def`)** — the tower over a base model. Because the query
/// signature is tower-invariant (`NFC-TInv`), the tower is determined by the base
/// model and its invariant atom count `|Q|`; levels `n ≥ 1` are all the free monoid
/// over that signature.
pub struct Tower<'a> {
    base: &'a Model,
    atom_count: u32, // |Q_M|, invariant across all levels (NFC-TInv)
}

/// **L8.4.D1 (`Tower-Def`)**: `Tower(M)`.
pub fn tower(base: &Model) -> Tower<'_> {
    let atom_count = base.operator().fixpoints().len() as u32;
    Tower { base, atom_count }
}

impl<'a> Tower<'a> {
    /// The base model `M₀`.
    pub fn base(&self) -> &Model {
        self.base
    }

    /// **L8.4.T2 (`NFC-TInv`)** — the invariant query-signature size `|Q_{M_n}| = |Q_{M₀}|`.
    pub fn query_signature_size(&self) -> u32 {
        self.atom_count
    }

    /// **L8.2.D2** — the lift `M₁ = Lift(M₀)`. (By `NFC-TInv`/`Tower-Frac` every higher
    /// level `M_{n+1} = Lift(M_n)` is the free monoid over the same signature, so this
    /// single lift captures the structure of the whole tail.)
    pub fn lift(&self) -> Lift {
        lift(self.base)
    }

    /// **L8.10.T2 (`Tower-Inf`)** — the tower is strictly infinite (no two distinct
    /// levels isomorphic) iff `|Q_M| ≥ 2`.
    pub fn is_strictly_infinite(&self) -> bool {
        self.atom_count >= 2
    }

    /// **L8.10.R2** — the tower is degenerate (`Lift` ≅ ℕ-with-successor; the words over
    /// a single atom are `aⁿ`) iff `|Q_M| = 1`.
    pub fn is_degenerate(&self) -> bool {
        self.atom_count == 1
    }

    /// **L8.6.D1 (`Twr-Img`)** — the **tower image** of `x` at level 1: `ι(CFix(x))`, the
    /// one-atom word `[CFix(x)]` in `FMA(Q_M) = Fix(ρ_{Lift(M)})`. By `NFC-TInv` it is the
    /// same atom at every higher level. `None` on ∞_M (no finitary canonical form).
    pub fn tower_image(&self, x: crate::l1::substrate::ElementId) -> Option<crate::l8::fma::Word> {
        self.base.operator().canonical_fixpoint(x).map(|f| self.lift().canonical_inclusion(f))
    }

    /// Witness **L8.6.R4 (`TwrImg-Fix`)** / **L8.6.D2 (`Twr-Disc`)** — tower discreteness:
    /// every convergent element's tower image is an **atom** (a length-1 word), i.e. a
    /// fixpoint of `ρ_{Lift(M)}`. Returns the first convergent element whose image is not an
    /// atom (none), or `Ok`.
    pub fn certify_tower_image_is_atom(&self) -> Result<(), crate::l1::substrate::ElementId> {
        let lifted = self.lift();
        for x in self.base.substrate().elements() {
            if let Some(image) = self.tower_image(x) {
                if !lifted.is_fixpoint(&image) {
                    return Err(x);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::{ElementId, Substrate};

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn signature_size_is_invariant_and_tower_strictly_infinite() {
        // Two fixpoints ⇒ |Q| = 2 ⇒ strictly infinite tower.
        let e = [(0, 1), (2, 3)];
        let base = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        assert_eq!(t.query_signature_size(), 2);
        assert!(t.is_strictly_infinite());
        assert!(!t.is_degenerate());
        // the lift's atoms are exactly Q_{M₀} (signature carried up).
        assert_eq!(t.lift().atom_count(), t.query_signature_size());
        assert_eq!(t.lift().atoms(), &[id(1), id(3)]);
    }

    #[test]
    fn tower_image_is_a_canonical_atom() {
        // 0→1, 2→3 ⇒ Q_M = {1,3}. Tower image of 0 is the atom [CFix(0)] = [1].
        let e = [(0, 1), (2, 3)];
        let base = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        assert_eq!(t.tower_image(id(0)), Some(vec![id(1)]));
        assert_eq!(t.tower_image(id(3)), Some(vec![id(3)])); // a fixpoint maps to its own atom
        // Twr-Disc / TwrImg-Fix: every tower image is an atom (a Lift fixpoint).
        assert!(matches!(t.certify_tower_image_is_atom(), Ok(())));
    }

    #[test]
    fn single_fixpoint_tower_is_degenerate() {
        // One fixpoint ⇒ |Q| = 1 ⇒ Lift ≅ ℕ-with-successor (degenerate).
        let e = [(0, 1)];
        let base = Model::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        assert_eq!(t.query_signature_size(), 1);
        assert!(t.is_degenerate());
        assert!(!t.is_strictly_infinite());
    }
}
