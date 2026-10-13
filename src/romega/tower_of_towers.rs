//! # Rω.4 — Tower of Towers
//!
//! Exact realization of spec section **Rω.4** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9):
//!
//! - Rω.4.T1 `Tower-of-Towers` — applying the Reification construction (`Tower` R6.7.D1) to
//!   the self-substrate `M := Self_CRPT` produces
//!   `Tower(Self_CRPT) = (Self_CRPT, Reify(Self_CRPT), Reify²(Self_CRPT), …)` whose levels
//!   are themselves towers. At level `n` the atoms of `Reify^n(Self_CRPT)` are the
//!   fiber-equivalence classes of `Reify^{n−1}`. Because `Self_CRPT` is **WF** (`∞ = ∅`,
//!   Rω.7.T1) and `Reify-Pure-WF` (R6.13.C2) propagates well-foundedness, **every** level of
//!   `Tower(Self_CRPT)` is a WF CRPT instance.
//!
//! Realized by [`crate::r6::tower::tower`] applied to the [`self_substrate`]: the *same* tower
//! construction every instance gets, pointed at the anchor.

use crate::r6::tower::tower;
use crate::romega::self_projection_system::self_substrate;

/// Witness **Rω.4.T1 (`Tower-of-Towers`)** — the reification of the self-substrate is a
/// legitimate WF CRPT instance whose tower tail is self-similar. Certifies: (i) the query
/// signature is the single root atom `{R1.1.D1}` (so the tower is degenerate — one primitive);
/// (ii) every convergent construct's tower image is an **atom** (Twr-Disc, R6.9), i.e. each
/// anchor construct reifies to its canonical primitive; (iii) the reified level is pure-WF.
/// Returns `true` when all three hold.
pub fn certify_tower_of_towers() -> bool {
    let base = self_substrate();
    let t = tower(&base);
    // (i) one primitive ⇒ |Q| = 1 ⇒ degenerate tower (ℕ-with-successor tail).
    let one_primitive = t.query_signature_size() == 1 && t.is_degenerate();
    // (ii) every construct's tower image is a one-atom word (its canonical primitive).
    let images_are_atoms = t.certify_tower_image_is_atom().is_ok();
    // (iii) the reified level resets every primitive to a depth-0 atom (Reify-Pure-WF).
    let pure_wf = crate::r6::tower::certify_depth_reset(&base).is_ok();
    one_primitive && images_are_atoms && pure_wf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reifying_the_anchor_yields_a_well_founded_tower() {
        assert!(certify_tower_of_towers());
        // the anchor has a single primitive root, so Tower(Self_CRPT) is the degenerate tower.
        let base = self_substrate();
        assert_eq!(tower(&base).query_signature_size(), 1);
    }
}
