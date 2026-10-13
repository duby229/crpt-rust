//! # Rω.6 — The Anchor as the Fractal It Describes
//!
//! Exact realization of spec section **Rω.6** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9):
//!
//! - Rω.6.T1 `Anchor-Fractal` — the anchor **is** the fractal structure its own R6 tower
//!   theory describes: `Tower(Self_CRPT)` exhibits the fractal self-similarity of
//!   `CRPT-Fractal` (R6.12.D2), since the query signature is tower-invariant (`NFC-TInv`
//!   R6.7.T2) and so every level `n ≥ 1` is the free monoid over the same signature.
//! - Rω.6.C1 — the fractal claim is **internal** to CRPT (proved by CRPT's own R6 machinery,
//!   not asserted from outside).
//! - Rω.6.C2 — **no tower-limit object `M_ω` is introduced**: the construction closes
//!   (`Self-FP` Rω.5.T1) without a new limit level beyond the tower. (Scoped to the absence of
//!   the limit *object* — distinct from the σ-persistent *orbits* `∞_CRPT^σ ≠ ∅`, which are a
//!   structural-aspect fact of the base, not a new ω-level; `Self-Inf` Rω.1.D2.)
//!
//! Realized via [`crate::r6::tower`] on the [`self_substrate`]: the anchor's tower tail is
//! self-similar (here the degenerate single-atom tail — the anchor's one primitive), and the
//! signature is invariant up the tower.

use crate::r6::tower::tower;
use crate::romega::self_projection_system::self_substrate;

/// Witness **Rω.6.T1 (`Anchor-Fractal`)** + **Rω.6.C1/C2** — the anchor is its own fractal:
/// (i) the tower signature is **invariant** (`NFC-TInv`: `Reify`'s atom count equals the
/// base query-signature size), so the tail `M₁, M₂, …` is self-similar — the internal
/// fractal claim, by CRPT's own R6 machinery; (ii) the growth is a proper embedding with a
/// **stable isomorphism type** (`Twr-Growth` R6.7.T4) — the tower self-similates without
/// introducing a new ω-state (Rω.6.C2). Returns `true` when the anchor exhibits its own
/// fractal structure.
pub fn certify_anchor_fractal() -> bool {
    let base = self_substrate();
    let t = tower(&base);
    // (i) NFC-TInv: the signature is carried up unchanged ⇒ self-similar tail (CRPT-Fractal).
    let signature_invariant = t.reify().atom_count() == t.query_signature_size();
    // (ii) Twr-Growth: proper embedding + stable type ⇒ no new ω-state is generated (C2),
    //      the fractal recurs without regress.
    let (proper_embedding, type_stable, _base_differs) = t.growth_trichotomy();
    signature_invariant && proper_embedding && type_stable
}

/// Witness **Rω.6.R1 (`Final-Framing`)** — the **final framing** of the self-application
/// result: CRPT, applied to its own constructs, is the fractal it describes — a pure-WF
/// self-instance whose single primitive root (R1.1.D1) the tower reifies into the atoms of its
/// own self-similar tail, closing without regress. Returns `true` when the anchor exhibits its
/// own fractal structure ([`certify_anchor_fractal`]) — the result the framing summarizes.
pub fn final_framing() -> bool {
    certify_anchor_fractal()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_anchor_is_the_fractal_it_describes() {
        // Anchor-Fractal (Rω.6.T1): the self-application exhibits the R6 fractal structure
        // internally, closing without a new ω-state (Rω.6.C2).
        assert!(certify_anchor_fractal());
    }
}
