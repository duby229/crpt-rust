//! # Rω.3 — Rank Ordering m_CRPT
//!
//! Exact realization of spec section **Rω.3** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9):
//!
//! - Rω.3.D1 `m_CRPT` — the rank of a construct `X` in the self-substrate is its derivation
//!   height there: `m_CRPT(X) := d_{ρ_CRPT}(X) = min{ n | ρ_CRPT^n(X) = R1.1.D1 }`. The level
//!   structure is the zonally-grouped expression of `m_CRPT`. This is literally
//!   [`crate::r1::derivation_height::d_M`](crate::r1::derivation_height::derivation_height)
//!   `(R1.10.D2)` read on the self-instance, so it is the **same** rank measure the theory
//!   uses for any pure-WF instance, applied to the anchor.

use crate::r1::derivation_height::{derivation_height, DerivationHeight};
use crate::r1::substrate::ElementId;
use crate::romega::self_projection_system::{self_substrate, R1_1_D1, RANK_CARRIERS};

/// **Rω.3.D1 (`m_CRPT`)** — the CRPT rank of construct `X`: its dependency depth from
/// R1.1.D1, computed as `d_M` on the self-substrate. `Finite(0)` exactly at the root;
/// finite everywhere (the self-application is pure-WF, Rω.7.T1).
pub fn m_crpt(x: ElementId) -> DerivationHeight {
    let m = self_substrate();
    derivation_height(&m.operator(), x)
}

/// Witness **Rω.3.D1 (`m_CRPT`)** — the rank function is total and finite, `0` exactly at
/// R1.1.D1, and strictly increasing up the carrier chain (R1 at depth 1 … R6 at depth 6) —
/// confirming the self-substrate is well-founded and the level structure expresses the rank.
/// Returns the first element violating totality/finiteness, or `Ok`.
pub fn certify_rank_function() -> Result<(), ElementId> {
    let m = self_substrate();
    let op = m.operator();
    // m_CRPT(R1.1.D1) = 0.
    if m_crpt(R1_1_D1) != DerivationHeight::Finite(0) {
        return Err(R1_1_D1);
    }
    // total and finite on every construct (pure-WF).
    for x in m.substrate().elements() {
        if matches!(derivation_height(&op, x), DerivationHeight::Infinite) {
            return Err(x);
        }
    }
    // strictly increasing along the carrier chain R1…R6: depth k at the k-th carrier.
    for (k, &c) in RANK_CARRIERS.iter().enumerate() {
        if m_crpt(c) != DerivationHeight::Finite(k as u32 + 1) {
            return Err(c);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rank_is_dependency_depth_from_the_root() {
        assert!(matches!(certify_rank_function(), Ok(())));
        assert_eq!(m_crpt(R1_1_D1), DerivationHeight::Finite(0));
        // R6 carrier sits six dependency steps above the root.
        assert_eq!(m_crpt(RANK_CARRIERS[5]), DerivationHeight::Finite(6));
    }
}
