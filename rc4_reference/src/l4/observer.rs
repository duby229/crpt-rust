//! # L4.1 — The Observer Triple 𝒪 = (PV, H, D)
//!
//! Exact realization of spec section **L4.1** (`CRPT_OMEGA_TOWER_L4.md`, rc3):
//!
//! - L4.1.D1 `Behav-F` — the observer is a **behavioral functor**: `observe` is the action
//!   on objects (each model element ↦ its triple); under a homomorphism the triples
//!   transform accordingly (the morphism action, cf. [`crate::l7::functor`]).
//! - L4.1.D2 `PV-Obs` — the **path-valuation observable** (the PV component), realized by
//!   [`crate::l4::valuation::path_valuation`].
//! - L4.1.D3 `HC-Obs` — the **horizon-class observable** (the H component), realized by
//!   [`crate::l3::classification::classify`].
//! - L4.1.D4 `RD-Obs` — the regime discriminator D(x) ∈ {WF, NWF}.
//! - L4.1.D5 `Obs-Triple` — the observer triple `𝒪(x) = (PV(orbit(x)), H(x), D(x))`,
//!   bundling the three component observables above.
//!
//! **Invariance (corrected in rc3, was a post-rc2 engine finding).** 𝒪 is a *behaviour*,
//! invariant under **bisimilarity ≈** (which is strictly finer than `≃_M`), **not**
//! constant on `≃_M`-classes: the per-element PV and H components separate elements
//! within a `≃_M`-class (two `≃_M`-equivalent elements can have different `d_M`, hence
//! different six-class H and orbit-length PV — e.g. `0→1→2`, `3→2`: `0` is Class A, `1`
//! is Class B, yet `0 ≃_M 1`). Only the regime component D is `≃_M`-invariant. The engine
//! implements 𝒪 to the literal L4.1.D5 definition.

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::is_convergent;
use crate::l3::classification::{classify, HorizonClass};
use crate::l4::valuation::{path_valuation, unit_weight, Semiring, Tropical};

/// **L4.1.D4 (`RD-Obs`)** — the regime discriminator. `==` compares the computed tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WellFoundedness {
    /// x ∈ ↓_M (convergent / well-founded).
    WF,
    /// x ∈ ∞_M (persistent / non-well-founded).
    NWF,
}

/// **L4.1.D4 (`RD-Obs`)**: D(x) — WF on ↓_M, NWF on ∞_M.
pub fn regime_discriminator(op: &ProjectionOperator, x: ElementId) -> WellFoundedness {
    if is_convergent(op, x) {
        WellFoundedness::WF
    } else {
        WellFoundedness::NWF
    }
}

/// **L4.1.D5 (`Obs-Triple`)** — the observer triple `𝒪(x) = (PV(orbit(x)), H(x), D(x))`.
///
/// `valuation` is the projection valuation in the chosen semiring (`None` on ∞_M);
/// `horizon` is the six-class (`None` on ∞_M, where the native twelve-class applies);
/// `regime` is the WF/NWF discriminator. `==` compares the computed observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ObserverTriple<V> {
    /// PV(orbit(x)) in the chosen semiring.
    pub valuation: Option<V>,
    /// H(x): six-class horizon membership.
    pub horizon: Option<HorizonClass>,
    /// D(x): regime discriminator.
    pub regime: WellFoundedness,
}

/// **L4.1.D5**: 𝒪(x) with PV in semiring `S` and the given step weights.
pub fn observe<S, W>(op: &ProjectionOperator, x: ElementId, weight: W) -> ObserverTriple<S::Value>
where
    S: Semiring,
    W: Fn(ElementId, ElementId) -> S::Value,
{
    ObserverTriple {
        valuation: path_valuation::<S, _>(op, x, weight),
        horizon: classify(op, x),
        regime: regime_discriminator(op, x),
    }
}

/// **L4.1.D5**: 𝒪(x) with the canonical unweighted PV (orbit length d_M, via the
/// tropical semiring) — the default behavioral observation.
pub fn observe_length(op: &ProjectionOperator, x: ElementId) -> ObserverTriple<u64> {
    observe::<Tropical, _>(op, x, unit_weight)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l2::projection::Model;
    use crate::l1::substrate::Substrate;
    use crate::l3::classification::HorizonClass::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn observer_triple() {
        // 0→2, 1→2, 2→3, 3 ∈ NF (↓_M); 4 ⇄ 5 (∞_M).
        let e = [(0, 2), (1, 2), (2, 3), (4, 5), (5, 4)];
        let s = Substrate::new(6, &e, &e).unwrap();
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        // 0: PV=d_M=2, H=C, D=WF
        assert_eq!(
            observe_length(&op, id(0)),
            ObserverTriple { valuation: Some(2), horizon: Some(C), regime: WellFoundedness::WF }
        );
        // 2: PV=1, H=B, D=WF
        assert_eq!(
            observe_length(&op, id(2)),
            ObserverTriple { valuation: Some(1), horizon: Some(B), regime: WellFoundedness::WF }
        );
        // 4 ∈ ∞_M: PV=None, H=None, D=NWF
        assert_eq!(
            observe_length(&op, id(4)),
            ObserverTriple { valuation: None, horizon: None, regime: WellFoundedness::NWF }
        );
    }
}
