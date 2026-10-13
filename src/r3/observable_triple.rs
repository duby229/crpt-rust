//! # R3.1 — The Observer Triple 𝒪 = (PV, H, D)
//!
//! Exact realization of spec section **R3.1** (`CRPT_OMEGA_TOWER_R3.md`, v1.0.0-rc9):
//!
//! - R3.1.D1 `Behav-F` — the observer is a **behavioral functor**: `observe` is the action
//!   on objects (each instance element ↦ its triple); under a homomorphism the triples
//!   transform accordingly (the morphism action; the CRPT functor is R6).
//! - R3.1.D2 `PV-Obs` — the **path-valuation observable** (the PV component), realized by
//!   [`crate::r3::projection_valuation::path_valuation`].
//! - R3.1.D3 `HC-Obs` — the **horizon-class observable** (the H component), realized by
//!   [`crate::r2::six_class_horizon_partition::classify`].
//! - R3.1.D4 `RD-Obs` — the aspect discriminator D(x) ∈ {WF, NWF}.
//! - R3.1.D5 `Obs-Triple` — the observer triple `𝒪(x) = (PV(orbit(x)), H(x), D(x))`,
//!   bundling the three component observables above.
//!
//! **Invariance.** 𝒪 is a *behaviour*,
//! invariant under **bisimilarity ≈** (which is strictly finer than `≃_M`), **not**
//! constant on `≃_M`-classes: the per-element PV and H components separate elements
//! within a `≃_M`-class (two `≃_M`-equivalent elements can have different `d_M`, hence
//! different six-class H and orbit-length PV — e.g. `0→1→2`, `3→2`: `0` is Class A, `1`
//! is Class B, yet `0 ≃_M 1`). Only the aspect component D is `≃_M`-invariant. The engine
//! implements 𝒪 to the literal R3.1.D5 definition.

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_convergent;
use crate::r2::six_class_horizon_partition::{classify, HorizonClass};
use crate::r3::projection_valuation::{path_valuation, unit_weight, Semiring, Tropical};

/// **R3.1.D4 (`RD-Obs`)** — the aspect discriminator. `==` compares the computed tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WellFoundedness {
    /// x ∈ ↓_M (convergent / well-founded).
    WF,
    /// x ∈ ∞_M (persistent / non-well-founded).
    NWF,
}

/// **R3.1.D4 (`RD-Obs`)**: D(x) — WF on ↓_M, NWF on ∞_M.
pub fn aspect_discriminator(op: &ProjectionOperator, x: ElementId) -> WellFoundedness {
    if is_convergent(op, x) {
        WellFoundedness::WF
    } else {
        WellFoundedness::NWF
    }
}

/// **R3.1.D5 (`Obs-Triple`)** — the observer triple `𝒪(x) = (PV(orbit(x)), H(x), D(x))`.
///
/// `valuation` is the projection valuation in the chosen semiring (`None` on ∞_M);
/// `horizon` is the six-class (`None` on ∞_M, where the native twelve-class applies);
/// `aspect` is the WF/NWF discriminator. `==` compares the computed observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ObserverTriple<V> {
    /// PV(orbit(x)) in the chosen semiring.
    pub valuation: Option<V>,
    /// H(x): six-class horizon membership.
    pub horizon: Option<HorizonClass>,
    /// D(x): aspect discriminator.
    pub aspect: WellFoundedness,
}

/// **R3.1.D5**: 𝒪(x) with PV in semiring `S` and the given step weights.
pub fn observe<S, W>(op: &ProjectionOperator, x: ElementId, weight: W) -> ObserverTriple<S::Value>
where
    S: Semiring,
    W: Fn(ElementId, ElementId) -> S::Value,
{
    ObserverTriple {
        valuation: path_valuation::<S, _>(op, x, weight),
        horizon: classify(op, x),
        aspect: aspect_discriminator(op, x),
    }
}

/// **R3.1.D5**: 𝒪(x) with the canonical unweighted PV (orbit length d_M, via the
/// tropical semiring) — the default behavioral observation.
pub fn observe_length(op: &ProjectionOperator, x: ElementId) -> ObserverTriple<u64> {
    observe::<Tropical, _>(op, x, unit_weight)
}

/// Witness **R3.1.R1 (`Prod-Conn`)** — the `Observable(y)` predicate of `PA-Prod` is the
/// **existential shadow** of the path-valuation (`PV`) observable: `PA-Prod`'s Observable
/// Contract (`OC-1`/`OC-2`) guarantees every non-fixpoint emits content, which is exactly the
/// `PV` component of the observer triple being non-degenerate at every `ρ_M`-step. Returns
/// `true` when the triple's `PV` (path-length) datum is strictly positive off the fixpoint of
/// `x` — the `PV`-shadow that `PA-Prod` projects. (`R3.1.R2` `Coal-Term`: of the three names —
/// "orbit characterisation triple", "coalgebra terminal triple", "observable triple" — the
/// last is preferred as it names the *role*, not the construction.)
pub fn prod_is_pv_shadow(op: &ProjectionOperator, x: ElementId) -> bool {
    // the PV component (path length to canonical form) is non-degenerate exactly when x is not
    // yet its own observable — the existential content PA-Prod's Observable predicate shadows.
    op.is_fixpoint(x) || observe_length(op, x).valuation != Some(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;
    use crate::r2::six_class_horizon_partition::HorizonClass::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn observer_triple() {
        // 0→2, 1→2, 2→3, 3 ∈ NF (↓_M); 4 ⇄ 5 (∞_M).
        let e = [(0, 2), (1, 2), (2, 3), (4, 5), (5, 4)];
        let s = Substrate::new(6, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        // 0: PV=d_M=2, H=C, D=WF
        assert_eq!(
            observe_length(&op, id(0)),
            ObserverTriple { valuation: Some(2), horizon: Some(C), aspect: WellFoundedness::WF }
        );
        // 2: PV=1, H=B, D=WF
        assert_eq!(
            observe_length(&op, id(2)),
            ObserverTriple { valuation: Some(1), horizon: Some(B), aspect: WellFoundedness::WF }
        );
        // 4 ∈ ∞_M: PV=None, H=None, D=NWF
        assert_eq!(
            observe_length(&op, id(4)),
            ObserverTriple { valuation: None, horizon: None, aspect: WellFoundedness::NWF }
        );
        // Prod-Conn: the PV component is the non-degenerate shadow PA-Prod's Observable casts.
        assert!(prod_is_pv_shadow(&op, id(0))); // a non-fixpoint: PV ≠ Some(0)
        assert!(prod_is_pv_shadow(&op, id(4))); // persistent: PV = None (still non-degenerate)
    }
}
