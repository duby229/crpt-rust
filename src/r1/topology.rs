//! # R1.7 — The Substrate Topology
//!
//! The substrate of R1.1.D1 carries a topology `𝒯` as a free parameter (R1.7.R1
//! `Top-Inst`). On a **finite** universe a Hausdorff topology is necessarily discrete
//! (finite T₂ ⇒ discrete), so a discrete sequence converges iff eventually constant —
//! `PA-WN_top` (R1.7.Ax1) is then vacuous or fails, and **convergence mode** (R1.4.D1)
//! degenerates to recurrence there. Inhabiting it requires an infinite universe — supplied symbolically,
//! like every infinite instance of the one [`ProjectionSystem`] trait.
//!
//! [`TopologicalProjectionSystem`] is **not a second kind of system**: it is a sub-trait of
//! [`ProjectionSystem`] (R0.1.D1 `ProjSys`) — the *same* operator `π`, extended by exactly
//! one datum, the `𝒯`-limit. The mode (recurrence / convergence — exactly two, R1.4.D1) is how
//! the canonical form is reached, not what the system is. It realizes:
//!
//! - R1.7.D1 `TopSep` (Hausdorff T₂ separation of 𝒯) + R1.7.D2 `Top-Lim` (the 𝒯-limit of an orbit).
//! - R1.7.Ax1 `PA-WN_top` — persistent orbits converge to a `𝒯`-limit.
//! - R1.4.D1 topological-mode `CFix` on `∞_M`: `CFix(x) = lim_{n→∞} ρ^n(x)` — the
//!   **co-recursive** projection (`CNF∞` R2.3.D6), dual to the recursive `Rec-Proj` (R1.8.D4).
//! - R5.5.T3 `ATD-Und` — aspect membership is undecidable on infinite universes (Rice), so
//!   the instance *supplies* the aspect ([`projection_depth`](ProjectionSystem::projection_depth));
//!   the engine does not (cannot) infer it by orbit exploration.
//!
//! The canonical witness is [`ConvergentChain`] — the chain `ℕ ∪ {ω}` (R1.7.R1 / the
//! `ℕ ∪ (0,1]` family): `ρ(n) = n+1`, `ρ(ω) = ω`, `n → ω`. Every `Step(n)` is persistent
//! (its orbit never reaches a fixpoint in finitely many steps) yet converges to `ω`.

use crate::r0::projection_systems_and_fibers::ProjectionSystem;

/// **R1.1.D1 (𝒯) + R1.7.Ax1 (`PA-WN_top`)** — a [`ProjectionSystem`] whose substrate
/// carries a topology: the *same* operator `π`, extended by the `𝒯`-limit of an orbit
/// (`Top-Lim` R1.7.D2). On the `PA-WN_top` sub-class of `∞_M` the limit canonicalizes the
/// persistent aspect — topological mode.
pub trait TopologicalProjectionSystem: ProjectionSystem {
    /// **R1.7.D2 (`Top-Lim`)**: `lim_{n→∞} π^n(x)` — the `𝒯`-limit of the orbit, when it
    /// exists (unique by `TopSep` R1.7.D1). `Some` on the `PA-WN_top` sub-class of `∞_M`;
    /// `None` where no `𝒯`-limit exists (the recurrence-realization part of ∞_M).
    fn topological_limit(&self, x: &Self::Point) -> Option<Self::Point>;

    /// **R1.4.D1 — topological-mode `CFix`**: the canonical form as a `𝒯`-limit — the
    /// co-recursive projection (`CNF∞` R2.3.D6). `CFix(x) = x` on a fixpoint;
    /// `= lim π^n(x)` on a convergent persistent orbit.
    fn canonical_form_topological(&self, x: &Self::Point) -> Option<Self::Point> {
        if self.is_fixpoint(x) {
            Some(x.clone())
        } else {
            self.topological_limit(x)
        }
    }

    /// **R1.7.Ax1 (`PA-WN_top`)** holds at `x`: either `x` is convergent (out of scope —
    /// finitary), or its persistent orbit has a `𝒯`-limit.
    fn satisfies_pa_wn_top_at(&self, x: &Self::Point) -> bool {
        self.projection_depth(x).is_some() || self.topological_limit(x).is_some()
    }


    /// **`𝒯`-presentation datum (R1.7.D2-derived)** — the number of **distinct ∞_M
    /// orbits** whose `𝒯`-limit is `y` ("topological pre-images": orbits, i.e.
    /// tail-equivalence classes, not points). Part of the topology's finite presentation,
    /// just as the π-kernel is presented at R0. *Consumed by* the R2 horizon predicates (`H_S^top`, `Q-top` — `crate::r2`). `None` if not finitely determined; `Some(0)` for a
    /// point that is no orbit's limit.
    fn topological_preimage_count(&self, y: &Self::Point) -> Option<u32> {
        let _ = y;
        None
    }

    /// **`Bisim~` (R1.1.D7) observation labeling, symbolic tier** — the obs label of a
    /// point: the datum the labeled bisimulation `≈` and tail-equivalence (`Tail-Eq`
    /// R5 (orbit invariants)) read. The finite [`Substrate`](crate::r1::substrate::Substrate) carries
    /// this as its `observation` component; a symbolic instance overrides it to make
    /// orbits **discernible by CRPT's own machinery** — including "convergence rates": an
    /// instantiation codes its rate observables into obs (e.g. a Hölder class label), and
    /// indistinguishability is then ≈/tail-equivalence — equality of observables, never
    /// an external order or arithmetic. Default: the constant (minimal) observation.
    fn observation(&self, x: &Self::Point) -> u32 {
        let _ = x;
        0
    }

    /// **`Tail-Eq` (R5) presentation datum** — whether the distinct ∞_M orbits whose
    /// `𝒯`-limit is `y` are **pairwise tail-equivalent**: their (obs-labeled) ≈-class
    /// traces agree from some index on. This is CRPT's own reading of "convergence rates
    /// indistinguishable" (`H_I^top`, `crate::r2`): discernment
    /// by `≈`/observation equality (`Disc-Obs` R3.1.R4) — not by metric comparison.
    /// Finitely presented by the instance; default `Some(true)` (under the minimal
    /// constant observation all approach orbits are ≈-indistinguishable); `None` if not
    /// finitely determined.
    fn approach_orbits_tail_equivalent(&self, y: &Self::Point) -> Option<bool> {
        let _ = y;
        Some(true)
    }
}

/// A point of the canonical convergent chain `ℕ ∪ {ω}` (R1.7.R1). `==` is identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChainPoint {
    /// `n ∈ ℕ` — a step of the chain; `ρ(Step(n)) = Step(n+1)`. Persistent (never a fixpoint).
    Step(u64),
    /// `ω` — the limit point; `ρ(ω) = ω` (the unique fixpoint), and `Step(n) → ω`.
    Limit,
}

/// **R1.7.Ax1 witness (`ℕ ∪ {ω}`)** — the canonical `PA-WN_top` instance (R1.7.R1 / the
/// `ℕ ∪ (0,1]` family): `ρ(n) = n+1`, `ρ(ω) = ω`, with `Step(n) → ω` in `𝒯`. Every
/// `Step(n)` is persistent yet topologically converges to `ω`, so it is canonicalized in
/// **convergence mode** with `CFix(Step(n)) = ω`.
pub struct ConvergentChain;

/// The chain is an instance of the one [`ProjectionSystem`] trait — an *infinite* one, with
/// the aspect supplied finitely (`ATD-Und`): every `Step(n)` is persistent (`d_π` undefined),
/// `ω` alone is a fixpoint.
impl ProjectionSystem for ConvergentChain {
    type Point = ChainPoint;

    fn projection(&self, x: &ChainPoint) -> ChainPoint {
        match x {
            ChainPoint::Step(n) => ChainPoint::Step(n + 1),
            ChainPoint::Limit => ChainPoint::Limit,
        }
    }

    fn projection_depth(&self, x: &ChainPoint) -> Option<u32> {
        match x {
            // Step(n)'s orbit is Step(n), Step(n+1), … — never the fixpoint ω: d_π undefined.
            ChainPoint::Step(_) => None,
            ChainPoint::Limit => Some(0),
        }
    }

}

impl TopologicalProjectionSystem for ConvergentChain {
    fn topological_limit(&self, x: &ChainPoint) -> Option<ChainPoint> {
        // every orbit (including ω's) converges to ω.
        let _ = x;
        Some(ChainPoint::Limit)
    }

    fn topological_preimage_count(&self, y: &ChainPoint) -> Option<u32> {
        // exactly ONE ∞_M orbit (all Step(n) are tails of one another) converges to ω;
        // no Step is any orbit's limit.
        Some(match y {
            ChainPoint::Limit => 1,
            ChainPoint::Step(_) => 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::aspects_and_modes::Mode;

    #[test]
    fn convergent_chain_inhabits_topological_mode() {
        let chain = ConvergentChain;
        let x = ChainPoint::Step(0);
        // π steps along the chain; Step(0) is persistent (never a fixpoint).
        assert_eq!(chain.projection(&x), ChainPoint::Step(1));
        assert!(crate::r0::orbit_fate::is_persistent(&chain, &x));
        assert!(!chain.is_fixpoint(&x));
        // the recursive projection (Rec-Proj) is undefined on ∞_M — the 𝒯-limit takes over.
        assert_eq!(chain.canonical_form(&x), None);
        // PA-WN_top holds: the persistent orbit converges to ω.
        assert!(chain.satisfies_pa_wn_top_at(&x));
        // topological-mode CFix(Step(0)) = ω — the 𝒯-limit, not a finitely-reached fixpoint.
        assert_eq!(chain.canonical_form_topological(&x), Some(ChainPoint::Limit));
        // *** convergence mode is inhabited (non-degenerately) ***
        assert_eq!(crate::r1::aspects_and_modes::canonicalization_mode(&chain, &x), Mode::Convergence);
        // (the R1.12/R2.1/R6.1 constructs over this tier live in their section modules:
        //  ≃_M → r1::fibers, limit_id → r2::orbit_signature_and_horizons, GI∞ → r6::collapse.)
    }

    #[test]
    fn the_limit_point_is_a_finitary_fixpoint() {
        let chain = ConvergentChain;
        let omega = ChainPoint::Limit;
        assert!(chain.is_fixpoint(&omega));
        assert!(!crate::r0::orbit_fate::is_persistent(&chain, &omega));
        assert_eq!(chain.canonical_form_topological(&omega), Some(ChainPoint::Limit));
        // ω reaches its (own) fixpoint finitely ⇒ recurrence (convergence degenerates).
        assert_eq!(crate::r1::aspects_and_modes::canonicalization_mode(&chain, &omega), Mode::Recurrence);
    }
}
