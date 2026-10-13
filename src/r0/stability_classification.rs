//! # R0.8 — Universal Stability Classification
//!
//! Exact realization of spec section **R0.8** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9) — the
//! observability extension to persistent elements (which have no finitary canonical form):
//!
//! - R0.8.D1 `SC-Form` — the **stable canonical form** `L_∞^π(x) = lim_{n→∞} π^n(x)`: the
//!   topological limit of the orbit, when it exists. `SC(Π) ⊆ Pers(π)` is the set of
//!   persistent elements admitting one. Realized generically over a
//!   [`TopologicalProjectionSystem`].
//! - R0.8.T1 `SC-Strat-U` — persistent elements stratify into **exactly three tiers**: Tier 1
//!   (unconditional — the orbit has a fixpoint limit in `𝒯`), Tier 2 (Cauchy-convergent),
//!   Tier 3 (topological-axiom-requiring). Asymptotically-periodic orbits (a `k`-cycle of
//!   limit points, no single limit) are **outside** `SC(Π)`.
//! - R0.8.T2 `CRPT-SC` — `CNF∞_M` (R2.3.D6) and the SC-1…SC-4 conditions are the CRPT
//!   instantiation; Tier 3 is the `PA-WN_top` (R1.7.Ax1) tier. The canonical PA-WN_top
//!   witness [`ConvergentChain`](crate::r1::topology::ConvergentChain) is a Tier-1 element.

use crate::r1::topology::TopologicalProjectionSystem;

/// **R0.8.D1 (`SC-Form`)** — the stable canonical form `L_∞^π(x)` of a *persistent* element:
/// the `𝒯`-limit of its orbit. `Some` iff `x ∈ Pers(π)` and the limit exists (`x ∈ SC(Π)`);
/// `None` on convergent elements (which have the finitary `CNF_π` instead) or where no limit
/// exists.
pub fn stable_canonical_form<T: TopologicalProjectionSystem>(sys: &T, x: &T::Point) -> Option<T::Point> {
    if sys.projection_depth(x).is_some() {
        return None; // convergent — out of Pers(π), use the finitary canonical form
    }
    sys.topological_limit(x)
}

/// **R0.8.T1 (`SC-Strat-U`)** — the stability tier of a persistent element. `==` compares the
/// tier tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StabilityTier {
    /// **Tier 1 (Unconditional)** — the orbit has a π-fixpoint limit in `𝒯`; `SC` holds with
    /// no further condition.
    Unconditional,
    /// **Tier 2 (Cauchy)** — the orbit is Cauchy in `𝒯` (a limit exists under completeness).
    Cauchy,
    /// **Tier 3 (Axiom-requiring)** — a stable form exists only under added topological
    /// completeness axioms; or the orbit is asymptotically periodic (outside `SC(Π)`).
    AxiomRequiring,
}

/// **R0.8.T1 (`SC-Strat-U`)** — classify a persistent element into its stability tier:
/// **Unconditional** when its `𝒯`-limit exists and is a **fixpoint** (the orbit settles to a
/// single point); **AxiomRequiring** when no fixpoint limit is available (Cauchy/topological
/// or asymptotically-periodic — needing PA-WN_top or completeness). `None` on convergent
/// elements. (Tier 2 is the metric-completeness refinement, realized where a non-fixpoint
/// limit exists.)
pub fn stability_tier<T: TopologicalProjectionSystem>(sys: &T, x: &T::Point) -> Option<StabilityTier> {
    if sys.projection_depth(x).is_some() {
        return None; // convergent
    }
    match sys.topological_limit(x) {
        Some(limit) if sys.is_fixpoint(&limit) => Some(StabilityTier::Unconditional),
        Some(_) => Some(StabilityTier::Cauchy), // a limit that is not itself a fixpoint
        None => Some(StabilityTier::AxiomRequiring), // no 𝒯-limit (asymptotically periodic etc.)
    }
}

/// Witness **R0.8.T2 (`CRPT-SC`)** — the CRPT realization instantiates the universal
/// stratification: the canonical PA-WN_top witness (`ℕ ∪ {ω}`) is a **Tier-1** persistent
/// element whose stable canonical form is the fixpoint `ω` — the CRPT `CNF∞` of that orbit.
/// (`CNF∞_M` R2.3.D6 is the CRPT stable canonical form; Tier 3 is the PA-WN_top tier.)
/// Returns `true` when the CRPT witness is Tier-1 with `ω` as its stable form.
pub fn certify_crpt_sc() -> bool {
    use crate::r1::topology::{ChainPoint, ConvergentChain};
    let chain = ConvergentChain;
    let x = ChainPoint::Step(0); // a persistent element whose orbit converges to ω
    stability_tier(&chain, &x) == Some(StabilityTier::Unconditional)
        && stable_canonical_form(&chain, &x) == Some(ChainPoint::Limit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::topology::{ChainPoint, ConvergentChain};

    #[test]
    fn persistent_elements_stratify_into_tiers() {
        let chain = ConvergentChain;
        // SC-Form: the stable canonical form of Step(0) is the limit ω.
        assert_eq!(stable_canonical_form(&chain, &ChainPoint::Step(3)), Some(ChainPoint::Limit));
        // SC-Strat-U: Step(n) is Tier 1 (its 𝒯-limit ω is a fixpoint).
        assert_eq!(stability_tier(&chain, &ChainPoint::Step(3)), Some(StabilityTier::Unconditional));
        // a fixpoint (ω) is convergent, not persistent ⇒ no stability tier.
        assert_eq!(stability_tier(&chain, &ChainPoint::Limit), None);
        // CRPT-SC: the CRPT PA-WN_top witness instantiates the universal Tier 1.
        assert!(certify_crpt_sc());
    }
}
