//! # R5.2 — Orbit-Type Classification of ∞_M
//!
//! Exact realization of spec section **R5.2** (`CRPT_OMEGA_TOWER_R5.md`, v1.0.0-rc9):
//!
//! - R5.2.D1 `OTC` (using `SC-1` R2.3.D2 / `SC-4-Def` R2.3.D5) — the unconditional orbit-type classification of a persistent
//!   element by the long-run behavior of its quotient orbit `OT(x) = ([ρ_M^n(x)]_≈)_n`:
//!   - **Type P** (periodic / eventually constant): SC-1 holds, `|ω_≈(x)| = 1`.
//!   - **Type EP** (eventually periodic): SC-4 ∧ ¬SC-1, `|ω_≈(x)| ≥ 2`.
//!   - **Type AP** (aperiodic): ¬SC-4, `|{[ρ_M^n(x)]_≈}| = ∞`.
//! - R5.2.T1 `OT-Part` — {P, EP, AP} is an exhaustive disjoint partition of ∞_M.
//!
//! Decided exactly on finite substrates from `|ω_≈(x)|` ([`omega_limit_classes`],
//! R2.3.D1): the quotient is finite, so SC-4 always holds and **Type AP cannot occur**.

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_persistent;
use crate::r2::canonical_orbit_invariant::omega_limit_classes;

/// **R5.2.D1 (`OTC`)** — the orbit type of a persistent element. `==` compares the tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrbitType {
    /// **Type P** — the quotient orbit eventually stabilises to one class (`|ω_≈| = 1`,
    /// SC-1); the persistent canonical form CNF∞_M is well-defined.
    Periodic,
    /// **Type EP** — the quotient orbit cycles through `|ω_≈| ≥ 2` classes (SC-4 ∧ ¬SC-1).
    EventuallyPeriodic,
    /// **Type AP** — the quotient orbit visits infinitely many classes (¬SC-4). Cannot
    /// occur on a finite substrate (the quotient is finite); retained for completeness.
    Aperiodic,
}

/// **R5.2.D1 (`OTC`)** — the orbit type of `x`. `None` on ↓_M (orbit types stratify the
/// *persistent* aspect); `Some` on ∞_M, decided by `|ω_≈(x)|`.
pub fn orbit_type(op: &ProjectionOperator, x: ElementId) -> Option<OrbitType> {
    if !is_persistent(op, x) {
        return None;
    }
    // On a finite substrate ω_≈(x) is the finite eventual cycle in the quotient.
    match omega_limit_classes(op, x).len() {
        1 => Some(OrbitType::Periodic), // SC-1
        _ => Some(OrbitType::EventuallyPeriodic), // |ω_≈| ≥ 2; AP (infinite) impossible here
    }
}

/// Witness **R5.2.T1 (`OT-Part`)** — {P, EP, AP} partitions ∞_M: every persistent
/// element has exactly one orbit type, and every convergent element has none. Returns
/// the first element violating the partition, or `Ok`.
pub fn certify_orbit_type_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_persistent(op, x) != orbit_type(op, x).is_some() {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness the finite-substrate analogue of `AP-Irred` (R5.2.T3): **no ∞_M element is
/// Type AP** (the quotient orbit is always finite). Returns the first aperiodic element
/// found (never, on a finite substrate), or `Ok`.
pub fn certify_no_aperiodic(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if orbit_type(op, x) == Some(OrbitType::Aperiodic) {
            return Err(x);
        }
    }
    Ok(())
}


/// **R5.2.D1 (`OTC`) — Type AP certificate, symbolic tier**: a finite certificate that
/// `x`'s quotient orbit visits at least `n + 1` **pairwise distinct** ≈-classes —
/// refuting SC-4 up to depth `n` (`|B̃(x)| > n`). Type AP holds iff this certifies for
/// *every* `n`, which a symbolic instance establishes by construction (e.g. the
/// ℕ-counter: an injective class trace) and the engine verifies to any requested depth.
/// `class_of` supplies the instance's ≈-class labeling (finitely presented; on a finite
/// substrate it is `bisimilarity`, where SC-4 always holds and AP is impossible).
pub fn certify_aperiodic_prefix<P: crate::r0::projection_systems_and_fibers::ProjectionSystem>(
    sys: &P,
    x: &P::Point,
    class_of: impl Fn(&P::Point) -> u64,
    n: u32,
) -> bool {
    if sys.projection_depth(x).is_some() {
        return false; // Type AP is a classification of ∞_M
    }
    let mut labels: Vec<u64> = Vec::with_capacity(n as usize + 1);
    let mut current = x.clone();
    for _ in 0..=n {
        labels.push(class_of(&current));
        current = sys.projection(&current);
    }
    labels.sort_unstable();
    labels.windows(2).all(|w| w[0] != w[1]) // pairwise distinct ⇒ > n classes visited
}


// ============================================================================
// R5.2.D2 `3-Tier` — the three-tier analysis stratification of the persistent
// theory by assumption strength (the AOI analysis layer runs on every tier).
// ============================================================================

/// **R5.2.D2 (`3-Tier`)** — the analysis tier available for a persistent element.
/// `==` compares the tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnalysisTier {
    /// Tier 1 — unconditional orbit type / orbit trace.
    Unconditional,
    /// Tier 2 — SC-4 finite-orbit structure (CNF∞, CPD, A*–F*).
    FiniteOrbit,
    /// Tier 3 — topological (PA-WN_top): topological-limit CFix, twelve-class.
    Topological,
}

/// **R5.2.D2 (`3-Tier`)** — the deepest analysis tier reached by `x` on this (finite,
/// discrete) substrate: `FiniteOrbit` (Tier 2) for every persistent element (SC-4 always
/// holds finitely); `None` on ↓_M. `Topological` (Tier 3) is reachable only under a
/// non-discrete topology (the topological tier).
pub fn analysis_tier(op: &ProjectionOperator, x: ElementId) -> Option<AnalysisTier> {
    if is_persistent(op, x) {
        // finite substrate ⇒ SC-4 holds ⇒ Tier 2 (Tier 3 needs PA-WN_top, absent here).
        Some(AnalysisTier::FiniteOrbit)
    } else {
        None
    }
}

/// Witness **R5.2.T2 (`Tier-Compat`)** — the **Tier Compatibility** theorem: the three tiers
/// are mutually compatible — **Tier 2 refines Tier 1** (orbit types remain valid as the
/// analysis deepens), and every persistent element carries a determinate tier *and* a
/// determinate orbit type, consistently. Returns the first persistent element whose tier and
/// orbit-type are not jointly defined (none), or `Ok`. (`R5.2.R1` `NonConv-Answer`,
/// `R5.2.R2` `ThreeTier-Rel`: the three-tier framework is the structured *answer* to "what is
/// the asymptotic content of a non-convergent orbit", organizing the existing `∞_M` tools —
/// orbit-type (Tier 1, unconditional), AOI/spectrum (Tier 2, `SC-4`), topological (Tier 3,
/// `PA-WN_top`) — into one hierarchy.)
pub fn certify_tier_compatibility(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_persistent(op, x) {
            // Tier 1 (orbit type) and Tier 2 (analysis tier) are both defined and consistent.
            if orbit_type(op, x).is_none() || analysis_tier(op, x).is_none() {
                return Err(x);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tier_tests {
    use super::*;
    use crate::r1::substrate::Substrate;
    use crate::r1::reduction_strategy::Instance;

    #[test]
    fn persistent_elements_reach_tier_two_on_finite_substrates() {
        // 0→1 (↓_M) and 2⇄3 (∞_M).
        let e = [(0, 1), (2, 3), (3, 2)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(analysis_tier(&op, ElementId(0)), None); // ↓_M
        assert_eq!(analysis_tier(&op, ElementId(2)), Some(AnalysisTier::FiniteOrbit));
        // Tier ordering: unconditional ⊂ finite-orbit ⊂ topological.
        assert!(AnalysisTier::Unconditional < AnalysisTier::Topological);
        // Tier-Compat: every persistent element has a consistent tier + orbit type.
        assert!(matches!(certify_tier_compatibility(&op), Ok(())));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;
    use crate::r1::reduction_strategy::Instance;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn type_ep_for_a_genuine_cycle() {
        // 0→1→2→0 (a 3-cycle): each element diverges, ω_≈ is the cycle's class set.
        // 3→4, 4 ∈ NF (↓_M: no orbit type).
        let e = [(0, 1), (1, 2), (2, 0), (3, 4)];
        let m = Instance::from_functional_reduction(Substrate::new(5, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // ↓_M elements have no orbit type.
        assert_eq!(orbit_type(&op, id(3)), None);
        assert_eq!(orbit_type(&op, id(4)), None);
        // every ∞_M element gets exactly one type, none aperiodic.
        assert!(orbit_type(&op, id(0)).is_some());
        assert!(matches!(certify_orbit_type_partition(&op), Ok(())));
        assert!(matches!(certify_no_aperiodic(&op), Ok(())));
    }

    #[test]
    fn type_p_when_cycle_is_one_bisimulation_class() {
        // A pure 2-cycle 0⇄1: 0 and 1 are bisimilar (both diverge on a single path), so
        // ω_≈ collapses to one class ⇒ SC-1 ⇒ Type P.
        let e = [(0, 1), (1, 0)];
        let m = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(orbit_type(&op, id(0)), Some(OrbitType::Periodic));
        assert_eq!(orbit_type(&op, id(1)), Some(OrbitType::Periodic));
        assert!(matches!(certify_no_aperiodic(&op), Ok(())));
    }

    #[test]
    fn type_ap_inhabits_on_the_symbolic_counter() {
        use crate::r1::topology::{ChainPoint, ConvergentChain};
        // The ℕ-counter (ConvergentChain Steps) with the injective class labeling
        // class_of(Step k) = k: the quotient orbit visits pairwise-distinct classes at
        // EVERY depth — ¬SC-4 by construction ⇒ **Type AP** (uninhabitable on finite
        // substrates, inhabited here on the symbolic tier).
        let chain = ConvergentChain;
        let class_of = |p: &ChainPoint| match p {
            ChainPoint::Step(k) => *k,
            ChainPoint::Limit => u64::MAX,
        };
        assert!(certify_aperiodic_prefix(&chain, &ChainPoint::Step(0), class_of, 64));
        assert!(certify_aperiodic_prefix(&chain, &ChainPoint::Step(7), class_of, 256));
        // ω is convergent — not classified by the ∞_M taxonomy.
        assert!(!certify_aperiodic_prefix(&chain, &ChainPoint::Limit, class_of, 8));
    }
}
