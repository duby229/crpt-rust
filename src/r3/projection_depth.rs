//! # R3.5 — Co-Projection Depth and Inversion Horizon
//!
//! Exact realization of the canonical-period constructs of spec section **R3.5**
//! (`CRPT_OMEGA_TOWER_R3.md`, v1.0.0-rc9):
//!
//! - R3.5.D1 `CPD` — the **canonical period** `CPD(x)`: the minimal period of the
//!   quotient orbit `([ρ_M^n(x)]_≈)_n`. With `N(x)` the quotient orbit's **pre-period**
//!   (`min N : ∃p≥1 ∀n≥N : [ρ^{n+p}(x)]_≈ = [ρ^n(x)]_≈`), `CPD(x) := min{p ≥ 1 :
//!   [ρ^{N+p}(x)]_≈ = [ρ^{N}(x)]_≈}`. `CPD` is the persistent-aspect dual of `d_M`.
//! - R3.5.T3 `CPD-Fin` — on a finite substrate `CPD(x) ∈ ℕ` (the quotient orbit is
//!   eventually periodic, `SC4-EP` R2.3.T1).
//! - R3.5.T4 `CIH` — the **co-inversion horizon** `CIH(x) := N(x) + CPD(x)`.
//!
//! For Type P elements `CPD = 1` (`|ω_≈| = 1`); for Type EP elements `CPD ≥ 2`
//! (`|ω_≈| ≥ 2`, R5.2.D1). On a finite substrate `CPD(x) = |ω_≈(x)|` exactly (the cycle
//! visits each ω-limit class once per period) — the period is decided from the labelled
//! bisimulation quotient (R1.1.D6), so distinguishing persistent elements requires the
//! substrate's observation labeling (`obs`, R1.1.D6).

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_persistent;

/// The quotient orbit's `(N(x), CPD(x))` — pre-period and minimal period — for a
/// persistent `x`; `None` on ↓_M. Computed exactly by following `[ρ_M^n(x)]_≈` until a
/// bisimulation class repeats (finite quotient ⇒ terminates).
fn quotient_orbit_period(op: &ProjectionOperator, x: ElementId) -> Option<(u32, u32)> {
    if !is_persistent(op, x) {
        return None;
    }
    let representative = op.substrate().bisimilarity();
    let size = op.substrate().universe_len() as usize;
    let mut first_seen = vec![u32::MAX; size]; // step at which each ≈-class was first visited
    let mut current = x;
    let mut step = 0u32;
    loop {
        let class = representative[current.index()].index();
        if first_seen[class] != u32::MAX {
            let pre_period = first_seen[class];
            return Some((pre_period, step - pre_period)); // (N(x), CPD(x))
        }
        first_seen[class] = step;
        current = op.project(current);
        step += 1;
    }
}

/// **R3.5.D1 (`CPD`)** — the canonical period `CPD(x)`: the minimal period of the
/// quotient orbit. `None` on ↓_M; on ∞_M, `1` iff Type P, `≥ 2` iff Type EP.
pub fn canonical_period(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    quotient_orbit_period(op, x).map(|(_, period)| period)
}

/// **R3.5.D1** — the quotient orbit pre-period `N(x)`: the number of steps before the
/// quotient orbit `[ρ_M^n(x)]_≈` becomes periodic. `None` on ↓_M.
pub fn quotient_pre_period(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    quotient_orbit_period(op, x).map(|(pre_period, _)| pre_period)
}

/// **R3.5.T4 (`CIH`)** — the co-inversion horizon `CIH(x) := N(x) + CPD(x)`. `None` on ↓_M.
pub fn co_inversion_horizon(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    quotient_orbit_period(op, x).map(|(pre_period, period)| pre_period + period)
}

/// Witness that `CPD(x) = |ω_≈(x)|` on ∞_M (R3.5.D1 vs R2.3.D1): the canonical period
/// equals the number of bisimulation classes in the ω-limit set. Returns the first
/// persistent element where they disagree, or `Ok`.
pub fn certify_period_is_omega_limit_size(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r2::canonical_orbit_invariant::omega_limit_classes;
    for x in op.substrate().elements() {
        if let Some(period) = canonical_period(op, x) {
            if period != omega_limit_classes(op, x).len() as u32 {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// **R3.5.T2 (`IH`)** — the **inversion horizon** `H(x) := d_M(x)`: the depth beyond which
/// `ρ_M^j` cannot invert `x` — for every `j > H(x)`, `x`'s entire `NFC` class maps to a single
/// point. `Some(d_M(x))` on `↓_M`; `None` on `∞_M`. (`R3.5.C2` `IH1.1`: the inversion horizon
/// is always **finite** on `↓_M`, since `d_M ∈ ℕ` there.)
pub fn inversion_horizon(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    use crate::r1::derivation_height::{derivation_height, DerivationHeight};
    match derivation_height(op, x) {
        DerivationHeight::Finite(d) => Some(d),
        DerivationHeight::Infinite => None,
    }
}

/// Witness **R3.5.C1 (`PD3`)** — projection **decrements derivation height by exactly one** off
/// the fixpoint set: for `x ∈ ↓_M \ Fix(ρ_M)`, `d_M(ρ_M(x)) = d_M(x) − 1`. Returns the first
/// convergent non-fixpoint violating the decrement (none), or `Ok`.
pub fn certify_projection_decrement(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::derivation_height::{derivation_height, DerivationHeight};
    for x in op.substrate().elements() {
        if let DerivationHeight::Finite(d) = derivation_height(op, x) {
            if d >= 1 && derivation_height(op, op.project(x)) != DerivationHeight::Finite(d - 1) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R3.5.T1 (`PD4`)** — **orbit non-injectivity beyond the horizon**: for `j > d_M(x)`,
/// `ρ_M^j` collapses `x` to its canonical fixpoint, so the `j`-step image of every element in
/// `x`'s `NFC` class is the *single* point `CFix(x)`. Returns the first convergent element
/// whose orbit, run past its horizon, is not collapsed to its canonical fixpoint (none), or
/// `Ok`. (`R3.5.C3` `IH1.2`: `H_S(x) = ⊤` iff `x` is **not uniquely recoverable** from
/// `ρ_M(x)` — the ramification locus is exactly the one-step inversion ambiguity.)
pub fn certify_collapse_beyond_horizon(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(cfix) = op.canonical_fixpoint(x) {
            let d = inversion_horizon(op, x).expect("convergent ⇒ finite horizon");
            // running one step past the horizon lands on (and stays at) the canonical fixpoint.
            if op.iterate(x, d + 1) != cfix {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R3.5.C3 (`IH1.2`)** — `H_S(x) = ⊤` iff `x` is **not uniquely recoverable** from
/// `ρ_M(x)`: the structural horizon marks exactly the one-step inversion ambiguity (more than
/// one element projects to `ρ_M(x)`). Returns whether `x` has a sibling under `ρ_M` (the
/// non-invertibility witness) — equal to `H_S(x)`.
pub fn not_uniquely_recoverable(op: &ProjectionOperator, x: ElementId) -> bool {
    crate::r2::orbit_signature_and_horizons::structural_horizon(op, x)
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
    fn type_p_cycle_has_period_one() {
        // 0⇄1 with default obs: 0,1 are bisimilar (one ω-class) ⇒ CPD = 1 (Type P).
        let e = [(0, 1), (1, 0)];
        let m = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(canonical_period(&op, id(0)), Some(1));
        assert_eq!(quotient_pre_period(&op, id(0)), Some(0));
        assert!(matches!(certify_period_is_omega_limit_size(&op), Ok(())));
    }

    #[test]
    fn type_ep_cycle_has_period_two() {
        // 0→1→0 with distinct observables on 0 and 1 (both non-NF): the quotient orbit
        // visits two classes ⇒ CPD = 2 (Type EP), the persistent aspect made non-degenerate
        // by the observation labeling (R1.1.D6).
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Instance::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        assert_eq!(canonical_period(&op, id(0)), Some(2)); // CPD ≥ 2 ⇒ Type EP
        assert_eq!(canonical_period(&op, id(1)), Some(2));
        // CIH = N + CPD; here N(0) = 0 (already periodic) so CIH = 2.
        assert_eq!(co_inversion_horizon(&op, id(0)), Some(2));
        assert!(matches!(certify_period_is_omega_limit_size(&op), Ok(())));
    }

    #[test]
    fn inversion_horizon_and_projection_decrement_on_convergent() {
        // 0→1→2, 2 ∈ NF ; 3→2 (ramified at 2). All convergent.
        let e = [(0, 1), (1, 2), (3, 2)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // IH / IH1.1: the inversion horizon is d_M, always finite on ↓_M.
        assert_eq!(inversion_horizon(&op, id(0)), Some(2));
        assert_eq!(inversion_horizon(&op, id(2)), Some(0));
        // PD3: projection decrements d_M by one off the fixpoint.
        assert!(matches!(certify_projection_decrement(&op), Ok(())));
        // PD4: running past the horizon collapses to the canonical fixpoint.
        assert!(matches!(certify_collapse_beyond_horizon(&op), Ok(())));
        // IH1.2: H_S(x) ⟺ x not uniquely recoverable from ρ_M(x); 1 and 3 both map to 2.
        assert!(not_uniquely_recoverable(&op, id(1)));
    }

    #[test]
    fn convergent_elements_have_no_period() {
        // 0→1, 1 ∈ NF: 0 and 1 are convergent ⇒ CPD undefined.
        let m = Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let op = m.operator();
        assert_eq!(canonical_period(&op, id(0)), None);
        assert_eq!(canonical_period(&op, id(1)), None);
    }
}
