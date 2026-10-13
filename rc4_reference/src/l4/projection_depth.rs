//! # L4.5 — Co-Projection Depth and Inversion Horizon
//!
//! Exact realization of the canonical-period constructs of spec section **L4.5**
//! (`CRPT_OMEGA_TOWER_L4.md`, v1.0.0-rc4):
//!
//! - L4.5.D1 `CPD` — the **canonical period** `CPD(x)`: the minimal period of the
//!   quotient orbit `([ρ_M^n(x)]_≈)_n`. With `N(x)` the quotient orbit's **pre-period**
//!   (`min N : ∃p≥1 ∀n≥N : [ρ^{n+p}(x)]_≈ = [ρ^n(x)]_≈`), `CPD(x) := min{p ≥ 1 :
//!   [ρ^{N+p}(x)]_≈ = [ρ^{N}(x)]_≈}`. `CPD` is the persistent-regime dual of `d_M`.
//! - L4.5.T3 `CPD-Fin` — on a finite substrate `CPD(x) ∈ ℕ` (the quotient orbit is
//!   eventually periodic, `SC4-EP` L3.3.T1).
//! - L4.5.T4 `CIH` — the **co-inversion horizon** `CIH(x) := N(x) + CPD(x)`.
//!
//! For Type P elements `CPD = 1` (`|ω_≈| = 1`); for Type EP elements `CPD ≥ 2`
//! (`|ω_≈| ≥ 2`, L6.2.D1). On a finite substrate `CPD(x) = |ω_≈(x)|` exactly (the cycle
//! visits each ω-limit class once per period) — the period is decided from the labelled
//! bisimulation quotient (L1.1.D6), so distinguishing persistent elements requires the
//! substrate's observation labeling (`obs`, L1.1.D6).

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::is_persistent;

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

/// **L4.5.D1 (`CPD`)** — the canonical period `CPD(x)`: the minimal period of the
/// quotient orbit. `None` on ↓_M; on ∞_M, `1` iff Type P, `≥ 2` iff Type EP.
pub fn canonical_period(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    quotient_orbit_period(op, x).map(|(_, period)| period)
}

/// **L4.5.D1** — the quotient orbit pre-period `N(x)`: the number of steps before the
/// quotient orbit `[ρ_M^n(x)]_≈` becomes periodic. `None` on ↓_M.
pub fn quotient_pre_period(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    quotient_orbit_period(op, x).map(|(pre_period, _)| pre_period)
}

/// **L4.5.T4 (`CIH`)** — the co-inversion horizon `CIH(x) := N(x) + CPD(x)`. `None` on ↓_M.
pub fn co_inversion_horizon(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    quotient_orbit_period(op, x).map(|(pre_period, period)| pre_period + period)
}

/// Witness that `CPD(x) = |ω_≈(x)|` on ∞_M (L4.5.D1 vs L3.3.D1): the canonical period
/// equals the number of bisimulation classes in the ω-limit set. Returns the first
/// persistent element where they disagree, or `Ok`.
pub fn certify_period_is_omega_limit_size(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::l3::persistent::omega_limit_classes;
    for x in op.substrate().elements() {
        if let Some(period) = canonical_period(op, x) {
            if period != omega_limit_classes(op, x).len() as u32 {
                return Err(x);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;
    use crate::l2::projection::Model;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn type_p_cycle_has_period_one() {
        // 0⇄1 with default obs: 0,1 are bisimilar (one ω-class) ⇒ CPD = 1 (Type P).
        let e = [(0, 1), (1, 0)];
        let m = Model::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(canonical_period(&op, id(0)), Some(1));
        assert_eq!(quotient_pre_period(&op, id(0)), Some(0));
        assert!(matches!(certify_period_is_omega_limit_size(&op), Ok(())));
    }

    #[test]
    fn type_ep_cycle_has_period_two() {
        // 0→1→0 with distinct observables on 0 and 1 (both non-NF): the quotient orbit
        // visits two classes ⇒ CPD = 2 (Type EP), the persistent regime made non-degenerate
        // by the observation labeling (L1.1.D6).
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Model::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        assert_eq!(canonical_period(&op, id(0)), Some(2)); // CPD ≥ 2 ⇒ Type EP
        assert_eq!(canonical_period(&op, id(1)), Some(2));
        // CIH = N + CPD; here N(0) = 0 (already periodic) so CIH = 2.
        assert_eq!(co_inversion_horizon(&op, id(0)), Some(2));
        assert!(matches!(certify_period_is_omega_limit_size(&op), Ok(())));
    }

    #[test]
    fn convergent_elements_have_no_period() {
        // 0→1, 1 ∈ NF: 0 and 1 are convergent ⇒ CPD undefined.
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let op = m.operator();
        assert_eq!(canonical_period(&op, id(0)), None);
        assert_eq!(canonical_period(&op, id(1)), None);
    }
}
