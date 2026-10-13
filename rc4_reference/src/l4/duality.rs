//! # L4.4 — Duality Theorems (regimes as least/greatest fixpoints)
//!
//! Exact realization of the fixpoint-duality core of spec section **L4.4**
//! (`CRPT_OMEGA_TOWER_L4.md`, v1.0.0-rc4):
//!
//! - L4.4.D1 `Pre_ρ-14` — the ρ-predecessor operator `Pre_ρ(X) = {x | ρ_M(x) ∈ X}`.
//! - L4.4.D2 `Reg-FPO` (= L2.2.D2 `T^{conv/pers}`) — the regime fixpoint operators `T_conv(X) = Fix(ρ_M) ∪ Pre_ρ(X)`
//!   and `T_pers(X) = (𝒰_M \ Fix(ρ_M)) ∩ Pre_ρ(X)`, monotone on `(𝒫(𝒰_M), ⊆)` (L4.4.L1).
//! - L4.4.T1 `Reg-FP` — the regimes *are* the μ/ν decomposition:
//!   `↓_M = μT_conv` (least fixpoint), `∞_M = νT_pers` (greatest fixpoint).
//! - L4.4.D3 `RP-CP1` / L4.4.D4 `RP-CP2` — the WF least-fixpoint (RP) and NWF greatest-fixpoint (CP) reasoning conventions, realized by the μ/ν above.
//! - L4.4.T2 `FP-Dual` (DU-1) — WF reasoning is least-fixpoint reasoning, NWF reasoning is
//!   greatest-fixpoint reasoning; the two are order-duals.
//!
//! The fixpoints are computed by the engine's Knaster–Tarski combinator
//! ([`crate::l0::sol_necessity`]) — this section is the canonical *instance* of CRPT's second-order
//! architecture: the `μ/ν` quantifiers of `Reg-FP` are realized as finite least/greatest
//! fixpoints, exactly (`FOL-Fin` L5.3.T4), not enumerated. Sets are dense `Vec<bool>`.

use crate::l2::projection::ProjectionOperator;
use crate::l0::sol_necessity::{greatest_fixpoint, least_fixpoint};

/// **L4.4.D1 (`Pre_ρ`)** — the ρ-predecessor of a set `X` (bitmap): `Pre_ρ(X)[x] = X[ρ_M(x)]`.
pub fn predecessor(op: &ProjectionOperator, set: &[bool]) -> Vec<bool> {
    op.substrate().elements().map(|x| set[op.project(x).index()]).collect()
}

/// **L4.4.D2 (`Reg-FPO`)** — `T_conv(X) = Fix(ρ_M) ∪ Pre_ρ(X)`.
pub fn t_conv(op: &ProjectionOperator, set: &[bool]) -> Vec<bool> {
    op.substrate()
        .elements()
        .map(|x| op.is_fixpoint(x) || set[op.project(x).index()])
        .collect()
}

/// **L4.4.D2 (`Reg-FPO`)** — `T_pers(X) = (𝒰_M \ Fix(ρ_M)) ∩ Pre_ρ(X)`.
pub fn t_pers(op: &ProjectionOperator, set: &[bool]) -> Vec<bool> {
    op.substrate()
        .elements()
        .map(|x| !op.is_fixpoint(x) && set[op.project(x).index()])
        .collect()
}

/// **L4.4.T1 (`Reg-FP`)** — the least fixpoint `μT_conv` (= `↓_M`), via the Knaster–Tarski
/// combinator ([`crate::l0::sol_necessity::least_fixpoint`]) on the monotone `T_conv` (L4.4.L1).
pub fn least_fixpoint_convergent(op: &ProjectionOperator) -> Vec<bool> {
    let n = op.substrate().universe_len() as usize;
    least_fixpoint(n, &|set: &[bool]| t_conv(op, set))
}

/// **L4.4.T1 (`Reg-FP`)** — the greatest fixpoint `νT_pers` (= `∞_M`), via the Knaster–Tarski
/// combinator ([`crate::l0::sol_necessity::greatest_fixpoint`]) on the monotone `T_pers` (L4.4.L1).
pub fn greatest_fixpoint_persistent(op: &ProjectionOperator) -> Vec<bool> {
    let n = op.substrate().universe_len() as usize;
    greatest_fixpoint(n, &|set: &[bool]| t_pers(op, set))
}

/// Witness **L4.4.T1 (`Reg-FP`)** / **L4.4.T2 (`FP-Dual`)** — the regime partition is the
/// μ/ν decomposition: `μT_conv = ↓_M`, `νT_pers = ∞_M`, and they are complementary. Returns
/// the first element where the fixpoints disagree with the computed regimes, or `Ok`.
pub fn certify_regime_fixpoints(op: &ProjectionOperator) -> Result<(), crate::l1::substrate::ElementId> {
    let mu = least_fixpoint_convergent(op);
    let nu = greatest_fixpoint_persistent(op);
    for x in op.substrate().elements() {
        let convergent = op.canonical_fixpoint(x).is_some(); // x ∈ ↓_M
        // μT_conv = ↓_M, νT_pers = ∞_M (= complement of ↓_M).
        if mu[x.index()] != convergent || nu[x.index()] == convergent {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;
    use crate::l2::projection::Model;

    #[test]
    fn regimes_are_mu_nu_fixpoints() {
        // 0→1 (↓_M, 1 ∈ NF) and 2⇄3 (∞_M).
        let e = [(0, 1), (2, 3), (3, 2)];
        let m = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // μT_conv = ↓_M = {0,1}; νT_pers = ∞_M = {2,3}.
        assert_eq!(least_fixpoint_convergent(&op), vec![true, true, false, false]);
        assert_eq!(greatest_fixpoint_persistent(&op), vec![false, false, true, true]);
        assert!(matches!(certify_regime_fixpoints(&op), Ok(())));
    }

    #[test]
    fn predecessor_pulls_back_along_rho() {
        // 0→1, 1 ∈ NF: Pre_ρ({1}) = {0,1} (ρ(0)=1∈X, ρ(1)=1∈X).
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let op = m.operator();
        let x_set = vec![false, true]; // {1}
        assert_eq!(predecessor(&op, &x_set), vec![true, true]);
        // pure WF ⇒ μT_conv = 𝒰, νT_pers = ∅.
        assert_eq!(least_fixpoint_convergent(&op), vec![true, true]);
        assert_eq!(greatest_fixpoint_persistent(&op), vec![false, false]);
    }
}
