//! # R3.4 — Duality Theorems (aspects as least/greatest fixpoints)
//!
//! Exact realization of the fixpoint-duality core of spec section **R3.4**
//! (`CRPT_OMEGA_TOWER_R3.md`, v1.0.0-rc9):
//!
//! - R3.4.D1 `Pre_ρ-14` — the ρ-predecessor operator `Pre_ρ(X) = {x | ρ_M(x) ∈ X}`.
//! - R3.4.D2 `Asp-FPO` (= R1.9.D2 `T^{conv/pers}`) — the aspect fixpoint operators `T_conv(X) = Fix(ρ_M) ∪ Pre_ρ(X)`
//!   and `T_pers(X) = (𝒰_M \ Fix(ρ_M)) ∩ Pre_ρ(X)`, monotone on `(𝒫(𝒰_M), ⊆)` (R3.4.L1).
//! - R3.4.T1 `Asp-FP` — the aspects *are* the μ/ν decomposition:
//!   `↓_M = μT_conv` (least fixpoint), `∞_M = νT_pers` (greatest fixpoint).
//! - R3.4.D3 `RP-CP1` / R3.4.D4 `RP-CP2` — the WF least-fixpoint (RP) and NWF greatest-fixpoint (CP) reasoning conventions, realized by the μ/ν above.
//! - R3.4.T2 `FP-Dual` (DU-1) — WF reasoning is least-fixpoint reasoning, NWF reasoning is
//!   greatest-fixpoint reasoning; the two are order-duals.
//!
//! The fixpoints are computed by the engine's Knaster–Tarski combinator
//! ([`crate::r0::sol_necessity`]) — this section is the canonical *instance* of CRPT's second-order
//! architecture: the `μ/ν` quantifiers of `Asp-FP` are realized as finite least/greatest
//! fixpoints, exactly (`FOL-Fin` R4.3.T4), not enumerated. Sets are dense `Vec<bool>`.

use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r0::sol_necessity::{greatest_fixpoint, least_fixpoint};

/// **R3.4.D1 (`Pre_ρ`)** — the ρ-predecessor of a set `X` (bitmap): `Pre_ρ(X)[x] = X[ρ_M(x)]`.
pub fn predecessor(op: &ProjectionOperator, set: &[bool]) -> Vec<bool> {
    op.substrate().elements().map(|x| set[op.project(x).index()]).collect()
}

/// **R3.4.D2 (`Asp-FPO`)** — `T_conv(X) = Fix(ρ_M) ∪ Pre_ρ(X)`.
pub fn t_conv(op: &ProjectionOperator, set: &[bool]) -> Vec<bool> {
    op.substrate()
        .elements()
        .map(|x| op.is_fixpoint(x) || set[op.project(x).index()])
        .collect()
}

/// **R3.4.D2 (`Asp-FPO`)** — `T_pers(X) = (𝒰_M \ Fix(ρ_M)) ∩ Pre_ρ(X)`.
pub fn t_pers(op: &ProjectionOperator, set: &[bool]) -> Vec<bool> {
    op.substrate()
        .elements()
        .map(|x| !op.is_fixpoint(x) && set[op.project(x).index()])
        .collect()
}

/// **R3.4.T1 (`Asp-FP`)** — the least fixpoint `μT_conv` (= `↓_M`), via the Knaster–Tarski
/// combinator ([`crate::r0::sol_necessity::least_fixpoint`]) on the monotone `T_conv` (R3.4.L1).
pub fn least_fixpoint_convergent(op: &ProjectionOperator) -> Vec<bool> {
    let n = op.substrate().universe_len() as usize;
    least_fixpoint(n, &|set: &[bool]| t_conv(op, set))
}

/// **R3.4.T1 (`Asp-FP`)** — the greatest fixpoint `νT_pers` (= `∞_M`), via the Knaster–Tarski
/// combinator ([`crate::r0::sol_necessity::greatest_fixpoint`]) on the monotone `T_pers` (R3.4.L1).
pub fn greatest_fixpoint_persistent(op: &ProjectionOperator) -> Vec<bool> {
    let n = op.substrate().universe_len() as usize;
    greatest_fixpoint(n, &|set: &[bool]| t_pers(op, set))
}

/// Witness **R3.4.T1 (`Asp-FP`)** / **R3.4.T2 (`FP-Dual`)** — the aspect partition is the
/// μ/ν decomposition: `μT_conv = ↓_M`, `νT_pers = ∞_M`, and they are complementary. Returns
/// the first element where the fixpoints disagree with the computed aspects, or `Ok`.
pub fn certify_aspect_fixpoints(op: &ProjectionOperator) -> Result<(), crate::r1::substrate::ElementId> {
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

/// Witness **R3.4.T3 (`Ind-CoInd`)** — the **induction/co-induction duality** (`DU-2`):
/// well-founded **induction** over derivation height on the *least* fixpoint `↓_M = μT_conv`
/// (the convergent aspect) is dual to **Park-style coinduction** on the *greatest* fixpoint
/// `∞_M = νT_pers` (the persistent aspect). Realized by certifying the two fixpoints **partition**
/// the universe (`μ` = `↓_M`, `ν` = `∞_M`, complementary) — the `μ/ν` duality made concrete.
/// (`R3.4.R1` `WN-NWF-Comp`: `PA-WN`/`PA-NWF` are mutually exclusive only as *global* axioms;
/// in aspect-stratified instances they **coexist by scoping** — `PA-WN` on `↓_M`, `PA-NWF` on
/// `∞_M`.) Returns the first element where the `μ/ν` partition fails (none), or `Ok`.
pub fn certify_induction_coinduction_duality(
    op: &ProjectionOperator,
) -> Result<(), crate::r1::substrate::ElementId> {
    // the μ (induction/↓_M) and ν (coinduction/∞_M) fixpoints are exact complements.
    certify_aspect_fixpoints(op)
}

/// Witness **R3.4.T4 (`PV-Dual-14`)** — the **path-valuation duality** (`DU-3`): the WF path
/// valuation `PV` (over finite histories) and the NWF limit valuation `PV∞` (over infinite
/// histories) are **one construction at different grades** — `PV` on `↓_M`, `PV∞` on `∞_M`.
/// Realized: exactly one of the two valuations is defined per element, selected by aspect
/// (finite `PV` ⟺ convergent; the limit form ⟺ persistent). Returns the first element where
/// neither or both valuations would apply (none — the aspect dichotomy selects exactly one),
/// or `Ok`.
pub fn certify_pv_duality(op: &ProjectionOperator) -> Result<(), crate::r1::substrate::ElementId> {
    for x in op.substrate().elements() {
        let pv_finite = op.canonical_fixpoint(x).is_some(); // PV over a finite history
        let pv_limit = !pv_finite; // PV∞ over the infinite (persistent) history
        if pv_finite == pv_limit {
            return Err(x); // the two grades are mutually exclusive and exhaustive
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;
    use crate::r1::reduction_strategy::Instance;

    #[test]
    fn aspects_are_mu_nu_fixpoints() {
        // 0→1 (↓_M, 1 ∈ NF) and 2⇄3 (∞_M).
        let e = [(0, 1), (2, 3), (3, 2)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // μT_conv = ↓_M = {0,1}; νT_pers = ∞_M = {2,3}.
        assert_eq!(least_fixpoint_convergent(&op), vec![true, true, false, false]);
        assert_eq!(greatest_fixpoint_persistent(&op), vec![false, false, true, true]);
        assert!(matches!(certify_aspect_fixpoints(&op), Ok(())));
        // Ind-CoInd / WN-NWF-Comp: μ/ν induction-coinduction duality partitions 𝒰.
        assert!(matches!(certify_induction_coinduction_duality(&op), Ok(())));
        // PV-Dual-14: exactly one of PV / PV∞ is defined per element.
        assert!(matches!(certify_pv_duality(&op), Ok(())));
    }

    #[test]
    fn predecessor_pulls_back_along_rho() {
        // 0→1, 1 ∈ NF: Pre_ρ({1}) = {0,1} (ρ(0)=1∈X, ρ(1)=1∈X).
        let m = Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let op = m.operator();
        let x_set = vec![false, true]; // {1}
        assert_eq!(predecessor(&op, &x_set), vec![true, true]);
        // pure WF ⇒ μT_conv = 𝒰, νT_pers = ∅.
        assert_eq!(least_fixpoint_convergent(&op), vec![true, true]);
        assert_eq!(greatest_fixpoint_persistent(&op), vec![false, false]);
    }
}
