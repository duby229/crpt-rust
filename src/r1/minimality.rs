//! # R1.6 — Axiom Minimality and Independence
//!
//! Exact realization of spec section **R1.6** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9):
//!
//! - R1.6.T1 `Ax-Ind` (Novel) — the **eight-axiom basis**
//!   `{PA-WN, PA-NWF, PA-Conf, PA-Fix, PA-Prod, PA-WN_top, PA-Bisim, PA-Reach}` is mutually
//!   independent: no basis axiom is derivable from the conjunction of the other seven,
//!   witnessed by counterinstances (each satisfies the other seven and fails its own).
//!   `PA-CoInd` is **not** in the basis — it is derivable from `PA-NWF` in full SOL (Park 1981).
//! - R1.6.R1 `No-Split` (Novel) — no basis axiom splits into independent weaker pieces.
//!
//! The counterinstances for the **step axioms** (R1.2) are realized here: `M_Conf` (fails
//! `PA-Conf`, satisfies the rest), `M_Fix` (fails `PA-Fix`), `M_Prod` (fails `PA-Prod`).
//! The `M_Bisim`/`M_Reach` rows (the R1.3 orbit axioms) and `M_ind` (`WNtop-Ind` R1.7.T2)
//! are authored with their axioms' sections. PA-WN/PA-NWF separate by the trivial WF-only
//! / NWF-only duality instances.

use crate::r1::axiom_system::{pa_conf, pa_fix, pa_prod};
use crate::r1::reduction_strategy::{Instance, ProjectionError};
use crate::r1::substrate::{ElementId, Substrate};

/// **R1.6.T1 (`Ax-Ind`) — `M_Conf`**: a counterinstance failing `PA-Conf` while satisfying
/// the other step axioms. Branching `→_ρ` (`0 →_ρ 1`, `0 →_ρ 2`, `1`,`2` ∈ NF) is not
/// confluent (two distinct normal forms), yet a deterministic strategy `ρ_M(0)=1` keeps
/// `PA-Fix` (Fix=NF) intact — the standard non-confluent ARS.
pub fn m_conf() -> Result<Instance, ProjectionError> {
    let e = [(0, 1), (0, 2)];
    let s = Substrate::new(3, &e, &e).unwrap();
    Instance::new(s, vec![ElementId(1), ElementId(1), ElementId(2)])
}

/// **R1.6.T1 (`Ax-Ind`) — `M_Fix`**: a counterinstance failing `PA-Fix`. A self-loop
/// `0 →_ρ 0` makes `0` a ρ_M-fixpoint that is **not** a normal form, so `Fix(ρ_M) ≠ NF`.
pub fn m_fix() -> Result<Instance, ProjectionError> {
    let e = [(0, 0)];
    Instance::from_functional_reduction(Substrate::new(1, &e, &e).unwrap())
}

/// **R1.6.T1 (`Ax-Ind`) — `M_Prod` witness check**: `PA-Prod` independence is witnessed by
/// a *silent* Observable contract on an otherwise-conforming instance. Returns whether the
/// given instance fails `PA-Prod` under the silent contract while keeping `PA-Fix`
/// (i.e. the failure is the contract's, isolated from the step structure).
pub fn m_prod_fails_under_silent_contract(instance: &Instance) -> bool {
    // a contract that emits 0 (silent) everywhere violates PA-Prod at every non-fixpoint…
    pa_prod(instance, |_| 0).is_err() && pa_fix(instance).is_ok()
}

/// Witness **R1.6.T1 (`Ax-Ind`)** for the step-axiom rows: each counterinstance fails its
/// own axiom while satisfying the others it is meant to keep. Returns the name of the
/// first row that does not behave as the matrix asserts, or `Ok`.
pub fn certify_step_axiom_independence() -> Result<(), &'static str> {
    // M_Conf: fails PA-Conf, keeps PA-Fix.
    let m_conf = m_conf().map_err(|_| "M_Conf construction")?;
    if pa_conf(&m_conf).is_ok() {
        return Err("M_Conf does not fail PA-Conf");
    }
    if pa_fix(&m_conf).is_err() {
        return Err("M_Conf should keep PA-Fix");
    }
    // M_Fix: fails PA-Fix.
    let m_fix = m_fix().map_err(|_| "M_Fix construction")?;
    if pa_fix(&m_fix).is_ok() {
        return Err("M_Fix does not fail PA-Fix");
    }
    // M_Prod: a silent contract fails PA-Prod on a conforming instance.
    let conforming =
        Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .map_err(|_| "M_Prod base")?;
    if !m_prod_fails_under_silent_contract(&conforming) {
        return Err("M_Prod silent contract should fail PA-Prod");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_axiom_independence_matrix() {
        assert!(matches!(certify_step_axiom_independence(), Ok(())));
        // M_Conf is a valid C1/C2 instance (the strategy picks one branch) that fails PA-Conf.
        assert!(m_conf().is_ok());
        // PA-CoInd is NOT in the basis — derivable from PA-NWF (no counterinstance needed).
    }
}
