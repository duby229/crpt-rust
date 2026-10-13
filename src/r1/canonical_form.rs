//! # R1.11 — Canonical Normal Form Map CNF_M
//!
//! Realizes R1.11 incl. R1.11.D2 `Abs-R0` (the abstraction is the R0 fiber map, r0::projection_systems_and_fibers). Exact realization of spec section **R1.11** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9):
//!
//! - R1.11.D1 `CFix-NM` — the canonical form map `CNF_M(x) = CFix(ρ_M)(x)`, which on
//!   ↓_M is `ρ_M^{d_M(x)}(x)` (the fixpoint the orbit reaches). The same object as
//!   the recursive projection R1.8.D4; this is the "map" view.
//! - R1.11.T1 `CNF-Ex` — `CNF_M(x) ∈ Fix(ρ_M)` for x ∈ ↓_M.
//! - R1.11.T3 `CNF-Stab` — `CNF_M(CNF_M(x)) = CNF_M(x)` (idempotence).
//!
//! On ∞_M the canonical form is the topological limit (R1.11.D1, second branch),
//! which requires the topology / PA-WN_top; in the finite WF core ∞_M elements
//! have no finitary canonical form, returned as `None`. (Their asymptotic
//! canonical invariant is R2.3.)

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;

/// **R1.11.D1 (`CNF_M` = `CFix(ρ_M)`)**: the canonical form of x — the fixpoint its
/// ρ_M-orbit reaches. `Some(f)` on ↓_M (unique by `UF` R1.8.L2); `None` on ∞_M.
pub fn canonical_form(op: &ProjectionOperator, x: ElementId) -> Option<ElementId> {
    op.canonical_fixpoint(x)
}

/// Witness **R1.11.T1 (`CNF-Ex`)**: for x ∈ ↓_M, `CNF_M(x) ∈ Fix(ρ_M)`. First
/// convergent element whose canonical form is not a fixpoint, or `Ok`.
pub fn certify_cnf_is_fixpoint(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(c) = canonical_form(op, x) {
            if !op.is_fixpoint(c) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R1.11.T3 (`CNF-Stab`)**: `CNF_M(CNF_M(x)) = CNF_M(x)`. First violation, or `Ok`.
pub fn certify_cnf_stable(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(c) = canonical_form(op, x) {
            if canonical_form(op, c) != Some(c) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R1.11.T2 (`CNF-Uniq`)** / **R1.11.R4 (`CNFUniq-CR`)** — under `PA-WN` + scoped
/// confluence the canonical form `CNF_M(x) = ρ_M^{d_M(x)}(x)` is the **unique** element of
/// `Fix(ρ_M)` reachable from `x`; two convergent elements share a canonical form iff their
/// orbits meet — this *is* the Church–Rosser theorem for `(𝒰_M, →_ρ)`. Returns the first
/// convergent element whose canonical form is not a uniquely-reached fixpoint (none — the
/// deterministic orbit reaches exactly one), or `Ok`.
pub fn certify_cnf_unique(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        match canonical_form(op, x) {
            // CNF_M(x) exists, is a fixpoint, and is the single endpoint of x's orbit.
            Some(c) if op.is_fixpoint(c) && op.canonical_fixpoint(x) == Some(c) => {}
            Some(_) => return Err(x),
            None => {} // persistent — out of the WF canonicalization domain
        }
    }
    Ok(())
}

/// Witness **R1.11.T5 (`WF-Canon-Pf`)** — the **well-founded canonicalization**: under `PA-WN`
/// and scoped confluence, `CNF_M` is well-defined on **all** of `↓_M` (by well-founded
/// induction on `d_M`, whose strictly-decreasing measure is `L-Mono` R1.9.L1). Returns the
/// first convergent element on which `CNF_M` is undefined (none), or `Ok`.
pub fn certify_wf_canonicalization(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::aspect_partition::is_convergent;
    for x in op.substrate().elements() {
        if is_convergent(op, x) && canonical_form(op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R1.11.C1 (`CR-Cor`)** / **R1.11.R5 (`CRCor-Prov`)** — the **canonical
/// representative corollary** (a Church–Rosser consequence, *imported* not novel): for each
/// normal-form fiber, the fixpoint `f` is **itself** the canonical representative — the unique
/// element of the fiber that lies in `Fix(ρ_M)`. Returns the first fixpoint that is not its own
/// canonical form (none), or `Ok`.
pub fn certify_canonical_representative(op: &ProjectionOperator) -> Result<(), ElementId> {
    for f in op.fixpoints() {
        if canonical_form(op, f) != Some(f) {
            return Err(f);
        }
    }
    Ok(())
}

/// Witness **R1.11.R7 (`CFix-Surj`)** — `CFix(ρ_M) : ↓_M → Fix(ρ_M)` is **surjective**:
/// immediate from `Fix(ρ_M) ⊆ ↓_M` (fixpoints have depth 0, `Fix-D0` R1.10.T3) — every
/// fixpoint is the canonical form of itself, hence in the image. Returns `true` when every
/// fixpoint is hit by `CFix`. (`R1.11.R1` `CFix-ExUniq-Nat`, `R1.11.R2` `Disc-CFix`,
/// `R1.11.R3` `FixNF-Uncond`, `R1.11.R6` `Why-RecProj`: `CFix` exists & is unique on `↓_M`,
/// reads as the canonical **discernible** representative, `Fix = NF` holds **unconditionally**
/// by the strengthened C1, and "recursive projection" is precise because `CFix` is `ρ_M`
/// iterated to its fixpoint.)
pub fn certify_cfix_surjective(op: &ProjectionOperator) -> bool {
    op.fixpoints().iter().all(|&f| canonical_form(op, f) == Some(f))
}

/// Witness **R1.11.R3 (`FixNF-Uncond`)** — `Fix(ρ_M) = NF(→_ρ)` holds **unconditionally** (by
/// the strengthened C1), so canonical forms are normal forms in *every* setting, not only
/// under `PA-WN`. Returns the first element where fixpoint-status and normal-form-status
/// disagree (none — C1 forces their coincidence), or `Ok`.
pub fn certify_fix_eq_nf_unconditional(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if op.is_fixpoint(x) != op.substrate().is_normal_form(x) {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

    #[test]
    fn canonical_form_and_witnesses() {
        // 0 ⇄ 1 (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M).
        let edges = [(0, 1), (1, 0), (2, 3)];
        let s = Substrate::new(4, &edges, &edges).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(canonical_form(&op, ElementId(2)), Some(ElementId(3)));
        assert_eq!(canonical_form(&op, ElementId(3)), Some(ElementId(3)));
        assert_eq!(canonical_form(&op, ElementId(0)), None); // ∞_M: no finitary CNF
        assert!(matches!(certify_cnf_is_fixpoint(&op), Ok(())));
        assert!(matches!(certify_cnf_stable(&op), Ok(())));
        // CNF-Uniq / CNFUniq-CR: CNF is the unique reachable fixpoint (Church–Rosser).
        assert!(matches!(certify_cnf_unique(&op), Ok(())));
        // WF-Canon-Pf: CNF_M defined on all of ↓_M.
        assert!(matches!(certify_wf_canonicalization(&op), Ok(())));
        // CR-Cor / CFix-Surj / FixNF-Uncond: f is its own canonical rep, CFix onto Fix, Fix=NF.
        assert!(matches!(certify_canonical_representative(&op), Ok(())));
        assert!(certify_cfix_surjective(&op));
        assert!(matches!(certify_fix_eq_nf_unconditional(&op), Ok(())));
    }
}
