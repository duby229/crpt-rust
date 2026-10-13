//! # Rω.7 — Supplementary Lemmas
//!
//! Exact realization of spec section **Rω.7** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9):
//!
//! - Rω.7.L1 `CRPT-Acyclic` — `→_{ρ_CRPT}` is acyclic (no construct depends on itself
//!   directly or transitively): the dependency level strictly decreases along every edge.
//! - Rω.7.R2 `Self-CRPT-Finite` — `|𝒰_CRPT| < ω` (finitely many labelled constructs).
//! - Rω.7.T1 `CRPT-WF` — the self-application is pure well-founded **on the dependency
//!   reading**: `∞_CRPT^ρ = ∅`; every construct reaches `Fix(ρ_CRPT) = {R1.1.D1}` in finitely
//!   many steps. (Scoped to `ρ_CRPT`; the structural reading `→_σ_CRPT` is NWF, so the full
//!   self-model is **Mixed** — `Self-Inf`/`Self-Mixed` Rω.1.D2/T2.)
//! - Rω.7.T2 `Rω-FixedPt-Unique` — `Fix(ρ_CRPT) = {R1.1.D1}`: the substrate definition is
//!   the **unique** projective fixed point (the unique sink of the dependency DAG).
//!
//! All four are certified directly on the [`self_substrate`].

use crate::r1::substrate::ElementId;
use crate::romega::self_projection_system::{self_substrate, R1_1_D1};

/// Witness **Rω.7.L1 (`CRPT-Acyclic`)** — `→_{ρ_CRPT}` has no positive-length cycles: every
/// non-fixpoint's `ρ_CRPT`-orbit strictly descends to the root without revisiting a
/// construct. Returns the first construct whose orbit revisits a node (none), or `Ok`.
pub fn certify_acyclic() -> Result<(), ElementId> {
    let m = self_substrate();
    let op = m.operator();
    let n = op.substrate().universe_len();
    for x in op.substrate().elements() {
        // walk the orbit; a non-fixpoint that returns to a seen node is a cycle.
        let mut seen = vec![x];
        let mut current = x;
        for _ in 0..=n {
            if op.is_fixpoint(current) {
                break;
            }
            current = op.project(current);
            if seen.contains(&current) && !op.is_fixpoint(current) {
                return Err(x); // a positive-length cycle
            }
            seen.push(current);
        }
    }
    Ok(())
}

/// **Rω.7.R2 (`Self-CRPT-Finite`)** — `|𝒰_CRPT|`, the (finite) cardinality of the
/// self-substrate. Finiteness is structural: the engine realizes the self-instance as a
/// finite dense universe.
pub fn self_substrate_cardinality() -> u32 {
    self_substrate().substrate().universe_len()
}

/// Witness **Rω.7.T1 (`CRPT-WF`)** — the self-application is pure well-founded **on the
/// dependency reading**: `∞_CRPT^ρ = ∅`. Every construct converges to the root `R1.1.D1` in
/// finitely many `ρ_CRPT`-steps. (Scoped to `ρ_CRPT` — the structural reading is NWF, so the
/// full model is Mixed, `Self-Mixed` Rω.1.T2.) Returns the first `ρ`-persistent construct
/// (none), or `Ok`.
pub fn certify_pure_wf() -> Result<(), ElementId> {
    let m = self_substrate();
    let op = m.operator();
    for x in op.substrate().elements() {
        // x ∈ ↓_CRPT iff its orbit reaches the unique fixpoint R1.1.D1.
        if op.canonical_fixpoint(x) != Some(R1_1_D1) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **Rω.7.T2 (`Rω-FixedPt-Unique`)** — `Fix(ρ_CRPT) = {R1.1.D1}`: the substrate
/// definition is the unique projective fixed point. `true` when the only fixpoint is the root.
pub fn certify_unique_fixpoint() -> bool {
    self_substrate().operator().fixpoints() == vec![R1_1_D1]
}

/// Witness **Rω.7.R1 (`Acyc-Term`)** — **acyclicity implies termination**: acyclicity
/// (`CRPT-Acyclic` Rω.7.L1) together with finiteness of `𝒰_CRPT` (`Self-CRPT-Finite` Rω.7.R2)
/// implies every construct reaches `Fix(ρ_CRPT)` in finitely many steps — a finite acyclic
/// graph has no infinite descending chains. Returns `true` when the self-substrate is both
/// acyclic and finite (so termination follows).
pub fn acyclicity_implies_termination() -> bool {
    certify_acyclic().is_ok() && self_substrate_cardinality() < u32::MAX
}

/// Witness **Rω.7.R3 (`AspPart-Extract`)** — the **formal extraction** of the aspect-partition
/// claim of Rω.1.T1(5): the self-substrate is **purely convergent on the dependency reading**
/// (`↓_CRPT^ρ = 𝒰_CRPT`, `∞_CRPT^ρ = ∅`), proved from finiteness and acyclicity alone — not
/// requiring the full CRPT axiom apparatus nor circular self-reference. (Scoped to `ρ_CRPT`;
/// the structural dual `∞_CRPT^σ ≠ ∅` makes the full model Mixed, `Self-Mixed` Rω.1.T2.)
/// Returns `true` when the dependency reading is pure-WF ([`certify_pure_wf`]).
pub fn aspect_partition_extracted() -> bool {
    certify_pure_wf().is_ok()
}

/// **Rω.7.R4 (`FixUniq-Scope`)** — the **scope** of the uniqueness claim: `Rω-FixedPt-Unique`
/// (Rω.7.T2) is specifically about **projective fixed points** (elements fixed by `ρ_CRPT`
/// itself) — `Fix(ρ_CRPT) = {R1.1.D1}` — distinct from the stronger self-consistency fixed
/// point of `Self-FP` (Rω.5.T1, the level structure as a meta-HOA fixed point). Returns `true`
/// when the projective-fixpoint uniqueness holds ([`certify_unique_fixpoint`]).
pub fn fixpoint_uniqueness_is_projective() -> bool {
    certify_unique_fixpoint()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_self_application_is_finite_acyclic_pure_wf_with_a_unique_root() {
        assert!(matches!(certify_acyclic(), Ok(()))); // CRPT-Acyclic
        assert_eq!(self_substrate_cardinality(), 15); // Self-CRPT-Finite (|𝒰_CRPT| < ω)
        assert!(matches!(certify_pure_wf(), Ok(()))); // CRPT-WF (∞_CRPT = ∅)
        assert!(certify_unique_fixpoint()); // Rω-FixedPt-Unique
    }
}
