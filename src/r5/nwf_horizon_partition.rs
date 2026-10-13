//! # R5.4 — NWF Horizon Partition (the persistent six-class A*–F*)
//!
//! Exact realization of spec section **R5.4** (`CRPT_OMEGA_TOWER_R5.md`, v1.0.0-rc9),
//! which is stated using **asymptotic invariants only** — bisimilarity `≈`
//! (R1.1.D6), persistent orbit equivalence `≃∞` (R2.3.D7), and the canonical period
//! `CPD` (R3.5.D1) — so the predicates are total on ∞_M (under SC-4, automatic on a
//! finite substrate) with no appeal to `PA-WN_top`:
//!
//! - R5.4.D1 `H_S*` — `H_S*(x) :⟺ ∃y ∈ ∞_M : y ≉ x ∧ ρ_M(y) ≃∞ ρ_M(x)` (an asymptotic
//!   co-sibling — a non-bisimilar persistent `y` whose one-step image shares x's `≃∞`
//!   class).
//! - R5.4.D2 `H_I*` — `H_I*(x) :⟺ H_S*(x) ∧ ∀y : (y ≉ x ∧ ρ_M(y) ≃∞ ρ_M(x)) ⟹
//!   sig_M*(y) = sig_M*(x)`, with the persistent orbit signature `sig_M*(x) := (H_S*(x),
//!   CPD(x))`.
//! - R5.4.D3 `H_O*` — `H_O*(x) :⟺ CPD(x) = 1` (a co-fixpoint: period 1 in the
//!   bisimulation-quotient stable tail).
//! - R5.4.D4 `A*-F*` — the six classes by `(H_O*, H_S*, H_I*)`; R5.4.T1 `NWF-6P` is the
//!   exhaustive disjoint partition of ∞_M, with **Class F\* provably empty**.
//!
//! Non-degeneracy of this partition needs the substrate's observation labeling `obs`
//! (R1.1.D6) to distinguish persistent elements; on the minimal (NF-anchored) `obs`,
//! every persistent element is Type P and the partition concentrates on D*.

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_persistent;
use crate::r2::canonical_orbit_invariant::persistent_equivalent;
use crate::r3::projection_depth::canonical_period;

/// **R5.4.D1 (`H_S*`)** — the NWF structural co-horizon: `x` has an asymptotic co-sibling
/// (a non-bisimilar persistent `y` with `ρ_M(y) ≃∞ ρ_M(x)`). `false` off ∞_M.
pub fn nwf_structural_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    if !is_persistent(op, x) {
        return false;
    }
    let representative = op.substrate().bisimilarity();
    let image_of_x = op.project(x);
    op.substrate().elements().any(|y| {
        is_persistent(op, y)
            && representative[y.index()] != representative[x.index()] // y ≉ x
            && persistent_equivalent(op, op.project(y), image_of_x) // ρ_M(y) ≃∞ ρ_M(x)
    })
}

/// **R5.4.D3 (`H_O*`)** — the NWF ontological co-horizon: `CPD(x) = 1` (a co-fixpoint).
/// `false` off ∞_M.
pub fn nwf_ontological_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    canonical_period(op, x) == Some(1)
}

/// The persistent orbit signature `sig_M*(x) := (H_S*(x), CPD(x))` (R5.4.D2).
fn nwf_signature(op: &ProjectionOperator, x: ElementId) -> (bool, Option<u32>) {
    (nwf_structural_horizon(op, x), canonical_period(op, x))
}

/// **R5.4.D2 (`H_I*`)** — the NWF invariant co-horizon: `H_S*(x)` and all asymptotic
/// co-siblings of `x` carry the same `sig_M*`. `false` off ∞_M.
pub fn nwf_invariant_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    if !nwf_structural_horizon(op, x) {
        return false;
    }
    let representative = op.substrate().bisimilarity();
    let image_of_x = op.project(x);
    let signature_of_x = nwf_signature(op, x);
    op.substrate().elements().all(|y| {
        let is_co_sibling = is_persistent(op, y)
            && representative[y.index()] != representative[x.index()]
            && persistent_equivalent(op, op.project(y), image_of_x);
        !is_co_sibling || nwf_signature(op, y) == signature_of_x
    })
}

/// **R5.4.D4 (`A*-F*`)** — the NWF six classes of the persistent aspect. `==` compares
/// the computed class tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NwfClass {
    /// A\* — `(H_O*, H_S*, H_I*) = (⊥, ⊥, ⊥)`: pre-orbit, no co-horizon.
    AStar,
    /// B\* — `(⊥, ⊤, ⊥)`: pre-orbit, structural co-horizon, distinguishable.
    BStar,
    /// C\* — `(⊥, ⊤, ⊤)`: pre-orbit, structural co-horizon, invisible.
    CStar,
    /// D\* — `(⊤, ⊥, —)`: period-1 co-fixpoint, unique orbit class.
    DStar,
    /// E\* — `(⊤, ⊤, ⊥)`: period-1 co-fixpoint, structural co-horizon, distinguishable.
    EStar,
    /// F\* — `(⊤, ⊤, ⊤)`: period-1 co-fixpoint, full co-horizon. **Provably empty** (R5.4.T1).
    FStar,
}

/// **R5.4.D4 (`A*-F*`)** — classify a persistent element. `None` off ∞_M (the NWF
/// six-class covers νT_{ρ,M} only; ↓_M is covered by the R2.2 six-class).
pub fn nwf_classify(op: &ProjectionOperator, x: ElementId) -> Option<NwfClass> {
    if !is_persistent(op, x) {
        return None;
    }
    let h_o = nwf_ontological_horizon(op, x);
    let h_s = nwf_structural_horizon(op, x);
    let h_i = nwf_invariant_horizon(op, x); // implies h_s
    Some(match (h_o, h_s, h_i) {
        (false, false, _) => NwfClass::AStar,
        (false, true, false) => NwfClass::BStar,
        (false, true, true) => NwfClass::CStar,
        (true, false, _) => NwfClass::DStar,
        (true, true, false) => NwfClass::EStar,
        (true, true, true) => NwfClass::FStar,
    })
}

/// Witness **R5.4.T1 (`NWF-6P`)** — Class F\* is empty: no persistent element is
/// classified F\*. Returns the first F\* element found (never), or `Ok`.
pub fn certify_class_f_star_empty(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if nwf_classify(op, x) == Some(NwfClass::FStar) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R5.4.T1 (`NWF-6P`)** — the partition is total on ∞_M: every persistent
/// element receives exactly one NWF class, every convergent element none. Returns the
/// first element violating coverage, or `Ok`.
pub fn certify_nwf_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if is_persistent(op, x) != nwf_classify(op, x).is_some() {
            return Err(x);
        }
    }
    Ok(())
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
    fn type_p_cycle_is_class_d_star() {
        // 0⇄1 default obs: bisimilar (Type P, CPD=1) ⇒ H_O* ⊤; no non-bisimilar co-sibling
        // ⇒ H_S* ⊥ ⇒ Class D*.
        let e = [(0, 1), (1, 0)];
        let m = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert!(nwf_ontological_horizon(&op, id(0)));
        assert!(!nwf_structural_horizon(&op, id(0)));
        assert_eq!(nwf_classify(&op, id(0)), Some(NwfClass::DStar));
        assert!(matches!(certify_class_f_star_empty(&op), Ok(())));
        assert!(matches!(certify_nwf_partition(&op), Ok(())));
    }

    #[test]
    fn type_ep_cycle_is_class_c_star() {
        // 0→1→0 with distinct obs (Type EP, CPD=2) ⇒ H_O* ⊥. Each is the other's co-sibling
        // (1 ≉ 0, ρ(1)=0 ≃∞ ρ(0)=1) ⇒ H_S* ⊤; both have sig*=(⊤,2) ⇒ H_I* ⊤ ⇒ Class C*.
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Instance::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        assert!(!nwf_ontological_horizon(&op, id(0))); // CPD = 2
        assert!(nwf_structural_horizon(&op, id(0)));
        assert!(nwf_invariant_horizon(&op, id(0)));
        assert_eq!(nwf_classify(&op, id(0)), Some(NwfClass::CStar));
        assert_eq!(nwf_classify(&op, id(1)), Some(NwfClass::CStar));
        // ↓_M elements get no NWF class; F* empty; partition total.
        assert!(matches!(certify_class_f_star_empty(&op), Ok(())));
        assert!(matches!(certify_nwf_partition(&op), Ok(())));
    }
}
