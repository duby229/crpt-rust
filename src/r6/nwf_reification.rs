//! # R6.8 — The NWF-Extended Reify Reify∞(M)
//!
//! Exact realization of spec section **R6.8** (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.8.D1 `NWF-Quot` — the NWF abstraction quotient `Q_M* = {[x]_{≃∞} | x ∈ ∞_M, SC-4}
//!   ⊆ Q∞_M`. On a finite substrate every persistent element is SC-4, so `Q_M* = Q∞_M`
//!   (`≃∞` R2.3.D7 / `Q∞` R2.3.D8) exactly.
//! - R6.8.D2 `Reify∞` — `Reify∞(M)` has universe `FMA(Q_M) ∪ FMA_∞(Q_M*)`: the convergent
//!   atoms `Q_M` are period-1 fixpoints (the well-founded [`crate::r6::reification_operator`] part), and
//!   each persistent atom `σ ∈ Q_M*` generates a **periodic** element of minimal period
//!   `CPD(σ)` (`CPD` R3.5.D1) — the cofree-coalgebra term whose observable content is
//!   the `CPD(σ)`-cycle.
//! - R6.8.T1 `NWF-Per` — `ρ^{CPD(σ)}(ι*(σ)) = ι*(σ)`: each persistent class reappears as a
//!   periodic fixpoint of period `CPD(σ)`.
//! - R6.8.T2 `Reify∞-NWF` — `Reify∞(M)` satisfies PA-NWF: `∞_{Reify∞(M)} ≠ ∅` whenever there
//!   is a persistent atom (its periodic orbit is infinite).
//!
//! The convergent part is the symbolic [`crate::r6::reification_operator::Reify`] over `Q_M`. The
//! persistent part is represented by its observable content: each `σ ∈ Q_M*` together
//! with its period `CPD(σ) = |σ|` (a class is an ω-limit set of `CPD(σ)` ≈-classes), and
//! a witness ∞_M element. (A non-degenerate `Q_M*` needs the substrate's observation
//! labeling, R1.1.D6 — see the module tests.)

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::Instance;
use crate::r2::canonical_orbit_invariant::omega_limit_classes;
use crate::r3::projection_depth::canonical_period;
use crate::r6::reification_operator::{reify, Reify};

/// A persistent atom of `Reify∞(M)` — a class `σ ∈ Q_M*` (R6.8.D1) that becomes a periodic
/// generator of period `CPD(σ)`.
#[derive(Debug, Clone)]
pub struct PersistentAtom {
    /// The `≃∞` class as the ω-limit set of its ≈-classes (R2.3.D1); ascending.
    pub omega_limit: Vec<ElementId>,
    /// The minimal period `CPD(σ) = |σ|` of the generated periodic orbit (R3.5.D1).
    pub period: u32,
    /// A witnessing ∞_M element of this class.
    pub witness: ElementId,
}

/// **R6.8.D2 (`Reify∞`)** — the NWF-extended reify `Reify∞(M)`: the convergent atom set
/// `Q_M` (period-1 fixpoints) and the persistent atom set `Q_M*` (period-`CPD` generators).
pub struct ReifyInf {
    convergent_atoms: Vec<ElementId>,
    persistent_atoms: Vec<PersistentAtom>,
}

/// **R6.8.D1 (`NWF-Quot`)** — `Q_M*`: the persistent abstraction quotient with each
/// class's period `CPD(σ)` and a witness. (`= Q∞_M` on a finite substrate.)
pub fn nwf_quotient(base: &Instance) -> Vec<PersistentAtom> {
    let op = base.operator();
    let mut atoms: Vec<PersistentAtom> = Vec::new();
    for x in base.substrate().elements() {
        if let Some(period) = canonical_period(&op, x) {
            let omega_limit = omega_limit_classes(&op, x);
            if !atoms.iter().any(|a| a.omega_limit == omega_limit) {
                atoms.push(PersistentAtom { omega_limit, period, witness: x });
            }
        }
    }
    atoms
}

/// **R6.8.D2 (`Reify∞`)**: `Reify∞(M)` — the convergent atoms `Q_M` (= base fixpoints) and
/// the persistent atoms `Q_M*` (the NWF quotient with periods).
pub fn reify_inf(base: &Instance) -> ReifyInf {
    ReifyInf {
        convergent_atoms: base.operator().fixpoints(),
        persistent_atoms: nwf_quotient(base),
    }
}

impl ReifyInf {
    /// The convergent atom set `Q_M` (period-1 fixpoint atoms). The well-founded part of
    /// `Reify∞(M)` is the symbolic [`Reify`] over these.
    pub fn convergent_atoms(&self) -> &[ElementId] {
        &self.convergent_atoms
    }

    /// The convergent (well-founded) reify `Reify(M)` over `Q_M` — `FMA(Q_M)` (R6.5.D2).
    pub fn convergent_lift(&self, base: &Instance) -> Reify {
        reify(base)
    }

    /// The persistent atom set `Q_M*` (period-`CPD` generators, R6.8.D1).
    pub fn persistent_atoms(&self) -> &[PersistentAtom] {
        &self.persistent_atoms
    }

    /// **R6.8.T2 (`Reify∞-NWF`)** — `Reify∞(M)` satisfies PA-NWF (`∞_{Reify∞(M)} ≠ ∅`) iff it
    /// has a persistent atom (a periodic generator whose orbit is infinite).
    pub fn is_non_well_founded(&self) -> bool {
        !self.persistent_atoms.is_empty()
    }

    /// Witness **R6.8.T1 (`NWF-Per`)** — each persistent atom's stored period equals
    /// `CPD(σ)` of its witnessing element (so `ι*(σ)` is a periodic fixpoint of period
    /// `CPD(σ)`). Also confirms `CPD(σ) = |σ|`. Returns the first inconsistent witness, or `Ok`.
    pub fn certify_nwf_periodicity(&self, base: &Instance) -> Result<(), ElementId> {
        let op = base.operator();
        for atom in &self.persistent_atoms {
            let cpd = canonical_period(&op, atom.witness);
            if cpd != Some(atom.period) || atom.period != atom.omega_limit.len() as u32 {
                return Err(atom.witness);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn nwf_quotient_carries_periods() {
        // Mixed: 0→1, 1 ∈ NF (↓_M, Q_M = {1}); 2→3→2 with distinct obs on 2,3 (Type EP,
        // CPD = 2, one Q_M* class).
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Instance::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let li = reify_inf(&m);
        // Q_M = {1} (the single fixpoint).
        assert_eq!(li.convergent_atoms(), &[id(1)]);
        // Q_M* = one persistent class of period CPD = 2.
        assert_eq!(li.persistent_atoms().len(), 1);
        assert_eq!(li.persistent_atoms()[0].period, 2);
        // PA-NWF holds; NWF-Per consistent (period = CPD = |ω-limit|).
        assert!(li.is_non_well_founded());
        assert!(matches!(li.certify_nwf_periodicity(&m), Ok(())));
    }

    #[test]
    fn nwf_quotient_uses_bisimulation_classes_for_type_p_cycles() {
        // 0⇄1 with default observation: the quotient orbit is a singleton class, so the
        // persistent atom should be a single SC-1 class of period 1, not a two-element orbit.
        let e = [(0, 1), (1, 0)];
        let m = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let li = reify_inf(&m);
        assert_eq!(li.persistent_atoms().len(), 1);
        assert_eq!(li.persistent_atoms()[0].period, 1);
        assert_eq!(li.persistent_atoms()[0].omega_limit.len(), 1);
        assert!(matches!(li.certify_nwf_periodicity(&m), Ok(())));
    }

    #[test]
    fn pure_wf_reify_inf_has_no_persistent_atoms() {
        // 0→1, 1 ∈ NF: pure WF ⇒ Q_M* = ∅ ⇒ Reify∞ is well-founded (no NWF atoms).
        let m = Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let li = reify_inf(&m);
        assert_eq!(li.convergent_atoms(), &[id(1)]);
        assert!(li.persistent_atoms().is_empty());
        assert!(!li.is_non_well_founded());
    }
}
