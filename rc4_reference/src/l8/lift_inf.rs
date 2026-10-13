//! # L8.5 — The NWF-Extended Lift Lift∞(M)
//!
//! Exact realization of spec section **L8.5** (`CRPT_OMEGA_TOWER_L8.md`, v1.0.0-rc4):
//!
//! - L8.5.D1 `NWF-Quot` — the NWF abstraction quotient `Q_M* = {[x]_{≃∞} | x ∈ ∞_M, SC-4}
//!   ⊆ Q∞_M`. On a finite substrate every persistent element is SC-4, so `Q_M* = Q∞_M`
//!   (`≃∞` L3.3.D7 / `Q∞` L3.3.D8) exactly.
//! - L8.5.D2 `Lift∞` — `Lift∞(M)` has universe `FMA(Q_M) ∪ FMA_∞(Q_M*)`: the convergent
//!   atoms `Q_M` are period-1 fixpoints (the well-founded [`crate::l8::lift`] part), and
//!   each persistent atom `σ ∈ Q_M*` generates a **periodic** element of minimal period
//!   `CPD(σ)` (`CPD` L4.5.D1) — the cofree-coalgebra term whose observable content is
//!   the `CPD(σ)`-cycle.
//! - L8.5.T1 `NWF-Per` — `ρ^{CPD(σ)}(ι*(σ)) = ι*(σ)`: each persistent class reappears as a
//!   periodic fixpoint of period `CPD(σ)`.
//! - L8.5.T2 `Lift∞-NWF` — `Lift∞(M)` satisfies PA-NWF: `∞_{Lift∞(M)} ≠ ∅` whenever there
//!   is a persistent atom (its periodic orbit is infinite).
//!
//! The convergent part is the symbolic [`crate::l8::lift::Lift`] over `Q_M`. The
//! persistent part is represented by its observable content: each `σ ∈ Q_M*` together
//! with its period `CPD(σ) = |σ|` (a class is an ω-limit set of `CPD(σ)` ≈-classes), and
//! a witness ∞_M element. (A non-degenerate `Q_M*` needs the substrate's observation
//! labeling, L1.1.D6 — see the module tests.)

use crate::l1::substrate::ElementId;
use crate::l2::projection::Model;
use crate::l3::persistent::omega_limit_set;
use crate::l4::projection_depth::canonical_period;
use crate::l8::lift::{lift, Lift};

/// A persistent atom of `Lift∞(M)` — a class `σ ∈ Q_M*` (L8.5.D1) that becomes a periodic
/// generator of period `CPD(σ)`.
#[derive(Debug, Clone)]
pub struct PersistentAtom {
    /// The `≃∞` class as the ω-limit set of its ≈-classes (L3.3.D1); ascending.
    pub omega_limit: Vec<ElementId>,
    /// The minimal period `CPD(σ) = |σ|` of the generated periodic orbit (L4.5.D1).
    pub period: u32,
    /// A witnessing ∞_M element of this class.
    pub witness: ElementId,
}

/// **L8.5.D2 (`Lift∞`)** — the NWF-extended lift `Lift∞(M)`: the convergent atom set
/// `Q_M` (period-1 fixpoints) and the persistent atom set `Q_M*` (period-`CPD` generators).
pub struct LiftInf {
    convergent_atoms: Vec<ElementId>,
    persistent_atoms: Vec<PersistentAtom>,
}

/// **L8.5.D1 (`NWF-Quot`)** — `Q_M*`: the persistent abstraction quotient with each
/// class's period `CPD(σ)` and a witness. (`= Q∞_M` on a finite substrate.)
pub fn nwf_quotient(base: &Model) -> Vec<PersistentAtom> {
    let op = base.operator();
    let mut atoms: Vec<PersistentAtom> = Vec::new();
    for x in base.substrate().elements() {
        if let Some(period) = canonical_period(&op, x) {
            let omega_limit = omega_limit_set(&op, x);
            if !atoms.iter().any(|a| a.omega_limit == omega_limit) {
                atoms.push(PersistentAtom { omega_limit, period, witness: x });
            }
        }
    }
    atoms
}

/// **L8.5.D2 (`Lift∞`)**: `Lift∞(M)` — the convergent atoms `Q_M` (= base fixpoints) and
/// the persistent atoms `Q_M*` (the NWF quotient with periods).
pub fn lift_inf(base: &Model) -> LiftInf {
    LiftInf {
        convergent_atoms: base.operator().fixpoints(),
        persistent_atoms: nwf_quotient(base),
    }
}

impl LiftInf {
    /// The convergent atom set `Q_M` (period-1 fixpoint atoms). The well-founded part of
    /// `Lift∞(M)` is the symbolic [`Lift`] over these.
    pub fn convergent_atoms(&self) -> &[ElementId] {
        &self.convergent_atoms
    }

    /// The convergent (well-founded) lift `Lift(M)` over `Q_M` — `FMA(Q_M)` (L8.2.D2).
    pub fn convergent_lift(&self, base: &Model) -> Lift {
        lift(base)
    }

    /// The persistent atom set `Q_M*` (period-`CPD` generators, L8.5.D1).
    pub fn persistent_atoms(&self) -> &[PersistentAtom] {
        &self.persistent_atoms
    }

    /// **L8.5.T2 (`Lift∞-NWF`)** — `Lift∞(M)` satisfies PA-NWF (`∞_{Lift∞(M)} ≠ ∅`) iff it
    /// has a persistent atom (a periodic generator whose orbit is infinite).
    pub fn is_non_well_founded(&self) -> bool {
        !self.persistent_atoms.is_empty()
    }

    /// Witness **L8.5.T1 (`NWF-Per`)** — each persistent atom's stored period equals
    /// `CPD(σ)` of its witnessing element (so `ι*(σ)` is a periodic fixpoint of period
    /// `CPD(σ)`). Also confirms `CPD(σ) = |σ|`. Returns the first inconsistent witness, or `Ok`.
    pub fn certify_nwf_periodicity(&self, base: &Model) -> Result<(), ElementId> {
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
    use crate::l1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn nwf_quotient_carries_periods() {
        // Mixed: 0→1, 1 ∈ NF (↓_M, Q_M = {1}); 2→3→2 with distinct obs on 2,3 (Type EP,
        // CPD = 2, one Q_M* class).
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let li = lift_inf(&m);
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
    fn pure_wf_lift_inf_has_no_persistent_atoms() {
        // 0→1, 1 ∈ NF: pure WF ⇒ Q_M* = ∅ ⇒ Lift∞ is well-founded (no NWF atoms).
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let li = lift_inf(&m);
        assert_eq!(li.convergent_atoms(), &[id(1)]);
        assert!(li.persistent_atoms().is_empty());
        assert!(!li.is_non_well_founded());
    }
}
