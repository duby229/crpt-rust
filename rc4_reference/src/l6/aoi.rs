//! # L6.1 — Asymptotic Orbit Invariants (AOI)
//!
//! Exact realization of spec section **L6.1** (`CRPT_OMEGA_TOWER_L6.md`, v1.0.0-rc4) —
//! the three-level hierarchy of bisimulation-invariant invariants for persistent orbits:
//!
//! - L6.1.D1 `OT` / L6.3.D1 `OT-21B` — the **orbit trace** `OT(x) = ([ρ_M^n(x)]_≈)_n`, the sequence of
//!   bisimulation classes the orbit visits. On a finite substrate it is eventually
//!   periodic (`SC4-EP` L3.3.T1), represented exactly as a (transient, cycle) of
//!   ≈-class representatives. L6.1.T1 `AOI1-BisInv`: `x ≈ y ⟹ OT(x) = OT(y)`.
//! - L6.1.T2 `AOI3-Ext` / L6.3.D2 `Tail-Eq` / L6.3.D3 `AOI₁` — `AOI₁(x) := [OT(x)]_tail` (the tail-equivalence class), which
//!   refines `≃∞` (it carries the cyclic *order* of the ω-limit classes, not just the
//!   set). For Type P, `OT` is eventually constant `(CNF∞_M(x), …)`.
//! - L6.1.D2 `OS` / L6.3.D4 `Freq` / L6.3.D5 `OS-21B` / L6.3.D6 `Spec-Def` — the **orbit spectrum** `OS_M(x)`: the asymptotic visit-frequency
//!   distribution over ≈-classes. On a finite (eventually-periodic) orbit the limit is
//!   the cycle's uniform distribution — each ω-limit class with frequency `1/CPD`.
//!   L6.1.T3 `AOI5-Spec`: `x ≈ y ⟹ OS(x) = OS(y)`.
//! - L6.1.D3 `OC` / L6.3.D9 `OC-21B` — the **orbit complexity** (Borel rank of `{OT(x)}`). For a periodic
//!   orbit `OC = 0` (Σ⁰₁, minimal); every finite-substrate orbit is periodic, so
//!   `OC ≡ 0` here — the aperiodic `OC > 0` case (Type AP) needs an infinite substrate.

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::is_persistent;

/// **L6.1.D1 (`OT`)** — the orbit trace as an eventually-periodic sequence of ≈-class
/// representatives: `OT(x) = transient · cycleᵒᵐᵉᵍᵃ`. `==` compares the computed trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrbitTrace {
    /// The pre-periodic prefix of ≈-classes (length `N(x)`), before the cycle is entered.
    pub transient: Vec<ElementId>,
    /// The repeating cycle of ≈-classes (length `CPD(x)`), in orbit order.
    pub cycle: Vec<ElementId>,
}

/// The quotient orbit `([ρ_M^n(x)]_≈)_n` as `(transient, cycle)` of ≈-class reps; `None`
/// on ↓_M. Computed by following the orbit's bisimulation classes until one repeats.
fn quotient_orbit(op: &ProjectionOperator, x: ElementId) -> Option<(Vec<ElementId>, Vec<ElementId>)> {
    if !is_persistent(op, x) {
        return None;
    }
    let representative = op.substrate().bisimilarity();
    let size = op.substrate().universe_len() as usize;
    let mut first_seen = vec![usize::MAX; size];
    let mut sequence: Vec<ElementId> = Vec::new();
    let mut current = x;
    loop {
        let class = representative[current.index()];
        if first_seen[class.index()] != usize::MAX {
            let start = first_seen[class.index()];
            return Some((sequence[..start].to_vec(), sequence[start..].to_vec()));
        }
        first_seen[class.index()] = sequence.len();
        sequence.push(class);
        current = op.project(current);
    }
}

/// **L6.1.D1 (`OT`)** — the orbit trace `OT(x)`. `None` on ↓_M.
pub fn orbit_trace(op: &ProjectionOperator, x: ElementId) -> Option<OrbitTrace> {
    quotient_orbit(op, x).map(|(transient, cycle)| OrbitTrace { transient, cycle })
}

/// **L6.1.T2 (`AOI3-Ext`)** — `AOI₁(x) = [OT(x)]_tail`: the tail-equivalence class of the
/// orbit trace, as the cycle in **canonical rotation** (rotated to begin at its
/// least-indexed ≈-class). Two persistent elements have equal `AOI₁` iff their orbits are
/// tail-equivalent (same cyclic sequence of ω-limit classes). `None` on ↓_M.
pub fn aoi1(op: &ProjectionOperator, x: ElementId) -> Option<Vec<ElementId>> {
    let (_, cycle) = quotient_orbit(op, x)?;
    // canonical rotation: start at the position of the least-indexed class.
    let pivot = (0..cycle.len()).min_by_key(|&i| cycle[i].0).unwrap_or(0);
    let mut rotated = Vec::with_capacity(cycle.len());
    rotated.extend_from_slice(&cycle[pivot..]);
    rotated.extend_from_slice(&cycle[..pivot]);
    Some(rotated)
}

/// **L6.1.D2 (`OS`)** — the orbit spectrum `OS_M(x)`: the asymptotic visit-frequency over
/// ≈-classes, as `(class, occurrences-per-period)` ascending by class, with the period
/// `CPD(x) = Σ occurrences` (frequency of a class = occurrences / period). `None` on ↓_M.
pub fn orbit_spectrum(op: &ProjectionOperator, x: ElementId) -> Option<Vec<(ElementId, u32)>> {
    let (_, cycle) = quotient_orbit(op, x)?;
    let mut spectrum: Vec<(ElementId, u32)> = Vec::new();
    for &class in &cycle {
        match spectrum.iter_mut().find(|(c, _)| *c == class) {
            Some((_, count)) => *count += 1,
            None => spectrum.push((class, 1)),
        }
    }
    spectrum.sort_by_key(|(c, _)| c.0);
    Some(spectrum)
}

/// **L6.1.D3 (`OC`)** — the orbit complexity (Borel rank of `{OT(x)}`). On a finite
/// substrate every orbit is periodic, so `OC = 0` (the trace is a Σ⁰₁ set, minimal rank);
/// `None` on ↓_M. (The aperiodic `OC > 0` case requires an infinite substrate.)
pub fn orbit_complexity(op: &ProjectionOperator, x: ElementId) -> Option<u32> {
    if is_persistent(op, x) {
        Some(0)
    } else {
        None
    }
}

/// Witness **L6.1.T1 (`AOI1-BisInv`)** — the orbit trace is bisimulation-invariant:
/// `x ≈ y ⟹ OT(x) = OT(y)`. Returns the first violating bisimilar pair, or `Ok`.
pub fn certify_orbit_trace_bisim_invariant(
    op: &ProjectionOperator,
) -> Result<(), (ElementId, ElementId)> {
    let representative = op.substrate().bisimilarity();
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            if representative[x.index()] == representative[y.index()]
                && orbit_trace(op, x) != orbit_trace(op, y)
            {
                return Err((x, y));
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
    fn type_p_trace_is_eventually_constant() {
        // 0⇄1 default obs: one ≈-class ⇒ OT eventually constant, cycle length 1.
        let e = [(0, 1), (1, 0)];
        let m = Model::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        let trace = orbit_trace(&op, id(0)).unwrap();
        assert!(trace.transient.is_empty());
        assert_eq!(trace.cycle.len(), 1); // CNF∞ — single stable class
        assert_eq!(orbit_complexity(&op, id(0)), Some(0));
        assert!(matches!(certify_orbit_trace_bisim_invariant(&op), Ok(())));
    }

    #[test]
    fn type_ep_trace_cycles_two_classes() {
        // 0→1→0 with distinct obs: two ≈-classes ⇒ cycle length 2 (Type EP).
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Model::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        let trace = orbit_trace(&op, id(0)).unwrap();
        assert_eq!(trace.cycle.len(), 2);
        // AOI₁ is the canonical rotation (starts at the least-indexed class 0).
        assert_eq!(aoi1(&op, id(0)), Some(vec![id(0), id(1)]));
        assert_eq!(aoi1(&op, id(1)), Some(vec![id(0), id(1)])); // tail-equivalent
        // spectrum: each class once per period (uniform over the cycle), period 2.
        assert_eq!(orbit_spectrum(&op, id(0)), Some(vec![(id(0), 1), (id(1), 1)]));
        assert!(matches!(certify_orbit_trace_bisim_invariant(&op), Ok(())));
    }

    #[test]
    fn convergent_elements_have_no_aoi() {
        let m = Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap())
            .unwrap();
        let op = m.operator();
        assert_eq!(orbit_trace(&op, id(1)), None);
        assert_eq!(aoi1(&op, id(0)), None);
        assert_eq!(orbit_complexity(&op, id(0)), None);
    }
}
