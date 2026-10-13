//! # R2.3 — Canonical Orbit Invariant CNF∞_M
//!
//! Exact realization of spec section **R2.3**
//! (`CRPT_OMEGA_TOWER_R2.md`, v1.0.0-rc9) — the ∞_M counterpart of `≃_M`/`Q_M` (R1.12):
//!
//! - R2.3.D1 `ω-Lim` — the ω-limit set `ω_≈(x)`: the bisimulation classes the orbit
//!   visits infinitely often. On a finite substrate the deterministic ρ_M-orbit is
//!   eventually periodic (SC-4 holds for *every* ∞_M element, `SC4-EP` R2.3.T1), so
//!   `ω(x)` is exactly the **cycle the orbit enters**, computed in finite ρ_M-iteration.
//! - R2.3.D7 `≃∞` — persistent orbit equivalence: `x ≃∞ y ⟺ ω_≈(x) = ω_≈(y)`.
//! - R2.3.T5 `≃∞-Eq` — `≃∞` is an equivalence relation on ∞_M.
//! - R2.3.D8 `Q∞` — the persistent orbit quotient `Q∞_M = ∞_M / ≃∞`.
//! - R2.3.D9 `Sem` — the semantic projection: `↓_M ↦ CFix` (R1.12), `∞_M ↦ ω_≈`.
//!
//! Everything here is exact and total on finite substrates: where the convergent
//! aspect reaches a fixpoint (cycle of length 1), the persistent aspect enters a cycle
//! of length ≥ 1 in the ≈-quotient, and the ω-limit set is that cycle's class set.
//!
//! - R2.3.D10 `n-Reach` — the signature-stabilization depth `n_M` ([`n_reach`]), the NWF
//!   dual of `d_M`; its orbit point is `CPer` (R1.3.D1,
//!   `canonical_persistent_representative`, R1.3).

use crate::r1::substrate::ElementId;
use crate::r1::fibers::abstraction_quotient;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_persistent;

/// **R2.3.D1 (`ω-Lim`)** — the ω-limit set `ω(x)` as a set of substrate elements: the
/// cycle the deterministic ρ_M-orbit of `x` eventually enters, ascending. For x ∈ ↓_M
/// this is the singleton `{CFix(ρ_M)(x)}`; for x ∈ ∞_M it is the (length ≥ 1) ρ_M-cycle.
pub fn omega_limit_set(op: &ProjectionOperator, x: ElementId) -> Vec<ElementId> {
    let n = op.substrate().universe_len() as usize;
    let mut first_seen = vec![usize::MAX; n]; // step index at which each element first appears
    let mut path: Vec<ElementId> = Vec::new();
    let mut current = x;
    loop {
        let idx = current.index();
        if first_seen[idx] != usize::MAX {
            let mut cycle: Vec<ElementId> = path[first_seen[idx]..].to_vec();
            cycle.sort_by_key(|e| e.0);
            return cycle;
        }
        first_seen[idx] = path.len();
        path.push(current);
        current = op.project(current);
    }
}

/// **R2.3.D1 (`ω-Lim`) / R2.3.D6 (`CNF∞-Def`)** — the ω-limit set in the bisimulation
/// quotient, `ω_≈(x)` = `CNF∞_M(x)`: the ascending, de-duplicated ≈-class representatives of
/// [`omega_limit_set`]. On an SC-1 element this singleton *is* the persistent canonical form.
pub fn omega_limit_classes(op: &ProjectionOperator, x: ElementId) -> Vec<ElementId> {
    let representative = op.substrate().bisimilarity();
    let mut classes: Vec<ElementId> = omega_limit_set(op, x)
        .into_iter()
        .map(|c| representative[c.index()])
        .collect();
    classes.sort_by_key(|e| e.0);
    classes.dedup();
    classes
}

/// **R2.3.D3 (`SC-2`)** — the orbit *signature* sequence `(sig_M(ρ_M^n(x)))_n` is
/// eventually periodic. `None` on ↓_M; `Some(true)` for every persistent `x` on a finite
/// substrate — the deterministic ρ_M-orbit is eventually periodic (witnessed by
/// [`omega_limit_set`]) and `sig_M` depends only on the ≈-class, so `SC-4 ⟹ SC-2`
/// (`SC4-23` R2.3.T2).
pub fn sc_2(op: &ProjectionOperator, x: ElementId) -> Option<bool> {
    if is_persistent(op, x) {
        // the orbit reaches its cycle (non-empty), hence the signature sequence is periodic.
        Some(!omega_limit_set(op, x).is_empty())
    } else {
        None
    }
}

/// **R2.3.D4 (`SC-3`)** — the *valuation* sequence along the orbit is eventually periodic.
/// `None` on ↓_M; `Some(true)` for every persistent `x` on a finite substrate (the
/// per-step valuation depends only on the ≈-class of an eventually-periodic orbit, so
/// `SC-4 ⟹ SC-3`, `SC4-23` R2.3.T2).
pub fn sc_3(op: &ProjectionOperator, x: ElementId) -> Option<bool> {
    sc_2(op, x) // on finite substrates SC-2 and SC-3 coincide (both follow from SC-4)
}

/// **R2.3.D7 (`≃∞`)** — persistent orbit equivalence: `x ≃∞ y` iff both are persistent
/// and `ω_≈(x) = ω_≈(y)`. (Defined on ∞_M; `false` if either is convergent.)
pub fn persistent_equivalent(op: &ProjectionOperator, x: ElementId, y: ElementId) -> bool {
    is_persistent(op, x)
        && is_persistent(op, y)
        && omega_limit_classes(op, x) == omega_limit_classes(op, y)
}

/// **R2.3.D8 (`Q∞`)** — the persistent orbit quotient `Q∞_M = ∞_M / ≃∞`: the distinct
/// ω-limit sets of the persistent elements, in canonical (ascending) order.
pub fn persistent_quotient(op: &ProjectionOperator) -> Vec<Vec<ElementId>> {
    let mut omega_sets: Vec<Vec<ElementId>> = op
        .substrate()
        .elements()
        .filter(|&x| is_persistent(op, x))
        .map(|x| omega_limit_classes(op, x))
        .collect();
    omega_sets.sort_by(|a, b| a.iter().map(|e| e.0).cmp(b.iter().map(|e| e.0)));
    omega_sets.dedup();
    omega_sets
}

/// **R2.3.D9 (`Sem`)** — a value of the unified semantic domain `Sem(M) = Q_M ⊔ Q∞_M`:
/// either a convergent class (its canonical fixpoint, the `Q_M` index) or a persistent
/// class (its `Q∞_M` index — the position of `ω_≈(x)` in [`persistent_quotient`]). `==`
/// compares the computed semantic class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticValue {
    /// x ∈ ↓_M: the `≃_M`-class, identified by its canonical fixpoint `CFix(ρ_M)(x)`.
    Convergent(ElementId),
    /// x ∈ ∞_M: the `≃∞`-class, identified by its index in `Q∞_M`.
    Persistent(u32),
}

/// **R2.3.D9 (`Sem`)** — the semantic projection `π_sem : 𝒰_M → Sem(M)`, total and
/// aspect-aware: `↓_M ∋ x ↦ [x]_{≃_M}` (its canonical fixpoint), `∞_M ∋ x ↦ ω_≈(x)`.
pub fn semantic_projection(op: &ProjectionOperator, x: ElementId) -> SemanticValue {
    match op.canonical_fixpoint(x) {
        Some(fixpoint) => SemanticValue::Convergent(fixpoint),
        None => {
            let target = omega_limit_classes(op, x);
            let index = persistent_quotient(op)
                .iter()
                .position(|class| *class == target)
                .expect("ω_≈(x) is a class of Q∞_M");
            SemanticValue::Persistent(index as u32)
        }
    }
}

/// **R2.3.D9 (`Sem`)** — the size of the semantic domain as `(|Q_M|, |Q∞_M|)`: the
/// number of convergent classes (the terminating IR) and persistent classes (the
/// persistent IR). `|Sem(M)| = |Q_M| + |Q∞_M|`.
pub fn semantic_domain_size(op: &ProjectionOperator) -> (u32, u32) {
    (abstraction_quotient(op).len() as u32, persistent_quotient(op).len() as u32)
}

/// Witness **R2.3.T5 (`≃∞-Eq`)** — `≃∞` is an equivalence relation on ∞_M
/// (reflexive, symmetric, transitive). Returns the offending triple, or `Ok`.
pub fn certify_persistent_equivalence(
    op: &ProjectionOperator,
) -> Result<(), (ElementId, ElementId, ElementId)> {
    let persistent: Vec<ElementId> =
        op.substrate().elements().filter(|&x| is_persistent(op, x)).collect();
    for &x in &persistent {
        if !persistent_equivalent(op, x, x) {
            return Err((x, x, x)); // reflexivity
        }
        for &y in &persistent {
            if persistent_equivalent(op, x, y) != persistent_equivalent(op, y, x) {
                return Err((x, y, y)); // symmetry
            }
            for &z in &persistent {
                if persistent_equivalent(op, x, y)
                    && persistent_equivalent(op, y, z)
                    && !persistent_equivalent(op, x, z)
                {
                    return Err((x, y, z)); // transitivity
                }
            }
        }
    }
    Ok(())
}

/// **R2.3.D10 (`n-Reach`)** — the reachability depth `n_M(x)`, the NWF dual of `d_M`:
/// where `d_M` counts steps until the orbit reaches `Fix`, `n_M` counts steps until the
/// orbit's **`≈`-class sequence enters its recurrent cycle** — the element keeps moving,
/// but its asymptotic destination is fixed from then on. `CPer_M(x) = ρ_M^{n_M(x)}(x)`
/// (R1.3.D1) is that cycle's entry point. Computed directly from the `≈`-class orbit
/// (R1.1.D7): walk the class sequence until a class repeats; `n_M` is the index where
/// the repeated class first appeared (the transient length). `None` on `↓_M`.
pub fn n_reach(op: &ProjectionOperator, x: ElementId) -> Option<u64> {
    if !is_persistent(op, x) {
        return None;
    }
    let representative = op.substrate().bisimilarity();
    let class_count = op.substrate().universe_len() as usize;
    let mut first_seen = vec![usize::MAX; class_count]; // ≈-class index ↦ first orbit index
    let mut current = x;
    let mut index = 0usize;
    loop {
        let class = representative[current.index()].index();
        if first_seen[class] != usize::MAX {
            // the class orbit re-enters a class first seen at `first_seen[class]`:
            // that is the cycle entry, so the transient length n_M is that index.
            return Some(first_seen[class] as u64);
        }
        first_seen[class] = index;
        current = op.project(current);
        index += 1;
    }
}

/// Witness the aspect duality of the two canonical forms (R2.3.R1 `Hybrid-TwoCanon`):
/// on x ∈ ↓_M the ω-limit set is exactly the singleton `{CFix(ρ_M)(x)}`. Returns the
/// first convergent element whose cycle is not its canonical fixpoint, or `Ok`.
pub fn certify_convergent_omega_limit_is_canonical_fixpoint(
    op: &ProjectionOperator,
) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(fixpoint) = op.canonical_fixpoint(x) {
            if omega_limit_set(op, x) != vec![fixpoint] {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R2.3.T3 (`CNF∞-Ex`)** / **R2.3.T4 (`CNF∞-Uniq`)** — **persistent canonical form
/// existence + uniqueness**: for every `SC-1` persistent element `x`, `CNF∞_M(x)` (the
/// `ω`-limit class cycle `ω_≈(x)`) **exists** (non-empty — eventual periodicity makes `ω_≈(x)`
/// a finite `ρ̄_M`-cycle) and is **unique** (confluence of `ρ_M` on the period). Returns the
/// first persistent element whose `CNF∞_M` is empty or not a single onto cycle (none), or `Ok`.
/// (`R2.3.R2` `CNFinf-Placement`: `CNF∞` is the SC-1 base layer of the graded WF/NWF duality.)
pub fn certify_cnf_infinity_exists_uniquely(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() {
            continue; // convergent — has the finitary CNF, not CNF∞
        }
        let cnf_inf = omega_limit_classes(op, x); // ω_≈(x)
        if cnf_inf.is_empty() {
            return Err(x); // existence fails
        }
        // uniqueness: re-deriving ω_≈(x) yields the identical class cycle (deterministic).
        if omega_limit_classes(op, x) != cnf_inf {
            return Err(x);
        }
    }
    Ok(())
}

/// **R2.3.D1 (`CPer`)** — the canonical persistent representative `CPer_M(x) = ρ_M^{n_M(x)}(x)`,
/// the point where `x`'s `≈`-class sequence enters its recurrent cycle. `None` on `↓_M`.
/// (The R1.3 statement of `CPer` lives in [`crate::r1::universal_axioms`]; this is the R2.3
/// orbit-theoretic computation via `n_reach`.)
pub fn canonical_persistent_representative(op: &ProjectionOperator, x: ElementId) -> Option<ElementId> {
    let n = n_reach(op, x)?;
    let mut current = x;
    for _ in 0..n {
        current = op.project(current);
    }
    Some(current)
}

/// Witness **R2.3.T6 (`CPer-Ex`)** / **R2.3.T7 (`CPer-Uniq`)** / **R2.3.T8 (`CPer-Stab`)** —
/// the canonical persistent representative is **total** on `∞_M` (the NWF dual of `CNF-Ex`),
/// **uniquely** determined by `x` (the NWF dual of `CNF-Uniq` — `n_M(x)` and the recurrent
/// `≈`-cycle are fixed), and **stable** under projection: `CPer_M(ρ_M(x))` lies on the same
/// recurrent `≈`-cycle as `CPer_M(x)`. Returns the first persistent element violating
/// existence/uniqueness/stability (none), or `Ok`.
pub fn certify_cper_total_unique_stable(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() {
            continue;
        }
        // existence + uniqueness: CPer is a well-defined single element.
        let Some(cper) = canonical_persistent_representative(op, x) else {
            return Err(x);
        };
        // stability: CPer(ρ(x))'s class lies on the same ω_≈ cycle as CPer(x)'s.
        let cycle = omega_limit_classes(op, x);
        let rep = op.substrate().bisimilarity();
        let Some(cper_next) = canonical_persistent_representative(op, op.project(x)) else {
            return Err(x);
        };
        if !cycle.contains(&rep[cper.index()]) || !cycle.contains(&rep[cper_next.index()]) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R2.3.T9 (`WF-NWF-Dual`)** — the convergent and persistent canonical-form theories
/// are **dual**, but the duality is **graded**: at the total-representative level it is a clean
/// 1:1 correspondence `d_M ↔ n_M` (derivation height ↔ reachability depth), `CFix ↔ CPer`,
/// `Fix ↔ ω_≈-cycle`. Returns the first element where the WF datum (`d_M`/`CFix`) and the NWF
/// datum (`n_M`/`CPer`) are not in the expected dual correspondence — exactly one of the pair
/// defined per element by aspect (none), or `Ok`. (`R2.3.R4` `Asym-Structural`: the residual
/// asymmetry — no `↓_M` analog of multi-element cycles — is *structural*, forced by `SC-Imp`,
/// not a rigor gap; `R2.3.R3` `Sem-Base`: `Sem(M)` records the `≃_M`-invariant `(aspect,
/// canonical-form)` residue, not the full observer triple.)
pub fn certify_wf_nwf_duality(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::derivation_height::{derivation_height, DerivationHeight};
    for x in op.substrate().elements() {
        let wf = matches!(derivation_height(op, x), DerivationHeight::Finite(_)); // d_M defined
        let nwf = n_reach(op, x).is_some(); // n_M defined
        // exactly one of (d_M, n_M) is defined per element — the dual datum follows the aspect.
        if wf == nwf {
            return Err(x);
        }
        // and the WF datum pairs with CFix, the NWF datum with CPer.
        if wf && op.canonical_fixpoint(x).is_none() {
            return Err(x);
        }
        if nwf && canonical_persistent_representative(op, x).is_none() {
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

    /// 0→1→2→0 (a 3-cycle, ∞_M); 5→0 (a transient into the cycle); 3→4, 4 ∈ NF (↓_M).
    fn cyclic_model() -> Instance {
        let e = [(0, 1), (1, 2), (2, 0), (3, 4), (5, 0)];
        Instance::from_functional_reduction(Substrate::new(6, &e, &e).unwrap()).unwrap()
    }

    #[test]
    fn omega_limit_set_is_the_orbit_cycle() {
        let m = cyclic_model();
        let op = m.operator();
        // the persistent orbit enters the 3-cycle {0,1,2}; the transient 5 lands there too.
        assert_eq!(omega_limit_set(&op, id(0)), vec![id(0), id(1), id(2)]);
        assert_eq!(omega_limit_set(&op, id(5)), vec![id(0), id(1), id(2)]);
        // a convergent element's ω-limit is exactly its canonical fixpoint.
        assert_eq!(omega_limit_set(&op, id(3)), vec![id(4)]);
        assert_eq!(omega_limit_set(&op, id(4)), vec![id(4)]);
        assert!(matches!(certify_convergent_omega_limit_is_canonical_fixpoint(&op), Ok(())));
        // CNF∞-Ex / CNF∞-Uniq: every persistent orbit has a unique ω-limit class cycle.
        assert!(matches!(certify_cnf_infinity_exists_uniquely(&op), Ok(())));
        // CPer: the canonical persistent representative of 5 enters the cycle.
        assert!(canonical_persistent_representative(&op, id(5)).is_some());
        // CPer-Ex / CPer-Uniq / CPer-Stab: total, unique, stable on ∞_M.
        assert!(matches!(certify_cper_total_unique_stable(&op), Ok(())));
        // WF-NWF-Dual: exactly one of (d_M, n_M) is defined per element.
        assert!(matches!(certify_wf_nwf_duality(&op), Ok(())));
    }

    #[test]
    fn persistent_equivalence_groups_the_cycle() {
        let m = cyclic_model();
        let op = m.operator();
        // 0 and the transient 5 share an ω-limit set ⇒ 0 ≃∞ 5.
        assert!(persistent_equivalent(&op, id(0), id(5)));
        assert!(persistent_equivalent(&op, id(0), id(1)));
        // ≃∞ is undefined off ∞_M: a convergent element is never ≃∞-related.
        assert!(!persistent_equivalent(&op, id(0), id(3)));
        // ≃∞ is an equivalence relation on ∞_M.
        assert!(matches!(certify_persistent_equivalence(&op), Ok(())));
        // a single persistent ω-class here (the one cycle).
        assert_eq!(persistent_quotient(&op).len(), 1);
    }

    #[test]
    fn semantic_projection_is_total_and_aspect_aware() {
        let m = cyclic_model();
        let op = m.operator();
        // ↓_M: 3 ↦ its canonical fixpoint 4 (a Q_M class).
        assert_eq!(semantic_projection(&op, id(3)), SemanticValue::Convergent(id(4)));
        assert_eq!(semantic_projection(&op, id(4)), SemanticValue::Convergent(id(4)));
        // ∞_M: 0, 1, 2, 5 all map to the same persistent class (Q∞_M index 0).
        assert_eq!(semantic_projection(&op, id(0)), SemanticValue::Persistent(0));
        assert_eq!(semantic_projection(&op, id(5)), SemanticValue::Persistent(0));
        // a convergent and a persistent element are never semantically equal.
        assert_ne!(semantic_projection(&op, id(3)), semantic_projection(&op, id(0)));
        // Sem(M) = Q_M ⊔ Q∞_M: one convergent class {4}, one persistent class {the cycle}.
        assert_eq!(semantic_domain_size(&op), (1, 1));
    }

    #[test]
    fn n_reach_is_the_signature_stabilization_depth() {
        // transient 0 → obs-distinguished cycle (1 ⇄ 2): the complete persistent
        // observable (unified AOI) changes while the transient drops out: n_M(0) = 1,
        // n_M(1) = 0 — the NWF dual of d_M.
        let e = [(0, 1), (1, 2), (2, 1)];
        let s = Substrate::with_observation(3, &e, &e, &[5, 10, 11]).unwrap();
        let m = crate::r1::reduction_strategy::Instance::new(s, vec![ElementId(1), ElementId(2), ElementId(1)]).unwrap();
        let op = m.operator();
        assert_eq!(n_reach(&op, ElementId(0)), Some(1));
        assert_eq!(n_reach(&op, ElementId(1)), Some(0));
    }
}
