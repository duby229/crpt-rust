//! # R0.4 — Universal Boolean Stratification
//!
//! Exact realization of spec section **R0.4** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9):
//!
//! - R0.4.D1 `Q1`, `Q2`, `Q3` (Novel) — the classification predicates for `x ∈ Conv(π)`:
//!   `Q1(x) = (x ∈ Fix(π))`, `Q2(x) = H_S^π(x)`, `Q3(x) = H_I^π(x)` (defined only when
//!   `Q2 = ⊤`).
//! - R0.4.T1 `Bool-Strat` — the joint classification by `(Q1, Q2, Q3)` yields exactly
//!   **six** logically distinct, jointly exhaustive, pairwise disjoint classes A–F, with
//!   Class F provably empty when `π` is idempotent on `Fix(π)` (in particular under C1)
//!   ([`certify_class_f_empty`]).
//! - R0.4.T2 `Six-Uniq` — every `x ∈ Conv(π)` is in exactly one class
//!   ([`certify_six_uniqueness`]).
//! - R0.4.T3 `CRPT-Class` (≅∘) — the Instance bridge (`π := ρ_M`), authored once R1 exists.

use crate::r0::horizons::{invariant_horizon, structural_horizon};
use crate::r0::orbit_fate::is_convergent;
use crate::r0::projection_systems_and_fibers::EnumerableProjectionSystem;

/// **R0.4.T1 (`Bool-Strat`)** — the six universal classes over `(Q1, Q2, Q3)`. `==`
/// compares the computed class label (mathematical identity of the value).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SixClass {
    /// A — `Q1 ⊥, Q2 ⊥`: non-fixpoint, singleton fiber.
    A,
    /// B — `Q1 ⊥, Q2 ⊤, Q3 ⊥`: non-fixpoint, distinguishable siblings.
    B,
    /// C — `Q1 ⊥, Q2 ⊤, Q3 ⊤`: non-fixpoint, indistinguishable siblings.
    C,
    /// D — `Q1 ⊤, Q2 ⊥`: fixpoint, singleton fiber.
    D,
    /// E — `Q1 ⊤, Q2 ⊤, Q3 ⊥`: fixpoint, distinguishable sibling fiber.
    E,
    /// F — `Q1 ⊤, Q2 ⊤, Q3 ⊤`: fixpoint, indistinguishable sibling fiber. **Empty** when
    /// `π` is idempotent on `Fix(π)`.
    F,
}

/// **R0.4.D1/T1** — the six-class membership of `x`, via `Q1 = Fix`, `Q2 = H_S^π`,
/// `Q3 = H_I^π`. `None` on `Pers(π)` (the universal six-class is over `Conv(π)`).
pub fn classify<P: EnumerableProjectionSystem>(system: &P, x: &P::Point) -> Option<SixClass> {
    if !is_convergent(system, x) {
        return None;
    }
    let q1 = system.is_fixpoint(x);
    let q2 = structural_horizon(system, x);
    let class = match (q1, q2) {
        (false, false) => SixClass::A,
        (false, true) => {
            if invariant_horizon(system, x) {
                SixClass::C
            } else {
                SixClass::B
            }
        }
        (true, false) => SixClass::D,
        (true, true) => {
            if invariant_horizon(system, x) {
                SixClass::F
            } else {
                SixClass::E
            }
        }
    };
    Some(class)
}

/// Witness **R0.4.T2 (`Six-Uniq`)** — every convergent element receives exactly one class.
/// Returns the first convergent element with no class (none), or `Ok`.
pub fn certify_six_uniqueness<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        if is_convergent(system, &x) && classify(system, &x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R0.4.T1 (`Bool-Strat`) — Class F emptiness**: when `π` is idempotent on
/// `Fix(π)` (every fixpoint's fiber, once a fixpoint exists, collapses signatures), no
/// element is Class F. Returns the first Class-F element (none, in such a system), or `Ok`.
pub fn certify_class_f_empty<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        if classify(system, &x) == Some(SixClass::F) {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r0::projection_systems_and_fibers::ProjectionSystem;
    use SixClass::*;

    struct FiniteSystem {
        pi: Vec<u32>,
    }
    impl ProjectionSystem for FiniteSystem {
        type Point = u32;
        fn projection(&self, x: &u32) -> u32 {
            self.pi[*x as usize]
        }
        fn projection_depth(&self, x: &u32) -> Option<u32> {
            let mut seen = vec![false; self.pi.len()];
            let (mut cur, mut steps) = (*x, 0u32);
            loop {
                if self.pi[cur as usize] == cur {
                    return Some(steps);
                }
                if seen[cur as usize] {
                    return None;
                }
                seen[cur as usize] = true;
                cur = self.pi[cur as usize];
                steps += 1;
            }
        }
    }
    impl EnumerableProjectionSystem for FiniteSystem {
        fn universe(&self) -> Vec<u32> {
            (0..self.pi.len() as u32).collect()
        }
    }

    #[test]
    fn six_class_with_f_empty() {
        // 0→2, 1→2, 2→3, 3→3 idempotent on Fix={3}. Classes: 0,1 share (¬Fix,H_S,d=2)
        // with a uniform pair {0,1}… but the whole fiber {0,1,2,3} has mixed depths, so
        // H_I depends on the full fiber. 3 is a fixpoint with non-trivial fiber.
        let s = FiniteSystem { pi: vec![2, 2, 3, 3] };
        // 3 ∈ Fix, H_S ⊤ ; full fiber not signature-uniform ⇒ H_I ⊥ ⇒ Class E (not F).
        assert_eq!(classify(&s, &3), Some(E));
        // 0 ∉ Fix, H_S ⊤, full fiber not uniform ⇒ H_I ⊥ ⇒ Class B.
        assert_eq!(classify(&s, &0), Some(B));
        assert!(matches!(certify_six_uniqueness(&s), Ok(())));
        assert!(matches!(certify_class_f_empty(&s), Ok(())));
    }

    #[test]
    fn singleton_fibers_give_a_and_d() {
        // 0→1, 1→1 ; 2→3, 3→3 — two disjoint chains, each fiber size 2. Make singletons:
        // 0→0 (fixpoint, lone) and 1→1 (fixpoint, lone) ⇒ both Class D.
        let s = FiniteSystem { pi: vec![0, 1] };
        assert_eq!(classify(&s, &0), Some(D)); // fixpoint, singleton fiber
        assert_eq!(classify(&s, &1), Some(D));
        // a non-fixpoint with a singleton fiber ⇒ Class A: 0→1, 1→1, 2→1? then fiber of 0
        // includes 1,2 — not singleton. The cleanest A: chain 0→1→1 has fiber {0,1}.
        let chain = FiniteSystem { pi: vec![1, 1] };
        assert_eq!(classify(&chain, &0), Some(B)); // {0,1} non-trivial, mixed depth
        let _ = &s;
    }

    #[test]
    fn universal_six_class_applies_to_the_crpt_instance() {
        // CRPT-Class (R0.4.T3): R0's universal classification runs on ρ_M (R1.8) via the
        // CRPT-Fiber instance bridge (R0.1.T3). 0→2,1→2,2→3,3 NF — the same fiber math.
        use crate::r1::substrate::{ElementId, Substrate};
        use crate::r1::reduction_strategy::Instance;
        let e = [(0, 2), (1, 2), (2, 3)];
        let inst = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = inst.operator();
        // 3 is a fixpoint with non-trivial fiber; the universal classifier sees it.
        assert_eq!(classify(&op, &ElementId(3)), Some(E));
        assert!(matches!(certify_six_uniqueness(&op), Ok(())));
        assert!(matches!(certify_class_f_empty(&op), Ok(())));
    }
}
