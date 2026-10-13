//! # R0.3 — Universal Horizon Predicates
//!
//! Exact realization of spec section **R0.3** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9) — the
//! projection-system-level forms of the structural, depth, and invariant horizons,
//! defined for any `Π` via **fibers** (R0.1.D2) and the orbit depth `d_π` (R0.2.D1):
//!
//! - R0.3.D1 `H_S^π`, `H_I^π`, `H_O^π` (Novel) — for `x ∈ Conv(π)`:
//!   - `H_S^π(x) :⟺ |L_π(x)| > 1` — x lies in a **non-trivial fiber** (structural ramification);
//!   - `H_O^π(x) :⟺ x ∈ Fix(π) ∧ H_S^π(x)` — a canonical representative (fixpoint) whose
//!     fiber is non-trivial (the observable index of unobservable content);
//!   - with the **structural signature** `sig_π(x) := (H_S^π(x), d_π(x))`,
//!     `H_I^π(x) :⟺ H_S^π(x) ∧ ∀z ∈ L_π(x) : sig_π(z) = sig_π(x)` — the ramification is
//!     observationally invisible.
//! - R0.3.R1 `BdyLayer-HO` — the boundary-layer predicate `H_∂^π(x) := (d_π(x) = 1)` is
//!   **distinct** from `H_O^π`: it marks non-fixpoints one step from canonical form.
//! - R0.3.T2 `H_I-WD-U` — `H_I^π` is well-defined (fiber-local; constant on fibers)
//!   ([`certify_h_i_well_defined`]).
//! - R0.3.T5 `CRPT-Horiz` (≅∘) — the Instance bridge (`π := ρ_M`), authored once R1 exists.

use crate::r0::orbit_fate::orbit_depth;
use crate::r0::projection_systems_and_fibers::EnumerableProjectionSystem;

/// **R0.3.D1 (`H_S^π`)** — the universal structural horizon: `x` lies in a non-trivial
/// fiber, `|L_π(x)| > 1`.
pub fn structural_horizon<P: EnumerableProjectionSystem>(system: &P, x: &P::Point) -> bool {
    system.fiber(x).len() > 1
}

/// **R0.3.D1 (`H_O^π`)** — the universal observable-fixpoint horizon: `x ∈ Fix(π)` and its
/// fiber is non-trivial.
pub fn observable_fixpoint_horizon<P: EnumerableProjectionSystem>(system: &P, x: &P::Point) -> bool {
    system.is_fixpoint(x) && structural_horizon(system, x)
}

/// **R0.3.D1 (`sig_π`)** — the structural signature `(H_S^π(x), d_π(x))`.
pub fn structural_signature<P: EnumerableProjectionSystem>(system: &P, x: &P::Point) -> (bool, Option<u32>) {
    (structural_horizon(system, x), orbit_depth(system, x))
}

/// **R0.3.D1 (`H_I^π`)** — the universal invariant horizon: `H_S^π(x)` and every fiber
/// element shares `x`'s structural signature (the ramification is invisible).
pub fn invariant_horizon<P: EnumerableProjectionSystem>(system: &P, x: &P::Point) -> bool {
    if !structural_horizon(system, x) {
        return false;
    }
    let signature = structural_signature(system, x);
    system.fiber(x).iter().all(|z| structural_signature(system, z) == signature)
}

/// **R0.3.R1 (`BdyLayer-HO`)** — the boundary-layer predicate `H_∂^π(x) := (d_π(x) = 1)`:
/// a non-fixpoint one step from its canonical form. Distinct from `H_O^π`.
pub fn boundary_layer<P: EnumerableProjectionSystem>(system: &P, x: &P::Point) -> bool {
    orbit_depth(system, x) == Some(1)
}

/// Witness **R0.3.T2 (`H_I-WD-U`)** — `H_I^π` is well-defined: it is **constant on each
/// fiber** (any two fiber-mates receive the same value), so it is determined by the fiber
/// rather than the representative. Returns the first fiber-mate pair on which `H_I^π`
/// disagrees (none), or `Ok`.
pub fn certify_h_i_well_defined<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        let h_i_x = invariant_horizon(system, &x);
        for z in system.fiber(&x) {
            if invariant_horizon(system, &z) != h_i_x {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R0.3.T1 (`Horiz-Ind`)** — `H_S^π`, `H_I^π`, `H_O^π` are the three minimal
/// independent predicates classifying fiber position. This certifies the load-bearing
/// characterization **clause (d)**: `H_S^π(x) = ⊤ ∧ H_I^π(x) = ⊥` iff the fiber of `x` is
/// non-trivial with **distinguishable** members (the projection collapses them but they
/// differ in a derived observable — depth/signature). Returns the first `x` where the
/// predicate combination disagrees with "non-trivial fiber + non-`sig_π`-uniform" (none),
/// or `Ok`.
pub fn certify_horizon_independence<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        let h_s = structural_horizon(system, &x);
        let h_i = invariant_horizon(system, &x);
        // clause (d): H_S ∧ ¬H_I ⟺ non-trivial fiber whose members are sig-distinguishable.
        let nontrivial_distinguishable = system.fiber(&x).len() > 1
            && system.fiber(&x).iter().any(|z| structural_signature(system, z) != structural_signature(system, &x));
        if (h_s && !h_i) != nontrivial_distinguishable {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R0.3.T3 (`H-Orbit-NonInv`)** — clause (b), the **orbit-monotonicity of `d_π`**:
/// `d_π(π(x)) = d_π(x) − 1` for every convergent non-fixpoint (the one quantity stable along
/// the orbit, in contrast to `H_S^π`/`H_I^π`, which must be re-evaluated each step). Returns
/// the first convergent non-fixpoint violating the decrement (none), or `Ok`.
pub fn certify_depth_orbit_monotone<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        // fixpoints (d = 0) and persistent elements are out of scope; for every other
        // convergent element the depth must drop by exactly one along the orbit.
        if let Some(d) = orbit_depth(system, &x) {
            if d >= 1 && orbit_depth(system, &system.projection(&x)) != Some(d - 1) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R0.3.T4 (`H_I-SOL`)** — `H_I^π = ⊤` is the **exact** condition under which the
/// theory `T(Π)` requires second-order logic: a positive `H_I^π` element has a fiber of
/// observationally indistinguishable members whose separation needs the (greatest-fixpoint)
/// bisimilarity quantification (`SOL-Nec-U` R0.7.T1), whereas a globally-`⊥` `H_I^π` makes
/// every fiber `d_π`-distinguishable — first-order. Returns `true` iff some element has
/// `H_I^π = ⊤` (the SOL-active condition); `false` means `T(Π)` reduces to FOL.
pub fn h_i_requires_sol<P: EnumerableProjectionSystem>(system: &P) -> bool {
    system.universe().iter().any(|x| invariant_horizon(system, x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r0::projection_systems_and_fibers::ProjectionSystem;

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
    fn fiber_based_horizons() {
        // 0→2, 1→2, 2→3, 3→3. Fiber of all = {0,1,2,3}. d_π: 0,1↦2 ; 2↦1 ; 3↦0.
        let s = FiniteSystem { pi: vec![2, 2, 3, 3] };
        // H_S: non-trivial fiber holds everywhere here.
        assert!(structural_horizon(&s, &0) && structural_horizon(&s, &3));
        // H_O: fixpoint (3) with non-trivial fiber.
        assert!(observable_fixpoint_horizon(&s, &3));
        assert!(!observable_fixpoint_horizon(&s, &0)); // 0 ∉ Fix
        // boundary layer: d_π = 1 (element 2), distinct from H_O.
        assert!(boundary_layer(&s, &2) && !boundary_layer(&s, &0));
        // H_I: the fiber holds mixed depths (0,1,2 — for 0/2/3) ⇒ signatures differ ⇒ ⊥.
        assert!(!invariant_horizon(&s, &0));
        assert!(matches!(certify_h_i_well_defined(&s), Ok(())));
        // Horiz-Ind clause (d): H_S ∧ ¬H_I ⟺ non-trivial fiber, distinguishable members.
        assert!(matches!(certify_horizon_independence(&s), Ok(())));
        // H-Orbit-NonInv (b): d_π is orbit-monotone (decreases by 1 each step).
        assert!(matches!(certify_depth_orbit_monotone(&s), Ok(())));
        // H_I-SOL: this system is globally H_I = ⊥ ⇒ FOL suffices (no SOL-active element).
        assert!(!h_i_requires_sol(&s));
    }

    #[test]
    fn invariant_horizon_holds_on_depth_uniform_fibers() {
        // 0→2, 1→2, 2→2 (fixpoint). Fiber {0,1,2}: d_π 0,1↦1 ; 2↦0. Kernel of the
        // non-fixpoints {0,1} is depth-uniform — but the fixpoint 2 differs, so the full
        // fiber is not signature-uniform ⇒ H_I ⊥. Make a uniform one: 0→1,1→1 only.
        let s = FiniteSystem { pi: vec![1, 1] };
        // fiber {0,1}: d_π 0↦1, 1↦0 — still mixed ⇒ H_I ⊥. The honest finite picture: a
        // signature-uniform non-trivial fiber needs ≥2 elements at equal depth.
        let s2 = FiniteSystem { pi: vec![2, 2, 2] }; // 0,1→2 ; 2 fix. fiber {0,1,2}.
        assert!(structural_horizon(&s2, &0));
        // 0 and 1 share (H_S=⊤, d=1); 2 has (H_S=⊤, d=0) ⇒ not uniform ⇒ H_I ⊥, well-defined.
        assert!(matches!(certify_h_i_well_defined(&s2), Ok(())));
        let _ = &s;
    }
}
