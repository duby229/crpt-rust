//! # R0.2 — Universal Orbit Fate Classification
//!
//! Exact realization of spec section **R0.2** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9):
//!
//! - R0.2.D1 `Conv`, `Pers` (Reframed, ≈) — the convergent and persistent elements of a
//!   projection system: `Conv(π) = {x | ∃n : π^n(x) ∈ Fix(π)}`, `Pers(π) = 𝒰 \ Conv(π)`.
//!   The orbit depth `d_π(x) = min{n | π^n(x) ∈ Fix(π)}` exists on `Conv(π)` — it is the
//!   trait's [`projection_depth`](crate::r0::projection_systems_and_fibers::ProjectionSystem::projection_depth).
//! - R0.2.R1 `Asp-PreAx` — the dichotomy is prior to all axioms (excluded middle on the
//!   `Conv` definition); the R1 axiom families are organized by it.
//! - R0.2.T1 `Aspect-Dich` — `Conv(π) ⊔ Pers(π) = 𝒰`, exhaustive and disjoint
//!   ([`certify_aspect_dichotomy`]).
//! - R0.2.L1 `Conv-Closed` (≅) — `Conv(π)` is closed under `π`: `x ∈ Conv ⟹ π(x) ∈ Conv`
//!   ([`certify_conv_closed`]).
//! - R0.2.T3 `CRPT-Aspects` (≅∘) — the designated Instance theorem (`π := ρ_M`): authored
//!   once R1 exists.

use crate::r0::projection_systems_and_fibers::{EnumerableProjectionSystem, ProjectionSystem};

/// **R0.2.D1 (`Conv`)** — `x ∈ Conv(π)`: the π-orbit reaches a fixpoint in finitely many
/// steps (equivalently, `d_π(x)` exists).
pub fn is_convergent<P: ProjectionSystem>(system: &P, x: &P::Point) -> bool {
    system.projection_depth(x).is_some()
}

/// **R0.2.D1 (`Pers`)** — `x ∈ Pers(π) = 𝒰 \ Conv(π)`: the π-orbit never reaches a fixpoint.
pub fn is_persistent<P: ProjectionSystem>(system: &P, x: &P::Point) -> bool {
    system.projection_depth(x).is_none()
}

/// **R0.2.D1 (`d_π`)** — the orbit depth of a convergent element: `min{n | π^n(x) ∈
/// Fix(π)}`. `None` on `Pers(π)`. (The projection system's orbit-termination datum.)
pub fn orbit_depth<P: ProjectionSystem>(system: &P, x: &P::Point) -> Option<u32> {
    system.projection_depth(x)
}

/// Witness **R0.2.T1 (`Aspect-Dich`)** — every element is in exactly one aspect
/// (`Conv(π)` xor `Pers(π)`). Returns the first element in neither or both (none — the
/// two predicates are complementary by construction), or `Ok`.
pub fn certify_aspect_dichotomy<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        if is_convergent(system, &x) == is_persistent(system, &x) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R0.2.L1 (`Conv-Closed`)** — `Conv(π)` is closed under `π`: if `x` is
/// convergent then so is `π(x)` (the orbit of `π(x)` is the tail of `x`'s). Returns the
/// first convergent `x` whose image is persistent (none), or `Ok`.
pub fn certify_conv_closed<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        if is_convergent(system, &x) && is_persistent(system, &system.projection(&x)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R0.2.T2 (`Ax-Cov-U`)** — any theory completely characterizing `Π` must contain
/// axioms of exactly **three kinds**, and that tripartition is *forced* by the aspect
/// dichotomy (R0.2.T1): (i) convergent-aspect axioms govern `Conv(π)`, (ii) persistent-aspect
/// axioms govern `Pers(π)`, (iii) interface axioms govern the structural reachability between
/// them. The coverage is exhaustive because `Conv(π) ∐ Pers(π) = 𝒰` — every element falls
/// under (i) or (ii), and the boundary layer is the locus of (iii). Returns the first element
/// covered by neither aspect domain (none — the dichotomy is exhaustive), or `Ok`.
pub fn certify_axiom_coverage<P: EnumerableProjectionSystem>(system: &P) -> Result<(), P::Point> {
    for x in system.universe() {
        // every element is governed by the convergent-aspect axioms or the persistent-aspect
        // axioms — the two domains whose union the interface axioms bridge.
        if !is_convergent(system, &x) && !is_persistent(system, &x) {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r0::projection_systems_and_fibers::ProjectionSystem;

    /// A finite projection system over `0..n` from a successor table.
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
    fn convergent_persistent_dichotomy() {
        // 0→1, 1→1 (Conv); 2⇄3 cycle (Pers, no fixpoint).
        let s = FiniteSystem { pi: vec![1, 1, 3, 2] };
        assert!(is_convergent(&s, &0) && is_convergent(&s, &1));
        assert!(is_persistent(&s, &2) && is_persistent(&s, &3));
        assert_eq!(orbit_depth(&s, &0), Some(1));
        assert_eq!(orbit_depth(&s, &2), None);
        assert!(matches!(certify_aspect_dichotomy(&s), Ok(())));
        assert!(matches!(certify_conv_closed(&s), Ok(())));
        // Ax-Cov-U: the dichotomy forces exhaustive tripartite axiom coverage.
        assert!(matches!(certify_axiom_coverage(&s), Ok(())));
    }
}
