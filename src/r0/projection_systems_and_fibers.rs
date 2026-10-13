//! # R0.1 — Projection Systems and Fibers
//!
//! Exact realization of spec section **R0.1** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9):
//!
//! - R0.1.D1 `ProjSys` (Novel) — a projection system `Π = (𝒰, π, →_σ)`: a non-empty
//!   universe, a projection map `π : 𝒰 → 𝒰` (no properties assumed), and the structural
//!   relation `→_σ`. `Fix(π) = {x | π(x) = x}`; the canonical form
//!   `CNF_π(x) = lim_{n→∞} π^n(x)` exists when the orbit terminates in `Fix(π)`.
//! - R0.1.D2 `Fiber` (Reframed, ≈) — the fiber `L_π(x) = {z | CNF_π(z) = CNF_π(x)}` and
//!   the observable equivalence `x ≃_π y ⟺ CNF_π(x) = CNF_π(y)`. (Reframed from the
//!   preimage of a map: the fiber is read as an *indistinguishability* class.)
//! - R0.1.R1 `Fiber-InfoComp` (Novel) — the fiber measures information compression: the
//!   larger `L_π(x)`, the more `π` loses at `x`.
//! - R0.1.D3 `Obs_π` (Novel) — an invariant `I` is π-observable at `x` iff constant on
//!   `L_π(x)`.
//! - R0.1.T1 `Fiber-Compl` (Novel) — `|L_π(x)| = 1` iff every invariant is observable at
//!   `x`; `|L_π(x)| > 1` iff some invariant is unobservable at `x` ([`certify_fiber_completeness`]).
//! - R0.1.T2 `Reify-Mono` (Imported, ≅) — fibers are monotone under projection
//!   refinement: if `π₂` refines `π₁` then `L_{π₁}(x) ⊆ L_{π₂}(x)` ([`fibers_refine`]).
//! - R0.1.T3 `CRPT-Fiber` (Derived) — the designated **Instance** theorem (`π := ρ_M`):
//!   authored once R1 (`ρ_M` R1.8, `NFC-NM` R1.12) exists.
//!
//! This is the one operation of `Min-Interp` (R1.1.R5): recursive projection onto
//! discernible content. Every rank above is an instance or composite of it.

/// **R0.1.D1 (`ProjSys`)** — *the* projection system `Π = (𝒰, π, →_σ)`, generic over the
/// universe representation [`Point`](Self::Point). An implementor supplies the projection
/// map `π` and the orbit-termination datum [`projection_depth`](Self::projection_depth);
/// `Fix(π)`, the canonical form `CNF_π`, and the observable equivalence `≃_π` follow.
pub trait ProjectionSystem {
    /// An element of the (possibly infinite) universe `𝒰`. Equality is the universe's own
    /// mathematical identity `=` (never a derived structural ordering).
    type Point: Clone + PartialEq;

    /// **R0.1.D1**: `π(x)` — the projection map, one application.
    fn projection(&self, x: &Self::Point) -> Self::Point;

    /// **R0.1.D1**: the orbit-termination datum — the least `n` with `π^n(x) ∈ Fix(π)`, or
    /// `None` when the orbit never reaches a fixpoint. (Supplied by the instance; deciding
    /// it by blind iteration on an infinite `𝒰` is not assumed possible.) It is what makes
    /// `CNF_π` exist: `Some` exactly on the convergent elements `Conv(π)` (R0.2).
    fn projection_depth(&self, x: &Self::Point) -> Option<u32>;

    /// **R0.1.D1**: `x ∈ Fix(π)` (`π(x) = x`).
    fn is_fixpoint(&self, x: &Self::Point) -> bool {
        self.projection(x) == *x
    }

    /// **R0.1.D1**: `CNF_π(x) = lim_{n→∞} π^n(x)` — the canonical form, by applying `π`
    /// exactly `projection_depth(x)` times. `None` where the orbit does not terminate.
    fn canonical_form(&self, x: &Self::Point) -> Option<Self::Point> {
        let depth = self.projection_depth(x)?;
        let mut current = x.clone();
        for _ in 0..depth {
            current = self.projection(&current);
        }
        Some(current)
    }

    /// **R0.1.D2 (`≃_π`)**: `x ≃_π y ⟺ CNF_π(x) = CNF_π(y)` (both defined).
    fn observably_equivalent(&self, x: &Self::Point, y: &Self::Point) -> bool {
        match (self.canonical_form(x), self.canonical_form(y)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }
}

/// **R0.1.D1 on an enumerable universe** — the refinement where `𝒰` can be *listed*, so
/// the fiber `L_π(x)` and π-observability (`Obs_π`) materialize as finite computations.
/// This listing capability is the only thing the enumerable case adds; the operator and
/// `CNF_π` live on [`ProjectionSystem`].
pub trait EnumerableProjectionSystem: ProjectionSystem {
    /// `𝒰` as a list (the enumerable universe).
    fn universe(&self) -> Vec<Self::Point>;

    /// **R0.1.D2 (`Fiber`)**: `L_π(x) = {z | CNF_π(z) = CNF_π(x)}`. Empty when `CNF_π(x)`
    /// does not exist (the fiber is defined on `Conv(π)`).
    fn fiber(&self, x: &Self::Point) -> Vec<Self::Point> {
        match self.canonical_form(x) {
            None => Vec::new(),
            Some(target) => self
                .universe()
                .into_iter()
                .filter(|z| self.canonical_form(z) == Some(target.clone()))
                .collect(),
        }
    }

    /// **R0.1.D3 (`Obs_π`)**: an invariant `I` is π-observable at `x` — constant on
    /// `L_π(x)`: `∀z ∈ L_π(x) : I(z) = I(x)`.
    fn is_observable<S: PartialEq>(&self, invariant: impl Fn(&Self::Point) -> S, x: &Self::Point) -> bool {
        let value_at_x = invariant(x);
        self.fiber(x).iter().all(|z| invariant(z) == value_at_x)
    }
}

/// Witness **R0.1.T1 (`Fiber-Compl`)** (a)/(b): `|L_π(x)| = 1` iff every invariant is
/// π-observable at `x`, and `|L_π(x)| > 1` iff some invariant is unobservable at `x` —
/// witnessed by the identity invariant (the finest one), which is observable at `x`
/// exactly when the fiber is the singleton `{x}`. Returns the first element where the
/// fiber size and the identity-invariant observability disagree (none), or `Ok`.
pub fn certify_fiber_completeness<P>(system: &P) -> Result<(), P::Point>
where
    P: EnumerableProjectionSystem,
{
    for x in system.universe() {
        let trivial_fiber = system.fiber(&x).len() == 1;
        // the identity invariant I(z) = z is observable at x iff every fiber element is x.
        let identity_observable = system.is_observable(|z| z.clone(), &x);
        if trivial_fiber != identity_observable {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R0.1.T2 (`Reify-Mono`)** — fibers are monotone under projection refinement:
/// if `finer` refines `coarser` (every `coarser`-fiber is contained in a `finer`-fiber —
/// i.e. `z ≃_coarser x ⟹ z ≃_finer x`), then `L_coarser(x) ⊆ L_finer(x)` for every `x`.
/// Over a shared enumerable universe, returns the first `x` whose coarser-fiber is not
/// contained in its finer-fiber (none, when `finer` genuinely refines `coarser`), or `Ok`.
pub fn fibers_refine<C, F>(coarser: &C, finer: &F) -> Result<(), C::Point>
where
    C: EnumerableProjectionSystem,
    F: EnumerableProjectionSystem<Point = C::Point>,
{
    for x in coarser.universe() {
        let coarse_fiber = coarser.fiber(&x);
        let fine_fiber = finer.fiber(&x);
        if !coarse_fiber.iter().all(|z| fine_fiber.contains(z)) {
            return Err(x);
        }
    }
    Ok(())
}

/// **R0.1.T3 (`CRPT-Fiber`, Derived ≅∘) — the designated Instance bridge**: the CRPT
/// reduction strategy `ρ_M` (R1.8.D1) is a projection system with `π := ρ_M`. Implementing
/// the universal [`ProjectionSystem`] here makes every R0 universal construct (fibers,
/// `Conv`/`Pers`, the horizons R0.3, the six-class R0.4) apply to the CRPT instance — the
/// universal layer specializing to CRPT's own, exactly as the spec's `CRPT-*` Instance
/// theorems assert. `→_ρ ⊆ →_σ` (`Sub` R1.1.D1) and determinism (C1–C2) make this a valid
/// instance.
impl crate::r0::projection_systems_and_fibers::ProjectionSystem
    for crate::r1::reduction_strategy::ProjectionOperator<'_>
{
    type Point = crate::r1::substrate::ElementId;

    fn projection(&self, x: &Self::Point) -> Self::Point {
        self.project(*x) // π := ρ_M, one step
    }

    fn projection_depth(&self, x: &Self::Point) -> Option<u32> {
        // d_π(x) = min{n | ρ_M^n(x) ∈ Fix(ρ_M)}; None on the persistent aspect.
        let bound = self.substrate().universe_len();
        let mut current = *x;
        for steps in 0..=bound {
            if self.is_fixpoint(current) {
                return Some(steps);
            }
            current = self.project(current);
        }
        None
    }

    fn is_fixpoint(&self, x: &Self::Point) -> bool {
        crate::r1::reduction_strategy::ProjectionOperator::is_fixpoint(self, *x)
    }
}

/// **R0.1.T3 (`CRPT-Fiber`) — the enumerable instance**: the CRPT operator's universe is
/// the finite substrate `0..|𝒰_M|`, so the fiber/observability constructs of R0.1 are
/// finite computations on it.
impl crate::r0::projection_systems_and_fibers::EnumerableProjectionSystem
    for crate::r1::reduction_strategy::ProjectionOperator<'_>
{
    fn universe(&self) -> Vec<Self::Point> {
        self.substrate().elements().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A finite projection system over `0..n` given by a successor table `π` and the
    /// orbit-termination depths. (A concrete, enumerable `Π` for exercising R0.1.)
    struct FiniteSystem {
        pi: Vec<u32>, // π(i) = pi[i]
    }

    impl FiniteSystem {
        fn depth_to_fix(&self, mut x: u32) -> Option<u32> {
            // walk the orbit; a fixpoint terminates, a non-fixpoint cycle does not.
            let mut seen = vec![false; self.pi.len()];
            let mut steps = 0u32;
            loop {
                if self.pi[x as usize] == x {
                    return Some(steps);
                }
                if seen[x as usize] {
                    return None; // entered a non-trivial cycle: no fixpoint
                }
                seen[x as usize] = true;
                x = self.pi[x as usize];
                steps += 1;
            }
        }
    }

    impl ProjectionSystem for FiniteSystem {
        type Point = u32;
        fn projection(&self, x: &u32) -> u32 {
            self.pi[*x as usize]
        }
        fn projection_depth(&self, x: &u32) -> Option<u32> {
            self.depth_to_fix(*x)
        }
    }

    impl EnumerableProjectionSystem for FiniteSystem {
        fn universe(&self) -> Vec<u32> {
            (0..self.pi.len() as u32).collect()
        }
    }

    #[test]
    fn cnf_fiber_and_observable_equivalence() {
        // 0→2, 1→2, 2→3, 3→3 (fixpoint). CNF of 0,1,2,3 is all 3 ⇒ one fiber {0,1,2,3}.
        let s = FiniteSystem { pi: vec![2, 2, 3, 3] };
        assert!(s.is_fixpoint(&3));
        assert_eq!(s.canonical_form(&0), Some(3));
        assert_eq!(s.projection_depth(&0), Some(2));
        assert!(s.observably_equivalent(&0, &1));
        assert_eq!(s.fiber(&0), vec![0, 1, 2, 3]);
    }

    #[test]
    fn fiber_completeness_and_observability() {
        // two fixpoints: 0→1, 1→1, 2→3, 3→3 ⇒ fibers {0,1} and {2,3}.
        let s = FiniteSystem { pi: vec![1, 1, 3, 3] };
        // the identity invariant is unobservable where the fiber is non-trivial …
        assert!(!s.is_observable(|z| *z, &0));
        // … but the canonical-form invariant is observable everywhere (constant on fibers).
        assert!(s.is_observable(|z| s.canonical_form(z), &0));
        assert!(matches!(certify_fiber_completeness(&s), Ok(())));
    }

    #[test]
    fn fibers_are_monotone_under_refinement() {
        // coarser collapses everything to one fixpoint (0→0, 1→0, 2→0) ⇒ one fiber {0,1,2};
        // finer keeps two fixpoints (0→0, 1→1, 2→1) ⇒ fibers {0} and {1,2}.
        // finer refines coarser? No — coarser-fiber {0,1,2} ⊄ any finer-fiber. So the
        // inclusion FAILS, and the certificate reports it (the hypothesis is not met).
        let coarser = FiniteSystem { pi: vec![0, 0, 0] };
        let finer = FiniteSystem { pi: vec![0, 1, 1] };
        assert!(fibers_refine(&coarser, &finer).is_err());
        // a genuine refinement: coarser = finer ⇒ inclusion holds (reflexive case).
        assert!(matches!(fibers_refine(&coarser, &coarser), Ok(())));
    }
}
