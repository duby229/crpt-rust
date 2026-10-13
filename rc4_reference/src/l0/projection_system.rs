//! # L0.1 — The Projection System
//!
//! Exact realization of spec section **L0.1** (`CRPT_OMEGA_TOWER_L0.md`, v1.0.0-rc4):
//!
//! - L0.1.D1 `ProjSys` — a projection system `Π = (𝒰, π, →_σ)`: a universe, a projection
//!   map `π : 𝒰 → 𝒰` (no properties assumed), and the structural relation. The canonical
//!   form `CNF_π(x) = lim π^n(x)` exists when the π-orbit terminates in `Fix(π)`.
//! - L0.1.D2 `Fiber` — the fiber `L_π(x) = {z | CNF_π(z) = CNF_π(x)}` and observable
//!   equivalence `x ≃_π y ⟺ CNF_π(x) = CNF_π(y)`.
//! - L0.1.D3 `Obs_π` — an invariant `I` is π-observable at `x` iff it is constant on `L_π(x)`.
//! - L0.1.T3 `CRPT-Fiber` — the **CRPT instance**: with `π = ρ_M`, `CNF_π = CFix`, the
//!   universal fiber `L_π` *is* the normal-form fiber `NFC_M` and `≃_π` *is* `≃_M`.
//!
//! ## One notion — everything is a projection system
//!
//! There is exactly **one** trait here, [`ProjectionSystem`] = L0.1.D1 `ProjSys`, because
//! the theory has exactly one notion. *Recursive Projection Theory*: every projection
//! system is built by recursion on the one below it —
//!
//! - the **recursive projection** `Rec-Proj` (L2.1.D4): `CFix(ρ_M)(x) := ρ_M^{d_M(x)}(x)`,
//!   the operator iterated on itself (its NWF dual is the *co-recursive* projection
//!   `CNF∞` L3.3.D6) — realized verbatim by [`canonical_form`](ProjectionSystem::canonical_form);
//! - the **tower lift** `TowerLift` (L0.5.D1): `Lift(Π)` *is itself a projection system*
//!   `(𝒰', π', →_σ')` over the fiber classes of `Π` — realized by
//!   [`Lift`](crate::l8::lift::Lift)`: ProjectionSystem`;
//! - the **tower** (L8.4.D1): `Mₙ₊₁ := Lift(Mₙ)` — CRPT models all the way up, **fractal**
//!   (`Frac` L8.9: every tail self-similar to the whole).
//!
//! So [`ProjectionOperator`] (the finite `ρ_M`), [`Lift`](crate::l8::lift::Lift) (the
//! infinite `Lift(M)`), and the topological chain
//! [`ConvergentChain`](crate::l1::topology::ConvergentChain) (`ℕ ∪ {ω}`) are **instances of
//! the same trait** — one operator, one abstraction bridging WF and NWF. What differs is
//! only the universe *representation*: dense [`ElementId`] indices versus symbolic points,
//! with every construct computed from the finitely-presented queries
//! ([`projection_depth`](ProjectionSystem::projection_depth),
//! [`preimage_size`](ProjectionSystem::preimage_size)) — never by enumerating `𝒰`. That
//! infinite structure is always finitely presented is `Inf-Dual` (L2.2.T7,
//! [`crate::l2::regime`]).
//!
//! A projection system on a **finite substrate** additionally admits *listing* — fibers,
//! kernels, the partition — which is exactly where the theory is fully decidable
//! (`Finite-Collapse` L0.7.T2, `FOL-Fin` L5.3.T4). That refinement, and only that, is
//! [`FiniteProjectionSystem`]. The canonicalization *mode* (recurrence / convergence —
//! exactly two, L1.4.D1 rc4) is orthogonal: the same operator, extended by a `𝒯`-limit —
//! [`TopologicalProjectionSystem`](crate::l1::topology::TopologicalProjectionSystem), a
//! sub-trait of this one.

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;

/// **L0.1.D1 (`ProjSys`)** — *the* projection system `Π = (𝒰, π, →_σ)`, generic over the
/// universe representation [`Point`](Self::Point) (finite or infinite). Implementors supply
/// the projection map `π` and the finitely-presented queries — the depth
/// [`projection_depth`](Self::projection_depth) and the kernel size
/// [`preimage_size`](Self::preimage_size); the canonical form (`Rec-Proj`), the regimes,
/// `≃_π`, and the horizon predicates follow as default methods, identical for every
/// instance.
pub trait ProjectionSystem {
    /// An element of the (possibly infinite) universe `𝒰`.
    type Point: Clone + PartialEq;

    /// **L0.1.D1**: `π(x)` — the projection map, one application (`π = ρ_M` in the CRPT
    /// instance, L2.1.D1).
    fn projection(&self, x: &Self::Point) -> Self::Point;

    /// `d_π(x)` — the projection depth (`d_M` L2.3.D2 in the CRPT instance): the least `n`
    /// with `π^n(x) ∈ Fix(π)`, or `None` on `Pers(π) = ∞_M`. The finitely-presented regime
    /// query — supplied by the instance, since deciding it by blind orbit iteration on an
    /// infinite universe is undecidable (`RTD-Und` L6.5.T3).
    fn projection_depth(&self, x: &Self::Point) -> Option<u32>;

    /// `|π⁻¹(y)|` — the kernel size at `y` (the sibling structure the horizons read,
    /// L0.3.D1), computed from the finite presentation: finite even when `𝒰` is infinite
    /// (in `Lift(M)`, `π⁻¹(w) ⊇ {w·a : a ∈ Q_M}`). `None` if the instance does not
    /// finitely determine it.
    fn preimage_size(&self, y: &Self::Point) -> Option<u32> {
        let _ = y;
        None
    }

    /// **L0.4.D1 (`Q1`)** — the classification predicate `Q1(x) = (x ∈ Fix(π))`: x is a
    /// projection fixpoint (`π(x) = x`), the anchor of the fiber structure.
    fn is_projection_fixpoint(&self, x: &Self::Point) -> bool {
        self.projection(x) == *x
    }

    /// **L0.1.D1 (`CNF_π`) = L2.1.D4 (`Rec-Proj`)** — the *recursive projection*
    /// `CFix(π)(x) := π^{d_π(x)}(x)`: the canonical form, by applying `π` exactly `d_π(x)`
    /// times. `None` on `Pers(π)` (where its dual, the co-recursive `CNF∞` L3.3.D6, takes
    /// over in the NWF tier).
    fn canonical_form(&self, x: &Self::Point) -> Option<Self::Point> {
        let d = self.projection_depth(x)?;
        let mut current = x.clone();
        for _ in 0..d {
            current = self.projection(&current);
        }
        Some(current)
    }

    /// **L0.2.D1 (`Conv`)** — `x ∈ Conv(π) = ↓_M`: the π-orbit reaches a fixpoint finitely.
    fn is_convergent(&self, x: &Self::Point) -> bool {
        self.projection_depth(x).is_some()
    }

    /// **L0.2.D1 (`Pers`)** — `x ∈ Pers(π) = ∞_M`: the π-orbit never reaches a fixpoint.
    fn is_persistent(&self, x: &Self::Point) -> bool {
        self.projection_depth(x).is_none()
    }

    /// **L0.1.D2 (`≃_π`)**: `x ≃_π y ⟺ CNF_π(x) = CNF_π(y)` (both defined).
    fn observable_equivalent(&self, x: &Self::Point, y: &Self::Point) -> bool {
        match (self.canonical_form(x), self.canonical_form(y)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }

    /// **L0.3.D1 (`H_S^π`)** — the universal structural horizon: x has a sibling under π
    /// (the kernel at `π(x)` has more than one element). Computed from
    /// [`preimage_size`](Self::preimage_size) — symbolically, on any representation;
    /// `None` where the kernel size is not finitely determined.
    fn structural_horizon(&self, x: &Self::Point) -> Option<bool> {
        self.preimage_size(&self.projection(x)).map(|k| k > 1)
    }

    /// **L0.3.D1 (`H_O^π`)** — the universal depth horizon: `d_π(x) = 1` (one π-step from a
    /// fixpoint).
    fn depth_horizon(&self, x: &Self::Point) -> bool {
        self.projection_depth(x) == Some(1)
    }
}

/// **L0.1.D1 on a finite substrate** — the refinement where `𝒰` can be *listed*, which is
/// exactly where the theory is fully decidable (`Finite-Collapse` L0.7.T2; `FOL-Fin`
/// L5.3.T4): fibers, kernels, and observability checks materialize as finite sets. This
/// listing capability is the **only** thing the finite case adds — the operator and every
/// per-point construct live on [`ProjectionSystem`], shared with the infinite instances.
pub trait FiniteProjectionSystem: ProjectionSystem<Point = ElementId> {
    /// `|𝒰|`.
    fn universe_size(&self) -> u32;

    /// **L0.1.D1**: the structural successors `{y | x →_σ y}`.
    fn structural_successors(&self, x: ElementId) -> &[ElementId];

    /// **L0.1.D2 (`Fiber`)**: `L_π(x) = {z | CNF_π(z) = CNF_π(x)}`, ascending (by listing).
    fn fiber(&self, x: ElementId) -> Vec<ElementId> {
        let target = self.canonical_form(&x);
        (0..self.universe_size())
            .map(ElementId)
            .filter(|z| self.canonical_form(z) == target)
            .collect()
    }

    /// The **π-kernel** at `y`: `{z | π(z) = y}` (the one-step preimage), ascending — the
    /// sibling structure of L0.3.D1, materialized by listing.
    fn kernel(&self, y: ElementId) -> Vec<ElementId> {
        (0..self.universe_size()).map(ElementId).filter(|z| self.projection(z) == y).collect()
    }

    /// **L0.3.D1 (`H_I^π`)** — the universal invariant horizon: `H_S^π(x)` and the kernel of
    /// `π` at `π(x)` is **depth-uniform** (every sibling shares x's projection depth) — the
    /// non-circular `H_I-Dec` form (L3.1.C1). Reads the kernel *elements*, hence finite.
    fn invariant_horizon(&self, x: ElementId) -> bool {
        if self.structural_horizon(&x) != Some(true) {
            return false;
        }
        let depth = self.projection_depth(&x);
        self.kernel(self.projection(&x)).into_iter().all(|z| self.projection_depth(&z) == depth)
    }

    /// **L0.1.D3 (`Obs_π`)**: an invariant `I` is π-observable at `x` — constant on `L_π(x)`.
    fn is_observable<T: PartialEq>(&self, invariant: impl Fn(ElementId) -> T, x: ElementId) -> bool {
        let value_at_x = invariant(x);
        self.fiber(x).into_iter().all(|z| invariant(z) == value_at_x)
    }
}

/// **L0.1.T3 (`CRPT-Fiber`)** — the CRPT operator is a projection system with `π = ρ_M`.
impl ProjectionSystem for ProjectionOperator<'_> {
    type Point = ElementId;

    fn projection(&self, x: &ElementId) -> ElementId {
        self.project(*x) // π = ρ_M (one step)
    }

    fn projection_depth(&self, x: &ElementId) -> Option<u32> {
        // finite substrate: the orbit either hits Fix(ρ_M) within |𝒰| steps or has cycled.
        let bound = self.substrate().universe_len();
        let mut current = *x;
        for n in 0..=bound {
            if self.is_fixpoint(current) {
                return Some(n);
            }
            current = self.project(current);
        }
        None
    }

    fn preimage_size(&self, y: &ElementId) -> Option<u32> {
        Some(self.substrate().elements().filter(|&z| self.project(z) == *y).count() as u32)
    }
}

/// The finite CRPT operator admits listing (`Finite-Collapse` L0.7.T2).
impl FiniteProjectionSystem for ProjectionOperator<'_> {
    fn universe_size(&self) -> u32 {
        self.substrate().universe_len()
    }

    fn structural_successors(&self, x: ElementId) -> &[ElementId] {
        self.substrate().structural_successors(x)
    }
}

/// Witness **L0.1.T3 (`CRPT-Fiber`)** — the universal L0.1 structure, instantiated at
/// `π = ρ_M`, coincides with CRPT's `NFC_M`/`≃_M`: the universal fiber `L_π(x)` equals the
/// normal-form fiber of `CFix(x)` (L2.5.D1), and `≃_π` equals `≃_M` (L2.5.D2). Returns the
/// first element/pair where they disagree (none), or `Ok`.
pub fn certify_crpt_fiber_instance(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::l2::fiber::{normal_form_fiber, observable_equivalence};
    for x in op.substrate().elements() {
        // L_π(x) = NFC_M(CFix(x)) on ↓_M.
        if let Some(canonical) = op.canonical_form(&x) {
            if op.fiber(x) != normal_form_fiber(op, canonical) {
                return Err(x);
            }
        }
        // ≃_π = ≃_M.
        for y in op.substrate().elements() {
            if op.observable_equivalent(&x, &y) != observable_equivalence(op, x, y) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **L0.2.T3 (`CRPT-Regimes`)** + **L0.3 / L0.4 instance** — the universal
/// projection-system layer (π = ρ_M) coincides with CRPT's L2/L3 constructs: `Conv(π)`/
/// `Pers(π)` are `↓_M`/`∞_M` (L2.2), `Q1` is `Fix(ρ_M)`, and `H_S^π`/`H_I^π`/`H_O^π` are the
/// L3.1 horizons. Returns the first element where any universal/instance pair disagrees, or `Ok`.
pub fn certify_crpt_universal_instance(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::l2::regime::is_convergent;
    use crate::l3::horizon::{depth_horizon, invariant_horizon, structural_horizon};
    for x in op.substrate().elements() {
        let ok = op.is_convergent(&x) == is_convergent(op, x) // Conv(π) = ↓_M (L0.2.T3)
            && op.is_projection_fixpoint(&x) == op.is_fixpoint(x) // Q1 = Fix(ρ_M)
            && op.structural_horizon(&x) == Some(structural_horizon(op, x)) // H_S^π = H_S
            && op.depth_horizon(&x) == depth_horizon(op, x) // H_O^π = H_O
            && op.invariant_horizon(x) == invariant_horizon(op, x); // H_I^π = H_I
        if !ok {
            return Err(x);
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
    fn crpt_operator_is_a_projection_system() {
        // 0→2, 1→2, 2→3, 3 ∈ NF. π = ρ_M; CNF_π = CFix; L_π = NFC; ≃_π = ≃_M.
        let e = [(0, 2), (1, 2), (2, 3)];
        let m = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // π is the one-step projection ρ_M.
        assert_eq!(op.projection(&id(0)), id(2));
        // CNF_π(0) = CFix(0) = 3 — the recursive projection (Rec-Proj): π applied d_π times.
        assert_eq!(op.projection_depth(&id(0)), Some(2));
        assert_eq!(op.canonical_form(&id(0)), Some(id(3)));
        // the whole component is one fiber (all reach 3).
        assert_eq!(op.fiber(id(0)), vec![id(0), id(1), id(2), id(3)]);
        assert!(op.observable_equivalent(&id(0), &id(1)));
        // CRPT-Fiber (L0.1.T3): the universal structure coincides with NFC_M/≃_M.
        assert!(matches!(certify_crpt_fiber_instance(&op), Ok(())));
        // the universal regime/Q1/horizons coincide with the CRPT L2/L3 instance;
        // the structural horizon is computed symbolically (via preimage_size).
        assert!(op.is_convergent(&id(0)) && op.is_projection_fixpoint(&id(3)));
        assert_eq!(op.structural_horizon(&id(2)), Some(true)); // 0,1 both ρ-map to 2
        assert!(matches!(certify_crpt_universal_instance(&op), Ok(())));
    }

    #[test]
    fn observability_is_constancy_on_the_fiber() {
        // Two NF components: 0→1, 2→3. Fibers {0,1} and {2,3}.
        let e = [(0, 1), (2, 3)];
        let m = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // the invariant "canonical form" is π-observable everywhere (constant on fibers).
        assert!(op.is_observable(|z| op.canonical_form(&z), id(0)));
        // an invariant that splits the fiber {0,1} is NOT π-observable at 0.
        assert!(!op.is_observable(|z| z == id(0), id(0)));
    }
}
