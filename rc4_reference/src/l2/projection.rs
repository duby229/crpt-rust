//! # L2.1 — The Reduction Strategy ρ_M (and the `Model` it completes)
//!
//! Exact realization of spec section **L2.1** (`CRPT_OMEGA_TOWER_L2.md`, v1.0.0-rc4).
//! Items: L2.1.D1 `ρ_M` (C1 Step-or-Fix, C2 Bisimulation Equivariance), L2.1.D2 `ρ^n`,
//! L2.1.D3 `Fix`, L2.1.T1 `NF⊆Fix`, L2.1.T2 `Fix=NF`, L2.1.L1 `Fix-Stab`,
//! L2.1.D4 `Rec-Proj` (CFix). (C3, L2.1.R3, is a consequence, not a condition.)
//!
//! A **CRPT model** is a substrate together with a projection operator ρ_M
//! satisfying C1/C2. [`Model`] is that owned object; [`ProjectionOperator`] is the
//! borrowing operator *view* it hands out ([`Model::operator`]) — so the L2–L4
//! query functions read a `&ProjectionOperator` with no clone, and L5+ map between
//! `Model` values. C1/C2 are validated once, at `Model` construction.

use crate::l1::substrate::{ElementId, Substrate};

/// Error constructing a [`Model`] — i.e. data that is not a projection operator (L2.1.D1).
#[derive(Debug, Clone, Copy)]
pub enum ProjectionError {
    /// The strategy length differs from |𝒰|.
    WrongLength { expected: u32, got: usize },
    /// ρ_M(x) lands outside `0..n`.
    OutOfRange { x: ElementId, value: u32, n: u32 },
    /// **C1 (Step-or-Fix)** violated at x (L2.1.D1 C1).
    StepOrFix { x: ElementId, image: ElementId },
    /// **C2 (Bisimulation Equivariance)** violated: x ≈ y but ρ_M(x) ≉ ρ_M(y) (L2.1.D1 C2).
    BisimEquivariance { x: ElementId, y: ElementId },
    /// `from_functional_reduction` only: →_ρ branches at x.
    ReductionBranches { x: ElementId },
}

/// **L2.1.D1 (`ρ_M`)** — the projection operator, as a borrowing *view* over a
/// substrate and a strategy. The owned, validated object is [`Model`]; obtain a
/// view with [`Model::operator`]. The L2–L4 query functions take `&ProjectionOperator`.
pub struct ProjectionOperator<'a> {
    substrate: &'a Substrate,
    successor: &'a [ElementId], // ρ_M(x) for each x ∈ 𝒰
}

impl<'a> ProjectionOperator<'a> {
    /// The substrate ρ_M acts on.
    pub fn substrate(&self) -> &Substrate {
        self.substrate
    }

    /// **L2.1.D1**: ρ_M(x).
    #[inline]
    pub fn project(&self, x: ElementId) -> ElementId {
        self.successor[x.index()]
    }

    /// **L2.1.D2 (`ρ^n`)**: ρ_M^n(x) — n-fold application (ρ_M^0 = identity).
    pub fn iterate(&self, x: ElementId, n: u32) -> ElementId {
        let mut current = x;
        for _ in 0..n {
            current = self.project(current);
        }
        current
    }

    /// **L2.1.D3 (`Fix`)**: x ∈ Fix(ρ_M), i.e. ρ_M(x) = x.
    pub fn is_fixpoint(&self, x: ElementId) -> bool {
        self.project(x) == x
    }

    /// **L2.1.D3 (`Fix`)**: the set Fix(ρ_M) = {x | ρ_M(x) = x}, ascending.
    pub fn fixpoints(&self) -> Vec<ElementId> {
        self.substrate.elements().filter(|&x| self.is_fixpoint(x)).collect()
    }

    /// **L2.1.D4 (`Rec-Proj`)**: CFix(ρ_M)(x) = ρ_M^{d_M(x)}(x) — the fixpoint the
    /// ρ_M-orbit reaches. `Some` on ↓_M (unique by `UF` L2.1.L2); `None` on ∞_M
    /// (the asymptotic canonical form is L3.3). Exact on finite 𝒰.
    pub fn canonical_fixpoint(&self, x: ElementId) -> Option<ElementId> {
        let n = self.substrate.universe_len();
        let mut current = x;
        for _ in 0..=n {
            let next = self.project(current);
            if next == current {
                return Some(current);
            }
            current = next;
        }
        None
    }

    /// Witness **C1 (Step-or-Fix)** (L2.1.D1). First violating x, or `Ok`.
    pub fn certify_step_or_fix(&self) -> Result<(), ProjectionError> {
        for x in self.substrate.elements() {
            let image = self.successor[x.index()];
            let step_or_fix = self.substrate.reduces(x, image)
                || (image == x && self.substrate.is_normal_form(x));
            if !step_or_fix {
                return Err(ProjectionError::StepOrFix { x, image });
            }
        }
        Ok(())
    }

    /// Witness **C2 (Bisimulation Equivariance)** (L2.1.D1): ρ_M maps each ≈-class
    /// into a single ≈-class (against the substrate's computed ≈, L1.1.D7). First
    /// violating pair, or `Ok`.
    pub fn certify_bisim_equivariance(&self) -> Result<(), ProjectionError> {
        let representative = self.substrate.bisimilarity();
        let n = self.substrate.universe_len() as usize;
        let mut image_class: Vec<Option<(ElementId, ElementId)>> = vec![None; n];
        for x in self.substrate.elements() {
            let class = representative[x.index()].index();
            let image_of_class = representative[self.successor[x.index()].index()];
            match image_class[class] {
                None => image_class[class] = Some((image_of_class, x)),
                Some((previous, witness)) => {
                    if previous != image_of_class {
                        return Err(ProjectionError::BisimEquivariance { x, y: witness });
                    }
                }
            }
        }
        Ok(())
    }

    /// Witness **L2.1.T1 (`NF⊆Fix`)**: every normal form is a fixpoint.
    pub fn certify_nf_subset_fix(&self) -> Result<(), ElementId> {
        for x in self.substrate.normal_forms() {
            if !self.is_fixpoint(x) {
                return Err(x);
            }
        }
        Ok(())
    }

    /// **L2.1.T2 (`Fix=NF`)**: whether Fix(ρ_M) = NF(→_ρ) holds (the PA-Fix model property).
    pub fn fix_equals_nf(&self) -> bool {
        self.substrate
            .elements()
            .all(|x| self.is_fixpoint(x) == self.substrate.is_normal_form(x))
    }
}

/// A **CRPT model** (L2.1.D1 / L5.1.D1 `CRPT-Mod-18` / L1.5.D4 `CRPT-Mod`): a [`Substrate`] together with a projection operator
/// ρ_M satisfying C1 (Step-or-Fix) and C2 (Bisimulation Equivariance). Owns its
/// data; C1/C2 are validated at construction, so a `Model` *is* a CRPT model. No
/// derived equality — model sameness is homomorphism/isomorphism (L5).
#[derive(Debug)]
pub struct Model {
    substrate: Substrate,
    strategy: Vec<ElementId>, // ρ_M(x) for each x ∈ 𝒰
}

impl Model {
    /// Construct a model from a substrate and an explicit strategy `ρ_M(x)`,
    /// validating C1 and C2 (L2.1.D1).
    pub fn new(substrate: Substrate, strategy: Vec<ElementId>) -> Result<Self, ProjectionError> {
        let n = substrate.universe_len();
        if strategy.len() != n as usize {
            return Err(ProjectionError::WrongLength { expected: n, got: strategy.len() });
        }
        for (i, &image) in strategy.iter().enumerate() {
            if image.index() >= n as usize {
                return Err(ProjectionError::OutOfRange { x: ElementId(i as u32), value: image.0, n });
            }
        }
        {
            let view = ProjectionOperator { substrate: &substrate, successor: &strategy };
            view.certify_step_or_fix()?; // C1
            view.certify_bisim_equivariance()?; // C2
        }
        Ok(Self { substrate, strategy })
    }

    /// Construct the canonical model when →_ρ is *functional* (each non-normal-form
    /// element has exactly one →_ρ-successor). Fails on a branching →_ρ.
    pub fn from_functional_reduction(substrate: Substrate) -> Result<Self, ProjectionError> {
        let mut strategy = Vec::with_capacity(substrate.universe_len() as usize);
        for x in substrate.elements() {
            let successors = substrate.reduction_successors(x);
            match successors.len() {
                0 => strategy.push(x), // normal form: ρ_M(x) = x
                1 => strategy.push(successors[0]),
                _ => return Err(ProjectionError::ReductionBranches { x }),
            }
        }
        Self::new(substrate, strategy)
    }

    /// The borrowing projection-operator view (L2.1.D1), for the L2–L4 query functions.
    pub fn operator(&self) -> ProjectionOperator<'_> {
        ProjectionOperator { substrate: &self.substrate, successor: &self.strategy }
    }

    /// The model's substrate.
    pub fn substrate(&self) -> &Substrate {
        &self.substrate
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l2::projection::Model;

    /// Common-Pitfalls substrate (spec L2.1.1): 𝒰 = {0,1,2}, ρ(0)=ρ(1)=2, 2 ∈ NF.
    fn pitfalls() -> Substrate {
        Substrate::new(3, &[(0, 2), (1, 2)], &[(0, 2), (1, 2), (0, 1)]).unwrap()
    }

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn model_from_functional_reduction() {
        let m = Model::from_functional_reduction(pitfalls()).unwrap();
        let p = m.operator();
        assert_eq!(p.project(id(0)), id(2));
        assert_eq!(p.project(id(2)), id(2)); // normal form fixes itself
        assert_eq!(p.iterate(id(0), 5), id(2)); // idempotent past the fixpoint
    }

    #[test]
    fn fixpoints_and_canonical_form() {
        let m = Model::from_functional_reduction(pitfalls()).unwrap();
        let p = m.operator();
        assert!(p.is_fixpoint(id(2)));
        assert!(!p.is_fixpoint(id(0)));
        assert_eq!(p.fixpoints(), vec![id(2)]);
        assert_eq!(p.canonical_fixpoint(id(0)), Some(id(2)));
    }

    #[test]
    fn theorems_nf_fix() {
        let m = Model::from_functional_reduction(pitfalls()).unwrap();
        let p = m.operator();
        assert!(matches!(p.certify_nf_subset_fix(), Ok(()))); // T1
        assert!(p.fix_equals_nf()); // T2
        assert!(matches!(p.certify_step_or_fix(), Ok(()))); // C1
        assert!(matches!(p.certify_bisim_equivariance(), Ok(()))); // C2
    }

    #[test]
    fn c1_violation_is_rejected() {
        // ρ(0) = 1, but 0 →_ρ {2} only and 1 ≠ 0 ⇒ neither C1 disjunct holds.
        assert!(matches!(
            Model::new(pitfalls(), vec![id(1), id(2), id(2)]),
            Err(ProjectionError::StepOrFix { x, image }) if x == id(0) && image == id(1)
        ));
    }

    #[test]
    fn functional_reduction_rejects_branching() {
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        assert!(matches!(
            Model::from_functional_reduction(s),
            Err(ProjectionError::ReductionBranches { x }) if x == id(0)
        ));
    }

    #[test]
    fn c2_violation_is_rejected() {
        // 0,1 each branch →_ρ to {2,3}; 2 self-loops (∞), 3 ∈ NF ⇒ 0 ≈ 1 but 2 ≉ 3.
        let edges = [(0, 2), (0, 3), (1, 2), (1, 3), (2, 2)];
        let s = Substrate::new(4, &edges, &edges).unwrap();
        assert!(s.bisimilar(id(0), id(1)));
        assert!(!s.bisimilar(id(2), id(3)));
        assert!(matches!(
            Model::new(s, vec![id(2), id(3), id(2), id(3)]),
            Err(ProjectionError::BisimEquivariance { .. })
        ));
    }

    #[test]
    fn canonical_form_is_none_on_persistent() {
        let s = Substrate::new(2, &[(0, 1), (1, 0)], &[(0, 1), (1, 0)]).unwrap();
        let m = Model::from_functional_reduction(s).unwrap();
        let p = m.operator();
        assert_eq!(p.canonical_fixpoint(id(0)), None);
        assert!(p.fixpoints().is_empty());
    }
}
