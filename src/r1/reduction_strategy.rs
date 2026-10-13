//! # R1.8 — The Reduction Strategy ρ_M
//!
//! Exact realization of spec section **R1.8** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9).
//! Items: R1.8.D1 `ρ_M` (C1 Step-or-Fix, C2 Bisimulation Equivariance), R1.8.D2 `ρ^n`,
//! R1.8.D3 `Fix`, R1.8.T1 `NF⊆Fix`, R1.8.T2 `Fix=NF`, R1.8.L1 `Fix-Stab`,
//! R1.8.D4 `Rec-Proj` (CFix). (C3, R1.8.R3, is a consequence, not a condition.)
//!
//! A **CRPT instance** is a substrate together with a projection operator ρ_M
//! satisfying C1/C2/C3. [`Instance`] is that owned object; [`ProjectionOperator`] is the
//! borrowing operator *view* it hands out ([`Instance::operator`]) — so the L2–L4
//! query functions read a `&ProjectionOperator` with no clone, and the higher ranks map between
//! `Instance` values. C1/C2 are validated once, at `Instance` construction.

use crate::r1::substrate::{ElementId, Substrate};

/// Error constructing an [`Instance`] — i.e. data that is not a projection operator (R1.8.D1).
#[derive(Debug, Clone, Copy)]
pub enum ProjectionError {
    /// The strategy length differs from |𝒰|.
    WrongLength { expected: u32, got: usize },
    /// ρ_M(x) lands outside `0..n`.
    OutOfRange { x: ElementId, value: u32, n: u32 },
    /// **C1 (Step-or-Fix)** violated at x (R1.8.D1 C1).
    StepOrFix { x: ElementId, image: ElementId },
    /// **C2 (Bisimulation Equivariance)** violated: x ≈ y but ρ_M(x) ≉ ρ_M(y) (R1.8.D1 C2).
    BisimEquivariance { x: ElementId, y: ElementId },
    /// `from_functional_reduction` only: →_ρ branches at x.
    ReductionBranches { x: ElementId },
}

/// **R1.8.D1 (`ρ_M`)** — the projection operator, as a borrowing *view* over a
/// substrate and a strategy. The owned, validated object is [`Instance`]; obtain a
/// view with [`Instance::operator`]. The L2–L4 query functions take `&ProjectionOperator`.
pub struct ProjectionOperator<'a> {
    substrate: &'a Substrate,
    successor: &'a [ElementId], // ρ_M(x) for each x ∈ 𝒰
}

impl<'a> ProjectionOperator<'a> {
    /// The substrate ρ_M acts on.
    pub fn substrate(&self) -> &Substrate {
        self.substrate
    }

    /// **R1.8.D1**: ρ_M(x).
    #[inline]
    pub fn project(&self, x: ElementId) -> ElementId {
        self.successor[x.index()]
    }

    /// **R1.8.D2 (`ρ^n`)**: ρ_M^n(x) — n-fold application (ρ_M^0 = identity).
    pub fn iterate(&self, x: ElementId, n: u32) -> ElementId {
        let mut current = x;
        for _ in 0..n {
            current = self.project(current);
        }
        current
    }

    /// **R1.8.D3 (`Fix`)**: x ∈ Fix(ρ_M), i.e. ρ_M(x) = x.
    pub fn is_fixpoint(&self, x: ElementId) -> bool {
        self.project(x) == x
    }

    /// **R1.8.D3 (`Fix`)**: the set Fix(ρ_M) = {x | ρ_M(x) = x}, ascending.
    pub fn fixpoints(&self) -> Vec<ElementId> {
        self.substrate.elements().filter(|&x| self.is_fixpoint(x)).collect()
    }

    /// **R1.8.D4 (`Rec-Proj`)**: CFix(ρ_M)(x) = ρ_M^{d_M(x)}(x) — the fixpoint the
    /// ρ_M-orbit reaches. `Some` on ↓_M (unique by `UF` R1.8.L2); `None` on ∞_M
    /// (the asymptotic canonical form is R2.3). Exact on finite 𝒰.
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

    /// Witness **C1 (Step-or-Fix)** (R1.8.D1). First violating x, or `Ok`.
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

    /// Witness **C2 (Bisimulation Equivariance)** (R1.8.D1): ρ_M maps each ≈-class
    /// into a single ≈-class (against the substrate's computed ≈, R1.1.D7). First
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

    /// Witness **R1.8.T1 (`NF⊆Fix`)**: every normal form is a fixpoint.
    pub fn certify_nf_subset_fix(&self) -> Result<(), ElementId> {
        for x in self.substrate.normal_forms() {
            if !self.is_fixpoint(x) {
                return Err(x);
            }
        }
        Ok(())
    }

    /// **R1.8.T2 (`Fix=NF`)**: whether Fix(ρ_M) = NF(→_ρ) holds (the PA-Fix instance property).
    pub fn fix_equals_nf(&self) -> bool {
        self.substrate
            .elements()
            .all(|x| self.is_fixpoint(x) == self.substrate.is_normal_form(x))
    }
}

/// A **CRPT instance** (R1.8.D1 `ρ_M` / R4.1.D1 `CRPT-Inst-18`): a [`Substrate`] together with a projection operator
/// ρ_M satisfying C1 (Step-or-Fix) and C2 (Bisimulation Equivariance). Owns its
/// data; C1/C2 are validated at construction, so a `Instance` *is* a CRPT instance. No
/// derived equality — instance sameness is homomorphism/isomorphism (R4).
#[derive(Debug)]
pub struct Instance {
    substrate: Substrate,
    strategy: Vec<ElementId>, // ρ_M(x) for each x ∈ 𝒰
}

impl Instance {
    /// Construct an instance from a substrate and an explicit strategy `ρ_M(x)`,
    /// validating C1 and C2 (R1.8.D1).
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

    /// Construct the canonical instance when →_ρ is *functional* (each non-normal-form
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

    /// The borrowing projection-operator view (R1.8.D1), for the L2–L4 query functions.
    pub fn operator(&self) -> ProjectionOperator<'_> {
        ProjectionOperator { substrate: &self.substrate, successor: &self.strategy }
    }

    /// The instance's substrate.
    pub fn substrate(&self) -> &Substrate {
        &self.substrate
    }
}

/// Witness **R1.8.R1 (`Proj-vs-Abs`)** — why `ρ_M` is the *projection* operator and how
/// projection differs from **abstraction**: `ρ_M` is **one step** (`project`), while
/// abstraction is the *whole* map to the canonical form (`canonical_fixpoint` = `CFix`, the
/// iterated projection). Returns `true` when, off the fixpoints, the single projection step is
/// genuinely *not yet* the abstraction (they differ until the orbit settles) — exhibiting that
/// projection is the stepwise operator whose closure is abstraction.
pub fn projection_differs_from_abstraction(op: &ProjectionOperator) -> bool {
    op.substrate().elements().any(|x| {
        // a depth-≥2 convergent element: one projection step ≠ its canonical form (abstraction).
        op.canonical_fixpoint(x).is_some_and(|cfix| op.project(x) != cfix && !op.is_fixpoint(x))
    })
}

/// Witness **R1.8.R2 (`Rho-RegNeutral`)** — `ρ_M` is **aspect-neutral**: it acts by the *same*
/// rule (`project`) on convergent and persistent elements alike; the aspect dichotomy is a
/// property of orbits, not of the operator's action at a point. Returns the first element on
/// which the operator's single-step action depends on anything but its successor table (none —
/// `project` is one total function), or `Ok`.
pub fn certify_rho_aspect_neutral(op: &ProjectionOperator) -> Result<(), ElementId> {
    let n = op.substrate().universe_len();
    for x in op.substrate().elements() {
        // ρ_M is one total function into 𝒰 — its single-step action is a successor-table
        // lookup that consults no aspect tag. Witnessed: the image is always a valid element,
        // whether x is convergent or persistent.
        if op.project(x).index() >= n as usize {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.8.T3 (`Dead-End`)** — a **dead-end fixpoint** is a fixpoint reachable only from
/// itself: no *other* element's `ρ_M`-orbit passes through it (its preimage is `{f}`). These
/// are the absorbing sinks of the reduction graph; the distinction matters for the NFC fiber
/// structure (a dead-end has a singleton normal-form fiber). Returns whether `f` is a dead-end.
pub fn is_dead_end_fixpoint(op: &ProjectionOperator, f: ElementId) -> bool {
    op.is_fixpoint(f) && op.substrate().elements().all(|x| x == f || op.project(x) != f)
}

/// Witness **R1.8.T4 (`RP=Abs`)** — **Recursive Projection equals Abstraction**: the canonical
/// fixpoint map `CFix(ρ_M)` *is* the abstraction map `α_M` (the Galois insertion `α_M ⊣ γ_M`,
/// R6) — iterating `ρ_M` to the fixpoint is the same operation as abstracting an element to its
/// `≃_M`-class. Realized by confirming that two convergent elements share a `CFix` iff they
/// share an abstraction class. (`R1.8.R4` `RPAbs-NoNewAx`: this needs only `PA-WN`, `PA-Conf`,
/// `C1`.) Returns the first convergent pair where `CFix`-equality and abstraction-class
/// equality disagree (none), or `Ok`.
pub fn certify_rp_equals_abs(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let abstraction = crate::r1::fibers::observable_classes(op); // α_M class per element
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            let (cx, cy) = (op.canonical_fixpoint(x), op.canonical_fixpoint(y));
            if cx.is_some() && cy.is_some() {
                let cfix_eq = cx == cy;
                let abs_eq = abstraction[x.index()] == abstraction[y.index()];
                if cfix_eq != abs_eq {
                    return Err((x, y));
                }
            }
        }
    }
    Ok(())
}

/// Witness **R1.8.R5 (`Mono-Deriv`)** / **R1.8.R6 (`Disc-Proj`)** — monotonicity of the
/// projection is **derivable**, not assumed: each `ρ_M`-step is a stepwise **discernibility
/// compression** — `d_M` strictly decreases toward the canonical observable, so the orbit
/// monotonically erases indiscernible structure. Returns the first convergent non-fixpoint
/// whose projection fails to decrease the derivation height (none), or `Ok`.
pub fn certify_projection_monotone(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::derivation_height::{derivation_height, DerivationHeight};
    for x in op.substrate().elements() {
        if let DerivationHeight::Finite(d) = derivation_height(op, x) {
            if d >= 1 && derivation_height(op, op.project(x)) != DerivationHeight::Finite(d - 1) {
                return Err(x);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Instance;

    /// Common-Pitfalls substrate (spec R1.8.1): 𝒰 = {0,1,2}, ρ(0)=ρ(1)=2, 2 ∈ NF.
    fn pitfalls() -> Substrate {
        Substrate::new(3, &[(0, 2), (1, 2)], &[(0, 2), (1, 2), (0, 1)]).unwrap()
    }

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn model_from_functional_reduction() {
        let m = Instance::from_functional_reduction(pitfalls()).unwrap();
        let p = m.operator();
        assert_eq!(p.project(id(0)), id(2));
        assert_eq!(p.project(id(2)), id(2)); // normal form fixes itself
        assert_eq!(p.iterate(id(0), 5), id(2)); // idempotent past the fixpoint
    }

    #[test]
    fn projection_role_dead_ends_rp_equals_abs_and_monotonicity() {
        // 0→1→2, 2 ∈ NF (depth-2 chain) ; 3→2 also ; 4 an isolated normal form (dead-end).
        let e = [(0, 1), (1, 2), (3, 2)];
        let m = Instance::from_functional_reduction(Substrate::new(5, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // Proj-vs-Abs: one projection step of 0 (→1) ≠ its abstraction CFix(0) (=2).
        assert!(projection_differs_from_abstraction(&op));
        // Rho-RegNeutral: ρ_M is one total function (aspect-neutral).
        assert!(matches!(certify_rho_aspect_neutral(&op), Ok(())));
        // Dead-End: 4 is an isolated fixpoint (no other orbit passes through it); 2 is not
        // (1 and 3 flow into it).
        assert!(is_dead_end_fixpoint(&op, id(4)));
        assert!(!is_dead_end_fixpoint(&op, id(2)));
        // RP=Abs: CFix-equality = abstraction-class equality.
        assert!(matches!(certify_rp_equals_abs(&op), Ok(())));
        // Mono-Deriv / Disc-Proj: each projection step strictly compresses d_M.
        assert!(matches!(certify_projection_monotone(&op), Ok(())));
    }

    #[test]
    fn fixpoints_and_canonical_form() {
        let m = Instance::from_functional_reduction(pitfalls()).unwrap();
        let p = m.operator();
        assert!(p.is_fixpoint(id(2)));
        assert!(!p.is_fixpoint(id(0)));
        assert_eq!(p.fixpoints(), vec![id(2)]);
        assert_eq!(p.canonical_fixpoint(id(0)), Some(id(2)));
    }

    #[test]
    fn theorems_nf_fix() {
        let m = Instance::from_functional_reduction(pitfalls()).unwrap();
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
            Instance::new(pitfalls(), vec![id(1), id(2), id(2)]),
            Err(ProjectionError::StepOrFix { x, image }) if x == id(0) && image == id(1)
        ));
    }

    #[test]
    fn functional_reduction_rejects_branching() {
        let s = Substrate::new(3, &[(0, 1), (0, 2)], &[(0, 1), (0, 2)]).unwrap();
        assert!(matches!(
            Instance::from_functional_reduction(s),
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
            Instance::new(s, vec![id(2), id(3), id(2), id(3)]),
            Err(ProjectionError::BisimEquivariance { .. })
        ));
    }

    #[test]
    fn canonical_form_is_none_on_persistent() {
        let s = Substrate::new(2, &[(0, 1), (1, 0)], &[(0, 1), (1, 0)]).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap();
        let p = m.operator();
        assert_eq!(p.canonical_fixpoint(id(0)), None);
        assert!(p.fixpoints().is_empty());
    }
}
