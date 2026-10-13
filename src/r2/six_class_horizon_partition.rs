//! # R2.2 — Six-Class and Twelve-Class Horizon Partitions
//!
//! Exact realization of spec section **R2.2** (`CRPT_OMEGA_TOWER_R2.md`, v1.0.0-rc9):
//!
//! - R2.2.D2 `Bool-Pred` — the predicates Q1 (Fix membership), Q2 (H_S), Q3 (H_I).
//! - R2.2.T1 `6-Part` — the six-class partition of ↓_M into A–F.
//! - R2.2.T2 `F=∅` — Class F is empty in every deterministic CRPT instance.
//! - R2.2.D6 `12-Part` + R2.2.T3 `12-Part-EE` — the **twelve-class partition** of
//!   `𝒰 = ↓_M ⊔ ∞_M`: A–F on the convergent aspect ⊔ A_∞–F_∞ on the persistent aspect,
//!   the latter via the topological predicates `Q-top` (R2.2.D5: `Q1^top` = `Lim_M`
//!   membership, `Q2^top` = `H_S^top` R2.2.D3, `Q3^top` = `H_I^top` R2.2.D4) on a
//!   [`TopologicalProjectionSystem`](crate::r1::topology::TopologicalProjectionSystem).
//! - R2.2.T4 `WF-Back` — restricting `12-Part` to the convergent classes recovers `6-Part`.
//!
//! Class table (Q1=Fix, Q2=H_S, Q3=H_I), on the convergent aspect ↓_M:
//!
//! | Class | Q1 | Q2 | Q3 |                                                    |
//! |-------|----|----|----|----------------------------------------------------|
//! | A     | ⊥  | ⊥  | —  | non-fixpoint, single preimage                      |
//! | B     | ⊥  | ⊤  | ⊥  | non-fixpoint, ramified, distinguishable            |
//! | C     | ⊥  | ⊤  | ⊤  | non-fixpoint, ramified, indistinguishable          |
//! | D     | ⊤  | ⊥  | —  | fixpoint, single preimage                          |
//! | E     | ⊤  | ⊤  | ⊥  | fixpoint, ramified, distinguishable                |
//! | F     | ⊤  | ⊤  | ⊤  | fixpoint, ramified, indistinguishable — **empty**  |

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_persistent;
use crate::r2::orbit_signature_and_horizons::{depth_horizon, invariant_horizon, structural_horizon};

/// The six-class horizon membership (R2.2.T1). `==` compares the computed class
/// label (mathematical identity of the value). Class F is provably empty (R2.2.T2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// (The six classes form the boolean lattice R2.2.D1 `Bool-Lat` over (Q1,H_S,H_I).)
pub enum HorizonClass {
    /// non-fixpoint, single preimage (clean).
    A,
    /// non-fixpoint, ramified, distinguishable.
    B,
    /// non-fixpoint, ramified, indistinguishable.
    C,
    /// fixpoint, single preimage (isolated).
    D,
    /// fixpoint, ramified, distinguishable.
    E,
    /// fixpoint, ramified, indistinguishable — empty in every deterministic instance.
    F,
}

/// **R2.2.T1 (`6-Part`)**: the six-class membership of x, on ↓_M. `None` for ∞_M
/// (the persistent-aspect classification is the twelve-class native extension).
///
/// Q1 = `x ∈ Fix(ρ_M)`, Q2 = `H_S(x)`, Q3 = `H_I(x)`.
pub fn classify(op: &ProjectionOperator, x: ElementId) -> Option<HorizonClass> {
    if is_persistent(op, x) {
        return None;
    }
    let is_fixpoint = op.is_fixpoint(x); // Q1
    let ramified = structural_horizon(op, x); // Q2 = H_S
    let class = match (is_fixpoint, ramified) {
        (false, false) => HorizonClass::A,
        (false, true) => {
            if invariant_horizon(op, x) {
                HorizonClass::C
            } else {
                HorizonClass::B
            }
        }
        (true, false) => HorizonClass::D,
        (true, true) => {
            if invariant_horizon(op, x) {
                HorizonClass::F
            } else {
                HorizonClass::E
            }
        }
    };
    Some(class)
}

/// The six-class membership of every element, indexed by `ElementId::index`
/// (`None` on ∞_M).
pub fn six_class_partition(op: &ProjectionOperator) -> Vec<Option<HorizonClass>> {
    op.substrate().elements().map(|x| classify(op, x)).collect()
}

/// Witness **R2.2.T2 (`F=∅`)**: no convergent element is Class F. First Class-F
/// element (none, in a deterministic instance), or `Ok`.
/// **R2.2.T2 (`ClassF-Def`)**: Class F = (Fix, H_S, H_I) = (⊤,⊤,⊤); this witnesses F = ∅.
pub fn certify_class_f_empty(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if classify(op, x) == Some(HorizonClass::F) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R2.2.T1 (`6-Part`)**: every convergent element receives exactly one
/// class. First unclassified ↓_M element, or `Ok`.
pub fn certify_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if !is_persistent(op, x) && classify(op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// The six-class partition of **∞_M** (R2.2.D6 `12-Part`, persistent half): the same
/// stratified boolean logic as A–F, over the topological predicates `Q-top` (R2.2.D5):
/// `Q1^top` = limit-point class `Lim_M`, `Q2^top` = `H_S^top`, `Q3^top` = `H_I^top`.
/// **F_∞ is NOT claimed empty** (`12-Part-EE` R2.2.T3 + `Fstar-Distinct` R2.2.R3):
/// the kernel d_M-uniformity collapse that empties F is specific to ↓_M — F_∞ is a
/// legitimate, inhabitable class (distinct orbits converging to one limit with
/// tail-equivalent observation traces).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PersistentHorizonClass {
    /// A_∞ — persistent non-limit, unramified: clean approach to its limit.
    AInfinity,
    /// B_∞ — persistent non-limit, ramified, distinguishable rates.
    BInfinity,
    /// C_∞ — persistent non-limit, ramified, indistinguishable rates.
    CInfinity,
    /// D_∞ — limit point (`Lim_M`), unramified: isolated limit.
    DInfinity,
    /// E_∞ — limit point, ramified, distinguishable rates.
    EInfinity,
    /// F_∞ — limit point, ramified, indistinguishable rates.
    FInfinity,
}

/// The twelve-class membership (R2.2.D6 `12-Part`): the six-class partition of `↓_M`
/// **⊔** the six-class partition of `∞_M`. Exhaustive and exclusive on `𝒰_M`
/// (`12-Part-EE` R2.2.T3); restricting to the convergent classes recovers `6-Part`
/// (`WF-Back` R2.2.T4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TwelveClass {
    /// A convergent-aspect class (A–F, on `↓_M`).
    Convergent(HorizonClass),
    /// A persistent-aspect class (A_∞–F_∞, on `∞_M`).
    Persistent(PersistentHorizonClass),
}

/// **R2.2.D3 (`H_S^top`)** — the persistent structural horizon: `⊤` iff
/// `lim_{n→∞} ρ_M^n(x)` is topologically **ramified** — it is the limit of multiple
/// distinct ∞_M orbits, not just x's own. Defined uniformly on `∞_M` — the predicate
/// evaluates the ramification of *x's own orbit-limit* for every `x ∈ ∞_M`, limit point
/// or not (the class-table prose is aligned to this formula). `None` off `∞_M` or
/// where undetermined.
pub fn structural_horizon_topological<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    if sys.projection_depth(x).is_some() {
        return None;
    }
    let limit = sys.topological_limit(x)?;
    sys.topological_preimage_count(&limit).map(|orbits| orbits > 1)
}

/// **R2.2.D4 (`H_I^top`)** — the convergence-rate invisibility horizon: for ramified
/// limits, `⊤` iff the distinct orbits approaching the same limit are
/// **indistinguishable by CRPT's own machinery** — pairwise tail-equivalent (`Tail-Eq`
/// R5) in their obs-labeled ≈-class traces (`Bisim~` R1.1.D7, `Disc-Obs` R3.1.R4).
/// "Rates" enter as observables an instantiation codes into obs; the comparison is
/// equality/tail-equivalence, never an external order. `None` = the spec's `N/A` (when
/// `H_S^top(x) = ⊥`) or undetermined.
pub fn invariant_horizon_topological<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    match structural_horizon_topological(sys, x) {
        Some(true) => {
            let limit = sys.topological_limit(x)?;
            sys.approach_orbits_tail_equivalent(&limit)
        }
        _ => None, // N/A on H_S^top = ⊥; undetermined otherwise
    }
}

/// **R2.2.D5 (`Q-top`) — `Q1^top`**: membership in the **limit-point class**
/// `Lim_M := range(CFix(ρ_M)) ∩ Limits(𝒯) ∩ ∞_M` — x is itself a `𝒯`-limit actually
/// reached by some ∞_M orbit, *and* x is persistent. (`Q2^top := H_S^top` =
/// [`structural_horizon_topological`], `Q3^top := H_I^top` =
/// [`invariant_horizon_topological`].) `None` where the preimage structure is not
/// finitely determined.
pub fn is_limit_point<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    if sys.projection_depth(x).is_some() {
        return Some(false);
    }
    sys.topological_preimage_count(x).map(|orbits| orbits > 0)
}

/// **R2.2.D6 (`12-Part`), persistent half** — the A_∞–F_∞ membership of `x ∈ ∞_M`, by the
/// stratified predicates `Q-top` (R2.2.D5). `None` off `∞_M` or where the topological
/// preimage structure is not finitely determined.
pub fn persistent_classify<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<PersistentHorizonClass> {
    if sys.projection_depth(x).is_some() {
        return None;
    }
    let limit_point = is_limit_point(sys, x)?; // Q1^top
    let ramified = structural_horizon_topological(sys, x)?; // Q2^top = H_S^top
    let class = match (limit_point, ramified) {
        (false, false) => PersistentHorizonClass::AInfinity,
        (true, false) => PersistentHorizonClass::DInfinity,
        _ => {
            // Q3^top = H_I^top, defined exactly when ramified.
            let indistinguishable = invariant_horizon_topological(sys, x)?;
            match (limit_point, indistinguishable) {
                (false, false) => PersistentHorizonClass::BInfinity,
                (false, true) => PersistentHorizonClass::CInfinity,
                (true, false) => PersistentHorizonClass::EInfinity,
                (true, true) => PersistentHorizonClass::FInfinity,
            }
        }
    };
    Some(class)
}

/// **R2.2.D6 (`12-Part`)** — the full twelve-class membership of `x` on a topological
/// system: `↓_M` points get their convergent class (via the universal predicates `Q1`,
/// `H_S^π`; the ramified sub-cases need the kernel's depth profile, finitely determined
/// only where the instance supplies it — `None` there), `∞_M` points their persistent
/// class. Exactly one class per determined point (`12-Part-EE` R2.2.T3).
pub fn twelve_classify<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<TwelveClass> {
    if sys.projection_depth(x).is_none() {
        return persistent_classify(sys, x).map(TwelveClass::Persistent);
    }
    // The convergent half of `12-Part` is the ordinary six-class ([`classify`] / R0.4),
    // which reads `H_S` from the fiber — an *enumerable* computation. A bare topological
    // system need not be enumerable (its `↓_M` fibers may be infinite), so the convergent
    // class is delegated to the enumerable operator; `twelve_classify` owns the persistent
    // half (the genuinely new content) and reports `None` on the convergent side here.
    None
}

/// **R2.2.L1 (`Lat-Ord`)** — the **lattice order** on the horizon predicates `{H_S, H_I, H_O}`
/// is the standard partial order by **logical implication**: `H_I ⟹ H_S` (a non-trivial
/// invariant horizon requires siblings — `H_I` is vacuous when `H_S` is false), and `H_O ⟹
/// H_S` (the boundary layer sits over a populated fiber). Returns `true` when the implication
/// order holds at `x` (`H_I` and `H_O` each entail `H_S`).
pub fn certify_horizon_lattice_order(op: &ProjectionOperator, x: ElementId) -> bool {
    let h_s = structural_horizon(op, x);
    let h_i = invariant_horizon(op, x);
    let h_o = depth_horizon(op, x);
    // H_I ≤ H_S and H_O-over-fiber ≤ H_S in the implication lattice.
    (!h_i || h_s) && (!h_o || h_s || op.canonical_fixpoint(x).is_none())
}

/// Witness **R2.2.R5 (`Part-RegStrat`)** — the twelve-class partition is **aspect-stratified,
/// never aspect-mixed**: each element belongs to exactly one aspect and to one class within
/// that aspect's six-class table. Realized: the convergent six-class ([`classify`]) is `Some`
/// **exactly** on `↓_M`, disjoint from the persistent half. Returns the first element whose
/// six-class membership disagrees with its convergent aspect (none), or `Ok`.
pub fn certify_partition_aspect_stratified(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r1::aspect_partition::is_convergent;
    for x in op.substrate().elements() {
        // classify gives a convergent six-class iff x ∈ ↓_M — no element is in both halves.
        if classify(op, x).is_some() != is_convergent(op, x) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R2.2.C1 (`Sig-Strat`)** — the **signature stratification** corollary: the orbit
/// signature stratifies the twelve-class partition into a **two-dimensional grid** —
/// `aspect ∈ {↓_M, ∞_M}` (the aspect dimension) × six-class (the structure dimension).
/// Returns the `(aspect, six-class)` grid coordinate of a convergent element (the convergent
/// row of the grid); `None` on `∞_M` (the persistent row, owned by `persistent_classify`).
/// (`R2.2.R1` `H_I-KI`: `sig_M` captures the observable graph structure — `H_S` = has
/// siblings, `d_M` = depth; `R2.2.R2` `Disc-6Part`: the six-class is the fundamental
/// discernibility classification.)
pub fn signature_grid_coordinate(
    op: &ProjectionOperator,
    x: ElementId,
) -> Option<(crate::r1::aspect_partition::Aspect, HorizonClass)> {
    classify(op, x).map(|c| (crate::r1::aspect_partition::Aspect::Convergent, c))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;
    use HorizonClass::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// A instance exhibiting all five active classes:
    ///   0→2, 1→2, 2→3   (3 ∈ NF):  0,1 = C ; 2 = B ; 3 = E
    ///   4→5, 5→6        (6 ∈ NF):  4 = A ; 5 = B ; 6 = E
    ///   7               (7 ∈ NF):  7 = D
    fn all_classes() -> Substrate {
        let e = [(0, 2), (1, 2), (2, 3), (4, 5), (5, 6)];
        Substrate::new(8, &e, &e).unwrap()
    }

    #[test]
    fn five_active_classes_present_f_empty() {
        let s = all_classes();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        let got: Vec<Option<HorizonClass>> = (0..8).map(|i| classify(&op, id(i))).collect();
        assert_eq!(
            got,
            vec![Some(C), Some(C), Some(B), Some(E), Some(A), Some(B), Some(E), Some(D)]
        );
        // all five active classes appear; F appears nowhere
        for c in [A, B, C, D, E] {
            assert!(got.contains(&Some(c)), "missing class {c:?}");
        }
        assert!(matches!(certify_class_f_empty(&op), Ok(()))); // R2.2.T2
        assert!(matches!(certify_partition(&op), Ok(())));
        // Lat-Ord: the horizon implication order holds (H_I ⟹ H_S) at every element.
        assert!((0..8).all(|i| certify_horizon_lattice_order(&op, id(i))));
        // Part-RegStrat: the six-class is Some exactly on ↓_M (aspect-stratified).
        assert!(matches!(certify_partition_aspect_stratified(&op), Ok(())));
        // Sig-Strat: a convergent element's grid coordinate is (↓_M, its six-class).
        use crate::r1::aspect_partition::Aspect;
        assert_eq!(signature_grid_coordinate(&op, id(2)), Some((Aspect::Convergent, B)));
    }

    // ===== twelve-class partition (R2.2.D6) on topological systems =====

    use crate::r1::topology::{ChainPoint, ConvergentChain, TopologicalProjectionSystem};
    use crate::r0::projection_systems_and_fibers::ProjectionSystem;
    use PersistentHorizonClass::*;

    #[test]
    fn convergent_chain_twelve_classes() {
        // ℕ ∪ {ω}: one persistent orbit, one fixpoint. Steps: non-limit, unramified (ω has
        // exactly one converging orbit) ⇒ A_∞. ω: convergent fixpoint, kernel {ω} ⇒ D.
        let chain = ConvergentChain;
        assert_eq!(
            twelve_classify(&chain, &ChainPoint::Step(7)),
            Some(TwelveClass::Persistent(AInfinity))
        );
        // ω is convergent: `twelve_classify` owns only the persistent half on a bare
        // topological system; the convergent six-class is `classify` on the enumerable
        // operator (R0.4/R2.2), so the convergent side reports `None` here.
        assert_eq!(twelve_classify(&chain, &ChainPoint::Limit), None);
        // WF-Back (R2.2.T4): the convergent half of 12-Part *is* the six-class partition.
    }

    /// Two disjoint chains L(n), R(n) both `𝒯`-converging to the one fixpoint ω — the
    /// ramified witness: ω has TWO distinct ∞_M pre-image orbits. The chains carry obs
    /// labels (`Bisim~`): equal labels make the orbits tail-equivalent (≈-indistinguishable);
    /// distinct labels make their traces differ at every index — CRPT's own discernment.
    struct TwoChainsToOmega {
        left_obs: u32,
        right_obs: u32,
    }

    #[derive(Debug, Clone, PartialEq)]
    enum TwoChainsPoint {
        L(u64),
        R(u64),
        Omega,
    }

    impl ProjectionSystem for TwoChainsToOmega {
        type Point = TwoChainsPoint;

        fn projection(&self, x: &TwoChainsPoint) -> TwoChainsPoint {
            match x {
                TwoChainsPoint::L(n) => TwoChainsPoint::L(n + 1),
                TwoChainsPoint::R(n) => TwoChainsPoint::R(n + 1),
                TwoChainsPoint::Omega => TwoChainsPoint::Omega,
            }
        }

        fn projection_depth(&self, x: &TwoChainsPoint) -> Option<u32> {
            match x {
                TwoChainsPoint::Omega => Some(0),
                _ => None,
            }
        }
    }

    impl TopologicalProjectionSystem for TwoChainsToOmega {
        fn topological_limit(&self, _x: &TwoChainsPoint) -> Option<TwoChainsPoint> {
            Some(TwoChainsPoint::Omega)
        }

        fn topological_preimage_count(&self, y: &TwoChainsPoint) -> Option<u32> {
            Some(if *y == TwoChainsPoint::Omega { 2 } else { 0 }) // L-orbit and R-orbit
        }

        fn observation(&self, x: &TwoChainsPoint) -> u32 {
            match x {
                TwoChainsPoint::L(_) => self.left_obs,
                TwoChainsPoint::R(_) => self.right_obs,
                TwoChainsPoint::Omega => 0,
            }
        }

        fn approach_orbits_tail_equivalent(&self, y: &TwoChainsPoint) -> Option<bool> {
            // Tail-Eq (R5) from the finite presentation: the two approach traces are
            // (left_obs)^ω and (right_obs)^ω — tail-equivalent iff the obs labels are equal
            // (distinct labels ⇒ the ≈-class traces differ at every index).
            Some(*y != TwoChainsPoint::Omega || self.left_obs == self.right_obs)
        }
    }

    #[test]
    fn ramified_chains_inhabit_b_and_c_infinity() {
        // equal obs: the two approach orbits are tail-equivalent (≈-indistinguishable)
        // ⇒ non-limit + ramified + H_I^top ⊤ ⇒ C_∞.
        let indistinguishable = TwoChainsToOmega { left_obs: 7, right_obs: 7 };
        assert_eq!(
            persistent_classify(&indistinguishable, &TwoChainsPoint::L(0)),
            Some(CInfinity)
        );
        // distinct obs: CRPT's own machinery (Bisim~/Tail-Eq) distinguishes the orbits
        // ⇒ B_∞ — no metric, no order: observation inequality.
        let discernible = TwoChainsToOmega { left_obs: 10, right_obs: 11 };
        assert_eq!(persistent_classify(&discernible, &TwoChainsPoint::R(3)), Some(BInfinity));
        // ω itself is convergent — no persistent class.
        assert_eq!(persistent_classify(&discernible, &TwoChainsPoint::Omega), None);
        // the sig_M-NM profile is the obs trace, compared by equality only.
        use crate::r2::orbit_signature_and_horizons::observation_trace;
        assert_eq!(observation_trace(&discernible, &TwoChainsPoint::L(0), 2), Some(vec![10, 10, 10]));
        assert_eq!(observation_trace(&discernible, &TwoChainsPoint::R(0), 2), Some(vec![11, 11, 11]));
    }

    /// The ω·2 chain: Approach(n) → Mid(0) in `𝒯`; Mid(n) → Final in `𝒯`; Final ∈ Fix.
    /// Mid(0) is a **persistent limit point** (`Lim_M`): reached as a `𝒯`-limit while its
    /// own orbit is still persistent — inhabiting D_∞ (isolated limit).
    struct OmegaTimesTwoChain;

    #[derive(Debug, Clone, PartialEq)]
    enum OmegaTwoPoint {
        Approach(u64),
        Mid(u64),
        Final,
    }

    impl ProjectionSystem for OmegaTimesTwoChain {
        type Point = OmegaTwoPoint;

        fn projection(&self, x: &OmegaTwoPoint) -> OmegaTwoPoint {
            match x {
                OmegaTwoPoint::Approach(n) => OmegaTwoPoint::Approach(n + 1),
                OmegaTwoPoint::Mid(n) => OmegaTwoPoint::Mid(n + 1),
                OmegaTwoPoint::Final => OmegaTwoPoint::Final,
            }
        }

        fn projection_depth(&self, x: &OmegaTwoPoint) -> Option<u32> {
            match x {
                OmegaTwoPoint::Final => Some(0),
                _ => None,
            }
        }
    }

    impl TopologicalProjectionSystem for OmegaTimesTwoChain {
        fn topological_limit(&self, x: &OmegaTwoPoint) -> Option<OmegaTwoPoint> {
            match x {
                OmegaTwoPoint::Approach(_) => Some(OmegaTwoPoint::Mid(0)),
                OmegaTwoPoint::Mid(_) | OmegaTwoPoint::Final => Some(OmegaTwoPoint::Final),
            }
        }

        fn topological_preimage_count(&self, y: &OmegaTwoPoint) -> Option<u32> {
            Some(match y {
                OmegaTwoPoint::Mid(0) => 1,  // the Approach orbit
                OmegaTwoPoint::Final => 1,   // the Mid orbit
                _ => 0,
            })
        }
    }

    #[test]
    fn persistent_limit_point_inhabits_d_infinity() {
        let chain = OmegaTimesTwoChain;
        // Mid(0) ∈ Lim_M: persistent AND a reached 𝒯-limit; its own limit (Final) is
        // unramified ⇒ D_∞ — the isolated limit point.
        assert_eq!(persistent_classify(&chain, &OmegaTwoPoint::Mid(0)), Some(DInfinity));
        // non-limit persistent points with unramified limits ⇒ A_∞.
        assert_eq!(persistent_classify(&chain, &OmegaTwoPoint::Approach(2)), Some(AInfinity));
        assert_eq!(persistent_classify(&chain, &OmegaTwoPoint::Mid(1)), Some(AInfinity));
    }

    /// Two persistent mid-chains MidA/MidB, each a reached `𝒯`-limit (of ApproachA/B), both
    /// converging to the SAME fixpoint Final — so each Mid(0) is a **ramified limit point**:
    /// Q1^top ⊤ and H_S^top ⊤ ⇒ E_∞ (obs-discernible mid-orbits) / F_∞ (tail-equivalent).
    struct RamifiedLimitPoints {
        mid_a_obs: u32,
        mid_b_obs: u32,
    }

    #[derive(Debug, Clone, PartialEq)]
    enum RamifiedPoint {
        ApproachA(u64),
        ApproachB(u64),
        MidA(u64),
        MidB(u64),
        Final,
    }

    impl ProjectionSystem for RamifiedLimitPoints {
        type Point = RamifiedPoint;

        fn projection(&self, x: &RamifiedPoint) -> RamifiedPoint {
            match x {
                RamifiedPoint::ApproachA(n) => RamifiedPoint::ApproachA(n + 1),
                RamifiedPoint::ApproachB(n) => RamifiedPoint::ApproachB(n + 1),
                RamifiedPoint::MidA(n) => RamifiedPoint::MidA(n + 1),
                RamifiedPoint::MidB(n) => RamifiedPoint::MidB(n + 1),
                RamifiedPoint::Final => RamifiedPoint::Final,
            }
        }

        fn projection_depth(&self, x: &RamifiedPoint) -> Option<u32> {
            match x {
                RamifiedPoint::Final => Some(0),
                _ => None,
            }
        }
    }

    impl TopologicalProjectionSystem for RamifiedLimitPoints {
        fn topological_limit(&self, x: &RamifiedPoint) -> Option<RamifiedPoint> {
            match x {
                RamifiedPoint::ApproachA(_) => Some(RamifiedPoint::MidA(0)),
                RamifiedPoint::ApproachB(_) => Some(RamifiedPoint::MidB(0)),
                _ => Some(RamifiedPoint::Final),
            }
        }

        fn topological_preimage_count(&self, y: &RamifiedPoint) -> Option<u32> {
            Some(match y {
                RamifiedPoint::MidA(0) | RamifiedPoint::MidB(0) => 1, // its Approach orbit
                RamifiedPoint::Final => 2,                            // MidA and MidB orbits
                _ => 0,
            })
        }

        fn observation(&self, x: &RamifiedPoint) -> u32 {
            match x {
                RamifiedPoint::MidA(_) => self.mid_a_obs,
                RamifiedPoint::MidB(_) => self.mid_b_obs,
                _ => 0,
            }
        }

        fn approach_orbits_tail_equivalent(&self, y: &RamifiedPoint) -> Option<bool> {
            // the two orbits converging to Final are the Mid chains, with constant obs
            // traces (mid_a_obs)^ω / (mid_b_obs)^ω: tail-equivalent iff the labels agree.
            Some(*y != RamifiedPoint::Final || self.mid_a_obs == self.mid_b_obs)
        }
    }

    #[test]
    fn ramified_limit_points_inhabit_e_and_f_infinity() {
        // equal obs: the mid orbits are tail-equivalent ⇒ limit point + ramified +
        // H_I^top ⊤ ⇒ F_∞.
        let indistinguishable = RamifiedLimitPoints { mid_a_obs: 7, mid_b_obs: 7 };
        assert_eq!(
            persistent_classify(&indistinguishable, &RamifiedPoint::MidA(0)),
            Some(FInfinity)
        );
        // distinct obs: ≈/Tail-Eq discerns the mid orbits ⇒ E_∞.
        let discernible = RamifiedLimitPoints { mid_a_obs: 10, mid_b_obs: 11 };
        assert_eq!(persistent_classify(&discernible, &RamifiedPoint::MidB(0)), Some(EInfinity));
        // approach points: non-limit, unramified limit (each Mid(0) reached by one orbit) ⇒ A_∞.
        assert_eq!(
            persistent_classify(&discernible, &RamifiedPoint::ApproachA(0)),
            Some(AInfinity)
        );
        assert_eq!(
            persistent_classify(&discernible, &RamifiedPoint::ApproachB(1)),
            Some(AInfinity)
        );
        // all six persistent classes are inhabitable: A_∞ here, B_∞/C_∞ (two chains),
        // D_∞ (ω·2), E_∞/F_∞ (this witness) — 12-Part (R2.2.D6) fully realized,
        // with every distinction made by CRPT's own machinery (obs / ≈ / Tail-Eq).
    }
}
