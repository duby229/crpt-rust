//! # L3.2 — Six-Class and Twelve-Class Horizon Partitions
//!
//! Exact realization of spec section **L3.2** (`CRPT_OMEGA_TOWER_L3.md`, rc3):
//!
//! - L3.2.D2 `Bool-Pred` — the predicates Q1 (Fix membership), Q2 (H_S), Q3 (H_I).
//! - L3.2.T1 `6-Part` — the six-class partition of ↓_M into A–F.
//! - L3.2.T2 `F=∅` — Class F is empty in every deterministic CRPT model.
//! - L3.2.D6 `12-Part` + L3.2.T3 `12-Part-EE` — the **twelve-class partition** of
//!   `𝒰 = ↓_M ⊔ ∞_M`: A–F on the convergent regime ⊔ A_∞–F_∞ on the persistent regime,
//!   the latter via the topological predicates `Q-top` (L3.2.D5: `Q1^top` = `Lim_M`
//!   membership, `Q2^top` = `H_S^top` L3.2.D3, `Q3^top` = `H_I^top` L3.2.D4) on a
//!   [`TopologicalProjectionSystem`](crate::l1::topology::TopologicalProjectionSystem).
//! - L3.2.T4 `WF-Back` — restricting `12-Part` to the convergent classes recovers `6-Part`.
//!
//! Class table (Q1=Fix, Q2=H_S, Q3=H_I), on the convergent regime ↓_M:
//!
//! | Class | Q1 | Q2 | Q3 |                                                    |
//! |-------|----|----|----|----------------------------------------------------|
//! | A     | ⊥  | ⊥  | —  | non-fixpoint, single preimage                      |
//! | B     | ⊥  | ⊤  | ⊥  | non-fixpoint, ramified, distinguishable            |
//! | C     | ⊥  | ⊤  | ⊤  | non-fixpoint, ramified, indistinguishable          |
//! | D     | ⊤  | ⊥  | —  | fixpoint, single preimage                          |
//! | E     | ⊤  | ⊤  | ⊥  | fixpoint, ramified, distinguishable                |
//! | F     | ⊤  | ⊤  | ⊤  | fixpoint, ramified, indistinguishable — **empty**  |

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::is_persistent;
use crate::l3::horizon::{invariant_horizon, structural_horizon};

/// The six-class horizon membership (L3.2.T1). `==` compares the computed class
/// label (mathematical identity of the value). Class F is provably empty (L3.2.T2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// (The six classes form the boolean lattice L3.2.D1 `Bool-Lat` over (Q1,H_S,H_I).)
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
    /// fixpoint, ramified, indistinguishable — empty in every deterministic model.
    F,
}

/// **L3.2.T1 (`6-Part`)**: the six-class membership of x, on ↓_M. `None` for ∞_M
/// (the persistent-regime classification is the twelve-class native extension).
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

/// Witness **L3.2.T2 (`F=∅`)**: no convergent element is Class F. First Class-F
/// element (none, in a deterministic model), or `Ok`.
/// **L4.8.D1 (`ClassF-Def`)**: Class F = (Fix, H_S, H_I) = (⊤,⊤,⊤); this witnesses F = ∅.
pub fn certify_class_f_empty(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if classify(op, x) == Some(HorizonClass::F) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **L3.2.T1 (`6-Part`)**: every convergent element receives exactly one
/// class. First unclassified ↓_M element, or `Ok`.
pub fn certify_partition(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if !is_persistent(op, x) && classify(op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// The six-class partition of **∞_M** (L3.2.D6 `12-Part`, persistent half): the same
/// stratified boolean logic as A–F, over the topological predicates `Q-top` (L3.2.D5):
/// `Q1^top` = limit-point class `Lim_M`, `Q2^top` = `H_S^top`, `Q3^top` = `H_I^top`.
/// **F_∞ is NOT claimed empty** (rc4, `12-Part-EE` L3.2.T3 + `Fstar-Distinct` L3.2.R3):
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

/// The twelve-class membership (L3.2.D6 `12-Part`): the six-class partition of `↓_M`
/// **⊔** the six-class partition of `∞_M`. Exhaustive and exclusive on `𝒰_M`
/// (`12-Part-EE` L3.2.T3); restricting to the convergent classes recovers `6-Part`
/// (`WF-Back` L3.2.T4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TwelveClass {
    /// A convergent-regime class (A–F, on `↓_M`).
    Convergent(HorizonClass),
    /// A persistent-regime class (A_∞–F_∞, on `∞_M`).
    Persistent(PersistentHorizonClass),
}

/// **L3.2.D3 (`H_S^top`)** — the persistent structural horizon: `⊤` iff
/// `lim_{n→∞} ρ_M^n(x)` is topologically **ramified** — it is the limit of multiple
/// distinct ∞_M orbits, not just x's own. Defined uniformly on `∞_M` — the predicate
/// evaluates the ramification of *x's own orbit-limit* for every `x ∈ ∞_M`, limit point
/// or not (rc4: the class-table prose is aligned to this formula). `None` off `∞_M` or
/// where undetermined.
pub fn structural_horizon_topological<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    if !sys.is_persistent(x) {
        return None;
    }
    let limit = sys.topological_limit(x)?;
    sys.topological_preimage_count(&limit).map(|orbits| orbits > 1)
}

/// **L3.2.D4 (`H_I^top`)** — the convergence-rate invisibility horizon: for ramified
/// limits, `⊤` iff the distinct orbits approaching the same limit are
/// **indistinguishable by CRPT's own machinery** — pairwise tail-equivalent (`Tail-Eq`
/// L6.3.D2) in their obs-labeled ≈-class traces (`Bisim~` L1.1.D7, `Disc-Obs` L4.1.R4).
/// "Rates" enter as observables an instantiation codes into obs; the comparison is
/// equality/tail-equivalence, never an external order. `None` = the spec's `N/A` (when
/// `H_S^top(x) = ⊥`) or undetermined.
pub fn invariant_horizon_topological<T: crate::l1::topology::TopologicalProjectionSystem>(
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

/// **L3.2.D5 (`Q-top`) — `Q1^top`**: membership in the **limit-point class**
/// `Lim_M := range(CFix(ρ_M)) ∩ Limits(𝒯) ∩ ∞_M` — x is itself a `𝒯`-limit actually
/// reached by some ∞_M orbit, *and* x is persistent. (`Q2^top := H_S^top` =
/// [`structural_horizon_topological`], `Q3^top := H_I^top` =
/// [`invariant_horizon_topological`].) `None` where the preimage structure is not
/// finitely determined.
pub fn is_limit_point<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<bool> {
    if !sys.is_persistent(x) {
        return Some(false);
    }
    sys.topological_preimage_count(x).map(|orbits| orbits > 0)
}

/// **L3.2.D6 (`12-Part`), persistent half** — the A_∞–F_∞ membership of `x ∈ ∞_M`, by the
/// stratified predicates `Q-top` (L3.2.D5). `None` off `∞_M` or where the topological
/// preimage structure is not finitely determined.
pub fn persistent_classify<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<PersistentHorizonClass> {
    if !sys.is_persistent(x) {
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

/// **L3.2.D6 (`12-Part`)** — the full twelve-class membership of `x` on a topological
/// system: `↓_M` points get their convergent class (via the universal predicates `Q1`,
/// `H_S^π`; the ramified sub-cases need the kernel's depth profile, finitely determined
/// only where the instance supplies it — `None` there), `∞_M` points their persistent
/// class. Exactly one class per determined point (`12-Part-EE` L3.2.T3).
pub fn twelve_classify<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<TwelveClass> {
    if sys.is_persistent(x) {
        return persistent_classify(sys, x).map(TwelveClass::Persistent);
    }
    let fixpoint = sys.is_projection_fixpoint(x); // Q1
    let ramified = sys.structural_horizon(x)?; // Q2 = H_S^π
    let class = match (fixpoint, ramified) {
        (false, false) => HorizonClass::A,
        (true, false) => HorizonClass::D,
        // the B/C and E/F splits read H_I^π (kernel depth-uniformity), which needs the
        // kernel elements — finitely determined only on listing-capable instances.
        _ => return None,
    };
    Some(TwelveClass::Convergent(class))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l2::projection::Model;
    use crate::l1::substrate::Substrate;
    use HorizonClass::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// A model exhibiting all five active classes:
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
        let m = Model::from_functional_reduction(s).unwrap(); let op = m.operator();
        let got: Vec<Option<HorizonClass>> = (0..8).map(|i| classify(&op, id(i))).collect();
        assert_eq!(
            got,
            vec![Some(C), Some(C), Some(B), Some(E), Some(A), Some(B), Some(E), Some(D)]
        );
        // all five active classes appear; F appears nowhere
        for c in [A, B, C, D, E] {
            assert!(got.contains(&Some(c)), "missing class {c:?}");
        }
        assert!(matches!(certify_class_f_empty(&op), Ok(()))); // L3.2.T2
        assert!(matches!(certify_partition(&op), Ok(())));
    }

    // ===== twelve-class partition (L3.2.D6) on topological systems =====

    use crate::l1::topology::{ChainPoint, ConvergentChain, TopologicalProjectionSystem};
    use crate::l0::projection_system::ProjectionSystem;
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
        assert_eq!(
            twelve_classify(&chain, &ChainPoint::Limit),
            Some(TwelveClass::Convergent(HorizonClass::D))
        );
        // WF-Back (L3.2.T4): the convergent side of 12-Part is the six-class partition.
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
            // Tail-Eq (L6.3.D2) from the finite presentation: the two approach traces are
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
        use crate::l3::horizon::observation_trace;
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
        // D_∞ (ω·2), E_∞/F_∞ (this witness) — 12-Part (L3.2.D6) fully realized,
        // with every distinction made by CRPT's own machinery (obs / ≈ / Tail-Eq).
    }
}
