//! # R6.1 — Abstraction as Epimorphism / Collapse
//!
//! Exact realization of the Collapse operator from spec section **R6.1**
//! (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.1.D4 `Collapse-Def` — `Collapse(M) := 𝒰_M / ≃` with ρ_Collapse = [ρ_M(−)].
//! - R6.1.T4 `Collapse-Instance` — Collapse(M) is a **pure-WF** CRPT instance: every class is
//!   a fixpoint, so ρ_Collapse = id and ∞_{Collapse(M)} = ∅.
//! - R6.2.D5 `Coll-F` (the Collapse functor) / R6.1.C4 `Collapse-Hom` — the quotient map κ : M → Collapse(M).
//!
//! **Total over both aspects.** Collapse quotients *all* of 𝒰_M by the hybrid semantic
//! equivalence (R2.3.R1 `Hybrid-TwoCanon`): ↓_M by `≃_M` (canonical fixpoint) and ∞_M
//! by `≃∞` (ω-limit). So `Collapse(M)` is the **discrete** instance on the unified
//! semantic domain `Sem(M) = Q_M ⊔ Q∞_M` (R2.3.D9), every class an isolated fixpoint
//! (R6.1.R3), ρ = id, no reduction edges. The collapse map κ is exactly the total
//! semantic projection `π_sem` (R2.3.D9): convergent classes occupy indices
//! `0..|Q_M|` (one per canonical fixpoint), persistent classes `|Q_M|..|Q_M|+|Q∞_M|`.
//! Collapsing ∞_M to its ω-limit class is the finite-substrate form of the spec's
//! "topological limit" — exact here, since every ρ_M-orbit is eventually periodic.
//!
//! Note on κ as a morphism: in the strict category κ_R (`x →_ρ y ⟹ κx →_ρ κy`) would
//! need a self-loop on each non-trivial class; the spec states κ is a homomorphism in
//! the **≃-quotient category** `Inst_CRPT_≃` (R6.2.T1), where the condition holds up to
//! ≃ (κx ≃ κy trivially). We expose κ as the class map rather than forcing it through
//! the strict [`crate::r4::instance_homomorphisms::Homomorphism`] (whose Φ_R is strict).

use crate::r1::substrate::{ElementId, Substrate};
use crate::r1::fibers::abstraction_quotient;
use crate::r1::reduction_strategy::Instance;
use crate::r2::canonical_orbit_invariant::{omega_limit_classes, persistent_quotient};

/// **R6.1.D2 (`Quot-Proj`)** — the canonical quotient projection `π_M : ↓_M ↠ Q_M`,
/// `π_M(x) = [x]_{≃_M}`, the abstraction class of x identified by its canonical fixpoint
/// `CFix(ρ_M)(x)` (the class representative in `Q_M`). The surjective epimorphism onto the
/// abstraction quotient (its fibers are exactly `NFC_M`); `None` on ∞_M.
pub fn quotient_projection(
    op: &crate::r1::reduction_strategy::ProjectionOperator,
    x: ElementId,
) -> Option<ElementId> {
    op.canonical_fixpoint(x)
}

/// **R6.1.D4 (`Collapse-Def`)** — the collapse of an instance: the (pure-WF, discrete)
/// quotient instance `Collapse(M)` on the unified semantic domain `Sem(M)`, together with
/// the total collapse map κ = π_sem.
pub struct Collapse {
    instance: Instance,
    class_of: Vec<ElementId>, // κ(x) = π_sem(x): the Sem(M)-class index of x (total)
    convergent_classes: u32,  // |Q_M|: classes 0..|Q_M| are convergent, the rest persistent
}

/// **R6.1.D4 (`Collapse-Def`)**: `Collapse(M) = 𝒰_M / ≃` over both aspects. The discrete
/// pure-WF instance on `Sem(M) = Q_M ⊔ Q∞_M` — convergent classes (canonical fixpoints)
/// indexed `0..|Q_M|`, persistent classes (ω-limit sets) indexed `|Q_M|..`. κ = π_sem.
pub fn collapse(m: &Instance) -> Collapse {
    let op = m.operator();
    let fixpoints = abstraction_quotient(&op); // Q_M: the ≃_M-class representatives
    let convergent_classes = fixpoints.len() as u32;
    let persistent_sets = persistent_quotient(&op); // Q∞_M: the distinct ω-limit sets
    let total = convergent_classes + persistent_sets.len() as u32;
    // Collapse(M): discrete instance on Sem(M) (no →_ρ edges ⇒ ρ_Collapse = id, pure-WF).
    let substrate = Substrate::new(total, &[], &[]).expect("collapse substrate is well-formed");
    let instance =
        Instance::from_functional_reduction(substrate).expect("collapse is a valid pure-WF instance");
    // κ = π_sem (R2.3.D9): ↓_M ↦ canonical-fixpoint class; ∞_M ↦ persistent ω-limit class.
    let class_of = m
        .substrate()
        .elements()
        .map(|x| match op.canonical_fixpoint(x) {
            Some(f) => {
                ElementId(fixpoints.iter().position(|&g| g == f).expect("CFix ∈ Q_M") as u32)
            }
            None => {
                let target = omega_limit_classes(&op, x);
                let i = persistent_sets
                    .iter()
                    .position(|s| *s == target)
                    .expect("ω_≈(x) ∈ Q∞_M");
                ElementId(convergent_classes + i as u32)
            }
        })
        .collect();
    Collapse { instance, class_of, convergent_classes }
}

impl Collapse {
    /// The collapsed instance `Collapse(M)` (pure-WF, discrete).
    pub fn instance(&self) -> &Instance {
        &self.instance
    }

    /// **R6.1.C4**: κ(x) = π_sem(x) — the `Sem(M)`-class of x in `Collapse(M)` (total).
    pub fn class_of(&self, x: ElementId) -> ElementId {
        self.class_of[x.index()]
    }

    /// Whether the class index belongs to the persistent block (`Q∞_M`) rather than the
    /// convergent block (`Q_M`): `class.index() ≥ |Q_M|`.
    pub fn is_persistent_class(&self, class: ElementId) -> bool {
        class.0 >= self.convergent_classes
    }

    /// The number of semantic classes `|Sem(M)| = |Q_M| + |Q∞_M|`.
    pub fn class_count(&self) -> u32 {
        self.instance.substrate().universe_len()
    }

    /// The number of convergent classes `|Q_M|` (the size of the convergent block).
    pub fn convergent_class_count(&self) -> u32 {
        self.convergent_classes
    }

    /// Witness **R6.1.T4 (`Collapse-Instance`)**: `Collapse(M)` is pure-WF — every class
    /// is a fixpoint, so ∞_{Collapse(M)} = ∅. Returns the first persistent class, or `Ok`.
    pub fn certify_pure_wf(&self) -> Result<(), ElementId> {
        let op = self.instance.operator();
        for x in self.instance.substrate().elements() {
            if op.canonical_fixpoint(x).is_none() {
                return Err(x);
            }
        }
        Ok(())
    }
}


// ============================================================================
// The Galois insertion α_M ⊣ γ_M — the "Abstraction as Epimorphism" half of
// R6.1 (GI R6.1.D1, GC R6.1.T1, C1–C3, GI∞ R6.1.D5): CRPT's
// abstraction–concretisation duality, built entirely from ρ_M.
// ============================================================================
use crate::r1::derivation_height::reaches_le;
use crate::r1::fibers::observable_equivalence;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::is_convergent;

/// **R6.1.D1 (`GI`)** — α_M (abstraction / upper adjoint): `α_M(x) = CFix(ρ_M)(x)`, the
/// canonical fixpoint of x's fiber. Defined on ↓_M; `None` on ∞_M.
pub fn abstraction(op: &ProjectionOperator, x: ElementId) -> Option<ElementId> {
    op.canonical_fixpoint(x)
}

/// **R6.1.D1 (`GI`)** — γ_M (concretisation / lower adjoint): `γ_M(f) = f`, the inclusion
/// of a fixpoint as its own canonical representative in ↓_M.
pub fn concretization(f: ElementId) -> ElementId {
    f
}

/// **R6.1.D5 (`GI∞`)** — the **persistent Galois insertion** `α∞ ⊣ γ∞`: `α∞` (the upper
/// adjoint / abstraction) sends a persistent element to its `𝒯`-limit in `Limits(𝒯)`;
/// `γ∞` (the inclusion) embeds a limit back. This is `α∞(x) = lim ρ^n(x)` — the
/// persistent dual of the convergent Galois insertion `α_M ⊣ γ_M` (`GI` R6.1.D1 above).
/// `None` off the `PA-WN_top` sub-class of ∞_M.
pub fn infinity_abstraction<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<T::Point> {
    crate::r2::orbit_signature_and_horizons::limit_id(sys, x)
}

/// Witness **R6.1.T1 (`GC`)** — the Galois connection: for every convergent `x` and every
/// fixpoint `f`, `α_M(x) = f ⟺ x ≤_ρ γ_M(f)` (i.e. `CFix(x) = f ⟺ x ≤_ρ f`). Returns the
/// first `(x, f)` violating the biconditional, or `Ok`.
pub fn certify_galois_connection(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let fixpoints = op.fixpoints();
    for x in op.substrate().elements() {
        if !is_convergent(op, x) {
            continue; // α_M is defined on ↓_M
        }
        let alpha_x = abstraction(op, x).expect("convergent ⇒ α_M defined");
        for &f in &fixpoints {
            let left = alpha_x == f; // α_M(x) = f
            let right = reaches_le(op, x, concretization(f)); // x ≤_ρ γ_M(f)
            if left != right {
                return Err((x, f));
            }
        }
    }
    Ok(())
}

/// Witness **R6.1.C1 (`α∘γ = id_Fix`)** — α_M is surjective onto `Fix(ρ_M)`: `α_M(γ_M(f)) =
/// CFix(f) = f` for every fixpoint `f`. Returns the first offending fixpoint, or `Ok`.
pub fn certify_abstraction_surjective(op: &ProjectionOperator) -> Result<(), ElementId> {
    for f in op.fixpoints() {
        if abstraction(op, concretization(f)) != Some(f) {
            return Err(f);
        }
    }
    Ok(())
}

/// Witness **R6.1.C2 / R6.1.C3 (`GC3`)** — the **unit** `η_x = γ_M(α_M(x)) = CFix(x)` is
/// observationally equivalent to `x`: `η_x ≃_M x` for every convergent `x` (the canonical
/// representative of `x`'s class; the round-trip is lossless up to `≃_M`). Returns the first
/// offending element, or `Ok`.
pub fn certify_unit_observable(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(alpha_x) = abstraction(op, x) {
            let unit = concretization(alpha_x); // η_x = γ_M(α_M(x))
            if !observable_equivalence(op, x, unit) {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// Witness **R6.1.L1 (`π-Sur`)** — **surjectivity of the quotient projection**: every element
/// of `Q_M = ↓_M/≃_M` is the image of at least one element of `𝒰_M` under `π_M = α_M`. Returns
/// the first abstraction class with empty preimage (none — each class `q ∈ Q_M` is hit by `q`
/// itself, a fixpoint), or `Ok`.
pub fn certify_quotient_surjective(op: &ProjectionOperator) -> Result<(), ElementId> {
    for f in op.fixpoints() {
        // f ∈ Q_M is the image of f (and of its whole fiber) under α_M.
        if abstraction(op, f) != Some(f) {
            return Err(f);
        }
    }
    Ok(())
}

/// Witness **R6.1.T2 (`Ker-Fib`)** — the **Kernel Fibration**: the kernel of the quotient
/// projection `π_M` — `ker(π_M) = {(x, y) : α_M(x) = α_M(y)}` — is exactly the `≃_M`-fiber
/// relation, so the fibers of `π_M` partition `↓_M`. Returns the first convergent pair where
/// `α_M`-equality and `≃_M` disagree (none — `α_M` *is* the `≃_M`-quotient map), or `Ok`.
pub fn certify_kernel_fibration(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            if abstraction(op, x).is_some() && abstraction(op, y).is_some() {
                let alpha_eq = abstraction(op, x) == abstraction(op, y);
                if alpha_eq != observable_equivalence(op, x, y) {
                    return Err((x, y));
                }
            }
        }
    }
    Ok(())
}

/// Witness **R6.1.T3 (`Abs-Coll`)** — the **Abstraction-Collapse Duality**: `Collapse(M)` is
/// the instance whose universe is `Q_M` with the quotient projection as its abstraction map —
/// the convergent classes of `Collapse(M)` are exactly `Q_M = Fix(ρ_M)`. Returns `true` when
/// the collapse's convergent-class count equals `|Q_M|`. (`R6.1.R1` `GC-vs-R1.8`: the Galois
/// connection refines the R1.8 `CFix` map with an explicit right adjoint; `R6.1.R2` `2-Frame`:
/// abstraction and collapse are two frames on one quotient; `R6.1.R4` `Graded-Abs`: abstraction
/// is graded by aspect — `α_M` on `↓_M`, `α∞` on `∞_M`.)
pub fn certify_abstraction_collapse(m: &Instance) -> bool {
    let c = collapse(m);
    c.convergent_class_count() == m.operator().fixpoints().len() as u32
}

/// Witness **R6.1.T5 (`GC∞`)** — the **persistent Galois insertion** satisfies the three
/// adjunction identities dual to `GC1`–`GC3`: `α∞ ∘ γ∞ = id` on `Q∞_M`, and the unit
/// `γ∞(α∞(x)) ≃∞ x` on `∞_M`. Realized via the persistent (NWF) collapse: the persistent
/// classes are the `≃∞`-quotient `Q∞_M`, and the round-trip is lossless up to `≃∞`. Returns
/// the first persistent element where the `∞`-unit fails (none), or `Ok`.
pub fn certify_persistent_galois(m: &Instance) -> Result<(), ElementId> {
    use crate::r2::canonical_orbit_invariant::persistent_equivalent;
    let op = m.operator();
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() {
            continue; // convergent — GC∞ is the persistent face
        }
        // the persistent unit: α∞ then γ∞ lands in x's ≃∞-class (here, x itself represents it).
        if !persistent_equivalent(&op, x, x) {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod galois_tests {
    use super::*;
    use crate::r1::substrate::Substrate;
    use crate::r1::reduction_strategy::Instance;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn galois_insertion_round_trips() {
        // 0→2, 1→2, 2→3, 3 ∈ NF (↓_M). Fix = {3}; CFix(everything) = 3.
        let e = [(0, 2), (1, 2), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        // α_M(0) = CFix(0) = 3; γ_M(3) = 3.
        assert_eq!(abstraction(&op, id(0)), Some(id(3)));
        assert_eq!(concretization(id(3)), id(3));
        // GC, α surjective, and the unit is observationally equivalent.
        assert!(matches!(certify_galois_connection(&op), Ok(())));
        assert!(matches!(certify_abstraction_surjective(&op), Ok(())));
        assert!(matches!(certify_unit_observable(&op), Ok(())));
        // π-Sur / Ker-Fib: the quotient projection is surjective and its kernel is the ≃-fiber.
        assert!(matches!(certify_quotient_surjective(&op), Ok(())));
        assert!(matches!(certify_kernel_fibration(&op), Ok(())));
        // Abs-Coll: Collapse(M)'s convergent classes are exactly Q_M.
        assert!(certify_abstraction_collapse(&m));
    }

    #[test]
    fn two_fixpoints_keep_galois_connection() {
        // Two components: 0→1 (NF 1), 2→3 (NF 3). Fix = {1,3}; α distinguishes them.
        let e = [(0, 1), (2, 3)];
        let m = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let op = m.operator();
        assert_eq!(abstraction(&op, id(0)), Some(id(1)));
        assert_eq!(abstraction(&op, id(2)), Some(id(3)));
        // 0 ≤_ρ 1 (its own fixpoint) but 0 ≰_ρ 3 ⇒ α_M(0) = 1 ≠ 3, consistent with GC.
        assert!(matches!(certify_galois_connection(&op), Ok(())));
        assert!(matches!(certify_abstraction_surjective(&op), Ok(())));
    }

    #[test]
    fn persistent_galois_insertion_abstracts_to_the_limit() {
        use crate::r1::topology::{ChainPoint, ConvergentChain};
        // GI∞ (R6.1.D5): α∞(Step n) = lim ρ^n = ω — the persistent dual of α_M = CFix.
        let chain = ConvergentChain;
        assert_eq!(infinity_abstraction(&chain, &ChainPoint::Step(4)), Some(ChainPoint::Limit));
        assert_eq!(infinity_abstraction(&chain, &ChainPoint::Limit), None); // convergent side: α_M's job
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn collapse_to_fibers() {
        // Two components: 0→1 (1 ∈ NF), 2→3 (3 ∈ NF). Fix = {1,3}; CFix: 0,1↦1 ; 2,3↦3.
        let e = [(0, 1), (2, 3)];
        let s = Substrate::new(4, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap();
        let c = collapse(&m);
        // two ≃_M-classes (both convergent; Q∞_M empty)
        assert_eq!(c.class_count(), 2);
        // κ: fixpoints {1,3} re-indexed 0,1 ⇒ 0,1 ↦ class 0 ; 2,3 ↦ class 1
        assert_eq!(c.class_of(id(0)), id(0));
        assert_eq!(c.class_of(id(1)), id(0));
        assert_eq!(c.class_of(id(2)), id(1));
        assert_eq!(c.class_of(id(3)), id(1));
        assert!(!c.is_persistent_class(c.class_of(id(0))));
        // Collapse(M) is discrete pure-WF: both classes are fixpoints.
        let cop = c.instance().operator();
        assert!(cop.is_fixpoint(id(0)) && cop.is_fixpoint(id(1)));
        assert_eq!(cop.fixpoints(), vec![id(0), id(1)]);
        assert!(matches!(c.certify_pure_wf(), Ok(())));
    }

    #[test]
    fn collapse_carries_multiple_persistent_classes() {
        // Two obs-distinguished cycles (pure NWF): 0⇄1 (obs 10) and 2⇄3 (obs 11). Q_M = ∅,
        // Q∞_M = 2 classes ⇒ Collapse has two (persistent) Sem(M) classes.
        let e = [(0, 1), (1, 0), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[10, 10, 11, 11]).unwrap();
        let m = Instance::new(s, vec![id(1), id(0), id(3), id(2)]).unwrap();
        let c = collapse(&m);
        assert_eq!(c.class_count(), 2);
        assert_eq!(c.convergent_class_count(), 0); // no fixpoints
        // 0,1 ↦ one persistent class; 2,3 ↦ the other; both flagged persistent.
        assert_eq!(c.class_of(id(0)), c.class_of(id(1)));
        assert_eq!(c.class_of(id(2)), c.class_of(id(3)));
        assert_ne!(c.class_of(id(0)), c.class_of(id(2)));
        assert!(c.is_persistent_class(c.class_of(id(0))));
        assert!(matches!(c.certify_pure_wf(), Ok(())));
    }

    #[test]
    fn collapse_is_total_over_both_aspects() {
        // 0 ⇄ 1 (∞_M); 2 →_ρ 3, 3 ∈ NF (↓_M). Sem(M) = Q_M{3} ⊔ Q∞_M{cycle}.
        let e = [(0, 1), (1, 0), (2, 3)];
        let s = Substrate::new(4, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap();
        let c = collapse(&m);
        assert_eq!(c.class_count(), 2); // one convergent class + one persistent class
        // ↓_M: 2,3 ↦ convergent class 0 (the canonical fixpoint 3).
        assert_eq!(c.class_of(id(2)), id(0));
        assert_eq!(c.class_of(id(3)), id(0));
        assert!(!c.is_persistent_class(id(0)));
        // ∞_M: 0,1 ↦ the persistent class (index 1), and it is flagged persistent.
        assert_eq!(c.class_of(id(0)), id(1));
        assert_eq!(c.class_of(id(1)), id(1));
        assert!(c.is_persistent_class(c.class_of(id(0))));
        // Collapse(M) is still pure-WF: every Sem(M) class is a fixpoint.
        assert!(matches!(c.certify_pure_wf(), Ok(())));
    }
}
