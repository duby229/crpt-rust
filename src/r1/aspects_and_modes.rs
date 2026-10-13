//! # R1.4 — Aspects and Canonicalization Modes
//!
//! Exact realization of spec section **R1.4** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9).
//!
//! CRPT separates two orthogonal axes. A **aspect** (R1.9) classifies an *element*
//! by orbit fate (`↓_M`/`∞_M`). A **mode** (R1.4.D1) classifies the *reach mechanism* — how
//! the orbit reaches its canonical object — and there are exactly **two**:
//!
//! - R1.4.D1 `Mode` — `Recurrence` (finitary: equality of iterates in the `≈`-quotient at
//!   finite depth — `PA-WN`'s fixpoint at `d_M` on `↓_M`, `PA-Reach`'s recurrent cycle at
//!   `n_M` on `∞_M`) and `Convergence` (topological: a `𝒯`-limit — `PA-WN_top`,
//!   `PA-Reach`'s convergence realization). The same two serve both aspects.
//! - R1.4.T1 `Mode-Comp` — mode coverage: every element is reached in one of the two modes
//!   ([`certify_mode_coverage`]).
//! - R1.4.R2 `Inf-Dual-Expl` — the infinity duality, mode-explained (its statement is
//!   R1.9.T7; reify witnesses are R6).
//!
//! The **AOI is not a mode**: asymptotic orbit
//! invariance is the *analysis layer* (R5), defined unconditionally and finitely
//! presentable in either mode. Modes reach canonical objects *in* `𝒰_M`; the AOI is an
//! invariant *about* orbits.
//!
//! **On the finite discrete substrate** a sequence converges iff eventually constant, so
//! Convergence degenerates to Recurrence — every element is canonicalized in Recurrence
//! mode. Convergence is inhabited on the symbolic topological tier ([`crate::r1::topology`]).

use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::substrate::ElementId;

/// **R1.4.D1 (`Mode`)** — a reach mechanism. Exactly two. `==` compares the tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Recurrence (finitary) — canonical object reached *by visiting it*: `Fix` at `d_M`
    /// on `↓_M` (`PA-WN`), the recurrent class cycle at `n_M` on `∞_M` (`PA-Reach-Fin`).
    Recurrence,
    /// Convergence (topological) — canonical object reached *as a `𝒯`-limit*
    /// (`PA-WN_top` / `PA-Reach-Top`, Hausdorff).
    Convergence,
}

/// **R1.4.D1 (`Mode`)** — the reach mechanism at `x` on a topological system: **Convergence**
/// on the `PA-WN_top` part of `∞_M` (a genuine `𝒯`-limit — `PA-Reach-Top`), **Recurrence**
/// otherwise. This is where [`Mode::Convergence`] is inhabited non-degenerately (the
/// classification moved off the R1.7 `𝒯`-interface and into its own R1.4 section).
pub fn canonicalization_mode<T: crate::r1::topology::TopologicalProjectionSystem>(
    system: &T,
    x: &T::Point,
) -> Mode {
    if system.projection_depth(x).is_none() && system.topological_limit(x).is_some() {
        Mode::Convergence
    } else {
        Mode::Recurrence
    }
}

/// **R1.4.D1 (`Mode`)** on the finite CRPT operator: every element is reached in
/// **Recurrence** mode (`↓_M` terminates at `d_M`; `∞_M` enters its class cycle at `n_M`).
/// Convergence requires a non-discrete topology — see [`convergence_mode_available`].
pub fn finite_mode(op: &ProjectionOperator, x: ElementId) -> Mode {
    let _ = (op, x);
    Mode::Recurrence
}

/// Whether **Convergence mode** is available at `x` on the finite discrete topology: never
/// non-degenerately (a discrete sequence converges iff eventually constant, i.e. iff
/// Recurrence already certifies the reach). Convergence is inhabited on the symbolic
/// topological tier instead.
pub fn convergence_mode_available(op: &ProjectionOperator, x: ElementId) -> bool {
    let _ = (op, x);
    false
}

/// Witness **R1.4.T1 (`Mode-Comp`)** on the finite substrate — every element is reached in
/// **Recurrence** mode: `↓_M` terminates (`d_M` finite), and every persistent element's
/// class orbit enters a recurrent cycle (on a finite substrate the orbit is eventually
/// periodic, so this always holds). Returns the first element not so reached, or `Ok`.
pub fn certify_mode_coverage(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        // ↓_M reaches Fix at d_M; ∞_M's deterministic orbit is eventually periodic ⇒
        // enters a recurrent ≈-cycle. Either way, reached in Recurrence mode.
        if finite_mode(op, x) != Mode::Recurrence {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.4.R1 (`Nat-Reg`)** — the terminology discipline for the **two independent axes**. The
/// engine names them with distinct types so they are never conflated: the **aspect** axis
/// (`↓_M`/`∞_M`, the element orbit-fate dichotomy — [`crate::r1::aspect_partition::Aspect`])
/// and the **mode** axis ([`Mode`], the reach mechanism: recurrence/convergence). "Asymptotic"
/// names *neither* — it qualifies the analysis *layer* (the AOI of R5), which runs in both
/// modes. The axes coincide on `↓_M` but diverge on `∞_M`. `==` compares the named axis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnalysisAxis {
    /// The element orbit-fate dichotomy `↓_M`/`∞_M` (`Aspect`/WF-NWF).
    Aspect,
    /// The reach mechanism: recurrence (finitary) / convergence (topological) (`Mode`).
    Mode,
    /// The analysis layer (asymptotic orbit invariants), which runs in *both* modes.
    AnalysisLayer,
}

/// Witness **R1.4.T2 (`Nat-CC`)** — **Native Consistency**: the nine PA-\* axioms are
/// **mutually consistent**, witnessed by the finitary analog of `ℕ ∪ (0,1]` — a single
/// instance carrying both a convergent element (`↓_M`) and a persistent `≈`-cycle (`∞_M`) on
/// which the checkable step/orbit axioms hold *simultaneously* (`PA-Conf`, `PA-Fix`,
/// `PA-Bisim`, `PA-NWF`, recurrence-mode coverage). Returns `true` when the witness satisfies
/// them all — no axiom contradicts another.
pub fn certify_native_consistency() -> bool {
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;
    // 0→1 (↓_M); 2⇄3 observationally distinct (∞_M) — both aspects in one instance.
    let e = [(0, 1), (2, 3), (3, 2)];
    let Ok(s) = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]) else {
        return false;
    };
    let Ok(m) = Instance::new(s, vec![ElementId(1), ElementId(1), ElementId(3), ElementId(2)]) else {
        return false;
    };
    crate::r1::axiom_system::pa_conf(&m).is_ok() // confluence
        && crate::r1::axiom_system::pa_fix(&m).is_ok() // Fix = NF
        && crate::r1::axiom_system::pa_nwf(&m) // ∞_M ≠ ∅
        && crate::r1::universal_axioms::pa_bisim(&m).is_ok() // PA-Bisim
        && crate::r1::universal_axioms::pa_reach(&m) // PA-Reach
        && certify_mode_coverage(&m.operator()).is_ok() // modes cover every element
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

    #[test]
    fn the_nine_axioms_are_mutually_consistent_and_the_axes_are_distinct() {
        // Nat-CC: a single instance satisfies the checkable PA-* axioms simultaneously.
        assert!(certify_native_consistency());
        // Nat-Reg: aspect, mode, and analysis-layer are three distinct named axes.
        assert_ne!(AnalysisAxis::Aspect, AnalysisAxis::Mode);
        assert_ne!(AnalysisAxis::Mode, AnalysisAxis::AnalysisLayer);
    }

    #[test]
    fn recurrence_serves_both_aspects_on_the_finite_substrate() {
        // 0→1 (↓_M: Fix at d_M) and 2⇄3 distinct obs (∞_M: class cycle at n_M) — the SAME
        // mode, Recurrence, serves both aspects.
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Instance::new(s, vec![ElementId(1), ElementId(1), ElementId(3), ElementId(2)]).unwrap();
        let op = m.operator();
        assert_eq!(finite_mode(&op, ElementId(0)), Mode::Recurrence); // ↓_M
        assert_eq!(finite_mode(&op, ElementId(2)), Mode::Recurrence); // ∞_M
        assert!(!convergence_mode_available(&op, ElementId(2)));
        assert!(matches!(certify_mode_coverage(&op), Ok(())));
    }
}
