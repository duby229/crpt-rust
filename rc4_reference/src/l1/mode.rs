//! # L1.4 — Canonicalization Modes (two modes; rc4)
//!
//! Exact realization of spec section **L1.4** (`CRPT_OMEGA_TOWER_L1.md`, v1.0.0-rc4):
//!
//! - L1.4.D1 `Mode` — CRPT separates two axes. The **regime** axis classifies an
//!   *element* by orbit fate (↓_M / ∞_M — no third regime, `Part` L2.2.T3). The **mode**
//!   axis classifies the *reach mechanism* — how the orbit reaches its canonical object
//!   and what certifies the reach — and there are exactly **two**:
//!   - **Recurrence (finitary mode)** — the orbit reaches its canonical object *by
//!     visiting it*: equality of iterates in the ≈-quotient at finite depth. On ↓_M this
//!     is termination — Fix reached at depth `d_M`, a recurrent 1-cycle at a fixpoint
//!     (`PA-WN`). On ∞_M it is eventual periodicity — the class orbit enters its
//!     recurrent cycle at depth `n_M` (`PA-Reach-Fin` L1.3.T2). No topology needed.
//!   - **Convergence (topological mode)** — the orbit reaches its canonical object *as a
//!     𝒯-limit*: `CFix(x) = lim ρ^n(x)`. Certified by `PA-WN_top` with a Hausdorff
//!     topology (`TopSep-Uniq` L1.2.T1); on ∞_M this is PA-Reach's convergence
//!     realization (`PA-Reach-Top` L1.3.T3). On ↓_M it degenerates (a reached fixpoint
//!     is trivially its own limit).
//!
//! These are the only mechanisms; the composite — convergence onto a recurrent limit
//! cycle — introduces no third (`PA-Reach-Decomp` L1.3.T4).
//!
//! **The AOI is not a mode** (rc4): asymptotic orbit invariance is the *analysis layer*
//! — the invariant theory computed on the destination ([`crate::l6::aoi_full_proofs`]),
//! defined unconditionally and finitely presentable in either mode (the cycle presents
//! it under recurrence, the limit under convergence). Modes reach canonical objects *in*
//! `𝒰_M`; the AOI is an invariant *about* orbits.
//!
//! **On the finite discrete substrate** (the engine's 𝒯, see [`crate::l1::substrate`]):
//! a discrete sequence converges iff eventually constant, so convergence degenerates to
//! recurrence — **every** element is canonicalized in recurrence mode (↓_M at `d_M`,
//! ∞_M at `n_M`). Convergence mode is inhabited on the symbolic topological tier
//! ([`crate::l1::topology`]). This is the exact finite picture, not an omission.

use crate::l1::substrate::ElementId;
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::is_convergent;

/// **L1.4.D1 (`Mode`)** — a reach mechanism. Exactly two. `==` compares the tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Recurrence (finitary) — canonical object reached *by visiting it*: Fix at `d_M`
    /// on ↓_M (`PA-WN`), the recurrent class cycle at `n_M` on ∞_M (`PA-Reach-Fin`).
    Recurrence,
    /// Convergence (topological) — canonical object reached *as a 𝒯-limit*
    /// (`PA-WN_top` / `PA-Reach-Top`, Hausdorff).
    Convergence,
}

/// **L1.4.D1 (`Mode`)** — the mode by which `x`'s canonical object is reached, on the
/// engine's finite discrete topology: **Recurrence**, for every element (↓_M terminates
/// at `d_M`; ∞_M enters its class cycle at `n_M`). Convergence requires a non-discrete
/// topology — see [`convergence_mode_available`] and the symbolic topological tier.
pub fn canonicalization_mode(op: &ProjectionOperator, x: ElementId) -> Mode {
    let _ = (op, x);
    Mode::Recurrence
}

/// Whether **convergence mode** is available at `x`: its orbit has a genuine `𝒯`-limit
/// (`PA-WN_top`). On the finite discrete topology a sequence converges iff eventually
/// constant — i.e. iff recurrence already certifies the reach — so convergence never
/// applies non-degenerately here (it is inhabited on the symbolic topological tier).
pub fn convergence_mode_available(op: &ProjectionOperator, x: ElementId) -> bool {
    let _ = (op, x);
    false
}

/// Witness the L1.4.D1/L1.4.T1 (`Mode-Comp`) coverage on the finite substrate: every
/// element is reached in **recurrence** mode — ↓_M terminates (`d_M` finite), and every
/// persistent element's class orbit enters a recurrent cycle (`n_M` total — the
/// `PA-Reach-Fin` realization, automatic on finite substrates). Returns the first
/// element with neither reach, or `Ok`.
pub fn certify_mode_coverage(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        let reached = if is_convergent(op, x) {
            true // Fix reached at d_M
        } else {
            crate::l3::persistent::n_reach(op, x).is_some() // cycle entered at n_M
        };
        if !reached || canonicalization_mode(op, x) != Mode::Recurrence {
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
    fn recurrence_serves_both_regimes_on_the_finite_substrate() {
        // 0→1 (↓_M: Fix at d_M) and 2⇄3 distinct obs (∞_M: class cycle at n_M) — the
        // SAME mode, recurrence, serves both regimes (rc4 two-mode resolution).
        let e = [(0, 1), (2, 3), (3, 2)];
        let s = Substrate::with_observation(4, &e, &e, &[5, 6, 7, 8]).unwrap();
        let m = Model::new(s, vec![id(1), id(1), id(3), id(2)]).unwrap();
        let op = m.operator();
        assert_eq!(canonicalization_mode(&op, id(0)), Mode::Recurrence); // ↓_M
        assert_eq!(canonicalization_mode(&op, id(2)), Mode::Recurrence); // ∞_M
        // convergence is degenerate on the discrete topology, even for ∞_M.
        assert!(!convergence_mode_available(&op, id(2)));
        assert!(matches!(certify_mode_coverage(&op), Ok(())));
    }

    #[test]
    fn pure_wf_is_recurrence_at_one_cycles() {
        let m = Model::from_functional_reduction(
            Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap(),
        )
        .unwrap();
        let op = m.operator();
        assert_eq!(canonicalization_mode(&op, id(0)), Mode::Recurrence);
        assert!(matches!(certify_mode_coverage(&op), Ok(())));
    }
}
