//! # R0.6 — Universal Horizontal-Vertical Duality
//!
//! Exact realization of spec section **R0.6** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9) — the
//! **static** duality (distinct from the dynamic tower duality of R0.5):
//!
//! - R0.6.T1 `HV-Dual-Static` — in any projection system the **reduction** relation governs
//!   the *vertical* (observable, canonical-form) dimension and the **structural** relation
//!   governs the *horizontal* (unobservable, within-fiber) dimension; the two are
//!   independent. This grounds the two-relation substrate design (R1.1.D1).
//! - R0.6.R1 `HVDual-InfDual` — the static duality (this section) and the dynamic `Inf-Dual-U`
//!   (R0.5.T1) are *both needed*: the static grounds the substrate's two relations, the
//!   dynamic grounds the tower exchange.
//! - R0.6.T2 `CRPT-HV-Static` — the substrate inclusion `→_ρ ⊆ →_σ` (R1.1.D1) is the
//!   substrate-level expression of **vertical ⊆ horizontal**: every observable change is a
//!   structural change, not conversely.
//!
//! Realized on the CRPT substrate, where both relations are present and the inclusion is
//! enforced at construction.

use crate::r1::substrate::{ElementId, Substrate};

/// Witness **R0.6.T1 (`HV-Dual-Static`)** / **R0.6.T2 (`CRPT-HV-Static`)** — the two
/// dimensions are present and ordered on a substrate: **(vertical ⊆ horizontal)** every
/// reduction edge `x →_ρ y` is also structural `x →_σ y` (`→_ρ ⊆ →_σ`, the R1.1.D1
/// inclusion — observable change ⟹ structural change). Returns the first reduction edge that
/// is not structural (none — the inclusion is enforced at construction), or `Ok`.
pub fn certify_vertical_subset_horizontal(s: &Substrate) -> Result<(), (ElementId, ElementId)> {
    for x in s.elements() {
        for &y in s.reduction_successors(x) {
            if !s.structural_step(x, y) {
                return Err((x, y)); // a vertical edge that is not horizontal — impossible
            }
        }
    }
    Ok(())
}

/// Witness **R0.6.T1 (`HV-Dual-Static`) — independence** — the horizontal dimension is
/// *strictly richer* than the vertical: there is `→_σ`-structure not visible to `→_ρ` (a
/// purely structural edge), so the two dimensions do not coincide. Returns `true` when the
/// substrate carries a structural edge that is not a reduction edge (horizontal content
/// invisible to the projection).
pub fn has_purely_horizontal_structure(s: &Substrate) -> bool {
    s.elements().any(|x| s.structural_successors(x).iter().any(|&y| !s.reduces(x, y)))
}

/// Witness **R0.6.R1 (`HVDual-InfDual`)** — both dualities are needed: the **static** witness
/// (the substrate inclusion `→_ρ ⊆ →_σ`, this section) and the **dynamic** witness (the
/// reification depth law `d_{π'}(w) = |w|−1`, R0.5) each hold on the CRPT realization.
/// Returns `true` when both the static inclusion and the dynamic depth law are witnessed.
pub fn certify_both_dualities(base: &crate::r1::reduction_strategy::Instance) -> bool {
    let static_ok = certify_vertical_subset_horizontal(base.substrate()).is_ok();
    // dynamic: the universal reification depth law (R0.5) on the same base.
    let dynamic_ok =
        crate::r0::universal_inf_dual::certify_reify_quot_invariant(base);
    static_ok && dynamic_ok
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduction_is_vertical_subset_of_horizontal_structural() {
        // 0 →_ρ 2, 1 →_ρ 2, 2 a normal form; →_σ adds the purely-horizontal edge 0 →_σ 1.
        let s = Substrate::new(3, &[(0, 2), (1, 2)], &[(0, 2), (1, 2), (0, 1)]).unwrap();
        // HV-Dual-Static / CRPT-HV-Static: vertical ⊆ horizontal.
        assert!(matches!(certify_vertical_subset_horizontal(&s), Ok(())));
        // independence: there is horizontal structure (0 →_σ 1) invisible to →_ρ.
        assert!(has_purely_horizontal_structure(&s));
        // HVDual-InfDual: both the static and dynamic dualities are witnessed on the instance.
        let base = crate::r1::reduction_strategy::Instance::from_functional_reduction(
            Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap(),
        )
        .unwrap();
        assert!(certify_both_dualities(&base));
    }
}
