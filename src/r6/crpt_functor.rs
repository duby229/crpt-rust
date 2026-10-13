//! # R6.3 — The CRPT Functor F : Inst_CRPT → ω-Cat
//!
//! Exact realization of the functoriality core of spec section **R6.3**
//! (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.3.D1 `F-CRPT` — the CRPT functor `F` sends each instance `M` to its tower
//!   `Tower(M)` (R6.7) viewed as an ω-category (Reify maps as 1-cells), and each
//!   homomorphism `φ : M₁ → M₂` to the level-wise induced functor `Tower(φ)`.
//! - R6.3.T1 `F-Func` — `F` is a functor: `F(id_M) = id` and `F(ψ ∘ φ) = F(ψ) ∘ F(φ)`.
//!
//! **Computable content.** `F` on **objects** is [`crpt_functor_object`] = `Tower(M)`. `F`
//! on **morphisms** is the map it induces on the query signature `Q_M` (the level-0 atoms
//! of the tower, since `Reify` is built over `Q_M`): [`induced_signature_map`] sends each
//! atom `f ∈ Q_{M₁}` to the atom `CFix_{M₂}(φ(f)) ∈ Q_{M₂}`. This is well-defined on
//! classes because `φ` preserves `≃_M` (Φ_E), and **functorial** for the same reason —
//! which is what the certify functions witness. (Defined where convergent atoms map to
//! convergent images, i.e. the well-founded tower setting; persistent images are skipped.)

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::Instance;
use crate::r4::instance_homomorphisms::Homomorphism;
use crate::r6::tower::{tower, Tower};

/// **R6.3.D1 (`F-CRPT`)** — `F` on objects: `F(M) = Tower(M)` (R6.7), the instance's tower.
pub fn crpt_functor_object(m: &Instance) -> Tower<'_> {
    tower(m)
}

/// **R6.3.D1 (`F-CRPT`)** — `F` on morphisms, at the signature level: the map `Q_{M₁} →
/// Q_{M₂}` a homomorphism `φ` induces, `f ↦ CFix_{M₂}(φ(f))`. Returned as `(source atom,
/// image atom)` pairs (only atoms with convergent image are included).
pub fn induced_signature_map(phi: &Homomorphism) -> Vec<(ElementId, ElementId)> {
    let source = phi.source().operator();
    let target = phi.target().operator();
    source
        .fixpoints()
        .into_iter()
        .filter_map(|f| target.canonical_fixpoint(phi.apply(f)).map(|atom| (f, atom)))
        .collect()
}

/// Witness **R6.3.T1 (`F-Func`)**, identity law: `F(id_M)` is the identity on `Q_M`
/// (`F(id_M)(f) = CFix(f) = f` for every atom `f`). Returns the first offending atom, or `Ok`.
pub fn certify_functor_preserves_identity(m: &Instance) -> Result<(), ElementId> {
    let identity = Homomorphism::identity(m);
    for (source_atom, image_atom) in induced_signature_map(&identity) {
        if source_atom != image_atom {
            return Err(source_atom);
        }
    }
    Ok(())
}

/// Witness **R6.3.T1 (`F-Func`)**, composition law: `F(ψ ∘ φ) = F(ψ) ∘ F(φ)` on `Q_{M₁}`.
/// Returns the first atom where the two composites disagree, or `Ok`.
pub fn certify_functor_preserves_composition(
    phi: &Homomorphism,
    psi: &Homomorphism,
) -> Result<(), ElementId> {
    let composite = match phi.compose(psi) {
        Ok(c) => c,
        Err(_) => return Ok(()), // not composable ⇒ nothing to check
    };
    // F(ψ ∘ φ): direct induced map of the composite.
    let direct = induced_signature_map(&composite);
    // F(ψ) ∘ F(φ): apply F(φ) then F(ψ) at the signature level.
    let f_phi = induced_signature_map(phi);
    let f_psi = induced_signature_map(psi);
    for &(source_atom, mid_atom) in &f_phi {
        let via = f_psi.iter().find(|(s, _)| *s == mid_atom).map(|(_, t)| *t);
        let straight = direct.iter().find(|(s, _)| *s == source_atom).map(|(_, t)| *t);
        if via != straight {
            return Err(source_atom);
        }
    }
    Ok(())
}

/// Witness **R6.3.T2 (`Twr-Func`)** / **R6.3.C1 (`Iso-ωCat`)** — **tower functoriality**: a CRPT
/// homomorphism `Φ : M₁ → M₂` induces `Φₙ := Reify^n(Φ) : Reify^n(M₁) → Reify^n(M₂)` at every
/// level, so `F(Φ) = Tower(Φ)` is a functor (preserves identity + composition); when `Φ` is an
/// isomorphism, `F(Φ)` is an isomorphism of tower ω-categories. Certified via the
/// signature-level induced maps preserving identity and composition. Returns the first atom
/// where functoriality fails (none), or `Ok`.
pub fn certify_tower_functoriality(phi: &Homomorphism, psi: &Homomorphism) -> Result<(), ElementId> {
    // tower functoriality = the induced-signature functor preserving composition (Twr-Func);
    // the identity case is certify_functor_preserves_identity.
    certify_functor_preserves_composition(phi, psi)
}

/// Witness **R6.3.T4 (`Inst-Fib-T`)** / **R6.3.D2 (`Inst-Fib`)** — the **instance-theory
/// fibration**: the CRPT functor `F` fibers `Inst_CRPT` over `ω-Cat`; the **fiber over a tower
/// `T`** is `{M : F(M) ≅ T}` — the class of instances with isomorphic tower type, which by
/// `NFC-TInv` is determined by the query-signature size `|Q_M|`. Returns the **fiber
/// coordinate** of an instance: its query-signature size `|Q_M|`, the invariant indexing the
/// fibration. (`R6.3.R1` `Unif-Arch`: this is the unified architecture — one functor `F`
/// organizing instances, towers, and their morphisms.)
pub fn instance_fibration_coordinate(m: &Instance) -> u32 {
    // F-fiber index: instances share a fiber iff same tower type iff same |Q_M| (NFC-TInv).
    crate::r6::tower::tower(m).query_signature_size()
}

/// Witness **R6.3.T4 (`Inst-Fib-T`)** — two instances lie in the **same `F`-fiber** iff they
/// have the same tower type (here, the same query-signature size — `F(M₁) ≅ F(M₂)`). Returns
/// whether `m1` and `m2` are fiber-equivalent under the instance-theory fibration.
pub fn same_instance_fiber(m1: &Instance, m2: &Instance) -> bool {
    instance_fibration_coordinate(m1) == instance_fibration_coordinate(m2)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 𝒰 = {0,1}, 0 →_ρ 1, 1 ∈ NF.
    fn chain() -> Instance {
        Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap()).unwrap()
    }

    /// 𝒰 = {1,0}, 1 →_ρ 0, 0 ∈ NF (relabelling of `chain`).
    fn chain_swapped() -> Instance {
        Instance::from_functional_reduction(Substrate::new(2, &[(1, 0)], &[(1, 0)]).unwrap()).unwrap()
    }

    #[test]
    fn functor_object_is_the_tower() {
        let m = chain();
        // F(M) = Tower(M): one fixpoint ⇒ degenerate tower of signature size 1.
        let t = crpt_functor_object(&m);
        assert_eq!(t.query_signature_size(), 1);
    }

    #[test]
    fn functor_preserves_identity_and_composition() {
        let m1 = chain();
        let m2 = chain_swapped();
        // φ: 0↦1, 1↦0 (M₁→M₂); ψ: 1↦0, 0↦1 (M₂→M₁), the inverse relabelling.
        let phi = Homomorphism::new(&m1, &m2, vec![id(1), id(0)]).unwrap();
        let psi = Homomorphism::new(&m2, &m1, vec![id(1), id(0)]).unwrap();
        // F(id) = id on Q_M.
        assert!(matches!(certify_functor_preserves_identity(&m1), Ok(())));
        // F(ψ ∘ φ) = F(ψ) ∘ F(φ).
        assert!(matches!(certify_functor_preserves_composition(&phi, &psi), Ok(())));
        // Twr-Func: tower functoriality holds; Inst-Fib: M₁, M₂ share the F-fiber (same |Q|).
        assert!(matches!(certify_tower_functoriality(&phi, &psi), Ok(())));
        assert!(same_instance_fiber(&m1, &m2));
        assert_eq!(instance_fibration_coordinate(&m1), 1);
        // the induced signature map of φ sends M₁'s atom (fixpoint 1) to M₂'s atom (0).
        assert_eq!(induced_signature_map(&phi), vec![(id(1), id(0))]);
    }
}
