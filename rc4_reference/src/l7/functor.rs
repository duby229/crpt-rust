//! # L7.3 — The CRPT Functor F : Mod_CRPT → ω-Cat
//!
//! Exact realization of the functoriality core of spec section **L7.3**
//! (`CRPT_OMEGA_TOWER_L7.md`, v1.0.0-rc4):
//!
//! - L7.3.D1 `F-CRPT` — the CRPT functor `F` sends each model `M` to its tower
//!   `Tower(M)` (L8.4) viewed as an ω-category (Lift maps as 1-cells), and each
//!   homomorphism `φ : M₁ → M₂` to the level-wise induced functor `Tower(φ)`.
//! - L7.3.T1 `F-Func` — `F` is a functor: `F(id_M) = id` and `F(ψ ∘ φ) = F(ψ) ∘ F(φ)`.
//!
//! **Computable content.** `F` on **objects** is [`crpt_functor_object`] = `Tower(M)`. `F`
//! on **morphisms** is the map it induces on the query signature `Q_M` (the level-0 atoms
//! of the tower, since `Lift` is built over `Q_M`): [`induced_signature_map`] sends each
//! atom `f ∈ Q_{M₁}` to the atom `CFix_{M₂}(φ(f)) ∈ Q_{M₂}`. This is well-defined on
//! classes because `φ` preserves `≃_M` (Φ_E), and **functorial** for the same reason —
//! which is what the certify functions witness. (Defined where convergent atoms map to
//! convergent images, i.e. the well-founded tower setting; persistent images are skipped.)

use crate::l1::substrate::ElementId;
use crate::l2::projection::Model;
use crate::l5::homomorphism::Homomorphism;
use crate::l8::tower::{tower, Tower};

/// **L7.3.D1 (`F-CRPT`)** — `F` on objects: `F(M) = Tower(M)` (L8.4), the model's tower.
pub fn crpt_functor_object(m: &Model) -> Tower<'_> {
    tower(m)
}

/// **L7.3.D1 (`F-CRPT`)** — `F` on morphisms, at the signature level: the map `Q_{M₁} →
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

/// Witness **L7.3.T1 (`F-Func`)**, identity law: `F(id_M)` is the identity on `Q_M`
/// (`F(id_M)(f) = CFix(f) = f` for every atom `f`). Returns the first offending atom, or `Ok`.
pub fn certify_functor_preserves_identity(m: &Model) -> Result<(), ElementId> {
    let identity = Homomorphism::identity(m);
    for (source_atom, image_atom) in induced_signature_map(&identity) {
        if source_atom != image_atom {
            return Err(source_atom);
        }
    }
    Ok(())
}

/// Witness **L7.3.T1 (`F-Func`)**, composition law: `F(ψ ∘ φ) = F(ψ) ∘ F(φ)` on `Q_{M₁}`.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 𝒰 = {0,1}, 0 →_ρ 1, 1 ∈ NF.
    fn chain() -> Model {
        Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap()).unwrap()
    }

    /// 𝒰 = {1,0}, 1 →_ρ 0, 0 ∈ NF (relabelling of `chain`).
    fn chain_swapped() -> Model {
        Model::from_functional_reduction(Substrate::new(2, &[(1, 0)], &[(1, 0)]).unwrap()).unwrap()
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
        // the induced signature map of φ sends M₁'s atom (fixpoint 1) to M₂'s atom (0).
        assert_eq!(induced_signature_map(&phi), vec![(id(1), id(0))]);
    }
}
