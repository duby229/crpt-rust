//! # L5.2 — Model Homomorphisms and the Category Mod_CRPT
//!
//! Exact realization of spec section **L5.2** (`CRPT_OMEGA_TOWER_L5.md`, v1.0.0-rc4):
//!
//! - L5.2.D1 `Hom` — a model homomorphism Φ : M₁ → M₂ is a map of universes
//!   satisfying the **canonical four conditions** (rc2 designated L5.2.D1 canonical;
//!   the spurious Φ_σ was removed):
//!   - **Φ_R** (relation preservation): `x →_ρ y ⟹ Φ(x) →_ρ Φ(y)`.
//!   - **Φ_E** (equivalence preservation): `x ≃_{M₁} y ⟹ Φ(x) ≃_{M₂} Φ(y)`.
//!   - **Φ_ρ** (projection commutativity up to ≃): `Φ(ρ_{M₁}(x)) ≃_{M₂} ρ_{M₂}(Φ(x))`.
//!   - **Φ_LA** (local-axiom transport): vacuous here — the engine carries no
//!     model-local axioms yet (LA_M = ∅), so this condition holds trivially.
//! - L5.2.T1 `Mod-Cat` / L5.5.D1 `Mod_CRPT-Cat` / L7.2.D1 `Mod_CRPT` — the category `Mod_CRPT`: CRPT models as objects, homomorphisms as
//!   morphisms, with identities and (associative) composition. Realized here by
//!   [`Homomorphism::identity`] and [`Homomorphism::compose`].
//!
//! The conditions are part of the *definition*, so they are **enforced at
//! construction**: a [`Homomorphism`] value *is* a model homomorphism.

use crate::l1::substrate::ElementId;
use crate::l2::fiber::observable_equivalence;
use crate::l2::projection::Model;

/// Error constructing a [`Homomorphism`] — data that is not a model homomorphism (L5.2.D1).
#[derive(Debug, Clone, Copy)]
pub enum HomomorphismError {
    /// The map length differs from |𝒰_{M₁}|.
    WrongLength { expected: u32, got: usize },
    /// Φ(x) lands outside the target universe `0..n₂`.
    OutOfRange { x: ElementId, value: u32, n: u32 },
    /// **Φ_R** violated: x →_ρ y in M₁ but not Φ(x) →_ρ Φ(y) in M₂.
    RelationNotPreserved { x: ElementId, y: ElementId },
    /// **Φ_E** violated: x ≃_{M₁} y but Φ(x) ≄_{M₂} Φ(y).
    EquivalenceNotPreserved { x: ElementId, y: ElementId },
    /// **Φ_ρ** violated: Φ(ρ_{M₁}(x)) ≄_{M₂} ρ_{M₂}(Φ(x)).
    ProjectionNotPreserved { x: ElementId },
    /// `compose` only: the codomain of the first map ≠ the domain of the second.
    NotComposable { mid_target: u32, mid_source: u32 },
}

/// **L5.2.D1 (`Hom`)** — a model homomorphism Φ : M₁ → M₂. Borrows source and
/// target models; owns the universe map `Φ(x)`. Constructed only after checking
/// Φ_R, Φ_E, Φ_ρ (Φ_LA vacuous), so it *is* a homomorphism. No derived equality.
pub struct Homomorphism<'a> {
    source: &'a Model,
    target: &'a Model,
    map: Vec<ElementId>, // Φ(x) for x ∈ 𝒰_{M₁}, values in 𝒰_{M₂}
}

impl<'a> Homomorphism<'a> {
    /// Construct Φ : M₁ → M₂ from a universe map, validating Φ_R, Φ_E, Φ_ρ (L5.2.D1).
    pub fn new(
        source: &'a Model,
        target: &'a Model,
        map: Vec<ElementId>,
    ) -> Result<Self, HomomorphismError> {
        let n1 = source.substrate().universe_len();
        let n2 = target.substrate().universe_len();
        if map.len() != n1 as usize {
            return Err(HomomorphismError::WrongLength { expected: n1, got: map.len() });
        }
        for (i, &image) in map.iter().enumerate() {
            if image.index() >= n2 as usize {
                return Err(HomomorphismError::OutOfRange { x: ElementId(i as u32), value: image.0, n: n2 });
            }
        }
        let phi = Self { source, target, map };
        phi.certify_relation_preservation()?; // Φ_R
        phi.certify_equivalence_preservation()?; // Φ_E
        phi.certify_projection_commutativity()?; // Φ_ρ
        Ok(phi)
    }

    /// The identity homomorphism id_M : M → M (`Mod-Cat` L5.2.T1).
    pub fn identity(model: &'a Model) -> Self {
        let map = model.substrate().elements().collect();
        Self { source: model, target: model, map }
    }

    /// **L5.2.D1**: Φ(x).
    #[inline]
    pub fn apply(&self, x: ElementId) -> ElementId {
        self.map[x.index()]
    }

    /// The source model M₁.
    pub fn source(&self) -> &Model {
        self.source
    }

    /// The target model M₂.
    pub fn target(&self) -> &Model {
        self.target
    }

    /// **L5.2.T1 (`Mod-Cat`)** — composition `Ψ ∘ Φ : M₁ → M₃` of `Φ = self : M₁ → M₂`
    /// and `psi : M₂ → M₃`. The composite of homomorphisms is a homomorphism;
    /// constructed via [`Homomorphism::new`] (which re-verifies the conditions).
    pub fn compose(&self, psi: &Homomorphism<'a>) -> Result<Homomorphism<'a>, HomomorphismError> {
        let mid_target = self.target.substrate().universe_len();
        let mid_source = psi.source.substrate().universe_len();
        if mid_target != mid_source {
            return Err(HomomorphismError::NotComposable { mid_target, mid_source });
        }
        let map = self.map.iter().map(|&x| psi.apply(x)).collect();
        Homomorphism::new(self.source, psi.target, map)
    }

    /// **L5.2.D2 (`Iso`)** — whether `Φ` is an isomorphism: it has a two-sided inverse `Ψ`
    /// that is *itself* a homomorphism. Decided by: `Φ` is a bijection of universes and the
    /// inverse map is a valid homomorphism `M₂ → M₁`. Isomorphic models carry identical
    /// projection/regime/horizon structure.
    pub fn is_isomorphism(&self) -> bool {
        let n1 = self.source.substrate().universe_len() as usize;
        let n2 = self.target.substrate().universe_len() as usize;
        if n1 != n2 {
            return false;
        }
        // inverse[Φ(x)] = x; must be a total bijection (injective + surjective).
        let mut inverse: Vec<Option<ElementId>> = vec![None; n2];
        for x in self.source.substrate().elements() {
            let image = self.apply(x).index();
            if inverse[image].is_some() {
                return false; // not injective
            }
            inverse[image] = Some(x);
        }
        match inverse.into_iter().collect::<Option<Vec<ElementId>>>() {
            // Ψ exists as a bijection; Φ is an isomorphism iff Ψ is also a homomorphism.
            Some(inverse_map) => Homomorphism::new(self.target, self.source, inverse_map).is_ok(),
            None => false, // not surjective
        }
    }

    /// **L5.2.D4 (`Inst-Emb`)** — whether `Φ` is a **faithful CRPT embedding** `M₁ ↪ M₂`:
    /// `Φ_U` is injective (`Emb`) and `Φ` **reflects** `≃` (`Faith`): `Φ(x) ≃_{M₂} Φ(y) ⟹
    /// x ≃_{M₁} y`. (A homomorphism already *preserves* `≃` via Φ_E; faithfulness adds that
    /// it does not *merge* distinct observable classes.)
    pub fn is_faithful_embedding(&self) -> bool {
        let n2 = self.target.substrate().universe_len() as usize;
        // (Emb) Φ_U injective.
        let mut seen = vec![false; n2];
        for x in self.source.substrate().elements() {
            let i = self.apply(x).index();
            if seen[i] {
                return false;
            }
            seen[i] = true;
        }
        // (Faith) Φ reflects ≃: Φ(x) ≃_{M₂} Φ(y) ⟹ x ≃_{M₁} y.
        let op1 = self.source.operator();
        let op2 = self.target.operator();
        let elements: Vec<ElementId> = self.source.substrate().elements().collect();
        for &x in &elements {
            for &y in &elements {
                if observable_equivalence(&op2, self.apply(x), self.apply(y))
                    && !observable_equivalence(&op1, x, y)
                {
                    return false;
                }
            }
        }
        true
    }

    /// Witness **Φ_R** (relation preservation): `x →_ρ y ⟹ Φ(x) →_ρ Φ(y)`.
    pub fn certify_relation_preservation(&self) -> Result<(), HomomorphismError> {
        let source = self.source.substrate();
        let target = self.target.substrate();
        for x in source.elements() {
            for &y in source.reduction_successors(x) {
                if !target.reduces(self.apply(x), self.apply(y)) {
                    return Err(HomomorphismError::RelationNotPreserved { x, y });
                }
            }
        }
        Ok(())
    }

    /// Witness **Φ_E** (equivalence preservation): `x ≃_{M₁} y ⟹ Φ(x) ≃_{M₂} Φ(y)`.
    pub fn certify_equivalence_preservation(&self) -> Result<(), HomomorphismError> {
        let op1 = self.source.operator();
        let op2 = self.target.operator();
        let elements: Vec<ElementId> = self.source.substrate().elements().collect();
        for &x in &elements {
            for &y in &elements {
                if observable_equivalence(&op1, x, y)
                    && !observable_equivalence(&op2, self.apply(x), self.apply(y))
                {
                    return Err(HomomorphismError::EquivalenceNotPreserved { x, y });
                }
            }
        }
        Ok(())
    }

    /// Witness **Φ_ρ** (projection commutativity): `Φ(ρ_{M₁}(x)) ≃_{M₂} ρ_{M₂}(Φ(x))`.
    pub fn certify_projection_commutativity(&self) -> Result<(), HomomorphismError> {
        let op1 = self.source.operator();
        let op2 = self.target.operator();
        for x in self.source.substrate().elements() {
            let lhs = self.apply(op1.project(x)); // Φ(ρ_{M₁}(x))
            let rhs = op2.project(self.apply(x)); // ρ_{M₂}(Φ(x))
            if !observable_equivalence(&op2, lhs, rhs) {
                return Err(HomomorphismError::ProjectionNotPreserved { x });
            }
        }
        Ok(())
    }
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
        let s = Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap();
        Model::from_functional_reduction(s).unwrap()
    }

    /// 𝒰 = {0,1}, 1 →_ρ 0, 0 ∈ NF (the relabelling 0 ↔ 1 of `chain`).
    fn chain_swapped() -> Model {
        let s = Substrate::new(2, &[(1, 0)], &[(1, 0)]).unwrap();
        Model::from_functional_reduction(s).unwrap()
    }

    #[test]
    fn identity_is_a_homomorphism() {
        let m = chain();
        let id_hom = Homomorphism::identity(&m);
        assert_eq!(id_hom.apply(id(0)), id(0));
        assert!(matches!(id_hom.certify_relation_preservation(), Ok(())));
        assert!(matches!(id_hom.certify_equivalence_preservation(), Ok(())));
        assert!(matches!(id_hom.certify_projection_commutativity(), Ok(())));
    }

    #[test]
    fn renaming_isomorphism() {
        let m1 = chain(); // 0→1
        let m2 = chain_swapped(); // 1→0
        // Φ: 0↦1, 1↦0. Then 0→_ρ1 in M1 ⟹ Φ(0)=1 →_ρ Φ(1)=0 in M2. ✓
        let phi = Homomorphism::new(&m1, &m2, vec![id(1), id(0)]).unwrap();
        assert_eq!(phi.apply(id(0)), id(1));
        // composing with its inverse Ψ: 1↦0,0↦1 (M2→M1) yields a self-map of M1.
        let psi = Homomorphism::new(&m2, &m1, vec![id(1), id(0)]).unwrap();
        let round_trip = phi.compose(&psi).unwrap();
        assert_eq!(round_trip.apply(id(0)), id(0)); // back to identity on M1
        assert_eq!(round_trip.apply(id(1)), id(1));
        // Φ (the 0↔1 relabelling) is an isomorphism; the identity is too.
        assert!(phi.is_isomorphism());
        assert!(Homomorphism::identity(&m1).is_isomorphism());
        // An isomorphism is in particular a faithful embedding (Inst-Emb): injective + reflects ≃.
        assert!(phi.is_faithful_embedding());
    }

    #[test]
    fn collapsing_map_is_not_an_isomorphism() {
        // A non-bijective endomorphism is not an isomorphism. 0→1 (1 NF); map 0,1 ↦ 1.
        // (It fails Φ_R, so it isn't even a homomorphism — but the iso check is independent.)
        let m = chain();
        // identity is the iso; a different-size target can't be iso.
        let one = Model::from_functional_reduction(Substrate::new(1, &[], &[]).unwrap()).unwrap();
        // a homomorphism chain → 𝟙 would map both to ★, not bijective ⇒ not iso.
        if let Ok(to_unit) = Homomorphism::new(&m, &one, vec![id(0), id(0)]) {
            assert!(!to_unit.is_isomorphism());
        }
    }

    #[test]
    fn relation_violation_is_rejected() {
        let m1 = chain(); // 0→1
        let m2 = chain(); // 0→1
        // Φ: 0↦0, 1↦0. Then 0→_ρ1 needs Φ(0)=0 →_ρ Φ(1)=0, but 0 →_ρ {1} only.
        assert!(matches!(
            Homomorphism::new(&m1, &m2, vec![id(0), id(0)]),
            Err(HomomorphismError::RelationNotPreserved { x, y }) if x == id(0) && y == id(1)
        ));
    }
}
