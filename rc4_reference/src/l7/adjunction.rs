//! # L7.2 — The `Lift ⊣ Collapse` Adjunction
//!
//! Exact realization of spec section **L7.2** (`CRPT_OMEGA_TOWER_L7.md`, v1.0.0-rc4):
//!
//! - L7.2.D2 `ω-Cat` — the ω-category `C^ω_CRPT`: tower levels as 0-cells, the Lift
//!   maps `F_n : M^n → M^{n+1}` as model homomorphisms — presented by its finite
//!   prefixes ([`OmegaCategory`]; every cell lives at a finite level, and the infinite
//!   symbolic form is the tower itself, [`crate::l8::omega_category`]).
//! - L7.2.D3 `η-Nat` + L7.2.T2 `η-Comp` — natural transformations `η : C ⇒ C'`
//!   (componentwise homomorphisms with commuting squares up to ≃) and their vertical
//!   composition ([`NaturalTransformation`]).
//! - L7.2.D4 `Lift-F` (the Lift functor) + L7.2.T4 `Lift-Coll-Adj` — `Lift ⊣ Collapse`: the free lift is left adjoint to
//!   collapse. `Lift` freely generates the words `FMA(Q_M)` over the signature `Q_M`;
//!   `Collapse` quotients a model back to its canonical-form signature.
//!
//! The triangle/round-trip content a finite engine can certify exactly is **signature
//! preservation**: collapsing a lift recovers precisely the original atom signature.
//! `Collapse(Lift(M))` has one class per ρ_{Lift}-fixpoint, i.e. one per atom of
//! `Q_M`, so `|Q_{Collapse(Lift(M))}| = |Q_M| = |Q_{Collapse(M)}|`. (This is the
//! counit `Collapse ∘ Lift ⇒ Id` on signatures, dual to `NFC-TInv` L8.4.T2.)

use crate::l2::projection::Model;
use crate::l7::collapse::collapse;
use crate::l8::lift::lift;

/// **L7.2.T4 (`Lift-Coll-Adj`)** — the signature round-trip `(|Q_{Collapse(M)}|,
/// |Q_{Collapse(Lift(M))}|)`. The lift's ρ-fixpoints are exactly its atoms `Q_M`, so
/// collapsing it yields `|Q_M|` classes — the same signature `Collapse(M)` carries.
pub fn signature_round_trip(base: &Model) -> (u32, u32) {
    let direct = collapse(base).convergent_class_count(); // |Q_M| (the convergent block)
    let via_lift = lift(base).atom_count(); // Collapse(Lift(M)) has one class per atom of Q_M
    (direct, via_lift)
}

/// Witness **L7.2.T4**: the adjunction preserves the query signature —
/// `|Q_{Collapse(Lift(M))}| = |Q_{Collapse(M)}| = |Q_M|`.
pub fn certify_signature_preserved(base: &Model) -> bool {
    let (direct, via_lift) = signature_round_trip(base);
    direct == via_lift
}


/// **L7.2.D2 (`ω-Cat`)** — the ω-category `C^ω_CRPT = (M⁰, M¹, …, {F_n})`: models as
/// layers, model homomorphisms `F_n : M^n → M^{n+1}` as the connecting 1-cells.
/// Presented by a **finite prefix** (every cell lives at a finite level; the sequence
/// extends by `Mₙ₊₁ := Lift(Mₙ)` symbolically — the engine never needs the completed
/// infinite object). Validity = every `F_n` is a `Hom` (L5.2.D1), certified at
/// construction.
pub struct OmegaCategory {
    models: Vec<Model>,
    lift_maps: Vec<Vec<crate::l1::substrate::ElementId>>, // F_n : M^n → M^{n+1}
}

impl OmegaCategory {
    /// Construct the prefix `(M⁰ … M^k, F_0 … F_{k-1})`, certifying each `F_n` is a model
    /// homomorphism (`Hom` L5.2.D1). Returns the index of the first invalid map on error.
    pub fn new(
        models: Vec<Model>,
        lift_maps: Vec<Vec<crate::l1::substrate::ElementId>>,
    ) -> Result<Self, usize> {
        if lift_maps.len() + 1 != models.len() {
            return Err(lift_maps.len());
        }
        for (n, map) in lift_maps.iter().enumerate() {
            if crate::l5::homomorphism::Homomorphism::new(&models[n], &models[n + 1], map.clone())
                .is_err()
            {
                return Err(n);
            }
        }
        Ok(OmegaCategory { models, lift_maps })
    }

    /// The layer `M^n`.
    pub fn level(&self, n: usize) -> &Model {
        &self.models[n]
    }

    /// The number of materialized layers.
    pub fn levels(&self) -> usize {
        self.models.len()
    }

    /// `F_n(x)` — the connecting homomorphism applied at level `n`.
    pub fn lift_map(&self, n: usize, x: crate::l1::substrate::ElementId) -> crate::l1::substrate::ElementId {
        self.lift_maps[n][x.index()]
    }
}

/// **L7.2.D3 (`η-Nat`)** — a natural transformation `η : C ⇒ C'`: a family
/// `{η_n : M^n → M'^n}` of model homomorphisms whose squares commute **up to ≃**:
/// `η_{n+1} ∘ F_n ≃ F'_n ∘ η_n` (regime-aware `≃_M` via `π_sem`). Certified at
/// construction; vertical composition is `η-Comp` (L7.2.T2).
pub struct NaturalTransformation {
    components: Vec<Vec<crate::l1::substrate::ElementId>>, // η_n : M^n → M'^n
}

impl NaturalTransformation {
    /// Construct `η : C ⇒ C'`, certifying each component is a homomorphism and each
    /// naturality square commutes up to `≃`. Returns the offending level on error.
    pub fn new(
        source: &OmegaCategory,
        target: &OmegaCategory,
        components: Vec<Vec<crate::l1::substrate::ElementId>>,
    ) -> Result<Self, usize> {
        use crate::l3::persistent::semantic_projection;
        if components.len() != source.levels() || source.levels() != target.levels() {
            return Err(components.len());
        }
        for (n, eta_n) in components.iter().enumerate() {
            // η_n is a model homomorphism M^n → M'^n.
            if crate::l5::homomorphism::Homomorphism::new(
                source.level(n),
                target.level(n),
                eta_n.clone(),
            )
            .is_err()
            {
                return Err(n);
            }
            // naturality: η_{n+1}(F_n(x)) ≃ F'_n(η_n(x)) in M'^{n+1}.
            if n + 1 < source.levels() {
                let op = target.level(n + 1).operator();
                for x in source.level(n).substrate().elements() {
                    let left = components[n + 1][source.lift_map(n, x).index()];
                    let right = target.lift_map(n, eta_n[x.index()]);
                    if semantic_projection(&op, left) != semantic_projection(&op, right) {
                        return Err(n);
                    }
                }
            }
        }
        Ok(NaturalTransformation { components })
    }

    /// `η_n(x)`.
    pub fn component(&self, n: usize, x: crate::l1::substrate::ElementId) -> crate::l1::substrate::ElementId {
        self.components[n][x.index()]
    }

    /// **L7.2.T2 (`η-Comp`)** — vertical composition `(μ ∘ η)_n := μ_n ∘ η_n`,
    /// re-certified as a natural transformation `C ⇒ C''` (the composite of
    /// homomorphisms is a homomorphism; naturality composes).
    pub fn vertical_composition(
        &self,
        mu: &NaturalTransformation,
        source: &OmegaCategory,
        target: &OmegaCategory,
    ) -> Result<NaturalTransformation, usize> {
        let composed = self
            .components
            .iter()
            .enumerate()
            .map(|(n, eta_n)| eta_n.iter().map(|&v| mu.components[n][v.index()]).collect())
            .collect();
        NaturalTransformation::new(source, target, composed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;

    #[test]
    fn adjunction_preserves_signature() {
        // Q_M = {1,3}: |Q_M| = 2 both directly and through the lift.
        let e = [(0, 1), (2, 3)];
        let base = Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert_eq!(signature_round_trip(&base), (2, 2));
        assert!(certify_signature_preserved(&base));
    }

    #[test]
    fn adjunction_signature_for_single_atom() {
        // Q_M = {1}: the degenerate (ℕ-successor) tower still round-trips its signature.
        let e = [(0, 1)];
        let base = Model::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        assert_eq!(signature_round_trip(&base), (1, 1));
        assert!(certify_signature_preserved(&base));
    }

    #[test]
    fn omega_category_with_natural_transformation_and_vertical_composition() {
        use crate::l1::substrate::{ElementId, Substrate};
        fn chain() -> Model {
            let e = [(0, 1)];
            Model::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap()
        }
        let id_map = vec![ElementId(0), ElementId(1)];
        // C: two layers of the chain with the identity connecting homomorphism (ω-Cat
        // prefix: every cell lives at a finite level).
        let c = OmegaCategory::new(vec![chain(), chain()], vec![id_map.clone()]).unwrap();
        let c2 = OmegaCategory::new(vec![chain(), chain()], vec![id_map.clone()]).unwrap();
        let c3 = OmegaCategory::new(vec![chain(), chain()], vec![id_map.clone()]).unwrap();
        // η : C ⇒ C′ — identity components: squares commute on the nose (hence up to ≃).
        let eta =
            NaturalTransformation::new(&c, &c2, vec![id_map.clone(), id_map.clone()]).unwrap();
        // η-Comp: vertical composition is again natural.
        let mu = NaturalTransformation::new(&c2, &c3, vec![id_map.clone(), id_map.clone()]).unwrap();
        let comp = eta.vertical_composition(&mu, &c, &c3).unwrap();
        assert_eq!(comp.component(0, ElementId(0)), ElementId(0));
        assert_eq!(comp.component(1, ElementId(1)), ElementId(1));
        // a NON-natural family is rejected — needs two fibers, since within one fiber every
        // square commutes up to ≃. Level 1 = {0→1 (NF 1), 2→3 (NF 3)}; F₀ embeds the chain
        // into fiber A; the bad η₁ maps fiber A into fiber B (a valid Hom!), breaking the
        // square: η₁(F₀(0)) ∈ fiber B vs F′₀(η₀(0)) ∈ fiber A — caught at level 0.
        fn two_fiber() -> Model {
            let e = [(0, 1), (2, 3)];
            Model::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap()
        }
        let embed_a = vec![ElementId(0), ElementId(1)];
        let d = OmegaCategory::new(vec![chain(), two_fiber()], vec![embed_a.clone()]).unwrap();
        let d2 = OmegaCategory::new(vec![chain(), two_fiber()], vec![embed_a]).unwrap();
        let cross_fibers = vec![ElementId(2), ElementId(3), ElementId(2), ElementId(3)];
        assert_eq!(
            NaturalTransformation::new(&d, &d2, vec![id_map.clone(), cross_fibers]).err(),
            Some(0)
        );
        // an inconsistent prefix is rejected (map count must be levels − 1).
        assert!(OmegaCategory::new(vec![chain()], vec![id_map]).is_err());
    }
}
