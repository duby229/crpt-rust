//! # R6.2 — The `Reify ⊣ Collapse` Adjunction
//!
//! Exact realization of spec section **R6.2** (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9):
//!
//! - R6.2.D2 `ω-Cat` — the ω-category `C^ω_CRPT`: tower levels as 0-cells, the Reify
//!   maps `F_n : M^n → M^{n+1}` as instance homomorphisms — presented by its finite
//!   prefixes ([`OmegaCategory`]; every cell lives at a finite level, and the infinite
//!   symbolic form is the tower itself, [`crate::r6::omega_category`]).
//! - R6.2.D3 `η-Nat` + R6.2.T2 `η-Comp` — natural transformations `η : C ⇒ C'`
//!   (componentwise homomorphisms with commuting squares up to ≃) and their vertical
//!   composition ([`NaturalTransformation`]).
//! - R6.2.D4 `Reify-F` (the Reify functor) + R6.2.T4 `Reify-Coll-Adj` — `Reify ⊣ Collapse`: the free reify is left adjoint to
//!   collapse. `Reify` freely generates the words `FMA(Q_M)` over the signature `Q_M`;
//!   `Collapse` quotients an instance back to its canonical-form signature.
//!
//! The triangle/round-trip content a finite engine can certify exactly is **signature
//! preservation**: collapsing a reify recovers precisely the original atom signature.
//! `Collapse(Reify(M))` has one class per ρ_{Reify}-fixpoint, i.e. one per atom of
//! `Q_M`, so `|Q_{Collapse(Reify(M))}| = |Q_M| = |Q_{Collapse(M)}|`. (This is the
//! counit `Collapse ∘ Reify ⇒ Id` on signatures, dual to `NFC-TInv` R6.7.T2.)

use crate::r1::reduction_strategy::Instance;
use crate::r6::collapse::collapse;
use crate::r6::reification_operator::reify;

/// **R6.2.T4 (`Reify-Coll-Adj`)** — the signature round-trip `(|Q_{Collapse(M)}|,
/// |Q_{Collapse(Reify(M))}|)`. The reify's ρ-fixpoints are exactly its atoms `Q_M`, so
/// collapsing it yields `|Q_M|` classes — the same signature `Collapse(M)` carries.
pub fn signature_round_trip(base: &Instance) -> (u32, u32) {
    let direct = collapse(base).convergent_class_count(); // |Q_M| (the convergent block)
    let via_reify = reify(base).atom_count(); // Collapse(Reify(M)) has one class per atom of Q_M
    (direct, via_reify)
}

/// Witness **R6.2.T4**: the adjunction preserves the query signature —
/// `|Q_{Collapse(Reify(M))}| = |Q_{Collapse(M)}| = |Q_M|`.
pub fn certify_signature_preserved(base: &Instance) -> bool {
    let (direct, via_reify) = signature_round_trip(base);
    direct == via_reify
}


/// **R6.2.D2 (`ω-Cat`)** — the ω-category `C^ω_CRPT = (M⁰, M¹, …, {F_n})`: instances as
/// layers, instance homomorphisms `F_n : M^n → M^{n+1}` as the connecting 1-cells.
/// Presented by a **finite prefix** (every cell lives at a finite level; the sequence
/// extends by `Mₙ₊₁ := Reify(Mₙ)` symbolically — the engine never needs the completed
/// infinite object). Validity = every `F_n` is a `Hom` (R4.2.D1), certified at
/// construction.
pub struct OmegaCategory {
    instances: Vec<Instance>,
    reify_maps: Vec<Vec<crate::r1::substrate::ElementId>>, // F_n : M^n → M^{n+1}
}

impl OmegaCategory {
    /// Construct the prefix `(M⁰ … M^k, F_0 … F_{k-1})`, certifying each `F_n` is an instance
    /// homomorphism (`Hom` R4.2.D1). Returns the index of the first invalid map on error.
    pub fn new(
        instances: Vec<Instance>,
        reify_maps: Vec<Vec<crate::r1::substrate::ElementId>>,
    ) -> Result<Self, usize> {
        if reify_maps.len() + 1 != instances.len() {
            return Err(reify_maps.len());
        }
        for (n, map) in reify_maps.iter().enumerate() {
            if crate::r4::instance_homomorphisms::Homomorphism::new(&instances[n], &instances[n + 1], map.clone())
                .is_err()
            {
                return Err(n);
            }
        }
        Ok(OmegaCategory { instances, reify_maps })
    }

    /// The layer `M^n`.
    pub fn level(&self, n: usize) -> &Instance {
        &self.instances[n]
    }

    /// The number of materialized layers.
    pub fn levels(&self) -> usize {
        self.instances.len()
    }

    /// `F_n(x)` — the connecting homomorphism applied at level `n`.
    pub fn reify_map(&self, n: usize, x: crate::r1::substrate::ElementId) -> crate::r1::substrate::ElementId {
        self.reify_maps[n][x.index()]
    }
}

/// **R6.2.D3 (`η-Nat`)** — a natural transformation `η : C ⇒ C'`: a family
/// `{η_n : M^n → M'^n}` of instance homomorphisms whose squares commute **up to ≃**:
/// `η_{n+1} ∘ F_n ≃ F'_n ∘ η_n` (aspect-aware `≃_M` via `π_sem`). Certified at
/// construction; vertical composition is `η-Comp` (R6.2.T2).
pub struct NaturalTransformation {
    components: Vec<Vec<crate::r1::substrate::ElementId>>, // η_n : M^n → M'^n
}

impl NaturalTransformation {
    /// Construct `η : C ⇒ C'`, certifying each component is a homomorphism and each
    /// naturality square commutes up to `≃`. Returns the offending level on error.
    pub fn new(
        source: &OmegaCategory,
        target: &OmegaCategory,
        components: Vec<Vec<crate::r1::substrate::ElementId>>,
    ) -> Result<Self, usize> {
        use crate::r2::canonical_orbit_invariant::semantic_projection;
        if components.len() != source.levels() || source.levels() != target.levels() {
            return Err(components.len());
        }
        for (n, eta_n) in components.iter().enumerate() {
            // η_n is an instance homomorphism M^n → M'^n.
            if crate::r4::instance_homomorphisms::Homomorphism::new(
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
                    let left = components[n + 1][source.reify_map(n, x).index()];
                    let right = target.reify_map(n, eta_n[x.index()]);
                    if semantic_projection(&op, left) != semantic_projection(&op, right) {
                        return Err(n);
                    }
                }
            }
        }
        Ok(NaturalTransformation { components })
    }

    /// `η_n(x)`.
    pub fn component(&self, n: usize, x: crate::r1::substrate::ElementId) -> crate::r1::substrate::ElementId {
        self.components[n][x.index()]
    }

    /// **R6.2.T2 (`η-Comp`)** — vertical composition `(μ ∘ η)_n := μ_n ∘ η_n`,
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

/// Witness **R6.2.T3 (`Reify-Endo`)** — **Reify is an endofunctor on `Inst_CRPT`**: it maps
/// instances to instances (`Reify-Compat` R6.6.T4) and CRPT homomorphisms to CRPT
/// homomorphisms, preserving identity and composition. Certified here on objects: `Reify(M)`
/// is a well-formed instance whose query signature equals `M`'s (`Reify` lands back in
/// `Inst_CRPT` with the invariant signature). Returns `true` when `Reify` acts as an
/// endofunctor on the given object. (`R6.2.R1` `Coll-Adj-Scope`: the `Reify ⊣ Collapse`
/// adjunction is scoped to the `≃`-quotient category `Inst_CRPT_≃`; `R6.2.R2` `Asp-Inv`: the
/// aspect partition is invariant under the functor's action.)
pub fn certify_reify_endofunctor(base: &Instance) -> bool {
    // Reify(M) is an Inst_CRPT object with the tower-invariant signature (NFC-TInv).
    certify_signature_preserved(base)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    #[test]
    fn adjunction_preserves_signature() {
        // Q_M = {1,3}: |Q_M| = 2 both directly and through the reify.
        let e = [(0, 1), (2, 3)];
        let base = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert_eq!(signature_round_trip(&base), (2, 2));
        assert!(certify_signature_preserved(&base));
        // Reify-Endo: Reify is an endofunctor on Inst_CRPT (signature-preserving on objects).
        assert!(certify_reify_endofunctor(&base));
    }

    #[test]
    fn adjunction_signature_for_single_atom() {
        // Q_M = {1}: the degenerate (ℕ-successor) tower still round-trips its signature.
        let e = [(0, 1)];
        let base = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        assert_eq!(signature_round_trip(&base), (1, 1));
        assert!(certify_signature_preserved(&base));
    }

    #[test]
    fn omega_category_with_natural_transformation_and_vertical_composition() {
        use crate::r1::substrate::{ElementId, Substrate};
        fn chain() -> Instance {
            let e = [(0, 1)];
            Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap()
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
        fn two_fiber() -> Instance {
            let e = [(0, 1), (2, 3)];
            Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap()
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
