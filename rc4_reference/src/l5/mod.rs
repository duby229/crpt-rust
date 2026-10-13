//! # L5 — Model Algebra, Homomorphisms, and Model Order
//!
//! Spec level **L5** (`CRPT_OMEGA_TOWER_L5.md`, v1.0.0-rc4). Submodules:
//!
//! - [`algebra`] — L5.1 model algebra (product ×/∘, the unit model 𝟙).
//! - [`homomorphism`] — L5.2 model homomorphisms (Φ_R, Φ_E, Φ_ρ, Φ_LA) and `Mod_CRPT`.
//! - [`conformance`] — L5.3 the `T_CRPT` conformance verdict (`Mod-Corr`/`FOL-Fin`):
//!   whether a `Model` actually *is* a CRPT model.
//! - [`order`] — L5.4 the model orders ⊑ (refinement) and ⪯ (expressiveness).

pub mod algebra; // L5.1
pub mod homomorphism; // L5.2
pub mod conformance; // L5.3
pub mod order; // L5.4
