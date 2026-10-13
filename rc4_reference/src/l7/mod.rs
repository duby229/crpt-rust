//! # L7 — Categorical Collapse, Functoriality, and Model-Theory Fibration
//!
//! Spec level **L7** (`CRPT_OMEGA_TOWER_L7.md`, v1.0.0-rc4). Submodules:
//!
//! - [`collapse`] — L7.1 the Collapse operator (quotient by ≃_M to a pure-WF model)
//!   and the collapse map κ.
//! - the Galois insertion (in [`collapse`]) — L7.1 the Galois insertion α_M ⊣ γ_M (abstraction ⊣ concretisation).
//! - [`adjunction`] — L7.2 the `Lift ⊣ Collapse` adjunction (signature round-trip).
//! - [`functor`] — L7.3 the CRPT functor F : Mod_CRPT → ω-Cat (model ↦ Tower(M)).

pub mod adjunction; // L7.2
pub mod collapse; // L7.1 — Abstraction as Epimorphism / Collapse (incl. the Galois insertion)
pub mod functor; // L7.3
