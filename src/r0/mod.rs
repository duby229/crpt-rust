//! # R0 — Universal Projection Framework
//!
//! Spec rank **R0** (`CRPT_OMEGA_TOWER_R0.md`, v1.0.0-rc9). The universal semantic
//! framework that CRPT rank R1 instantiates: every construct is stated for an arbitrary
//! projection system `Π = (𝒰, π, →_σ)`, before any axiom. CRPT appears only in designated
//! **Instance** theorems (the `CRPT-*` bridges, proved once the instance R1 exists).
//!
//! *Dependencies: none.* R0 precedes and grounds all other ranks.
//!
//! Sections:
//! - [`projection_systems_and_fibers`] — R0.1: `ProjSys`, `Fiber`/`≃_π`, `Obs_π`,
//!   `Fiber-Compl`, `Reify-Mono`, `CRPT-Fiber`.
//! - [`orbit_fate`] — R0.2: `Conv`/`Pers`, `d_π`, `Aspect-Dich`, `Conv-Closed`.
//! - [`horizons`] — R0.3: `H_S^π`/`H_I^π`/`H_O^π`, `sig_π`, boundary layer, `H_I-WD-U`.
//! - [`boolean_stratification`] — R0.4: `Q1`/`Q2`/`Q3`, the six classes `Bool-Strat`,
//!   `Six-Uniq`, Class-F emptiness.
//! - [`universal_inf_dual`] — R0.5: `TowerReify`, `Inf-Dual-U`, `Reify-Quot-Inv`, `CRPT-InfDual`.
//! - [`horizontal_vertical_duality`] — R0.6: `HV-Dual-Static`, `HVDual-InfDual`, `CRPT-HV-Static`.
//! - [`sol_necessity`] — R0.7: `SOL-Nec-U`, `Finite-Collapse`, `CRPT-SOL` (the Knaster–Tarski combinator).
//! - [`stability_classification`] — R0.8: `SC-Form`, `SC-Strat-U`, `CRPT-SC`.
//! - [`projection_category`] — R0.9: `ProjMor`, `ProjSys-Cat`, `CRPT-InstCat`.
//! - [`self_application`] — R0.10: `HOA-Self-Cons`, `CRPT-Self-Cons`.

pub mod projection_systems_and_fibers; // R0.1
pub mod orbit_fate; // R0.2
pub mod horizons; // R0.3
pub mod boolean_stratification; // R0.4
pub mod universal_inf_dual; // R0.5
pub mod horizontal_vertical_duality; // R0.6
pub mod sol_necessity; // R0.7 — Universal SOL Necessity (Knaster–Tarski combinator)
pub mod stability_classification; // R0.8
pub mod projection_category; // R0.9
pub mod self_application; // R0.10
