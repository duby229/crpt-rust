//! # R3 — The Observer
//!
//! Spec rank **R3** (`CRPT_OMEGA_TOWER_R3.md`, v1.0.0-rc9) — the former L4. What can be
//! *observed* about an element from its `ρ_M`-orbit: the observable triple, gateway
//! structure, the projection valuation, the duality theorems (incl. `Fold-Unfold`), the
//! inversion horizon, self-projection, and coherent perturbation.
//!
//! Sections:
//! - [`observable_triple`] — R3.1: `Behav-F`, `PV-Obs`/`HC-Obs`/`AD-Obs`, `Obs-Triple`,
//!   `Obs-Const`/`Obs-Nat`/`Obs-Pres`.
//! - [`gateway`] — R3.2: aspect reachability / gateway structure.
//! - [`projection_valuation`] — R3.3: the projection valuation `PV`.
//! - [`duality_theorems`] — R3.4: the duality theorems (incl. `Fold-Unfold`).
//! - [`projection_depth`] — R3.5: projection depth and the inversion horizon.
//! - [`self_projection`] — R3.6: self-projection and the admissible encoding `Enc`.
//! - [`coherent_perturbation`] — R3.7: coherent perturbation.

pub mod observable_triple; // R3.1
pub mod gateway; // R3.2
pub mod projection_valuation; // R3.3
pub mod duality_theorems; // R3.4
pub mod projection_depth; // R3.5
pub mod self_projection; // R3.6
pub mod coherent_perturbation; // R3.7
