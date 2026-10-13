//! # L4 — Observer, Gateway, Valuation
//!
//! Spec level **L4** (`CRPT_OMEGA_TOWER_L4.md`, v1.0.0-rc4). Submodules:
//!
//! - [`valuation`] — L4.3 the value semiring and projection valuation PV.
//! - [`observer`] — L4.1 the observer triple 𝒪 = (PV, H, D).
//! - [`gateway`] — L4.2 the gateway predicate GW and regime reachability.
//! - [`duality`] — L4.4 the regime fixpoint operators (↓_M = μT_conv, ∞_M = νT_pers).
//! - [`projection_depth`] — L4.5 the co-projection depth CPD and co-inversion horizon.
//! - [`self_projection`] — L4.6 the self-projection fixpoint (SP-2).
//! - [`perturbation`] — L4.7 the ρ_M-perturbation notion and CPEP detectability.

pub mod valuation; // L4.3
pub mod observer; // L4.1
pub mod gateway; // L4.2
pub mod duality; // L4.4
pub mod projection_depth; // L4.5
pub mod self_projection; // L4.6
pub mod perturbation; // L4.7
