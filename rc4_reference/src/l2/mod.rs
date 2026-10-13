//! # L2 — Projection, Regime, Depth, Canonical Form, and Fibers
//!
//! Spec level **L2** (`CRPT_OMEGA_TOWER_L2.md`, v1.0.0-rc4). Mirroring the tower's
//! structure, submodules realize L2's sections:
//!
//! - [`projection`] — L2.1 "The Reduction Strategy ρ_M".
//! - [`regime`] — L2.2 "Regime Partition" (↓_M ∐ ∞_M).
//! - [`depth`] — L2.3 "Derivation Height d_M".
//! - [`canonical`] — L2.4 "Canonical Normal Form Map" (CNF_M).
//! - [`fiber`] — L2.5 "Normal-Form Fibers and Observable Equivalence" (NFC_M, ≃_M).

pub mod projection; // L2.1
pub mod regime; // L2.2
pub mod depth; // L2.3
pub mod canonical; // L2.4
pub mod fiber; // L2.5
