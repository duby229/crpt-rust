//! # R2 — Horizon and Classification
//!
//! Spec rank **R2** (`CRPT_OMEGA_TOWER_R2.md`, v1.0.0-rc9) — the former L3. The CRPT
//! *instance* horizon theory: the kernel-based horizons `H_S`/`H_I`/`H_O` (the R2
//! specialization of R0.3's universal fiber-based forms, related by `CRPT-Horiz`), the
//! six/twelve-class partition, and the persistent canonical invariant `CNF∞_M`.
//!
//! Sections:
//! - [`orbit_signature_and_horizons`] — R2.1: `H_S`/`H_I`/`H_O`, `Ker-Cong`, `sig_M`/
//!   `sig_M-NM`, `HP`, `H_I-WD`/`H_I-Dec`/`H_I-KernelLocal`.

pub mod orbit_signature_and_horizons; // R2.1
pub mod six_class_horizon_partition; // R2.2 — six-class + twelve-class (12-Part)
pub mod canonical_orbit_invariant; // R2.3 — CNF∞_M, ω-limit, ≃∞, Q∞, n-Reach
