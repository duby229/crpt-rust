//! # L3 — Horizon, Classification, and Persistent Canonical Invariants
//!
//! Spec level **L3** (`CRPT_OMEGA_TOWER_L3.md`, v1.0.0-rc4). Submodules realize
//! L3's sections:
//!
//! - [`horizon`] — L3.1 horizon predicates H_S, H_I, H_O, kernel, orbit signature.
//! - [`classification`] — L3.2 the six-class partition A–F (F = ∅) on ↓_M.
//! - [`persistent`] — L3.3 the persistent canonical invariants: ω-limit set, `≃∞`,
//!   the persistent orbit quotient `Q∞_M` (the ∞_M counterpart of `≃_M`/`Q_M`).
//!
//! The persistent classification proper is the NWF six-class A*–F* in
//! [`crate::l6::nwf_horizon`] (L6.4). The signature-stabilization dual `n_M`/`CPer`
//! (L3.3.D10) rests on the topological `sig_M-NM` (L3.1.D5) and is deferred with the
//! `PA-WN_top` tier.

pub mod horizon; // L3.1
pub mod classification; // L3.2
pub mod persistent; // L3.3
