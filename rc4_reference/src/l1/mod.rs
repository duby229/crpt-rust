//! # L1 — CRPT Substrate, Axioms, Regimes, and Modes
//!
//! Spec level **L1** (`CRPT_OMEGA_TOWER_L1.md`, v1.0.0-rc4). The engine mirrors
//! the tower's structure exactly: this module is level L1, and its submodules are
//! L1's sections.
//!
//! - [`substrate`] — L1.1 "The Substrate" (axiom-free base).
//! - [`axioms`] — L1.2/L1.3 the nine PA-* projection axioms as checkable constraints
//!   (the constraints that make a C1/C2-valid model an actual CRPT model).
//! - [`mode`] — L1.4 the two canonicalization modes (recurrence / convergence; rc4 —
//!   the AOI is the analysis layer, not a mode).
//! - [`profile`] — L1.5 the PA-* scope system (Global / Scoped(S) / Vacuous / Fails).
//! - [`topology`] — L1.1.D1 (𝒯) / L1.2.Ax7 (PA-WN_top): the symbolic *topological tier*
//!   (infinite universes with 𝒯-limits), where topological mode is inhabited.

pub mod substrate; // L1.1 — The Substrate
pub mod axioms; // L1.2 / L1.3 — The Projection Axiom System
pub mod mode; // L1.4 — Canonicalization Modes
pub mod profile; // L1.5 — Model Axiom Profiles
pub mod topology; // L1.1.D1 𝒯 / L1.2.Ax7 PA-WN_top — the topological tier
