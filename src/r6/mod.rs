//! # R6 — Abstraction-Quotient and Tower
//!
//! Spec rank **R6** (`CRPT_OMEGA_TOWER_R6.md`, v1.0.0-rc9) — the abstraction-quotient and
//! tower rank, co-defined via the **reification** functor `Reify`. Sections R6.1–R6.13:
//!
//! - [`collapse`] — R6.1: abstraction as epimorphism / collapse (incl. the Galois insertion).
//! - [`categorical_structure`] — R6.2: CRPT's own categorical structure (`Reify ⊣ Collapse`,
//!   the ω-category prefix, natural transformations).
//! - [`crpt_functor`] — R6.3: the CRPT functor and tower structure.
//! - [`free_monoidal_algebra`] — R6.4: `FMA(A)` and the canonical projection.
//! - [`reification_operator`] — R6.5: the **reification** operator `Reify(M)`.
//! - [`nwf_reification`] — R6.8: the NWF-extended `Reify*`.
//! - [`tower`] — R6.7/R6.9/R6.12/R6.13: the tower sequence, `Twr-Growth`, fractality.
//! - [`omega_category`] — R6.10: the tower as a strict ω-category.

pub mod free_monoidal_algebra; // R6.4
pub mod reification_operator; // R6.5
pub mod collapse; // R6.1
pub mod categorical_structure; // R6.2
pub mod crpt_functor; // R6.3
pub mod reification_preservation; // R6.6
pub mod nwf_reification; // R6.8
pub mod tower; // R6.7 / R6.9 / R6.12 / R6.13
pub mod omega_category; // R6.10
pub mod wf_specialization; // R6.11
