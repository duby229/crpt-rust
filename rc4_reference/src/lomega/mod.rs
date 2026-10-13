//! # Lω — Self-Application
//!
//! Spec level **Lω** (`CRPT_OMEGA_TOWER_Lomega.md`, v1.0.0-rc4): CRPT applied to
//! itself. rc2 (`Lω.5.R2`) confirmed self-application is *not generative* for the
//! engine's module layout — so this level is **diagnostic**, not constructive.
//!
//! - [`self_application`] — Lω.5 the self-conformance test: feed the engine its own
//!   construct-dependency graph in as a substrate, build it as a CRPT [`Model`], and
//!   certify it is a **pure-WF** model — acyclic, with the unique root `L1.1.D1`
//!   (the substrate) that every construct reduces to, and `∞_CRPT = ∅`.
//!
//! [`Model`]: crate::l2::projection::Model

pub mod self_application; // Lω.5
