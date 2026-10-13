//! # R4 — Instance / Instance Algebra
//!
//! Spec rank **R4** (`CRPT_OMEGA_TOWER_R4.md`, v1.0.0-rc9) — the former L5. The algebra
//! and category of CRPT **instances**, and the instance-theory correspondence.
//!
//! Sections:
//! - [`instance_algebra`] — R4.1: `CRPT-Inst-18`, `Inst-∩` (a **partial meet**),
//!   `Inst-×`/`×-Mon`, `Inst-/`, `Inst-∪`, `Dist-Laws`.
//! - [`instance_homomorphisms`] — R4.2: `Hom`, `Iso`, `Inst-Emb`, `A-Iso`/`A-Iso∞`, the
//!   category `Inst_CRPT`.
//! - [`model_correspondence`] — R4.3: the CRPT theory `T_CRPT` and the Tarski
//!   instance-correspondence (`⊧`, `Mod-Corr`, `FOL-Fin`). **This is the one locus that keeps
//!   "instance"**: here instances are *proven to be instances* of `T_CRPT`.
//! - [`instance_order`] — R4.4: the instance order, refinement, and faithful embedding.
//! - [`category_of_instances`] — R4.5: the category laws (`Id-Mor`, `Comp-Closed`,
//!   `Cat-Laws`).

pub mod instance_algebra; // R4.1
pub mod instance_homomorphisms; // R4.2
pub mod model_correspondence; // R4.3
pub mod instance_order; // R4.4
pub mod category_of_instances; // R4.5 — Inst_CRPT category laws
