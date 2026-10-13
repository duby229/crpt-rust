//! # R5 — Persistent Orbit Invariants
//!
//! Spec rank **R5** (`CRPT_OMEGA_TOWER_R5.md`, v1.0.0-rc9) — the former L6. The asymptotic
//! analysis layer: invariants *about* persistent orbits (the AOI), defined unconditionally
//! and finitely presentable in either mode (it is **not** a mode — R1.4).
//!
//! Sections:
//! - [`asymptotic_orbit_invariants`] — R5.1: the AOI (`OT`, `OS`, `OC`).
//! - [`orbit_type_classification`] — R5.2: orbit-type {P, EP, AP} + the three tiers.
//! - [`aoi_full_proofs`] — R5.3: `Rec-Set`/`Freq`/`OS`/`OC`/`SC-k` and the full proofs.
//! - [`nwf_horizon_partition`] — R5.4: the NWF six-class A\*–F\*.
//! - [`aspect_type_determinacy`] — R5.5: aspect-type determinacy (`ATD-Und` R5.5.T3).
//! - [`instance_classification`] — R5.6: instance classification and degeneracy.

pub mod asymptotic_orbit_invariants; // R5.1
pub mod orbit_type_classification; // R5.2
pub mod aoi_full_proofs; // R5.3
pub mod nwf_horizon_partition; // R5.4
pub mod aspect_type_determinacy; // R5.5
pub mod instance_classification; // R5.6
