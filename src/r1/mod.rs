//! # R1 — The Projection Substrate
//!
//! Spec rank **R1** (`CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9) — the merge of the former L1
//! (substrate + axioms) and L2 (the projection strategy ρ_M), co-defined via Mode. R1
//! instantiates the universal framework R0 with the concrete CRPT substrate
//! `(𝒰, →_ρ, →_σ, 𝒯)` and the deterministic reduction strategy `ρ_M`.
//!
//! Sections (R1.1–R1.12):
//! - [`substrate`] — R1.1: `Sub`, `NF`, `n-Step`/`RT*`, `Div`, the labelled bisimulation
//!   `≈` (`Bisim`/`Bisim~`), the derived observation labelling `Obs-Lab`, and `Min-Interp`.
//! - [`reduction_strategy`] — R1.8: `ρ_M` (C1/C2/C3), `Fix`/`NF=Fix`, `Rec-Proj` (CFix),
//!   and the owned [`reduction_strategy::Instance`].

pub mod substrate; // R1.1
pub mod reduction_strategy; // R1.8 — ρ_M, the projection operator, and the Instance
pub mod aspect_partition; // R1.9 — ↓_M/∞_M, closure, Part, Inf-Dual (statement)
pub mod derivation_height; // R1.10 — ≤_ρ, d_M
pub mod canonical_form; // R1.11 — CNF_M map, Abs=RP
pub mod fibers; // R1.12 — NFC-NM, ≃_M, the abstraction quotient Q_M
pub mod axiom_system; // R1.2 — the aspect-local step axioms (PA-WN/Conf/Fix/NWF/Prod)
pub mod aspects_and_modes; // R1.4 — Mode (Recurrence/Convergence), Mode-Comp
pub mod topology; // R1.7 — the substrate topology 𝒯 (TopSep/Top-Lim/PA-WN_top)
pub mod instance_profiles; // R1.5 — PA-Scope, LA_M, SC-Orb, Scope-Suf
pub mod minimality; // R1.6 — Ax-Ind independence matrix, No-Split
pub mod universal_axioms; // R1.3 — PA-Bisim, PA-Reach (meaning form), CPer, realizations
