//! # Rω — Meta-CRPT: The Theory Applied to Itself
//!
//! Spec rank **Rω** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9) — the terminal rank, where the
//! full CRPT apparatus (the HOA, the six-class partition, the ω-tower) is applied to the
//! CRPT anchor **itself** as an object. The anchor content, organized by logical
//! dependency, forms a projection system to which CRPT's own machinery applies — so this
//! rank is realized by running [`r1`](crate::r1)/[`r2`](crate::r2)/[`r6`](crate::r6) on a
//! concrete *self-instance* built from the tower's own dependency DAG. Depends on R0–R6.
//!
//! Sections:
//! - [`self_projection_system`] — Rω.1: the self-substrate `𝒰_CRPT` (`U_CRPT`); the
//!   `Self-Model` theorem (a valid CRPT instance, pure-WF on the dependency reading); and the
//!   **dual self-model** — `Self-Inf` (`∞_CRPT^σ ≠ ∅`, the structural NWF aspect), `Self-Mixed`
//!   (the self-model is Mixed: WF under `ρ`, NWF under `σ`), `Self-InfDual` (`Inf-Dual` at the
//!   self level).
//! - [`self_horizon`] — Rω.2: `Self-Horiz` — the six-class partition of the anchor (R1.1.D1
//!   is Class E; the rank carriers are Class B).
//! - [`rank_ordering`] — Rω.3: `m_CRPT` — the rank of a construct = its derivation height.
//! - [`tower_of_towers`] — Rω.4: `Tower-of-Towers` — Reify applied to the self-substrate.
//! - [`meta_tower_fixpoint`] — Rω.5: `Self-FP` — the level structure is the unique fixed
//!   point of the meta-HOA (the theory closes without regress).
//! - [`anchor_fractality`] — Rω.6: `Anchor-Fractal` — the anchor is the fractal it describes.
//! - [`supplementary_lemmas`] — Rω.7: `CRPT-Acyclic`, `Self-CRPT-Finite`, `CRPT-WF`,
//!   `Rω-FixedPt-Unique`.
//! - [`self_sectioning`] — Rω.8: `Spec-Sub`, `Self-Sect` (sections are fibers), `Spec-Depth`,
//!   `Rank-vs-Depth`, `Status`, `Sameness`, `Fiber-Unif`.
//! - [`import_substrate`] — Rω.9: `Imp-Sub`, `Ax-Map`, `Imp-Track`, `Imp-Reify`.

pub mod self_projection_system; // Rω.1
pub mod self_horizon; // Rω.2
pub mod rank_ordering; // Rω.3
pub mod tower_of_towers; // Rω.4
pub mod meta_tower_fixpoint; // Rω.5
pub mod anchor_fractality; // Rω.6
pub mod supplementary_lemmas; // Rω.7
pub mod self_sectioning; // Rω.8
pub mod import_substrate; // Rω.9
