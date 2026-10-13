//! # L0 — Universal Projection Framework
//!
//! Spec level **L0** (`CRPT_OMEGA_TOWER_L0.md`, v1.0.0-rc4): the *universal* projection
//! framework that CRPT instantiates. L0 develops the foundational structure — projection
//! systems, fibers, observable equivalence, regimes, horizons — before any axiom, at full
//! generality; the concrete CRPT model (L1–L8) is then an **instance** of it.
//!
//! rc2/rc3 exclude L0 from `𝒰_CRPT` (it is the external template, not a construct of the
//! tower). The engine realizes it as the design's *one* universal interface (a trait the
//! CRPT operator implements), per the trait-placement decision (`docs/BUILD_PLAN.md`):
//!
//! - [`projection_system`] — L0.1 the projection system `Π = (𝒰, π, →_σ)`, the fiber
//!   `L_π` and observable equivalence `≃_π`, π-observability, realized as the
//!   `ProjectionSystem` trait that [`crate::l2::projection::ProjectionOperator`]
//!   implements (π = ρ_M, `CNF_π` = `CFix`) — so `CRPT-Fiber` (L0.1.T3) is a verifiable
//!   instance, not an assumption.
//!
//! The other L0 universals are realized by their CRPT instances: L0.5.D1 `TowerLift` is
//! realized *literally* — [`crate::l8::lift::Lift`] implements the same
//! [`projection_system::ProjectionSystem`] trait (the lift of a projection system **is** a
//! projection system); L0.8.D1 `SC-Form` ↔ the topological limit
//! ([`crate::l1::topology`]); L0.9.D1 `ProjMor` ↔ the homomorphism (L5.2). Further:
//! L0.2 regimes ↔ L2.2 (`↓_M`/`∞_M`), L0.3 horizons ↔ L3.1, L0.4 six-class ↔ L3.2,
//! L0.7.T2 `Finite-Collapse` ↔ the engine's finite-decidability throughout.

pub mod projection_system; // L0.1
pub mod sol_necessity; // L0.7 — Universal SOL Necessity (the Knaster–Tarski combinator)
