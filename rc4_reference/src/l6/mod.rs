//! # L6 — Native Non-Well-Founded Mode
//!
//! Spec level **L6** (`CRPT_OMEGA_TOWER_L6.md`, v1.0.0-rc4): the persistent regime
//! ∞_M analysed *natively*, without assuming topological convergence (PA-WN_top).
//! Submodules:
//!
//! - [`orbit_type`] — L6.2 the unconditional orbit-type classification of ∞_M into
//!   Type P / Type EP / Type AP (Tier 1, requires only PA-NWF + PA-Bisim).
//! - [`regime_type`] — L6.5 regime-type determinacy: WF / NWF / Mixed, decidable for
//!   finite substrates.
//! - [`nwf_horizon`] — L6.4 the NWF six-class partition A*–F* (asymptotic-invariant form:
//!   `≈`, `≃∞`, `CPD`), with Class F* provably empty.
//! - [`aoi`] — L6.1 the asymptotic orbit invariants: orbit trace OT, `AOI₁`, orbit
//!   spectrum OS, orbit complexity OC.
//!
//! **Finite-substrate fact.** The bisimulation quotient 𝒰_M/≈ is finite, so every
//! ρ_M-orbit visits finitely many classes — SC-4 holds for *every* ∞_M element. Hence
//! **Type AP is empty on finite substrates** (it requires an infinite quotient orbit),
//! the finite analogue of `AP-Irred` (L6.2.T3); the orbit type is decided exactly by
//! `|ω_≈(x)|` (`RTD-Dec` L6.5.T2, regime type decidable for finite substrates).

pub mod aoi; // L6.1
pub mod orbit_type; // L6.2
pub mod aoi_full_proofs; // L6.3
pub mod nwf_horizon; // L6.4
pub mod regime_type; // L6.5
pub mod degeneracy; // L6.6
