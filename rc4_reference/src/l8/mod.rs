//! # L8 — Tower, Horizontal-Vertical Duality, Fractality
//!
//! Spec level **L8** (`CRPT_OMEGA_TOWER_L8.md`, v1.0.0-rc4). The generative core.
//! Submodules:
//!
//! - [`fma`] — L8.1 the free monoidal algebra FMA(A) (words over an atom set).
//! - [`lift`] — L8.2 the Lift operator `Lift(M) = (FMA(Q_M), ρ_Lift, …)`, represented
//!   *symbolically* (its universe is infinite), with fixpoints-to-basics and
//!   `d_Lift(w) = |w|−1`.
//! - [`lift_inf`] — L8.5 the NWF-extended lift `Lift∞(M)` over `Q_M ⊔ Q_M*`: persistent
//!   classes become periodic atoms of period `CPD(σ)` (so `Lift∞` satisfies PA-NWF).
//! - [`tower`] — L8.4/L8.9/L8.10 the Tower, the query-signature invariant (NFC-TInv),
//!   Tower-Inf, and pure-WF-ness of each lift.
//!
//! **Two post-rc2 engine findings, now resolved in rc3** (and matching this engine):
//! 1. **FMA depth** (L8.1.D1) is the flat word-length grading `depth(w) = |w| − 1` (the
//!    binary-tree `1+max` reading is gone). The engine uses `|w| − 1`.
//! 2. **Strip convention** (L8.1.D2 / L2) is standardized: strip the **last atom** each
//!    step, so `CFix` = the **first atom**. The engine implements exactly this.

pub mod fma; // L8.1
pub mod lift; // L8.2
pub mod lift_inf; // L8.5
pub mod omega_category; // L8.7
pub mod tower; // L8.4 / L8.9 / L8.10
