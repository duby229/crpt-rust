//! # crpt_engine
//!
//! The CRPT ω-Tower implemented **exactly** — construct for construct, as written
//! in the specification (sole source of truth: `../CRPT_OMEGA_TOWER_`, v1.0.0-rc4).
//! This crate does not approximate or resemble CRPT; each item corresponds to a
//! specific labelled spec construct, cited by label, realizing its literal
//! definition.
//!
//! **Structure = the tower's structure.** The module hierarchy mirrors the spec
//! exactly: a module per level (`l0`–`l8`, `lomega`), and within each level a
//! submodule per section. L0 is the *external* Universal Projection Framework that
//! CRPT instantiates (rc2+: excluded from 𝒰_CRPT); it surfaces as the
//! [`l0::projection_system::ProjectionSystem`] trait the CRPT operator implements.
//!
//! **Scope.** One notion, every substrate: a single [`ProjectionSystem`] trait
//! (L0.1.D1 `ProjSys`) covers the finite operator `ρ_M`, the infinite `Lift(M)`
//! (`TowerLift` L0.5.D1: the lift of a projection system *is* a projection
//! system), and the topological tier — recursive projection all the way up
//! (`Rec-Proj` L2.1.D4; the tower is fractal, L8.9). On **finite** substrates
//! ([`FiniteProjectionSystem`]) the theory is fully decidable (`Finite-Collapse`
//! L0.7.T2; `FOL-Fin` L5.3.T4): bisimilarity, reachability, and divergence are
//! exact finite computations. Infinite substrates are computed symbolically from
//! their finite presentations (`Inf-Dual` L2.2.T7), never by enumeration.
//!
//! **Equality & determinism.** Equality is CRPT's own (mathematical identity `=`,
//! bisimilarity ≈, observable equivalence ≃_M) — not blanket-derived structural
//! equality; no hashing, no `Ord`-keyed maps; dense-indexed representations; clone
//! is avoided. See `docs/DETERMINISM_CONTRACT.md`.

#![forbid(unsafe_code)]

pub mod l0; // L0 — Universal Projection Framework (the interface CRPT instantiates)
pub mod l1; // L1 — Substrate, Axioms, Regimes, and Modes
pub mod l2; // L2 — Projection, Regime, Depth, Canonical Form, and Fibers
pub mod l3; // L3 — Horizon, Classification, and Persistent Canonical Invariants
pub mod l4; // L4 — Observer, Gateway, Valuation
pub mod l5; // L5 — Model Algebra, Homomorphisms, and Model Order
pub mod l6; // L6 — Native Non-Well-Founded Mode
pub mod l7; // L7 — Categorical Collapse, Functoriality, and Model-Theory Fibration
pub mod l8; // L8 — Tower, Horizontal-Vertical Duality, Fractality
pub mod lomega; // Lω — Self-Application

pub use l0::projection_system::{FiniteProjectionSystem, ProjectionSystem};
pub use l1::axioms::{axiom_profile, canonical_persistent_representative, pa_reach, AxiomProfile};
pub use l1::mode::{canonicalization_mode, Mode};
pub use l1::topology::{ChainPoint, ConvergentChain, TopologicalProjectionSystem};
pub use l1::profile::{
    axiom_scope_profile, local_axioms_hold, sc_orb, AxiomScopeProfile, LocalAxiom, Scope,
    ScopeSet,
};
pub use l1::substrate::{ElementId, Substrate, SubstrateError};
pub use l2::depth::DerivationHeight;
pub use l2::projection::{Model, ProjectionError, ProjectionOperator};
pub use l2::regime::Regime;
pub use l3::classification::{
    persistent_classify, twelve_classify, HorizonClass, PersistentHorizonClass, TwelveClass,
};
pub use l3::horizon::{
    horizon_profile, observation_trace, persistent_orbit_signature, HorizonProfile,
    OrbitSignature, PersistentOrbitSignature,
};
pub use l6::degeneracy::{degeneracy, is_degenerate, DegeneracyReport};
pub use l3::persistent::{n_reach, SemanticValue};
pub use l4::duality::{greatest_fixpoint_persistent, least_fixpoint_convergent};
pub use l4::valuation::{
    finite_reduction_histories, infinite_reduction_history, pv_infinity, DiscreteLimit,
};
pub use l6::orbit_type::{analysis_tier, AnalysisTier};
pub use l4::perturbation::{is_absorbing, is_perturbation, is_reflective, persistent_detectable};
pub use l5::order::{is_regime_isomorphism, is_regime_isomorphism_infinity};
pub use l4::projection_depth::{canonical_period, co_inversion_horizon};
pub use l6::aoi::{aoi1, orbit_trace, OrbitTrace};
pub use l6::aoi_full_proofs::{
    aoi_hierarchy_terminates_at, aoi_unified, complexity_class, orbit_complexity,
    orbit_spectrum, recurrence_set, recurrence_type, sc_infinity, ComplexityClass, Frequency,
    OrbitComplexity, RecurrenceSet, RecurrenceTypeReport, UnifiedAoi,
};
pub use l6::orbit_type::certify_aperiodic_prefix;
pub use l6::nwf_horizon::{nwf_classify, NwfClass};
pub use l6::orbit_type::OrbitType;
pub use l6::regime_type::RegimeType;
pub use l4::observer::{ObserverTriple, WellFoundedness};
pub use l4::self_projection::{
    certify_enc_compositional, certify_enc_injective, certify_enc_nwf_faithful,
    certify_enc_wf_faithful, denotationally_equal, term_denotation, AdmissibleEncoding, Term,
};
pub use l4::valuation::Semiring;
pub use l5::algebra::{identity_model, intersection, product, quotient, union};
pub use l5::conformance::{
    certify_tarski_agrees_with_native, conforms, is_crpt_model, is_l_homomorphism,
    satisfies, satisfies_relativized, satisfies_theory, scope_aware_satisfaction,
    Conformance, Formula, SigmaTerm,
};
pub use l5::homomorphism::{Homomorphism, HomomorphismError};
pub use l7::adjunction::{NaturalTransformation, OmegaCategory};
pub use l7::collapse::{collapse, Collapse, quotient_projection};
pub use l7::functor::{crpt_functor_object, induced_signature_map};
pub use l7::collapse::{abstraction, concretization, infinity_abstraction};
pub use l8::lift::{lift, Lift};
pub use l8::omega_category::{
    certify_strict_axioms, identity_cell, left_whisker, vertical_compose, PathCell,
};
pub use l8::lift_inf::{lift_inf, LiftInf, PersistentAtom};
pub use l8::tower::{tower, Tower};
