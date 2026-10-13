//! # crpt_engine
//!
//! The CRPT ω-Tower implemented **exactly** — construct for construct, as written in the
//! specification (sole source of truth: `../CRPT_OMEGA_TOWER_`, **v1.0.0-rc9**). This crate
//! does not approximate or resemble CRPT; each item realizes a specific labelled spec
//! construct, cited by its R-label.
//!
//! **Structure = the specification's structure.** The spec is organized into **eight
//! genuine ranks** (`R0`–`R6`, `Rω` — its own CRPT-rank, the document strata). The module
//! hierarchy mirrors them exactly: one module per rank, and within each rank one submodule
//! per section `R#.s`, named by the section's meaning. There is no module that is not a
//! spec section, and no aliasing.
//!
//! - [`r0`] — Universal Projection Framework (the universal `Π = (𝒰, π, →_σ)` template).
//! - [`r1`] — The Projection Substrate (substrate, the nine PA-* axioms, modes, `ρ_M`,
//!   aspects, `d_M`, CNF, fibers).
//! - [`r2`] — Horizon and Classification (`sig_M`, horizons, six/twelve-class, `CNF∞_M`).
//! - [`r3`] — The Observer (observable triple, gateway, projection valuation, dualities,
//!   projection depth, self-projection, coherent perturbation).
//! - [`r4`] — Instance Algebra & Model Theory (`Inst-∩/×///∪`, homomorphisms, the category
//!   `Inst_CRPT`, the Tarski model-correspondence — the one locus that keeps "model").
//! - [`r5`] — Persistent Orbit Invariants (AOI, orbit-type, the spectrum/complexity machinery,
//!   NWF horizon partition, aspect-type determinacy, instance classification).
//! - [`r6`] — Abstraction-Quotient and Tower (collapse, the categorical structure, the
//!   `Reify` operator, the tower, `Twr-Growth`, `Inf-Dual`, fractality).
//! - [`romega`] — Meta-CRPT: the theory applied to itself (the self-substrate, self-horizon,
//!   tower-of-towers, the self-consistency fixed point, self-sectioning, import internalizing).
//!
//! **The minimal interpretation** (`Min-Interp`, R1.1.R5): CRPT is, minimally, the
//! recursive projection of a structure onto its discernible content — the deterministic
//! discrete dynamical system `(𝒰, ρ_M)`. Abstraction and observation are two *readings* of
//! the one operation; the WF/NWF duality is induction–coinduction made dynamical. The
//! engine's one [`r0::projection_systems_and_fibers::ProjectionSystem`] trait is that one
//! operation; every rank above instantiates or composes it.
//!
//! **Equality & determinism.** Equality is CRPT's own (mathematical identity `=`,
//! bisimilarity `≈`, observable equivalence `≃`) — never blanket-derived structural
//! equality; no hashing, no `Ord`-keyed maps; dense-indexed representations.

#![forbid(unsafe_code)]

pub mod r0; // R0 — Universal Projection Framework
pub mod r1; // R1 — The Projection Substrate
pub mod r2; // R2 — Horizon and Classification
pub mod r3; // R3 — The Observer
pub mod r4; // R4 — Instance / Model Algebra
pub mod r5; // R5 — Persistent Orbit Invariants
pub mod r6; // R6 — Abstraction-Quotient and Tower
pub mod romega; // Rω — Meta-CRPT: The Theory Applied to Itself

#[cfg(test)]
mod persistent_semantics_checks {
	use std::fs;
	use std::path::Path;

	#[test]
	fn forbid_raw_omega_limit_set_outside_r2() {
		let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR");
		let src_dir = Path::new(&manifest_dir).join("src");

		let mut offenders: Vec<String> = Vec::new();
		// Allow the canonical R2 implementation and this test file itself.
		let allowed = vec!["src/r2/canonical_orbit_invariant.rs", "src/lib.rs"];

		fn visit(dir: &Path, files: &mut Vec<String>) {
			for entry in fs::read_dir(dir).unwrap() {
				let entry = entry.unwrap();
				let path = entry.path();
				if path.is_dir() {
					visit(&path, files);
				} else if let Some(ext) = path.extension() {
					if ext == "rs" {
						files.push(path.to_string_lossy().into_owned());
					}
				}
			}
		}

		let mut files: Vec<String> = Vec::new();
		visit(&src_dir, &mut files);

		for f in files {
			let crate_rel = f.trim_start_matches(&format!("{}/", manifest_dir));
			if allowed.iter().any(|a| crate_rel.ends_with(a)) {
				continue;
			}

			let contents = fs::read_to_string(&f).unwrap_or_default();
			if contents.contains("omega_limit_set(") {
				offenders.push(crate_rel.to_string());
			}
		}

		assert!(offenders.is_empty(), "Found raw `omega_limit_set` uses in src/ outside R2: {:#?}", offenders);
	}
}
