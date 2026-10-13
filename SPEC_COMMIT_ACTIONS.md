Spec commit → Engine mapping (selected, rc9-import-substrate)
==========================================================

This file maps authoritative commits from `CRPT_OMEGA_TOWER_` (branch
`feat/rc9-import-substrate`) to the engine files that implement, rely on,
or needed alignment with the change.

- dba4b76 — spec(R3.7.T1 CPEP-Ind): "M_cohere/M_absorb persistent aspect is a cycle, not a fixpoint"
  - Engine: `src/r3/coherent_perturbation.rs` (coherent perturbation classification; uses `omega_limit_classes`)

- 58b6219 — proofs(R2.3.D6/T3/T4): "CNF∞ persistent canonical form; relocate ω_≈/≃∞ to R2.3"
  - Engine: `src/r2/canonical_orbit_invariant.rs` (defines `omega_limit_set`, `omega_limit_classes`, `persistent_quotient`)

- 125b560 — proofs(R5.1/R2.3 ≃∞): "AOI bisimulation-quotient ω-limit; re-point H_S* to it"
  - Engine: `src/r5/aoi_full_proofs.rs`, `src/r2/canonical_orbit_invariant.rs` (AOI computations should use `omega_limit_classes`)

- fe8a4c5 — proofs(R3.5 CPD): "co-projection depth — minimal eventual period + CPD-Fin + CIH"
  - Engine: `src/r3/projection_depth.rs` (co-projection depth / canonical period semantics)

- a2afe71 — proofs(R4.1.T5): "CNF∞-BQF — CNF∞ is a bisimulation-quotient fixpoint"
  - Engine: `src/r4/*` and `src/r2/canonical_orbit_invariant.rs` (collapse/quotient semantics)

- 330ee3d — spec(R5 SC-4): "SC-4 is finite-B̃ (R2.3.D5)"
  - Engine: `src/r5/*` (spectrum / complexity machinery)

- 125b560, 58b6219, and related R2/R5 commits together:
  - Action: Ensure all persistent semantics across `src/r{2,3,5,6}` use `omega_limit_classes` / `persistent_quotient` and do not rely on raw `omega_limit_set` for bisimulation-sensitive decisions.

Notes:
- `rc4_reference/` contains historical code and may still use raw `omega_limit_set`; that directory is intentionally left as reference and not part of the aligned engine runtime.
- I scanned `src/` and confirmed remaining raw `omega_limit_set(` literal occurrences are only in `src/r2/canonical_orbit_invariant.rs` (allowed) and reference files; persistent APIs (`omega_limit_classes`, `persistent_quotient`, `persistent_equivalent`, `orbit_trace`, `n_reach`, etc.) are present across `src/`.

Next recommended actions:
- Apply any missing renames / meaning-based identifier normalizations to match spec names exactly (if desired).
- Add per-module unit tests that assert bisimulation-quotient use where the spec requires it (we added one crate-local check already).
- Finish any remaining regression tests flagged in the TODO list and optionally tag code comments with spec SHAs for traceability.
