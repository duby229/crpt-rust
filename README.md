# crpt_engine

An **exact** Rust implementation of the **CRPT ω-Tower** specification (Compositional
Recursive Projection Theory). Not a resemblance or an approximation: every item realizes
a specific labelled spec construct, cited by its tag, and is built to the construct's
literal definition.

- **Spec (sole source of truth):** `../CRPT_OMEGA_TOWER_`, currently **v1.0.0-rc3**.
- **Scope:** finite substrates, where the theory is fully decidable (`Finite-Collapse`
  L0.7.T2, `FOL-Fin` L5.3.T4) — bisimilarity, regimes, horizons, and orbit invariants are
  exact finite computations. The **topological tier** (`PA-WN_top`, infinite substrates)
  is out of scope by design; see `docs/BUILD_PLAN.md`.

## Design stances

- **Exactness, never approximation.** Where the spec is internally inconsistent the engine
  implements the primary definition and *surfaces* the conflict rather than guessing; the
  seven post-rc2 findings it raised were resolved in rc3 (`docs/SPEC_FINDINGS_RC2.md`).
- **Structure = the tower's structure.** One crate; a module per spec level (`l1`…`l8`,
  `lomega`), a submodule per section. Identifiers are the spec's exact tag or
  meaning-based name — never a paraphrase.
- **CRPT's own equality, computed.** No blanket-derived `Eq`/`Hash`. Mathematical identity
  `=` is derived only on `ElementId`; bisimilarity `≈`, observable equivalence `≃_M`, and
  persistent orbit equivalence `≃∞` are *computed*. Constructs `certify_*` their spec
  conditions (compute-and-verify witnesses), not declare them.
- **Determinism by construction.** Dense element indices, sorted `Vec`/bitmaps, grouping by
  sorting — no hashing, no `Ord`-keyed maps, no nondeterministic parallelism. See
  `docs/DETERMINISM_CONTRACT.md`. `#![forbid(unsafe_code)]`.
- **Second-order commitments, exactly.** CRPT's second-order quantifiers (bisimilarity,
  coinduction, the regimes) are realized as least/greatest fixpoints on the finite powerset
  lattice — one Knaster–Tarski combinator (`src/lattice.rs`), `O(n²–n³)` and exact by
  `FOL-Fin` (L5.3.T4). See `docs/SECOND_ORDER.md`.

## Layout

| Module | Spec level |
|---|---|
| `l0` | L0 — the universal `ProjectionSystem` trait CRPT instantiates (fiber, `≃_π`) |
| `l1` | L1 — substrate (L1.1), the nine PA-* projection axioms (L1.2/L1.3) |
| `l2` | L2 — ρ_M/Model, regime, depth, canonical form, fiber/≃_M/Q_M |
| `l3` | L3 — horizons + sig_M, six-class A–F, persistent ω-limit/≃∞/Q∞/Sem |
| `l4` | L4 — observer 𝒪, gateway, valuation/PV, CPD/CIH |
| `l5` | L5 — model algebra, homomorphisms/Mod_CRPT, model order |
| `l6` | L6 — AOI hierarchy, orbit types, NWF six-class A*–F*, regime determinacy |
| `l7` | L7 — Collapse (total over Sem(M)), Lift ⊣ Collapse |
| `l8` | L8 — FMA, Lift, Lift∞, the Tower |
| `lomega` | Lω — the self-conformance test |

See `docs/BUILD_PLAN.md` for the full per-section status and the deferred topological tier.

## Build & test

```sh
cargo test      # the construct/witness test suite
cargo clippy    # lints (clean)
cargo doc --no-deps --open   # the cited, construct-by-construct documentation
```

No external dependencies.
