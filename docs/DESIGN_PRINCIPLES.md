# crpt_engine — Design Principles

Distilled from the spec's requirements and from surveying every prior Rust attempt
(`CRPT-1` v0.6, the `crpt1→crpt3→current→crpt-2` line, and the Feb engines). Each
principle names the prior failure it corrects. These govern every construct.

## 1. Exactness, never approximation — *the* lesson

The prior engines "looked like CRPT" because they approximated. We do not.
- **Compute the condition; never declare or shortcut it.** Prior: bisimilarity ≈
  shortcut to *label equality*; self-validation that merely checks a required-law
  list is *present*. Ours: ≈ computed by partition refinement; `certify_*` that
  *verify the structural condition* (e.g. the L1.1.D6 forward/backward transfer).
- **No iteration bounds, no sentinels.** Prior: `max_steps` caps; `u64::MAX` as ∞.
  Ours: finite 𝒰 ⇒ exact termination (cycle detection); a real `Infinite` variant.
- Justified by the theory: on finite models everything is decidable
  (`Finite-Collapse` L0.7.T2, `FOL-Fin` L5.3.T4).

## 2. The engine *is* the spec

- **Structure = the tower's structure.** Module hierarchy mirrors the spec exactly:
  a module per level (`l1`…`l8`, `lomega`; `l0` is the external universal frame),
  a submodule per section (`l1::substrate` = L1.1). Every prior attempt mirrored
  the spec structure of its era (tiers, then anchor-layers) — now: ω-tower levels.
- **Every item cites its construct** by rc2 label (`L1.1.D1 \`Sub\``) and realizes
  its literal definition. Sole source of truth: `../CRPT_OMEGA_TOWER_`.
- **Definitional invariants are enforced at construction**, not checked later
  (e.g. →_ρ ⊆ →_σ; the projection-operator conditions C1/C2). A value of the type
  *is* the construct.

## 3. Name by meaning, never by symbol

Identifiers use the construct's meaning or tag, never the notation symbol. `reduces`
/ `reduction_successors` for →_ρ (not `rho_succ`); `Regime::{Convergent,Persistent}`;
`DerivationHeight::{Finite,Infinite}`. A symbol name (`rho`, `sigma`) appears only in
a doc comment that is literally naming that symbol.

## 4. Equality is CRPT's, not Rust's

CRPT carries stratified equality; we build on it rather than blanket-deriving.
- **mathematical identity `=`** — derived `==` only on `ElementId` (universe-position
  identity), documented as `=`.
- **bisimilarity ≈** (L1.1.D7) and **observable equivalence ≃_M** (L2.5.D2) are
  *computed* partitions, never derived traits.
- Compound model types get **no** structural `Eq`/`PartialEq` — model sameness is
  homomorphism/isomorphism (L5), computed.

## 5. Determinism by construction

- Dense `ElementId` = array index; sets are sorted `Vec`/`Vec<bool>` bitmaps; maps
  are `Vec`-by-index. **No `Hash`/HashMap, no `Ord`-keyed maps**; grouping by sorting.
- **No nondeterministic parallelism** in the core (rayon is excluded — it broke the
  prior engines' determinism and violates `docs/DETERMINISM_CONTRACT.md`).
- Bit-for-bit reproducible. (Full contract: `docs/DETERMINISM_CONTRACT.md`.)

## 6. Clone is a last resort

Only indices flow; element values are never cloned. Prior engines cloned generic
`U` element values through `Vec<U>` everywhere — we pass `&Substrate` and indices.

## 7. Witnesses that verify (`certify_*`)

Each construct gets a `certify_*` free function that *proves* the implementation
satisfies the spec definition by computing the condition (not by asserting a flag).
The heavier validation suite is feature-gated (`validation`), off the query path.

## 8. Core exact before breadth

Get the WF core exact and complete before any breadth (no GPU/parallel backends, no
many-domain instantiations until the core is faithful). The prior engines chased
breadth (cuda/vulkan, domain catalogs) before the core was exact — and missed.

## 9. One crate, no duplication

A single `crpt_engine` crate. No parallel `engine/` + `engine/spec/` copies (a prior
source of drift). Optional/heavy parts are feature-gated, not forked.
