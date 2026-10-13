# CRPT Engine — Determinism Contract

**Status:** binding for all engine code. Written before the substrate types, because
it constrains every container and algorithm choice above it.

**Sole source of truth:** the CRPT ω-Tower spec (`../CRPT_OMEGA_TOWER_`). Every
invariant below is either a spec requirement (cited) or an engine realization choice
that serves the spec's commitment to a *maximally deterministic recursive projection
system*. Where a choice is the engine's, it is marked **[engine]**.

## Scope

The engine is built **WF-core first** (∞_M = ∅). In that regime the worst determinism
hazards (floating point, topological limits) are absent, and the theory is fully
decidable: `Finite-Collapse` (L0.7.T2) and `FOL-Fin` (L5.3.T4) prove every second-order
construct collapses to a terminating first-order computation on finite models. The
contract is written so the topological/NWF mode (L1.2 PA-WN_top, L6) can be added later
without weakening it.

## Invariants

1. **Dense integer identity.** The universe 𝒰 of a model is the dense range `0..n`.
   `ElementId` *is* the array index. There is no separate id→index map. **[engine]**
   *Why:* a `HashMap<Id, usize>` would introduce seeded iteration order; positional
   ids remove the hazard at the source.

2. **No hash-ordered iteration in semantics.** No `HashMap`/`HashSet` may be iterated
   in any path that produces a semantic result. Use sorted `Vec`, `BTreeMap`,
   `BTreeSet`. Adjacency lists are stored sorted and deduplicated. **[engine]**

3. **ρ_M is a deterministic total function** (L2.1.D1, C1/C2). Exactly one successor
   ρ_M(x) per element; `project` is total over `0..n`. The reduction *relation* →_ρ may
   be multi-valued, but the *strategy* ρ_M is single-valued by definition.

4. **No floating point in the WF core.** The domain is discrete/combinatorial. FP enters
   only with the topological canonicalization mode (PA-WN_top, L1.2.Ax7), which is
   deferred; when added it must specify a deterministic, platform-stable numeric policy.

5. **No nondeterministic parallelism in core projection.** The core (ρ_M-orbits,
   regimes, horizons, Lift) runs single-threaded. No `rayon`/thread scheduling until a
   provably order-independent strategy is established. **[engine]**

6. **Canonical output order.** Any function returning a set of elements returns it in
   ascending `ElementId` order. Any partition is reported with a stable, documented
   block order. **[engine]**

7. **Exhaustive, not sampled.** Every `certify_*` / membership / horizon computation is
   a complete finite computation — never sampled or approximated (Common Pitfalls L2.3:
   "kernel uniformity checked exhaustively, not sampled"). Justified terminating by
   `Finite-Collapse` (L0.7.T2) / `FOL-Fin` (L5.3.T4).

8. **Bit-for-bit reproducibility.** Identical inputs yield identical outputs across runs
   and platforms: no address-dependent behavior, no nondeterministic iteration, no
   wall-clock or RNG influence on semantics. **[engine]**

## Enforcement

- `#![forbid(unsafe_code)]` at the crate root (no address-dependent escape hatches).
- Hash-based collections are disallowed on semantic paths by review; prefer `BTree*`.
- Correctness is witnessed by `certify_*` free functions (conformance/test path), kept
  off the hot query path (a query is an array lookup; certification proves the array
  faithful to the spec construct it represents).
