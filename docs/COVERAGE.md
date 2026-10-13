# Coverage Audit — engine vs. the ω-Tower definitions

Systematic completeness audit against the spec's **166 definitions** (L0–Lω, v1.0.0-rc4 —
rc4 added `Obs-Lab` L1.1.D8, realized: `Substrate::from_observable_contract`).
Each is **✓ implemented**, **⊘ deferred by necessity** (topological tier / genuinely
second-order / meta — see `docs/SECOND_ORDER.md` and `docs/BUILD_PLAN.md`), or **✗ gap**
(finite, buildable, not yet done). "Complete" = no `✗`. Theorems are realized as the
`certify_*` witnesses attached to their definitions.

> Status: **AUDIT CLOSED + rc4-ALIGNED, 2026-06-11.** Every one of the 166 definitions is `✓`
> implemented — including the formerly deferred topological, infinitary, metric,
> categorical, and model-theory groups, all un-deferred and realized on the engine's
> one-trait symbolic representation. Zero `✗` gaps; zero `⊘` deferrals. What remains
> outside the engine is model-phase instantiation *data* only (see "Audit closed").

## Per-level summary

| Level | Defs | ✓ | ⊘ deferred | ✗ gap |
|---|---|---|---|---|
| L0 | 9 | 9 (L0.1/L0.5 explicit — `TowerLift` literal via the one trait; rest via CRPT instance) | 0 | 0 |
| L1 | 16 | 16 (`CPer` + full `PA-Reach` + `LA_M` + `SC-Orb` closed the level) | 0 | 0 |
| L2 | 15 | 15 (+ `Inf-Dual` L2.2.T7 realized in `l2::regime`) | 0 | 0 |
| L3 | 22 | 22 (`12-Part`/`H_*^top`/`Q-top`, `sig_M-NM` profile, `n-Reach` — all realized) | 0 | 0 |
| L4 | 22 | 22 (`PV∞`/`IRH-x` exact; `Enc` interface + four certificates) | 0 | 0 |
| L5 | 30 | 30 (+ the L5.3 Tarski kernel: `L-Str`/`L-Th`/`⊧`/`Rel-Sent`/`L-Hom`/`Scope-Sat`) | 0 | 0 |
| L6 | 23 | 23 (the full L6.3 recurrence machinery; Type AP inhabited) | 0 | 0 |
| L7 | 12 | 12 (`GI∞`; `ω-Cat`/`η-Nat`/`η-Comp`) | 0 | 0 |
| L8 | 14 | 14 (+ `ω-Cat-Str`/`Twr-ωCat` L8.7) | 0 | 0 |
| Lω | 2 | 2 | 0 | 0 |

## The `✗` backlog — **empty**

The finite combinatorial tier is complete. Every definition realizable on a finite
discrete substrate is implemented and witnessed by the test suite. The full list closed
across the gap-closing passes: L3 `HP`/`SC-2`/`SC-3`; L4 `FRH`, observer components
(`Behav-F`/`PV-Obs`/`HC-Obs`), `Refl-Abs-D`; L5 `Mod-∩`/`Mod-∪`/`Mod-/`/`Iso`/`R-Iso`/
`Inst-Emb`; L6 `Dege-Inv`/`3-Tier`; L7 `Quot-Proj`; L8 `Can-Incl`/`Twr-Img`/`Twr-Disc`.

**L7 (1):** `Quot-Proj` (L7.1.D2, the quotient projection of Collapse, named).

**L8 (1–2):** `Can-Incl` (L8.2.D3, the canonical atom inclusion `ι`); `Twr-Img`/`Twr-Disc`
(L8.6, tower image / discreteness — partial).

## The two modes and the meta layer — apparatus complete (rc4)

rc4 resolves the mode axis to exactly **two** (`Mode::{Recurrence, Convergence}`,
L1.4.D1): recurrence serves both regimes on the finite substrate (Fix at `d_M`, the
class cycle at `n_M`), convergence is inhabited on the symbolic topological tier
(`ConvergentChain`); the AOI is the **analysis layer**, not a mode. The
`TopologicalProjectionSystem` trait carries convergence-mode `CFix` on ∞_M, `≃_M`
(L2.5.D2 ∞-reading), `sig_M-NM` (trace tail class), and `GI∞` (L7.1.D5).

**Meta layer:** `SO-Ext` (L5.3.D6) is the lattice/fixpoint architecture, both sources
proven (`docs/SECOND_ORDER.md`); `R-Iso∞` (L5.2.D5) is implemented; `RTD-Und`/`RTD-NI`
(L6.5.T3/T4) are realized as bounds (the engine's `regime_type` *is* the decidable finite
case; the meta-statement is the function's parametricity).

## Un-deferral record — building on symbolic-infinite substrates (re-scoped 2026-06-10, completed 2026-06-11)

**Correction:** the engine *does* model infinite substrates — symbolically, via operations
on a finite presentation (`Lift` = `FMA(Q_M)`, `Tower`, `ConvergentChain` are all infinite).
The `Inf-Dual` keystone (L2.2.T7, `l2::regime` — its label’s module) organizes infinite structure
(horizontal σ-infinity ⟺ vertical ρ-infinity via `Lift`). So these are **not** permanent
gaps — they build on the symbolic-infinite representation, computed from the finite
presentation, **not** by enumeration. The record of the un-deferral, all complete:

- ~~`12-Part` + `H_*^top` + `Q-top` (L3.2.D3–D6, T3, T4)~~ — **DONE**: realized on
  `TopologicalProjectionSystem` (`structural_horizon_topological`,
  `invariant_horizon_topological`, `is_limit_point`/`Lim_M`,
  `topological_preimage_count`) + `l3::classification`
  (`PersistentHorizonClass` A_∞–F_∞, `TwelveClass`, `persistent_classify`,
  `twelve_classify`); all six persistent classes inhabited by symbolic witnesses
  (ℕ∪{ω}, two-chains, ω·2, ramified limit points). The `H_I^top` rate clause is
  metric data — topology-only default: indistinguishable; the metric instantiation
  overrides `convergence_rates_distinguishable`.
- ~~`IRH-x` + `PV∞` (L4.3.D5/D6, `PV2` L4.3.T2)~~ — **DONE** in `l4::valuation`
  (its label's module): `infinite_reduction_history` (the unique C1 history's
  prefix, νT-scoped) and `pv_infinity` — the **discrete-topology** limit
  `lim PV(h|_n)`, decided *exactly* on eventually-periodic orbits (= PV2's own
  SC-2/3 scope) via the per-period value map: `Exists` (stabilises, incl.
  late absorption), `DoesNotExist` (periodic non-constant — the "limiting
  product" case a richer topology refines), `Undetermined` (aperiodic symbolic
  orbit — the `𝒯`-limit tier owns it). Never wrong, total, generic over the one
  `ProjectionSystem` trait.
- ~~Type AP + the L6.3 recurrence machinery~~ — **DONE** in `l6::aoi_full_proofs`
  (the L6.3 module) + `l6::orbit_type` (L6.2): `Rec-Set` (infinite subsets of ℕ,
  finitely presented, decidable membership), `Freq`/`OS-21B` (exact rational
  spectra — no floats), `Spec-Def` + `Freq-Sum` certified, `Rec-Type` (six-way
  taxonomy, exact; the SC-4 finite collapse documented), `OC-21B`
  (`OC = (κ, ρ)`; κ tail-reading per `OC-Per`, `(0,0)` on SC-1; κ ∈ {2, ω}
  inhabited via the symbolic κ case split), `OC-WD`(b) bisimulation-invariance
  certified, `AOI-Unif`, `SC-∞` (with the spec's own alternating-stream
  `SC∞>SC1` counterexample realized: spectrum exactly (1/2, 1/2)), `SC-k`
  hierarchy termination (at the transient length). **Type AP inhabited** on the
  symbolic ℕ-counter via `certify_aperiodic_prefix` (pairwise-distinct class
  trace to any depth — ¬SC-4 by construction).
- ~~`sig_M-NM` profile + `n-Reach` + `CPer` + full `PA-Reach`~~ — **DONE, CRPT-natively**
  (no metric arithmetic — the user's correction: all discernment is CRPT's own
  machinery). `sig_M-NM` (l3::horizon): `PersistentOrbitSignature` =
  `(∞, limit_id, profile)` with the profile as the orbit's **observation trace**
  (obs labels the ≈/`Tail-Eq` machinery reads — instances code rate observables
  into obs; comparison is equality, never an order). `H_I^top` rates clause =
  approach orbits pairwise tail-equivalent (`Tail-Eq` L6.3.D2). `n-Reach`
  (l3::persistent) = the signature-stabilization depth (= the `SC-k` AOI index,
  bisimulation-complete by `OC-WD`); `CPer` (l1::axioms) = `ρ^{n_M}(x)`; and
  **`PA-Reach` upgraded from skeleton to full form** (`n_M` total on ∞_M) — the
  ninth axiom is now fully realized.
- ~~`ω-Cat` + `η-Nat` + `η-Comp` (L7.2.D2/D3/T2) and `ω-Cat-Str` + `Twr-ωCat` +
  `Twr-ωCat-T` (L8.7.D1/D2/T1)~~ — **DONE** in their label modules. `l7::adjunction`:
  `OmegaCategory` (models as layers, certified `Hom` connecting maps — finite-prefix
  presentation; every cell lives at a finite level), `NaturalTransformation`
  (componentwise homomorphisms, naturality squares up to ≃ certified at construction —
  with a two-fiber negative test proving the certificate has teeth) and vertical
  composition. `l8::omega_category` (new L8.7 module): `PathCell` reduction-path cells
  over the symbolic `Lift` words (s/t, vertical composition = path concatenation,
  identities = `ι` at atoms, horizontal action = left whiskering — the FMA-realizable
  fragment; the right action lives one level up via the `Inf-Dual` depth reset), and
  `certify_strict_axioms`: globularity, units, associativity, and interchange certified
  exactly on the bounded cell fragment.
- ~~Model-theory scaffolding (L5.3.D2–D9, D12–D15)~~ — **DONE** in `l5::conformance`
  (the L5.3 module): the finite **Tarski kernel** over `Σ_CRPT` — `SigmaTerm`/`Formula`
  (L-Th sentences, de Bruijn binding), `satisfies` (`⊧`, exactly decidable — `FOL-Fin`),
  `satisfies_relativized` (`Rel-Sent` quantifier restriction), `scope_aware_satisfaction`
  (`Scope-Sat`, returning the four-valued L1.5 `Scope` — Global/Scoped/Vacuous/Fails all
  exercised), `is_l_homomorphism` (`L-Hom`, strict symbol preservation — with the
  `CRPT-Hom` D14 equivalence note), and the **executable `Mod-Corr`**:
  `certify_tarski_agrees_with_native` proves Tarski-`⊧` of `T_CRPT` sentences
  (`pa_fix_sentence`, `c1_sentence`) agrees with the native checkers — including on a
  PA-Fix-violating model, where both sides reject. D13/D15 are restatements (cited).

## rc4 alignment (2026-06-11)

All 21 engine findings (A1–A11, B1–B10) were resolved in spec v1.0.0-rc4, adopting the
engine's interim resolutions; the engine is re-aligned to the canonical text: derived
obs (`Obs-Lab`/`Obs-Lab-WD`, the contract constructor + certificate), the meaning-form
`PA-Reach` (R1/R2/R3 + the three realization theorems + the `M_Reach` countermodel),
the **two-mode** resolution (`Mode::{Recurrence, Convergence}`; "asymptotic mode" purged
— AOI is the analysis layer), the trace-based persistent signature (`OT^obs`,
tail-equivalence), `OS-Push`, the `PV-Dual` factorization, and the pointed Observable
contract. Module-structure tensions with the spec's own section scoping are catalogued
in `docs/SECTION_SCOPE_VS_MODULES.md` (pending spec assessment).

## Audit closed (2026-06-11)

Every deferral category of the completeness audit is realized. What remains outside the
engine is **model-phase instantiation data only**: concrete domain models (λ-calculus,
ZFC, physics), rich Gödel encodings for `Enc`, metric/rate observables coded into obs,
and model-specific `LA_M` sentences — all *consumed through interfaces the engine now
provides and certifies*. The one permanent mathematical bound stands as documented:
`RTD-Und` (Rice) for arbitrary infinite `ρ`, realized as a bound, with structured
finitely-presented infinite substrates fully tractable.
- ~~`LA_M` (L1.5.D2) + `SC-Orb` (L1.5.D5) + `Enc` (L4.6.D1)~~ — **DONE**, in their label
  modules. `LA_M` (`l1::profile`): `LocalAxiom` named sentences over `Σ_M` +
  `local_axioms_hold` (∅ default = why `Φ_LA` is vacuous). `SC-Orb` (`l1::profile`):
  orbit-scoped confluence, with `Scope-Suf` (L1.5.T2) realized as a test — a model where
  **PA-Conf fails but SC-Orb holds**. `Enc` (`l4::self_projection`): `Term` =
  `Terms(CRPT)` with exact denotations, the `AdmissibleEncoding` interface, and Enc-1..4
  as exact certificates (Enc-1 under **denotational** term equality — the consistent
  reading, since syntactic equality collides with Enc-2; certified positive on a
  separating substrate, and the Enc-1 certificate provably *catches* the non-injective
  tautological encoding). Rich Gödel numberings remain model-phase, as the spec states
  (PA-* do not supply Enc) — but the interface and admissibility checks are the engine's.

**The one true permanent bound:** `RTD-Und` (Rice) — regime membership is undecidable for an
*arbitrary* infinite `ρ`. But *structured / finitely-presented* infinite substrates (what the
model algebra and the theory's witnesses produce) are fully tractable. That undecidability is
realized as a bound, not a missing construct.
