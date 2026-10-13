# Specification Issues Found Since rc3 — Engine Audit Hand-Off

> **STATUS: RESOLVED in v1.0.0-rc4** (commits 0a24d2c, cf583ad, ca8f1e0) — all 21
> findings addressed as recommended, plus the deeper mode/PA-Reach refactor. The engine
> is rc4-aligned. This document is retained as the historical record. The successor
> assessment request is `docs/SECTION_SCOPE_VS_MODULES.md`.

Audience: the specification agent. Scope: **every specification-level issue discovered
during engine development against v1.0.0-rc3** (post-rc3 only; all rc1/rc2-era findings
were resolved in rc2 commit c84fb29 and rc3 commit 48d899b — see
`docs/SPEC_FINDINGS_RC2.md`, historical).

For each item: the labels involved, the inconsistency, the engine's interim resolution
(with the file/test that depends on it), and a recommended spec fix. Engine state at
audit time: 130 tests green, all 165 definitions realized.

Severity key — **A** = substantive (contradiction, false-as-stated theorem, or
under-specification that forced an engine-side semantic decision); **B** = editorial
(synopsis/body drift, notation, substitution artifacts).

---

## A. Substantive

### A1. `12-Part-EE` (L3.2.T3): the claim "Class F\* (persistent) is empty" appears FALSE as stated
- **Labels:** L3.2.T3 `12-Part-EE`; L3.2.D3 `H_S^top`, L3.2.D4 `H_I^top`, L3.2.D5 `Q-top`.
- **Issue:** The theorem asserts F and F_∞ are both empty "under the native axiom system
  (PA-WN globally, PA-WN_top on ∞_M, PA-Conf on all)". The convergent `F = ∅` follows
  from determinism via kernel d_M-uniformity (`H_I-Dec`): a fixpoint's d_M-uniform kernel
  collapses to the fixpoint itself. **No analogous mechanism exists on the persistent
  side**: in a T₂ topology, two distinct ∞_M orbits can converge to the same limit with
  indistinguishable rates — nothing forces them to coincide. Engine counterexample
  satisfying all the stated axioms (deterministic ⇒ PA-Conf; PA-WN on ↓; PA-WN_top on ∞):
  two persistent mid-chains, each a reached 𝒯-limit, both converging to one fixpoint,
  with equal observations — the mid-chain heads classify **F_∞** (limit point, ramified,
  rates indistinguishable).
- **Engine evidence:** `src/l3/classification.rs`, test
  `ramified_limit_points_inhabit_e_and_f_infinity` (the `mid_a_obs == mid_b_obs` branch
  produces an F_∞ inhabitant).
- **Recommended fix:** either (i) drop the F_∞ = ∅ clause from `12-Part-EE` (F_∞ is a
  legitimate, inhabitable class — the engine's classifier treats it so), or (ii) add the
  explicit separation axiom that would empty it (a persistent analogue of `H_I-Dec`,
  e.g. "ramified limits have ≈-distinguishable approach orbits") and scope the claim to
  models satisfying it.

### A2. `Freq-Sum` (L6.3.L2) is false for spectrum-definite orbits with infinite B̃; `Spec-Def` (L6.3.D6) synopsis and body disagree on the sum clause
- **Labels:** L6.3.L2 `Freq-Sum`; L6.3.D6 `Spec-Def`; L6.3.D9 `OC-21B` (κ = 2 case).
- **Issue:** `Freq-Sum` states `Σ_{C ∈ B̃(x)} OS_M(x)(C) = 1` for spectrum-definite x.
  For an aperiodic orbit visiting countably many classes each finitely often (e.g. the
  ℕ-counter: every class visited once), **every `freq_x(C)` exists and equals 0**, so the
  orbit is spectrum-definite by the D6 *body* ("∀C ∈ B̃(x): freq_x(C) exists") yet the
  sum is 0 ≠ 1. Note this is exactly the κ = 2 regime that `OC-21B` itself names
  ("countably infinite and spectrum-definite") — so the lemma and the κ-table cannot both
  stand as written. Meanwhile the D6 *synopsis* says "all limits exist **and sum to 1**"
  — a stronger condition than the body's.
- **Engine evidence:** `src/l6/aoi_full_proofs.rs` (`certify_frequency_sum` is scoped to
  finite substrates, where B̃ is finite and the sum is exactly 1 — residue counts sum to
  the period); the κ = 2 inhabitation in `complexity_class(None, true)` with the
  ℕ-counter certificate (`src/l6/orbit_type.rs`, `certify_aperiodic_prefix`).
- **Recommended fix:** decide the canonical `Spec-Def`: if it is "all freqs exist", scope
  `Freq-Sum` to finite B̃ (the imported result is for *finite* partitions — the Source
  line already says so); if it is "exist and sum to 1", then κ = 2 needs a different
  side condition (and the κ-table's "spectrum-definite" reference must be re-examined,
  since sum-to-1 spectrum-definiteness may make κ = 2 uninhabitable for
  finitely-recurrent aperiodic orbits).

### A3. `n-Reach`/`CPer` (L3.3.D10 / L1.3.D1) under the literal `sig_M-NM` reading contradict PA-Reach on the spec's own canonical witness
- **Labels:** L3.3.D10 `n-Reach`; L1.3.D1 `CPer`; L3.1.D5 `sig_M-NM`; L1.3.Ax2 PA-Reach;
  L1.4.R3 `Top-Inst`.
- **Issue:** `n_M(x) = min{n | ∀j: sig_M(ρ^{n+j}(x)) = sig_M(ρ^n(x))}` with
  `sig_M(x) = (∞, limit_id, convergence_profile)` and the profile a raw sequence in
  `ℝ^ℕ`. The profile of `ρ^n(x)` is the n-shifted sequence; pairwise equality of all
  tails of a sequence holds **iff the sequence is eventually constant**. On the spec's
  own canonical metric witness `ℕ ∪ (0,1]` (d(ρⁿx, lim) = 1/(n+1), strictly decreasing),
  no tail is constant ⇒ `n_M(x)` **does not exist** ⇒ PA-Reach fails on the canonical
  witness — a contradiction with PA-Reach's "substantively true" status and `CPer`
  existence.
- **Engine resolution:** signature constancy is read against a *stabilizable* complete
  observable: the unified AOI (`AOI-Unif` L6.3.D10, bisimulation-complete by `OC-WD`
  L6.3.T10). Then `n_M` = the `SC-k` hierarchy's stabilization index (= the transient
  length on finite substrates), total on ∞_M, and full PA-Reach is realized
  (`src/l3/persistent.rs::n_reach`, `src/l1/axioms.rs::pa_reach`,
  `canonical_persistent_representative`).
- **Recommended fix:** specify what "sig_M stabilises" quantifies over — either define
  the profile component up to shift/tail-equivalence (rate class), or state that
  `n-Reach` reads the stabilizable fragment of `sig_M-NM` (limit_id + rate class, not
  the raw shifted sequence). See also A11.

### A4. `OC-21B` (L6.3.D9) κ-formula vs `OC-Per` (L6.3.T11): full B̃ vs tail-restricted B̃
- **Labels:** L6.3.D9 `OC-21B`; L6.3.T11 `OC-Per`.
- **Issue:** D9 defines κ = 0 as "B̃(x) is a singleton (orbit stays in one class — SC-1
  with N = 0)". T11 proves `OC_M(x) = (0,0)` for SC-1 **with transient N possibly > 0**
  ("B̃(x) has at most N+1 elements but the tail is a single class … κ(x) = 0"). Under the
  literal D9 (full B̃), such an x has |B̃| > 1 ⇒ κ = 1, contradicting T11.
- **Engine resolution:** κ reads the **tail** classes (asymptotic reading — consistent
  with AOI₁'s tail-equivalence and with T11). `src/l6/aoi_full_proofs.rs::orbit_complexity`;
  test `sc_1_orbit_has_complexity_zero_zero_and_dirac_spectrum`.
- **Recommended fix:** restate D9's κ cases over the tail-restricted B̃ (or over
  `ω_≈(x)`), and delete the "with N = 0" parenthetical.

### A5. `H_S^top` (L3.2.D3) formula vs the twelve-class table prose: whose pre-images?
- **Labels:** L3.2.D3 `H_S^top`; the D_∞/E_∞/F_∞ rows of the L3.2.D6 class table.
- **Issue:** The D3 formula evaluates the ramification of **x's own orbit-limit**
  (`lim ρⁿ(x)` has multiple pre-image orbits), for every x ∈ ∞_M. The class-table prose
  for the limit-point rows reads as if H_S^top of a limit point counts **that point's
  own** pre-images ("Limit point, multiple ∞_M-pre-images"). For a limit point a (whose
  own orbit converges onward to some ℓ(a)), the two readings differ.
- **Engine resolution:** the formula is canonical (per the standing formula-over-prose
  policy): `structural_horizon_topological` evaluates the ramification of x's own
  orbit-limit uniformly. D_∞/E_∞/F_∞ then mean "limit point whose own limit is
  (un)ramified". `src/l3/classification.rs`.
- **Recommended fix:** align the table prose with the formula (or, if the prose is the
  intent, restate D3 with a case split at limit points).

### A6. `Enc` (L4.6.D1): Enc-1 and Enc-2 are jointly unsatisfiable under syntactic term equality
- **Labels:** L4.6.D1 `Enc`, conditions Enc-1 (injectivity), Enc-2 (WF faithfulness).
- **Issue:** Enc-2 forces every proj-computing term t at convergent x to satisfy
  `CFix(Enc(t,x)) ≃_M proj(x)` — i.e. all such codes lie in x's fiber, hence are pairwise
  `≃_M`. Enc-1 (`Enc(t₁,x) ≃_M Enc(t₂,x) ⟹ t₁ = t₂`) under **syntactic** equality then
  forces all proj-computing terms to be syntactically identical — false (e.g.
  `CFix(Var)` vs `CFix(Var) ∘ Var`). The conditions are consistent only if `t₁ = t₂`
  means **denotational** equality of terms.
- **Engine resolution:** `t₁ = t₂` is denotational (`∀x: ⟦t₁⟧(x) = ⟦t₂⟧(x)`, decidable
  on finite substrates). `src/l4/self_projection.rs::denotationally_equal`,
  `certify_enc_injective`; positive/negative witnesses in its tests.
- **Recommended fix:** state explicitly in Enc-1 that term equality is
  denotational/semantic (or quotient `Terms(CRPT)` by denotational equality before
  stating injectivity).

### A7. The observation labeling `obs` has no formal home in the substrate or the signature
- **Labels:** L1.1.D1 `Sub` (the quadruple); L1.1.D6/D7 `Bisim~` (rc3 keystone);
  L5.3.D10 `Σ_CRPT`; L1.3.Ax1 PA-Bisim; L5.3.T1 `Mod-Corr`.
- **Issue:** rc3's labeled bisimulation — the keystone fix making PA-Bisim non-vacuous —
  defines `≈` on `(𝒰, →_ρ, obs)` with `obs ↾ NF` injective. But the substrate is the
  quadruple `(𝒰, →_ρ, →_σ, 𝒯)` with no obs component, and `Σ_CRPT` carries
  `Observable : U → Bool` but not the obs labeling. Since PA-Bisim ∈ T_CRPT and `≈`
  reads obs, `Mod-Corr` ("satisfaction is model-hood") is not well-posed unless obs is
  part of the structure. The engine had to carry `observation` as substrate data
  (finite `Substrate::observation`; symbolic tier `observation()` hook).
- **Recommended fix:** add obs to the substrate tuple (or formally attach it at
  L1.1.D6), and add the labeling to `Σ_CRPT` (a `Label` sort + `obs : U → Label`,
  with the existing Remark noting `≈` itself stays second-order/computed).

### A8. SC-1's two characterizations disagree — inside L3.3.D2 itself, and again at L6.3.D12
- **Labels:** L3.3.D2 `SC-1` (synopsis vs body); L6.3.D12 `SC-k` (synopsis);
  L6.3.T11 `OC-Per`, L6.3.T16 `SC∞>SC1` (usage).
- **Issue:** The L3.3.D2 **synopsis** says SC-1 = *eventually periodic*
  (`∃n, p ≥ 1 : ρ^{n+p}(x) ≃_M ρ^n(x)`). The L3.3.D2 **body** says SC-1 = tail
  **constant** in `𝒰/≈` (`ω_≈(x)` a singleton — period 1 in classes). These differ: an
  alternating two-class cycle is eventually periodic (p = 2) but not tail-constant.
  The L6.3.D12 synopsis repeats the "eventual periodicity" reading; T11 and T16(b)
  (which classifies the alternating stream as ¬SC-1) use the singleton reading.
- **Engine resolution:** the body/usage reading (singleton tail). The alternating-stream
  counterexample of T16(b) is realized verbatim
  (`src/l6/aoi_full_proofs.rs::alternating_stream_satisfies_sc_infinity_but_not_sc_1`).
- **Recommended fix:** correct the L3.3.D2 and L6.3.D12 synopses to the singleton-tail
  reading ("eventual periodicity" is SC-4's territory — see also B9).

### A9. `Twr-ωCat` (L8.7.D2) horizontal composition is under-specified relative to the rc3 strip convention
- **Labels:** L8.7.D2 `Twr-ωCat` ("Horizontal composition (∘_k for k < n−1): via tower
  embeddings ι_k"); L8.7.T1 `Twr-ωCat-T`; L8.1.D2 strip convention; L2.2.T7 `Inf-Dual`.
- **Issue:** With strip-LAST reduction (rc3-standardized), the only horizontal action
  realizable on a non-trivial reduction-path cell *within a level* is **left
  whiskering** (a prefix never disturbs the reduction); the right action would have to
  consume the suffix first, so `x' · y'` is not reachable from `x · y` in-level. The
  general interchange law therefore does not hold for in-level concatenation of
  arbitrary path cells; it holds for the left-whiskering fragment, and the full
  horizontal structure exists only through the cross-level embedding (`Inf-Dual`'s
  depth reset, T7(iii)/(iv)). "via tower embeddings ι_k" gestures at this but does not
  define `∘_k` or state which interchange instances hold where.
- **Engine resolution:** vertical composition (path concatenation), identities (ι at
  atoms), left whiskering, and interchange **for the left-whiskering fragment** are
  realized and certified (`src/l8/omega_category.rs::certify_strict_axioms`).
- **Recommended fix:** give the globular construction of `∘_k` explicitly, stating the
  strip-convention-induced asymmetry (left whiskering in-level; right action via ι one
  level up), and scope `Twr-ωCat-T`'s interchange claim accordingly.

### A10. `OS-21B` (L6.3.D5) domain mismatch: five-letter classes vs ≈-classes
- **Labels:** L6.3.D5 `OS-21B` (synopsis vs body); L6.3.D6 `Spec-Def` synopsis ("all
  five limits").
- **Issue:** The synopsis types the spectrum as `OS_M(x) : {A,B,C,D,E} → [0,1]` (the
  five active horizon classes); the body types it as `OS_M(x) : 𝒰_M/≈ → [0,1]` over
  `B̃(x)` (bisimulation classes). These are different domains with different
  cardinalities and different invariance properties (the ≈-class reading is what
  `OS-BisInv` T7 needs). `Spec-Def`'s synopsis "all five limits exist" repeats the
  five-class reading.
- **Engine resolution:** the body (≈-classes over B̃). `src/l6/aoi_full_proofs.rs::orbit_spectrum`.
- **Recommended fix:** update both synopses to the ≈-class domain (the five-class
  spectrum, if wanted, is a derived push-forward worth its own remark).

### A11. The `ℝ^ℕ` convergence profile and the Hölder rate clause import external order/arithmetic that CRPT's own discernibility machinery does not use
- **Labels:** L3.1.D5 `sig_M-NM` (profile ∈ ℝ^ℕ); L3.2.D4 `H_I^top` ("distinguishable
  (e.g., by Hölder exponent)"); cf. L4.1.R4 `Disc-Obs`, L1.1.D7 `Bisim~`, L6.3.D2
  `Tail-Eq`.
- **Issue (design-level, raised by the project owner):** every comparison CRPT's own
  framework performs is an equality — of observables, signatures, ≈-classes, traces
  (`Disc-Obs`: identical observer data = indiscernible; `Tail-Eq`: traces equal from
  some index). The raw `ℝ^ℕ` profile and Hölder-exponent comparison introduce an
  external ordered-field apparatus the theory never otherwise touches, and they are the
  source of issues A3 and (partly) A1.
- **Engine resolution:** the profile is realized as the orbit's **observation trace**
  (a metric instantiation codes its rate observables into obs); "rates distinguishable"
  = the approach orbits are **not pairwise tail-equivalent** under the labeled `≈`.
  All comparisons are CRPT-native equalities. (`src/l3/horizon.rs::convergence_profile`,
  `PersistentOrbitSignature`; `src/l3/classification.rs::invariant_horizon_topological`;
  trait data `observation` / `approach_orbits_tail_equivalent` in `src/l1/topology.rs`.)
- **Recommended fix:** restate the `sig_M-NM` profile component and the `H_I^top` rate
  clause in observation/tail-equivalence terms, demoting `ℝ^ℕ`/Hölder to a remark about
  how *metric instantiations* supply such observables. This simultaneously resolves A3's
  stabilization quantifier.

---

## B. Editorial (synopsis/body drift, notation, artifacts)

### B1. `PV2` (L4.3.T2): synopsis describes a different theorem
The synopsis is about the **finite orbit valuation** `PV_orbit(x) = Σ_{h ∈ ℋ_finite}`
under PA-WN; the body states **PV∞ existence** on infinite histories under
PA-NWF + PA-Prod + SC-1/2/3. The synopsis appears to belong to a PV1-style result.

### B2. `PV-Dual` (L4.3.T3): body restates `PV∞` instead of the stated duality
The synopsis announces the factorization `PV_M(x) = PV_M^fix(CNF_M(x)) · w-path(...)`;
the printed body and proof merely restate `PV∞ = lim PV` (L4.3.D6). The duality itself
is unproved in the text as printed.

### B3. `L-Str` (L5.3.D2) and `L-Th` (L5.3.D3): synopses attached to the wrong definitions
D2's synopsis describes the CRPT signature (D10's content); D3's synopsis describes the
model-correspondence functor (T1's content). Both bodies are the standard imported
definitions and are fine.

### B4. `Σ_CRPT` (L5.3.D10): synopsis/body symbol mismatch
Synopsis lists "a binary relation symbol ≃ for observable equivalence, and a constant
symbol 𝒯 for the topology"; the body's `R_CRPT` has `→_ρ, →_σ, Fix, In` (no ≃ — it is
definable, per the body's own remark) and handles the topology via the `Open` sort +
`In`, not a constant 𝒯. (And see A7: the obs labeling is missing from both.)

### B5. `SC-k` (L6.3.D12): tag/synopsis vs body
The tag and synopsis announce the scope-condition **family** SC-k (k ∈ {1,2,3,4,∞});
the body defines the **AOI hierarchy** `AOI_M(ρ^n(x))` and its termination — no general
SC-k is actually defined. (The engine realized the body:
`aoi_hierarchy_terminates_at`.)

### B6. `Inf-Dual` (L2.2.T7): two statement-level slips
(i) "there exist d ∈ ℕ such that `inf{...} = ∞`" — the quantified d is unused and the
quantifier shape is garbled (the intended statement is presumably "the depths are
unbounded"). (ii) clause (ii) applies `NFC_M(·)` to a persistent x
(`ι_{0→n}(NFC_M(x)) ∈ ∞_{Mₙ}`), but `NFC_M` is defined on fixpoints/convergent
elements. Also, the (i) hypothesis is stated via infinite σ-structure `G(f)` while the
proof argues from `|NFC_M(f)| = ∞` — the two conditions should be reconciled.

### B7. Source-line substitution artifacts (systematic)
Template substitution has leaked meaning-names and internal label styles into citation
lines, e.g. L4.1.R2: "Rutten [2000] Def (Projection Operator on (𝒰_M,the reduction
relation), Jacobs [2016] L2.3"; L8.7.D1: "(Street 1987, L1.1)" (external §-references
rendered as internal L-labels). A pass over **Source:** lines for `L\d.\d`-style refs to
external works, and for substituted phrases inside quoted material, would catch the
class.

### B8. `ω-Cat` (L7.2.D2): notation drift within one definition
The displayed sequence is `C = (D⁰, D¹, D², …, {F_n : D_n → D_{n+1}})` but the following
sentence reads "where each **M^n** is a model" — D vs M^n for the same objects.

### B9. `PV2` proof wording: "Under SC-2/3, the orbit is eventually periodic"
SC-2/SC-3 (L3.3.D3/D4) concern the **signature** and **valuation** sequences; orbit
eventual periodicity is SC-4 territory (and on the *class* level relates to SC-1 — see
A8). The proof's conclusion ("the sequence PV(h|_n) stabilises or has a well-defined
limiting product") is what the engine realized; the scope wording should cite the right
condition.

### B10. (Carried, pre-rc3, re-verify) L8.6 vs L8.10 section-label drift
Noted before rc3 for some supplementary lemmas; not re-verified line-by-line in rc3.
Harmless if still present, but worth a label sweep.

---

## Resolution dependencies (what the engine relies on)

If the spec agent resolves these differently from the engine's interim choices, the
following engine constructs/tests must be revisited:

| Issue | Engine dependency |
|---|---|
| A1 | `PersistentHorizonClass::FInfinity` inhabitation test |
| A2 | `certify_frequency_sum` scope; `complexity_class(None, true) = Two` |
| A3 | `n_reach`, `canonical_persistent_representative`, full `pa_reach` |
| A4 | `orbit_complexity` (tail κ); `OC-Per` test values `(0,0)` |
| A5 | `structural_horizon_topological`; D_∞/E_∞/F_∞ classifications |
| A6 | `denotationally_equal`; `certify_enc_injective` |
| A7 | `Substrate::observation`; `TopologicalProjectionSystem::observation`; `pa_bisim` |
| A8 | SC-1-dependent tests (Dirac spectrum, T16(b) counterexample) |
| A9 | `left_whisker`; `certify_strict_axioms` interchange scope |
| A10 | `orbit_spectrum` domain |
| A11 | `convergence_profile` (obs trace); `approach_orbits_tail_equivalent` |
