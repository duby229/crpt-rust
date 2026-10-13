# rc6 External-Review Assessment + Status-Label System Proposal

Audience: the specification agent. Assessed against **v1.0.0-rc6** (b9b95b4), construct
census 553 (167 definitions / 251 theorems / 126 remarks / 9 axioms), with every claim
below verified against the actual text (loci cited). Engine evidence cited where the
engine has computed the relevant mathematics.

Verdict scale: **VALID** (survives against rc6 text) / **PARTIAL** (kernel of truth,
wrong strength or wrong locus) / **INVALID** (contradicted by rc6 text or by theorems
the engine has verified computationally).

---

## Part 1 — Verdicts

### ChatGPT's ten surviving issues

| # | Claim | Verdict | Basis |
|---|---|---|---|
| A1 | Strict tower growth `Mₙ < Mₙ₊₁` not a closed theorem | **PARTIAL — and the conjecture is FALSE as posed** | See Resolution R1: strictness of *isomorphism type* fails for n ≥ 1 (it contradicts `Twr-Tail-Sim` L8.9.T1, which rc6 proves); the truth is a trichotomy, and the L8.4 synopsis ("strictly richer… more elements") is itself wrong for n ≥ 1 |
| A2 | Axiom-minimality matrix incomplete | **VALID** | L1.6 carries only `Ax-Ind` (L1.6.T1) + `No-Split` (R1) — no per-axiom removable/derivable/independent matrix. Resolution R2 |
| A3 | Higher-categorical claims carry largest proof burden | **PARTIAL** | rc6 closed much of it: `Lift-F` functor laws are now stated-and-verified (L7.2.D4 + companion, "Lift(id) = id, Lift(ψ∘φ) = …"); `Twr-ωCat-T` interchange was scoped in rc4. Remaining: `Behav-F` naturality (see R5) |
| B1 | "Model" misaligned with model theory | **INVALID since rc4** | The L5.3 Tarski kernel makes `M ⊧ T_CRPT` literal Tarski satisfaction (`⊧` L5.3.D4, `Mod-Corr` L5.3.T1, `FOL-Fin` L5.3.T4) — and the engine *executes* it (`certify_tarski_agrees_with_native`). CRPT models are structures satisfying a theory, in the standard sense. Optional: a remark distinguishing the satisfaction layer from the categorical-semantics layer |
| B2 | "CRPT is a model of itself" stronger than construction | **PARTIAL** | `SelfCons-NotGen` (Lω.5.R2) already demotes self-application to a certificate; rc6's `Spec-Sub` (Lω.8.D1) makes the self-reading literal (the spec IS a pure-WF CRPT model, census-checked). The remaining gap is wording: state the theorem as "Self_CRPT ⊧ T_CRPT" (checkable by the same kernel) and avoid slogan forms |
| B3 | "Lift" imports unintended meanings | **PARTIAL (terminology)** | The construction genuinely IS free ("free monoidal algebra", `FMA-UD`); "free lift" is defensible. Add a one-line disambiguation remark (not a lifting property/fibration). Low priority |
| B4 | Projection carries reduction-theory baggage | **VALID — and it is a *status-label* defect, not a vocabulary defect** | `ρ_M` (L2.1.D1) is **Reframed** with the justification compressed into a Source-line fragment ("Cousot & Cousot — the abstraction step; reframed as the deterministic projection strategy"). The true basis is dual (ARS reduction strategy + abstract-interpretation abstraction step) and the reframing *reason* (canonicalization read as information projection — the theory's founding move) is exactly what the body should state. Resolved by Part 2's Reframing Discipline, with ρ_M as the flagship Reframing Note |
| B5 | "Observer" too philosophical | **PARTIAL** | The spec already names the alternative: "**Observable Triple** (formal name used below)" (L4.1.R2). Adopt the already-listed formal name as primary; "observer" survives as the epistemological gloss in the remark |
| B6 | "Ontological horizon" misread | **VALID (naming)** | The construct's own meaning-name is "Abstraction Depth Horizon" (H_O, L3.1.D4); "ontological" appears only as legacy gloss. Standardize on the meaning-name |
| C1 | Vocabulary lags the mathematics | **VALID in aggregate** | Subsumed by the status-label system (Part 2) + B5/B6 renames. The reviewer's own table maps 1:1 onto label-discipline fixes |

### Gemini's five "critical" issues

| # | Claim | Verdict | Basis |
|---|---|---|---|
| I | `Mod-∘`/`Mod-×` collapse coordinate-wise | **VALID — confirmed verbatim** | L5.1.D2 `Mod-∘` and L5.1.D4 `Mod-×` define the *identical* operation (universe product, componentwise ρ), both **Imported** from the *same* source clause ("Mac Lane §I.3 — categorical product"). `Mod-×`'s synopsis promises a distinction ("unlike composition (∘), which may impose interaction") that `Mod-∘`'s definition does not contain — no coupling mechanism exists, and `Mod-∘` has **no →_σ clause at all**. Additionally "composition" *misnames* a product (Mac Lane's composition composes morphisms) — a double import-discipline violation. Resolution R3 |
| II | `Mod-∩` non-total (empty intersection) | **PARTIAL — observation right, corrective wrong** | The partiality is real. But the proposed fix (admit the empty model 𝟘) **violates the import discipline the spec is built on**: `L-Str` (L5.3.D2, Imported, Chang–Keisler/Hodges) requires *non-empty carriers* — standard model theory excludes empty structures, and `Mod-Corr` rides on that import. The mathematically correct resolution is the standard one: `Mod-∩` is a **partial meet** (defined when universes intersect non-trivially), stated as such. Resolution R4 |
| III | Galois insertion fractured across regimes; wants terminal-coalgebra unification | **INVALID as an error; rejected as a corrective** | The "fracture" *is* the regime partition — exhaustive and exclusive (`Part` L2.2.T3), the theory's spine. rc4's PA-Reach already unifies the destination semantics (one meaning, two realization mechanisms, `PA-Reach-Decomp` proves no third), and `π_sem` is total on `Sem(M) = Q_M ⊔ Q∞_M`. A terminal-coalgebra target would trade C1-determinism and finite presentability for machinery yielding no new theorems. Optional: a remark stating the coproduct structure is regime-principled, citing Part + PA-Reach-Decomp |
| IV | FMA strip "destroys" compositional data | **INVALID — the objection restates a theorem as a bug** | The depth reset is `Inf-Dual` (L2.2.T7)(iii), and clause (iv) states precisely that the data is **re-encoded, not lost** ("infinities are transformed", `Infinity-Cycle` R8). The proposed accumulation domain would destroy freeness (`FMA-UD`) and the query-signature invariant (`NFC-TInv` L8.4.T2) — i.e., the tower itself. Add a preempting remark at `FMA-Proj` citing Inf-Dual(iii)/(iv) |
| V | Single-valued ρ erases higher structure of HoTT/Cat | **INVALID as flaw; documented boundary** | Misreads the two-level design: **→_ρ is a relation** (multi-valued, substrate-level); `ρ_M` is the *strategy* over it (C1). Higher structure lives in →_σ/obs/branching →_ρ. `Inst-Emb`'s own synopsis already states D may carry structure invisible to ρ_D, and `Iso-Sat` (L5.2.T7) marks saturation as the special case. The corrective (multi-valued ρ) abolishes C1 — the determinism the entire canonical-form theory rests on. Keep as documented expressive boundary |

### Copilot's meta-verdicts (on the third list)

Spot-checked against rc6; its gradings are mostly correct. Two updates: item 18
(`Lift` functoriality "not stated") is **now resolved** — rc6 states and verifies the
endofunctor laws (L7.2.D4 + L7.2's companion theorem); item 16's pushback is right —
`AOI` completeness IS stated (L6.1.T4 / `OC-WD`). Items 1–2 (Behav-F naturality;
observer-triple/homomorphism preservation) remain **VALID** and are picked up in R5.
Items 9–12 (novelty attribution) are absorbed wholesale by the status-label system.

---

## Part 2 — Chosen resolutions (mathematically preferred)

### R1. Tower growth: close it *negatively* — the trichotomy theorem
The engine's computed facts: `Lift(M) = FMA(Q_M)`; `Q` is tower-invariant
(`NFC-TInv`); hence for n ≥ 1, `Mₙ₊₁ = FMA(Q_{Mₙ}) ≅ FMA(Q_{M₀}) ≅ Mₙ` — **the
isomorphism type stabilizes after one Lift**. This is not a defect: it is the finite
form of fractality, and rc6's `Twr-Tail-Sim` (L8.9.T1) already implies it. The sought
"strictness theorem `Mₙ ≇ Mₙ₊₁`" is therefore **false** for n ≥ 1. Add one theorem
("Tower Growth Resolution") stating the trichotomy:
1. `ιₙ : Mₙ ↪ Mₙ₊₁` is always a **proper** faithful embedding (growth in the embedding
   order — never surjective);
2. `Mₙ ≅ Mₙ₊₁` for all n ≥ 1 (isomorphism-type stabilization = fractality made
   element-wise);
3. `M₀ ≇ M₁` iff M₀ is not itself free on its own Q (e.g. every finite M₀ with a
   non-fixpoint).
**And correct the L8.4.D1 synopsis**: "each level is a strictly richer CRPT model:
more elements" is false for n ≥ 1 (equal cardinality, isomorphic); the truthful phrase
is "each level properly embeds in the next; from level 1 the type stabilizes — the
tower grows in embedding structure, not in isomorphism type."

### R2. Complete the L1.6 axiom matrix
A 9-row table: for each PA-\*, three columns — *derivable?* (e.g. PA-CoInd ⊢ from
PA-NWF, L1.6.T1), *independent?* (witness model, e.g. `M_Reach`), *removable?* (which
theorems fall). Each independence cell gets a finite or symbolic countermodel — the
engine can certify every witness computationally (it already realizes `M_Reach`).

### R3. `Mod-∘`: delete it
One source concept (Mac Lane's product) may ground one construct. Keep `Mod-×`
(honest import; fold `∘-Assoc` into the product's monoidal structure), **delete
`Mod-∘`** and its promise of "interaction" that nothing delivers. If a genuine coupled
composition is ever wanted, it must arrive as **Novel** with real content (an explicit
coupling relation ℛ_C ⊆ 𝒰₁ × 𝒰₂ and theorems about it) — Gemini's formula for the
product's →_σ (componentwise interleaving) is correct and should be added to
`Mod-×`'s body, which currently leaves →_σ unstated.

### R4. `Mod-∩`: partial meet, by the import discipline itself
Non-empty carriers are part of the `L-Str` import (Chang–Keisler convention) that
`Mod-Corr` depends on. Admitting 𝟘 would silently break that import. State `Mod-∩`
as a partial operation (defined iff `𝒰₁ ∩ 𝒰₂ ≠ ∅` and the restriction closes under
ρ/→_ρ), with the partiality named in the synopsis. The model algebra is a partial
algebra; that is the standard, honest price of standard model theory.

### R5. The two surviving observer-side proof obligations
1. **`Behav-F` naturality** (L4.1.D1, Imported, calls itself a natural transformation):
   either construct the behavior functor on Mod_CRPT and prove the square, or weaken
   the claim to "the coalgebra observable map" (Specialized import of Rutten) without
   the naturality assertion. Recommended: prove it — the square commutes exactly on
   the ≃-quotient category (the engine can certify it model-by-model, as with η-Nat).
2. **Observer-triple preservation under Hom**: state the true component-wise theorem —
   `D` (regime) is preserved by every homomorphism; the `CFix`-class is preserved via
   Φ_E; `H` and path-`PV` are *not* preserved in general (the engine has
   counterexamples: ≃-equivalent elements already differ in H). An honest
   "preservation profile" theorem kills the expectation mismatch permanently.

---

## Part 3 — The status-label system (owner observations 1–3)

### The defect, in one construct each
- **Import violation:** `Mod-∘` — imports Mac Lane's *product* under the name
  *composition*; the import is real, the term/meaning transport is not.
- **Under-justified reframing:** `ρ_M` (L2.1.D1, Reframed) — the single most important
  reframing in the theory (reduction → projection) justified only by a Source-line
  fragment.
- **Inflated novelty:** 447 of 553 constructs are **Novel** (81%). Spot-checks show
  several are consequences or specializations of their imports (`HC-Obs`: standard
  classifier over the novel six-class; `Inst-Emb`: standard faithful embedding,
  novel only in the regime-split clauses; `PV-Obs`: imported path valuation + CRPT
  orbit form under one label).

### The proposed label set
Five statuses, each with a **mandatory body obligation**, all auditable by census
(extending `Sect-Census` Lω.8.R1 — the labels become part of the Spec-Sub self-model:
a construct's status *is* its relationship to its Source anchor):

| Status | Criterion | Mandatory body obligation |
|---|---|---|
| **Imported** | Complete and correct transport: the source's *term, notation, name, and meaning* preserved exactly; CRPT contributes placement only | Precise source citation (work + §). Any deviation in term/notation/meaning **disqualifies** the label |
| **Specialized** | An imported construct restricted to a CRPT domain with **no semantic change** — the restriction is the only delta | A *Specialization clause*: "the general form is X (source); here restricted to Y" (e.g. `Ker-Cong`, `Tail-Eq`, `Iso`) |
| **Reframed** | Maximal import + the **minimal delta required for the stated purpose** | A *Reframing Note* in the body: source form → CRPT form, the exact delta, and the justification (mathematical reasons preferred; conceptual reasons admissible and stated as such). Flagship: ρ_M's note — ARS reduction strategy + abstraction step, reframed because CRPT reads canonicalization as information projection; delta = the projection vocabulary + C1–C3 packaging; nothing else changes |
| **Derived** | A consequence of imported/prior constructs composed; **no new mathematical content** beyond the composition | The derivation chain (which anchors compose, in one line). Absorbs the misfiled Novels |
| **Novel** | Genuinely new content | A *Novelty Note*: the imported basis (maximal — everything that is *not* new, credited), the precise statement of what **is** new, and why it does not follow from the basis |

Migration: one census pass over the 553 constructs re-classifying against the five
criteria; the expected bulk moves are Novel → Derived/Specialized (this *strengthens*
the theory's real novelty claims by isolating them), plus the per-label body
obligations back-filled. The audit tooling already validates status values; extend it
to validate the body obligations (Reframing/Novelty notes present where required).

This single mechanism resolves owner observations 1–3 and ChatGPT items B1–B6/C1 and
Copilot items 9–12 at the root.

---

## Part 4 — Text artifacts (owner observations 4–5)

### 4a. The "crossed-out line" — ASCII tilde strikethrough
GitHub-flavored markdown renders single-tilde-delimited runs as strikethrough.
Census: **7 lines** across `L3.md`, `L5.md`, `L6.md` carry two or more bare ASCII `~`
in prose/math (e.g. L5.md:109 — the `Mod-/` synopsis "the quotient model M₁/~ for a
compatible equivalence relation ~ on 𝒰…"; L6.md:588 `Tail-Eq`; L6.md:670 `[OT(x)]_~ =
[OT(y)]_~`). **Fix:** replace the ASCII tilde with U+223C `∼` (TILDE OPERATOR) in all
mathematical uses — typographically correct for the math *and* render-safe — or
code-span the symbol. Sweep pattern: lines matching `~.*~` outside URLs.

### 4b. Mojibake in headings (worse than cosmetic — they are anchors now)
Four UTF-8-as-Latin-1 corruptions sit in **heading lines**, and rc6's hyperlink pass
(f7008fa) made headings the anchor targets, so these corrupt link targets too:
- `L0.md:341` "### Boundary Layer vs. H_O^Ï" (= H_O^π)
- `L2.md:61` "### Ï_M as Regime-Neutral Projection" (= ρ_M)
- `L2.md:974` "### Antisymmetry of â¤_Ï" (= ≤_ρ)
- `L1.md:1216` "### CCS, Ï-Calculus, Petri Nets Are Compliant" (= π-Calculus)
**Fix:** repair the four + a byte-level sweep for the class (`Ï`, `â`, `Ã` byte
sequences) across all files, then re-run the anchor audit.

### 4c. L0 labels on heading lines
L0 alone puts construct labels in headings ("### L0.1.D1 — Projection System") while
every other level uses meaning-name headings with the label in the table row — the
label is duplicated and the L0 anchors are label-shaped instead of meaning-shaped.
**Fix:** normalize L0 headings to meaning-names only (labels live in the table row,
as everywhere else), and re-anchor the affected links in the same pass as 4b.

---

## Summary for the specification agent

**Adopt:** R1 (trichotomy theorem + L8.4 synopsis correction), R2 (axiom matrix), R3
(delete `Mod-∘`, add the product's →_σ), R4 (`Mod-∩` partial meet), R5 (Behav-F
naturality + preservation profile), Part 3 (five-status system + census migration +
body obligations), Part 4 (tilde → ∼, mojibake repair, L0 heading normalization).

**Reject, with grounds recorded:** Gemini III (regime coproduct is principled), IV
(restates Inf-Dual as a bug; corrective destroys freeness), V (misreads the
relation/strategy split; corrective abolishes C1), Gemini II's empty-model corrective
(violates the L-Str import), ChatGPT A1's strictness conjecture (false for n ≥ 1 —
the engine's `NFC-TInv`/`FMA` facts close it the other way).

The engine stands ready to certify computationally: every R2 independence witness,
the R1 trichotomy on finite bases, R5's preservation profile, and (post-migration)
the status-census obligations.
