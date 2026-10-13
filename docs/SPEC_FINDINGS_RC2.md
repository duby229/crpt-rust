# Specification Findings — discovered during engine implementation (post rc2)

These are spec-level issues the `crpt_engine` implementation surfaced **after** v1.0.0-rc2
was released (the earlier rc1 findings — Class F, the spurious homomorphism `Φ_σ`, L0
status, self-application generativity — were all resolved in rc2 and are not repeated
here). Each is implemented to the *literal* spec text; where the literal text is
inconsistent or under-specified, the engine flags it rather than silently picking a
semantics. Labels are rc2 labels.

---

## 1. `Obs-Const` (L4.1.T1) over-states observer invariance — FALSE as written

**Where:** L4.1.D5 (`Obs-Triple`) / L4.1.T1 (`Obs-Const`).

**Issue:** The spec claims `x ≃_M y ⟹ 𝒪(x) = 𝒪(y)` — the observer triple is constant on
`≃_M`-classes. This is false for the per-element **PV** and **H** components: two
`≃_M`-equivalent elements (same canonical form) can have different derivation height
`d_M`, hence different six-class `H` and different orbit-length `PV`.

**Witness:** orbit `0 → 1 → 2` with `3 → 2`. Then `0` is Class A and `1` is Class B, yet
`0 ≃_M 1` (both have `CFix = 2`). Only the regime component `D` and the canonical form
`CFix` are `≃_M`-invariant.

**Suggested fix:** restrict `Obs-Const` to the `≃_M`-invariant data (`D`, `CFix`), or
redefine `𝒪` so the invariant-claimed part factors through `CFix`.

---

## 2. Bare `≈` + `≃_M` + `PA-Bisim` jointly force a UNIQUE normal form

**Where:** L1.1.D6/D7 (`Bisim`/`Bisim~`), L2.5.D2 (`≃_M`), L1.3.Ax1 (`PA-Bisim`).

**Issue:** `≈` is bisimulation on the *bare* `(𝒰, →_ρ)`. Under it **all normal forms are
bisimilar** — a normal form has no `→_ρ`-successors, so `{(a,b)}` for any two NFs is
vacuously a bisimulation. But `≃_M` is `CFix(x) = CFix(y)` (L2.5.D2), so distinct NFs are
**not** `≃_M`. `PA-Bisim` says `x ≈ y ⟹ x ≃_M y`. Composing the three literally: **any
model with two distinct normal forms violates `PA-Bisim`** — i.e. a CRPT model could have
at most one canonical form. This contradicts a multi-element `Q_M` and the entire
six-class theory (which presume many normal forms).

**Diagnosis:** the theory's `≈` cannot be the bare unlabeled `(𝒰, →_ρ)` bisimulation; it
must be a **labeled** bisimulation that distinguishes normal forms by observable content
(element identity, the Observable contract, or `→_σ`). L1.1.D6 as written is
under-specified. (Consequence the engine also hit: on bare `≈`, *every* persistent element
is bisimilar to every other, collapsing `Q∞_M`/Type EP — same root cause.)

**Suggested fix:** state L1.1.D6 over a labeled transition system (states carry observable
content), or define `≈` relative to `→_σ` / the Observable predicate, so `PA-Bisim` is
non-vacuous and multi-NF models exist.

---

## 3. `≃_M` is partial on ∞_M, and its relation to `≃∞` is unstated

**Where:** L2.5.D2 (`≃_M`), L1.3.Ax1 (`PA-Bisim`), L3.3.D7 (`≃∞`).

**Issue:** `≃_M = (CFix(x) = CFix(y))`, and on `∞_M` `CFix` is the *topological* limit
`lim ρ^n(x)` (requires `PA-WN_top`). So `≃_M` is undefined on `∞_M` whenever `PA-WN_top`
is absent (the native/asymptotic regime). L3.3.D7 introduces `≃∞` (equal ω-limit set) as
"the `∞_M` analogue of `≃_M`", but the spec never states (a) whether `PA-Bisim`'s
conclusion `x ≃_M y` should be read as `≃∞` on `∞_M` in the non-topological regime, nor
(b) whether `≃_M` and `≃∞` coincide on the `PA-WN_top` sub-class where both are defined.

**Suggested fix:** specify `PA-Bisim` (and any `≃_M` use on `∞_M`) to fall back to `≃∞`
in asymptotic mode, and state the `≃_M ↔ ≃∞` agreement on the topological sub-class.

---

## 4. FMA depth grading is self-contradictory (`FMA-Def` vs `Lift-Depth`)

**Where:** L8.1.D1 (`FMA-Def`) vs L8.2.C1 (`Lift-Depth`), Tower-Inf (L8.10.T2).

**Issue:** `FMA-Def` grades `FMA(A)` by **binary-tree** depth
(`depth(t₁·t₂) = 1 + max(depth t₁, depth t₂)`), but `Lift-Depth` and Tower-Inf require
`d_Lift(w) = |w| − 1` (**flat** word length). These disagree for every word of length ≥ 3.

**Suggested fix:** pick one grading — either define FMA depth as flat length `|w| − 1`, or
restate `Lift-Depth`/Tower-Inf in binary-tree-depth terms. (Engine uses `|w| − 1`, the
tower-relevant one.)

---

## 5. Lift strip direction / canonical form is inconsistent (`FMA-Proj` vs Inf-Dual)

**Where:** L8.1.D2 (`FMA-Proj`) vs the Inf-Dual remark (persistent-dual of Lift).

**Issue:** `FMA-Proj` defines `ρ_Lift(t₁·t₂) = t₁` — strip the **right** factor. The
Inf-Dual remark strips the **leftmost** factor (`ρ(ι[a₁]·…·ι[aₙ]) = ι[a₂]·…·ι[aₙ]`). Both
give `d = |w| − 1`, but they pick **different canonical atoms** (the first vs the last),
so `CFix` on `FMA` is ambiguous.

**Suggested fix:** fix one strip convention and make both locations agree. (Engine follows
`FMA-Proj` the definition: strip rightmost ⇒ `CFix` = first atom.)

---

## 6. `Collapse(M)` "discrete" (L7.1.R3) conflicts with κ being a homomorphism (L7.1.C4)

**Where:** L7.1.R3 vs L7.1.C4 (`Collapse-Hom`), L7.2.T1 (`Mod_CRPT_≃`).

**Issue:** R3 calls `Collapse(M)` *discrete* — "every class an isolated fixpoint", i.e. no
`→_ρ` edges. But for κ to satisfy the strict `Φ_R` (`x →_ρ y ⟹ κx →_ρ κy`), a class with
internal reduction needs a **self-loop** (`x →_ρ y` with `x, y` in the same class forces
`[x] →_ρ [x]`). Strict-`Φ_R` and "discrete" are mutually exclusive on non-trivial classes.

**Suggested fix:** state explicitly that κ is a homomorphism in the ≃-quotient category
`Mod_CRPT_≃` (condition up to ≃), **or** give `Collapse(M)` self-loops on non-trivial
classes (then it is not literally discrete). (Engine builds it discrete and treats κ as the
quotient map up to ≃, per `Mod_CRPT_≃`.)

---

## 7. L6.4 NWF horizon predicates use topological notions inside a topology-free tier

**Where:** L6.4.D1–D4 (`H_S*`, `H_I*`, `H_O*`, `A*–F*`).

**Issue:** L6.4.D4 classifies `∞_M` "under PA-NWF + PA-Bisim + SC-4" — explicitly the
**native, non-topological** tier (no `PA-WN_top`). Yet the predicates it depends on are
defined topologically: `H_S*` (L6.4.D1) is stated via the "topological fiber (elements
sharing x's topological limit under PA-WN_top)", and `H_S*`/`H_I*` use `≃_M` (which on
`∞_M` is the topological limit, see finding #3) plus `sig_M*` and `CPD`. So the Tier-1/2
(SC-4) classification invokes Tier-3 (`PA-WN_top`) machinery, which is circular for models
where `PA-WN_top` fails. The `≁_M` / `≃_M` / `≈` usages within the definitions are also not
disambiguated.

**Suggested fix:** restate `H_S*`/`H_I*` for the SC-4 tier using only `≈` / `≃∞` / `CPD`
(asymptotic-mode invariants) rather than the topological fiber and `≃_M`, reserving the
topological forms for the `PA-WN_top` tier. (Engine has *not* implemented L6.4 because a
faithful encoding is impossible until this is resolved.)

---

*Engine status note (not a spec issue):* `PA-Reach` (L1.3.Ax2) is only partially realized,
because it is stated over `sig_M-NM` (L3.1.D5, the non-terminating orbit signature), which
the finite engine has not yet built; the reachability skeleton is exact, signature
constancy awaits `sig_M-NM`.
