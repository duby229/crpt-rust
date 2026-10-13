# Specification Section Scope vs. Engine Modules — Assessment Request (v2)

Audience: the specification agent. Engine version: rc4-aligned, 135 tests.

## The governing principle (owner-mandated, two-sided)

**Engine side:** the module set mirrors the section set **bijectively** — every module IS
a spec section, every labeled construct lives in its label's section module, and no
module may exist that is not a section.

**Spec side (the half this document is about):** for that bijection to be *natural* —
never a thin stub module, never a grab-bag — **every specification section must have a
finite, well-defined scope**: a scope that owns real content, whose implementation is a
substantive module. A section whose entire content is a restatement of another section
has zero net scope; a coherent body of theory with no section is a missing section; a
section boundary that cuts through one indivisible object is an ill-drawn boundary.

The engine does **not** want compensating devices (thin delegating modules, documented
exceptions). Where the bijection fails today, the request is that the **spec re-scope**
so it holds naturally. v1 of this document offered such devices as options; they are
withdrawn.

---

## A. Engine-side misplacements — fixed (no spec action)

| Was | Finding | Resolution |
|---|---|---|
| `src/lattice.rs` | Homeless module — but its content **is** L0.7 "Universal SOL Necessity" (the Knaster–Tarski combinator realizing every SOL commitment) | Moved to `l0/sol_necessity.rs`. L0.7's scope was well-defined all along; the engine had simply not recognized the section. Confirm intended |
| `src/l7/galois.rs` | Two modules for L7.1 | Merged into `l7/collapse.rs` — the section title "Abstraction as Epimorphism / Collapse" names exactly both halves; L7.1's scope is well-defined and the merged module is its natural unit |
| `src/l6/tier.rs` | Module named for a definition (L6.2.D2), not a section | Merged into `l6/orbit_type.rs` (L6.2) |

These three confirm the principle works when section scope is well-defined: the module
is substantive and the bijection is natural.

---

## B. Sections whose scope needs a spec ruling

### B1. L1.2 "The Axiom System" / L1.3 "Universal Axioms" — is the boundary a scope?
One axiom system (all nine listed by `PA-NS` L1.2.R1; treated uniformly by L1.5, L1.6,
L5.3) is divided across two sections. For the bijection to hold with two substantive
modules, **each section needs a stated membership criterion** — a finite, well-defined
scope. The rc4 PA-Reach commit supplies a candidate: the four recursive-projection-axiom
criteria. **Ruling requested:** either (i) state the L1.3 criterion in the section
header (then L1.3's scope is well-defined: the recursive-projection axioms PA-Bisim +
PA-Reach with `CPer`, the realization theorems T2–T4, `M_Reach` — a genuinely
substantive module, and the engine splits accordingly), or (ii) merge L1.3 into L1.2
(one section, one module). The engine currently holds one module spanning both, pending
this ruling.

### B2. The topological tier — a coherent scope with **no section** (missing section)
The 𝒯-apparatus is a finite, well-defined, *coherent* body of theory: the 𝒯 component
(L1.1.D1), `TopSep`/`Top-Lim` (L1.2.D1/D2), `PA-WN_top` (L1.2.Ax7), convergence-mode
`CFix` and the `Top-Inst` witness family (L1.4.D1/R3), `PA-Reach-Top` (L1.3.T3), plus
the presentation data the higher levels consume. In the engine it is one indivisible
carrier (the `TopologicalProjectionSystem` trait + the `ℕ ∪ {ω}` witness) — a
*substantive* module with no section to be. This is the clearest case of the spec-side
principle: **the scope exists; the spec has not sectioned it.**
**Ruling requested:** add the section (e.g. "L1.x — The Substrate Topology"), collecting
the 𝒯-apparatus the way L1.5 collects the profile apparatus. The engine module then maps
1:1 with no residue. (The alternative — distributing the trait across L1.1/L1.2/L1.4 —
is exactly the boundary-through-an-indivisible-object failure the principle forbids.)

### B3. Derived-theory sections must own their scope — or be subsections
**L0.2–L0.4** relative to L0.1, and **L8.6/L8.9/L8.10** relative to L8.4: their content
is the derived theory of the preceding section's object. Under the principle there are
exactly two coherent outcomes, and *thin certificate modules are not one of them*:

- **(i) The section owns a real scope** → the engine implements it as a substantive
  module. This is available: L0.2 "Universal Orbit Fate Classification" owns
  `Conv`/`Pers`, the regime coincidence certificates, and the fate theory; L0.3 owns the
  three universal horizon predicates and their kernel theory; L0.4 owns `Q1` and the
  stratification. The engine would convert the corresponding trait defaults into
  section-owned free functions (generic over the L0.1 carrier — the established
  pattern), making each module genuinely substantive. Same shape for L8.6 (the
  horizontal-vertical duality theory: `Twr-Img`, `Twr-Disc`, the duality certificates),
  L8.9 (fractality), L8.10 (the supplementary results).
- **(ii) The spec demotes them to subsections** of L0.1 / L8.4 (one section, one
  module, scope = object + its derived theory).

**Ruling requested:** (i) or (ii), per section. The engine implements either — what it
cannot implement is the current state, where the sections exist but their content's
natural home is another section's carrier.

### B4. Reprise sections have zero net scope — re-scope or merge
- **L4.8 "The Empty Field: Class F = ∅"** — currently a restatement anchored in L3.2
  (rc2 made L3.2 canonical). Zero net scope as it stands. **Either** give L4.8 its own
  finite scope (the emptiness *theory*: `ClassF-Def`, `F=∅`, its observer-side
  consequences — then the engine moves that content into a substantive `l4` module)
  **or** merge L4.8 into L3.2.
- **L5.5 "The Category of CRPT Models"** — `Mod_CRPT-Cat` defers to L5.2.D1, and L5.2's
  own title already names the category Mod_CRPT. **Either** scope L5.5 as the category
  theory proper (identity/composition laws, functor targets — the engine would move
  `Homomorphism::identity`/`compose` and the category certificates there, a substantive
  module) **or** merge L5.5 into L5.2.
- Generalize: rc4's "restates" markers on L5.3.D13–D15 are the right device — but a
  *definition-level* marker. At *section* level, the principle demands there be no
  reprise sections at all: every section either owns scope or is merged.

### B5. One theorem, three homes — confirm the scope division
`Inf-Dual` is stated at L2.2.T7, has its universal template at L0.6, and its tower-level
theory at L8.6. This is acceptable **iff** each of the three scopes is well-defined
(statement / universal form / tower theory) and cross-referenced. **Ruling requested:**
confirm that division explicitly in the three section headers; the engine's placements
(l2/regime.rs for the L2.2 statement; L8.6 pending B3; L0.6 pending B3) then follow.

### B6. Lω section granularity
The engine realizes Lω.5 (`SelfCons`). **Rulings requested:** (i) confirm Lω.5 is the
canonical home of the self-conformance certificate (engine renames its module to the
section's meaning-name); (ii) clarify L0.10 vs Lω.5 scope division; (iii) confirm
Lω.1–Lω.4, Lω.6–Lω.7 carry no implementable definitions beyond the totals' 2 — if any
of those sections has no implementable scope, that is acceptable (not every section
must have a module — the bijection constrains modules, not sections; but every section
that *induces* a module must have well-defined scope).

### B7. Section-heading grammar inside L6.3
"## LEVEL 1/2/3 — …" headings inside L6.3 parse as top-level sections and break the
`## L<k>.<j>` grammar that the bijection (and tooling) reads. Demote to `###`.

---

## C. The placement discipline — request for ratification (revised)

1. **Module set = section set**, bijectively, named by the section's meaning-name.
2. **Every section that induces a module has a finite, well-defined scope** (spec-side
   obligation); its module is the substantive implementation of exactly that scope. No
   thin modules, no stubs, no grab-bags — their appearance is a sectioning defect, fixed
   in the spec, not papered over in the engine.
3. **Carrier objects** (one trait, one struct — indivisible) live in the section that
   defines them; their interface carries that section's constructs plus the
   finitely-presented data queries other sections consume (documented with consumer
   labels).
4. **Other sections' constructs over a carrier are free functions in their own section's
   module**, generic over the carrier — substantive because the section's scope is real
   (the pattern already governing L3.2-over-the-topological-carrier).
5. **No reprise sections**: every section owns scope or is merged into its anchor.
6. Cross-section/cross-level imports are unrestricted; the dependency DAG governs build
   order, not placement.

---

## Engine state pending these rulings

- `l1/axioms.rs` spans L1.2+L1.3 — held, pending **B1**.
- `l1/topology.rs` — held as the would-be module of the **missing section** (B2).
- `l8/tower.rs` spans L8.4/L8.6/L8.9/L8.10 — held, pending **B3** (the engine is ready
  to implement (i): substantive per-section modules from the derived theory).
- L0.2–L0.4 trait defaults — held in L0.1, pending **B3**.
- L4.8/L5.5 content — held with anchors, pending **B4**.
- All Category-A fixes complete; 135 tests, 0 warnings.
