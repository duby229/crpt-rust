# Second-Order Commitments — the engine's discipline

CRPT makes genuine **second-order** commitments (quantifiers over relations / predicate
transformers). Read naively a quantifier `∃R / ∀R` over `𝒫(𝒰²)` is `2^(n²)` — intractable.
This document records how the engine handles every one of them: **exactly**, in polynomial
time, grounded in the ω-Tower spec itself and confirmed by the anchor instantiations.

## The one mechanism

> Every second-order commitment CRPT actually makes is a **least or greatest fixpoint of a
> monotone operator on the finite powerset lattice**. By Knaster–Tarski the extremal
> fixpoint exists and, on a finite lattice, is computed by Kleene iteration in `≤ |𝒰|`
> steps. This is `O(n²–n³)`, not `2^(n²)`, and it is **exact**, not an approximation.

**Why exact (not a tractability hack):**

- **`FOL-Fin` (L5.3.T4)** is a *biconditional*: on finite models `T_CRPT` collapses to its
  first-order fragment, and a finite structure is a CRPT model **iff** it satisfies
  `T_CRPT^FOL`. The `∃R` of a second-order axiom reduces to its canonical first-order
  witness relation — which is the extremal fixpoint.
- **`Reg-FP` (L4.4.T1)** already states a flagship case inside the ω-Tower: the regimes
  *are* the `μ/ν` decomposition (`↓_M = μT_conv`, `∞_M = νT_pers`).
- **Anchor coalgebra instantiation, Thm 3.5**: "*for any monotone `F'`, `νF'` exists — by
  Knaster–Tarski, `νF' = ⋃{X | X ⊆ F'(X)}*". The final coalgebra `νF` — the canonical home
  of coinduction — is a greatest fixpoint, built by **Adámek's terminal chain**
  `𝟙 ← F𝟙 ← F²𝟙 ← …`, which on accessible/bounded (finite) functors terminates. That
  terminal chain, in the powerset case, *is* Kleene iteration / partition refinement.
- **Anchor CCS instantiation**: `≈` = strong bisimilarity = greatest fixpoint of the
  bisimulation operator; Type AP is "non-finite-control" (infinite-state) — so on finite
  state there is no AP and `≈` is computed by partition refinement.

The realization lives in [`src/lattice.rs`](../src/lattice.rs): `least_fixpoint` /
`greatest_fixpoint` over monotone operators on dense `Vec<bool>` bitmaps.

## The two sources the spec names — both resolved and *proven*

`SO-Ext` (L5.3.D6) lists what needs second order — "transitive closure `→_ρ*`, divergence,
bisimulation, and coinduction" — and `T_CRPT` (L5.3.D11) states `T_CRPT^SOL` "adds the
**bisimulation** and **transitive-closure** axioms." Those are the two `∃R`-over-relations
sources, and they are exact duals:

| Source | Spec form | Fixpoint | Engine — *proven* against the fast path |
|---|---|---|---|
| **Bisimulation** `≈` | `∃R[R a bisimulation] ∧ R(x,y)` (L5.3.R5) | **greatest** `νB` | partition refinement = `νB`: `Substrate::bisimilarity_is_greatest_fixpoint` |
| **Transitive closure** `→_ρ*` | `∃R[R ⊇ →_ρ ∪ id, transitive] ∧ (x,y)∈R` (L5.3.2.4) | **least** `μT` | BFS reachability = `μT`: `Substrate::reachability_is_least_fixpoint` |

So both relation-quantifier sources are computed by the same Knaster–Tarski combinator
(`νB` coinductively, `μT` inductively) and each is *verified* to equal the engine's
efficient production path. Divergence (`Div`) is the persistent-set fixpoint; coinduction
(`PA-CoInd`) is the proof-principle case below.

## The four categories (every SOL commitment is tagged)

| Kind | Commitments | Realization |
|---|---|---|
| **Fixpoint** | `≈` (L1.1.D7); `→_ρ*` (L1.1.D4); `↓_M`/`∞_M` (L4.4); `C2`/`PA-Bisim` (use `≈`) | Computed and **proven** against the fast path: `≈` = `νB` (`bisimilarity_is_greatest_fixpoint`); `→_ρ*` = `μT` (`reachability_is_least_fixpoint`); `↓_M`/`∞_M` = `μ`/`ν` via `lattice` (`l4::duality`). |
| **Proof principle** | `PA-CoInd` (L1.2.Ax5, Park's lemma); induction on `d_M` | **Not** a check over all `Φ`. Realized *as the correctness of* `lattice::greatest_fixpoint`/`least_fixpoint` (Knaster–Tarski). The combinator's existence *is* the principle instantiated; `lattice::is_fixpoint` witnesses it per use. |
| **Infinitary** | `OC > 0` / Type AP (L6.1.D3, Borel rank in `Q_M^ω`); `sig_M-NM` on ∞_M (topology) | Genuinely need infinite objects. On finite they provably degenerate (`OC ≡ 0`, no AP). Out of scope **by mathematical necessity**, not tractability. |
| **Meta** | `RTD-NI` (L6.5.T4): quantify over all models; the model-correspondence | Realized by **parametricity**: a total `fn f(m: &Model) -> …` *is* the universal "∀ models". The quantifier becomes the function signature. |

## The line we draw

We **never enumerate the powerset**. The claim that makes this safe: *CRPT never requires a
second-order witness that is not an extremal fixpoint (or `FOL-Fin`-reducible to one).* If a
future construct genuinely needed `∃R.Ψ(R)` with `R` neither a fixpoint nor `FOL-Fin`-reducible,
it would be treated as **infinitary** (deferred, with the necessity reason stated) rather than
brute-forced. Every second-order commitment found in the ω-Tower so far is monotone-fixpoint-shaped.
