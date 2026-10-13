# CRPT Engine — Build Plan & Status

**Sole source of truth:** `../CRPT_OMEGA_TOWER_` (the ω-Tower spec, currently
**v1.0.0-rc3**). This plan orders the spec's constructs into an implementation sequence
and records the module layout. It adds nothing to the theory.

## One crate, structure = the tower's structure

`crpt_engine` is a **single crate**. The module hierarchy **mirrors the spec exactly**:
a module per level (`l1`…`l8`, `lomega`), and within each level a submodule per section
(e.g. `l2::projection` = L2.1, `l3::persistent` = L3.3, `l6::nwf_horizon` = L6.4). Each
item realizes a specific labelled spec construct, cited by its rc3 label.

> An earlier plan proposed *deriving* the module layout by applying CRPT to the engine's
> own construct graph (self-application). That was abandoned: rc2/rc3 `Lω.5.R2`
> (`SelfCons-NotGen`) confirms self-application is a self-consistency *certificate*, not a
> generative decomposition. The engine mirrors the spec's literal structure instead.
> (Self-application survives as the Lω.5 self-conformance *test*, `lomega::self_application`.)

## Trait ↔ data-orientation resolution

Traits/generics at exactly two spec locations: **L0** (the universal projection
framework, meant to be instantiated) and **L4.3/L5** (the value semiring `Semiring`,
morphisms `Φ`). Static dispatch / monomorphization, not `Box<dyn>`. Everything else:
concrete dense struct-of-arrays + free functions; correctness witnessed by `certify_*`
free functions. See `DETERMINISM_CONTRACT.md` and `DESIGN_PRINCIPLES.md`.

## Build order = the dependency DAG

Constructs are implemented in the spec's dependency order (acyclic by Lω.7). The pure-WF
core (∞_M = ∅) came first; the persistent/NWF apparatus was added once the convergent
core and the rc3 labelled bisimulation were in place.

## Status (implemented)

- **L0** the universal projection framework — `ProjectionSystem` trait, fiber `L_π` /
  `≃_π` / `Obs_π` (L0.1), with `CRPT-Fiber` (L0.1.T3) verified
- **L1** substrate (L1.1) · the nine PA-* projection axioms (L1.2/L1.3, decidable subset)
  · canonicalization modes finitary/topological/asymptotic (L1.4) · the PA-* scope
  profile Global/Scoped/Vacuous/Fails (L1.5)
- **L2** ρ_M/Model + C1/C2 (L2.1) · regime (L2.2) · depth d_M (L2.3) · canonical form
  (L2.4) · fiber/≃_M/Q_M (L2.5)
- **L3** horizons H_S/H_I/H_O + sig_M (L3.1) · six-class A–F, F=∅ (L3.2) · persistent
  invariants ω-limit/≃∞/Q∞/Sem (L3.3)
- **L4** observer 𝒪 (L4.1) · gateway (L4.2) · valuation/PV/semiring (L4.3) · regime
  μ/ν-fixpoint duality (L4.4) · CPD/CIH (L4.5) · self-projection SP-2 (L4.6) ·
  perturbation/CPEP detectability (L4.7)
- **L5** model algebra ×/𝟙 (L5.1) · homomorphism/Mod_CRPT (L5.2) · `T_CRPT` conformance
  / `Mod-Corr` / `FOL-Fin` (L5.3) · order ⊑/⪯ (L5.4)
- **L6** AOI: OT/AOI₁/OS/OC (L6.1) · orbit type P/EP/AP (L6.2) · NWF six-class A*–F*
  (L6.4) · regime-type determinacy (L6.5)
- **L7** Galois insertion α_M ⊣ γ_M + Collapse, total over Sem(M) (L7.1) · Lift ⊣
  Collapse (L7.2) · CRPT functor F : Mod_CRPT → ω-Cat (L7.3)
- **L8** FMA (L8.1) · Lift (L8.2) · Lift∞ (L8.5) · Tower (L8.4/8.9/8.10)
- **Lω** self-conformance test (Lω.5)

## The topological tier — founded (symbolic/infinite), being extended

A finite Hausdorff topology is discrete (a theorem), so `PA-WN_top` / topological mode
genuinely need an **infinite** universe. The engine represents those symbolically (as it
already does for `Lift`/`Tower`). The foothold is built (`l1::topology`): the
`TopologicalProjectionSystem` trait + the canonical `ConvergentChain` (`ℕ ∪ {ω}`) witness,
which **inhabits** `PA-WN_top` (L1.2.Ax7), topological-mode `CFix` on `∞_M` (L1.4.D1), and
`Mode::Topological`. Still to extend on this base:

- `sig_M-NM` on ∞_M (the topological orbit signature, L3.1.D5) and full `PA-Reach`
- `n_M`/`CPer` signature-stabilization dual (L3.3.D10)
- richer instantiations of `𝒯` (metric / order topologies, L1.4.R3) beyond the chain
- orbit complexity `OC > 0` / Type AP (L6.1.D3) — needs an infinite bisimulation quotient
- L6.3 AOI full-proof / recurrence-type machinery

## Genuinely meta / cross-model (out of scope by kind, not tractability)

- L4.6 `SP1` (cross-model composition) & `SP3` (Gödel encoding `Enc`); L4.7 full `CPEP`
  (∀ perturbations) & `CPEP-Ind` (independence, infinite countermodels); `RTD-Und`/`RTD-NI`
  (undecidability / non-internalizability) — realized as *bounds* on the engine, not constructs.

**The finite combinatorial tier is complete**; the topological tier is **founded** and the
infinite/symbolic representation is in place to extend it.

## Spec findings

rc1 findings resolved in rc2; the 7 post-rc2 engine findings resolved in rc3 (see
`SPEC_FINDINGS_RC2.md` and memory `crpt-spec-discrepancies`). The engine now tracks rc3.
