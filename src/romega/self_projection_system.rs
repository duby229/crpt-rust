//! # Rω.1 — CRPT as Its Own Projection System
//!
//! Exact realization of spec section **Rω.1** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9):
//!
//! - Rω.1.D1 `U_CRPT` — the self-substrate `𝒰_CRPT`: the tower's own labelled constructs
//!   (ranks R1–R6 and Rω; R0 is the external meta-foundation and is **not** a member). It
//!   carries **two** relations: the **dependency** relation `→_{ρ_CRPT}` (`X →_ρ Y` iff `Y` is
//!   a direct prerequisite of `X`; acyclic) with `ρ_CRPT(X)` = `X`'s most primitive direct
//!   dependency, and the **cross-reference** relation `→_{σ_CRPT}` (citation; `→_ρ ⊆ →_σ`),
//!   which — through forward references and mutual citations — is **non-well-founded**.
//! - Rω.1.T1 `Self-Model` — the self-substrate is a genuine CRPT instance (C1/C2); on the
//!   **dependency reading** it is pure-WF (`∞_CRPT^ρ = ∅`, R1.1.D1 the unique fixpoint —
//!   `CRPT-WF` Rω.7.T1, scoped to this reading).
//! - Rω.1.D2 `Self-Inf` — the **structural persistent aspect** `∞_CRPT^σ := νT_pers(→_σ_CRPT)`,
//!   whose recurrent heart is the σ-strongly-connected core; it is **non-empty**.
//! - Rω.1.T2 `Self-Mixed` — the faithful self-model is **Mixed**, its **dual aspects** the two
//!   HV-dual readings of one self-projection (`Min-Interp`): `ρ_CRPT` the vertical/observable/WF
//!   axis (`↓^ρ = 𝒰`), `→_σ_CRPT` the horizontal/structural/NWF axis (`∞^σ ≠ ∅`).
//! - Rω.1.T3 `Self-InfDual` — `Inf-Dual` at the self level: the σ-NWF aspect lifts under `Reify`
//!   to the meta-tower's vertical NWF (`Tower-of-Towers`, `Self-FP`); instantiates `WF-NWF-Dual`.
//!
//! **Realization.** The self-substrate is a concrete [`Instance`] over the tower's dependency
//! DAG (the acyclic `→_ρ`), with a **distinct** `→_σ` that adds forward-citation cycles (the
//! σ-recurrent core). `Self-Model` is certified by the same `Instance` C1/C2 validation as
//! every rank; `Self-Inf`/`Self-Mixed` are certified by SCC analysis of `→_σ_CRPT` — CRPT
//! recognizing both of its own faces.

use crate::r1::reduction_strategy::Instance;
use crate::r1::substrate::{ElementId, Substrate};

/// `R1.1.D1` — the substrate definition, the unique dependency root / fixpoint of `ρ_CRPT`.
pub const R1_1_D1: ElementId = ElementId(0);

/// The self-substrate's element labels (Rω.1.D1), index-aligned with the [`Instance`]
/// returned by [`self_substrate`]. Index 0 is the root R1.1.D1; thereafter each rank R1–R6
/// contributes a **carrier** (`Rk`) and a **leaf** sibling (`Rk·s`); the terminal Rω
/// contributes two constructs.
pub const ANCHOR_LABELS: [&str; 15] = [
    "R1.1.D1", // 0 — root (depends on nothing)
    "R1", "R1·s", // 1,2 — R1 carrier + leaf → R1.1.D1
    "R2", "R2·s", // 3,4 — R2 carrier + leaf → R1
    "R3", "R3·s", // 5,6 — R3 → R2
    "R4", "R4·s", // 7,8 — R4 → R3
    "R5", "R5·s", // 9,10 — R5 → R4
    "R6", "R6·s", // 11,12 — R6 → R5
    "Rω·a", "Rω·b", // 13,14 — Rω pair → R6
];

/// The rank **carrier** element ids R1…R6 (the load-bearing locus each next rank depends
/// on), ascending — the Class-B constructs of [`Self-Horiz`](super::self_horizon).
pub const RANK_CARRIERS: [ElementId; 6] =
    [ElementId(1), ElementId(3), ElementId(5), ElementId(7), ElementId(9), ElementId(11)];

/// **Rω.1.D1 (`U_CRPT`)** — the dependency edges `X →_ρ Y` (the acyclic DAG). Carriers chain
/// `R1.1.D1 ← R1 ← R2 ← … ← R6 ← Rω`; each rank's leaf and the Rω pair share their carrier's
/// anchor (so every carrier's kernel mixes a populated and an empty fiber — the `H_I = ⊥` that
/// makes them Class B, Rω.2.T1).
const DEPENDENCY_EDGES: [(u32, u32); 14] = [
    (1, 0), (2, 0),   // R1, R1·s → R1.1.D1
    (3, 1), (4, 1),   // R2, R2·s → R1
    (5, 3), (6, 3),   // R3 → R2
    (7, 5), (8, 5),   // R4 → R3
    (9, 7), (10, 7),  // R5 → R4
    (11, 9), (12, 9), // R6 → R5
    (13, 11), (14, 11), // Rω·a, Rω·b → R6
];

/// **Rω.1.D1 (`U_CRPT`)** — the σ-only **forward citations** (cross-references not backed by
/// dependency): `R1 →_σ R2 →_σ R3` (axioms/definitions citing later operators) and
/// `R6 →_σ Rω` (the tower citing its self-application). Combined with the upward `→_ρ ⊆ →_σ`
/// back-edges these close **σ-cycles** — the recurrent core that makes `→_σ_CRPT`
/// non-well-founded (`Self-Inf` Rω.1.D2).
const FORWARD_CITATIONS: [(u32, u32); 3] = [
    (1, 3),  // R1 →_σ R2 (with R2 →_ρ R1 ⇒ σ-cycle {R1, R2})
    (3, 5),  // R2 →_σ R3 (with R3 →_ρ R2 ⇒ extends the core to {R1, R2, R3})
    (11, 13), // R6 →_σ Rω·a (with Rω·a →_ρ R6 ⇒ σ-cycle {R6, Rω·a})
];

/// **Rω.1.D1 (`U_CRPT`)** — build the self-substrate `𝒰_CRPT` as a concrete CRPT [`Instance`].
/// `→_{ρ_CRPT}` is the acyclic dependency DAG (`DEPENDENCY_EDGES`); `→_{σ_CRPT} ⊇ →_{ρ_CRPT}`
/// adds the forward citations (`FORWARD_CITATIONS`) that make the structural relation
/// non-well-founded; `𝒯_CRPT` is discrete. The operator `ρ_CRPT` is derived from `→_ρ` alone,
/// so the dependency reading is pure-WF while the structural reading is Mixed.
pub fn self_substrate() -> Instance {
    let mut sigma: Vec<(u32, u32)> = DEPENDENCY_EDGES.to_vec(); // →_ρ ⊆ →_σ
    sigma.extend_from_slice(&FORWARD_CITATIONS);
    let substrate = Substrate::new(15, &DEPENDENCY_EDGES, &sigma).expect("self-substrate is well-formed");
    Instance::from_functional_reduction(substrate)
        .expect("the dependency DAG is a deterministic functional reduction")
}

/// Witness **Rω.1.T1 (`Self-Model`)** — the self-substrate is a genuine CRPT instance. The
/// construction validates C1 (Step-or-Fix) and C2 (Bisimulation Equivariance) — a value of type
/// [`Instance`] *is* a verified CRPT instance — and this certifies the **dependency-reading**
/// pure-WF profile (clause 5, *scoped to `ρ_CRPT`*): `Fix(ρ_CRPT) = {R1.1.D1}` and every
/// construct convergent under `ρ_CRPT` (`∞_CRPT^ρ = ∅`, `CRPT-WF` Rω.7.T1 — preserved, not
/// retracted). The *full* self-model is **Mixed** (the structural dual `∞_CRPT^σ ≠ ∅`,
/// [`certify_self_mixed`]). Returns `true` when the anchor passes its own dependency-reading
/// criteria.
pub fn certify_self_model() -> bool {
    let m = self_substrate();
    let op = m.operator();
    // Fix(ρ_CRPT) = {R1.1.D1}: exactly one fixpoint, and it is the root.
    if op.fixpoints() != vec![R1_1_D1] {
        return false;
    }
    // ∞_CRPT^ρ = ∅: every construct reaches the root in finitely many dependency steps.
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x) != Some(R1_1_D1) {
            return false;
        }
    }
    true
}

/// **Rω.1.D2 (`Self-Inf`)** — a construct is **σ-recurrent** iff it lies on a `→_σ_CRPT`
/// cycle (`∃` a positive σ-walk returning to it) — the heart of `∞_CRPT^σ` (the σ-strongly-
/// connected core, the `CPer` destination set). Returns the σ-recurrent core, ascending.
pub fn structural_recurrent_core(s: &Substrate) -> Vec<ElementId> {
    s.elements()
        .filter(|&x| {
            // a positive σ-cycle through x: some σ-successor σ-reaches x.
            s.structural_successors(x).iter().any(|&y| s.structural_reachable(y, x))
        })
        .collect()
}

/// **Rω.1.D2 (`Self-Inf`)** — the **structural persistent aspect** `∞_CRPT^σ`: the constructs
/// admitting an infinite σ-walk — those that `→_σ_CRPT`-reach the recurrent core. Returns
/// `∞_CRPT^σ`, ascending. (`↓_CRPT^σ` is the complement — the σ-well-founded constructs,
/// chiefly the root and σ-sinks.)
pub fn structural_persistent_aspect(s: &Substrate) -> Vec<ElementId> {
    let core = structural_recurrent_core(s);
    s.elements()
        .filter(|&x| core.iter().any(|&r| s.structural_reachable(x, r)))
        .collect()
}

/// Witness **Rω.1.D2 (`Self-Inf`)** — `∞_CRPT^σ ≠ ∅`: the structural relation is
/// non-well-founded, so the self-substrate has a non-empty persistent aspect on `→_σ_CRPT`.
/// Returns `true` when the σ-recurrent core (hence `∞_CRPT^σ`) is non-empty.
pub fn certify_self_inf_nonempty() -> bool {
    !structural_recurrent_core(self_substrate().substrate()).is_empty()
}

/// Witness **Rω.1.T2 (`Self-Mixed`)** — the faithful self-model is a genuine **Mixed**-profile
/// CRPT instance realizing its own **WF–NWF duality**: `↓_CRPT^ρ = 𝒰_CRPT` with `∞_CRPT^ρ = ∅`
/// (the dependency/observable/WF axis — `CRPT-WF`, preserved & scoped) *and* `∞_CRPT^σ ≠ ∅`
/// (the structural/horizontal/NWF axis — `Self-Inf`). The two are the HV-dual readings
/// (`HV-Dual-Static` R0.6.T1) of one self-projection (`Min-Interp` R1.1.R5). Returns `true`
/// when both faces hold — pure-WF under `ρ`, non-well-founded under `σ`.
pub fn certify_self_mixed() -> bool {
    // dependency face: pure-WF (∞^ρ = ∅); structural face: NWF (∞^σ ≠ ∅).
    certify_self_model() && certify_self_inf_nonempty()
}

/// Witness **Rω.1.T3 (`Self-InfDual`)** — `Inf-Dual` at the self level: the σ-NWF aspect
/// `∞_CRPT^σ` is carried, under one reification step, to the **vertical NWF of the meta-tower**
/// (`Tower-of-Towers` Rω.4 / `Self-FP` Rω.5) — horizontal-σ infinity at level `n` becomes
/// vertical structure at level `n+1` (`Inf-Dual` R1.9.T7, via `Imp-Reify` Rω.9.T2). Realized:
/// the base has a non-empty σ-NWF aspect (the horizontal end) **and** its reification resets
/// every primitive to a depth-0 atom (`Fix-Bas`, the vertical end one level up — the
/// meta-tower's WF restructuring of the σ-recurrent content). Returns `true` when both ends of
/// the duality are witnessed.
pub fn certify_self_inf_dual() -> bool {
    let base = self_substrate();
    // horizontal end: ∞_CRPT^σ ≠ ∅; vertical end: the reify ascent resets primitives to atoms.
    certify_self_inf_nonempty() && crate::r6::tower::certify_depth_reset(&base).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_anchor_is_a_mixed_self_model_wf_under_rho_nwf_under_sigma() {
        // Self-Model (Rω.1.T1): the dependency reading is pure-WF (∞^ρ = ∅).
        assert!(certify_self_model());
        let m = self_substrate();
        let op = m.operator();
        assert!(op.is_fixpoint(R1_1_D1)); // R1.1.D1 the unique dependency root
        assert_eq!(op.fixpoints().len(), 1);
        for &c in &RANK_CARRIERS {
            assert!(!op.is_fixpoint(c));
            assert_eq!(op.canonical_fixpoint(c), Some(R1_1_D1)); // ∞^ρ = ∅
        }
        assert_eq!(ANCHOR_LABELS.len(), m.substrate().universe_len() as usize);
    }

    #[test]
    fn the_structural_relation_is_non_well_founded_and_the_model_is_mixed() {
        let m = self_substrate();
        let s = m.substrate();
        // Self-Inf (Rω.1.D2): →_σ_CRPT has a non-empty σ-recurrent core ⇒ ∞_CRPT^σ ≠ ∅.
        let core = structural_recurrent_core(s);
        assert!(!core.is_empty());
        // the forward citations close σ-cycles {R1,R2,R3} and {R6,Rω·a}: R1, R3, R6 are recurrent.
        assert!(core.contains(&ElementId(1)) && core.contains(&ElementId(3)) && core.contains(&ElementId(11)));
        let inf_sigma = structural_persistent_aspect(s);
        assert!(!inf_sigma.is_empty());
        // ↓_CRPT^σ is the well-founded complement and is NOT all of 𝒰 (the model is Mixed).
        assert!((inf_sigma.len() as u32) < s.universe_len());
        // the root R1.1.D1 is a σ-sink ⇒ in ↓_CRPT^σ (no infinite σ-walk).
        assert!(!inf_sigma.contains(&R1_1_D1));
        // Self-Mixed (Rω.1.T2) + Self-InfDual (Rω.1.T3).
        assert!(certify_self_inf_nonempty());
        assert!(certify_self_mixed());
        assert!(certify_self_inf_dual());
    }
}
