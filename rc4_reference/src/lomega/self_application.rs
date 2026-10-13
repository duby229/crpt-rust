//! # Lω.5 — The Self-Conformance Test
//!
//! Exact realization of the self-application diagnostic from spec section **Lω.5**
//! (`CRPT_OMEGA_TOWER_Lomega.md`, v1.0.0-rc4):
//!
//! - Lω.5 `Self-Sub` / `Self-WF` — the tower's own construct-dependency graph is a
//!   CRPT substrate, and CRPT classifies *itself* as **pure-WF**: the derivation of
//!   every construct is well-founded, terminating at the unique foundational root
//!   `L1.1.D1` (the substrate). `∞_CRPT = ∅` (Lω.5.R2: no construct is self-justifying
//!   / circular).
//!
//! We build that graph from *this engine's actual constructs*: each construct
//! [`reduces`](Substrate::reduces) (along →_ρ) to the primary construct it is built
//! on — a spanning **dependency tree** rooted at `L1.1.D1`. (The full dependency DAG
//! has extra structural-only edges; they do not change the WF conclusion, so the
//! reduction relation here is the primary-dependency tree, →_σ = →_ρ.) The engine then
//! runs its own L2/L3 machinery on this model and certifies:
//!
//! 1. it is a valid CRPT [`Model`] (C1/C2 hold) — the construction is self-consistent;
//! 2. it is **pure-WF** (`certify_well_founded`) — `∞_CRPT = ∅`, no circular construct;
//! 3. it has the **unique root** `L1.1.D1` (`certify_unique_root`) — every construct's
//!    canonical form is the substrate.

use crate::l1::substrate::{ElementId, Substrate};
use crate::l2::projection::Model;

/// A construct of the engine (a labelled spec item realized as a module), and the
/// primary construct it is built on (its →_ρ-successor). The root reduces to itself.
struct Construct {
    /// The spec label / module path of the construct.
    label: &'static str,
    /// Index of the primary dependency this construct reduces to (itself, for the root).
    reduces_to: u32,
}

/// The engine's construct-dependency tree: each entry's `reduces_to` is the construct
/// it is primarily built on. Index 0 is the foundational root `L1.1.D1` (the substrate).
const CONSTRUCTS: &[Construct] = &[
    Construct { label: "L1.1.D1 substrate", reduces_to: 0 }, // 0 — root (NF)
    Construct { label: "L2.1 projection / Model", reduces_to: 0 }, // 1
    Construct { label: "L2.2 regime", reduces_to: 1 }, // 2
    Construct { label: "L2.3 depth", reduces_to: 1 }, // 3
    Construct { label: "L2.4 canonical form", reduces_to: 1 }, // 4
    Construct { label: "L2.5 fiber", reduces_to: 4 }, // 5
    Construct { label: "L3.1 horizon", reduces_to: 5 }, // 6
    Construct { label: "L3.2 classification", reduces_to: 6 }, // 7
    Construct { label: "L4.3 valuation", reduces_to: 1 }, // 8
    Construct { label: "L4.1 observer", reduces_to: 7 }, // 9
    Construct { label: "L4.2 gateway", reduces_to: 2 }, // 10
    Construct { label: "L5.1 algebra", reduces_to: 1 }, // 11
    Construct { label: "L5.2 homomorphism", reduces_to: 5 }, // 12
    Construct { label: "L5.4 order", reduces_to: 12 }, // 13
    Construct { label: "L7.1 collapse", reduces_to: 5 }, // 14
    Construct { label: "L8.1 fma", reduces_to: 0 }, // 15
    Construct { label: "L8.2 lift", reduces_to: 15 }, // 16
    Construct { label: "L7.2 adjunction", reduces_to: 14 }, // 17 (also builds on lift, structurally)
    Construct { label: "L8.4 tower", reduces_to: 16 }, // 18
    Construct { label: "Lω.5 self-application", reduces_to: 18 }, // 19
];

/// The index of the foundational root construct `L1.1.D1` (the substrate).
const ROOT: u32 = 0;

/// **Lω.5 (`Self-Sub`)** — build the engine's own construct-dependency graph as a CRPT
/// [`Model`]: the universe is the engine's constructs, and →_ρ (= →_σ) sends each
/// construct to the primary construct it is built on. Constructing the `Model` already
/// certifies the graph is a *valid* CRPT model (C1/C2) — the engine is self-consistent.
pub fn self_model() -> Model {
    let reduction: Vec<(u32, u32)> = CONSTRUCTS
        .iter()
        .enumerate()
        .filter(|(i, c)| c.reduces_to != *i as u32) // the root reduces to itself ⇒ no edge (NF)
        .map(|(i, c)| (i as u32, c.reduces_to))
        .collect();
    let substrate = Substrate::new(CONSTRUCTS.len() as u32, &reduction, &reduction)
        .expect("the construct-dependency tree is a well-formed substrate");
    Model::from_functional_reduction(substrate)
        .expect("CRPT's own construct graph is a valid CRPT model (self-consistency)")
}

/// **Lω.5 (`Self-WF`)** — certify the engine's construct graph is **pure-WF**:
/// `∞_CRPT = ∅`. Every construct's ρ-orbit terminates (no circular / self-justifying
/// construct). Returns the first persistent construct's label on failure.
pub fn certify_well_founded() -> Result<(), &'static str> {
    let model = self_model();
    let op = model.operator();
    for x in model.substrate().elements() {
        if op.canonical_fixpoint(x).is_none() {
            return Err(CONSTRUCTS[x.index()].label);
        }
    }
    Ok(())
}

/// **Lω.5** — certify the **unique root** `L1.1.D1`: the substrate is the only normal
/// form, and it is the canonical form (CFix) every construct reduces to. Returns the
/// label of an offending construct on failure.
pub fn certify_unique_root() -> Result<(), &'static str> {
    let model = self_model();
    let op = model.operator();
    let root = ElementId(ROOT);
    // exactly one normal form, and it is the root
    let normal_forms = model.substrate().normal_forms();
    if normal_forms != vec![root] {
        return Err("the substrate L1.1.D1 is not the unique normal form");
    }
    // every construct's canonical form is the root
    for x in model.substrate().elements() {
        if op.canonical_fixpoint(x) != Some(root) {
            return Err(CONSTRUCTS[x.index()].label);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engine_classifies_its_own_construction_as_pure_wf() {
        // Self-consistency: the construct graph is a valid CRPT model (no panic).
        let _ = self_model();
        // Self-WF: ∞_CRPT = ∅ — no construct is circular.
        assert!(matches!(certify_well_founded(), Ok(())));
        // Unique root: every construct reduces to L1.1.D1, the sole normal form.
        assert!(matches!(certify_unique_root(), Ok(())));
    }

    #[test]
    fn the_root_is_the_substrate() {
        let model = self_model();
        let op = model.operator();
        // The deepest construct (Lω.5 self-application itself) bottoms out at L1.1.D1.
        let self_construct = ElementId((CONSTRUCTS.len() - 1) as u32);
        assert_eq!(op.canonical_fixpoint(self_construct), Some(ElementId(ROOT)));
        assert!(op.is_fixpoint(ElementId(ROOT)));
        assert_eq!(CONSTRUCTS[ROOT as usize].label, "L1.1.D1 substrate");
    }
}
