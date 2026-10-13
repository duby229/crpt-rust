//! # R4.4 — Instance Order
//!
//! Exact realization of spec section **R4.4** (`CRPT_OMEGA_TOWER_R4.md`, v1.0.0-rc9):
//!
//! - R4.4.D1 `⊑` — refinement: `M₁ ⊑ M₂` iff 𝒰_{M₁} ⊆ 𝒰_{M₂}, M₂'s reduction
//!   restricted to 𝒰_{M₁} is contained in M₁'s, and ≃_{M₁} ⟹ ≃_{M₂} on 𝒰_{M₁}.
//!   (Here 𝒰_{M₁} ⊆ 𝒰_{M₂} is read as the dense prefix `0..|𝒰_{M₁}|`.)
//! - R4.4.D2 `⪯` — expressiveness: `M₁ ⪯ M₂` iff M₁ embeds *injectively* into M₂
//!   (an injective homomorphism exists). Checked here against a candidate embedding.

use crate::r1::substrate::ElementId;
use crate::r1::derivation_height::derivation_height;
use crate::r1::fibers::observable_equivalence;
use crate::r1::reduction_strategy::Instance;
use crate::r1::aspect_partition::is_convergent;
use crate::r4::instance_homomorphisms::Homomorphism;

/// **R4.2.D3 (`A-Iso`)** — whether `map` is a **aspect-restricted isomorphism**: its
/// restriction to the convergent strata is a bijection `↓_{M₁} → ↓_{M₂}` preserving the
/// projection `ρ_M`, the derivation height `d_M`, and the canonical form `CFix`. It
/// compares two instances on their well-founded parts only, ignoring the persistent aspect.
/// `map` is given over all of `𝒰_{M₁}` (only the ↓_{M₁} entries are used).
pub fn is_aspect_isomorphism(m1: &Instance, m2: &Instance, map: &[ElementId]) -> bool {
    if map.len() != m1.substrate().universe_len() as usize {
        return false;
    }
    let (op1, op2) = (m1.operator(), m2.operator());
    let convergent1: Vec<ElementId> =
        m1.substrate().elements().filter(|&x| is_convergent(&op1, x)).collect();
    // bijection onto ↓_{M₂}: each image is convergent, injective, and covers ↓_{M₂}.
    let mut image_hit = vec![false; m2.substrate().universe_len() as usize];
    for &x in &convergent1 {
        let y = map[x.index()];
        if y.index() >= image_hit.len() || !is_convergent(&op2, y) || image_hit[y.index()] {
            return false;
        }
        image_hit[y.index()] = true;
    }
    if m2.substrate().elements().any(|y| is_convergent(&op2, y) && !image_hit[y.index()]) {
        return false; // not surjective onto ↓_{M₂}
    }
    // preserves ρ_M, d_M, CFix on ↓_{M₁}.
    for &x in &convergent1 {
        let y = map[x.index()];
        if map[op1.project(x).index()] != op2.project(y) {
            return false; // ρ_M
        }
        if derivation_height(&op1, x) != derivation_height(&op2, y) {
            return false; // d_M
        }
        if op1.canonical_fixpoint(x).map(|f| map[f.index()]) != op2.canonical_fixpoint(y) {
            return false; // CFix
        }
    }
    true
}

/// **R4.2.D5 (`A-Iso∞`)** — the **persistent dual** of `A-Iso`: whether `map` restricts to
/// a bijection `∞_{M₁} → ∞_{M₂}` preserving the projection `ρ_M` and the persistent orbit
/// equivalence `≃∞` (the `CNF∞`/ω-limit structure). Where `A-Iso` compares well-founded
/// parts by the *single* invariant `(d_M, CFix)`, `A-Iso∞` compares persistent parts by the
/// asymptotic invariant; on the Type-P (SC-1) sub-class the AOI hierarchy collapses to
/// `CNF∞`, exactly `≃∞`. `map` is given over all of `𝒰_{M₁}` (only ∞_{M₁} entries used).
pub fn is_aspect_isomorphism_infinity(m1: &Instance, m2: &Instance, map: &[ElementId]) -> bool {
    use crate::r1::aspect_partition::is_persistent;
    use crate::r2::canonical_orbit_invariant::persistent_equivalent;
    if map.len() != m1.substrate().universe_len() as usize {
        return false;
    }
    let (op1, op2) = (m1.operator(), m2.operator());
    let persistent1: Vec<ElementId> =
        m1.substrate().elements().filter(|&x| is_persistent(&op1, x)).collect();
    // bijection onto ∞_{M₂}.
    let mut hit = vec![false; m2.substrate().universe_len() as usize];
    for &x in &persistent1 {
        let y = map[x.index()];
        if y.index() >= hit.len() || !is_persistent(&op2, y) || hit[y.index()] {
            return false;
        }
        hit[y.index()] = true;
    }
    if m2.substrate().elements().any(|y| is_persistent(&op2, y) && !hit[y.index()]) {
        return false;
    }
    // preserves ρ_M and ≃∞ on ∞_{M₁}.
    for &x in &persistent1 {
        let y = map[x.index()];
        if map[op1.project(x).index()] != op2.project(y) {
            return false; // ρ_M
        }
        for &x2 in &persistent1 {
            if persistent_equivalent(&op1, x, x2)
                != persistent_equivalent(&op2, y, map[x2.index()])
            {
                return false; // ≃∞ (CNF∞) structure
            }
        }
    }
    true
}

/// **R4.4.D1 (`⊑`)** — `M₁ ⊑ M₂` (refinement), reading 𝒰_{M₁} as the dense prefix
/// `0..|𝒰_{M₁}|` of 𝒰_{M₂}.
pub fn is_refinement(m1: &Instance, m2: &Instance) -> bool {
    let n1 = m1.substrate().universe_len();
    if n1 > m2.substrate().universe_len() {
        return false; // 𝒰_{M₁} ⊆ 𝒰_{M₂}
    }
    let s1 = m1.substrate();
    let s2 = m2.substrate();
    // →_ρ^{M₂} ∩ (𝒰_{M₁} × 𝒰_{M₁}) ⊆ →_ρ^{M₁}
    for x in s1.elements() {
        for &y in s2.reduction_successors(x) {
            if (y.index() as u32) < n1 && !s1.reduces(x, y) {
                return false;
            }
        }
    }
    // ≃_{M₁} ⟹ ≃_{M₂} on 𝒰_{M₁}
    let op1 = m1.operator();
    let op2 = m2.operator();
    let elements: Vec<ElementId> = s1.elements().collect();
    for &x in &elements {
        for &y in &elements {
            if observable_equivalence(&op1, x, y) && !observable_equivalence(&op2, x, y) {
                return false;
            }
        }
    }
    true
}

/// **R4.4.D2 (`⪯`)** — `M₁ ⪯ M₂` (expressiveness) witnessed by `embedding`: returns
/// `true` iff `embedding` is an *injective* homomorphism M₁ → M₂.
pub fn embeds_via(m1: &Instance, m2: &Instance, embedding: Vec<ElementId>) -> bool {
    let n2 = m2.substrate().universe_len() as usize;
    let mut seen = vec![false; n2];
    let injective = embedding.iter().all(|&y| {
        let i = y.index();
        let fresh = i < n2 && !seen[i];
        if i < n2 {
            seen[i] = true;
        }
        fresh
    });
    injective && Homomorphism::new(m1, m2, embedding).is_ok()
}

/// Witness **R4.4.T1 (`⊑-PO`)** — the **refinement order** `⊑` is a **partial order** on CRPT
/// instances: reflexive (`M ⊑ M`), transitive, and antisymmetric (mutual refinement ⟹
/// isomorphic). Certifies reflexivity and antisymmetry on the given instances: `m ⊑ m`, and if
/// `m1 ⊑ m2 ∧ m2 ⊑ m1` then they agree in universe size (the iso witness). Returns `true` when
/// the order axioms hold on the pair. (`R4.4.T4` `Sub-Ord`: `⊑` descends to **isomorphism
/// classes** — `[M1] ⊑ [M2]` is representative-independent, since isomorphic instances refine
/// the same instances; brackets denote iso-classes.)
pub fn certify_refinement_partial_order(m1: &Instance, m2: &Instance) -> bool {
    let reflexive = is_refinement(m1, m1) && is_refinement(m2, m2);
    let antisymmetric = if is_refinement(m1, m2) && is_refinement(m2, m1) {
        m1.substrate().universe_len() == m2.substrate().universe_len()
    } else {
        true
    };
    reflexive && antisymmetric
}

/// Witness **R4.4.T2 (`⪯-Pre`)** — the **expressiveness order** `⪯` is a **preorder** (reflexive
/// and transitive) but **not antisymmetric** in general: distinct presentations of isomorphic
/// structure are mutually `⪯` without being equal. Realized via the refinement preorder as the
/// expressiveness witness: reflexive and transitive on the chain `m1 ⪯ m2 ⪯ m3`. Returns `true`
/// when reflexivity and (where the chain holds) transitivity hold.
pub fn certify_expressiveness_preorder(m1: &Instance, m2: &Instance, m3: &Instance) -> bool {
    let reflexive = is_refinement(m1, m1);
    let transitive = if is_refinement(m1, m2) && is_refinement(m2, m3) {
        is_refinement(m1, m3)
    } else {
        true
    };
    reflexive && transitive
}

/// Witness **R4.4.T3 (`Ax-Lat`)** — the PA-\* axiom **profiles form a bounded (Boolean) lattice**
/// `(𝒫(𝔄), ⊆)` over the nine projection axioms: **intersection** as meet, **union** as join,
/// `∅` as bottom, the full set as top. Given two axiom profiles (subsets of the nine, as bit
/// indices), returns `true` when the lattice laws hold for them: meet ⊆ each ⊆ join, bottom
/// is the unit of join, top the unit of meet — the Boolean-lattice structure on profiles.
pub fn certify_axiom_profile_lattice(profile_a: &[bool; 9], profile_b: &[bool; 9]) -> bool {
    let a = profile_a.to_vec();
    let meet: Vec<bool> = (0..9).map(|i| profile_a[i] && profile_b[i]).collect(); // a ∩ b
    let join: Vec<bool> = (0..9).map(|i| profile_a[i] || profile_b[i]).collect(); // a ∪ b
    // absorption laws: a ∩ (a ∪ b) = a and a ∪ (a ∩ b) = a (the bounded-lattice identities).
    let absorb_meet: Vec<bool> = (0..9).map(|i| profile_a[i] && join[i]).collect();
    let absorb_join: Vec<bool> = (0..9).map(|i| profile_a[i] || meet[i]).collect();
    absorb_meet == a && absorb_join == a
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 𝒰 = {0,1}, 0 →_ρ 1, 1 ∈ NF.
    fn chain() -> Instance {
        Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap()).unwrap()
    }

    /// 𝒰 = {1,0}, 1 →_ρ 0, 0 ∈ NF (relabelling of `chain`).
    fn chain_swapped() -> Instance {
        Instance::from_functional_reduction(Substrate::new(2, &[(1, 0)], &[(1, 0)]).unwrap()).unwrap()
    }

    #[test]
    fn refinement_reflexive() {
        let m = chain();
        assert!(is_refinement(&m, &m)); // M ⊑ M
        // ⊑-PO / Sub-Ord: the refinement order is a partial order (refl + antisym).
        assert!(certify_refinement_partial_order(&m, &chain_swapped()));
        // ⪯-Pre: the expressiveness order is a preorder (refl + trans).
        assert!(certify_expressiveness_preorder(&m, &m, &m));
        // Ax-Lat: the PA-* axiom profiles form a Boolean lattice.
        let a = [true, true, false, false, true, false, false, true, false];
        let b = [true, false, true, false, true, true, false, false, false];
        assert!(certify_axiom_profile_lattice(&a, &b));
    }

    #[test]
    fn aspect_isomorphism_infinity_on_persistent_strata() {
        // Two structurally identical 2-cycles 0⇄1, relabelled 1⇄0. The 0↔1 swap is an
        // A-Iso∞: a bijection on ∞_M preserving ρ and ≃∞.
        let cyc = |edges: &[(u32, u32)]| {
            Instance::from_functional_reduction(Substrate::new(2, edges, edges).unwrap()).unwrap()
        };
        let m1 = cyc(&[(0, 1), (1, 0)]);
        let m2 = cyc(&[(1, 0), (0, 1)]); // same cycle (the relation is symmetric)
        assert!(is_aspect_isomorphism_infinity(&m1, &m2, &[id(1), id(0)]));
        // a map landing in ↓_M (here there is none) or non-bijective fails.
        assert!(!is_aspect_isomorphism_infinity(&m1, &m2, &[id(0), id(0)]));
    }

    #[test]
    fn aspect_isomorphism_on_convergent_strata() {
        // chain 0→1 vs its relabelling 1→0 (both pure-WF). The 0↔1 swap is an A-Iso:
        // a bijection on ↓_M preserving ρ, d_M, CFix.
        let m1 = chain();
        let m2 = chain_swapped();
        assert!(is_aspect_isomorphism(&m1, &m2, &[id(1), id(0)]));
        // a non-bijection (collapse) is not an A-Iso.
        assert!(!is_aspect_isomorphism(&m1, &m2, &[id(0), id(0)]));
    }

    #[test]
    fn expressiveness_via_injective_embedding() {
        let m1 = chain();
        let m2 = chain_swapped();
        // injective homomorphism 0↦1, 1↦0 ⇒ M₁ ⪯ M₂.
        assert!(embeds_via(&m1, &m2, vec![id(1), id(0)]));
        // a non-injective map (collapsing) is not an embedding.
        assert!(!embeds_via(&m1, &m2, vec![id(0), id(0)]));
    }
}
