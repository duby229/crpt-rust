//! # L5.4 — Model Order
//!
//! Exact realization of spec section **L5.4** (`CRPT_OMEGA_TOWER_L5.md`, v1.0.0-rc4):
//!
//! - L5.4.D1 `⊑` — refinement: `M₁ ⊑ M₂` iff 𝒰_{M₁} ⊆ 𝒰_{M₂}, M₂'s reduction
//!   restricted to 𝒰_{M₁} is contained in M₁'s, and ≃_{M₁} ⟹ ≃_{M₂} on 𝒰_{M₁}.
//!   (Here 𝒰_{M₁} ⊆ 𝒰_{M₂} is read as the dense prefix `0..|𝒰_{M₁}|`.)
//! - L5.4.D2 `⪯` — expressiveness: `M₁ ⪯ M₂` iff M₁ embeds *injectively* into M₂
//!   (an injective homomorphism exists). Checked here against a candidate embedding.

use crate::l1::substrate::ElementId;
use crate::l2::depth::derivation_height;
use crate::l2::fiber::observable_equivalence;
use crate::l2::projection::Model;
use crate::l2::regime::is_convergent;
use crate::l5::homomorphism::Homomorphism;

/// **L5.2.D3 (`R-Iso`)** — whether `map` is a **regime-restricted isomorphism**: its
/// restriction to the convergent strata is a bijection `↓_{M₁} → ↓_{M₂}` preserving the
/// projection `ρ_M`, the derivation height `d_M`, and the canonical form `CFix`. It
/// compares two models on their well-founded parts only, ignoring the persistent regime.
/// `map` is given over all of `𝒰_{M₁}` (only the ↓_{M₁} entries are used).
pub fn is_regime_isomorphism(m1: &Model, m2: &Model, map: &[ElementId]) -> bool {
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

/// **L5.2.D5 (`R-Iso∞`)** — the **persistent dual** of `R-Iso`: whether `map` restricts to
/// a bijection `∞_{M₁} → ∞_{M₂}` preserving the projection `ρ_M` and the persistent orbit
/// equivalence `≃∞` (the `CNF∞`/ω-limit structure). Where `R-Iso` compares well-founded
/// parts by the *single* invariant `(d_M, CFix)`, `R-Iso∞` compares persistent parts by the
/// asymptotic invariant; on the Type-P (SC-1) sub-class the AOI hierarchy collapses to
/// `CNF∞`, exactly `≃∞`. `map` is given over all of `𝒰_{M₁}` (only ∞_{M₁} entries used).
pub fn is_regime_isomorphism_infinity(m1: &Model, m2: &Model, map: &[ElementId]) -> bool {
    use crate::l2::regime::is_persistent;
    use crate::l3::persistent::persistent_equivalent;
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

/// **L5.4.D1 (`⊑`)** — `M₁ ⊑ M₂` (refinement), reading 𝒰_{M₁} as the dense prefix
/// `0..|𝒰_{M₁}|` of 𝒰_{M₂}.
pub fn is_refinement(m1: &Model, m2: &Model) -> bool {
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

/// **L5.4.D2 (`⪯`)** — `M₁ ⪯ M₂` (expressiveness) witnessed by `embedding`: returns
/// `true` iff `embedding` is an *injective* homomorphism M₁ → M₂.
pub fn embeds_via(m1: &Model, m2: &Model, embedding: Vec<ElementId>) -> bool {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 𝒰 = {0,1}, 0 →_ρ 1, 1 ∈ NF.
    fn chain() -> Model {
        Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap()).unwrap()
    }

    /// 𝒰 = {1,0}, 1 →_ρ 0, 0 ∈ NF (relabelling of `chain`).
    fn chain_swapped() -> Model {
        Model::from_functional_reduction(Substrate::new(2, &[(1, 0)], &[(1, 0)]).unwrap()).unwrap()
    }

    #[test]
    fn refinement_reflexive() {
        let m = chain();
        assert!(is_refinement(&m, &m)); // M ⊑ M
    }

    #[test]
    fn regime_isomorphism_infinity_on_persistent_strata() {
        // Two structurally identical 2-cycles 0⇄1, relabelled 1⇄0. The 0↔1 swap is an
        // R-Iso∞: a bijection on ∞_M preserving ρ and ≃∞.
        let cyc = |edges: &[(u32, u32)]| {
            Model::from_functional_reduction(Substrate::new(2, edges, edges).unwrap()).unwrap()
        };
        let m1 = cyc(&[(0, 1), (1, 0)]);
        let m2 = cyc(&[(1, 0), (0, 1)]); // same cycle (the relation is symmetric)
        assert!(is_regime_isomorphism_infinity(&m1, &m2, &[id(1), id(0)]));
        // a map landing in ↓_M (here there is none) or non-bijective fails.
        assert!(!is_regime_isomorphism_infinity(&m1, &m2, &[id(0), id(0)]));
    }

    #[test]
    fn regime_isomorphism_on_convergent_strata() {
        // chain 0→1 vs its relabelling 1→0 (both pure-WF). The 0↔1 swap is an R-Iso:
        // a bijection on ↓_M preserving ρ, d_M, CFix.
        let m1 = chain();
        let m2 = chain_swapped();
        assert!(is_regime_isomorphism(&m1, &m2, &[id(1), id(0)]));
        // a non-bijection (collapse) is not an R-Iso.
        assert!(!is_regime_isomorphism(&m1, &m2, &[id(0), id(0)]));
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
