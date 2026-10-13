//! # L5.1 — Model Algebra
//!
//! Exact realization of spec section **L5.1** (`CRPT_OMEGA_TOWER_L5.md`, v1.0.0-rc4):
//!
//! - L5.1.D2/D4 `Mod-∘` / `Mod-×` — the product model M₁ × M₂: universe 𝒰₁ × 𝒰₂,
//!   componentwise reduction, `ρ(x,y) = (ρ_{M₁}(x), ρ_{M₂}(y))`. (Composition ∘ and
//!   product × coincide structurally — composition is the categorical product.)
//! - L5.1.D7 `Spec-Mod` — the identity (unit) model 𝟙 = ({★}, ρ(★)=★). (The zero
//!   model 𝟘 = (∅, …) is excluded by non-triviality, so it is not constructed.)
//!
//! These are model-*producing* operations: each returns a new owned [`Model`].

use crate::l1::substrate::{ElementId, Substrate};
use crate::l2::projection::{Model, ProjectionError};

/// **L5.1.D4/D2 (`Mod-×`/`Mod-∘`)** — the product model M₁ × M₂.
///
/// The universe 𝒰₁ × 𝒰₂ is encoded densely as `(x, y) ↦ x·|𝒰₂| + y`. Reduction is
/// componentwise and ρ is componentwise — `ρ(x,y) = (ρ_{M₁}(x), ρ_{M₂}(y))` — so a
/// product state is a normal form iff *both* components are fixpoints (matching C1).
/// The result is validated as a CRPT model (C1/C2) by construction.
pub fn product(m1: &Model, m2: &Model) -> Result<Model, ProjectionError> {
    let n2 = m2.substrate().universe_len();
    let op1 = m1.operator();
    let op2 = m2.operator();
    let encode = |x: ElementId, y: ElementId| x.0 * n2 + y.0;
    let n = m1.substrate().universe_len() * n2;
    let mut reduction_edges = Vec::new();
    for x in m1.substrate().elements() {
        for y in m2.substrate().elements() {
            if !(op1.is_fixpoint(x) && op2.is_fixpoint(y)) {
                reduction_edges.push((encode(x, y), encode(op1.project(x), op2.project(y))));
            }
        }
    }
    let substrate = Substrate::new(n, &reduction_edges, &reduction_edges)
        .expect("product substrate is well-formed (→_σ = →_ρ, indices in range)");
    Model::from_functional_reduction(substrate)
}

/// **L5.1.D7 (`Spec-Mod`)** — the identity model 𝟙 = ({★}, ρ(★)=★): a single
/// element (★ = `ElementId(0)`) that is a normal form. The unit for product
/// (M × 𝟙 ≅ M).
pub fn identity_model() -> Model {
    let substrate = Substrate::new(1, &[], &[]).expect("identity substrate is well-formed");
    Model::from_functional_reduction(substrate).expect("identity is a valid model")
}

/// **L5.1.D3 (`Mod-∩`)** — the intersection `M₁ ∩ M₂`, the **meet** in the lattice of
/// CRPT models (universe inclusion read as the dense prefix `0..min(|𝒰₁|,|𝒰₂|)`). The
/// reduction and structural relations are the edges present in **both**; the result is
/// the canonical model on the intersected relation. Fails if the intersected →_ρ is not
/// functional.
pub fn intersection(m1: &Model, m2: &Model) -> Result<Model, ProjectionError> {
    let n = m1.substrate().universe_len().min(m2.substrate().universe_len());
    let (s1, s2) = (m1.substrate(), m2.substrate());
    let mut reduction = Vec::new();
    let mut structural = Vec::new();
    for x in 0..n {
        for y in 0..n {
            let (xi, yi) = (ElementId(x), ElementId(y));
            if s1.reduces(xi, yi) && s2.reduces(xi, yi) {
                reduction.push((x, y));
            }
            if s1.structural_step(xi, yi) && s2.structural_step(xi, yi) {
                structural.push((x, y));
            }
        }
    }
    let substrate = Substrate::new(n, &reduction, &structural)
        .expect("intersection substrate is well-formed (→_ρ ⊆ →_σ preserved)");
    Model::from_functional_reduction(substrate)
}

/// **L5.1.D6 (`Mod-∪`)** — the union `M₁ ∪ M₂`, the **join** in the model lattice
/// (universe `0..max(|𝒰₁|,|𝒰₂|)`). The relations are the union of both; the models must
/// **agree on the shared prefix** (else the union →_ρ branches and construction fails).
pub fn union(m1: &Model, m2: &Model) -> Result<Model, ProjectionError> {
    let n1 = m1.substrate().universe_len();
    let n2 = m2.substrate().universe_len();
    let n = n1.max(n2);
    let (s1, s2) = (m1.substrate(), m2.substrate());
    let mut reduction = Vec::new();
    let mut structural = Vec::new();
    for x in 0..n {
        for y in 0..n {
            let (xi, yi) = (ElementId(x), ElementId(y));
            let in_reduction = (x < n1 && y < n1 && s1.reduces(xi, yi))
                || (x < n2 && y < n2 && s2.reduces(xi, yi));
            let in_structural = (x < n1 && y < n1 && s1.structural_step(xi, yi))
                || (x < n2 && y < n2 && s2.structural_step(xi, yi));
            if in_reduction {
                reduction.push((x, y));
            }
            if in_structural {
                structural.push((x, y));
            }
        }
    }
    let substrate = Substrate::new(n, &reduction, &structural)
        .expect("union substrate is well-formed (→_ρ ⊆ →_σ preserved)");
    Model::from_functional_reduction(substrate)
}

/// **L5.1.D5 (`Mod-/`)** — the quotient `M / ~` by a compatible equivalence, given as a
/// per-element class assignment `class_of[x]` (any labels; re-indexed densely). The
/// quotient reduction is the image `[x] →_ρ [ρ_M(x)]` and `ρ_{M/~}([x]) = [ρ_M(x)]`.
/// Compatibility of `~` with ρ_M (it respects the projection) is required for the quotient
/// →_ρ to be functional; otherwise construction fails.
pub fn quotient(m: &Model, class_of: &[u32]) -> Result<Model, ProjectionError> {
    let mut classes: Vec<u32> = class_of.to_vec();
    classes.sort_unstable();
    classes.dedup();
    let class_index = |c: u32| classes.binary_search(&c).unwrap() as u32;
    let s = m.substrate();
    let mut reduction = Vec::new();
    let mut structural = Vec::new();
    for x in s.elements() {
        let cx = class_index(class_of[x.index()]);
        for &y in s.reduction_successors(x) {
            let cy = class_index(class_of[y.index()]);
            if cx != cy {
                reduction.push((cx, cy)); // drop internal self-loops ⇒ [x] is a fixpoint
            }
        }
        for &y in s.structural_successors(x) {
            let cy = class_index(class_of[y.index()]);
            if cx != cy {
                structural.push((cx, cy));
            }
        }
    }
    reduction.sort_unstable();
    reduction.dedup();
    structural.sort_unstable();
    structural.dedup();
    let substrate = Substrate::new(classes.len() as u32, &reduction, &structural)
        .expect("quotient substrate is well-formed");
    Model::from_functional_reduction(substrate)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 𝒰 = {0,1}, 0 →_ρ 1, 1 ∈ NF.
    fn chain() -> Model {
        Model::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap()).unwrap()
    }

    #[test]
    fn product_is_componentwise() {
        let m = chain();
        let p = product(&m, &m).unwrap();
        let op = p.operator();
        let encode = |x: u32, y: u32| ElementId(x * 2 + y);
        // ρ(0,0) = (1,1); ρ(0,1) = (1,1); ρ(1,0) = (1,1); (1,1) is the only fixpoint.
        assert_eq!(op.project(encode(0, 0)), encode(1, 1));
        assert_eq!(op.project(encode(0, 1)), encode(1, 1));
        assert_eq!(op.project(encode(1, 0)), encode(1, 1));
        assert!(op.is_fixpoint(encode(1, 1)));
        assert_eq!(op.fixpoints(), vec![encode(1, 1)]);
    }

    #[test]
    fn lattice_ops_intersection_union_quotient() {
        // M1: 0→1→2 (chain). M2: 0→1, 2 isolated NF (over the same 3-element prefix).
        let m1 = Model::from_functional_reduction(
            Substrate::new(3, &[(0, 1), (1, 2)], &[(0, 1), (1, 2)]).unwrap(),
        )
        .unwrap();
        let m2 = Model::from_functional_reduction(
            Substrate::new(3, &[(0, 1)], &[(0, 1)]).unwrap(),
        )
        .unwrap();
        // ∩: edges in both = {0→1}; 1,2 become NF.
        let meet = intersection(&m1, &m2).unwrap();
        let op = meet.operator();
        assert_eq!(op.project(id(0)), id(1));
        assert!(op.is_fixpoint(id(1)) && op.is_fixpoint(id(2)));
        // ∪: edges in either = {0→1, 1→2} (they agree on the shared prefix).
        let join = union(&m1, &m2).unwrap();
        let jop = join.operator();
        assert_eq!(jop.project(id(0)), id(1));
        assert_eq!(jop.project(id(1)), id(2));
        // /~ : collapse {0,1} into one class (compatible: ρ keeps it consistent).
        // M = 0→1, 1 NF; ~ merges 0,1 ⇒ quotient is a single NF class.
        let chain = Model::from_functional_reduction(
            Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap(),
        )
        .unwrap();
        let q = quotient(&chain, &[7, 7]).unwrap(); // both in class 7
        assert_eq!(q.substrate().universe_len(), 1);
        assert!(q.operator().is_fixpoint(id(0)));
    }

    #[test]
    fn identity_model_is_a_unit_fixpoint() {
        let one = identity_model();
        let op = one.operator();
        assert_eq!(op.substrate().universe_len(), 1);
        assert!(op.is_fixpoint(id(0)));
        assert_eq!(op.fixpoints(), vec![id(0)]);
    }
}
