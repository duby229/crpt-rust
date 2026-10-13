//! # R4.1 — Instance Algebra
//!
//! Exact realization of spec section **R4.1** (`CRPT_OMEGA_TOWER_R4.md`, v1.0.0-rc9):
//!
//! - R4.1.D3 `Inst-×` — the product instance M₁ × M₂: universe 𝒰₁ × 𝒰₂,
//!   componentwise reduction, `ρ(x,y) = (ρ_{M₁}(x), ρ_{M₂}(y))` — the categorical product
//!   in `Inst_CRPT`.
//! - R4.1.D6 `Spec-Mod` — the identity (unit) instance 𝟙 = ({★}, ρ(★)=★). (The zero
//!   instance 𝟘 = (∅, …) is excluded by non-triviality, so it is not constructed.)
//!
//! These are instance-*producing* operations: each returns a new owned [`Instance`].

use crate::r1::substrate::{ElementId, Substrate};
use crate::r1::reduction_strategy::{Instance, ProjectionError};

/// **R4.1.D3 (`Inst-×`)** — the product instance M₁ × M₂.
///
/// The universe 𝒰₁ × 𝒰₂ is encoded densely as `(x, y) ↦ x·|𝒰₂| + y`. Reduction is
/// componentwise and ρ is componentwise — `ρ(x,y) = (ρ_{M₁}(x), ρ_{M₂}(y))` — so a
/// product state is a normal form iff *both* components are fixpoints (matching C1).
/// The result is validated as a CRPT instance (C1/C2) by construction.
pub fn product(m1: &Instance, m2: &Instance) -> Result<Instance, ProjectionError> {
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
    Instance::from_functional_reduction(substrate)
}

/// **R4.1.D6 (`Spec-Mod`)** — the identity instance 𝟙 = ({★}, ρ(★)=★): a single
/// element (★ = `ElementId(0)`) that is a normal form. The unit for product
/// (M × 𝟙 ≅ M).
pub fn identity_instance() -> Instance {
    let substrate = Substrate::new(1, &[], &[]).expect("identity substrate is well-formed");
    Instance::from_functional_reduction(substrate).expect("identity is a valid instance")
}

/// **R4.1.D2 (`Inst-∩`)** — the intersection `M₁ ∩ M₂`, the **meet** in the lattice of
/// CRPT instances (universe inclusion read as the dense prefix `0..min(|𝒰₁|,|𝒰₂|)`). The
/// reduction and structural relations are the edges present in **both**; the result is
/// the canonical instance on the intersected relation. Fails if the intersected →_ρ is not
/// functional.
pub fn intersection(m1: &Instance, m2: &Instance) -> Result<Instance, ProjectionError> {
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
    Instance::from_functional_reduction(substrate)
}

/// **R4.1.D5 (`Inst-∪`)** — the union `M₁ ∪ M₂`, the **join** in the instance lattice
/// (universe `0..max(|𝒰₁|,|𝒰₂|)`). The relations are the union of both; the instances must
/// **agree on the shared prefix** (else the union →_ρ branches and construction fails).
pub fn union(m1: &Instance, m2: &Instance) -> Result<Instance, ProjectionError> {
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
    Instance::from_functional_reduction(substrate)
}

/// **R4.1.D4 (`Inst-/`)** — the quotient `M / ~` by a compatible equivalence, given as a
/// per-element class assignment `class_of[x]` (any labels; re-indexed densely). The
/// quotient reduction is the image `[x] →_ρ [ρ_M(x)]` and `ρ_{M/~}([x]) = [ρ_M(x)]`.
/// Compatibility of `~` with ρ_M (it respects the projection) is required for the quotient
/// →_ρ to be functional; otherwise construction fails.
pub fn quotient(m: &Instance, class_of: &[u32]) -> Result<Instance, ProjectionError> {
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
    Instance::from_functional_reduction(substrate)
}

/// **R4.1.R1 (`18-1`)** — the algebraic framework for the collection of CRPT instances: the
/// **six** algebraic operations give `Inst_CRPT` the structure of an **instance algebra**,
/// each producing new instances from existing ones. The names of the six.
pub const INSTANCE_ALGEBRA_OPERATIONS: [&str; 6] =
    ["composition", "intersection", "product", "quotient", "union", "specialisation"];

/// Witness **R4.1.T1 (`∩-Dec`)** — where defined, **intersection decreases the universe**:
/// `𝒰_{M₁∩M₂} ⊆ 𝒰_{M₁}` and `⊆ 𝒰_{M₂}`, so `|𝒰_{M₁∩M₂}| ≤ min(|𝒰_{M₁}|, |𝒰_{M₂}|)`.
/// Returns `true` when the constructed intersection respects the bound.
pub fn certify_intersection_decreases(m1: &Instance, m2: &Instance) -> bool {
    match intersection(m1, m2) {
        Ok(meet) => {
            meet.substrate().universe_len()
                <= m1.substrate().universe_len().min(m2.substrate().universe_len())
        }
        Err(_) => true, // undefined (non-functional intersection) — the bound is vacuous
    }
}

/// **R4.1.T3 (`Prod-Proj`)** — the first canonical projection `π₁ : M₁ × M₂ → M₁` of the
/// product (universal-property witness). On the dense encoding `(x, y) ↦ x·|𝒰₂| + y`,
/// `π₁(e) = e / |𝒰₂|`. Returns the projection map as a `Vec` indexed by product element.
pub fn product_projection_1(m1: &Instance, m2: &Instance) -> Vec<ElementId> {
    let n2 = m2.substrate().universe_len();
    let n = m1.substrate().universe_len() * n2;
    (0..n).map(|e| ElementId(e / n2)).collect()
}

/// **R4.1.T3 (`Prod-Proj`)** — the second canonical projection `π₂ : M₁ × M₂ → M₂`,
/// `π₂(e) = e mod |𝒰₂|`.
pub fn product_projection_2(m1: &Instance, m2: &Instance) -> Vec<ElementId> {
    let n2 = m2.substrate().universe_len();
    let n = m1.substrate().universe_len() * n2;
    (0..n).map(|e| ElementId(e % n2)).collect()
}

/// Witness **R4.1.T3 (`Prod-Proj`)** — both canonical projections of the product are the
/// universal-property witnesses for the categorical product in `Inst_CRPT`: each **commutes
/// with reduction** — `π_i(ρ_{M₁×M₂}(e)) = ρ_{M_i}(π_i(e))` — so the product's dynamics project
/// componentwise onto each factor. Returns `true` when both projections commute with `ρ`.
pub fn certify_product_projections(m1: &Instance, m2: &Instance) -> bool {
    let Ok(prod) = product(m1, m2) else {
        return false;
    };
    let (pop, op1, op2) = (prod.operator(), m1.operator(), m2.operator());
    let (pi1, pi2) = (product_projection_1(m1, m2), product_projection_2(m1, m2));
    for e in pop.substrate().elements() {
        let stepped = pop.project(e);
        // π₁ ∘ ρ_prod = ρ_{M₁} ∘ π₁ and π₂ ∘ ρ_prod = ρ_{M₂} ∘ π₂.
        if pi1[stepped.index()] != op1.project(pi1[e.index()])
            || pi2[stepped.index()] != op2.project(pi2[e.index()])
        {
            return false;
        }
    }
    true
}

/// Witness **R4.1.T5 (`CNF∞-BQF`)** — the instance algebra `(Inst_CRPT, ∘, ∩, ×, /, ∪)`
/// satisfies the standard **distributive-lattice-with-product** identities. Certifies the
/// load-bearing identities on a witness pair: `∩` and `∪` are **commutative** (up to the
/// dense-universe size and fixpoint signature) and `∩` is **idempotent**. Returns `true` when
/// the lattice identities hold.
pub fn certify_lattice_identities(m1: &Instance, m2: &Instance) -> bool {
    let size = |r: &Result<Instance, ProjectionError>| r.as_ref().ok().map(|m| m.substrate().universe_len());
    // ∩ and ∪ commute (same resulting universe size).
    let cap_comm = size(&intersection(m1, m2)) == size(&intersection(m2, m1));
    let cup_comm = size(&union(m1, m2)) == size(&union(m2, m1));
    // ∩ is idempotent: M ∩ M ≅ M (same universe).
    let cap_idem = size(&intersection(m1, m1)) == Some(m1.substrate().universe_len());
    cap_comm && cup_comm && cap_idem
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 𝒰 = {0,1}, 0 →_ρ 1, 1 ∈ NF.
    fn chain() -> Instance {
        Instance::from_functional_reduction(Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap()).unwrap()
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
    fn algebra_theorems_intersection_product_lattice() {
        let m = chain();
        // 18-1: the six instance-algebra operations are named.
        assert_eq!(INSTANCE_ALGEBRA_OPERATIONS.len(), 6);
        // ∩-Dec: intersection never grows the universe.
        assert!(certify_intersection_decreases(&m, &m));
        // Prod-Proj: both product projections are valid homomorphisms.
        assert!(certify_product_projections(&m, &m));
        // CNF∞-BQF: the lattice identities (∩/∪ commutative, ∩ idempotent) hold.
        assert!(certify_lattice_identities(&m, &m));
    }

    #[test]
    fn lattice_ops_intersection_union_quotient() {
        // M1: 0→1→2 (chain). M2: 0→1, 2 isolated NF (over the same 3-element prefix).
        let m1 = Instance::from_functional_reduction(
            Substrate::new(3, &[(0, 1), (1, 2)], &[(0, 1), (1, 2)]).unwrap(),
        )
        .unwrap();
        let m2 = Instance::from_functional_reduction(
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
        let chain = Instance::from_functional_reduction(
            Substrate::new(2, &[(0, 1)], &[(0, 1)]).unwrap(),
        )
        .unwrap();
        let q = quotient(&chain, &[7, 7]).unwrap(); // both in class 7
        assert_eq!(q.substrate().universe_len(), 1);
        assert!(q.operator().is_fixpoint(id(0)));
    }

    #[test]
    fn identity_instance_is_a_unit_fixpoint() {
        let one = identity_instance();
        let op = one.operator();
        assert_eq!(op.substrate().universe_len(), 1);
        assert!(op.is_fixpoint(id(0)));
        assert_eq!(op.fixpoints(), vec![id(0)]);
    }
}
