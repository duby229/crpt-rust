//! # R3.3 — Projection Valuation (PV)
//!
//! Exact realization of spec section **R3.3** (`CRPT_OMEGA_TOWER_R3.md`, v1.0.0-rc9):
//!
//! - R3.3.D1 `VS` — the value semiring V = (V, +, ·, 0, 1).
//! - R3.3.D2 `Step-W` — the step weighting w : →_ρ → V.
//! - R3.3.D4/C1 `PV-WF`/`PV1C` — the projection valuation, with PV(ε) = 1 and
//!   PV accumulating step weights by the semiring product. For the deterministic
//!   ρ_M-orbit the orbit valuation is `PV_c(x) = ∏_i w(ρ_M^i(x) → ρ_M^{i+1}(x))`.
//! - R3.3.D5 `IRH-x` — the infinite reduction histories `ℋ_infinite(x)` on `∞_M`
//!   ([`infinite_reduction_history`]; under C1 there is exactly one).
//! - R3.3.D6 `PV∞` + R3.3.T2 `PV2` — the NWF valuation `PV∞(h) := lim_{n→∞} PV(h|_n)`
//!   in a topologised semiring ([`pv_infinity`]): the engine decides the
//!   **discrete-topology** limit *exactly* on eventually-periodic orbits — which is
//!   precisely PV2's scope ("under SC-2/3, the orbit is eventually periodic; the
//!   sequence PV(h|_n) stabilises or has a well-defined limiting product").
//!
//! Parametric in the semiring (R3.3.D1). The product along the orbit needs only
//! `one`/`multiply`; `zero`/`add` complete the semiring (used by the full
//! sum-over-histories PV1 on a branching →_ρ, out of scope for the orbit form).

use crate::r1::substrate::{ElementId, Substrate};
use crate::r1::reduction_strategy::ProjectionOperator;

/// **R3.3.D3 (`FRH`)** — the finite reduction histories `ℋ_finite(x)`: the maximal finite
/// →_ρ-paths from x, each ending at a normal form (or a point all of whose successors are
/// already on the path). The sum-over-histories form of `PV` ranges over these. Paths are
/// **simple** (no element repeats), so the enumeration is finite even when →_ρ has cycles.
/// Each history is the element sequence `x = x₀ →_ρ x₁ →_ρ … →_ρ xₙ`.
pub fn finite_reduction_histories(s: &Substrate, x: ElementId) -> Vec<Vec<ElementId>> {
    fn walk(
        s: &Substrate,
        current: ElementId,
        path: &mut Vec<ElementId>,
        on_path: &mut [bool],
        out: &mut Vec<Vec<ElementId>>,
    ) {
        let mut extended = false;
        for &y in s.reduction_successors(current) {
            if !on_path[y.index()] {
                on_path[y.index()] = true;
                path.push(y);
                walk(s, y, path, on_path, out);
                path.pop();
                on_path[y.index()] = false;
                extended = true;
            }
        }
        if !extended {
            out.push(path.clone()); // a normal form, or maximal (all successors on-path)
        }
    }
    let mut on_path = vec![false; s.universe_len() as usize];
    on_path[x.index()] = true;
    let mut path = vec![x];
    let mut out = Vec::new();
    walk(s, x, &mut path, &mut on_path, &mut out);
    out
}

/// **R3.3.D1 (`VS`)** — a value semiring V = (V, +, ·, 0, 1): (V, +, 0) a commutative
/// monoid, (V, ·, 1) a monoid, · distributes over +, 0 absorbing.
pub trait Semiring {
    /// The carrier V.
    type Value;
    /// The additive identity 0.
    fn zero() -> Self::Value;
    /// The multiplicative identity 1.
    fn one() -> Self::Value;
    /// The additive operation +.
    fn add(a: &Self::Value, b: &Self::Value) -> Self::Value;
    /// The multiplicative operation ·.
    fn multiply(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// **R3.3.C1 (`PV1C`)** — the orbit valuation `PV_c(x) = ∏_i w(ρ_M^i(x) → ρ_M^{i+1}(x))`,
/// the semiring product of step weights along the ρ_M-orbit from x to CFix(ρ_M)(x).
/// `Some` on ↓_M (the orbit terminates); `None` on ∞_M (no finitary orbit valuation).
pub fn path_valuation<S, W>(op: &ProjectionOperator, x: ElementId, weight: W) -> Option<S::Value>
where
    S: Semiring,
    W: Fn(ElementId, ElementId) -> S::Value,
{
    op.canonical_fixpoint(x)?; // ∞_M ⇒ None
    let mut accumulator = S::one();
    let mut current = x;
    while !op.is_fixpoint(current) {
        let next = op.project(current);
        accumulator = S::multiply(&accumulator, &weight(current, next));
        current = next;
    }
    Some(accumulator)
}

/// The unit step weight (`w ≡ 1`). Under [`Tropical`] this makes PV the orbit length.
pub fn unit_weight(_from: ElementId, _to: ElementId) -> u64 {
    1
}

/// **R3.3.D5 (`IRH-x`)** — the infinite reduction histories
/// `ℋ_infinite(x) := { h : ℕ → 𝒰_M | h(0) = x, ∀n : h(n) →_ρ h(n+1) }`, defined on
/// `x ∈ ∞_M` (νT). Under determinism (C1) the projection is functional, so `ℋ_infinite(x)`
/// is the **singleton** {π-orbit of x}; this returns its finite prefix `h|_n`
/// (n+1 points), on any instance of the one
/// [`ProjectionSystem`](crate::r0::projection_systems_and_fibers::ProjectionSystem) trait — finite or
/// symbolic-infinite. `None` off `∞_M` (a convergent element has no infinite →_ρ-history).
pub fn infinite_reduction_history<P: crate::r0::projection_systems_and_fibers::ProjectionSystem>(
    sys: &P,
    x: &P::Point,
    n: u32,
) -> Option<Vec<P::Point>> {
    if sys.projection_depth(x).is_some() {
        return None; // ℋ_infinite(x) = ∅ on ↓_M
    }
    let mut history = Vec::with_capacity(n as usize + 1);
    let mut current = x.clone();
    for _ in 0..n {
        let next = sys.projection(&current);
        history.push(current);
        current = next;
    }
    history.push(current);
    Some(history)
}

/// The exact **discrete-topology** decision for `PV∞` (R3.3.D6): `lim_{n→∞} PV(h|_n)`
/// exists in the discrete topology iff the prefix-valuation sequence is eventually
/// constant. Three-valued and never wrong.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiscreteLimit<V> {
    /// Proven: the sequence `PV(h|_n)` stabilises — the limit is this value.
    Exists(V),
    /// Proven: the sequence is eventually periodic and **non-constant** on its period —
    /// no discrete limit. (A metric/order semiring topology may still assign one — e.g.
    /// the per-period "limiting product" — that is the metric tier's refinement.)
    DoesNotExist,
    /// Outside the decided scope within the step budget: the orbit did not reveal a
    /// period (e.g. a non-periodic symbolic orbit — beyond PV2's SC-2/3 scope, where the
    /// `𝒯`-limit machinery, not the discrete one, owns the limit).
    Undetermined,
}

/// **R3.3.D6 (`PV∞`) / R3.3.T2 (`PV2`)** — the NWF valuation
/// `PV∞(h) := lim_{n→∞} PV(h|_n)` for the (unique, C1) infinite history `h` of
/// `x ∈ ∞_M`, in the **discrete** semiring topology — decided *exactly* on
/// eventually-periodic orbits, which is PV2's own scope (SC-2/3). The decision walks the
/// orbit until it cycles (entry `k`, period `p`), then iterates the per-period value map
/// `u ↦ u · c` (`c` = the period's weight product): if some period-pass leaves the value
/// fixed at every step, the sequence has stabilised (`Exists`); if the per-period values
/// cycle without ever being flat, the sequence oscillates forever (`DoesNotExist`).
/// Budgeted by `max_steps` in both phases; `None` off `∞_M` (no infinite history).
pub fn pv_infinity<P, S, W>(
    sys: &P,
    x: &P::Point,
    weight: W,
    max_steps: u32,
) -> Option<DiscreteLimit<S::Value>>
where
    P: crate::r0::projection_systems_and_fibers::ProjectionSystem,
    S: Semiring,
    S::Value: Clone + PartialEq,
    W: Fn(&P::Point, &P::Point) -> S::Value,
{
    if sys.projection_depth(x).is_some() {
        return None; // ℋ_infinite(x) = ∅ on ↓_M (IRH-x is νT-scoped)
    }
    // Phase 1: walk h, accumulating PV(h|_n), until the orbit reveals its period.
    let mut points: Vec<P::Point> = vec![x.clone()];
    let mut prefix_values: Vec<S::Value> = vec![S::one()]; // PV(h|_n) at each n
    let mut current = x.clone();
    let mut cycle: Option<(usize, usize)> = None; // (entry index k, period p)
    for _ in 0..max_steps {
        let next = sys.projection(&current);
        let value = S::multiply(prefix_values.last().expect("nonempty"), &weight(&current, &next));
        if let Some(entry) = points.iter().position(|q| *q == next) {
            cycle = Some((entry, points.len() - entry));
            break;
        }
        points.push(next.clone());
        prefix_values.push(value);
        current = next;
    }
    let Some((entry, period)) = cycle else {
        return Some(DiscreteLimit::Undetermined); // no period within budget (beyond SC-2/3)
    };
    // Phase 2: from u_0 = PV(h|_entry), iterate period passes u_{j+1} = u_j · c.
    let mut u = prefix_values[entry].clone();
    let mut seen: Vec<S::Value> = Vec::new();
    for _ in 0..max_steps {
        // one period pass, checking flatness step by step.
        let mut value = u.clone();
        let mut flat = true;
        for i in 0..period {
            let from = &points[entry + i];
            let to = if entry + i + 1 < points.len() { &points[entry + i + 1] } else { &points[entry] };
            let next_value = S::multiply(&value, &weight(from, to));
            if next_value != value {
                flat = false;
            }
            value = next_value;
        }
        if flat {
            return Some(DiscreteLimit::Exists(u)); // every further step leaves PV fixed
        }
        seen.push(u);
        if seen.contains(&value) {
            // per-period values cycle and no member of the cycle is flat ⇒ PV(h|_n)
            // changes within every period forever ⇒ not eventually constant.
            return Some(DiscreteLimit::DoesNotExist);
        }
        u = value;
    }
    Some(DiscreteLimit::Undetermined)
}

/// The tropical (min-plus) semiring (ℕ ∪ {∞}, min, +, ∞, 0). With [`unit_weight`],
/// `path_valuation` yields the orbit length — i.e. d_M(x) — realizing the
/// "unweighted PV counts the trajectory length" reading (R3.1.D2). `∞ = u64::MAX`.
pub struct Tropical;

impl Semiring for Tropical {
    type Value = u64;
    fn zero() -> u64 {
        u64::MAX
    }
    fn one() -> u64 {
        0
    }
    fn add(a: &u64, b: &u64) -> u64 {
        (*a).min(*b)
    }
    fn multiply(a: &u64, b: &u64) -> u64 {
        a.saturating_add(*b)
    }
}

/// The Boolean reachability semiring (𝔹, ∨, ∧, ⊥, ⊤).
pub struct Boolean;

impl Semiring for Boolean {
    type Value = bool;
    fn zero() -> bool {
        false
    }
    fn one() -> bool {
        true
    }
    fn add(a: &bool, b: &bool) -> bool {
        *a || *b
    }
    fn multiply(a: &bool, b: &bool) -> bool {
        *a && *b
    }
}


/// Witness **R3.3.T3 (`PV-Dual`)** — the projection valuation duality: for
/// convergent `x` with canonical form `f = CNF_M(x)`,
/// `PV_M(x) = w-path(x, f) · PV_M^{fix}(f)` — element valuation factors as the
/// accumulated weight of the canonical reduction path times the canonical form's own
/// valuation (`PV^{fix}(f) = PV(ε) = 1`, the constant history at `f`, R3.3.D4). Returns
/// the first convergent element where the factorization fails, or `Ok`.
pub fn certify_pv_dual<S, W>(op: &ProjectionOperator, weight: W) -> Result<(), ElementId>
where
    S: Semiring,
    S::Value: PartialEq,
    W: Fn(ElementId, ElementId) -> S::Value,
{
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_none() {
            continue;
        }
        // w-path(x, f): the product of step weights along the canonical path.
        let mut w_path = S::one();
        let mut current = x;
        while !op.is_fixpoint(current) {
            let next = op.project(current);
            w_path = S::multiply(&w_path, &weight(current, next));
            current = next;
        }
        let pv_fix = S::one(); // PV^{fix}(f) = PV(ε) = 1
        let factored = S::multiply(&w_path, &pv_fix);
        if path_valuation::<S, _>(op, x, &weight) != Some(factored) {
            return Err(x);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

    #[test]
    fn unweighted_pv_is_orbit_length() {
        // 0→2, 1→2, 2→3, 3 ∈ NF ⇒ d_M(0)=2, d_M(2)=1, d_M(3)=0; 0 ⇄ 1 would be ∞.
        let e = [(0, 2), (1, 2), (2, 3)];
        let s = Substrate::new(4, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(path_valuation::<Tropical, _>(&op, ElementId(0), unit_weight), Some(2));
        assert_eq!(path_valuation::<Tropical, _>(&op, ElementId(2), unit_weight), Some(1));
        assert_eq!(path_valuation::<Tropical, _>(&op, ElementId(3), unit_weight), Some(0));
    }

    #[test]
    fn finite_reduction_histories_enumerate_paths_to_nf() {
        // Branching: 0→1, 0→2, 1→3, 2→3, 3 ∈ NF. Two histories: [0,1,3] and [0,2,3].
        let e = [(0, 1), (0, 2), (1, 3), (2, 3)];
        let s = Substrate::new(4, &e, &e).unwrap();
        let mut hist = finite_reduction_histories(&s, ElementId(0));
        hist.sort_by(|a, b| a.iter().map(|e| e.0).cmp(b.iter().map(|e| e.0)));
        assert_eq!(
            hist,
            vec![
                vec![ElementId(0), ElementId(1), ElementId(3)],
                vec![ElementId(0), ElementId(2), ElementId(3)],
            ]
        );
        // a normal form has the single trivial history [3].
        assert_eq!(finite_reduction_histories(&s, ElementId(3)), vec![vec![ElementId(3)]]);
    }

    #[test]
    fn pv_dual_factorization() {
        // PV-Dual (R3.3.T3): PV(x) = w-path(x, f) · PV^fix(f) on every convergent x.
        let e = [(0, 2), (1, 2), (2, 3)];
        let s = Substrate::new(4, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap();
        let op = m.operator();
        assert!(matches!(certify_pv_dual::<Tropical, _>(&op, unit_weight), Ok(())));
        assert!(matches!(certify_pv_dual::<Boolean, _>(&op, |_, _| true), Ok(())));
    }

    #[test]
    fn pv_none_on_persistent() {
        let e = [(0, 1), (1, 0)];
        let s = Substrate::new(2, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap(); let op = m.operator();
        assert_eq!(path_valuation::<Tropical, _>(&op, ElementId(0), unit_weight), None);
        assert_eq!(path_valuation::<Boolean, _>(&op, ElementId(0), |_, _| true), None);
    }

    // ===== IRH-x (R3.3.D5) and PV∞ (R3.3.D6 / PV2) =====

    /// The sign monoid as a value semiring ({…,−1,0,1,…}, +, ·, 0, 1) — multiplicative
    /// wobble: weight −1 each step makes PV(h|_n) oscillate 1, −1, 1, … (no discrete limit,
    /// though each full period's product is +1 — the "limiting product" a richer topology
    /// would assign).
    struct Sign;
    impl Semiring for Sign {
        type Value = i64;
        fn zero() -> i64 {
            0
        }
        fn one() -> i64 {
            1
        }
        fn add(a: &i64, b: &i64) -> i64 {
            a + b
        }
        fn multiply(a: &i64, b: &i64) -> i64 {
            a * b
        }
    }

    #[test]
    fn infinite_reduction_history_is_the_orbit_prefix() {
        // pure cycle 0 ⇄ 1 (∞_M): the unique infinite history h = 0,1,0,1,…
        let e = [(0, 1), (1, 0)];
        let s = Substrate::new(2, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap();
        let op = m.operator();
        assert_eq!(
            infinite_reduction_history(&op, &ElementId(0), 3),
            Some(vec![ElementId(0), ElementId(1), ElementId(0), ElementId(1)])
        );
        // ℋ_infinite is νT-scoped: a convergent element has no infinite →_ρ-history.
        let e2 = [(0, 1)];
        let s2 = Substrate::new(2, &e2, &e2).unwrap();
        let m2 = Instance::from_functional_reduction(s2).unwrap();
        assert_eq!(infinite_reduction_history(&m2.operator(), &ElementId(0), 3), None);
    }

    #[test]
    fn pv_infinity_decides_all_three_outcomes_on_the_cycle() {
        let e = [(0, 1), (1, 0)];
        let s = Substrate::new(2, &e, &e).unwrap();
        let m = Instance::from_functional_reduction(s).unwrap();
        let op = m.operator();
        // (1) stabilises immediately: Boolean with weight ≡ ⊤ keeps PV(h|_n) = ⊤ forever.
        assert_eq!(
            pv_infinity::<_, Boolean, _>(&op, &ElementId(0), |_, _| true, 16),
            Some(DiscreteLimit::Exists(true))
        );
        // (2) stabilises *later* (absorption): weight ⊥ on 0→1 sends PV to the absorbing ⊥
        //     during the first pass; from then on every step leaves it fixed.
        assert_eq!(
            pv_infinity::<_, Boolean, _>(
                &op,
                &ElementId(0),
                |from, _| *from != ElementId(0),
                16
            ),
            Some(DiscreteLimit::Exists(false))
        );
        // (3) no discrete limit: Sign weight −1 each step ⇒ PV(h|_n) = 1, −1, 1, −1, …
        //     (each period's product is +1, but the sequence is non-constant on the period).
        assert_eq!(
            pv_infinity::<_, Sign, _>(&op, &ElementId(0), |_, _| -1, 16),
            Some(DiscreteLimit::DoesNotExist)
        );
        // νT-scoping: a convergent element has no infinite history at all.
        let e2 = [(0, 1)];
        let s2 = Substrate::new(2, &e2, &e2).unwrap();
        let m2 = Instance::from_functional_reduction(s2).unwrap();
        assert_eq!(
            pv_infinity::<_, Boolean, _>(&m2.operator(), &ElementId(0), |_, _| true, 16),
            None
        );
    }

    #[test]
    fn pv_infinity_is_undetermined_beyond_the_periodic_scope() {
        use crate::r1::topology::{ChainPoint, ConvergentChain};
        // ℕ ∪ {ω}: the Step orbit never cycles (aperiodic symbolic orbit) — outside PV2's
        // SC-2/3 scope, so the discrete decision is honestly Undetermined (the 𝒯-limit
        // tier, not the discrete topology, owns this limit).
        let chain = ConvergentChain;
        assert_eq!(
            pv_infinity::<_, Boolean, _>(&chain, &ChainPoint::Step(0), |_, _| true, 32),
            Some(DiscreteLimit::Undetermined)
        );
        // and the IRH prefix is still exact there:
        assert_eq!(
            infinite_reduction_history(&chain, &ChainPoint::Step(0), 2),
            Some(vec![ChainPoint::Step(0), ChainPoint::Step(1), ChainPoint::Step(2)])
        );
        // ω is convergent: no infinite history.
        assert_eq!(infinite_reduction_history(&chain, &ChainPoint::Limit, 2), None);
    }
}
