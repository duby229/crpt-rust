//! # L3.1 — Horizon Predicates and Orbit Signature
//!
//! Exact realization of spec section **L3.1** (`CRPT_OMEGA_TOWER_L3.md`, rc3):
//!
//! - L3.1.D3 `Ker-Cong` — the kernel ker(ρ_M, y) = ρ_M⁻¹(y) = {z | ρ_M(z) = y}.
//! - L3.1.D1 `H_S` — structural horizon: `H_S(x) :⟺ |ρ_M⁻¹(ρ_M(x))| > 1`.
//! - L3.1.D4 `H_O` — depth horizon: `H_O(x) :⟺ d_M(x) = 1`.
//! - L3.1.D2 `H_I` — invariant horizon, computed via the **decidable criterion**
//!   `H_I-Dec` (L3.1.C1): `H_I(x) = ⊤ ⟺ H_S(x) ∧ ∀z ∈ ker(ρ_M, ρ_M(x)) : d_M(z) = d_M(x)`
//!   (kernel d_M-uniformity — the non-circular form of L3.1.D2).
//! - L3.1.D5 `sig_M` — the orbit signature, ↓_M form `(↓, H_S, H_I, d_M, CFix)`.
//! - L3.1.T2/T4 `H_I-WD`/`H_I-KernelLocal` — H_I is kernel-local (witnessed).
//!
//! Horizons are computed on the convergent regime ↓_M (where d_M is finite); H_S is
//! well-defined everywhere but H_I/H_O and the six-class (L3.2) live on ↓_M.

use crate::l1::substrate::ElementId;
use crate::l2::depth::{derivation_height, DerivationHeight};
use crate::l2::projection::ProjectionOperator;
use crate::l2::regime::preimage;

/// **L3.1.D3 (`Ker-Cong`)**: ker(ρ_M, y) = ρ_M⁻¹(y) = {z | ρ_M(z) = y}, ascending.
/// (Identical to `Pre_ρ({y})`, L2.2.D1.)
pub fn kernel(op: &ProjectionOperator, y: ElementId) -> Vec<ElementId> {
    preimage(op, y)
}

/// **L3.1.D1 (`H_S`)**: x has a structural horizon iff ρ_M(x) has more than one
/// preimage — `|ρ_M⁻¹(ρ_M(x))| > 1` (x has ρ_M-siblings).
pub fn structural_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    kernel(op, op.project(x)).len() > 1
}

/// **L3.1.D4 (`H_O`)**: x is on the boundary layer iff `d_M(x) = 1`.
pub fn depth_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    derivation_height(op, x) == DerivationHeight::Finite(1)
}

/// **L3.1.D2 (`H_I`)** via **L3.1.C1 (`H_I-Dec`)**: `H_I(x) = ⊤` iff `H_S(x)` and
/// every kernel-sibling shares x's derivation height (the kernel is d_M-uniform).
/// This is the exact, non-circular form of the L3.1.D2 signature-uniformity
/// condition (proved equivalent by `H_I-WD` L3.1.T2).
pub fn invariant_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    if !structural_horizon(op, x) {
        return false;
    }
    let height = derivation_height(op, x);
    kernel(op, op.project(x))
        .iter()
        .all(|&z| derivation_height(op, z) == height)
}

/// **L3.1.D6 (`HP`)** — the horizon profile `HP_M(x) = (H_S(x), H_I(x), H_O(x), Reg(x))`:
/// the three horizon predicates packaged with the regime tag. It is the input to the
/// six-class partition function (L3.2) and to the observer triple (L4.1). `==` compares
/// the computed profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HorizonProfile {
    /// `H_S(x)` — the structural horizon (L3.1.D1).
    pub structural: bool,
    /// `H_I(x)` — the invariant horizon (L3.1.D2).
    pub invariant: bool,
    /// `H_O(x)` — the depth (ontological) horizon (L3.1.D4).
    pub ontological: bool,
    /// `Reg(x)` — the regime tag (`Convergent` ↓_M / `Persistent` ∞_M, L2.2.D3).
    pub regime: crate::l2::regime::Regime,
}

/// **L3.1.D6 (`HP`)** — the horizon profile `HP_M(x)` of an element.
pub fn horizon_profile(op: &ProjectionOperator, x: ElementId) -> HorizonProfile {
    HorizonProfile {
        structural: structural_horizon(op, x),
        invariant: invariant_horizon(op, x),
        ontological: depth_horizon(op, x),
        regime: crate::l2::regime::regime_of(op, x),
    }
}

/// **L3.1.D5 (`sig_M`)** — the orbit signature of a convergent element:
/// `(↓, H_S(x), H_I(x), d_M(x), CFix(ρ_M)(x))`. The `↓` regime tag is implicit
/// (this is `Some` only on ↓_M). `==` compares the computed signature value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrbitSignature {
    /// H_S(x).
    pub structural: bool,
    /// H_I(x).
    pub invariant: bool,
    /// d_M(x).
    pub depth: u32,
    /// CFix(ρ_M)(x).
    pub canonical_form: ElementId,
}

/// **L3.1.D5 (`sig_M`)**: the orbit signature of x — `Some` on ↓_M, `None` on ∞_M
/// (the persistent-regime signature is the topological form, L3.3).
pub fn orbit_signature(op: &ProjectionOperator, x: ElementId) -> Option<OrbitSignature> {
    match (derivation_height(op, x), op.canonical_fixpoint(x)) {
        (DerivationHeight::Finite(depth), Some(canonical_form)) => Some(OrbitSignature {
            structural: structural_horizon(op, x),
            invariant: invariant_horizon(op, x),
            depth,
            canonical_form,
        }),
        _ => None,
    }
}

/// **L3.1.D5 (`sig_M-NM`) limit_id** — the persistent canonical representative's defining
/// datum on the topological tier: `lim ρ^n(x)`, the `𝒯`-limit the orbit converges to (the
/// `(∞, limit_id)` core of `sig_M-NM`; cf. `CPer` L1.3.D1). `None` off the `PA-WN_top`
/// sub-class of ∞_M. (The trace component is [`observation_trace`] below.)
pub fn limit_id<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<T::Point> {
    if sys.is_persistent(x) {
        sys.topological_limit(x)
    } else {
        None
    }
}

/// **L3.1.D5 (`sig_M-NM`, rc4), persistent form** — the persistent operative signature
/// `sig_M(x) = (∞, [OT^obs_M(x)]_{~tail})`: the regime tag (implicit — `Some` only on
/// ∞_M) and the **tail class of the observation trace** (`Obs-Lab` L1.1.D8, `Tail-Eq`
/// L6.3.D2) — what the orbit emits, up to finite prefix. Every comparison the signature
/// supports is an equality of traces (`Disc-Obs` L4.1.R4): no `ℝ^ℕ` profile, no
/// external order. Where `PA-WN_top` holds, the tail class *determines* the limit point
/// (`limit_id` is recovered, not postulated); metric instantiations supply rate
/// observables through `O_M` (`sig-Metric` L3.1.R11).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistentOrbitSignature<P> {
    /// `limit_id` — the `𝒯`-limit, **recovered** from the trace's tail class where
    /// `PA-WN_top` holds.
    pub limit_id: P,
    /// A prefix of the observation trace `OT^obs_M(x)` (its `~tail`-class is the
    /// signature component; the prefix is the finite presentation at this depth).
    pub trace_prefix: Vec<u32>,
}

/// **`OT^obs` (L1.1.D8 / `sig_M-NM` L3.1.D5)** — the orbit's **observation trace**
/// `OT^obs_M(x) = (obs(ρ_M^k(x)))_{k ∈ ℕ}`, exactly: the prefix to `depth`. The
/// substrate-native record of how the orbit behaves observably; traces compare by
/// equality / `Tail-Eq` — never an external order. `None` off the `PA-WN_top`
/// sub-class of ∞_M (no persistent signature there to present).
pub fn observation_trace<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
    depth: u32,
) -> Option<Vec<u32>> {
    limit_id(sys, x)?;
    let mut trace = Vec::with_capacity(depth as usize + 1);
    let mut current = x.clone();
    for _ in 0..=depth {
        trace.push(sys.observation(&current));
        current = sys.projection(&current);
    }
    Some(trace)
}

/// **L3.1.D5 (`sig_M-NM`, rc4)** — the persistent orbit signature of `x ∈ ∞_M`, with the
/// observation trace presented to `depth`. `None` off the `PA-WN_top` sub-class.
pub fn persistent_orbit_signature<T: crate::l1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
    depth: u32,
) -> Option<PersistentOrbitSignature<T::Point>> {
    Some(PersistentOrbitSignature {
        limit_id: limit_id(sys, x)?,
        trace_prefix: observation_trace(sys, x, depth)?,
    })
}

/// Witness **L3.1.T2/T4 (`H_I-WD` / `H_I-KernelLocal`)**: H_I is kernel-local — if
/// ρ_M(x) = ρ_M(y) (same kernel) then H_I(x) = H_I(y). First violation, or `Ok`.
pub fn certify_h_i_kernel_local(
    op: &ProjectionOperator,
) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            if op.project(x) == op.project(y)
                && invariant_horizon(op, x) != invariant_horizon(op, y)
            {
                return Err((x, y));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l2::projection::Model;
    use crate::l1::substrate::Substrate;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// 0→2, 1→2, 2→3, 3 ∈ NF. Kernel(2) = {0,1} (uniform, d=2); kernel(3) = {2,3}
    /// (non-uniform, d∈{1,0}).
    fn s() -> Substrate {
        let e = [(0, 2), (1, 2), (2, 3)];
        Substrate::new(4, &e, &e).unwrap()
    }

    #[test]
    fn horizons() {
        let sub = s();
        let m = Model::from_functional_reduction(sub).unwrap(); let op = m.operator();
        // H_S
        assert!(structural_horizon(&op, id(0))); // kernel(ρ0=2) = {0,1}
        assert!(structural_horizon(&op, id(2))); // kernel(ρ2=3) = {2,3}
        // H_I via d_M-uniformity
        assert!(invariant_horizon(&op, id(0))); // {0,1} both d=2 ⇒ uniform ⇒ H_I=⊤
        assert!(!invariant_horizon(&op, id(2))); // {2,3} d∈{1,0} ⇒ non-uniform ⇒ H_I=⊥
        // H_O
        assert!(depth_horizon(&op, id(2))); // d_M(2)=1
        assert!(!depth_horizon(&op, id(0))); // d_M(0)=2
        // sig_M
        assert_eq!(
            orbit_signature(&op, id(0)),
            Some(OrbitSignature { structural: true, invariant: true, depth: 2, canonical_form: id(3) })
        );
        assert!(matches!(certify_h_i_kernel_local(&op), Ok(())));
        // HP (L3.1.D6): the horizon profile packages (H_S, H_I, H_O, Reg).
        use crate::l2::regime::Regime;
        assert_eq!(
            horizon_profile(&op, id(0)),
            HorizonProfile { structural: true, invariant: true, ontological: false, regime: Regime::Convergent }
        );
    }

    #[test]
    fn limit_id_is_the_topological_limit_on_persistent_orbits() {
        use crate::l1::topology::{ChainPoint, ConvergentChain};
        // sig_M-NM core: the Step orbit's defining datum is its 𝒯-limit ω; None on ↓_M.
        let chain = ConvergentChain;
        assert_eq!(limit_id(&chain, &ChainPoint::Step(0)), Some(ChainPoint::Limit));
        assert_eq!(limit_id(&chain, &ChainPoint::Limit), None);
    }

    #[test]
    fn persistent_orbit_signature_is_limit_and_observation_trace() {
        use crate::l1::topology::{ChainPoint, ConvergentChain};
        // sig_M-NM = (∞, limit_id, profile): on the chain, limit ω and the (minimal,
        // constant-0) observation trace — compared by CRPT equality, never an order.
        let chain = ConvergentChain;
        let sig = persistent_orbit_signature(&chain, &ChainPoint::Step(2), 3).unwrap();
        assert_eq!(sig.limit_id, ChainPoint::Limit);
        assert_eq!(sig.trace_prefix, vec![0, 0, 0, 0]);
        // equal signatures ⇒ observationally indiscernible (Disc-Obs): Step(2) vs Step(9).
        assert_eq!(sig, persistent_orbit_signature(&chain, &ChainPoint::Step(9), 3).unwrap());
        // no signature on the convergent side (ω): regime-stratified.
        assert!(persistent_orbit_signature(&chain, &ChainPoint::Limit, 3).is_none());
    }
}
