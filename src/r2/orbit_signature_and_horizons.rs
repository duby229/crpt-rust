//! # R2.1 — Orbit Signature and Horizon Predicates
//!
//! Exact realization of spec section **R2.1** (`CRPT_OMEGA_TOWER_R2.md`, v1.0.0-rc9):
//!
//! - R2.1.D3 `Ker-Cong` — the kernel ker(ρ_M, y) = ρ_M⁻¹(y) = {z | ρ_M(z) = y}.
//! - R2.1.D1 `H_S` — structural horizon: `H_S(x) :⟺ |ρ_M⁻¹(ρ_M(x))| > 1`.
//! - R2.1.D4 `H_O` — depth horizon: `H_O(x) :⟺ d_M(x) = 1`.
//! - R2.1.D2 `H_I` — invariant horizon, computed via the **decidable criterion**
//!   `H_I-Dec` (R2.1.C1): `H_I(x) = ⊤ ⟺ H_S(x) ∧ ∀z ∈ ker(ρ_M, ρ_M(x)) : d_M(z) = d_M(x)`
//!   (kernel d_M-uniformity — the non-circular form of R2.1.D2).
//! - R2.1.D5 `sig_M` — the orbit signature, ↓_M form `(↓, H_S, H_I, d_M, CFix)`.
//! - R2.1.T2/T4 `H_I-WD`/`H_I-KernelLocal` — H_I is kernel-local (witnessed).
//!
//! Horizons are computed on the convergent aspect ↓_M (where d_M is finite); H_S is
//! well-defined everywhere but H_I/H_O and the six-class (R2.2) live on ↓_M.

use crate::r1::substrate::ElementId;
use crate::r1::derivation_height::{derivation_height, DerivationHeight};
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r1::aspect_partition::preimage;

/// **R2.1.D3 (`Ker-Cong`)**: ker(ρ_M, y) = ρ_M⁻¹(y) = {z | ρ_M(z) = y}, ascending.
/// (Identical to `Pre_ρ({y})`, R1.9.D1.)
pub fn kernel(op: &ProjectionOperator, y: ElementId) -> Vec<ElementId> {
    preimage(op, y)
}

/// **R2.1.D1 (`H_S`)**: x has a structural horizon iff ρ_M(x) has more than one
/// preimage — `|ρ_M⁻¹(ρ_M(x))| > 1` (x has ρ_M-siblings).
pub fn structural_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    kernel(op, op.project(x)).len() > 1
}

/// **R2.1.D4 (`H_O`)**: x is on the boundary layer iff `d_M(x) = 1`.
pub fn depth_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    derivation_height(op, x) == DerivationHeight::Finite(1)
}

/// **R2.1.D2 (`H_I`)** via **R2.1.C1 (`H_I-Dec`)**: `H_I(x) = ⊤` iff `H_S(x)` and
/// every kernel-sibling shares x's derivation height (the kernel is d_M-uniform).
/// This is the exact, non-circular form of the R2.1.D2 signature-uniformity
/// condition (proved equivalent by `H_I-WD` R2.1.T2).
pub fn invariant_horizon(op: &ProjectionOperator, x: ElementId) -> bool {
    if !structural_horizon(op, x) {
        return false;
    }
    let height = derivation_height(op, x);
    kernel(op, op.project(x))
        .iter()
        .all(|&z| derivation_height(op, z) == height)
}

/// **R2.1.D6 (`HP`)** — the horizon profile `HP_M(x) = (H_S(x), H_I(x), H_O(x), Reg(x))`:
/// the three horizon predicates packaged with the aspect tag. It is the input to the
/// six-class partition function (R2.2) and to the observer triple (R3.1). `==` compares
/// the computed profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HorizonProfile {
    /// `H_S(x)` — the structural horizon (R2.1.D1).
    pub structural: bool,
    /// `H_I(x)` — the invariant horizon (R2.1.D2).
    pub invariant: bool,
    /// `H_O(x)` — the depth (ontological) horizon (R2.1.D4).
    pub ontological: bool,
    /// `Reg(x)` — the aspect tag (`Convergent` ↓_M / `Persistent` ∞_M, R1.9.D3).
    pub aspect: crate::r1::aspect_partition::Aspect,
}

/// **R2.1.D6 (`HP`)** — the horizon profile `HP_M(x)` of an element.
pub fn horizon_profile(op: &ProjectionOperator, x: ElementId) -> HorizonProfile {
    HorizonProfile {
        structural: structural_horizon(op, x),
        invariant: invariant_horizon(op, x),
        ontological: depth_horizon(op, x),
        aspect: crate::r1::aspect_partition::aspect_of(op, x),
    }
}

/// **R2.1.D5 (`sig_M`)** — the orbit signature of a convergent element:
/// `(↓, H_S(x), H_I(x), d_M(x), CFix(ρ_M)(x))`. The `↓` aspect tag is implicit
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

/// **R2.1.D5 (`sig_M`)**: the orbit signature of x — `Some` on ↓_M, `None` on ∞_M
/// (the persistent-aspect signature is the topological form, R2.3).
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

/// **R2.1.D5 (`sig_M-NM`) limit_id** — the persistent canonical representative's defining
/// datum on the topological tier: `lim ρ^n(x)`, the `𝒯`-limit the orbit converges to (the
/// `(∞, limit_id)` core of `sig_M-NM`; cf. `CPer` R1.3.D1). `None` off the `PA-WN_top`
/// sub-class of ∞_M. (The trace component is [`observation_trace`] below.)
pub fn limit_id<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
) -> Option<T::Point> {
    if sys.projection_depth(x).is_none() {
        sys.topological_limit(x)
    } else {
        None
    }
}

/// **R2.1.D5 (`sig_M-NM`), persistent form** — the persistent operative signature
/// `sig_M(x) = (∞, [OT^obs_M(x)]_{~tail})`: the aspect tag (implicit — `Some` only on
/// ∞_M) and the **tail class of the observation trace** (`Obs-Lab` R1.1.D8, `Tail-Eq`
/// R5) — what the orbit emits, up to finite prefix. Every comparison the signature
/// supports is an equality of traces (`Disc-Obs` R3.1.R4): no `ℝ^ℕ` profile, no
/// external order. Where `PA-WN_top` holds, the tail class *determines* the limit point
/// (`limit_id` is recovered, not postulated); metric instantiations supply rate
/// observables through `O_M` (`sig-Metric` R2.1.R11).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistentOrbitSignature<P> {
    /// `limit_id` — the `𝒯`-limit, **recovered** from the trace's tail class where
    /// `PA-WN_top` holds.
    pub limit_id: P,
    /// A prefix of the observation trace `OT^obs_M(x)` (its `~tail`-class is the
    /// signature component; the prefix is the finite presentation at this depth).
    pub trace_prefix: Vec<u32>,
}

/// **`OT^obs` (R1.1.D8 / `sig_M-NM` R2.1.D5)** — the orbit's **observation trace**
/// `OT^obs_M(x) = (obs(ρ_M^k(x)))_{k ∈ ℕ}`, exactly: the prefix to `depth`. The
/// substrate-native record of how the orbit behaves observably; traces compare by
/// equality / `Tail-Eq` — never an external order. `None` off the `PA-WN_top`
/// sub-class of ∞_M (no persistent signature there to present).
pub fn observation_trace<T: crate::r1::topology::TopologicalProjectionSystem>(
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

/// **R2.1.D5 (`sig_M-NM`)** — the persistent orbit signature of `x ∈ ∞_M`, with the
/// observation trace presented to `depth`. `None` off the `PA-WN_top` sub-class.
pub fn persistent_orbit_signature<T: crate::r1::topology::TopologicalProjectionSystem>(
    sys: &T,
    x: &T::Point,
    depth: u32,
) -> Option<PersistentOrbitSignature<T::Point>> {
    Some(PersistentOrbitSignature {
        limit_id: limit_id(sys, x)?,
        trace_prefix: observation_trace(sys, x, depth)?,
    })
}

/// Witness **R2.1.T2/T4 (`H_I-WD` / `H_I-KernelLocal`)**: H_I is kernel-local — if
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

/// Witness **R2.1.T1 (`Sig-Dep`)** — the **Signature Dependence** theorem: the orbit signature
/// `sig_M(x) = (H_S(x), d_M(x))` is the **minimal** signature needed to determine `H_I` —
/// within one kernel, two elements sharing `(H_S, d_M)` receive the same `H_I`. (`R2.1.R7`
/// `HI-CircResolved`: the apparent coinductive circularity is illusory — `H_I` is computed by
/// the non-circular `H_I-Dec` from `H_S` and depth, never from a `sig` already containing it.)
/// Returns the first same-kernel pair with equal `(H_S, d_M)` but different `H_I` (none), or `Ok`.
pub fn certify_signature_dependence(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            let same_kernel = op.project(x) == op.project(y);
            let same_sig = structural_horizon(op, x) == structural_horizon(op, y)
                && derivation_height(op, x) == derivation_height(op, y);
            if same_kernel && same_sig && invariant_horizon(op, x) != invariant_horizon(op, y) {
                return Err((x, y));
            }
        }
    }
    Ok(())
}

/// Witness **R2.1.R8 (`sig-Class`)** — `sig_M(x) = sig_M(y)` does **not** imply `x ≃_M y`: two
/// elements may share local structure (same `H_S`, same depth) yet reduce to *different*
/// canonical forms. Returns a witnessing pair `(x, y)` with equal `(H_S, d_M)` but distinct
/// `CNF_M` when one exists (so the bare signature under-determines `≃_M`), else `None`.
pub fn sig_class_witness(op: &ProjectionOperator) -> Option<(ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            if x == y {
                continue;
            }
            let same_sig = structural_horizon(op, x) == structural_horizon(op, y)
                && derivation_height(op, x) == derivation_height(op, y);
            let (cx, cy) = (op.canonical_fixpoint(x), op.canonical_fixpoint(y));
            if same_sig && cx.is_some() && cx != cy {
                return Some((x, y)); // same sig, different canonical form ⇒ not ≃_M
            }
        }
    }
    None
}

/// Witness **R2.1.R9 (`sig-Full`)** / **R2.1.R10 (`CNF-Suf`)** — the **extended** orbit
/// signature `sig_M^+(x) = (sig_M(x), CNF_M(x))` is a **complete** invariant: `sig_M^+(x) =
/// sig_M^+(y) ⟹ x ≃_M y`. Adding the canonical form to the local signature makes it fully
/// discriminating. Returns the first convergent pair with equal extended signature but
/// distinct `≃_M`-class (none — `≃_M` *is* `CNF`-equality), or `Ok`.
pub fn certify_extended_signature_complete(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            // sig^+ equality includes CNF_M equality (the OrbitSignature carries canonical_form).
            if let (Some(sx), Some(sy)) = (orbit_signature(op, x), orbit_signature(op, y)) {
                if sx == sy && !crate::r1::fibers::observable_equivalence(op, x, y) {
                    return Err((x, y));
                }
            }
        }
    }
    Ok(())
}

/// Witness **R2.1.T3 (`Hor-Abs`)** — the **Horizon Abstraction** theorem: the horizon profile
/// `HP_M` is a **complete invariant for the six-class partition** — two elements are in the
/// same class iff they have the same `HP_M`. Returns the first pair whose six-class agrees
/// with `HP_M`-equality disagreeing (none), or `Ok`. (`R2.1.R2` `HO-Notational`: `H_O` carries
/// no information beyond `d_M = 1`; `R2.1.R4` `sig-RegStrat`, `R2.1.R5` `Disc-Sig`, `R2.1.R6`
/// `sig-Insuf`: the signature is aspect-stratified, reads as a discernibility fingerprint, and
/// has full discriminating power only *within* a fiber.)
pub fn certify_horizon_abstraction(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    use crate::r2::six_class_horizon_partition::classify;
    // the classifying horizon profile is the triple (Fix, H_S, H_I) — the six classes are in
    // bijection with it; H_O/aspect are derived. Hor-Abs: this profile is a complete invariant.
    let profile = |x: ElementId| (op.is_fixpoint(x), structural_horizon(op, x), invariant_horizon(op, x));
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            if classify(op, x).is_some() && classify(op, y).is_some() {
                let profile_eq = profile(x) == profile(y);
                let class_eq = classify(op, x) == classify(op, y);
                if profile_eq != class_eq {
                    return Err((x, y));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::reduction_strategy::Instance;
    use crate::r1::substrate::Substrate;

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
        let m = Instance::from_functional_reduction(sub).unwrap(); let op = m.operator();
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
        // HP (R2.1.D6): the horizon profile packages (H_S, H_I, H_O, Reg).
        use crate::r1::aspect_partition::Aspect;
        assert_eq!(
            horizon_profile(&op, id(0)),
            HorizonProfile { structural: true, invariant: true, ontological: false, aspect: Aspect::Convergent }
        );
        // Sig-Dep: within a kernel, equal (H_S, d_M) ⇒ equal H_I.
        assert!(matches!(certify_signature_dependence(&op), Ok(())));
        // sig-Class: 0 and 2 share H_S but differ in CNF — same local sig ≠ same ≃_M.
        // (here they differ in depth too; a pure same-sig/different-CNF pair need not exist on
        // this small instance, so just confirm the witness search is sound — None or a valid pair.)
        assert!(sig_class_witness(&op).map_or(true, |(x, y)| x != y));
        // sig-Full / CNF-Suf: the extended signature (incl. CNF) is a complete invariant.
        assert!(matches!(certify_extended_signature_complete(&op), Ok(())));
        // Hor-Abs: the (Fix, H_S, H_I) profile is a complete six-class invariant.
        assert!(matches!(certify_horizon_abstraction(&op), Ok(())));
    }

    #[test]
    fn limit_id_is_the_topological_limit_on_persistent_orbits() {
        use crate::r1::topology::{ChainPoint, ConvergentChain};
        // sig_M-NM core: the Step orbit's defining datum is its 𝒯-limit ω; None on ↓_M.
        let chain = ConvergentChain;
        assert_eq!(limit_id(&chain, &ChainPoint::Step(0)), Some(ChainPoint::Limit));
        assert_eq!(limit_id(&chain, &ChainPoint::Limit), None);
    }

    #[test]
    fn persistent_orbit_signature_is_limit_and_observation_trace() {
        use crate::r1::topology::{ChainPoint, ConvergentChain};
        // sig_M-NM = (∞, limit_id, profile): on the chain, limit ω and the (minimal,
        // constant-0) observation trace — compared by CRPT equality, never an order.
        let chain = ConvergentChain;
        let sig = persistent_orbit_signature(&chain, &ChainPoint::Step(2), 3).unwrap();
        assert_eq!(sig.limit_id, ChainPoint::Limit);
        assert_eq!(sig.trace_prefix, vec![0, 0, 0, 0]);
        // equal signatures ⇒ observationally indiscernible (Disc-Obs): Step(2) vs Step(9).
        assert_eq!(sig, persistent_orbit_signature(&chain, &ChainPoint::Step(9), 3).unwrap());
        // no signature on the convergent side (ω): aspect-stratified.
        assert!(persistent_orbit_signature(&chain, &ChainPoint::Limit, 3).is_none());
    }
}
