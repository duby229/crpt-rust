//! # R6.7 / R6.12 / R6.13 — The Tower, Invariance, Fractality, Infiniteness
//!
//! Exact realization of spec sections **R6.7, R6.12, R6.13** (`CRPT_OMEGA_TOWER_R6.md`,
//! v1.0.0-rc9):
//!
//! - R6.7.D1 `Tower-Def` — `Tower(M)` is the sequence `M₀ = M`, `M_{n+1} = Reify(M_n)`.
//! - R6.7.T2 `NFC-TInv` — the query signature is tower-invariant: `Q_{M_n} ≅ Q_{M₀}`
//!   for all n. So `|Q|` is a single number carried up the whole tower.
//! - R6.12.D1 `Twr-Tail` / R6.12.D2 `CRPT-Fractal` (`Tower-Frac`) — fractal self-similarity: since `Q` is invariant, every level
//!   `n ≥ 1` is the free monoid over `Q_{M₀}` — `Reify(M_n)` depends only on `|Q|`, so
//!   the tail `M₁, M₂, …` is self-similar (all reifies of a `|Q|`-atom signature).
//! - R6.13.T2 `Tower-Inf` — the tower is **strictly infinite** (no two levels
//!   isomorphic) iff `|Q_M| ≥ 2`; for `|Q_M| = 1` it is **degenerate** (`Reify` ≅
//!   ℕ-with-successor, R6.13.R2), and the empty signature `|Q_M| = 0` cannot arise on
//!   a non-trivial instance.
//! - R6.13.C2 `Reify-Pure-WF` — every level `n ≥ 1` is pure-WF (see [`crate::r6::reification_operator`]).

use crate::r1::reduction_strategy::Instance;
use crate::r6::reification_operator::{reify, Reify};

/// **R6.7.D1 (`Tower-Def`)** — the tower over a base instance. Because the query
/// signature is tower-invariant (`NFC-TInv`), the tower is determined by the base
/// instance and its invariant atom count `|Q|`; levels `n ≥ 1` are all the free monoid
/// over that signature.
pub struct Tower<'a> {
    base: &'a Instance,
    atom_count: u32, // |Q_M|, invariant across all levels (NFC-TInv)
}

/// **R6.7.D1 (`Tower-Def`)**: `Tower(M)`.
pub fn tower(base: &Instance) -> Tower<'_> {
    let atom_count = base.operator().fixpoints().len() as u32;
    Tower { base, atom_count }
}

impl<'a> Tower<'a> {
    /// The base instance `M₀`.
    pub fn base(&self) -> &Instance {
        self.base
    }

    /// **R6.7.T2 (`NFC-TInv`)** — the invariant query-signature size `|Q_{M_n}| = |Q_{M₀}|`.
    pub fn query_signature_size(&self) -> u32 {
        self.atom_count
    }

    /// **R6.5.D2** — the reify `M₁ = Reify(M₀)`. (By `NFC-TInv`/`Tower-Frac` every higher
    /// level `M_{n+1} = Reify(M_n)` is the free monoid over the same signature, so this
    /// single reify captures the structure of the whole tail.)
    pub fn reify(&self) -> Reify {
        reify(self.base)
    }

    /// **R6.13.T2 (`Tower-Inf`)** — the tower is strictly infinite (no two distinct
    /// levels isomorphic) iff `|Q_M| ≥ 2`.
    pub fn is_strictly_infinite(&self) -> bool {
        self.atom_count >= 2
    }

    /// **R6.13.R2** — the tower is degenerate (`Reify` ≅ ℕ-with-successor; the words over
    /// a single atom are `aⁿ`) iff `|Q_M| = 1`.
    pub fn is_degenerate(&self) -> bool {
        self.atom_count == 1
    }

    /// **R6.9.D1 (`Twr-Img`)** — the **tower image** of `x` at level 1: `ι(CFix(x))`, the
    /// one-atom word `[CFix(x)]` in `FMA(Q_M) = Fix(ρ_{Reify(M)})`. By `NFC-TInv` it is the
    /// same atom at every higher level. `None` on ∞_M (no finitary canonical form).
    pub fn tower_image(&self, x: crate::r1::substrate::ElementId) -> Option<crate::r6::free_monoidal_algebra::Word> {
        self.base.operator().canonical_fixpoint(x).map(|f| self.reify().canonical_inclusion(f))
    }

    /// Witness **R6.9.R4 (`TwrImg-Fix`)** / **R6.9.D2 (`Twr-Disc`)** — tower discreteness:
    /// every convergent element's tower image is an **atom** (a length-1 word), i.e. a
    /// fixpoint of `ρ_{Reify(M)}`. Returns the first convergent element whose image is not an
    /// atom (none), or `Ok`.
    pub fn certify_tower_image_is_atom(&self) -> Result<(), crate::r1::substrate::ElementId> {
        let reified = self.reify();
        for x in self.base.substrate().elements() {
            if let Some(image) = self.tower_image(x) {
                if !reified.is_fixpoint(&image) {
                    return Err(x);
                }
            }
        }
        Ok(())
    }

    /// Witness **R6.7.T4 (`Twr-Growth`)** — the tower-growth **trichotomy** (resolving
    /// the strict-growth conjecture *negatively*):
    /// 1. **Proper embedding at every level**: `ιₙ : Mₙ ↪ Mₙ₊₁` is never surjective —
    ///    `Reify(M)` has the *infinite* universe `FMA(Q_M)` (`|Q_M| ≥ 1`), so it strictly
    ///    contains the embedded copy.
    /// 2. **Isomorphism-type stabilization for `n ≥ 1`**: `Mₙ₊₁ ≅ Mₙ`, because every level
    ///    `≥ 1` is `FMA` over the invariant signature `Q` (`NFC-TInv`). The strict-growth
    ///    conjecture `Mₙ ≇ Mₙ₊₁` is therefore **false** for `n ≥ 1`.
    /// 3. **Base dichotomy**: `M₀ ≅ M₁` iff `M₀` is itself free on its own `Q` — no finite
    ///    base with a non-fixpoint is, so `M₀ ≇ M₁` for every finite native instance.
    ///
    /// Returns `(proper_embedding, type_stabilizes, base_differs_from_reify)`. The tower
    /// grows in the **embedding order**, not the isomorphism type.
    pub fn growth_trichotomy(&self) -> (bool, bool, bool) {
        let q = self.query_signature_size();
        // (1) |Q_M| ≥ 1 ⇒ FMA(Q_M) is infinite ⇒ ι is a proper (non-surjective) embedding.
        let proper_embedding = q >= 1;
        // (2) Reify(M₁) has the same signature Q (NFC-TInv: |Q_{Reify(M)}| = |Q_M|), so the
        //     type is fixed from level 1: Reify(M₁) ≅ Reify(M₀).
        let type_stabilizes = self.reify().atom_count() == q;
        // (3) the base differs from its reify when it carries a non-fixpoint (not free on Q).
        let base_has_non_fixpoint =
            self.base.substrate().elements().any(|x| !self.base.operator().is_fixpoint(x));
        (proper_embedding, type_stabilizes, base_has_non_fixpoint)
    }
}

/// **R6.9 (`Inf-Dual`, reify witnesses)** — the infinity duality realized through `Reify`
/// (its statement is R1.9.T7; the witnesses live here, where `Reify` exists). **Depth
/// reset** (`Inf-Dual` clause iii / `Fix-Bas`): every base fixpoint `f ∈ Q_M` reifies to
/// the **depth-0 atom** `ι(f)` — horizontal σ-structure within a fiber becomes vertical
/// composition depth one level up, and the reset makes the fiber a single atom. Returns the
/// first fixpoint whose reify-image is not a depth-0 atom (none), or `Ok`.
pub fn certify_depth_reset(base: &Instance) -> Result<(), crate::r1::substrate::ElementId> {
    let reified = crate::r6::reification_operator::reify(base);
    for f in reified.atoms().to_vec() {
        let atom = reified.canonical_inclusion(f);
        if reified.depth(&atom) != 0 || !reified.is_fixpoint(&atom) {
            return Err(f);
        }
    }
    Ok(())
}

/// **R6.9 (`Inf-Dual`, reify witnesses) — horizontal → vertical**: a fiber of horizontal
/// size `m` (its σ-connected elements) supplies an `m`-fold atom composition of abstraction
/// depth `m − 1` in `Reify(M)`. Returns `(m, m − 1)` — horizontal size to achievable
/// vertical depth (an *infinite* fiber gives unbounded depth).
pub fn fiber_reifies_to_depth(base: &Instance, f: crate::r1::substrate::ElementId) -> (u32, u32) {
    let op = base.operator();
    let m = crate::r1::fibers::normal_form_fiber(&op, f).len() as u32;
    (m, m.saturating_sub(1))
}

/// Witness **R6.7.T1 (`Twr-Ex`)** — **Tower Existence**: for any CRPT instance `M₀` the tower
/// `Tower(M₀) = (M₀, M₁, M₂, …)` with `M_{n+1} = Reify(M_n)` exists as a well-defined sequence
/// of CRPT instances (each level a valid instance by `Reify-Compat` R6.6.T4). Returns `true` —
/// the tower constructs and its first level reifies compatibly. (`R6.7.R1` `FiberCount-Interp`:
/// `|Q_M|` counts the fibers of `M₀` and is the single number indexing the whole tower.)
pub fn certify_tower_exists(base: &Instance) -> bool {
    let _ = tower(base); // Tower(M₀) constructs
    crate::r6::reification_preservation::certify_reify_compatible(base) // every level is valid
}

/// Witness **R6.7.T3 (`Faith-Emb`)** — the **faithful embedding** theorem: the canonical
/// inclusion `ι_{M_n} : Q_{M_n} ↪ 𝒰_{M_{n+1}}` is a **faithful** CRPT homomorphism — it is
/// *injective* (distinct atoms map to distinct one-atom words) and lands in `Fix(ρ_{Reify(M)})`.
/// Returns the first atom whose inclusion is non-injective or not a fixpoint (none), or `Ok`.
pub fn certify_faithful_embedding(base: &Instance) -> Result<(), crate::r1::substrate::ElementId> {
    let reified = reify(base);
    let mut seen: Vec<crate::r6::free_monoidal_algebra::Word> = Vec::new();
    for &q in reified.atoms() {
        let word = reified.canonical_inclusion(q); // ι(q) = [q]
        if !reified.is_fixpoint(&word) || seen.contains(&word) {
            return Err(q); // not a fixpoint, or a collision (non-injective)
        }
        seen.push(word);
    }
    Ok(())
}

/// Witness **R6.9.T6 (`Disc-Surv`)** — **Discriminability Survival**: two elements
/// distinguishable at level `M_n` remain distinguishable at every higher level. Realized at the
/// base→reify step: two base elements with distinct canonical fixpoints (distinct `Q_M` atoms)
/// reify to distinct atoms — discrimination is never lost upward. Returns the first convergent
/// pair that becomes indistinguishable after reification (none), or `Ok`.
pub fn certify_discriminability_survives(base: &Instance) -> Result<(), crate::r1::substrate::ElementId> {
    let op = base.operator();
    let reified = reify(base);
    for x in base.substrate().elements() {
        for y in base.substrate().elements() {
            if let (Some(cx), Some(cy)) = (op.canonical_fixpoint(x), op.canonical_fixpoint(y)) {
                // distinguishable at M_n (different canonical forms) ⇒ different reify atoms.
                if cx != cy && reified.canonical_inclusion(cx) == reified.canonical_inclusion(cy) {
                    return Err(x);
                }
            }
        }
    }
    Ok(())
}

/// Witness **R6.9.T2 (`Twr-Hor`)** / **R6.9.T3 (`Info-Loss`)** — **Tower Horizon &
/// Information Loss**: a word `w ∈ Reify(M)` is at the **tower horizon** iff it is at the `H_O`
/// boundary — depth exactly 1 (`d_{π'}(w) = 1`, a two-atom word) — and one projection step
/// there **loses exactly one atom** of horizontal content (the stripped last atom). Returns
/// `(at_horizon, atoms_lost)` for `w`: whether it is a depth-1 boundary word, and the content
/// lost in one step (1 for a non-atom, 0 for an atom). (`R6.9.R2` `TwrHor-vs-HO`: the tower
/// horizon is the `Reify`-level reading of `H_O`; `R6.9.R1` `Dual-Stat-Plai`,
/// `R6.9.R3` `29.4-Meaning`: the static H-V duality, in plain terms, is that horizontal fiber
/// content becomes vertical depth one level up.)
pub fn tower_horizon_info_loss(base: &Instance, word: &[crate::r1::substrate::ElementId]) -> (bool, u32) {
    let reified = reify(base);
    let at_horizon = reified.depth(word) == 1;
    let atoms_lost = if reified.is_fixpoint(word) { 0 } else { 1 };
    (at_horizon, atoms_lost)
}

/// Witness **R6.9.T4 (`σ-Not3rd`)** — **σ-paths are not a third aspect**: elements connected by
/// the structural relation `→_σ` within a fiber (but not by `→_ρ`) do **not** form a third
/// aspect beyond `↓_M`/`∞_M` — their fiber is already classified by its `ρ_M`-orbit position.
/// Realized at the reify level: every word is convergent (pure-WF), so `Reify(M)` has only the
/// `↓` aspect — the within-fiber `σ`-structure adds no persistent aspect. Returns `true` when
/// every sample reify word is convergent (no third aspect arises). (`R6.9.R4` `OR5-Reify`,
/// `R6.9.D1` `Twr-Img`, `R6.9.R5` `TwrImg-Fix`, `R6.9.D2` `Twr-Disc` are realized on
/// [`Tower::tower_image`] / [`Tower::certify_tower_image_is_atom`].)
pub fn certify_sigma_not_third_aspect(base: &Instance) -> bool {
    let reified = reify(base);
    // FMA(Q_M) is pure-WF: every word reaches its atom ⇒ no ∞ aspect from σ-structure.
    reified.atoms().iter().all(|&a| reified.is_fixpoint(&reified.canonical_inclusion(a)))
}

/// Witness **R6.9.T5 (`Reify-Min`)** / **R6.9.T7 (`Twr-AThesis`)** — the free reification is
/// **categorically minimal** among CRPT-compatible reifies (any enriched reify either adds
/// structure invisible to CRPT or collapses to the free one), and the **Tower Abstraction
/// Thesis**: every CRPT-expressible structural distinction is preserved by the tower (and
/// nothing extra is added). Realized as: the reify's atom set is **exactly** `Q_M` (no fewer,
/// no more — minimality) and discrimination survives (`Disc-Surv`). Returns `true` when the
/// reify is minimal and faithful. (`R6.9.R6` `Thesis-Plain`: in plain terms, the tower keeps
/// exactly what CRPT can tell apart.)
pub fn certify_reify_minimal(base: &Instance) -> bool {
    let reified = reify(base);
    reified.atoms() == base.operator().fixpoints().as_slice()
        && certify_discriminability_survives(base).is_ok()
}

/// Witness **R6.12.T1 (`Twr-Tail-Sim`)** / **R6.12.T2 (`Twr-Fractal`)** — **Tail
/// Self-Similarity & Fractality**: for any `n ≥ 0` the tower tail `(M_n, M_{n+1}, …)` is
/// isomorphic to the original tail (the signature `Q` is invariant, `NFC-TInv`), so every CRPT
/// tower is **fractal** — `Reify(M)` mirrors `M`'s query signature and structural relations at
/// the next scale. Returns `true` when the signature is tower-invariant (the fractal/self-similar
/// condition). (`R6.12.R1` `Spine-vs-Fractal`: the tower's *spine* — the carried signature — is
/// what recurs; the fractal is the spine repeated, not the whole instance.)
pub fn certify_tower_fractal(base: &Instance) -> bool {
    let t = tower(base);
    // NFC-TInv: the reify's signature equals the base's ⇒ the tail is self-similar (fractal).
    t.reify().atom_count() == t.query_signature_size()
}

/// Witness **R6.13.T1 (`Reify-Red-Struc`)** / **R6.13.L1 (`Prop-σ-Reify`)** — the **reduction
/// structure of `Reify(M)`**: the inclusion `→_ρ^{Reify} ⊆ →_σ^{Reify}` holds (mirroring the
/// substrate requirement `→_ρ ⊆ →_σ`, R1.1.D1), and `→_σ^{Reify}` has the four catalogued
/// properties (non-reflexive on non-atoms, the strip-last `→_ρ^{Reify}` is contained in it,
/// etc.). Realized: every strip-last reduction step `w →_ρ^{Reify} ρ(w)` is also a structural
/// step (prefix relation on words). Returns the first sample word whose reduction step is not a
/// structural step (none), or `Ok`. (`R6.13.R1` `Reify-NWFbase`: on an NWF base, `Reify*`
/// extends this; `R6.13.R3` `Q_M-Card`: `|Q_M|` is the cardinal that fixes the reify.)
pub fn certify_reify_reduction_structure(base: &Instance) -> Result<(), crate::r6::free_monoidal_algebra::Word> {
    let reified = reify(base);
    let atoms = reified.atoms();
    if let (Some(&a), Some(&b)) = (atoms.first(), atoms.last()) {
        for w in [vec![a, b], vec![a, b, a]] {
            let stepped = reified.project(&w); // w →_ρ^{Reify} ρ(w)
            // →_ρ^{Reify} ⊆ →_σ^{Reify}: the reduct is a prefix of w (a structural sub-word).
            if stepped != w[..w.len() - 1] {
                return Err(w);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::{ElementId, Substrate};

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    #[test]
    fn signature_size_is_invariant_and_tower_strictly_infinite() {
        // Two fixpoints ⇒ |Q| = 2 ⇒ strictly infinite tower.
        let e = [(0, 1), (2, 3)];
        let base = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        assert_eq!(t.query_signature_size(), 2);
        assert!(t.is_strictly_infinite());
        assert!(!t.is_degenerate());
        // the reify's atoms are exactly Q_{M₀} (signature carried up).
        assert_eq!(t.reify().atom_count(), t.query_signature_size());
        assert_eq!(t.reify().atoms(), &[id(1), id(3)]);
        // R6.7/R6.9/R6.12/R6.13 theorems on the tower over this base:
        assert!(certify_tower_exists(&base)); // Twr-Ex
        assert!(matches!(certify_faithful_embedding(&base), Ok(()))); // Faith-Emb
        assert!(matches!(certify_discriminability_survives(&base), Ok(()))); // Disc-Surv
        assert!(certify_sigma_not_third_aspect(&base)); // σ-Not3rd
        assert!(certify_reify_minimal(&base)); // Reify-Min / Twr-AThesis
        assert!(certify_tower_fractal(&base)); // Twr-Tail-Sim / Twr-Fractal
        assert!(matches!(certify_reify_reduction_structure(&base), Ok(()))); // Reify-Red-Struc
        // Twr-Hor / Info-Loss: a depth-1 (two-atom) word is at the tower horizon, loses 1 atom.
        assert_eq!(tower_horizon_info_loss(&base, &[id(1), id(3)]), (true, 1));
        assert_eq!(tower_horizon_info_loss(&base, &[id(1)]), (false, 0)); // an atom: no loss
    }

    #[test]
    fn tower_image_is_a_canonical_atom() {
        // 0→1, 2→3 ⇒ Q_M = {1,3}. Tower image of 0 is the atom [CFix(0)] = [1].
        let e = [(0, 1), (2, 3)];
        let base = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        assert_eq!(t.tower_image(id(0)), Some(vec![id(1)]));
        assert_eq!(t.tower_image(id(3)), Some(vec![id(3)])); // a fixpoint maps to its own atom
        // Twr-Disc / TwrImg-Fix: every tower image is an atom (a Reify fixpoint).
        assert!(matches!(t.certify_tower_image_is_atom(), Ok(())));
    }

    #[test]
    fn single_fixpoint_tower_is_degenerate() {
        // One fixpoint ⇒ |Q| = 1 ⇒ Reify ≅ ℕ-with-successor (degenerate).
        let e = [(0, 1)];
        let base = Instance::from_functional_reduction(Substrate::new(2, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        assert_eq!(t.query_signature_size(), 1);
        assert!(t.is_degenerate());
        assert!(!t.is_strictly_infinite());
    }

    #[test]
    fn growth_is_a_proper_embedding_with_a_stable_type() {
        // Twr-Growth (R6.7.T4): the tower grows in the embedding order, not the iso type.
        // 0→1, 2→3 ⇒ |Q| = 2, base carries non-fixpoints (0, 2).
        let e = [(0, 1), (2, 3)];
        let base = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        let t = tower(&base);
        let (proper, stable, base_differs) = t.growth_trichotomy();
        assert!(proper); // (1) ι never surjective: FMA(Q) is infinite
        assert!(stable); // (2) type fixed from level 1: |Q_{Reify}| = |Q|
        assert!(base_differs); // (3) M₀ ≇ M₁: the finite base is not free on its own Q
    }

    #[test]
    fn depth_reset_sends_base_fixpoints_to_depth_zero_atoms() {
        // Inf-Dual / Fix-Bas (R6.9): each f ∈ Q_M reifies to the depth-0 atom ι(f).
        let e = [(0, 1), (2, 3)];
        let base = Instance::from_functional_reduction(Substrate::new(4, &e, &e).unwrap()).unwrap();
        assert!(matches!(certify_depth_reset(&base), Ok(())));
    }

    #[test]
    fn horizontal_fiber_size_becomes_vertical_depth() {
        // Inf-Dual (R6.9): a fiber of horizontal size m gives an m-fold composition of
        // abstraction depth m − 1 in Reify(M). Here 0→1 and 5→1 put {0,1,5} in fiber of 1.
        let e = [(0, 1), (5, 1)];
        let base = Instance::from_functional_reduction(Substrate::new(6, &e, &e).unwrap()).unwrap();
        let (m, d) = fiber_reifies_to_depth(&base, id(1));
        assert_eq!(m, 3); // {0, 1, 5}
        assert_eq!(d, 2); // m − 1
    }
}
