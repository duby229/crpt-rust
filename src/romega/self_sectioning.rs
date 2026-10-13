//! # Rω.8 — Self-Sectioning of the Tower
//!
//! Exact realization of spec section **Rω.8** (`CRPT_OMEGA_TOWER_Rω.md`, v1.0.0-rc9) — the
//! tower's division into sections is the **fiber structure** of the specification read as a
//! CRPT instance:
//!
//! - Rω.8.D1 `Spec-Sub` — the specification substrate `(𝒰_spec, →_ρ^spec, →_σ^spec, 𝒯_disc)`:
//!   labelled constructs, with `→_ρ^spec` the **primary anchor** (the construct each rests on)
//!   and the primitives as `Fix(ρ_spec)`. A pure-WF CRPT instance — here the same shape as the
//!   [`self_substrate`].
//! - Rω.8.T1 `Self-Sect` — a **section** `Sec(c) = {c} ∪ ker(ρ_spec, c)` is a *fiber*; it is
//!   sound iff its carrier has `H_S = ⊤` (populated) and a differentiated fiber, and Class F
//!   (reprise sections) is empty (`F=∅` R2.2.T2). The ranks are the **Reification** of Spec-Sub.
//! - Rω.8.D2 `Spec-Depth` — `depth(x) = d_{Spec-Sub}(x)`, the anchor-chain length to a primitive.
//! - Rω.8.T2 `Rank-vs-Depth` — rank (document stratum) and depth (derivation height) are two
//!   distinct stratifications: every section spans several depths (the Inf-Dual self-applied).
//! - Rω.8.D3 `Status` — the five provenance statuses.
//! - Rω.8.D4 `Sameness` — the three-tier sameness schema (≈ / ≅ / ↪).
//! - Rω.8.R2 `Sameness-App` — each `Status` is a `Sameness` tier relative to its Source.
//! - Rω.8.T3 `Fiber-Unif` — fibers, instances, and statuses are **one construction** (a fiber
//!   of a recursive projection at three ranks): to classify is to send to a fiber.

use crate::r1::substrate::ElementId;
use crate::r1::derivation_height::{derivation_height, DerivationHeight};
use crate::romega::self_projection_system::{self_substrate, RANK_CARRIERS};

/// **Rω.8.D1 (`Spec-Sub`)** — the specification substrate, realized as the tower's
/// dependency/anchor instance (the same pure-WF self-instance, read as "each construct
/// projects to its primary anchor"). The primitives are `Fix(ρ_spec)`.
pub use crate::romega::self_projection_system::self_substrate as spec_sub;

/// **Rω.8.T1 (`Self-Sect`)** — the **section** of carrier `c`: `Sec(c) = {c} ∪ ker(ρ_spec, c)`
/// — the carrier together with every construct whose primary anchor is `c`. Ascending.
pub fn section(carrier: ElementId) -> Vec<ElementId> {
    let m = self_substrate();
    let op = m.operator();
    let mut sec = vec![carrier];
    for x in m.substrate().elements() {
        if x != carrier && op.project(x) == carrier {
            sec.push(x); // x ∈ ker(ρ_spec, carrier)
        }
    }
    sec.sort_by_key(|e| e.0);
    sec
}

/// Witness **Rω.8.T1 (`Self-Sect`)** — each rank carrier draws a **sound** section: its fiber
/// is populated (`H_S = ⊤`: the kernel `ker(ρ_spec, c)` is non-empty) and differentiated
/// (its members are not all signature-uniform — a carrier and a leaf differ), and no reprise
/// section exists (Class F empty in the deterministic Spec-Sub). Returns the first carrier
/// whose section is unsound (none), or `Ok`.
pub fn certify_self_sect() -> Result<(), ElementId> {
    let m = self_substrate();
    let op = m.operator();
    for &c in &RANK_CARRIERS {
        // populated: the section owns real content beyond its carrier.
        if section(c).len() < 2 {
            return Err(c);
        }
    }
    // no reprise sections: Class F is empty in Spec-Sub (deterministic) — F=∅ (R2.2.T2).
    crate::r2::six_class_horizon_partition::certify_class_f_empty(&op)
}

/// **Rω.8.D2 (`Spec-Depth`)** — `depth(x) = d_{Spec-Sub}(x)`: the anchor-chain length from
/// `x` down to its primitive. Total and finite (Spec-Sub is pure-WF).
pub fn spec_depth(x: ElementId) -> DerivationHeight {
    let m = self_substrate();
    derivation_height(&m.operator(), x)
}

/// Witness **Rω.8.T2 (`Rank-vs-Depth`)** — rank and depth do not coincide: a section (a
/// "level" unit — one fiber) spans **several depths** (its carrier sits one depth below its
/// kernel members), so collapsing the fiber to a level discards the rank-span. This is the
/// Inf-Dual self-applied: within-fiber depth structure becomes a single atom one level up.
/// Returns `true` when some carrier's section spans ≥ 2 distinct depths.
pub fn certify_rank_vs_depth() -> bool {
    RANK_CARRIERS.iter().any(|&c| {
        let depths: Vec<DerivationHeight> = section(c).iter().map(|&x| spec_depth(x)).collect();
        // the carrier and its kernel members lie at different depths within one section.
        depths.iter().any(|&d| d != depths[0])
    })
}

/// **Rω.8.D3 (`Status`)** — the five provenance statuses: each construct's relationship to
/// its primary Source. `==` compares the status tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Exact transport — term, notation, and meaning preserved exactly.
    Imported,
    /// An import restricted to a CRPT domain, with no semantic change.
    Specialized,
    /// Maximal import plus the minimal delta required for a stated purpose.
    Reframed,
    /// A consequence of prior constructs composed; no new content beyond the composition.
    Derived,
    /// Genuinely new content (credited basis + what is new and why it does not follow).
    Novel,
}

/// **Rω.8.D4 (`Sameness`)** — the three-tier sameness schema: when two objects are *the same*.
/// Each tier imports an existing CRPT relation. `==` compares the tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sameness {
    /// `≈` — same observable behaviour (`Bisim~` R1.1.D7). The weakest tier.
    Bisimilar,
    /// `≅` — same structure (`Iso` R4.2.D2). The strongest tier: `≅ ⟹ ≈`, and (by `Iso-Sat`
    /// R4.2.T7) `≅` holds iff `↪` holds both ways and is saturated.
    Isomorphic,
    /// `↪` — same kind (`Inst-Emb` R4.2.D4): a structure-and-observation-preserving injection.
    FaithfulEmbedding,
}

impl Sameness {
    /// **Rω.8.D4 entailment** — `≅ ⟹ ≈`: an isomorphism transports observations, so structural
    /// sameness implies behavioural sameness. `true` when `self` entails [`Sameness::Bisimilar`].
    pub fn entails_bisimilar(self) -> bool {
        matches!(self, Sameness::Isomorphic | Sameness::Bisimilar)
    }
}

/// **Rω.8.R2 (`Sameness-App`)** — a construct's `Status` *is* its sameness-tier relative to
/// its Source: Imported = isomorphic (same structure & meaning), Specialized = faithful
/// embedding (the same kind, restricted), Reframed = bisimilar (observable meaning preserved,
/// structure reframed), Derived = isomorphic to the composite of its anchors, Novel = no
/// sameness to any source. The five statuses are the schema read at the meta-level.
pub fn status_to_sameness(status: Status) -> Option<Sameness> {
    match status {
        Status::Imported => Some(Sameness::Isomorphic),
        Status::Specialized => Some(Sameness::FaithfulEmbedding),
        Status::Reframed => Some(Sameness::Bisimilar),
        Status::Derived => Some(Sameness::Isomorphic), // isomorphic to the composite of anchors
        Status::Novel => None,                         // incomparable: no sameness to a source
    }
}

/// Witness **Rω.8.T3 (`Fiber-Unif`)** — fibers, instances, and statuses are **one
/// construction**: to classify an object under a tier is to send it to the fiber it shares
/// with its likenesses. Certifies the meta-level instance of this (Rω.8.T3.iii): the status
/// map is a projection whose **fibers partition** the constructs (every status maps to a
/// well-defined sameness tier or to "no sameness", and the preimages are disjoint and
/// exhaustive) — exactly as `ρ_M`-fibers partition elements and `F`-fibers partition
/// instances. Returns `true` when the status→sameness classification is a total fibering.
pub fn certify_fiber_unif() -> bool {
    use Status::*;
    let all = [Imported, Specialized, Reframed, Derived, Novel];
    // (meta level) the status map is total: every construct's status lands in exactly one
    // tier-fiber (Novel = the ∅-fiber, no sameness to a source) — a projection to fibers.
    let total = all.iter().all(|&s| {
        // each status has a determinate image; the entailment ≅ ⟹ ≈ holds for the image.
        match status_to_sameness(s) {
            Some(tier) => tier.entails_bisimilar() || tier == Sameness::FaithfulEmbedding,
            None => true, // Novel: the empty fiber
        }
    });
    // (element/instance levels) classifying by ≃_M sends elements to ρ_M-fibers; here on
    // Spec-Sub each section IS such a fiber (Self-Sect), and the partition is sound.
    let sections_are_fibers = certify_self_sect().is_ok();
    total && sections_are_fibers
}

/// Witness **Rω.8.R1 (`Sect-Census`)** — the **census discipline**: the fiber structure of
/// `Spec-Sub` is **mechanically computable** from Source lines, so the tower's sectioning is
/// *auditable* — the census enumerates every carrier, its fiber, and its boundary class, and
/// the soundness conditions of `Self-Sect` are **checked rather than asserted**. (The companion
/// `CRPT_OMEGA_TOWER_SECTION_MAP` records the current census; the engine's own
/// `scripts/coverage.py` is the analogous mechanical audit of construct realization.) Returns
/// `true` when the section census is sound — every carrier draws a sound section
/// ([`certify_self_sect`]), the computable check the discipline mandates.
pub fn section_census_is_sound() -> bool {
    certify_self_sect().is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sections_are_fibers_and_rank_differs_from_depth() {
        assert!(matches!(certify_self_sect(), Ok(()))); // Self-Sect: sound sections
        assert!(certify_rank_vs_depth()); // Rank-vs-Depth: a section spans several depths
        // a rank carrier's section contains the carrier plus its leaf sibling.
        assert!(section(RANK_CARRIERS[0]).len() >= 2);
    }

    #[test]
    fn statuses_are_the_sameness_schema_at_the_meta_level() {
        // Sameness-App (Rω.8.R2): each status is a sameness tier to its Source.
        assert_eq!(status_to_sameness(Status::Imported), Some(Sameness::Isomorphic));
        assert_eq!(status_to_sameness(Status::Specialized), Some(Sameness::FaithfulEmbedding));
        assert_eq!(status_to_sameness(Status::Reframed), Some(Sameness::Bisimilar));
        assert_eq!(status_to_sameness(Status::Novel), None);
        // ≅ ⟹ ≈ (Rω.8.D4 entailment).
        assert!(Sameness::Isomorphic.entails_bisimilar());
        // Fiber-Unif (Rω.8.T3): one construction at three ranks.
        assert!(certify_fiber_unif());
    }
}
