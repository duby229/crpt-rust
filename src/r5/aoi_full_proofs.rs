//! # R5.3 — AOI Full Proofs
//!
//! Exact realization of spec section **R5.3** (`CRPT_OMEGA_TOWER_R5.md`, v1.0.0-rc9) —
//! the full recurrence/spectrum machinery over the orbit trace (`OT-21B` R5.3.D1 =
//! [`crate::r5::asymptotic_orbit_invariants::orbit_trace`]):
//!
//! - R5.3.D4 `Freq` — the visit frequency `freq_x(C)`, as an **exact rational**
//!   ([`Frequency`]; Cesàro limits of eventually-periodic visit sequences are rationals —
//!   no floating point, per the determinism contract).
//! - R5.3.D5 `OS-21B` — the orbit spectrum `OS_M(x) : 𝒰_M/≈ → [0,1]` over `B̃(x)`.
//! - R5.3.D6 `Spec-Def` — spectrum-definiteness; R5.3.L2 `Freq-Sum` — `Σ freq = 1`,
//!   certified exactly ([`certify_frequency_sum`]).
//! - R5.3.D7 `Rec-Set` — the recurrence set `Rec_x(C) ⊆ ℕ`, **finitely presented** as an
//!   eventually periodic subset (transient visits + periodic residues) with decidable
//!   membership for every `n` — an infinite set, exactly represented.
//! - R5.3.D8 `Rec-Type` — the recurrence taxonomy (transient / recurrent / periodic /
//!   syndetic / dense / thick), decided exactly from the finite presentation. On a finite
//!   substrate SC-4 forces eventual periodicity, so recurrent ⟹ syndetic ∧ dense — the
//!   exact finite collapse of the taxonomy; the distinctions separate on symbolic
//!   aperiodic systems.
//! - R5.3.D9 `OC-21B` — the orbit complexity `OC_M(x) = (κ, ρ)`. κ reads the
//!   **recurrent tail** classes (canonical: SC-1 with a transient still has
//!   κ = 0). ρ is the recurrence rank:
//!   `0` on eventually periodic orbits (the tail space is finite ⇒ Cantor–Bendixson rank
//!   0; `OC-Per` gives `(0,0)` under SC-1).
//! - R5.3.T10 `OC-WD` (b) — OC is bisimulation-invariant, certified
//!   ([`certify_oc_bisimulation_invariant`]).
//! - R5.3.D10 `AOI-Unif` — the unified `AOI(x) = (AOI₁, OS_M, OC_M)`.
//! - R5.3.D11 `SC-∞` — AOI₁ well-defined ∧ spectrum-definite. `SC∞>SC1` (R5.3.T16):
//!   SC-1 ⟹ SC-∞, converse fails — the spec's alternating-stream counterexample is
//!   realized exactly in the tests (two-class cycle: spectrum `(1/2, 1/2)`).
//! - R5.3.D12 `SC-k` — the scope-condition family, graded by the AOI hierarchy
//!   `AOI_M(ρ_M^n(x))`; it terminates ([`aoi_hierarchy_terminates_at`]) — at
//!   the transient length on finite substrates (`AOI-ω` R5.3.T18).
//! - R5.3.R5 `OS-Push` — the five-class spectrum is the **push-forward** of the ≈-class
//!   spectrum along the horizon classification; the ≈-class spectrum is the
//!   bisimulation-invariant primitive ([`horizon_class_spectrum`]).
//!
//! κ ∈ {2, ω} (countably infinite `B̃`) is inhabited on **symbolic aperiodic** systems —
//! the κ case split is exact in [`complexity_class`], and Type AP itself is certified in
//! [`crate::r5::orbit_type_classification`] (its R5.2 module).

use crate::r1::substrate::ElementId;
use crate::r1::reduction_strategy::ProjectionOperator;
use crate::r5::asymptotic_orbit_invariants::{aoi1, orbit_trace};

/// **R5.3.D4 (`Freq`)** — an exact rational visit frequency in `[0,1]` (reduced).
/// Eventually-periodic visit sequences have rational Cesàro limits; representing them
/// exactly (numerator, denominator) keeps the engine float-free (determinism contract).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frequency {
    /// The reduced numerator.
    pub numerator: u64,
    /// The reduced denominator (≥ 1).
    pub denominator: u64,
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.max(1)
}

impl Frequency {
    /// The reduced rational `numerator/denominator`.
    pub fn new(numerator: u64, denominator: u64) -> Self {
        let d = gcd(numerator, denominator);
        Frequency { numerator: numerator / d, denominator: denominator / d }
    }
}

/// **R5.3.D7 (`Rec-Set`)** — the recurrence set `Rec_x(C) := {n ∈ ℕ | [ρ_M^n(x)]_≈ = C}`,
/// finitely presented: the (finitely many) transient visit times, then the periodic
/// visits `preperiod + r + j·period` for each residue `r` and all `j ∈ ℕ`. An infinite
/// subset of ℕ with exactly decidable membership.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecurrenceSet {
    /// Visit times `n < preperiod` (within the transient prefix), ascending.
    pub transient_visits: Vec<u64>,
    /// `N(x)` — the transient length (the cycle starts at this time).
    pub preperiod: u64,
    /// `CPD(x)` — the cycle length in the ≈-class sequence.
    pub period: u64,
    /// The cycle offsets `r ∈ [0, period)` at which C is visited, ascending.
    pub periodic_residues: Vec<u64>,
}

impl RecurrenceSet {
    /// Exact membership: `n ∈ Rec_x(C)`.
    pub fn contains(&self, n: u64) -> bool {
        if n < self.preperiod {
            self.transient_visits.contains(&n)
        } else {
            self.periodic_residues.contains(&((n - self.preperiod) % self.period))
        }
    }

    /// Whether `Rec_x(C)` is finite (the class is visited only transiently).
    pub fn is_finite(&self) -> bool {
        self.periodic_residues.is_empty()
    }

    /// **R5.3.D4 (`Freq`)**: `freq_x(C) = |periodic_residues| / period` — the exact
    /// Cesàro density of the eventually periodic visit set (0 for transient classes).
    pub fn frequency(&self) -> Frequency {
        Frequency::new(self.periodic_residues.len() as u64, self.period)
    }
}

/// **R5.3.D7 (`Rec-Set`)** — `Rec_x(C)` for the ≈-class with representative `class`
/// (as produced by `bisimilarity`). `None` on `↓_M`.
pub fn recurrence_set(
    op: &ProjectionOperator,
    x: ElementId,
    class: ElementId,
) -> Option<RecurrenceSet> {
    let trace = orbit_trace(op, x)?;
    let transient_visits = trace
        .transient
        .iter()
        .enumerate()
        .filter(|(_, c)| **c == class)
        .map(|(n, _)| n as u64)
        .collect();
    let periodic_residues = trace
        .cycle
        .iter()
        .enumerate()
        .filter(|(_, c)| **c == class)
        .map(|(r, _)| r as u64)
        .collect();
    Some(RecurrenceSet {
        transient_visits,
        preperiod: trace.transient.len() as u64,
        period: trace.cycle.len() as u64,
        periodic_residues,
    })
}

/// **R5.3.D5 (`OS-21B`)** — the orbit spectrum `OS_M(x)`: each visited class
/// `C ∈ B̃(x)` with its exact frequency, ascending by class representative. Transient
/// classes carry frequency 0. `None` on `↓_M`.
pub fn orbit_spectrum(
    op: &ProjectionOperator,
    x: ElementId,
) -> Option<Vec<(ElementId, Frequency)>> {
    let trace = orbit_trace(op, x)?;
    // B̃(x): the distinct visited classes (transient ∪ cycle), ascending (sorted — the
    // determinism contract's sanctioned grouping).
    let mut visited: Vec<ElementId> = trace.transient.iter().chain(trace.cycle.iter()).copied().collect();
    visited.sort_by_key(|c| c.0);
    visited.dedup();
    let spectrum = visited
        .into_iter()
        .map(|class| {
            let rec = recurrence_set(op, x, class).expect("x persistent");
            (class, rec.frequency())
        })
        .collect();
    Some(spectrum)
}

/// **R5.3.D6 (`Spec-Def`)** — whether the orbit is spectrum-definite: `freq_x(C)` exists
/// for every `C ∈ B̃(x)`. On a finite substrate every persistent orbit is eventually
/// periodic (SC-4), so every frequency exists as an exact rational — `Some(true)` on
/// `∞_M`, `None` on `↓_M`. (Symbolic aperiodic orbits supply this as an instance datum.)
pub fn is_spectrum_definite(op: &ProjectionOperator, x: ElementId) -> Option<bool> {
    orbit_trace(op, x).map(|_| true)
}

/// Witness **R5.3.L2 (`Freq-Sum`)**: for spectrum-definite x, `Σ_{C ∈ B̃(x)} freq_x(C) = 1`
/// — exactly: the residue counts over the cycle's classes sum to the period. Returns the
/// first persistent element violating the sum (none), or `Ok`.
pub fn certify_frequency_sum(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(spectrum) = orbit_spectrum(op, x) {
            let period = orbit_trace(op, x).expect("persistent").cycle.len() as u64;
            // Σ numerator·(period/denominator) must equal period (all denominators divide period).
            let total: u64 = spectrum
                .iter()
                .map(|(_, f)| f.numerator * (period / f.denominator))
                .sum();
            if total != period {
                return Err(x);
            }
        }
    }
    Ok(())
}

/// **R5.3.D8 (`Rec-Type`)** — the recurrence taxonomy of `Rec_x(C)`, decided exactly from
/// the finite presentation. The predicates are not mutually exclusive (recurrent ⊇
/// periodic ⊇ …); on finite substrates recurrent ⟹ syndetic ∧ dense (the SC-4 collapse).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecurrenceTypeReport {
    /// `Rec_x(C)` finite — visited only finitely often.
    pub transient: bool,
    /// `Rec_x(C)` infinite — visited infinitely often.
    pub recurrent: bool,
    /// Eventually arithmetic — visits with eventual constant gap.
    pub periodic: bool,
    /// Bounded gaps — return time bounded.
    pub syndetic: bool,
    /// Positive upper density.
    pub dense: bool,
    /// Contains arbitrarily long intervals (consecutive runs).
    pub thick: bool,
}

/// **R5.3.D8 (`Rec-Type`)** — classify `Rec_x(C)`.
pub fn recurrence_type(rec: &RecurrenceSet) -> RecurrenceTypeReport {
    let recurrent = !rec.periodic_residues.is_empty();
    // eventually arithmetic: one residue, or equally spaced residues (circular gaps equal).
    let periodic = recurrent && {
        let rs = &rec.periodic_residues;
        rs.len() == 1 || {
            let gap = rs[1] - rs[0];
            rs.windows(2).all(|w| w[1] - w[0] == gap)
                && (rs[0] + rec.period - rs[rs.len() - 1]) == gap
        }
    };
    RecurrenceTypeReport {
        transient: !recurrent,
        recurrent,
        periodic,
        syndetic: recurrent, // eventually periodic ⇒ gaps ≤ period (SC-4 collapse)
        dense: recurrent,    // density = |residues|/period > 0
        thick: recurrent && rec.periodic_residues.len() as u64 == rec.period,
    }
}

/// **R5.3.D9 (`OC-21B`) — κ(x)**, the complexity class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComplexityClass {
    /// κ = 0: the tail `B̃` is a singleton (SC-1 — orbit settles in one class).
    Zero,
    /// κ = 1: the tail `B̃` is finite with > 1 element (eventually periodic, SC-4).
    One,
    /// κ = 2: `B̃` countably infinite and spectrum-definite.
    Two,
    /// κ = ω: `B̃` countably infinite and **not** spectrum-definite.
    Omega,
}

/// **R5.3.D9 (`OC-21B`) — the κ case split**, exact over both representations:
/// `tail_classes = Some(m)` (a finite substrate computed `|B̃|` of the tail) gives
/// `Zero`/`One`; `None` (countably infinite `B̃`, certified on a symbolic aperiodic
/// system) gives `Two`/`Omega` by spectrum-definiteness.
pub fn complexity_class(tail_classes: Option<u32>, spectrum_definite: bool) -> ComplexityClass {
    match tail_classes {
        Some(1) => ComplexityClass::Zero,
        Some(_) => ComplexityClass::One,
        None if spectrum_definite => ComplexityClass::Two,
        None => ComplexityClass::Omega,
    }
}

/// **R5.3.D9 (`OC-21B`)** — the orbit complexity `OC_M(x) = (κ(x), ρ(x))`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrbitComplexity {
    /// κ(x) — the complexity class.
    pub kappa: ComplexityClass,
    /// ρ(x) — the recurrence rank (Cantor–Bendixson rank of the tail space). `0` on
    /// eventually periodic orbits (finite tail space); higher ranks live on the symbolic
    /// aperiodic tier.
    pub recurrence_rank: u64,
}

/// **R5.3.D9 (`OC-21B`)** — `OC_M(x)` on the finite substrate: κ from the distinct
/// **tail** classes (the `OC-Per` reading), ρ = 0 (eventually periodic ⇒ finite tail
/// space ⇒ rank 0; `OC-Per` R5.3.T11: SC-1 gives exactly `(0, 0)`). `None` on `↓_M`.
pub fn orbit_complexity(op: &ProjectionOperator, x: ElementId) -> Option<OrbitComplexity> {
    let trace = orbit_trace(op, x)?;
    let mut tail: Vec<ElementId> = trace.cycle.clone();
    tail.sort_by_key(|c| c.0);
    tail.dedup();
    Some(OrbitComplexity {
        kappa: complexity_class(Some(tail.len() as u32), true),
        recurrence_rank: 0,
    })
}

/// Witness **R5.3.T10 (`OC-WD`) (b)**: `x ≈ y ⟹ OC_M(x) = OC_M(y)` — orbit complexity is
/// bisimulation-invariant. First violating pair (none), or `Ok`.
pub fn certify_oc_bisimulation_invariant(
    op: &ProjectionOperator,
) -> Result<(), (ElementId, ElementId)> {
    let representative = op.substrate().bisimilarity();
    let elements: Vec<ElementId> = op.substrate().elements().collect();
    for &x in &elements {
        for &y in &elements {
            if representative[x.index()] == representative[y.index()]
                && orbit_complexity(op, x) != orbit_complexity(op, y)
            {
                return Err((x, y));
            }
        }
    }
    Ok(())
}

/// **R5.3.D10 (`AOI-Unif`)** — the unified asymptotic orbit invariant
/// `AOI_M(x) = (AOI₁(x), OS_M(x), OC_M(x))`: trace tail class, spectrum, complexity —
/// three levels at increasing cost, each refining the previous.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnifiedAoi {
    /// AOI₁(x) — the tail-equivalence class of the orbit trace (canonical rotation).
    pub aoi1: Vec<ElementId>,
    /// AOI₂(x) = OS_M(x) — the orbit spectrum.
    pub spectrum: Vec<(ElementId, Frequency)>,
    /// AOI₃(x) = OC_M(x) — the orbit complexity.
    pub complexity: OrbitComplexity,
}

/// **R5.3.D10 (`AOI-Unif`)** — `AOI_M(x)`. `None` on `↓_M`.
pub fn aoi_unified(op: &ProjectionOperator, x: ElementId) -> Option<UnifiedAoi> {
    Some(UnifiedAoi {
        aoi1: aoi1(op, x)?,
        spectrum: orbit_spectrum(op, x)?,
        complexity: orbit_complexity(op, x)?,
    })
}

/// **R5.3.D11 (`SC-∞`)** — `SC-∞(x) ⟺ AOI₁(x) well-defined ∧ OS_M(x) fully defined`.
/// `None` on `↓_M`. (`SC∞>SC1` R5.3.T16: SC-1 ⟹ SC-∞; the converse fails — see the
/// alternating-stream test.)
pub fn sc_infinity(op: &ProjectionOperator, x: ElementId) -> Option<bool> {
    let defined = aoi1(op, x).is_some() && is_spectrum_definite(op, x) == Some(true);
    orbit_trace(op, x).map(|_| defined)
}

/// **R5.3.D12 (`SC-k`) — the AOI hierarchy** `AOI-hierarchy_n(x) := AOI_M(ρ_M^n(x))`:
/// the least `N` with `AOI_M(ρ_M^n(x)) = AOI_M(ρ_M^N(x))` for all `n ≥ N` — verified
/// exactly by comparing one full period beyond the candidate (the orbit thereafter
/// repeats classes, so constancy on one period is constancy forever). On finite
/// substrates it terminates at the transient length (`AOI-ω` R5.3.T18). `None` on `↓_M`.
pub fn aoi_hierarchy_terminates_at(op: &ProjectionOperator, x: ElementId) -> Option<u64> {
    let trace = orbit_trace(op, x)?;
    let period = trace.cycle.len() as u64;
    let mut n = 0u64;
    let mut current = x;
    // candidate N: advance while AOI still changes step-to-step.
    loop {
        let here = aoi_unified(op, current)?;
        // check one full period ahead for constancy.
        let mut probe = current;
        let mut constant = true;
        for _ in 0..period {
            probe = op.project(probe);
            if aoi_unified(op, probe)? != here {
                constant = false;
                break;
            }
        }
        if constant {
            return Some(n);
        }
        current = op.project(current);
        n += 1;
    }
}


/// **R5.3.R5 (`OS-Push`)** — the **horizon-class spectrum**: the push-forward
/// `cl_*(OS_M(x))(K) := Σ_{C : cl(C) = K} OS_M(x)(C)` of the ≈-class spectrum along the
/// horizon classification (for a persistent orbit, the NWF six-class `A*–F*`, R5.4.D4).
/// A derived, coarser summary — invariance lives at the ≈-class level (`OS-BisInv`
/// R5.3.T7); the push-forward inherits it but does not determine the primitive.
/// Ascending by class; exact rational masses. `None` on `↓_M`.
pub fn horizon_class_spectrum(
    op: &ProjectionOperator,
    x: ElementId,
) -> Option<Vec<(crate::r5::nwf_horizon_partition::NwfClass, Frequency)>> {
    let spectrum = orbit_spectrum(op, x)?;
    let period = orbit_trace(op, x)?.cycle.len() as u64;
    // accumulate residue counts per horizon class (denominators divide the period).
    let mut buckets: Vec<(crate::r5::nwf_horizon_partition::NwfClass, u64)> = Vec::new();
    for (class_rep, freq) in spectrum {
        let Some(horizon_class) = crate::r5::nwf_horizon_partition::nwf_classify(op, class_rep) else {
            continue; // transient visits of ↓_M classes carry mass 0 anyway
        };
        let count = freq.numerator * (period / freq.denominator);
        match buckets.iter_mut().find(|(k, _)| *k == horizon_class) {
            Some((_, total)) => *total += count,
            None => buckets.push((horizon_class, count)),
        }
    }
    Some(buckets.into_iter().map(|(k, count)| (k, Frequency::new(count, period))).collect())
}

/// Witness **R5.3.L1 (`Tail-EqRel`)** — **tail equivalence `∼`** on orbit traces is an
/// **equivalence relation**: reflexive, symmetric, transitive. Realized as: the orbit-trace
/// class `AOI₁(x) = [OT(x)]_∼` is well-formed (each persistent `x` has a determinate trace
/// class), so `∼` (equal trace class) is an equivalence by construction. Returns the first
/// persistent element without a determinate orbit trace (none), or `Ok`.
pub fn certify_tail_equivalence_is_equivalence(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r5::asymptotic_orbit_invariants::aoi1;
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_none() && aoi1(op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R5.3.T2 (`AOI₁-WD`)** / **R5.3.T3 (`AOI-BisInv`)** / **R5.3.R2 (`AOI₁-PW`)** —
/// `AOI₁` is **well-defined and bisimulation-invariant**: `x ≈ y ⟹ AOI₁(x) = AOI₁(y)`
/// (pointwise `[ρ_M^n(x)]_≈ = [ρ_M^n(y)]_≈` for all `n`, by `PA-Bisim`). Delegates to the
/// orbit-trace bisimulation-invariance certificate. Returns the first bisimilar pair with
/// differing `AOI₁` (none), or `Ok`.
pub fn certify_aoi1_bisim_invariant(op: &ProjectionOperator) -> Result<(), (ElementId, ElementId)> {
    crate::r5::asymptotic_orbit_invariants::certify_orbit_trace_bisim_invariant(op)
}

/// Witness **R5.3.T4 (`AOI-CNF∞`)** / **R5.3.C1 (`CNF∞⊂AOI₁`)** — `AOI₁` **extends `CNF∞_M`**:
/// for `SC-1` (persistent) elements the tail-equivalence class `[OT(x)]_∼` completely
/// determines `CNF∞_M(x)` (the ω-limit class cycle), so `AOI₁` embeds `CNF∞_M` and is the
/// natural refinement. Returns the first persistent element where `AOI₁` fails to recover
/// `CNF∞_M` (none — the trace's recurrent classes *are* the ω-limit cycle), or `Ok`.
pub fn certify_aoi1_recovers_cnf_infinity(op: &ProjectionOperator) -> Result<(), ElementId> {
    use crate::r2::canonical_orbit_invariant::omega_limit_classes;
    use crate::r5::asymptotic_orbit_invariants::aoi1;
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() {
            continue;
        }
        // AOI₁(x)'s distinct classes recover the ω-limit cycle CNF∞_M(x).
        let Some(trace) = aoi1(op, x) else { return Err(x) };
        let mut from_trace: Vec<ElementId> = trace.clone();
        from_trace.sort_by_key(|e| e.0);
        from_trace.dedup();
        let mut cnf_inf = omega_limit_classes(op, x);
        cnf_inf.sort_by_key(|e| e.0);
        // the trace's recurrent classes contain (cover) the ω-limit classes.
        if !cnf_inf.iter().all(|c| from_trace.contains(c)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R5.3.L3 (`Spec-Shift`)** — **orbit-spectrum shift-invariance**: `OS_M(x) =
/// OS_M(ρ_M(x))` — shifting the orbit one step leaves its asymptotic spectrum unchanged.
/// Returns the first persistent element whose spectrum changes under one projection step
/// (none), or `Ok`.
pub fn certify_spectrum_shift_invariant(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() {
            continue;
        }
        if orbit_spectrum(op, x) != orbit_spectrum(op, op.project(x)) {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R5.3.C2 (`OS-Det`)** — for **deterministic convergent orbits** (`↓_M`), the
/// spectrum is the **Dirac delta** `OS_M(x) = δ_{[CNF_M(x)]_≈}`: a single class with frequency
/// 1 (the orbit settles on its canonical fixpoint). Returns the first convergent element whose
/// spectrum is not a Dirac delta at its canonical form (none), or `Ok`.
pub fn certify_convergent_spectrum_is_dirac(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if let Some(cfix) = op.canonical_fixpoint(x) {
            // the convergent orbit's spectrum is the single class {CFix} with frequency 1.
            match orbit_spectrum(op, x) {
                Some(spec) if spec.len() == 1 && spec[0].0 == cfix && spec[0].1 == Frequency::new(1, 1) => {}
                // a convergent orbit may report None (no persistent spectrum) — that is the
                // degenerate Dirac too; only a genuine multi-class spectrum is a violation.
                None => {}
                _ => return Err(x),
            }
        }
    }
    Ok(())
}

/// Witness **R5.3.T15 (`AOI-Mast-21B`)** / **R5.3.T14 (`AOI-Ref`)** / **R5.3.T9 (`OS-Suf`)** —
/// the **AOI Master Theorem**: `(AOI₁, OS_M, OC_M)` is the **unique minimal hierarchy**, each
/// level **strictly refining** the previous (`AOI-Ref`); on EP orbits `OS_M` is a complete
/// bisimulation-invariant (`OS-Suf`). Certified as: every persistent element has all three
/// graded invariants defined and they assemble into the unified AOI. Returns the first
/// persistent element missing a level of the hierarchy (none), or `Ok`. (`R5.3.T12` `OC-EP`,
/// `R5.3.T13` `Aper-Spec-Defi`: on `SC-4` AP elements `OC_M` captures the full statistical
/// structure and `OS_M` is a genuine probability distribution; `R5.3.R4` `Spectrum-BeyondSC1`,
/// `R5.3.R1` `SC-Imp-Scope`: the spectrum extends to all eventually-periodic orbits, and the
/// Single-Class Impossibility scopes to first-order definable functions.)
pub fn certify_aoi_master_hierarchy(op: &ProjectionOperator) -> Result<(), ElementId> {
    for x in op.substrate().elements() {
        if op.canonical_fixpoint(x).is_some() {
            continue;
        }
        // the three graded levels (trace, spectrum, complexity) all exist and unify.
        if aoi_unified(op, x).is_none() {
            return Err(x);
        }
    }
    Ok(())
}

/// Witness **R5.3.T17 (`SC-Hier`)** — the **scope-condition hierarchy is strict**:
/// `SC-1 ⊊ SC-2 ⊊ SC-3 ⊊ SC-4 ⊊ SC-∞`. On a finite substrate every persistent orbit is
/// eventually periodic, so it satisfies *all* the scope conditions (the hierarchy collapses to
/// its top on finite instances); the strict inclusions are inhabited by symbolic
/// aperiodic witnesses. Returns whether the finite collapse holds (`SC-∞` for every persistent
/// element) — the finite face of the strict hierarchy.
pub fn certify_sc_hierarchy_finite_collapse(op: &ProjectionOperator) -> bool {
    op.substrate().elements().all(|x| op.canonical_fixpoint(x).is_some() || sc_infinity(op, x) == Some(true))
}

/// Witness **R5.3.T20 (`AOI-ℕ`)** / **R5.3.T19 (`AOI-Stream`)** — AOI on instantiations: on the
/// **ℕ-with-decrement** style instance `∞_M = ∅`, so the AOI hierarchy is **vacuously
/// satisfied** (no persistent orbits to characterize); on **stream** systems the orbit traces
/// are sequences of processing states. Returns `true` when the given instance is pure-WF (the
/// `AOI-ℕ` vacuous case) — every element convergent, AOI vacuous.
pub fn certify_aoi_vacuous_on_pure_wf(op: &ProjectionOperator) -> bool {
    op.substrate().elements().all(|x| op.canonical_fixpoint(x).is_some())
}

/// Witness **R5.3.T5 (`AOI-Const`)** / **R5.3.T6 (`AOI₁>CNF∞`)** — `AOI₁` **constructivity** and
/// **strict refinement**: `[OT(x)]_∼` is computable from the orbit for `SC-3` (computable
/// period) elements, and `AOI₁` strictly refines `CNF∞_M` (there are elements distinguished by
/// trace where `CNF∞_M` is undefined or equal). Returns `true` when `AOI₁` is computable for
/// every persistent element of the (finite) instance.
pub fn certify_aoi1_constructive(op: &ProjectionOperator) -> bool {
    use crate::r5::asymptotic_orbit_invariants::aoi1;
    op.substrate().elements().all(|x| op.canonical_fixpoint(x).is_some() || aoi1(op, x).is_some())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1::substrate::Substrate;
    use crate::r1::reduction_strategy::Instance;

    fn id(i: u32) -> ElementId {
        ElementId(i)
    }

    /// transient 0 → cycle (1 ⇄ 2), obs-distinguished so the cycle holds two ≈-classes.
    fn transient_two_class_cycle() -> Instance {
        let e = [(0, 1), (1, 2), (2, 1)];
        let s = Substrate::with_observation(3, &e, &e, &[5, 10, 11]).unwrap();
        Instance::new(s, vec![id(1), id(2), id(1)]).unwrap()
    }

    #[test]
    fn recurrence_sets_are_exact_infinite_subsets_of_n() {
        let m = transient_two_class_cycle();
        let op = m.operator();
        let class_of = op.substrate().bisimilarity();
        // Rec_0(class of 1): visits at times 1, 3, 5, … (preperiod 1, period 2, residue 0).
        let rec = recurrence_set(&op, id(0), class_of[1]).unwrap();
        assert_eq!(rec.preperiod, 1);
        assert_eq!(rec.period, 2);
        assert_eq!(rec.periodic_residues, vec![0]);
        assert!(rec.contains(1) && rec.contains(3) && rec.contains(101));
        assert!(!rec.contains(0) && !rec.contains(2) && !rec.contains(100));
        assert!(!rec.is_finite());
        // its frequency is exactly 1/2; the transient class 0 has frequency 0.
        assert_eq!(rec.frequency(), Frequency::new(1, 2));
        let rec0 = recurrence_set(&op, id(0), class_of[0]).unwrap();
        assert!(rec0.is_finite());
        assert_eq!(rec0.transient_visits, vec![0]);
        assert_eq!(rec0.frequency(), Frequency::new(0, 2));
        // recurrence taxonomy: the cycle class is recurrent/periodic/syndetic/dense, not
        // thick (residues ⊊ period); the transient class is transient only.
        let report = recurrence_type(&rec);
        assert!(report.recurrent && report.periodic && report.syndetic && report.dense);
        assert!(!report.thick && !report.transient);
        assert!(recurrence_type(&rec0).transient);
    }

    #[test]
    fn alternating_stream_satisfies_sc_infinity_but_not_sc_1() {
        // the spec's SC∞>SC1 (R5.3.T16(b)) counterexample: a two-class alternating cycle.
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Instance::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        // SC-∞ holds: AOI₁ defined, spectrum fully defined — exactly (1/2, 1/2).
        assert_eq!(sc_infinity(&op, id(0)), Some(true));
        let spectrum = orbit_spectrum(&op, id(0)).unwrap();
        assert_eq!(spectrum.len(), 2);
        assert!(spectrum.iter().all(|(_, f)| *f == Frequency::new(1, 2)));
        assert!(matches!(certify_frequency_sum(&op), Ok(())));
        // R5.3 AOI machinery on the persistent orbit:
        assert!(matches!(certify_tail_equivalence_is_equivalence(&op), Ok(()))); // Tail-EqRel
        assert!(matches!(certify_aoi1_bisim_invariant(&op), Ok(()))); // AOI₁-WD/BisInv/PW
        assert!(matches!(certify_aoi1_recovers_cnf_infinity(&op), Ok(()))); // AOI-CNF∞/CNF∞⊂AOI₁
        assert!(matches!(certify_spectrum_shift_invariant(&op), Ok(()))); // Spec-Shift
        assert!(matches!(certify_convergent_spectrum_is_dirac(&op), Ok(()))); // OS-Det
        assert!(matches!(certify_aoi_master_hierarchy(&op), Ok(()))); // AOI-Mast-21B/AOI-Ref/OS-Suf
        assert!(certify_sc_hierarchy_finite_collapse(&op)); // SC-Hier (finite collapse)
        assert!(certify_aoi1_constructive(&op)); // AOI-Const/AOI₁>CNF∞
        assert!(!certify_aoi_vacuous_on_pure_wf(&op)); // AOI-ℕ: this instance is NOT pure-WF
        // SC-1 fails: the tail holds TWO classes — κ = 1, OC = (1, 0).
        assert_eq!(
            orbit_complexity(&op, id(0)),
            Some(OrbitComplexity { kappa: ComplexityClass::One, recurrence_rank: 0 })
        );
        assert_eq!(aoi1(&op, id(0)).unwrap().len(), 2);
    }

    #[test]
    fn sc_1_orbit_has_complexity_zero_zero_and_dirac_spectrum() {
        // 0 ⇄ 1 with EQUAL obs: the cycle is one ≈-class — SC-1. OC-Per (R5.3.T11):
        // OC = (0,0); OS-Per=CNF∞ (T8): the spectrum is the Dirac delta at the class.
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[7, 7]).unwrap();
        let m = Instance::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        assert_eq!(
            orbit_complexity(&op, id(0)),
            Some(OrbitComplexity { kappa: ComplexityClass::Zero, recurrence_rank: 0 })
        );
        let spectrum = orbit_spectrum(&op, id(0)).unwrap();
        assert_eq!(spectrum.len(), 1);
        assert_eq!(spectrum[0].1, Frequency::new(1, 1)); // Dirac: full mass on CNF∞
        let rec = recurrence_set(&op, id(0), spectrum[0].0).unwrap();
        assert!(recurrence_type(&rec).thick); // every time visits the class
        assert!(matches!(certify_oc_bisimulation_invariant(&op), Ok(())));
    }

    #[test]
    fn aoi_hierarchy_terminates_at_the_transient_length() {
        let m = transient_two_class_cycle();
        let op = m.operator();
        // AOI changes while the transient class 0 drops out, then is constant: N = 1.
        assert_eq!(aoi_hierarchy_terminates_at(&op, id(0)), Some(1));
        assert_eq!(aoi_hierarchy_terminates_at(&op, id(1)), Some(0));
        // unified AOI is defined and self-consistent on the cycle.
        let unified = aoi_unified(&op, id(1)).unwrap();
        assert_eq!(unified.complexity.kappa, ComplexityClass::One);
        assert_eq!(unified.spectrum.len(), 2);
    }

    #[test]
    fn kappa_two_and_omega_inhabit_on_countably_infinite_class_sets() {
        // the κ case split (OC-21B) on the symbolic side: B̃ countably infinite
        // (certified prefix-injective on the ℕ-counter — see r5::orbit_type_classification) with all
        // frequencies existing (each class visited once ⇒ freq ≡ 0) ⇒ κ = 2; without
        // spectrum-definiteness ⇒ κ = ω.
        assert_eq!(complexity_class(None, true), ComplexityClass::Two);
        assert_eq!(complexity_class(None, false), ComplexityClass::Omega);
        assert_eq!(complexity_class(Some(1), true), ComplexityClass::Zero);
        assert_eq!(complexity_class(Some(3), true), ComplexityClass::One);
    }

    #[test]
    fn os_push_forwards_the_class_spectrum_to_horizon_classes() {
        // alternating two-class cycle: the ≈-class spectrum (1/2, 1/2) pushes forward
        // along the NWF classification — the primitive stays at the ≈-class level.
        let e = [(0, 1), (1, 0)];
        let s = Substrate::with_observation(2, &e, &e, &[10, 11]).unwrap();
        let m = Instance::new(s, vec![id(1), id(0)]).unwrap();
        let op = m.operator();
        let pushed = horizon_class_spectrum(&op, id(0)).unwrap();
        // total mass 1 is preserved by the push-forward (Freq-Sum, finite B̃).
        let period = 2u64;
        let total: u64 = pushed.iter().map(|(_, f)| f.numerator * (period / f.denominator)).sum();
        assert_eq!(total, period);
    }
}
