//! # R1.1 — The Substrate
//!
//! Exact realization of spec section **R1.1** ("The Substrate",
//! `CRPT_OMEGA_TOWER_R1.md`, v1.0.0-rc9). Axiom-free base; every item here is a
//! *definition* (no PA-* axiom assumed). Items realized:
//!
//! - R1.1.D1 `Sub` — the substrate (𝒰, →_ρ, →_σ, 𝒯), with inclusion →_ρ ⊆ →_σ.
//! - R1.1.D2 `NF` — normal forms.
//! - R1.1.D3 `n-Step` — →_ρ^n.
//! - R1.1.D4 `RT*` — →_ρ* (and →_σ*).
//! - R1.1.D5 `Div` — diverging elements (R1.1.R2 `Div-NotDet`: not substrate-determined).
//! - R1.1.D6 `Bisim` / R1.1.D7 `Bisim~` (≈) — bisimulation and bisimilarity;
//!   R1.1.L1 `Bisim-Union` guarantees the *largest* bisimulation is well-defined.
//!
//! ## Equality, in CRPT terms
//!
//! CRPT carries its own stratified notions of equality, and we build on those
//! rather than deriving structural equality blanketly:
//! - **mathematical identity `=`** (Common Pitfalls: distinct from ≃_M, ≈) —
//!   for the finite universe this is element-index identity, the *only* place we
//!   derive `PartialEq`/`Eq` (on [`ElementId`]). `a == b` here means `a = b`.
//! - **bisimilarity ≈** (R1.1.D7) — a *computed* partition ([`Substrate::bisimilarity`]),
//!   not a derived trait.
//! - (observable equivalence ≃_M, R1.12.D2, arrives with the projection operator.)
//!
//! Compound types (the [`Substrate`] itself) get **no** derived equality —
//! structural "sameness" is homomorphism/isomorphism (R4), computed, never structural.
//!
//! ## Determinism & representation
//!
//! No hashing, no `Ord`-keyed maps: 𝒰 = `{0, …, n−1}` is dense, so sets are
//! sorted `Vec<ElementId>` or `Vec<bool>` bitmaps indexed by element, and
//! grouping is done by sorting (`docs/DETERMINISM_CONTRACT.md`). Element values
//! are never cloned — only indices flow.
//!
//! ## Finite instantiation
//!
//! 𝒰 is "a class" in R1.1.D1; we realize the finite case, with 𝒯 the **discrete
//! topology** (every subset open; T₂ trivially — the topology the spec uses for
//! finite substrates, e.g. Rω.1.D1), fully determined by 𝒰 and so carrying no
//! data. The topological-mode generalization (TopSep + continuity of ρ, imposed
//! as axioms at R1.7 for PA-WN_top) is a later extension point.

// The dense element-index loop `for x in 0..n { … block[x] … ElementId(x) … }` is the
// engine's deliberate representation idiom (see `docs/DETERMINISM_CONTRACT.md`): the
// loop variable *is* the element id, used both as an index and as an `ElementId`. So
// `clippy::needless_range_loop` does not apply here.
#![allow(clippy::needless_range_loop)]

/// A dense index into the substrate universe 𝒰 = `{0, …, n−1}` (R1.1.D1).
///
/// `ElementId` *is* the array index. The derived `==` is CRPT **mathematical
/// identity `=`** on universe positions (Common Pitfalls) — the one equality
/// we derive. No `Ord`/`Hash`: ordering uses the index key explicitly; lookups
/// use dense arrays, not maps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ElementId(pub u32);

impl ElementId {
    /// The element's array index.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Error constructing a [`Substrate`].
#[derive(Debug, Clone, Copy)]
pub enum SubstrateError {
    /// A reduction or structural edge `(from, to)` references an element outside `0..n`.
    EdgeOutOfRange { from: u32, to: u32, n: u32 },
    /// The inclusion constraint →_ρ ⊆ →_σ (part of the *definition* of a
    /// substrate, R1.1.D1) is violated: `x →_ρ y` holds but not `x →_σ y`.
    InclusionViolated { x: ElementId, y: ElementId },
    /// The observation labeling violates the R1.1.D6 anchoring: `obs(x) = obs(y)` for a
    /// pair that must be distinguished — either two distinct normal forms (`obs ↾ NF` must
    /// be injective), or a normal form and a non-normal-form (`obs` must respect NF-status).
    ObservationAnchorViolated { x: ElementId, y: ElementId },
    /// The supplied observation labeling has the wrong length (≠ |𝒰|).
    ObservationWrongLength { expected: u32, got: usize },
}

/// **R1.1.D1 (`Sub`)** — a finite CRPT substrate `(𝒰, →_ρ, →_σ, 𝒯)`.
///
/// - 𝒰 = `{0, …, n−1}`.
/// - the **reduction relation** →_ρ (sorted, deduped adjacency).
/// - the **structural relation** →_σ (sorted, deduped adjacency).
/// - the topology 𝒯 — discrete (see module docs), held implicitly.
///
/// The definitional inclusion constraint →_ρ ⊆ →_σ (R1.1.D1) is enforced at
/// construction: a value of this type *is* a substrate. No derived equality (see
/// module docs).
#[derive(Debug)]
pub struct Substrate {
    n: u32,
    reduction: Vec<Vec<ElementId>>,
    structural: Vec<Vec<ElementId>>,
    /// **`Obs-Lab` (R1.1.D8)** — the **derived** observation labelling
    /// `obs : 𝒰 → NF(→_ρ) ⊔ O_M`: a normal form is *its own atomic observable* (the NF
    /// summand — realized by injectively distinct labels here, theorem-backed by
    /// `Obs-Lab-WD` R1.1.T1(i,ii)), and a non-fixpoint emits `Observable(ρ_M(x))` — the
    /// content of its projection step, supplied by PA-Prod's Observable Contract
    /// `(O_M, 0)`. obs adds **no primitive structure**: it is definable from Fix, ρ_M,
    /// and Observable ([`Substrate::from_observable_contract`] performs the derivation;
    /// [`Substrate::with_observation`] accepts an already-derived labelling). `≈` is the
    /// bisimulation on the labelled system `(𝒰, →_ρ, obs)`.
    observation: Vec<u32>,
}

impl Substrate {
    /// Construct `(𝒰, →_ρ, →_σ, 𝒯)` over 𝒰 = `{0, …, n−1}` from edge lists of the
    /// reduction relation and the structural relation.
    ///
    /// Enforces the definitional inclusion →_ρ ⊆ →_σ (R1.1.D1): a quadruple
    /// violating it is not a substrate, and construction fails.
    pub fn new(
        n: u32,
        reduction_edges: &[(u32, u32)],
        structural_edges: &[(u32, u32)],
    ) -> Result<Self, SubstrateError> {
        let mut reduction = vec![Vec::new(); n as usize];
        let mut structural = vec![Vec::new(); n as usize];
        for &(a, b) in reduction_edges {
            if a >= n || b >= n {
                return Err(SubstrateError::EdgeOutOfRange { from: a, to: b, n });
            }
            reduction[a as usize].push(ElementId(b));
        }
        for &(a, b) in structural_edges {
            if a >= n || b >= n {
                return Err(SubstrateError::EdgeOutOfRange { from: a, to: b, n });
            }
            structural[a as usize].push(ElementId(b));
        }
        for row in reduction.iter_mut() {
            row.sort_by_key(|e| e.index());
            row.dedup();
        }
        for row in structural.iter_mut() {
            row.sort_by_key(|e| e.index());
            row.dedup();
        }
        // Inclusion constraint →_ρ ⊆ →_σ (definitional, R1.1.D1).
        for x in 0..n as usize {
            for &y in &reduction[x] {
                if structural[x].binary_search_by_key(&y.index(), |e| e.index()).is_err() {
                    return Err(SubstrateError::InclusionViolated { x: ElementId(x as u32), y });
                }
            }
        }
        // Default minimal observation (R1.1.D6): each normal form is its own observable,
        // all non-normal-forms share observable 0.
        let mut observation = vec![0u32; n as usize];
        let mut next_obs = 1u32;
        for x in 0..n as usize {
            if reduction[x].is_empty() {
                observation[x] = next_obs;
                next_obs += 1;
            }
        }
        Ok(Self { n, reduction, structural, observation })
    }

    /// Construct a substrate with an explicit **observation labelling** `obs`
    /// (`Obs-Lab` R1.1.D8) — an already-derived labelling, e.g. produced by an
    /// instantiation from its Observable Contract per the Obs-Lab case split. The
    /// reduction/structural relations are built as in [`Substrate::new`];
    /// `observation[x]` is the observable id of element x.
    ///
    /// Validates the R1.1.D6 anchoring: `obs` must respect NF-status (no normal form
    /// shares an observable with a non-normal-form) and be **injective on normal forms**
    /// (distinct normal forms are distinct observables). Non-normal-forms may share
    /// observables freely. A richer-than-default labeling lets `≈` distinguish persistent
    /// elements (so e.g. Type EP / `CPD ≥ 2` become reachable).
    pub fn with_observation(
        n: u32,
        reduction_edges: &[(u32, u32)],
        structural_edges: &[(u32, u32)],
        observation: &[u32],
    ) -> Result<Self, SubstrateError> {
        let mut s = Self::new(n, reduction_edges, structural_edges)?;
        if observation.len() != n as usize {
            return Err(SubstrateError::ObservationWrongLength {
                expected: n,
                got: observation.len(),
            });
        }
        // Validate the R1.1.D6 anchoring against the (already-built) reduction relation.
        for x in 0..n as usize {
            for y in (x + 1)..n as usize {
                if observation[x] != observation[y] {
                    continue;
                }
                let x_nf = s.is_normal_form(ElementId(x as u32));
                let y_nf = s.is_normal_form(ElementId(y as u32));
                // obs(x)=obs(y) is forbidden unless both are non-normal-forms.
                if x_nf || y_nf {
                    return Err(SubstrateError::ObservationAnchorViolated {
                        x: ElementId(x as u32),
                        y: ElementId(y as u32),
                    });
                }
            }
        }
        s.observation = observation.to_vec();
        Ok(s)
    }

    /// **`Obs-Lab` (R1.1.D8) — the derivation itself**: build the substrate with
    /// `obs(x) := x` on `Fix(ρ_M) = NF(→_ρ)` (each normal form its own atomic
    /// observable — the NF summand, realized by injectively distinct labels) and
    /// `obs(x) := Observable(ρ_M(x))` otherwise — the content emitted by x's projection
    /// step, from the instance's Observable Contract `(O_M, 0)` (PA-Prod R1.2.Ax6) and its
    /// chosen strategy `ρ_M`. The labelled reading adds no primitive structure
    /// (`Obs-Lab-WD` R1.1.T1(iv)).
    pub fn from_observable_contract(
        n: u32,
        reduction_edges: &[(u32, u32)],
        structural_edges: &[(u32, u32)],
        observable: &[u32],
        rho: &[ElementId],
    ) -> Result<Self, SubstrateError> {
        let mut s = Self::new(n, reduction_edges, structural_edges)?; // NF-identity defaults
        if observable.len() != n as usize {
            return Err(SubstrateError::ObservationWrongLength { expected: n, got: observable.len() });
        }
        for x in 0..n as usize {
            if !s.reduction[x].is_empty() {
                s.observation[x] = observable[rho[x].index()]; // obs(x) = Observable(ρ_M(x))
            } // NF keeps its identity label (the NF summand, distinct per normal form)
        }
        Ok(s)
    }

    /// Witness **`Obs-Lab-WD` (R1.1.T1)** on this substrate, given the contract data:
    /// **(i)** NF-injectivity — `obs ↾ NF` injective (distinct normal forms are distinct
    /// observables); **(ii)** aspect separation — realized structurally (NF labels are
    /// the identity summand, held in NF-singleton blocks by `≈`); **(iii)** no silent
    /// labels — for every non-fixpoint, `Observable(ρ_M(x)) ≠ 0` (PA-Prod). Returns the
    /// first violating element, or `Ok`.
    pub fn certify_obs_lab_wd(&self, observable: &[u32], rho: &[ElementId]) -> Result<(), ElementId> {
        for x in 0..self.n as usize {
            if self.reduction[x].is_empty() {
                // (i): distinct NFs carry distinct labels.
                for y in 0..self.n as usize {
                    if y != x && self.reduction[y].is_empty() && self.observation[x] == self.observation[y] {
                        return Err(ElementId(x as u32));
                    }
                }
            } else if observable[rho[x].index()] == 0 {
                return Err(ElementId(x as u32)); // (iii): a silent projection step
            }
        }
        Ok(())
    }

    /// **`Obs-Lab` (R1.1.D8)** — the derived observation labelling at `x`.
    pub fn observation(&self, x: ElementId) -> u32 {
        self.observation[x.index()]
    }

    /// |𝒰|.
    #[inline]
    pub fn universe_len(&self) -> u32 {
        self.n
    }

    /// The elements of 𝒰 in ascending order.
    pub fn elements(&self) -> impl Iterator<Item = ElementId> + '_ {
        (0..self.n).map(ElementId)
    }

    /// The reduction successors `{y | x →_ρ y}` (sorted).
    pub fn reduction_successors(&self, x: ElementId) -> &[ElementId] {
        &self.reduction[x.index()]
    }

    /// The structural successors `{y | x →_σ y}` (sorted).
    pub fn structural_successors(&self, x: ElementId) -> &[ElementId] {
        &self.structural[x.index()]
    }

    /// `x →_ρ y` (one reduction step).
    pub fn reduces(&self, x: ElementId, y: ElementId) -> bool {
        self.reduction[x.index()].binary_search_by_key(&y.index(), |e| e.index()).is_ok()
    }

    /// `x →_σ y` (one structural step).
    pub fn structural_step(&self, x: ElementId, y: ElementId) -> bool {
        self.structural[x.index()].binary_search_by_key(&y.index(), |e| e.index()).is_ok()
    }

    // ---- R1.1.D2 (`NF`) — Normal Form ------------------------------------

    /// **R1.1.D2 (`NF`)**: `NF(x) :⟺ ¬∃y : x →_ρ y` — x has no reduction successor.
    pub fn is_normal_form(&self, x: ElementId) -> bool {
        self.reduction[x.index()].is_empty()
    }

    /// **R1.1.D2 (`NF`)**: the set `NF(→_ρ) = {x ∈ 𝒰 | NF(x)}`, ascending.
    pub fn normal_forms(&self) -> Vec<ElementId> {
        self.elements().filter(|&x| self.is_normal_form(x)).collect()
    }

    // ---- R1.1.D3 (`n-Step`) — →_ρ^n --------------------------------------

    /// **R1.1.D3 (`n-Step`)**: `{y | x →_ρ^n y}`, the elements reachable from x in
    /// *exactly* n reduction steps (`→_ρ^0` is the identity, so n = 0 gives `{x}`).
    /// Ascending.
    pub fn reduction_in_steps(&self, x: ElementId, n: u32) -> Vec<ElementId> {
        let size = self.n as usize;
        let mut frontier = vec![false; size];
        frontier[x.index()] = true; // →_ρ^0 = identity
        for _ in 0..n {
            let mut next = vec![false; size];
            for u in 0..size {
                if frontier[u] {
                    for &v in &self.reduction[u] {
                        next[v.index()] = true;
                    }
                }
            }
            frontier = next;
        }
        (0..size).filter(|&i| frontier[i]).map(|i| ElementId(i as u32)).collect()
    }

    // ---- R1.1.D4 (`RT*`) — →_ρ* and →_σ* ---------------------------------

    /// **R1.1.D4 (`RT*`)**: `x →_ρ* y` (reflexive-transitive closure of →_ρ).
    /// Reflexive: `reduction_reachable(x, x)` is always true.
    pub fn reduction_reachable(&self, x: ElementId, y: ElementId) -> bool {
        Self::reachable(&self.reduction, self.n, x, y)
    }

    /// **R1.1.D4 (`RT*`)**: `x →_σ* y` (reflexive-transitive closure of →_σ).
    /// By the inclusion constraint, `x →_ρ* y ⟹ x →_σ* y`.
    pub fn structural_reachable(&self, x: ElementId, y: ElementId) -> bool {
        Self::reachable(&self.structural, self.n, x, y)
    }

    fn reachable(adj: &[Vec<ElementId>], n: u32, x: ElementId, y: ElementId) -> bool {
        let mut seen = vec![false; n as usize];
        let mut stack = vec![x];
        seen[x.index()] = true;
        while let Some(u) = stack.pop() {
            if u == y {
                return true; // covers reflexivity (first pop is x)
            }
            for &v in &adj[u.index()] {
                if !seen[v.index()] {
                    seen[v.index()] = true;
                    stack.push(v);
                }
            }
        }
        false
    }

    // ---- R1.1.D5 (`Div`) — Diverging Elements ----------------------------

    /// **R1.1.D5 (`Div`)**: `x ∈ Div(→_ρ) :⟺ ∃σ:ℕ→𝒰 : σ(0)=x ∧ ∀n : σ(n)→_ρσ(n+1)`
    /// — an infinite reduction sequence from x exists.
    ///
    /// Exact on finite 𝒰: such a sequence exists iff x reduction-reaches a vertex
    /// on a →_ρ-cycle (`w` with `w →_ρ^{≥1} w`).
    pub fn diverges(&self, x: ElementId) -> bool {
        self.divergent_set()[x.index()]
    }

    /// **R1.1.D5 (`Div`)**: `Div(→_ρ)` as a bitmap indexed by `ElementId::index`.
    /// (R1.1.R2 `Div-NotDet`: emptiness is not substrate-determined; here it is
    /// computed from the actual reduction graph.)
    pub fn divergent_set(&self) -> Vec<bool> {
        let size = self.n as usize;
        // cyclic[v] ⟺ v →_ρ^{≥1} v.
        let mut cyclic = vec![false; size];
        for v in 0..size {
            let mut seen = vec![false; size];
            let mut stack: Vec<usize> = self.reduction[v].iter().map(|e| e.index()).collect();
            for &s in &stack {
                seen[s] = true;
            }
            while let Some(u) = stack.pop() {
                if u == v {
                    cyclic[v] = true;
                    break;
                }
                for &w in &self.reduction[u] {
                    if !seen[w.index()] {
                        seen[w.index()] = true;
                        stack.push(w.index());
                    }
                }
            }
        }
        // Div = least set with: cyclic ⊆ Div, and a vertex with a reduction
        // successor in Div is in Div.
        let mut divergent = cyclic;
        let mut changed = true;
        while changed {
            changed = false;
            for x in 0..size {
                if !divergent[x] && self.reduction[x].iter().any(|s| divergent[s.index()]) {
                    divergent[x] = true;
                    changed = true;
                }
            }
        }
        divergent
    }

    // ---- R1.1.D6/D7 (`Bisim` / `Bisim~`) — Bisimilarity ≈ ----------------

    /// **R1.1.D7 (`Bisim~`, ≈)**: the largest bisimulation on the *labelled* substrate
    /// `(𝒰, →_ρ, obs)` (R1.1.D6, v1.0.0-rc9). Returned as the canonical representative
    /// (least-indexed member) of each element's ≈-class: `x ≈ y ⟺ rep[x] == rep[y]`.
    ///
    /// **Observation clause.** ≈ respects an observable `obs(x)`, with the minimal
    /// anchoring that **distinct normal forms are distinct observables** (`obs ↾ NF(→_ρ)`
    /// is injective — each normal form is its own atomic observable). This is what makes
    /// `PA-Bisim` (R1.3.Ax1) non-vacuous: without it every normal form is vacuously
    /// bisimilar to every other (NFs have no →_ρ-successors), collapsing all canonical
    /// forms. Non-normal-forms share one observable and are separated only by reduction.
    /// (Richer persistent-aspect observation — the orbit signature `sig_M-NM` R2.1.D5 —
    /// is a future refinement; the NF-anchoring is the minimal form realized here.)
    ///
    /// Computed exactly by partition refinement (Kanellakis–Smolka): from the **initial
    /// partition by `obs`**, repeatedly split blocks by the *set of successor blocks*
    /// under →_ρ until no block splits. On a finite substrate this terminates and yields
    /// ≈ exactly (decidable per `Finite-Collapse` R0.7.T2). Grouping is by sorting — no
    /// maps, no hashing.
    pub fn bisimilarity(&self) -> Vec<ElementId> {
        let size = self.n as usize;
        if size == 0 {
            return Vec::new();
        }
        // Initial partition by the substrate's observable obs (R1.1.D6 observation
        // clause): elements sharing an observable start together; the anchoring (held by
        // construction) keeps distinct normal forms — and NF vs non-NF — apart.
        let mut block = self.observation.clone();
        // Dense-renumber observables to 0..block_count.
        let mut present: Vec<u32> = block.clone();
        present.sort_unstable();
        present.dedup();
        for b in block.iter_mut() {
            *b = present.binary_search(b).unwrap() as u32;
        }
        let mut block_count = present.len();
        loop {
            // key(x) = (current block of x, sorted set of successor blocks).
            let mut keyed: Vec<((u32, Vec<u32>), usize)> = Vec::with_capacity(size);
            for x in 0..size {
                let mut succ: Vec<u32> =
                    self.reduction[x].iter().map(|e| block[e.index()]).collect();
                succ.sort_unstable();
                succ.dedup();
                keyed.push(((block[x], succ), x));
            }
            keyed.sort(); // deterministic grouping by key, then element index
            let mut new_block = vec![0u32; size];
            let mut next = 0u32;
            for i in 0..size {
                if i > 0 && keyed[i].0 != keyed[i - 1].0 {
                    next += 1;
                }
                new_block[keyed[i].1] = next;
            }
            let new_count = next as usize + 1;
            block = new_block;
            if new_count == block_count {
                break; // refinement (monotone: only splits) reached its fixpoint
            }
            block_count = new_count;
        }
        // canonical representative per block = least element index in the block.
        let mut block_rep: Vec<Option<ElementId>> = vec![None; size];
        for x in 0..size {
            let b = block[x] as usize;
            if block_rep[b].is_none() {
                block_rep[b] = Some(ElementId(x as u32));
            }
        }
        (0..size).map(|x| block_rep[block[x] as usize].unwrap()).collect()
    }

    /// `x ≈ y` (bisimilarity, R1.1.D7). Convenience over [`Substrate::bisimilarity`]
    /// (recomputes; callers needing many queries should hold the representative array).
    pub fn bisimilar(&self, x: ElementId, y: ElementId) -> bool {
        let rep = self.bisimilarity();
        rep[x.index()] == rep[y.index()]
    }

    /// Witness that the computed ≈ satisfies the literal **R1.1.D6** bisimulation
    /// transfer conditions (forward and backward). Returns the first violating
    /// pair, or `Ok(())`. (`Bisim-Union` R1.1.L1 guarantees the largest such
    /// relation exists; this certifies the computed one against the definition.)
    pub fn certify_bisimilarity(&self) -> Result<(), (ElementId, ElementId)> {
        let rep = self.bisimilarity();
        let same = |a: ElementId, b: ElementId| rep[a.index()] == rep[b.index()];
        for x in self.elements() {
            for y in self.elements() {
                if !same(x, y) {
                    continue;
                }
                for &xp in self.reduction_successors(x) {
                    if !self.reduction_successors(y).iter().any(|&yp| same(xp, yp)) {
                        return Err((x, y)); // forward
                    }
                }
                for &yp in self.reduction_successors(y) {
                    if !self.reduction_successors(x).iter().any(|&xp| same(yp, xp)) {
                        return Err((x, y)); // backward
                    }
                }
            }
        }
        Ok(())
    }

}

/// Witness **R1.1.R1 (`Two-Rel`)** — why the substrate carries **two** relations: `→_ρ` for
/// projection (the vertical/observable dimension) and `→_σ` for structure (the
/// horizontal/unobservable dimension), with `→_ρ ⊆ →_σ`. The two are genuinely distinct — a
/// substrate may carry `→_σ`-structure invisible to `→_ρ`. Returns `true` when the substrate
/// has a purely-structural edge (so the two relations do not collapse to one).
pub fn two_relations_are_distinct(s: &Substrate) -> bool {
    s.elements().any(|x| s.structural_successors(x).iter().any(|&y| !s.reduces(x, y)))
}

/// Witness **R1.1.L2 (`≈-Eq`)** — bisimilarity `≈` is an **equivalence relation** (reflexive,
/// symmetric, transitive): the identity is a bisimulation and bisimulations are closed under
/// inverse and composition, so the computed [`Substrate::bisimilarity`] representative map is
/// a well-formed equivalence. Returns the first element where the representative map fails
/// reflexivity/idempotence (none — "same representative" is an equivalence by construction),
/// or `Ok`.
pub fn certify_bisimilarity_is_equivalence(s: &Substrate) -> Result<(), ElementId> {
    let rep = s.bisimilarity();
    for x in s.elements() {
        // idempotence of the representative map ⟺ reflexivity + symmetry + transitivity of
        // the induced "same class" relation: rep(rep(x)) = rep(x).
        if rep[rep[x.index()].index()] != rep[x.index()] {
            return Err(x);
        }
    }
    Ok(())
}

/// **R1.1.D7 reading (`Disc-Bisim`, R1.1.R4)** — bisimilarity read as the **discernibility**
/// relation: `x ≈ y` iff `x` and `y` are indiscernible (share a bisimilarity class). Equality
/// of the computed representatives.
pub fn discernibility_equivalent(s: &Substrate, x: ElementId, y: ElementId) -> bool {
    let rep = s.bisimilarity();
    rep[x.index()] == rep[y.index()]
}

/// Witness **R1.1.R3 (`Bisim-NotEq`)** — the substrate does **not** identify bisimilar
/// elements: `x ≈ y ⟹ x = y` is never assumed at substrate level (the axiom-level link is
/// `PA-Bisim`). Returns a witnessing pair `(x, y)` with `x ≈ y` but `x ≠ y` when one exists
/// (so `≈` is strictly coarser than `=`), else `None` (the substrate happens to be
/// `≈`-discrete).
pub fn bisim_not_eq_witness(s: &Substrate) -> Option<(ElementId, ElementId)> {
    let rep = s.bisimilarity();
    for x in s.elements() {
        for y in s.elements() {
            if x != y && rep[x.index()] == rep[y.index()] {
                return Some((x, y));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Common-Pitfalls example: 𝒰 = {a,b,c} = {0,1,2},
    /// ρ(a)=ρ(b)=c, c a normal form. →_σ ⊇ →_ρ (with one extra structural edge).
    fn pitfalls() -> Substrate {
        Substrate::new(3, &[(0, 2), (1, 2)], &[(0, 2), (1, 2), (0, 1)]).unwrap()
    }

    #[test]
    fn inclusion_is_definitional() {
        // →_ρ edge (0,2) absent from →_σ ⇒ not a substrate (R1.1.D1).
        assert!(matches!(
            Substrate::new(3, &[(0, 2)], &[(0, 1)]),
            Err(SubstrateError::InclusionViolated { x: ElementId(0), y: ElementId(2) })
        ));
        assert!(pitfalls().structural_step(ElementId(0), ElementId(2))); // →_ρ ⊆ →_σ
    }

    #[test]
    fn normal_forms_d2() {
        let s = pitfalls();
        assert!(!s.is_normal_form(ElementId(0)));
        assert!(s.is_normal_form(ElementId(2)));
        assert_eq!(s.normal_forms(), vec![ElementId(2)]);
    }

    #[test]
    fn observation_d6() {
        // Default obs (minimal): NF 2 is its own observable; non-NFs 0,1 share observable 0.
        let s = pitfalls();
        assert_eq!(s.observation(ElementId(0)), s.observation(ElementId(1)));
        assert_ne!(s.observation(ElementId(0)), s.observation(ElementId(2)));
        // Richer obs may distinguish two persistent cycles 0⇄1 and 2⇄3 (all non-NF).
        let e = [(0, 1), (1, 0), (2, 3), (3, 2)];
        let labelled = Substrate::with_observation(4, &e, &e, &[10, 10, 11, 11]).unwrap();
        // 0,1 (obs 10) bisimilar; 2,3 (obs 11) bisimilar; the two cycles are NOT bisimilar.
        assert!(labelled.bisimilar(ElementId(0), ElementId(1)));
        assert!(!labelled.bisimilar(ElementId(0), ElementId(2)));
        // Anchoring rejected: a normal form may not share an observable with another element.
        // Here 1 is a normal form (no →_ρ edge); giving it obs equal to non-NF 0 violates D6.
        assert!(matches!(
            Substrate::with_observation(2, &[(0, 1)], &[(0, 1)], &[5, 5]),
            Err(SubstrateError::ObservationAnchorViolated { .. })
        ));
    }

    #[test]
    fn n_step_d3() {
        let s = pitfalls();
        assert_eq!(s.reduction_in_steps(ElementId(0), 0), vec![ElementId(0)]);
        assert_eq!(s.reduction_in_steps(ElementId(0), 1), vec![ElementId(2)]);
        assert!(s.reduction_in_steps(ElementId(0), 2).is_empty()); // 2 is NF
    }

    #[test]
    fn rt_closure_d4() {
        let s = pitfalls();
        assert!(s.reduction_reachable(ElementId(2), ElementId(2))); // reflexive
        assert!(s.reduction_reachable(ElementId(0), ElementId(2)));
        assert!(!s.reduction_reachable(ElementId(2), ElementId(0)));
        assert!(s.structural_reachable(ElementId(0), ElementId(2))); // →_ρ* ⟹ →_σ*
    }

    #[test]
    fn divergence_d5() {
        let s = pitfalls();
        assert_eq!(s.divergent_set(), vec![false, false, false]); // acyclic
        // 0 ⇄ 1 cycle, 2 → 0 pendant: all diverge.
        let cyc = Substrate::new(3, &[(0, 1), (1, 0), (2, 0)], &[(0, 1), (1, 0), (2, 0)]).unwrap();
        assert!(cyc.diverges(ElementId(0)));
        assert!(cyc.diverges(ElementId(1)));
        assert!(cyc.diverges(ElementId(2)));
        let loopy = Substrate::new(1, &[(0, 0)], &[(0, 0)]).unwrap(); // self-loop is a cycle
        assert!(loopy.diverges(ElementId(0)));
    }

    #[test]
    fn bisimilarity_d7() {
        let s = pitfalls();
        // 0 and 1 both reduce in one step to the normal form 2 ⇒ 0 ≈ 1; 2 alone.
        assert!(s.bisimilar(ElementId(0), ElementId(1)));
        assert!(!s.bisimilar(ElementId(0), ElementId(2)));
        let rep = s.bisimilarity();
        assert!(rep[0] == rep[1]); // CRPT mathematical identity = on representatives
        assert!(rep[0] != rep[2]);
        assert!(matches!(s.certify_bisimilarity(), Ok(()))); // computed ≈ is a bisimulation
    }



    #[test]
    fn obs_lab_derives_the_labelling_from_the_contract() {
        // Obs-Lab (R1.1.D8): 0→1 (1 ∈ NF), 2⇄3 cycle. Contract Observable: 𝒰 → (O_M, 0)
        // with Observable = [9, 9, 20, 30] (no silent content on the orbit images).
        // Derived: obs(0) = Observable(ρ(0)) = Observable(1) = 9; obs(2) = Observable(3)
        // = 30; obs(3) = Observable(2) = 20; obs(1) = the NF identity summand.
        let e = [(0, 1), (2, 3), (3, 2)];
        let rho = [ElementId(1), ElementId(1), ElementId(3), ElementId(2)];
        let s = Substrate::from_observable_contract(4, &e, &e, &[9, 9, 20, 30], &rho).unwrap();
        assert_eq!(s.observation[0], 9);
        assert_eq!(s.observation[2], 30);
        assert_eq!(s.observation[3], 20);
        // Obs-Lab-WD: (i) NF-injectivity, (iii) no silent labels — certified.
        assert!(matches!(s.certify_obs_lab_wd(&[9, 9, 20, 30], &rho), Ok(())));
        // the derived labelling makes the cycle classes ≈-distinct (obs 30 ≠ 20), so the
        // labelled bisimulation separates them — the contract drives discernibility.
        let rep = s.bisimilarity();
        assert_ne!(rep[2], rep[3]);
        // a silent contract (Observable(3) = 0) violates Obs-Lab-WD(iii) at x = 2.
        let silent = Substrate::from_observable_contract(4, &e, &e, &[9, 9, 20, 0], &rho).unwrap();
        assert_eq!(silent.certify_obs_lab_wd(&[9, 9, 20, 0], &rho), Err(ElementId(2)));
    }

    #[test]
    fn two_relations_bisim_equivalence_and_discernibility() {
        // 0 ⇄ 1 obs-equal cycle (bisimilar, distinct); 2 →_ρ 3, 3 ∈ NF. →_σ adds 0 →_σ 2.
        let r = [(0, 1), (1, 0), (2, 3)];
        let sigma = [(0, 1), (1, 0), (2, 3), (0, 2)];
        let s = Substrate::with_observation(4, &r, &sigma, &[5, 5, 6, 7]).unwrap();
        // Two-Rel: →_σ carries structure (0 →_σ 2) invisible to →_ρ.
        assert!(two_relations_are_distinct(&s));
        // ≈-Eq: the bisimilarity is a well-formed equivalence.
        assert!(matches!(certify_bisimilarity_is_equivalence(&s), Ok(())));
        // Bisim-NotEq / Disc-Bisim: 0 ≈ 1 (indiscernible) but 0 ≠ 1.
        assert_eq!(bisim_not_eq_witness(&s), Some((ElementId(0), ElementId(1))));
        assert!(discernibility_equivalent(&s, ElementId(0), ElementId(1)));
        assert!(!discernibility_equivalent(&s, ElementId(2), ElementId(3)));
    }
}
