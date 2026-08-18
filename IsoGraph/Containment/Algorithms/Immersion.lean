import IsoGraph.Containment.Algorithms.Embedding
import IsoGraph.Containment.Algorithms.Routing
import IsoGraph.Containment.Minors

/-!
# Deciding the immersion relation

`CGraph.findImmersion` searches for an immersion of `H` inside `G` and returns it if there is one;
`CGraph.isEmpty_immersionOf_of_eq_none` is the other half of the answer.

An immersion is a topological minor with the disjointness weakened: the trails standing for the
edges of `H` may run through each other's vertices, and through branch vertices, as long as no two
of them share an *edge*.  So the search is the one of `Algorithms/TopMinor.lean` with the
bookkeeping moved from vertices to edges, and it shares that file's plumbing — the list-shaped
walks, the interleaved `CGraph.tasks`, the entry-based reading of an assignment — through
`Algorithms/Routing.lean`.  What is this file's own is `CGraph.edgeList`, the edges a list-shaped
walk spends, and `CGraph.trails`, which enumerates the runs from one vertex to another that repeat
no edge and use none of a given set.  `CGraph.ImmModel` is an immersion written with those lists,
and `CGraph.ImmersionOf.toImmModel` and `CGraph.ImmModel.toImmersionOf` are the two bridges, the
only place a `SimpleGraph.Walk` is taken apart or put together.

A trail, unlike a path, may come back through a vertex it has already visited, so nothing bounds
its length by the number of vertices.  What bounds it is that its edges are distinct:
`CGraph.length_le_of_nodup_edgeList` embeds a repetition-free list of edges in the list of all
vertex pairs, which gives the fuel `CGraph.trails` recurses on.  The bound is generous and costs
nothing at run time, because the set of edges already spent runs out long before the fuel does.

Two prunes do the real work, and both are inherited.  A branch vertex must have at least the degree
of the vertex it stands for — `CGraph.ImmersionOf.degree_le`, which here is the cleaner statement of
the two, since distinct edges at `x` carry edge-disjoint trails, whose first edges must differ — and
the symmetry breaking of `Algorithms/Twins.lean` is reused unchanged, needing only
`CGraph.ImmersionOf.reindex` to relabel a model along an automorphism of the pattern.

## What it costs

Compiled, through `CGraph.immersionOf?`, on one shared machine, so read the numbers as orders of
magnitude.  The degree bound settles a class of negatives outright — `K₅` immersed in Petersen is
empty in under a millisecond — and positives on a ten- or fourteen-vertex host are quick: `K₄` in
Petersen 3 ms, Petersen in Petersen 6 ms, `K₄` in Heawood 18 ms, Petersen in Heawood 42 ms.  The
cached entry point is worth about 2.4× over the same search on the edge lists (Petersen in Heawood
100 ms raw against 42 ms cached).

The host is what costs, and it costs more here than in `Algorithms/TopMinor.lean`, because there
are far more trails between two vertices than there are simple paths: `K₄` in McGee (24 vertices,
cubic) takes 1.2 s where the topological minor search takes 44 ms, and Petersen in McGee 2.5 s.
Tutte's 46-vertex cubic graph is out of reach — the topological minor search already does not
finish there in eight minutes.  Twenty-odd vertices is the working range, and a dense host is worse
still.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {G H : CGraph}

/-! ## Walks as edge lists -/

/-- The edges the walk that starts at `u` and runs along `l` uses. -/
def edgeList : G.V → List G.V → List (Sym2 G.V)
  | _, [] => []
  | u, w :: l => s(u, w) :: edgeList w l

@[simp] theorem length_edgeList (u : G.V) (l : List G.V) : (edgeList u l).length = l.length := by
  induction l generalizing u with
  | nil => rfl
  | cons w l ih => rw [edgeList, List.length_cons, ih, List.length_cons]

@[simp] theorem edges_walkOfList (u : G.V) (l : List G.V) (h : isWalkList G u l = true) :
    (walkOfList G u l h).edges = edgeList u l := by
  induction l generalizing u with
  | nil => rfl
  | cons w l ih => rw [walkOfList, SimpleGraph.Walk.edges_cons, ih, edgeList]

theorem edgeList_support_tail {u v : G.V} (p : G.toSimple.Walk u v) :
    edgeList u p.support.tail = p.edges := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.tail_cons, p.support_eq_cons, edgeList,
      SimpleGraph.Walk.edges_cons, ih]

/-- The first edge of a walk that takes at least one step. -/
theorem mem_edges_getVert_one {u v : G.V} (p : G.toSimple.Walk u v) (h : 0 < p.length) :
    s(u, p.getVert 1) ∈ p.edges := by
  cases p with
  | nil => exact absurd h (by simp)
  | cons hadj q => simp

/-- Every element of `Sym2 G.V` is named by a pair of vertices, so the list of pairs is a bound on
any repetition-free list of edges. -/
theorem length_le_of_nodup_edgeList {gs : List G.V} (hgs : ∀ v : G.V, v ∈ gs) (u : G.V)
    (p : List G.V) (h : (edgeList u p).Nodup) : p.length ≤ gs.length * gs.length := by
  have hsub : edgeList u p ⊆ gs.flatMap fun a ↦ gs.map fun b ↦ s(a, b) := by
    intro e _
    induction e using Sym2.ind with
    | _ a b => exact List.mem_flatMap.mpr ⟨a, hgs a, List.mem_map.mpr ⟨b, hgs b, rfl⟩⟩
  have hlen := (h.subperm hsub).length_le
  rw [length_edgeList] at hlen
  simpa using hlen

/-! ## Enumerating the trails between two vertices -/

/-- Every way of running from `u` to `t` in at most `n` steps without repeating an edge and
without using one of `avoid`: the list of vertices visited after `u`, whose last is `t`.  Unlike
`CGraph.routes` a trail may come back through a vertex it has already been to — including `t` —
so nothing here filters on where the walk has been, only on which edges it has spent. -/
def trails (G : CGraph) (gs : List G.V) (t : G.V) :
    ℕ → G.V → List (Sym2 G.V) → List (List G.V)
  | 0, _, _ => []
  | n + 1, u, avoid =>
    (if G.Adj u t && !avoid.contains s(u, t) then [[t]] else []) ++
      (gs.filter fun w ↦ G.Adj u w && !avoid.contains s(u, w)).flatMap fun w ↦
        (trails G gs t n w (s(u, w) :: avoid)).map (w :: ·)

/-- **Every trail is enumerated**: a run from `u` to `t` short enough, repeating no edge and using
none of `avoid`, is one of the candidates `trails` offers. -/
theorem mem_trails {gs : List G.V} (hgs : ∀ v : G.V, v ∈ gs) {t : G.V} :
    ∀ (n : ℕ) (u : G.V) (avoid : List (Sym2 G.V)) (p : List G.V), p ≠ [] → p.length ≤ n →
      isWalkList G u p = true → chainEnd u p = t → (edgeList u p).Nodup →
      (∀ e ∈ edgeList u p, e ∉ avoid) → p ∈ trails G gs t n u avoid := by
  intro n
  induction n with
  | zero => intro u avoid p hne hlen; exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | succ n ih =>
    rintro u avoid (_ | ⟨w, q⟩) hne hlen hw hend hnd havoid
    · exact absurd rfl hne
    rw [isWalkList, Bool.and_eq_true] at hw
    rw [chainEnd] at hend
    rw [edgeList] at hnd havoid
    rw [trails]
    have hfirst : s(u, w) ∉ avoid := havoid _ (List.mem_cons_self ..)
    cases q with
    | nil =>
      rw [chainEnd] at hend
      subst hend
      refine List.mem_append_left _ ?_
      rw [if_pos (by simp only [Bool.and_eq_true, hw.1, true_and, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not]; exact hfirst)]
      exact List.mem_cons_self ..
    | cons z q' =>
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨w, ?_, ?_⟩)
      · refine List.mem_filter.mpr ⟨hgs w, ?_⟩
        simp only [Bool.and_eq_true, hw.1, true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.contains_eq_mem, decide_eq_false_iff_not]
        exact hfirst
      · refine List.mem_map.mpr ⟨z :: q', ?_, rfl⟩
        have hlen' : (z :: q').length ≤ n := by
          simp only [List.length_cons] at hlen ⊢; omega
        refine ih w (s(u, w) :: avoid) (z :: q') (by simp) hlen' hw.2 hend
          (List.nodup_cons.mp hnd).2 ?_
        intro e he
        rw [List.mem_cons]
        rintro (rfl | ha)
        · exact (List.nodup_cons.mp hnd).1 he
        · exact havoid e (List.mem_cons_of_mem _ he) ha

/-! ## Immersion models, as lists -/

/-- An immersion model with its trails written as lists.  Each edge of `H` is oriented by `ord`,
and `seg x y` is the run of vertices the trail of that edge visits after `f x`. -/
structure ImmModel (H G : CGraph) where
  /-- An ordering of the vertices of `H`, which orients each of its edges. -/
  ord : H.V → ℕ
  /-- Distinct vertices have distinct positions. -/
  ord_inj : Function.Injective ord
  /-- The branch vertices. -/
  f : H.V → G.V
  /-- Distinct vertices of `H` get distinct branch vertices. -/
  f_inj : Function.Injective f
  /-- The vertices the trail of `x`–`y` visits after `f x`, for the orientation `ord y < ord x`. -/
  seg : H.V → H.V → List G.V
  /-- Consecutive vertices of a run are adjacent. -/
  isWalk : ∀ x y, H.Adj x y = true → ord y < ord x → isWalkList G (f x) (seg x y) = true
  /-- A run ends at the other branch vertex. -/
  ends : ∀ x y, H.Adj x y = true → ord y < ord x → chainEnd (f x) (seg x y) = f y
  /-- A run repeats no edge. -/
  trail : ∀ x y, H.Adj x y = true → ord y < ord x → (edgeList (f x) (seg x y)).Nodup
  /-- Two runs share no edge. -/
  disj : ∀ x y x' y', H.Adj x y = true → ord y < ord x → H.Adj x' y' = true → ord y' < ord x' →
    (x, y) ≠ (x', y') → ∀ e ∈ edgeList (f x) (seg x y), e ∉ edgeList (f x') (seg x' y')

namespace ImmersionOf

variable (t : H.ImmersionOf G) {x y : H.V}

theorem ne_of_adj' (h : H.Adj x y = true) : x ≠ y := by rintro rfl; exact H.loopless x h

theorem length_pos (h : H.Adj x y = true) : 0 < (t.walk h).length := by
  have hne : t.toFun x ≠ t.toFun y := fun he ↦ (show H.toSimple.Adj x y from h).ne (t.injective he)
  rcases Nat.eq_zero_or_pos (t.walk h).length with h0 | h0
  · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hne
  · exact h0

/-- **A branch vertex has at least the degree of the vertex it stands for**: the trails of the
edges at `x` leave `t x` by distinct edges, and so by distinct neighbours. -/
theorem degree_le (t : H.ImmersionOf G) (x : H.V) :
    H.toSimple.degree x ≤ G.toSimple.degree (t.toFun x) := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun y ↦ if h : H.Adj x y = true then (t.walk h).getVert 1 else t.toFun x) ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
    have h1 : H.Adj x y = true := hy
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset, dif_pos h1]
    simpa using (t.walk h1).adj_getVert_succ (i := 0) (t.length_pos h1)
  · intro y hy y' hy' he
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy hy'
    have h1 : H.Adj x y = true := hy
    have h2 : H.Adj x y' = true := hy'
    simp only [dif_pos h1, dif_pos h2] at he
    by_contra hne
    have hsym : s(x, y) ≠ s(x, y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨-, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne rfl
      · exact H.loopless _ h1
    refine t.edgeDisjoint' h1 h2 hsym _ (mem_edges_getVert_one _ (t.length_pos h1)) ?_
    rw [he]
    exact mem_edges_getVert_one _ (t.length_pos h2)

/-- **Relabelling a model along an automorphism of the pattern.**  Nothing moves in `G`: the same
branch vertices and the same trails, read off `H` in a different order. -/
def reindex (t : H.ImmersionOf G) {σ : H.V → H.V} (hinj : Function.Injective σ)
    (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) : H.ImmersionOf G where
  toFun x := t.toFun (σ x)
  injective' := t.injective.comp hinj
  walk h := t.walk ((hadj _ _).trans h)
  isTrail' _ := t.isTrail' _
  reverse' _ _ := t.reverse' _ _
  edgeDisjoint' := fun {x y} _ {x' y'} _ hne e he ↦ by
    have hne' : s(σ x, σ y) ≠ s(σ x', σ y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨hinj h1, hinj h2⟩
      · exact Or.inr ⟨hinj h1, hinj h2⟩
    exact t.edgeDisjoint' _ _ hne' e he

/-- What `exists_sorted_pairs` asks of the relation: it is closed under relabelling the pattern
by one of its automorphisms. -/
theorem exists_reindex (t : H.ImmersionOf G) {σ : H.V → H.V} (hinj : Function.Injective σ)
    (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    ∃ g : H.ImmersionOf G, ∀ x, g.toFun x = t.toFun (σ x) :=
  ⟨t.reindex hinj hadj, fun _ ↦ rfl⟩

/-- **An immersion model can be written as lists.** -/
def toImmModel (t : H.ImmersionOf G) (ord : H.V → ℕ) (hord : Function.Injective ord) :
    ImmModel H G where
  ord := ord
  ord_inj := hord
  f := t.toFun
  f_inj := t.injective
  seg x y := if h : H.Adj x y = true then (t.walk h).support.tail else []
  isWalk x y h _ := by rw [dif_pos h]; exact isWalkList_support_tail _
  ends x y h _ := by rw [dif_pos h]; exact chainEnd_support_tail _
  trail x y h _ := by
    rw [dif_pos h, edgeList_support_tail]
    exact (SimpleGraph.Walk.isTrail_def _).mp (t.isTrail' h)
  disj x y x' y' h hc h' hc' hne e he := by
    rw [dif_pos h, edgeList_support_tail] at he
    rw [dif_pos h', edgeList_support_tail]
    have hsym : s(x, y) ≠ s(x', y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne rfl
      · omega
    exact t.edgeDisjoint' h h' hsym e he

end ImmersionOf

namespace ImmModel

variable (m : ImmModel H G) {x y : H.V}

theorem ne_of_adj (h : H.Adj x y = true) : x ≠ y := by rintro rfl; exact H.loopless x h

theorem ord_ne (h : H.Adj x y = true) : m.ord x ≠ m.ord y := fun e ↦ ne_of_adj h (m.ord_inj e)

/-- One of the two orientations of an edge is the canonical one. -/
theorem lt_or_lt (h : H.Adj x y = true) : m.ord y < m.ord x ∨ m.ord x < m.ord y :=
  Nat.lt_or_gt_of_ne (Ne.symm (m.ord_ne h))

/-- A run is nonempty: it ends at a different branch vertex from the one it starts at. -/
theorem seg_ne_nil (h : H.Adj x y = true) (hc : m.ord y < m.ord x) : m.seg x y ≠ [] := by
  intro he
  have := m.ends x y h hc
  rw [he, chainEnd] at this
  exact ne_of_adj h (m.f_inj this)

/-- The other orientation of an edge. -/
theorem adj_symm (h : H.Adj x y = true) : H.Adj y x = true := by rw [← H.symm]; exact h

/-- The orientation of an edge the model stores a run for. -/
def canon (m : ImmModel H G) (x y : H.V) : H.V × H.V :=
  if m.ord y < m.ord x then (x, y) else (y, x)

theorem canon_adj (h : H.Adj x y = true) : H.Adj (m.canon x y).1 (m.canon x y).2 = true := by
  rw [canon]; split <;> simp [h, adj_symm h]

theorem canon_lt (h : H.Adj x y = true) : m.ord (m.canon x y).2 < m.ord (m.canon x y).1 := by
  rw [canon]
  split
  · assumption
  · exact (m.lt_or_lt h).resolve_left (by assumption)

theorem canon_sym (_h : H.Adj x y = true) : s((m.canon x y).1, (m.canon x y).2) = s(x, y) := by
  rw [canon]; split
  · rfl
  · exact Sym2.eq_swap

theorem canon_ne (h : H.Adj x y = true) {x' y' : H.V} (h' : H.Adj x' y' = true)
    (hne : s(x, y) ≠ s(x', y')) : m.canon x y ≠ m.canon x' y' := fun e ↦
  hne (by rw [← m.canon_sym h, ← m.canon_sym h', e])

/-- The edges of `G` the trail of an edge of `H` spends. -/
def spent (m : ImmModel H G) (x y : H.V) : List (Sym2 G.V) :=
  edgeList (m.f (m.canon x y).1) (m.seg (m.canon x y).1 (m.canon x y).2)

/-- The walk a canonical run names. -/
def walkSeg (m : ImmModel H G) (h : H.Adj x y = true) (hc : m.ord y < m.ord x) :
    G.toSimple.Walk (m.f x) (m.f y) :=
  (walkOfList G (m.f x) (m.seg x y) (m.isWalk x y h hc)).copy rfl (m.ends x y h hc)

@[simp] theorem edges_walkSeg (h : H.Adj x y = true) (hc : m.ord y < m.ord x) :
    (m.walkSeg h hc).edges = edgeList (m.f x) (m.seg x y) := by
  rw [walkSeg, SimpleGraph.Walk.edges_copy, edges_walkOfList]

/-- The trail of the model between two adjacent branch vertices, in either orientation. -/
def trailOf (m : ImmModel H G) (h : H.Adj x y = true) : G.toSimple.Walk (m.f x) (m.f y) :=
  if hc : m.ord y < m.ord x then m.walkSeg h hc
  else (m.walkSeg (adj_symm h) ((m.lt_or_lt h).resolve_left hc)).reverse

theorem mem_edges_trailOf (h : H.Adj x y = true) {e : Sym2 G.V} :
    e ∈ (m.trailOf h).edges ↔ e ∈ m.spent x y := by
  rw [trailOf, spent, canon]
  split
  · rw [edges_walkSeg]
  · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse, edges_walkSeg]

theorem nodup_edges_trailOf (h : H.Adj x y = true) : (m.trailOf h).edges.Nodup := by
  rw [trailOf]
  split
  · rw [edges_walkSeg]; exact m.trail x y h (by assumption)
  · rw [SimpleGraph.Walk.edges_reverse, List.nodup_reverse, edges_walkSeg]
    exact m.trail y x (adj_symm h) ((m.lt_or_lt h).resolve_left (by assumption))

/-- **A list model is an immersion model.** -/
def toImmersionOf (m : ImmModel H G) : H.ImmersionOf G where
  toFun := m.f
  injective' := m.f_inj
  walk h := m.trailOf h
  isTrail' h := (SimpleGraph.Walk.isTrail_def _).mpr (m.nodup_edges_trailOf h)
  reverse' := fun {x y} h h' ↦ by
    simp only [trailOf]
    rcases m.lt_or_lt h with hc | hc
    · rw [dif_pos hc, dif_neg (by omega)]
    · rw [dif_pos hc, dif_neg (by omega), SimpleGraph.Walk.reverse_reverse]
  edgeDisjoint' := fun {x y} h {x' y'} h' hne e he he' ↦ by
    rw [m.mem_edges_trailOf h] at he
    rw [m.mem_edges_trailOf h'] at he'
    rw [spent] at he he'
    exact m.disj _ _ _ _ (m.canon_adj h) (m.canon_lt h) (m.canon_adj h') (m.canon_lt h')
      (by simpa using m.canon_ne h h' hne) e he he'

end ImmModel

/-! ## What a finished assignment has to satisfy -/

/-- What the run `s` given to the edge from `x` to `y` has to satisfy: it is a walk from the
branch vertex of `x` to that of `y` repeating no edge, and sharing no edge with the run of another
edge of `H`. -/
def trailOk (H G : CGraph) (hs : List H.V) (asg : Asg H G) (x y : H.V) (s : List G.V) : Bool :=
  oriented H hs x y &&
    ((branches asg).all fun p ↦ !decide (p.1 = x) ||
      (isWalkList G p.2 s && decide (edgeList p.2 s).Nodup &&
        ((branches asg).all fun q ↦ !decide (q.1 = y) || decide (chainEnd p.2 s = q.2)))) &&
    ((runs asg).all fun r ↦ !oriented H hs r.1 r.2.1 || decide (x = r.1 ∧ y = r.2.1) ||
      ((branches asg).all fun p ↦ !decide (p.1 = x) ||
        ((branches asg).all fun q ↦ !decide (q.1 = r.1) ||
          (edgeList p.2 s).all fun e ↦ !(edgeList q.2 r.2.2).contains e)))

/-- **What the search is looking for**: an assignment that places every vertex of `H` at a vertex
of its own, routes every edge, and whose runs are edge-disjoint trails.  `CGraph.modelOfGoalImm`
turns one into a `CGraph.ImmModel`, and hence into an immersion. -/
def goalImm (H G : CGraph) (hs : List H.V) (asg : Asg H G) : Bool :=
  asg.all placeShape &&
    hs.all (fun x ↦ (findB x (branches asg)).isSome) &&
    hs.all (fun x ↦ hs.all fun y ↦ !oriented H hs x y || (findR x y (runs asg)).isSome) &&
    (branches asg).all (fun p ↦ (branches asg).all fun q ↦
      decide (p.1 = q.1) || decide (p.2 ≠ q.2)) &&
    (runs asg).all fun r ↦ trailOk H G hs asg r.1 r.2.1 r.2.2

variable {hs : List H.V} {asg : Asg H G}

theorem goalImm_shape (hg : goalImm H G hs asg = true) {x : H.V} {b : List G.V}
    (h : (Task.place x, b) ∈ asg) : ∃ u, b = [u] := by
  simp only [goalImm, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.1.1 _ h
  rw [placeShape, beq_iff_eq] at this
  exact List.length_eq_one_iff.mp this

theorem goalImm_findB (hg : goalImm H G hs asg = true) {x : H.V} (hx : x ∈ hs) :
    (findB x (branches asg)).isSome = true := by
  simp only [goalImm, Bool.and_eq_true, List.all_eq_true] at hg
  exact hg.1.1.1.2 x hx

theorem goalImm_findR (hg : goalImm H G hs asg = true) {x y : H.V} (hx : x ∈ hs) (hy : y ∈ hs)
    (ho : oriented H hs x y = true) : (findR x y (runs asg)).isSome = true := by
  simp only [goalImm, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.2 x hx y hy
  simpa [ho] using this

theorem goalImm_inj (hg : goalImm H G hs asg = true) {x y : H.V} {u v : G.V}
    (hp : (x, u) ∈ branches asg) (hq : (y, v) ∈ branches asg) (hxy : x ≠ y) : u ≠ v := by
  simp only [goalImm, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.2 _ hp _ hq
  simpa [hxy] using this

theorem goalImm_trailOk (hg : goalImm H G hs asg = true) {x y : H.V} {s : List G.V}
    (hr : (x, y, s) ∈ runs asg) : trailOk H G hs asg x y s = true := by
  simp only [goalImm, Bool.and_eq_true, List.all_eq_true] at hg
  exact hg.2 _ hr

variable {x y : H.V} {s : List G.V}

theorem trailOk_oriented (h : trailOk H G hs asg x y s = true) : oriented H hs x y = true :=
  (Bool.and_eq_true .. ▸ (Bool.and_eq_true .. ▸ h).1).1

/-- The three conditions on a run that mention its endpoints, read off `trailOk` at once. -/
theorem trailOk_branch (h : trailOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) : isWalkList G u s = true ∧ (edgeList u s).Nodup ∧
      ∀ {v : G.V}, (y, v) ∈ branches asg → chainEnd u s = v := by
  simp only [trailOk, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.1.2 _ hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, decide_eq_true_eq, List.all_eq_true, not_true_eq_false,
    false_or] at h2
  refine ⟨h2.1.1, h2.1.2, fun {v} hq ↦ ?_⟩
  have h3 := h2.2 _ hq
  simp only [not_true_eq_false, false_or] at h3
  exact h3

theorem trailOk_isWalk (h : trailOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) : isWalkList G u s = true := (trailOk_branch h hp).1

theorem trailOk_nodup (h : trailOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) : (edgeList u s).Nodup := (trailOk_branch h hp).2.1

theorem trailOk_ends (h : trailOk H G hs asg x y s = true) {u v : G.V}
    (hp : (x, u) ∈ branches asg) (hq : (y, v) ∈ branches asg) : chainEnd u s = v :=
  (trailOk_branch h hp).2.2 hq

/-- **Two runs spend no edge twice.**  Both ends are looked up in the assignment, so the condition
is stated over its entries only. -/
theorem trailOk_disj (h : trailOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) {x' y' : H.V} {s' : List G.V} (hr : (x', y', s') ∈ runs asg)
    (ho : oriented H hs x' y' = true) (hne : ¬(x = x' ∧ y = y')) {w : G.V}
    (hw : (x', w) ∈ branches asg) {e : Sym2 G.V} (he : e ∈ edgeList u s) :
    e ∉ edgeList w s' := by
  simp only [trailOk, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 _ hr
  simp only [ho, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hne
  have h2 := h1 _ hp
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_true_eq_false,
    false_or] at h2
  have h3 := h2 _ hw
  simp only [not_true_eq_false, false_or] at h3
  simpa using h3 _ he

/-! ## The model a finished assignment describes -/

/-- The branch vertex an assignment the search accepted gives `x`. -/
def branchOfImm (H G : CGraph) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs) (asg : Asg H G)
    (hg : goalImm H G hs asg = true) (x : H.V) : G.V :=
  (findB x (branches asg)).get (goalImm_findB hg (hmem x))

theorem branchOfImm_mem (hmem : ∀ x : H.V, x ∈ hs) (hg : goalImm H G hs asg = true) (x : H.V) :
    (x, branchOfImm H G hs hmem asg hg x) ∈ branches asg := findB_mem (Option.some_get _).symm

theorem runOfImm_mem (hg : goalImm H G hs asg = true) {x y : H.V} (hx : x ∈ hs) (hy : y ∈ hs)
    (ho : oriented H hs x y = true) : (x, y, runOf asg x y) ∈ runs asg := by
  have hs := goalImm_findR hg hx hy ho
  rw [runOf]
  cases hf : findR x y (runs asg) with
  | none => rw [hf] at hs; exact absurd hs (by simp)
  | some t => rw [Option.getD_some]; exact findR_mem hf

/-- **A finished assignment is an immersion model.** -/
def modelOfGoalImm (H G : CGraph) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs) (asg : Asg H G)
    (hg : goalImm H G hs asg = true) : ImmModel H G where
  ord x := hs.idxOf x
  ord_inj _ _ h := (List.idxOf_inj (hmem _)).mp h
  f := branchOfImm H G hs hmem asg hg
  f_inj x y he := by
    by_contra hxy
    exact goalImm_inj hg (branchOfImm_mem hmem hg x) (branchOfImm_mem hmem hg y) hxy he
  seg := runOf asg
  isWalk x y hadj hlt :=
    trailOk_isWalk (goalImm_trailOk hg (runOfImm_mem hg (hmem x) (hmem y)
      (oriented_eq_true hadj hlt))) (branchOfImm_mem hmem hg x)
  ends x y hadj hlt :=
    trailOk_ends (goalImm_trailOk hg (runOfImm_mem hg (hmem x) (hmem y)
      (oriented_eq_true hadj hlt))) (branchOfImm_mem hmem hg x) (branchOfImm_mem hmem hg y)
  trail x y hadj hlt :=
    trailOk_nodup (goalImm_trailOk hg (runOfImm_mem hg (hmem x) (hmem y)
      (oriented_eq_true hadj hlt))) (branchOfImm_mem hmem hg x)
  disj x y x' y' hadj hlt hadj' hlt' hne e he :=
    trailOk_disj (goalImm_trailOk hg (runOfImm_mem hg (hmem x) (hmem y)
      (oriented_eq_true hadj hlt))) (branchOfImm_mem hmem hg x)
      (runOfImm_mem hg (hmem x') (hmem y') (oriented_eq_true hadj' hlt'))
      (oriented_eq_true hadj' hlt') (fun h ↦ hne (by rw [h.1, h.2]))
      (branchOfImm_mem hmem hg x') he

/-! ## The candidates at a step -/

/-- The vertices of `G` that are not available to `x`: the branch vertices of the other vertices
already placed.  A trail may run through any vertex, so nothing a run has visited is spent. -/
def usedBranch (H G : CGraph) (x : H.V) (pre : Asg H G) : List G.V :=
  (branches pre).filterMap fun p ↦ if p.1 = x then none else some p.2

/-- The edges of `G` the runs chosen so far have spent. -/
def usedEdges (H G : CGraph) (hs : List H.V) (x y : H.V) (pre : Asg H G) : List (Sym2 G.V) :=
  ((runs pre).filterMap fun r ↦
    if oriented H hs r.1 r.2.1 ∧ ¬(x = r.1 ∧ y = r.2.1) then
      (findB r.1 (branches pre)).map fun u ↦ edgeList u r.2.2
    else none).flatten

/-- The values worth trying at a step.  A branch vertex may be any vertex of high enough degree
not already spoken for; a run may be any trail between the two branch vertices, already placed,
that spends no edge another run has.

The last line is the case where the two ends are *not* already placed, which `CGraph.tasks` never
produces; saying "every trail between every pair of vertices" keeps the pruning sound without a
word about the order the steps come in. -/
def candImm (H G : CGraph) (hs : List H.V) (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (rs : List (Row G)) (gs : List G.V) (n : ℕ) : Task H → Asg H G → List (List G.V)
  | .place x, pre =>
    let used := usedBranch H G x pre
    let lo := (symLo H G rank pairs x (branches pre)).foldl max 0
    let dx := H.toSimple.degree x
    (rs.filter fun p ↦ decide (dx ≤ p.deg) && !used.contains p.vert &&
      decide (lo ≤ rank p.vert)).map fun p ↦ [p.vert]
  | .route x y, pre =>
    match findB x (branches pre), findB y (branches pre) with
    | some u, some v => trails G gs v n u (usedEdges H G hs x y pre)
    | _, _ => gs.flatMap fun u ↦ gs.flatMap fun v ↦ trails G gs v n u []

/-- The whole test the search applies: the model conditions, and the order symmetry breaking puts
on the images of interchangeable vertices. -/
def goalImmSym (H G : CGraph) (hs : List H.V) (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (asg : Asg H G) : Bool :=
  goalImm H G hs asg && sortedAsg H G rank pairs (branches asg) &&
    (branches asg).all fun p ↦ decide (H.toSimple.degree p.1 ≤ G.toSimple.degree p.2)

theorem goalImmSym_goal {rank : G.V → ℕ} {pairs : List (H.V × H.V)}
    (h : goalImmSym H G hs rank pairs asg = true) : goalImm H G hs asg = true := by
  simp only [goalImmSym, Bool.and_eq_true] at h; exact h.1.1

theorem goalImmSym_sorted {rank : G.V → ℕ} {pairs : List (H.V × H.V)}
    (h : goalImmSym H G hs rank pairs asg = true) :
    sortedAsg H G rank pairs (branches asg) = true := by
  simp only [goalImmSym, Bool.and_eq_true] at h; exact h.1.2

theorem goalImmSym_degree {rank : G.V → ℕ} {pairs : List (H.V × H.V)}
    (h : goalImmSym H G hs rank pairs asg = true) {x : H.V} {u : G.V}
    (hp : (x, u) ∈ branches asg) : H.toSimple.degree x ≤ G.toSimple.degree u := by
  simp only [goalImmSym, Bool.and_eq_true, List.all_eq_true] at h
  simpa using h.2 _ hp

/-- A run that a finished assignment accepts is one `CGraph.trails` offers. -/
theorem mem_trails_of_trailOk {gs : List G.V} (hgs : ∀ v : G.V, v ∈ gs)
    (hg : goalImm H G hs asg = true) {x y : H.V} {b : List G.V}
    (hok : trailOk H G hs asg x y b = true) {u v : G.V} (hu : (x, u) ∈ branches asg)
    (hv : (y, v) ∈ branches asg) (avoid : List (Sym2 G.V))
    (hav : ∀ e ∈ edgeList u b, e ∉ avoid) :
    b ∈ trails G gs v (gs.length * gs.length) u avoid := by
  have hnd := trailOk_nodup hok hu
  have hends := trailOk_ends hok hu hv
  refine mem_trails hgs _ u avoid b ?_ ?_ (trailOk_isWalk hok hu) hends hnd hav
  · rintro rfl
    rw [chainEnd] at hends
    exact goalImm_inj hg hu hv (ne_of_oriented (trailOk_oriented hok)) hends
  · exact length_le_of_nodup_edgeList hgs u b hnd

/-- **The pruning is sound**: a value that occurs in a finished assignment is one the search
offers at that step. -/
theorem mem_candImm {hs : List H.V} (hmem : ∀ x : H.V, x ∈ hs) {gs : List G.V}
    (hgs : ∀ v : G.V, v ∈ gs) {rank : G.V → ℕ} {pairs : List (H.V × H.V)} (a : Task H)
    (pre : Asg H G) (b : List G.V) (l : Asg H G)
    (hsym : goalImmSym H G hs rank pairs (l ++ (a, b) :: pre) = true) :
    b ∈ candImm H G hs rank pairs (rowList G gs) gs (gs.length * gs.length) a pre := by
  have hg := goalImmSym_goal hsym
  have hsub : pre ⊆ l ++ (a, b) :: pre := fun z hz ↦
    List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  cases a with
  | place x =>
    obtain ⟨u, rfl⟩ := goalImm_shape hg (List.mem_append_right _ (List.mem_cons_self ..))
    have hbu : (x, u) ∈ branches (l ++ (Task.place x, [u]) :: pre) :=
      mem_branches (List.mem_append_right _ (List.mem_cons_self ..))
    have hnu : u ∉ usedBranch H G x pre := by
      intro hu
      obtain ⟨p, hp, hpu⟩ := List.mem_filterMap.mp hu
      by_cases hx : p.1 = x
      · rw [if_pos hx] at hpu; exact absurd hpu (by simp)
      · rw [if_neg hx, Option.some_inj] at hpu
        exact goalImm_inj hg hbu (mem_branches_of_subset hsub hp) (fun he ↦ hx he.symm) hpu.symm
    have hlo : ∀ m ∈ symLo H G rank pairs x (branches pre), m ≤ rank u := by
      intro m hm
      obtain ⟨z, hz, hmz⟩ := List.mem_filterMap.mp hm
      cases hf : (branches pre).find? (fun q ↦ decide (q.1 = z)) with
      | none => rw [hf] at hmz; exact absurd hmz (by simp)
      | some q =>
        rw [hf, Option.map_some, Option.some_inj] at hmz
        have hq1 : q.1 = z := by simpa using List.find?_some hf
        rw [← hmz]
        exact sortedAsg_le H G (goalImmSym_sorted hsym) (mem_symBefore H hz)
          (mem_branches_of_subset hsub (List.mem_of_find?_eq_some hf)) hbu hq1 rfl
    refine List.mem_map.mpr ⟨row G gs u,
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨u, hgs u, rfl⟩, ?_⟩, rfl⟩
    simp only [row, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
      decide_eq_false_iff_not, decide_eq_true_eq]
    exact ⟨⟨goalImmSym_degree hsym hbu, hnu⟩, foldl_max_le (Nat.zero_le _) hlo⟩
  | route x y =>
    have hrun : (x, y, b) ∈ runs (l ++ (Task.route x y, b) :: pre) :=
      mem_runs (List.mem_append_right _ (List.mem_cons_self ..))
    have hok := goalImm_trailOk hg hrun
    rw [candImm]
    split
    · rename_i u v hfx hfy
      have hu := mem_branches_of_subset hsub (findB_mem hfx)
      refine mem_trails_of_trailOk hgs hg hok hu
        (mem_branches_of_subset hsub (findB_mem hfy)) _ ?_
      intro e he hused
      obtain ⟨t, ht, het⟩ := List.mem_flatten.mp hused
      obtain ⟨r, hr, hrt⟩ := List.mem_filterMap.mp ht
      by_cases ho : oriented H hs r.1 r.2.1 = true ∧ ¬(x = r.1 ∧ y = r.2.1)
      · rw [if_pos ho] at hrt
        cases hb : findB r.1 (branches pre) with
        | none => rw [hb] at hrt; exact absurd hrt.symm (by simp)
        | some w =>
          rw [hb, Option.map_some, Option.some_inj] at hrt
          exact trailOk_disj hok hu (mem_runs_of_subset hsub hr) ho.1 ho.2
            (mem_branches_of_subset hsub (findB_mem hb)) he (hrt ▸ het)
      · rw [if_neg ho] at hrt; exact absurd hrt.symm (by simp)
    · obtain ⟨u, hfu⟩ := Option.isSome_iff_exists.mp (goalImm_findB hg (hmem x))
      obtain ⟨v, hfv⟩ := Option.isSome_iff_exists.mp (goalImm_findB hg (hmem y))
      exact List.mem_flatMap.mpr ⟨u, hgs u, List.mem_flatMap.mpr ⟨v, hgs v,
        mem_trails_of_trailOk hgs hg hok (findB_mem hfu) (findB_mem hfv) []
          (fun e _ ↦ List.not_mem_nil)⟩⟩

/-! ## The search -/

/-- The assignment a model makes: a branch vertex for each vertex, a run for each oriented edge. -/
def valOfImm (m : ImmModel H G) : Task H → List G.V
  | .place x => [m.f x]
  | .route x y => m.seg x y

/-- What the search would have to find, given a model. -/
def asgOfImm (m : ImmModel H G) (hs : List H.V) : Asg H G :=
  (tasks H hs).map fun k ↦ (k, valOfImm m k)

theorem val_of_mem_asgOfImm {m : ImmModel H G} {hs : List H.V} {k : Task H} {v : List G.V}
    (h : (k, v) ∈ (asgOfImm m hs).reverse) : k ∈ tasks H hs ∧ v = valOfImm m k := by
  rw [asgOfImm, List.mem_reverse, List.mem_map] at h
  obtain ⟨k', hk', he⟩ := h
  rw [Prod.mk.injEq] at he
  exact ⟨he.1 ▸ hk', he.1 ▸ he.2.symm⟩

theorem branch_of_mem_branches_imm {m : ImmModel H G} {hs : List H.V} {x : H.V} {u : G.V}
    (h : (x, u) ∈ branches (asgOfImm m hs).reverse) : u = m.f x := by
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp h
  obtain ⟨k, v⟩ := q
  split at hqp
  · rename_i x' u' he
    rw [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨-, hv⟩ := val_of_mem_asgOfImm hq
    rw [valOfImm, List.cons.injEq] at hv
    rw [Option.some_inj, Prod.mk.injEq] at hqp
    rw [← hqp.1, ← hqp.2, hv.1]
  · exact absurd hqp.symm (by simp)

theorem mem_branches_asgOfImm {m : ImmModel H G} {hs : List H.V} {x : H.V} (hx : x ∈ hs) :
    (x, m.f x) ∈ branches (asgOfImm m hs).reverse :=
  mem_branches (List.mem_reverse.mpr (List.mem_map.mpr ⟨Task.place x, place_mem_tasks hx, rfl⟩))

theorem run_of_mem_runs_imm {m : ImmModel H G} {hs : List H.V} {x y : H.V} {s : List G.V}
    (h : (x, y, s) ∈ runs (asgOfImm m hs).reverse) :
    s = m.seg x y ∧ oriented H hs x y = true := by
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp h
  obtain ⟨k, v⟩ := q
  split at hqp
  · rename_i x' y' s' he
    rw [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hk, hv⟩ := val_of_mem_asgOfImm hq
    rw [Option.some_inj, Prod.mk.injEq, Prod.mk.injEq] at hqp
    obtain ⟨rfl, rfl, rfl⟩ := hqp
    exact ⟨hv, oriented_of_route_mem_tasks hk⟩
  · exact absurd hqp.symm (by simp)

theorem mem_runs_asgOfImm {m : ImmModel H G} {hs : List H.V} {x y : H.V} (hx : x ∈ hs)
    (hy : y ∈ hs) (ho : oriented H hs x y = true) :
    (x, y, m.seg x y) ∈ runs (asgOfImm m hs).reverse :=
  mem_runs (List.mem_reverse.mpr
    (List.mem_map.mpr ⟨Task.route x y, route_mem_tasks hx hy ho, rfl⟩))

/-- **A model passes every test the search applies.** -/
theorem goalImm_asgOfImm (m : ImmModel H G) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs)
    (hord : ∀ x : H.V, m.ord x = hs.idxOf x) :
    goalImm H G hs (asgOfImm m hs).reverse = true := by
  have hlt : ∀ {x y : H.V}, oriented H hs x y = true → m.ord y < m.ord x := fun ho ↦ by
    rw [hord, hord]; exact idxOf_lt_of_oriented ho
  simp only [goalImm, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨fun p hp ↦ ?_, fun x _ ↦ ?_⟩, fun x _ y _ ↦ ?_⟩, fun p hp q hq ↦ ?_⟩, fun r hr ↦ ?_⟩
  · obtain ⟨k, v⟩ := p
    obtain ⟨-, rfl⟩ := val_of_mem_asgOfImm hp
    cases k <;> simp [placeShape, valOfImm]
  · simp [findB_isSome (mem_branches_asgOfImm (hmem x))]
  · by_cases ho : oriented H hs x y = true
    · simp [findR_isSome (mem_runs_asgOfImm (hmem x) (hmem y) ho)]
    · simp [Bool.eq_false_iff.mpr ho]
  · obtain ⟨a, u⟩ := p
    obtain ⟨b, v⟩ := q
    rw [branch_of_mem_branches_imm hp, branch_of_mem_branches_imm hq]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, m.f_inj.ne_iff]
  · obtain ⟨x, y, s⟩ := r
    obtain ⟨rfl, ho⟩ := run_of_mem_runs_imm hr
    have hadj := adj_of_oriented ho
    simp only [trailOk, Bool.and_eq_true, List.all_eq_true, ho, true_and]
    refine ⟨fun p hp ↦ ?_, fun r' hr' ↦ ?_⟩
    · obtain ⟨a, u⟩ := p
      rw [branch_of_mem_branches_imm hp]
      by_cases hax : a = x
      · rw [hax]
        simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true]
        refine ⟨⟨m.isWalk _ _ hadj (hlt ho), m.trail _ _ hadj (hlt ho)⟩, fun q hq ↦ ?_⟩
        obtain ⟨b, v⟩ := q
        rw [branch_of_mem_branches_imm hq]
        by_cases hby : b = y
        · rw [hby]; simp [m.ends _ _ hadj (hlt ho)]
        · simp [hby]
      · simp [hax]
    · obtain ⟨x', y', s'⟩ := r'
      by_cases ho' : oriented H hs x' y' = true
      · obtain ⟨rfl, -⟩ := run_of_mem_runs_imm hr'
        by_cases hsame : x = x' ∧ y = y'
        · simp [hsame]
        · simp only [ho', Bool.not_true, Bool.false_or, hsame, decide_false, List.all_eq_true]
          rintro ⟨a, u⟩ hp
          rw [branch_of_mem_branches_imm hp]
          by_cases hax : a = x
          · rw [hax]
            simp only [decide_true, Bool.not_true, Bool.false_or, List.all_eq_true]
            rintro ⟨c, w⟩ hq
            rw [branch_of_mem_branches_imm hq]
            by_cases hcx : c = x'
            · rw [hcx]
              simp only [decide_true, Bool.not_true, Bool.false_or, List.all_eq_true]
              intro e he
              simpa using m.disj _ _ _ _ hadj (hlt ho) (adj_of_oriented ho') (hlt ho')
                (fun he' ↦ hsame ⟨congrArg Prod.fst he', congrArg Prod.snd he'⟩) e he
            · simp [hcx]
          · simp [hax]
      · simp [Bool.eq_false_iff.mpr ho']

/-- And it passes the symmetry test too, once its branch vertices are sorted. -/
theorem goalImmSym_asgOfImm (m : ImmModel H G) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs)
    (hord : ∀ x : H.V, m.ord x = hs.idxOf x) (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (hsort : ∀ p ∈ pairs, rank (m.f p.1) ≤ rank (m.f p.2))
    (hdeg : ∀ x : H.V, H.toSimple.degree x ≤ G.toSimple.degree (m.f x)) :
    goalImmSym H G hs rank pairs (asgOfImm m hs).reverse = true := by
  rw [goalImmSym, goalImm_asgOfImm m hs hmem hord, Bool.true_and, Bool.and_eq_true]
  constructor
  · rw [sortedAsg, List.all_eq_true]
    intro p hp
    rw [List.all_eq_true]
    rintro ⟨a, u⟩ hq
    rw [List.all_eq_true]
    rintro ⟨c, w⟩ hr
    by_cases ha : a = p.1
    · by_cases hc : c = p.2
      · rw [branch_of_mem_branches_imm hq, branch_of_mem_branches_imm hr]
        simp only [ha, hc, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        exact hsort p hp
      · simp [hc]
    · simp [ha]
  · rw [List.all_eq_true]
    rintro ⟨a, u⟩ hq
    rw [branch_of_mem_branches_imm hq]
    simpa using hdeg a

/-- The assignment the search finds, if there is one. -/
def searchImm (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : Option (Asg H G) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    Backtrack.dfs
      (candImm H G (searchOrder H rH.toList) (hostRank G rG)
        (symPairs H (searchOrder H rH.toList)) (rowList G rG.toList) rG.toList
        (rG.toList.length * rG.toList.length))
      (goalImmSym H G (searchOrder H rH.toList) (hostRank G rG)
        (symPairs H (searchOrder H rH.toList)))
      (tasks H (searchOrder H rH.toList)) []
  else none

theorem searchImm_goal {rH : Roster H.V} {rG : Roster G.V} {r : Asg H G}
    (h : searchImm H G rH rG = some r) :
    goalImm H G (searchOrder H rH.toList) r = true := by
  rw [searchImm] at h
  split at h
  · exact goalImmSym_goal (Backtrack.goal_of_dfs_eq_some h)
  · exact absurd h (by simp)

/-- **Does `H` immerse in `G`?**  Returns a model when there is one; see
`isEmpty_immersionOf_of_eq_none` for the other half of the answer. -/
def findImmersion (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) :
    Option (H.ImmersionOf G) :=
  Option.pmap (p := fun r ↦ goalImm H G (searchOrder H rH.toList) r = true)
    (fun r hr ↦ (modelOfGoalImm H G (searchOrder H rH.toList)
      (mem_searchOrder H rH.mem_toList) r hr).toImmersionOf)
    (searchImm H G rH rG) (fun _ hr ↦ searchImm_goal hr)

theorem findImmersion_eq_none_iff (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) :
    findImmersion H G rH rG = none ↔ searchImm H G rH rG = none := Option.pmap_eq_none_iff

/-- **Completeness**: when the search comes back empty, `H` does not immerse in `G`. -/
theorem isEmpty_immersionOf_of_eq_none {H G : CGraph} {rH : Roster H.V} {rG : Roster G.V}
    (h : findImmersion H G rH rG = none) : IsEmpty (H.ImmersionOf G) := by
  rw [findImmersion_eq_none_iff, searchImm] at h
  refine ⟨fun t ↦ ?_⟩
  split at h
  · have hmem := mem_searchOrder H rH.mem_toList
    obtain ⟨g, hgsort⟩ := exists_sorted_pairs (fun (t : H.ImmersionOf G) ↦ t.toFun)
      (fun t {_σ} hinj hadj ↦ t.exists_reindex hinj hadj) (hs := searchOrder H rH.toList)
      (hostRank G rG) hmem t
    have hinj : Function.Injective fun x : H.V ↦ (searchOrder H rH.toList).idxOf x :=
      fun x y he ↦ (List.idxOf_inj (hmem x)).mp he
    have hsol : (asgOfImm (g.toImmModel _ hinj) (searchOrder H rH.toList)).map Prod.fst
        = tasks H (searchOrder H rH.toList) := by
      rw [asgOfImm, List.map_map]
      exact List.map_id _
    have hn := Backtrack.dfs_eq_none (mem_candImm hmem rG.mem_toList) h hsol
    rw [List.append_nil,
      goalImmSym_asgOfImm _ _ hmem (fun _ ↦ rfl) _ _ hgsort (fun x ↦ g.degree_le x)] at hn
    exact absurd hn (by simp)
  · exact absurd (show FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E from
      ⟨t.card_le, t.E_le⟩) ‹_›

/-- `H` immerses in `G` exactly when the search finds a model. -/
theorem isEmpty_immersionOf_iff (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.ImmersionOf G) ↔ findImmersion H G rH rG = none := by
  refine ⟨fun hemp ↦ ?_, isEmpty_immersionOf_of_eq_none⟩
  rcases hm : findImmersion H G rH rG with _ | f
  · rfl
  · exact (hemp.false f).elim

end CGraph
