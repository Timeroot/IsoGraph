import IsoGraph.Containment.Algorithms.Embedding
import IsoGraph.Containment.Algorithms.Routing
import IsoGraph.Containment.Minors

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Deciding the topological minor relation

`CGraph.findTopMinor` searches for a subdivision of `H` inside `G` and returns it if there is one;
`CGraph.isEmpty_topMinorOf_of_eq_none` is the other half of the answer.

A topological minor model is two things at once — an injection `f` of the vertices of `H`, and a
path of `G` for every edge of `H` — and the paths have to be internally disjoint from each other
and from the branch vertices.  The `SimpleGraph.Walk` that `CGraph.TopMinorOf` carries is a
dependent type, indexed by its own endpoints, which is not something a search can build up one
step at a time.  So the file works with `CGraph.TopModel`, the same data written as lists — on the
list-shaped walks of `Algorithms/Routing.lean` — where `seg x y` is the list of vertices a path
visits after `f x`, for the endpoint order `ord y < ord x` fixed once and for all by where the
vertices sit in the search order.  `CGraph.TopMinorOf.toTopModel` and
`CGraph.TopModel.toTopMinorOf` are the two bridges, and they are the only place a `Walk` is taken
apart or put together.

The search itself is `Algorithms/Backtrack.lean` over the list of `CGraph.tasks` — place a vertex,
or route an edge whose two ends are already placed — which `Algorithms/Routing.lean` also
supplies.  The value of a place task is a one-element list, the value of a route task is the run
itself, and `CGraph.routes`, which is this file's own, enumerates the runs: every simple path of
`G` from one branch vertex to the other that avoids the vertices already spent.

Everything the goal test asks is asked of the *entries* of the assignment rather than of what a
lookup finds in it, for the reason `Algorithms/Routing.lean` gives.  For the same reason the goal
demands that every route entry be `CGraph.oriented`: without it there is no finite candidate list
to offer for a task the search never generates.

Two prunes do the real work.  A branch vertex must have at least the degree of the vertex it
stands for — `CGraph.TopMinorOf.degree_le`, which holds because the paths at `x` leave `f x` by
distinct neighbours — and that alone settles `K₅` against any cubic host instantly.  And the
symmetry breaking of `Algorithms/Twins.lean` is reused unchanged: `CGraph.TopMinorOf.reindex`
relabels a model along an automorphism of the pattern, which is what `CGraph.exists_sorted_pairs`
needs, so interchangeable vertices of `H` are only ever tried with their branch vertices in rank
order.

## What it costs

Compiled, through `CGraph.topMinorOf?`, on one shared machine, so read the numbers as orders of
magnitude.  The degree bound decides a whole class of negatives outright: `K₅ ≤ₜ Petersen` is empty
in under a millisecond, where without it the same search takes seconds.  Positives on a small host
are as quick — `K₄ ≤ₜ Petersen` and `K₄ ≤ₜ Heawood` under a millisecond, `Petersen ≤ₜ Petersen`
1 ms, `Petersen ≤ₜ Heawood` 3 ms.  The cached entry point is worth little here, because the path
enumeration no longer asks the graph anything: `CGraph.searchTopFast` hands it the neighbour lists,
tabulated once, and what used to be a scan of every vertex per step is a look at three.

What costs is the *host*, not the pattern.  `CGraph.routes` materialises every simple path between
two vertices, and in a sparse graph that number grows with the host far faster than the search
tree shrinks: `K₄ ≤ₜ McGee` (24 vertices, cubic) takes 25 ms, `Petersen ≤ₜ McGee` 100 ms, and the
same pattern in Tutte's 46-vertex cubic graph does not finish in eight minutes.  Twenty-odd
vertices is the working range, and a dense host is worse still, so this search is for small sparse
hosts.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {G H : CGraph}

/-! ## Enumerating the paths between two vertices -/

/-- Every way of running from `u` to `t` in at most `n` steps: the list of vertices visited after
`u`, whose last is `t`, staying clear of `avoid` until then.  Only completeness matters — a caller
checks what it is handed — so nothing here has to be proved sound.

`nb u` is the neighbours of `u`, and it is all this asks of `G` — the graph itself is not looked
at; completeness needs only that `nb u` *contain* the neighbours.  See `CGraph.searchTop` for where
the list comes from. -/
def routes (G : CGraph) (nb : G.V → List G.V) (t : G.V) : ℕ → G.V → List G.V → List (List G.V)
  | 0, _, _ => []
  | n + 1, u, avoid =>
    (if (nb u).contains t then [[t]] else []) ++
      ((nb u).filter fun w ↦ !avoid.contains w && w != t).flatMap fun w ↦
        (routes G nb t n w (w :: avoid)).map (w :: ·)

/-- **Every path is enumerated**: a run from `u` to `t` short enough, with no repeats, whose
interior misses `avoid`, is one of the candidates `routes` offers. -/
theorem mem_routes {nb : G.V → List G.V} (hnb : ∀ u w : G.V, G.Adj u w = true → w ∈ nb u)
    {t : G.V} :
    ∀ (n : ℕ) (u : G.V) (avoid : List G.V) (p : List G.V), p ≠ [] → p.length ≤ n →
      isWalkList G u p = true → chainEnd u p = t → (u :: p).Nodup →
      (∀ w ∈ p.dropLast, w ∉ avoid) → p ∈ routes G nb t n u avoid := by
  intro n
  induction n with
  | zero => intro u avoid p hne hlen; exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | succ n ih =>
    rintro u avoid (_ | ⟨w, q⟩) hne hlen hw hend hnd havoid
    · exact absurd rfl hne
    rw [isWalkList, Bool.and_eq_true] at hw
    rw [chainEnd] at hend
    rw [routes]
    rcases q.eq_nil_or_concat' with rfl | ⟨q', z, rfl⟩
    · rw [chainEnd] at hend
      subst hend
      exact List.mem_append_left _ (by rw [if_pos (by simpa using hnb u w hw.1)]; simp)
    · have hdrop : (w :: (q' ++ [z])).dropLast = w :: q' := by
        rw [← List.cons_append, List.dropLast_concat]
      have hwq : w ∉ q' ++ [z] := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨w, ?_, ?_⟩)
      · refine List.mem_filter.mpr ⟨hnb u w hw.1, ?_⟩
        have hwt : w ≠ t := by
          intro he
          refine hwq ?_
          rw [he, ← hend, chainEnd_eq_getLast, List.getLast_cons (by simp)]
          exact List.getLast_mem _
        have hwa : w ∉ avoid := havoid w (by rw [hdrop]; exact List.mem_cons_self ..)
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.contains_eq_mem, decide_eq_false_iff_not, bne_iff_ne, ne_eq]
        exact ⟨hwa, hwt⟩
      · refine List.mem_map.mpr ⟨q' ++ [z], ?_, rfl⟩
        have hlen' : (q' ++ [z]).length ≤ n := by
          simp only [List.length_cons] at hlen; omega
        refine ih w (w :: avoid) (q' ++ [z]) (by simp) hlen' hw.2 hend
          (List.nodup_cons.mp hnd).2 ?_
        intro v hv
        rw [List.dropLast_concat] at hv
        rw [List.mem_cons]
        rintro (rfl | hva)
        · exact hwq (List.mem_append_left _ hv)
        · exact havoid v (by rw [hdrop]; exact List.mem_cons_of_mem _ hv) hva

/-! ## Topological minor models, as lists -/

/-- A topological minor model with its paths written as lists.  Each edge of `H` is oriented by
`ord`, and `seg x y` is the run of vertices the path of that edge visits after `f x`. -/
structure TopModel (H G : CGraph) where
  /-- An ordering of the vertices of `H`, which orients each of its edges. -/
  ord : H.V → ℕ
  /-- Distinct vertices have distinct positions. -/
  ord_inj : Function.Injective ord
  /-- The branch vertices. -/
  f : H.V → G.V
  /-- Distinct vertices of `H` get distinct branch vertices. -/
  f_inj : Function.Injective f
  /-- The vertices the path of `x`–`y` visits after `f x`, for the orientation `ord y < ord x`. -/
  seg : H.V → H.V → List G.V
  /-- Consecutive vertices of a run are adjacent. -/
  isWalk : ∀ x y, H.Adj x y = true → ord y < ord x → isWalkList G (f x) (seg x y) = true
  /-- A run ends at the other branch vertex. -/
  ends : ∀ x y, H.Adj x y = true → ord y < ord x → chainEnd (f x) (seg x y) = f y
  /-- A run repeats no vertex. -/
  nodup : ∀ x y, H.Adj x y = true → ord y < ord x → (f x :: seg x y).Nodup
  /-- No branch vertex lies in the interior of a run. -/
  interior : ∀ x y, H.Adj x y = true → ord y < ord x → ∀ z : H.V, f z ∉ (seg x y).dropLast
  /-- Two runs share no interior vertex. -/
  disj : ∀ x y x' y', H.Adj x y = true → ord y < ord x → H.Adj x' y' = true → ord y' < ord x' →
    (x, y) ≠ (x', y') → ∀ z ∈ (seg x y).dropLast, z ∉ (seg x' y').dropLast

/-! ### Models whose paths have length at most two

Excision — delete a few vertices of a cubic graph, then suppress the degree-two vertices that
leaves behind — produces a subdivision in which every path has one edge or two.  Such a model is
much less data than a general `CGraph.TopModel`: where the branch vertices go, and the midpoint of
each subdivided edge.  The conditions are correspondingly local.  In particular `mid_ne_f` and
`mid_inj` are the whole of `interior` and `disj`, and neither of them mentions a *pair* of edges
of `H` — which is what makes a model on a hundred vertices checkable at all. -/

/-- A topological minor model in which the path of every edge of `H` has length one or two: `f`
places the branch vertices and `mid x y` is the interior vertex of the path of `x`–`y`, when that
path has one. -/
structure PathTwoModel (H G : CGraph) where
  /-- The branch vertices. -/
  f : H.V → G.V
  /-- Distinct vertices of `H` get distinct branch vertices. -/
  f_inj : Function.Injective f
  /-- The interior vertex of the path of an edge, if its path has length two. -/
  mid : H.V → H.V → Option G.V
  /-- An edge's path does not depend on which way the edge is read. -/
  mid_symm : ∀ x y, mid x y = mid y x
  /-- The path of an edge is a walk of `G` between the two branch vertices. -/
  step : ∀ x y, H.Adj x y = true →
    ((mid x y).elim (G.Adj (f x) (f y)) fun w ↦ G.Adj (f x) w && G.Adj w (f y)) = true
  /-- No interior vertex is a branch vertex. -/
  mid_ne_f : ∀ x y w, mid x y = some w → ∀ z, f z ≠ w
  /-- Distinct edges get distinct interior vertices. -/
  mid_inj : ∀ x y x' y' w, mid x y = some w → mid x' y' = some w → s(x, y) = s(x', y')

namespace PathTwoModel

variable {H G : CGraph}

/-- The run of vertices the path of `x`–`y` visits after `f x`. -/
def seg (m : H.PathTwoModel G) (x y : H.V) : List G.V :=
  match m.mid x y with
  | none => [m.f y]
  | some w => [w, m.f y]

/-- **A model whose paths have length at most two is a model.**  Any injective `ord` will orient
the edges; which one is chosen makes no difference, since the data is symmetric to begin with. -/
def toTopModel (m : H.PathTwoModel G) (ord : H.V → ℕ) (hord : Function.Injective ord) :
    H.TopModel G where
  ord := ord
  ord_inj := hord
  f := m.f
  f_inj := m.f_inj
  seg := m.seg
  isWalk := by
    intro x y hxy _
    have hs := m.step x y hxy
    rcases hm : m.mid x y with _ | w <;> rw [hm] at hs <;>
      simp only [seg, hm, isWalkList, Bool.and_true] <;> exact hs
  ends := by
    intro x y _ _
    rcases hm : m.mid x y with _ | w <;> simp [seg, hm, chainEnd]
  nodup := by
    intro x y hxy _
    have hne : m.f x ≠ m.f y := fun he ↦ H.loopless y (by rw [m.f_inj he] at hxy; exact hxy)
    rcases hm : m.mid x y with _ | w
    · simp [seg, hm, hne]
    · have h1 : m.f x ≠ w := m.mid_ne_f x y w hm x
      have h2 : m.f y ≠ w := m.mid_ne_f x y w hm y
      simp [seg, hm, hne, h1, Ne.symm h2]
  interior := by
    intro x y _ _ z
    rcases hm : m.mid x y with _ | w
    · simp [seg, hm]
    · simpa [seg, hm] using m.mid_ne_f x y w hm z
  disj := by
    intro x y x' y' _ hxy _ hxy' hne z hz hz'
    rcases hm : m.mid x y with _ | w
    · simp [seg, hm] at hz
    rcases hm' : m.mid x' y' with _ | w'
    · simp [seg, hm'] at hz'
    simp [seg, hm, hm'] at hz hz'
    subst hz
    subst hz'
    rcases Sym2.eq_iff.1 (m.mid_inj x y x' y' _ hm hm') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · omega

end PathTwoModel

namespace TopMinorOf

variable (t : H.TopMinorOf G) {x y : H.V}

theorem ne_of_adj' (h : H.Adj x y = true) : x ≠ y := by rintro rfl; exact H.loopless x h

theorem nodup_support (h : H.Adj x y = true) : (t.path h).support.Nodup :=
  (SimpleGraph.Walk.isPath_def _).mp (t.isPath' h)

/-- The interior of the path of an edge: the vertices strictly between its two branch ones. -/
theorem support_tail_eq (h : H.Adj x y = true) :
    (t.path h).support.tail = (t.path h).support.tail.dropLast ++ [t.toFun y] :=
  tail_support_eq _ fun e ↦ ne_of_adj' h (t.injective e)

theorem not_mem_dropLast (h : H.Adj x y = true) (z : H.V) :
    t.toFun z ∉ (t.path h).support.tail.dropLast := by
  intro hz
  have hsup : t.toFun z ∈ (t.path h).support := by
    rw [← (t.path h).cons_tail_support, List.mem_cons]
    exact Or.inr (List.mem_of_mem_dropLast hz)
  have hnd := t.nodup_support h
  rw [← (t.path h).cons_tail_support, t.support_tail_eq h] at hnd
  rcases t.branch' h z hsup with rfl | rfl
  · exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hz)
  · exact (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.2 _ hz _
      (List.mem_singleton_self _) rfl

theorem mem_support_of_mem_dropLast (h : H.Adj x y = true) {z : G.V}
    (hz : z ∈ (t.path h).support.tail.dropLast) : z ∈ (t.path h).support := by
  rw [← (t.path h).cons_tail_support, List.mem_cons]
  exact Or.inr (List.mem_of_mem_dropLast hz)

/-- The first step out of a branch vertex along the path of one of its edges. -/
theorem adj_getVert_one (t : H.TopMinorOf G) {x y : H.V} (h : H.Adj x y = true) :
    G.toSimple.Adj (t.toFun x) ((t.path h).getVert 1) := by
  have hne : t.toFun x ≠ t.toFun y := fun he ↦ (show H.toSimple.Adj x y from h).ne (t.injective he)
  have hlen : 0 < (t.path h).length := by
    rcases Nat.eq_zero_or_pos (t.path h).length with h0 | h0
    · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hne
    · exact h0
  simpa using (t.path h).adj_getVert_succ (i := 0) hlen

/-- **A branch vertex has at least the degree of the vertex it stands for**: the paths of the
edges at `x` leave `t x` by distinct neighbours. -/
theorem degree_le (t : H.TopMinorOf G) (x : H.V) :
    H.toSimple.degree x ≤ G.toSimple.degree (t.toFun x) := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun y ↦ if h : H.Adj x y = true then (t.path h).getVert 1 else t.toFun x) ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
    have h1 : H.Adj x y = true := hy
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset, dif_pos h1]
    exact t.adj_getVert_one h1
  · intro y hy y' hy' he
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy hy'
    have h1 : H.Adj x y = true := hy
    have h2 : H.Adj x y' = true := hy'
    simp only [dif_pos h1, dif_pos h2] at he
    by_contra hne
    have hlen : 0 < (t.path h1).length := by
      rcases Nat.eq_zero_or_pos (t.path h1).length with h0 | h0
      · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0)
          (fun hxy ↦ (show H.toSimple.Adj x y from h1).ne (t.injective hxy))
      · exact h0
    have hz1 : (t.path h1).getVert 1 ∈ (t.path h1).support :=
      SimpleGraph.Walk.getVert_mem_support _ _
    have hz2 : (t.path h1).getVert 1 ∈ (t.path h2).support :=
      he ▸ SimpleGraph.Walk.getVert_mem_support _ _
    have hsym : s(x, y) ≠ s(x, y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨-, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne rfl
      · exact H.loopless _ h1
    obtain ⟨b, hb⟩ := t.disjoint' h1 h2 hsym _ hz1 hz2
    rw [hb] at hz1 hz2
    rcases t.branch' h1 b hz1 with rfl | rfl
    · have h0 : (t.path h1).getVert 0 = (t.path h1).getVert 1 := by
        rw [SimpleGraph.Walk.getVert_zero]; exact hb.symm
      exact absurd ((t.isPath' h1).getVert_injOn (by simp) (by simp; omega) h0) (by simp)
    · rcases t.branch' h2 b hz2 with rfl | rfl
      · exact H.loopless _ h1
      · exact hne rfl

/-- **Relabelling a model along an automorphism of the pattern.**  Nothing moves in `G`: the same
branch vertices and the same paths, read off `H` in a different order. -/
def reindex (t : H.TopMinorOf G) {σ : H.V → H.V} (hinj : Function.Injective σ)
    (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) : H.TopMinorOf G where
  toFun x := t.toFun (σ x)
  injective' := t.injective.comp hinj
  path h := t.path ((hadj _ _).trans h)
  isPath' _ := t.isPath' _
  reverse' _ _ := t.reverse' _ _
  branch' _ z hz := (t.branch' _ (σ z) hz).imp (fun h ↦ hinj h) fun h ↦ hinj h
  disjoint' := fun {x y} _ {x' y'} _ hne z hz hz' ↦ by
    have hne' : s(σ x, σ y) ≠ s(σ x', σ y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨hinj h1, hinj h2⟩
      · exact Or.inr ⟨hinj h1, hinj h2⟩
    obtain ⟨b, rfl⟩ := t.disjoint' _ _ hne' z hz hz'
    obtain ⟨b', rfl⟩ := (Finite.injective_iff_surjective.mp hinj) b
    exact ⟨b', rfl⟩

/-- What `exists_sorted_pairs` asks of the relation: it is closed under relabelling the pattern
by one of its automorphisms. -/
theorem exists_reindex (t : H.TopMinorOf G) {σ : H.V → H.V} (hinj : Function.Injective σ)
    (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    ∃ g : H.TopMinorOf G, ∀ x, g.toFun x = t.toFun (σ x) :=
  ⟨t.reindex hinj hadj, fun _ ↦ rfl⟩

/-- **A topological minor model can be written as lists.** -/
def toTopModel (t : H.TopMinorOf G) (ord : H.V → ℕ) (hord : Function.Injective ord) :
    TopModel H G where
  ord := ord
  ord_inj := hord
  f := t.toFun
  f_inj := t.injective
  seg x y := if h : H.Adj x y = true then (t.path h).support.tail else []
  isWalk x y h _ := by rw [dif_pos h]; exact isWalkList_support_tail _
  ends x y h _ := by rw [dif_pos h]; exact chainEnd_support_tail _
  nodup x y h _ := by
    rw [dif_pos h]
    have hnd := t.nodup_support h
    rwa [← (t.path h).cons_tail_support] at hnd
  interior x y h _ z := by rw [dif_pos h]; exact t.not_mem_dropLast h z
  disj x y x' y' h hc h' hc' hne z hz hz' := by
    rw [dif_pos h] at hz
    rw [dif_pos h'] at hz'
    have hsym : s(x, y) ≠ s(x', y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hne rfl
      · omega
    obtain ⟨b, rfl⟩ := t.disjoint' h h' hsym z (t.mem_support_of_mem_dropLast h hz)
      (t.mem_support_of_mem_dropLast h' hz')
    exact t.not_mem_dropLast h b hz

end TopMinorOf

namespace TopModel

variable (m : TopModel H G) {x y : H.V}

theorem ne_of_adj (h : H.Adj x y = true) : x ≠ y := by
  rintro rfl; exact H.loopless x h

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

/-- A run ends at `f y`, so its last vertex is that. -/
theorem seg_eq (h : H.Adj x y = true) (hc : m.ord y < m.ord x) :
    m.seg x y = (m.seg x y).dropLast ++ [m.f y] := by
  have hne := m.seg_ne_nil h hc
  have hl : (m.seg x y).getLast hne = m.f y := by
    rw [← m.ends x y h hc, chainEnd_eq_getLast, List.getLast_cons hne]
  conv_lhs => rw [← List.dropLast_append_getLast hne, hl]

theorem mem_seg_iff (h : H.Adj x y = true) (hc : m.ord y < m.ord x) {z : G.V} :
    z ∈ m.seg x y ↔ z ∈ (m.seg x y).dropLast ∨ z = m.f y := by
  conv_lhs => rw [m.seg_eq h hc]
  simp

/-- The other orientation of an edge. -/
theorem adj_symm (h : H.Adj x y = true) : H.Adj y x = true := by rw [← H.symm]; exact h

/-- The orientation of an edge the model stores a run for. -/
def canon (m : TopModel H G) (x y : H.V) : H.V × H.V :=
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

theorem canon_comm (h : H.Adj x y = true) : m.canon y x = m.canon x y := by
  rw [canon, canon]
  rcases m.lt_or_lt h with hc | hc
  · rw [if_neg (by omega), if_pos hc]
  · rw [if_pos hc, if_neg (by omega)]

/-- The vertices of `G` a path of the model runs through strictly between its branch vertices. -/
def int (m : TopModel H G) (x y : H.V) : List G.V :=
  (m.seg (m.canon x y).1 (m.canon x y).2).dropLast

theorem int_comm (h : H.Adj x y = true) : m.int y x = m.int x y := by
  rw [int, int, m.canon_comm h]

/-- The walk a canonical run names. -/
def walkSeg (m : TopModel H G) (h : H.Adj x y = true) (hc : m.ord y < m.ord x) :
    G.toSimple.Walk (m.f x) (m.f y) :=
  (walkOfList G (m.f x) (m.seg x y) (m.isWalk x y h hc)).copy rfl (m.ends x y h hc)

@[simp] theorem support_walkSeg (h : H.Adj x y = true) (hc : m.ord y < m.ord x) :
    (m.walkSeg h hc).support = m.f x :: m.seg x y := by
  rw [walkSeg, SimpleGraph.Walk.support_copy, support_walkOfList]

/-- The path of the model between two adjacent branch vertices, in either orientation. -/
def pathOf (m : TopModel H G) (h : H.Adj x y = true) : G.toSimple.Walk (m.f x) (m.f y) :=
  if hc : m.ord y < m.ord x then m.walkSeg h hc
  else (m.walkSeg (adj_symm h) ((m.lt_or_lt h).resolve_left hc)).reverse

theorem mem_support_pathOf (h : H.Adj x y = true) {z : G.V} :
    z ∈ (m.pathOf h).support ↔ z = m.f x ∨ z = m.f y ∨ z ∈ m.int x y := by
  rw [pathOf, int, canon]
  split
  · rename_i hc
    rw [support_walkSeg]
    conv_lhs => rw [List.mem_cons, m.seg_eq h hc]
    simp [or_comm]
  · rename_i hc
    have hc' := (m.lt_or_lt h).resolve_left hc
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, support_walkSeg]
    conv_lhs => rw [List.mem_cons, m.seg_eq (adj_symm h) hc']
    simp [or_comm, or_left_comm]

theorem nodup_support_pathOf (h : H.Adj x y = true) : (m.pathOf h).support.Nodup := by
  rw [pathOf]
  split
  · rw [support_walkSeg]; exact m.nodup x y h (by assumption)
  · rw [SimpleGraph.Walk.support_reverse, List.nodup_reverse, support_walkSeg]
    exact m.nodup y x (adj_symm h) ((m.lt_or_lt h).resolve_left (by assumption))

theorem not_mem_int (h : H.Adj x y = true) (z : H.V) : m.f z ∉ m.int x y :=
  m.interior _ _ (m.canon_adj h) (m.canon_lt h) z

theorem canon_ne (h : H.Adj x y = true) {x' y' : H.V} (h' : H.Adj x' y' = true)
    (hne : s(x, y) ≠ s(x', y')) : m.canon x y ≠ m.canon x' y' := fun e ↦
  hne (by rw [← m.canon_sym h, ← m.canon_sym h', e])

/-- **A list model is a topological minor model.** -/
def toTopMinorOf (m : TopModel H G) : H.TopMinorOf G where
  toFun := m.f
  injective' := m.f_inj
  path h := m.pathOf h
  isPath' h := (SimpleGraph.Walk.isPath_def _).mpr (m.nodup_support_pathOf h)
  reverse' := fun {x y} h h' ↦ by
    simp only [pathOf]
    rcases m.lt_or_lt h with hc | hc
    · rw [dif_pos hc, dif_neg (by omega)]
    · rw [dif_pos hc, dif_neg (by omega), SimpleGraph.Walk.reverse_reverse]
  branch' := fun {x y} h z hz ↦ by
    rcases (m.mem_support_pathOf h).mp hz with he | he | he
    · exact Or.inl (m.f_inj he)
    · exact Or.inr (m.f_inj he)
    · exact absurd he (m.not_mem_int h z)
  disjoint' := fun {x y} h {x' y'} h' hne z hz hz' ↦ by
    rcases (m.mem_support_pathOf h).mp hz with he | he | he
    · exact ⟨x, he⟩
    · exact ⟨y, he⟩
    rcases (m.mem_support_pathOf h').mp hz' with he' | he' | he'
    · exact ⟨x', he'⟩
    · exact ⟨y', he'⟩
    rw [int] at he he'
    exact absurd he' (m.disj _ _ _ _ (m.canon_adj h) (m.canon_lt h) (m.canon_adj h')
      (m.canon_lt h') (by simpa using m.canon_ne h h' hne) z he)

end TopModel
/-- What the run `s` given to the edge from `x` to `y` has to satisfy: it is a walk from the
branch vertex of `x` to that of `y` repeating no vertex, its interior avoids every branch vertex,
and it shares no interior vertex with the run of another edge. -/
def runOk (H G : CGraph) (hs : List H.V) (asg : Asg H G) (x y : H.V) (s : List G.V) : Bool :=
  oriented H hs x y &&
    (branches asg).all (fun p ↦ !decide (p.1 = x) ||
      (isWalkList G p.2 s && decide (p.2 :: s).Nodup &&
        (branches asg).all fun q ↦ !decide (q.1 = y) || decide (chainEnd p.2 s = q.2))) &&
    (branches asg).all (fun p ↦ !s.dropLast.contains p.2) &&
    (runs asg).all fun r ↦ !oriented H hs r.1 r.2.1 || decide (x = r.1 ∧ y = r.2.1) ||
      s.dropLast.all fun z ↦ !r.2.2.dropLast.contains z

/-- **What the search is looking for**: an assignment that places every vertex of `H` at a vertex
of its own, routes every edge, and whose runs are internally disjoint paths avoiding the branch
vertices.  `CGraph.modelOfGoal` turns one into a `CGraph.TopModel`, and hence into a topological
minor model. -/
def goalTop (H G : CGraph) (hs : List H.V) (asg : Asg H G) : Bool :=
  asg.all placeShape &&
    hs.all (fun x ↦ (findB x (branches asg)).isSome) &&
    hs.all (fun x ↦ hs.all fun y ↦ !oriented H hs x y || (findR x y (runs asg)).isSome) &&
    (branches asg).all (fun p ↦ (branches asg).all fun q ↦
      decide (p.1 = q.1) || decide (p.2 ≠ q.2)) &&
    (runs asg).all fun r ↦ runOk H G hs asg r.1 r.2.1 r.2.2

variable {hs : List H.V} {asg : Asg H G}

theorem goalTop_shape (hg : goalTop H G hs asg = true) {x : H.V} {b : List G.V}
    (h : (Task.place x, b) ∈ asg) : ∃ u, b = [u] := by
  simp only [goalTop, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.1.1 _ h
  rw [placeShape, beq_iff_eq] at this
  exact List.length_eq_one_iff.mp this

theorem goalTop_findB (hg : goalTop H G hs asg = true) {x : H.V} (hx : x ∈ hs) :
    (findB x (branches asg)).isSome = true := by
  simp only [goalTop, Bool.and_eq_true, List.all_eq_true] at hg
  exact hg.1.1.1.2 x hx

theorem goalTop_findR (hg : goalTop H G hs asg = true) {x y : H.V} (hx : x ∈ hs) (hy : y ∈ hs)
    (ho : oriented H hs x y = true) : (findR x y (runs asg)).isSome = true := by
  simp only [goalTop, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.1.2 x hx y hy
  simpa [ho] using this

theorem goalTop_inj (hg : goalTop H G hs asg = true) {x y : H.V} {u v : G.V}
    (hp : (x, u) ∈ branches asg) (hq : (y, v) ∈ branches asg) (hxy : x ≠ y) : u ≠ v := by
  simp only [goalTop, Bool.and_eq_true, List.all_eq_true] at hg
  have := hg.1.2 _ hp _ hq
  simpa [hxy] using this

theorem goalTop_runOk (hg : goalTop H G hs asg = true) {x y : H.V} {s : List G.V}
    (hr : (x, y, s) ∈ runs asg) : runOk H G hs asg x y s = true := by
  simp only [goalTop, Bool.and_eq_true, List.all_eq_true] at hg
  exact hg.2 _ hr

variable {x y : H.V} {s : List G.V}

theorem runOk_oriented (h : runOk H G hs asg x y s = true) : oriented H hs x y = true :=
  (Bool.and_eq_true .. ▸ (Bool.and_eq_true .. ▸ (Bool.and_eq_true .. ▸ h).1).1).1

/-- The three conditions on a run that mention its endpoints, read off `runOk` at once. -/
theorem runOk_branch (h : runOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) : isWalkList G u s = true ∧ (u :: s).Nodup ∧
      ∀ {v : G.V}, (y, v) ∈ branches asg → chainEnd u s = v := by
  simp only [runOk, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.1.1.2 _ hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, List.all_eq_true, not_true_eq_false, false_or] at h2
  refine ⟨h2.1.1, h2.1.2, fun {v} hq ↦ ?_⟩
  have h3 := h2.2 _ hq
  simp only [not_true_eq_false, false_or] at h3
  exact h3

theorem runOk_isWalk (h : runOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) : isWalkList G u s = true := (runOk_branch h hp).1

theorem runOk_nodup (h : runOk H G hs asg x y s = true) {u : G.V}
    (hp : (x, u) ∈ branches asg) : (u :: s).Nodup := (runOk_branch h hp).2.1

theorem runOk_ends (h : runOk H G hs asg x y s = true) {u v : G.V}
    (hp : (x, u) ∈ branches asg) (hq : (y, v) ∈ branches asg) : chainEnd u s = v :=
  (runOk_branch h hp).2.2 hq

theorem runOk_interior (h : runOk H G hs asg x y s = true) {z : H.V} {w : G.V}
    (hp : (z, w) ∈ branches asg) : w ∉ s.dropLast := by
  simp only [runOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 _ hp
  simpa using this

theorem runOk_disj (h : runOk H G hs asg x y s = true) {x' y' : H.V} {s' : List G.V}
    (hr : (x', y', s') ∈ runs asg) (ho : oriented H hs x' y' = true) (hne : ¬(x = x' ∧ y = y'))
    {z : G.V} (hz : z ∈ s.dropLast) : z ∉ s'.dropLast := by
  simp only [runOk, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.2 _ hr
  simp only [ho, Bool.not_true, Bool.or_eq_true, Bool.false_or, decide_eq_true_eq,
    List.all_eq_true] at h2
  have h3 := (h2.resolve_left hne) _ hz
  simpa using h3

/-! ## The model a finished assignment describes -/

/-- The branch vertex an assignment the search accepted gives `x`. -/
def branchOf (H G : CGraph) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs) (asg : Asg H G)
    (hg : goalTop H G hs asg = true) (x : H.V) : G.V :=
  (findB x (branches asg)).get (goalTop_findB hg (hmem x))

theorem branchOf_mem (hmem : ∀ x : H.V, x ∈ hs) (hg : goalTop H G hs asg = true) (x : H.V) :
    (x, branchOf H G hs hmem asg hg x) ∈ branches asg := findB_mem (Option.some_get _).symm

theorem runOf_mem (hg : goalTop H G hs asg = true) {x y : H.V} (hx : x ∈ hs) (hy : y ∈ hs)
    (ho : oriented H hs x y = true) : (x, y, runOf asg x y) ∈ runs asg := by
  have hs := goalTop_findR hg hx hy ho
  rw [runOf]
  cases hf : findR x y (runs asg) with
  | none => rw [hf] at hs; exact absurd hs (by simp)
  | some t => rw [Option.getD_some]; exact findR_mem hf

/-- **A finished assignment is a topological minor model.** -/
def modelOfGoal (H G : CGraph) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs) (asg : Asg H G)
    (hg : goalTop H G hs asg = true) : TopModel H G where
  ord x := hs.idxOf x
  ord_inj _ _ h := (List.idxOf_inj (hmem _)).mp h
  f := branchOf H G hs hmem asg hg
  f_inj x y he := by
    by_contra hxy
    exact goalTop_inj hg (branchOf_mem hmem hg x) (branchOf_mem hmem hg y) hxy he
  seg := runOf asg
  isWalk x y hadj hlt :=
    runOk_isWalk (goalTop_runOk hg (runOf_mem hg (hmem x) (hmem y) (oriented_eq_true hadj hlt)))
      (branchOf_mem hmem hg x)
  ends x y hadj hlt :=
    runOk_ends (goalTop_runOk hg (runOf_mem hg (hmem x) (hmem y) (oriented_eq_true hadj hlt)))
      (branchOf_mem hmem hg x) (branchOf_mem hmem hg y)
  nodup x y hadj hlt :=
    runOk_nodup (goalTop_runOk hg (runOf_mem hg (hmem x) (hmem y) (oriented_eq_true hadj hlt)))
      (branchOf_mem hmem hg x)
  interior x y hadj hlt z :=
    runOk_interior (goalTop_runOk hg (runOf_mem hg (hmem x) (hmem y) (oriented_eq_true hadj hlt)))
      (branchOf_mem hmem hg z)
  disj x y x' y' hadj hlt hadj' hlt' hne z hz :=
    runOk_disj (goalTop_runOk hg (runOf_mem hg (hmem x) (hmem y) (oriented_eq_true hadj hlt)))
      (runOf_mem hg (hmem x') (hmem y') (oriented_eq_true hadj' hlt'))
      (oriented_eq_true hadj' hlt') (fun he ↦ hne (by rw [he.1, he.2])) hz

/-! ## The candidates at a step -/

/-- The vertices of `G` that are not available to `x`: the branch vertices of the other vertices
already placed, and the interior of every run already chosen. -/
def usedPlace (H G : CGraph) (hs : List H.V) (x : H.V) (pre : Asg H G) : List G.V :=
  (branches pre).filterMap (fun p ↦ if p.1 = x then none else some p.2) ++
    ((runs pre).filterMap fun r ↦
      if oriented H hs r.1 r.2.1 then some r.2.2.dropLast else none).flatten

/-- The vertices the run of `x`–`y` may not pass through on its way: every branch vertex placed so
far — it ends at one, which `CGraph.routes` allows for — and the interior of every other run. -/
def usedRoute (H G : CGraph) (hs : List H.V) (x y : H.V) (pre : Asg H G) : List G.V :=
  (branches pre).map Prod.snd ++
    ((runs pre).filterMap fun r ↦
      if oriented H hs r.1 r.2.1 ∧ ¬(x = r.1 ∧ y = r.2.1) then some r.2.2.dropLast
      else none).flatten

/-- The values worth trying at a step.  A branch vertex may be any vertex not already spoken for;
a run may be any path between the two branch vertices, already placed, that avoids what is.

The last line is the case where the two ends are *not* already placed.  The search never reaches
it — `CGraph.tasks` routes an edge only after both of its ends — but the definition has to say
something, and saying "every path between every pair of vertices" keeps the pruning sound without
a word about the order the steps come in. -/
def candTop (H G : CGraph) (hs : List H.V) (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (rs : List (Row G)) (gs : List G.V) (nb : G.V → List G.V) (n : ℕ) :
    Task H → Asg H G → List (List G.V)
  | .place x, pre =>
    let used := usedPlace H G hs x pre
    let lo := (symLo H G rank pairs x (branches pre)).foldl max 0
    let dx := H.deg x
    (rs.filter fun p ↦ decide (dx ≤ p.deg) && !used.contains p.vert &&
      decide (lo ≤ rank p.vert)).map fun p ↦ [p.vert]
  | .route x y, pre =>
    match findB x (branches pre), findB y (branches pre) with
    | some u, some v => routes G nb v n u (usedRoute H G hs x y pre)
    | _, _ => gs.flatMap fun u ↦ gs.flatMap fun v ↦ routes G nb v n u []

/-- The whole test the search applies: the model conditions, and the order symmetry breaking
puts on the images of interchangeable vertices.  `CGraph.sortedAsg` is the same test the embedding
search uses, read off the branch entries. -/
def goalSym (H G : CGraph) (hs : List H.V) (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (asg : Asg H G) : Bool :=
  goalTop H G hs asg && sortedAsg H G rank pairs (branches asg) &&
    (branches asg).all fun p ↦ decide (H.deg p.1 ≤ G.deg p.2)

theorem goalSym_goal {rank : G.V → ℕ} {pairs : List (H.V × H.V)}
    (h : goalSym H G hs rank pairs asg = true) : goalTop H G hs asg = true := by
  simp only [goalSym, Bool.and_eq_true] at h; exact h.1.1

theorem goalSym_sorted {rank : G.V → ℕ} {pairs : List (H.V × H.V)}
    (h : goalSym H G hs rank pairs asg = true) :
    sortedAsg H G rank pairs (branches asg) = true := by
  simp only [goalSym, Bool.and_eq_true] at h; exact h.1.2

theorem goalSym_degree {rank : G.V → ℕ} {pairs : List (H.V × H.V)}
    (h : goalSym H G hs rank pairs asg = true) {x : H.V} {u : G.V}
    (hp : (x, u) ∈ branches asg) : H.toSimple.degree x ≤ G.toSimple.degree u := by
  simp only [goalSym, Bool.and_eq_true, List.all_eq_true] at h
  simpa using h.2 _ hp

/-- A run that a finished assignment accepts is one `CGraph.routes` offers. -/
theorem mem_routes_of_runOk {gs : List G.V} (hgs : ∀ v : G.V, v ∈ gs)
    {nb : G.V → List G.V} (hnb : ∀ u w : G.V, G.Adj u w = true → w ∈ nb u)
    (hg : goalTop H G hs asg = true) {x y : H.V} {b : List G.V}
    (hok : runOk H G hs asg x y b = true) {u v : G.V} (hu : (x, u) ∈ branches asg)
    (hv : (y, v) ∈ branches asg) (avoid : List G.V)
    (hav : ∀ w ∈ b.dropLast, w ∉ avoid) : b ∈ routes G nb v gs.length u avoid := by
  have hnd := runOk_nodup hok hu
  have hends := runOk_ends hok hu hv
  refine mem_routes hnb gs.length u avoid b ?_ ?_ (runOk_isWalk hok hu) hends hnd hav
  · rintro rfl
    rw [chainEnd] at hends
    exact goalTop_inj hg hu hv (ne_of_oriented (runOk_oriented hok)) hends
  · have hsub : u :: b ⊆ gs := fun z _ ↦ hgs z
    have := (hnd.subperm hsub).length_le
    rw [List.length_cons] at this
    omega

/-- **The pruning is sound**: a value that occurs in a finished assignment is one the search
offers at that step. -/
theorem mem_candTop {hs : List H.V} (hmem : ∀ x : H.V, x ∈ hs) {gs : List G.V}
    (hgs : ∀ v : G.V, v ∈ gs) {nb : G.V → List G.V}
    (hnb : ∀ u w : G.V, G.Adj u w = true → w ∈ nb u)
    {rank : G.V → ℕ} {pairs : List (H.V × H.V)} (a : Task H)
    (pre : Asg H G) (b : List G.V) (l : Asg H G)
    (hsym : goalSym H G hs rank pairs (l ++ (a, b) :: pre) = true) :
    b ∈ candTop H G hs rank pairs (rowList G gs) gs nb gs.length a pre := by
  have hg := goalSym_goal hsym
  have hsub : pre ⊆ l ++ (a, b) :: pre := fun z hz ↦
    List.mem_append_right _ (List.mem_cons_of_mem _ hz)
  cases a with
  | place x =>
    obtain ⟨u, rfl⟩ := goalTop_shape hg (List.mem_append_right _ (List.mem_cons_self ..))
    have hbu : (x, u) ∈ branches (l ++ (Task.place x, [u]) :: pre) :=
      mem_branches (List.mem_append_right _ (List.mem_cons_self ..))
    have hnu : u ∉ usedPlace H G hs x pre := by
      intro hu
      rcases List.mem_append.mp hu with h1 | h2
      · obtain ⟨p, hp, hpu⟩ := List.mem_filterMap.mp h1
        by_cases hx : p.1 = x
        · rw [if_pos hx] at hpu; exact absurd hpu (by simp)
        · rw [if_neg hx, Option.some_inj] at hpu
          exact goalTop_inj hg hbu (mem_branches_of_subset hsub hp) (fun he ↦ hx he.symm)
            hpu.symm
      · obtain ⟨t, ht, hwt⟩ := List.mem_flatten.mp h2
        obtain ⟨r, hr, hrt⟩ := List.mem_filterMap.mp ht
        by_cases ho : oriented H hs r.1 r.2.1 = true
        · rw [if_pos ho, Option.some_inj] at hrt
          exact runOk_interior (goalTop_runOk hg (mem_runs_of_subset hsub hr)) hbu (hrt ▸ hwt)
        · rw [if_neg ho] at hrt; exact absurd hrt.symm (by simp)
    have hlo : ∀ m ∈ symLo H G rank pairs x (branches pre), m ≤ rank u := by
      intro m hm
      obtain ⟨z, hz, hmz⟩ := List.mem_filterMap.mp hm
      cases hf : (branches pre).find? (fun q ↦ decide (q.1 = z)) with
      | none => rw [hf] at hmz; exact absurd hmz (by simp)
      | some q =>
        rw [hf, Option.map_some, Option.some_inj] at hmz
        have hq1 : q.1 = z := by simpa using List.find?_some hf
        rw [← hmz]
        exact sortedAsg_le H G (goalSym_sorted hsym) (mem_symBefore H hz)
          (mem_branches_of_subset hsub (List.mem_of_find?_eq_some hf)) hbu hq1 rfl
    refine List.mem_map.mpr ⟨row G gs u,
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨u, hgs u, rfl⟩, ?_⟩, rfl⟩
    simp only [row, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
      decide_eq_false_iff_not, decide_eq_true_eq]
    exact ⟨⟨(goalSym_degree hsym hbu).trans (degree_le_row_deg G hgs u), hnu⟩,
      foldl_max_le (Nat.zero_le _) hlo⟩
  | route x y =>
    have hrun : (x, y, b) ∈ runs (l ++ (Task.route x y, b) :: pre) :=
      mem_runs (List.mem_append_right _ (List.mem_cons_self ..))
    have hok := goalTop_runOk hg hrun
    rw [candTop]
    split
    · rename_i u v hfx hfy
      refine mem_routes_of_runOk hgs hnb hg hok (mem_branches_of_subset hsub (findB_mem hfx))
        (mem_branches_of_subset hsub (findB_mem hfy)) _ ?_
      intro w hw hwu
      rcases List.mem_append.mp hwu with h1 | h2
      · obtain ⟨p, hp, hpw⟩ := List.mem_map.mp h1
        exact runOk_interior hok (mem_branches_of_subset hsub hp) (hpw ▸ hw)
      · obtain ⟨t, ht, hwt⟩ := List.mem_flatten.mp h2
        obtain ⟨r, hr, hrt⟩ := List.mem_filterMap.mp ht
        by_cases ho : oriented H hs r.1 r.2.1 = true ∧ ¬(x = r.1 ∧ y = r.2.1)
        · rw [if_pos ho, Option.some_inj] at hrt
          exact runOk_disj hok (mem_runs_of_subset hsub hr) ho.1 ho.2 hw (hrt ▸ hwt)
        · rw [if_neg ho] at hrt; exact absurd hrt.symm (by simp)
    · -- the ends are not both placed yet: fall back on every path between every pair
      obtain ⟨u, hfu⟩ := Option.isSome_iff_exists.mp (goalTop_findB hg (hmem x))
      obtain ⟨v, hfv⟩ := Option.isSome_iff_exists.mp (goalTop_findB hg (hmem y))
      exact List.mem_flatMap.mpr ⟨u, hgs u, List.mem_flatMap.mpr ⟨v, hgs v,
        mem_routes_of_runOk hgs hnb hg hok (findB_mem hfu) (findB_mem hfv) []
          (fun w _ ↦ List.not_mem_nil)⟩⟩

/-! ## The search -/

/-- The assignment a model makes: a branch vertex for each vertex, a run for each oriented edge. -/
def valOfModel (m : TopModel H G) : Task H → List G.V
  | .place x => [m.f x]
  | .route x y => m.seg x y

/-- What the search would have to find, given a model. -/
def asgOfModel (m : TopModel H G) (hs : List H.V) : Asg H G :=
  (tasks H hs).map fun k ↦ (k, valOfModel m k)

theorem val_of_mem_asgOfModel {m : TopModel H G} {hs : List H.V} {k : Task H} {v : List G.V}
    (h : (k, v) ∈ (asgOfModel m hs).reverse) : k ∈ tasks H hs ∧ v = valOfModel m k := by
  rw [asgOfModel, List.mem_reverse, List.mem_map] at h
  obtain ⟨k', hk', he⟩ := h
  rw [Prod.mk.injEq] at he
  exact ⟨he.1 ▸ hk', he.1 ▸ he.2.symm⟩

theorem branch_of_mem_branches {m : TopModel H G} {hs : List H.V} {x : H.V} {u : G.V}
    (h : (x, u) ∈ branches (asgOfModel m hs).reverse) : u = m.f x := by
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp h
  obtain ⟨k, v⟩ := q
  split at hqp
  · rename_i x' u' he
    rw [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨-, hv⟩ := val_of_mem_asgOfModel hq
    rw [valOfModel, List.cons.injEq] at hv
    rw [Option.some_inj, Prod.mk.injEq] at hqp
    rw [← hqp.1, ← hqp.2, hv.1]
  · exact absurd hqp.symm (by simp)

theorem mem_branches_asgOfModel {m : TopModel H G} {hs : List H.V} {x : H.V} (hx : x ∈ hs) :
    (x, m.f x) ∈ branches (asgOfModel m hs).reverse :=
  mem_branches (List.mem_reverse.mpr
    (List.mem_map.mpr ⟨Task.place x, place_mem_tasks hx, rfl⟩))

theorem run_of_mem_runs {m : TopModel H G} {hs : List H.V} {x y : H.V} {s : List G.V}
    (h : (x, y, s) ∈ runs (asgOfModel m hs).reverse) :
    s = m.seg x y ∧ oriented H hs x y = true := by
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp h
  obtain ⟨k, v⟩ := q
  split at hqp
  · rename_i x' y' s' he
    rw [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hk, hv⟩ := val_of_mem_asgOfModel hq
    rw [Option.some_inj, Prod.mk.injEq, Prod.mk.injEq] at hqp
    obtain ⟨rfl, rfl, rfl⟩ := hqp
    exact ⟨hv, oriented_of_route_mem_tasks hk⟩
  · exact absurd hqp.symm (by simp)

theorem mem_runs_asgOfModel {m : TopModel H G} {hs : List H.V} {x y : H.V} (hx : x ∈ hs)
    (hy : y ∈ hs) (ho : oriented H hs x y = true) :
    (x, y, m.seg x y) ∈ runs (asgOfModel m hs).reverse :=
  mem_runs (List.mem_reverse.mpr
    (List.mem_map.mpr ⟨Task.route x y, route_mem_tasks hx hy ho, rfl⟩))

/-- **A model passes every test the search applies.** -/
theorem goalTop_asgOfModel (m : TopModel H G) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs)
    (hord : ∀ x : H.V, m.ord x = hs.idxOf x) :
    goalTop H G hs (asgOfModel m hs).reverse = true := by
  have hlt : ∀ {x y : H.V}, oriented H hs x y = true → m.ord y < m.ord x := fun ho ↦ by
    rw [hord, hord]; exact idxOf_lt_of_oriented ho
  simp only [goalTop, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨fun p hp ↦ ?_, fun x _ ↦ ?_⟩, fun x _ y _ ↦ ?_⟩, fun p hp q hq ↦ ?_⟩, fun r hr ↦ ?_⟩
  · obtain ⟨k, v⟩ := p
    obtain ⟨-, rfl⟩ := val_of_mem_asgOfModel hp
    cases k <;> simp [placeShape, valOfModel]
  · simp [findB_isSome (mem_branches_asgOfModel (hmem x))]
  · by_cases ho : oriented H hs x y = true
    · simp [findR_isSome (mem_runs_asgOfModel (hmem x) (hmem y) ho)]
    · simp [Bool.eq_false_iff.mpr ho]
  · obtain ⟨a, u⟩ := p
    obtain ⟨b, v⟩ := q
    rw [branch_of_mem_branches hp, branch_of_mem_branches hq]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, m.f_inj.ne_iff]
  · obtain ⟨x, y, s⟩ := r
    obtain ⟨rfl, ho⟩ := run_of_mem_runs hr
    have hadj := adj_of_oriented ho
    simp only [runOk, Bool.and_eq_true, List.all_eq_true, ho, true_and]
    refine ⟨⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩, fun r' hr' ↦ ?_⟩
    · obtain ⟨a, u⟩ := p
      rw [branch_of_mem_branches hp]
      by_cases hax : a = x
      · subst hax
        simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
          decide_eq_true_eq, List.all_eq_true]
        refine ⟨⟨m.isWalk _ _ hadj (hlt ho), m.nodup _ _ hadj (hlt ho)⟩, fun q hq ↦ ?_⟩
        obtain ⟨b, v⟩ := q
        rw [branch_of_mem_branches hq]
        by_cases hby : b = y
        · subst hby
          simp [m.ends _ _ hadj (hlt ho)]
        · simp [hby]
      · simp [hax]
    · obtain ⟨a, u⟩ := p
      rw [branch_of_mem_branches hp]
      simpa using m.interior _ _ hadj (hlt ho) a
    · obtain ⟨x', y', s'⟩ := r'
      by_cases ho' : oriented H hs x' y' = true
      · obtain ⟨rfl, -⟩ := run_of_mem_runs hr'
        by_cases hsame : x = x' ∧ y = y'
        · simp [hsame]
        · simp only [ho', Bool.not_true, Bool.false_or, hsame, decide_false, List.all_eq_true]
          intro z hz
          simpa using
            m.disj _ _ _ _ hadj (hlt ho) (adj_of_oriented ho') (hlt ho')
              (fun he ↦ hsame ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩) z hz
      · simp [Bool.eq_false_iff.mpr ho']

/-- And it passes the symmetry test too, once its branch vertices are sorted. -/
theorem goalSym_asgOfModel (m : TopModel H G) (hs : List H.V) (hmem : ∀ x : H.V, x ∈ hs)
    (hord : ∀ x : H.V, m.ord x = hs.idxOf x) (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (hsort : ∀ p ∈ pairs, rank (m.f p.1) ≤ rank (m.f p.2))
    (hdeg : ∀ x : H.V, H.toSimple.degree x ≤ G.toSimple.degree (m.f x)) :
    goalSym H G hs rank pairs (asgOfModel m hs).reverse = true := by
  rw [goalSym, goalTop_asgOfModel m hs hmem hord, Bool.true_and, Bool.and_eq_true]
  constructor
  · rw [sortedAsg, List.all_eq_true]
    intro p hp
    rw [List.all_eq_true]
    rintro ⟨a, u⟩ hq
    rw [List.all_eq_true]
    rintro ⟨c, w⟩ hr
    by_cases ha : a = p.1
    · by_cases hc : c = p.2
      · rw [branch_of_mem_branches hq, branch_of_mem_branches hr]
        simp only [ha, hc, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        exact hsort p hp
      · simp [hc]
    · simp [ha]
  · rw [List.all_eq_true]
    rintro ⟨a, u⟩ hq
    rw [branch_of_mem_branches hq]
    simpa using hdeg a

/-- The assignment the search finds, if there is one. -/
def searchTop (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : Option (Asg H G) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    Backtrack.dfs
      (candTop H G (searchOrder H rH.toList) (hostRank G rG)
        (symPairs H (searchOrder H rH.toList)) (rowList G rG.toList) rG.toList
        (fun u ↦ rG.toList.filter (G.Adj u)) rG.toList.length)
      (goalSym H G (searchOrder H rH.toList) (hostRank G rG)
        (symPairs H (searchOrder H rH.toList)))
      (tasks H (searchOrder H rH.toList)) []
  else none

/-- `CGraph.searchTop` with the neighbour lists tabulated.  Every step of every path asks for the
neighbours of the vertex it stands on, and the path enumeration is nearly all of what the search
costs; filtering `rG.toList` there is a scan of the whole host, per step. -/
def searchTopFast (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : Option (Asg H G) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    let hs := searchOrder H rH.toList
    let gs := rG.toList
    let nb := Backtrack.tabAt (Backtrack.tabulate fun u ↦ gs.filter (G.Adj u))
    Backtrack.dfs
      (candTop H G hs (hostRank G rG) (symPairs H hs) (rowList G gs) gs nb gs.length)
      (goalSym H G hs (hostRank G rG) (symPairs H hs)) (tasks H hs) []
  else none

@[csimp] theorem searchTop_eq_searchTopFast : @searchTop = @searchTopFast := by
  funext H G rH rG
  simp only [searchTop, searchTopFast, Backtrack.tabAt_tabulate]

theorem searchTop_goal {rH : Roster H.V} {rG : Roster G.V} {r : Asg H G}
    (h : searchTop H G rH rG = some r) :
    goalTop H G (searchOrder H rH.toList) r = true := by
  rw [searchTop] at h
  split at h
  · exact goalSym_goal (Backtrack.goal_of_dfs_eq_some h)
  · exact absurd h (by simp)

/-- **Is `H` a topological minor of `G`?**  Returns a model when there is one; see
`isEmpty_topMinorOf_of_eq_none` for the other half of the answer. -/
def findTopMinor (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) :
    Option (H.TopMinorOf G) :=
  Option.pmap (p := fun r ↦ goalTop H G (searchOrder H rH.toList) r = true)
    (fun r hr ↦ (modelOfGoal H G (searchOrder H rH.toList)
      (mem_searchOrder H rH.mem_toList) r hr).toTopMinorOf)
    (searchTop H G rH rG) (fun _ hr ↦ searchTop_goal hr)

theorem findTopMinor_eq_none_iff (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) :
    findTopMinor H G rH rG = none ↔ searchTop H G rH rG = none := Option.pmap_eq_none_iff

/-- **Completeness**: when the search comes back empty, `H` is not a topological minor of `G`. -/
theorem isEmpty_topMinorOf_of_eq_none {H G : CGraph} {rH : Roster H.V} {rG : Roster G.V}
    (h : findTopMinor H G rH rG = none) : IsEmpty (H.TopMinorOf G) := by
  rw [findTopMinor_eq_none_iff, searchTop] at h
  refine ⟨fun t ↦ ?_⟩
  split at h
  · have hmem := mem_searchOrder H rH.mem_toList
    -- the model is first relabelled to one the symmetry test accepts
    obtain ⟨g, hgsort⟩ := exists_sorted_pairs (fun (t : H.TopMinorOf G) ↦ t.toFun)
      (fun t {_σ} hinj hadj ↦ t.exists_reindex hinj hadj) (hs := searchOrder H rH.toList)
      (hostRank G rG) hmem t
    have hinj : Function.Injective fun x : H.V ↦ (searchOrder H rH.toList).idxOf x :=
      fun x y he ↦ (List.idxOf_inj (hmem x)).mp he
    have hsol : (asgOfModel (g.toTopModel _ hinj) (searchOrder H rH.toList)).map Prod.fst
        = tasks H (searchOrder H rH.toList) := by
      rw [asgOfModel, List.map_map]
      exact List.map_id _
    have hn := Backtrack.dfs_eq_none (mem_candTop hmem rG.mem_toList
      (fun u w hadj ↦ List.mem_filter.mpr ⟨rG.mem_toList w, hadj⟩)) h hsol
    rw [List.append_nil,
      goalSym_asgOfModel _ _ hmem (fun _ ↦ rfl) _ _ hgsort (fun x ↦ g.degree_le x)] at hn
    exact absurd hn (by simp)
  · exact absurd (show FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E from
      ⟨FinEnum.card_le_of_injective _ t.injective, t.E_le⟩) ‹_›

/-- `H` is a topological minor of `G` exactly when the search finds a model. -/
theorem isEmpty_topMinorOf_iff (H G : CGraph) (rH : Backtrack.Roster H.V)
    (rG : Backtrack.Roster G.V) :
    IsEmpty (H.TopMinorOf G) ↔ findTopMinor H G rH rG = none := by
  refine ⟨fun hemp ↦ ?_, isEmpty_topMinorOf_of_eq_none⟩
  rcases hm : findTopMinor H G rH rG with _ | f
  · rfl
  · exact (hemp.false f).elim

end CGraph
