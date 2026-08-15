import IsoGraph.Containment.Minors
import IsoGraph.Containment.Algorithms.Backtrack

/-!
# Searching for a minor

`CGraph.findMinor H G rH rG` looks for `H` as a minor of `G`: a family of disjoint connected
*branch sets* in `G`, one for each vertex of `H`, with an edge of `G` between two of them whenever
there is an edge of `H`.  Like the induced subgraph search it does not return a `Bool`: when it
succeeds it returns the witness itself, an `H.MinorOf G`, and when it fails,
`isEmpty_minorOf_of_findMinor_eq_none` says there was nothing to find.  `rH` and `rG` are
`Backtrack.Roster`s; for a graph on `Fin n`, `Backtrack.Roster.fin n` is the one to use.

## What is searched over

A minor is a partial map `G.V → Option H.V` with connected fibres, so the naive search would be
over `(card H.V + 1) ^ card G.V` maps, with connectivity only testable at the very end.  Instead
the search builds the branch sets *one vertex at a time, in chain order*: `CGraph.ChainConn` says
that every vertex of a list is adjacent to one occurring later in it, which by
`CGraph.connectedOn_of_chainConn` makes the list connected, and by `CGraph.exists_pickChain` every
connected set can be listed that way.  Connectivity therefore holds by construction, and the
search never visits a partial assignment that is not extendable to connected sets.

The state (`MinorSearch.State`) is: the vertices of `H` still to be given a set, the set currently
being built, the sets already finished, and the vertices of `G` still unused.  There are two moves
(`MinorSearch.step`):

* `pick v` — add an unused `v` to the current set, which must be adjacent to something already in
  it and must come in the canonical order described below, or start the next set with `v`;
* `stop` — declare the current set finished.

`stop` is where most of the pruning lives, because a finished set is the last chance to reject it:

* every finished set that `H` requires to be adjacent to this one must actually have an edge to
  it — the sets are complete, so this test is final;
* there must be at least as many unused vertices left as there are vertices of `H` left, since the
  branch sets are disjoint and nonempty;
* each vertex of `H` still waiting for a set and adjacent to the one just finished must put a
  vertex of its own set next to this one, and those vertices are all different because the branch
  sets are (`MinorSearch.countP_le_flatMap`).  So the finished set needs at least that many unused
  neighbours.  In a host of maximum degree `d` this alone rules out every set of size `k` with
  fewer than `deg_H x` boundary vertices, which is what makes `K5` in a cubic graph cheap.

Starting a set is pruned too:

* `MinorSearch.attOf` — the seed must be adjacent to the branch set of the last-placed neighbour
  of its vertex, if there is one.  The seed is the least vertex of the set, so it can be pinned
  down only up to which finished set it has to touch, and this is the one the search knows about;
* `MinorSearch.feasibleSeed` — a set that must touch the new one is confined to the component of
  the seed in what is left (`CGraph.seedReach`), so if from there it cannot reach the finished sets
  it is also required to touch, the seed is hopeless.  This is what stops the search from starting
  a set in a corner of the host it can never get back from.

Two counting tests, `card H.V ≤ card G.V` and `H.E ≤ G.E`, reject hopeless pairs before the search
starts, and `CGraph.hsOrder` places the vertices of `H` in an order that keeps them connected as
they go, so that the seed rules above have something to bite on as early as possible.

## Shrinking the host

`CGraph.hostPool` throws away, before the search starts, the vertices of `G` that no branch set
could use.  When every vertex of `H` has two neighbours — `CGraph.minDegTwo`, which is the case for
every `H` one asks about in practice — a vertex of `G` with at most one neighbour left is in no
branch set at all: a set containing it and something else has it as a leaf that nothing needs, and
a set consisting of it alone would force the branch sets of two different neighbours of its vertex
to meet its one neighbour.  Deleting such a vertex can create another, so the peeling runs to a
fixed point and leaves the *two-core* (`CGraph.twoCore`); `CGraph.exists_model_twoCore` proves that
no model is lost.

A forest peels away completely, so asking whether a graph is a forest by asking for a `C₃` minor
costs no search at all.

The whole thing runs on `Backtrack.dfs` with `α = Unit` and the state itself for the value, over a
`todo` of fixed length `card G.V + card H.V` — the largest number of moves a successful run can
take, padded out with `stop`s once everything is placed.  A leaf of the search is therefore always
a complete model, so `goal` — which re-checks the chain of states and then everything a minor
needs, from scratch — is evaluated rarely and can afford to be expensive.  That is what makes the
correctness proof cheap: soundness (`MinorSearch.ofFinal`) reads only the final state, and the
pruning is discharged by `Backtrack.dfs_eq_none`'s single obligation, which here is the
observation that a state in a chain is by definition a candidate of its predecessor.

## One order per set

A set of size `k` has `k!` orders, so enumerating orders rather than sets would cost a factor of
`k!` per branch set.  `CGraph.PickChain` cuts that down to one order per set, using the position
`rank v` of a vertex in the roster as a tie-break: a vertex may be added to `u :: T` only when

* it is adjacent to something already there — the connectivity requirement;
* if it could have been the seed at all, it does not come before the vertex `T.getLastD u` the set
  actually was seeded at — this forces the seed to be the least vertex that the seed rule allows,
  not the least vertex outright, which is what lets `MinorSearch.attOf` restrict the seed to the
  neighbourhood of an already-placed set;
* it does not come before the previous pick `u`, unless `u` is the only reason it is adjacent to
  the set at all — the exception is what lets the order follow a growing frontier.

`CGraph.exists_pickChain` proves nothing is lost: greedily taking the least vertex on the frontier,
starting from the least *admissible* vertex of the set, always produces a legal order.  This needs
no assumption on `rank` or on the seed predicate whatsoever, so the search is free to choose them;
it uses the roster order, and admissibility is `attOf`.

## What it costs

The search is exponential — the problem is NP-hard — and what it costs depends much more on the
*answer* than on the size.  Finding a model is quick, because the pruning above leaves few ways to
start: `K5` in the Heawood graph takes 15 ms, `K3,3` in it 2 ms, `K5` in the 24-vertex McGee graph
35 ms, `C100` gives up a `C3` in 200 ms.  Trees and near-trees are answered by the peeling above
rather than by search: a `C3` in a path of 120 vertices, in a 13-vertex star or in a spider takes
no measurable time, and in a 40-cycle with a 40-vertex tail 0.8 s.

Ruling a minor out of a host with no vertices to peel is the expensive direction, since every
family of disjoint connected sets has to be looked at: `K5` in the 4×4 grid takes about four
minutes and `K3,3` in it three times that.

The obvious thing still missing is symmetry breaking.  Nothing stops the search from trying all
`5!` orders of the five branch sets of a `K5`, and for a negative answer it does try them all.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {G : CGraph}

/-! ## Reachability -/

/-- One round of `reach` per unit of fuel: everything next to the newest arrivals joins them.
Only the newest are looked at — everything else has had its neighbours taken already — so a round
costs one pass over the pool rather than one per vertex in hand. -/
def reachAux (G : CGraph) : ℕ → List G.V → List G.V → List G.V → List G.V
  | 0, S, _, _ => S
  | n + 1, S, front, pool =>
    if (pool.filter fun v ↦ front.any (G.Adj v)).isEmpty then S
    else reachAux G n ((pool.filter fun v ↦ front.any (G.Adj v)) ++ S)
      (pool.filter fun v ↦ front.any (G.Adj v)) (pool.filter fun v ↦ !front.any (G.Adj v))

/-- The vertices that `S` can reach without leaving `S ∪ pool`: the component of `S` in the
subgraph induced on those vertices.  Each round takes at least one vertex out of the pool, so
`pool.length` rounds are enough. -/
def reach (G : CGraph) (S pool : List G.V) : List G.V := reachAux G pool.length S S pool

theorem mem_reachAux_of_mem : ∀ (n : ℕ) (S front pool : List G.V) {v : G.V}, v ∈ S →
    v ∈ reachAux G n S front pool
  | 0, _, _, _, _, h => h
  | n + 1, S, front, pool, v, h => by
    rw [reachAux]
    split
    · exact h
    · exact mem_reachAux_of_mem n _ _ _ (List.mem_append_right _ h)

theorem mem_reach_of_mem {S pool : List G.V} {v : G.V} (h : v ∈ S) : v ∈ reach G S pool :=
  mem_reachAux_of_mem _ _ _ _ h

/-- Nothing outside the component is next to it: this is what makes `reach` a *whole* component,
and it is the only thing the search needs from it.  The invariant is what makes the frontier
enough: a vertex still in the pool can only be next to the newest arrivals. -/
theorem mem_reachAux_of_adj : ∀ (n : ℕ) (S front pool : List G.V), pool.length ≤ n →
    (∀ v ∈ pool, ∀ u ∈ S, G.Adj v u = true → u ∈ front) →
    ∀ {v u : G.V}, v ∈ pool → u ∈ reachAux G n S front pool → G.Adj v u = true →
      v ∈ reachAux G n S front pool
  | 0, _, _, pool, hlen, _, v, _, hv, _, _ => by
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)] at hv
    simp at hv
  | n + 1, S, front, pool, hlen, hinv, v, u, hv, hu, hadj => by
    rw [reachAux] at hu ⊢
    split at hu
    · rename_i hnil
      exact absurd (List.mem_filter.mpr ⟨hv, List.any_eq_true.mpr ⟨u, hinv v hv u hu hadj, hadj⟩⟩)
        (by rw [List.isEmpty_iff.mp hnil]; simp)
    · rename_i hnil
      rw [if_neg hnil]
      cases hva : front.any (G.Adj v)
      · refine mem_reachAux_of_adj n _ _ _ ?_ ?_
          (List.mem_filter.mpr ⟨hv, by simp [hva]⟩) hu hadj
        · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil (pool.filter fun v ↦ front.any (G.Adj v))
            fun hn ↦ hnil (by rw [hn]; rfl)
          obtain ⟨hwp, hwa⟩ := List.mem_filter.mp hw
          have := List.length_filter_lt_length_iff_exists (l := pool)
            (p := fun v ↦ !front.any (G.Adj v)) |>.mpr ⟨w, hwp, by simpa using hwa⟩
          omega
        · intro w hw z hz hwz
          rcases List.mem_append.mp hz with hz | hz
          · exact hz
          · obtain ⟨-, hwf⟩ := List.mem_filter.mp hw
            simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hwf
            exact absurd hwz (by simpa using hwf z (hinv w (List.mem_filter.mp hw).1 z hz hwz))
      · exact mem_reachAux_of_mem n _ _ _ (List.mem_append_left _
          (List.mem_filter.mpr ⟨hv, hva⟩))

theorem mem_reach_of_adj {S pool : List G.V} {v u : G.V} (hv : v ∈ pool)
    (hu : u ∈ reach G S pool) (hadj : G.Adj v u = true) : v ∈ reach G S pool :=
  mem_reachAux_of_adj _ _ _ _ le_rfl (fun _ _ _ h _ ↦ h) hv hu hadj

/-- **A connected set that meets the component is inside it.**  If the search has a foothold in a
connected set and the rest of the set is still available, the whole set is in what it can reach. -/
theorem subset_reach {s : Set G.V} (hs : G.ConnectedOn s) {S pool : List G.V}
    (hsub : ∀ v ∈ s, v ∈ S ∨ v ∈ pool) (hmeet : ∃ u ∈ s, u ∈ reach G S pool) :
    ∀ v ∈ s, v ∈ reach G S pool := by
  intro w hw
  by_contra hwR
  obtain ⟨u, hus, huR⟩ := hmeet
  obtain ⟨a, ha, b, hb, hbt, hab⟩ :=
    hs.exists_adj_of_ssubset (t := {z | z ∈ reach G S pool ∧ z ∈ s})
      (fun z hz ↦ hz.2) ⟨huR, hus⟩ hw (fun h ↦ hwR h.1)
  have hbR : b ∉ reach G S pool := fun h ↦ hbt ⟨h, hb⟩
  have hbp : b ∈ pool := ((hsub b hb).resolve_left fun h ↦ hbR (mem_reach_of_mem h))
  exact hbR (mem_reach_of_adj hbp ha.1 (by rw [G.symm b a]; exact hab))

/-- What a branch set started at `v` leaves for the sets that come after it: the component of `v`
in what is left of the host, with `v` itself dropped.  A set that has to touch `v`'s own set is
joined to `v` through vertices that are still available, so it lies in here. -/
def seedReach (G : CGraph) (v : G.V) (avail : List G.V) : List G.V :=
  (reach G [v] (avail.erase v)).filter fun u ↦ decide (u ≠ v)

/-- **A set that must touch the seed's set stays within `seedReach`.**  `sx` is the set being
started at `v`, `sz` one that has to touch it; both are still to be built out of `avail`. -/
theorem subset_seedReach {sx sz : Set G.V} (hx : G.ConnectedOn sx) (hz : G.ConnectedOn sz)
    {v : G.V} {avail : List G.V} (hnd : avail.Nodup) (hv : v ∈ sx)
    (hxa : ∀ u ∈ sx, u ∈ avail) (hza : ∀ u ∈ sz, u ∈ avail) (hvz : v ∉ sz)
    {a b : G.V} (ha : a ∈ sz) (hb : b ∈ sx) (hab : G.Adj a b) :
    ∀ u ∈ sz, u ∈ seedReach G v avail := by
  have herase : ∀ u, u ∈ avail → u ≠ v → u ∈ avail.erase v :=
    fun u hu hne ↦ (hnd.mem_erase_iff).mpr ⟨hne, hu⟩
  have hxR : ∀ u ∈ sx, u ∈ reach G [v] (avail.erase v) := by
    refine subset_reach hx (fun u hu ↦ ?_) ⟨v, hv, mem_reach_of_mem (by simp)⟩
    by_cases huv : u = v
    · exact Or.inl (by simp [huv])
    · exact Or.inr (herase u (hxa u hu) huv)
  have haR : a ∈ reach G [v] (avail.erase v) :=
    mem_reach_of_adj (herase a (hza a ha) fun h ↦ hvz (h ▸ ha)) (hxR b hb) hab
  have hzR : ∀ u ∈ sz, u ∈ reach G [v] (avail.erase v) :=
    subset_reach hz (fun u hu ↦ Or.inr (herase u (hza u hu) fun h ↦ hvz (h ▸ hu))) ⟨a, ha, haR⟩
  refine fun u hu ↦ List.mem_filter.mpr ⟨hzR u hu, ?_⟩
  simp only [decide_eq_true_eq]
  rintro rfl
  exact hvz hu

/-- A list is chain-connected when every vertex after the first is adjacent to one of the later
ones — that is, when reading it from the right builds a connected set one vertex at a time. -/
def ChainConn (G : CGraph) : List G.V → Bool
  | [] => false
  | v :: rest => rest.isEmpty || (rest.any (G.Adj v) && ChainConn G rest)

theorem chainConn_ne_nil {l : List G.V} (h : ChainConn G l = true) : l ≠ [] := by
  rintro rfl; simp [ChainConn] at h

theorem connectedOn_of_chainConn : ∀ {l : List G.V}, ChainConn G l = true →
    G.ConnectedOn {v | v ∈ l}
  | [], h => by simp [ChainConn] at h
  | v :: rest, h => by
    rw [ChainConn, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl : rest = [] := List.isEmpty_iff.mp h
      have : {u : G.V | u ∈ [v]} = {v} := by ext u; simp
      rw [this]
      exact connectedOn_singleton G v
    · rw [Bool.and_eq_true, List.any_eq_true] at h
      obtain ⟨⟨u, hu, hvu⟩, hrest⟩ := h
      have hset : {u : G.V | u ∈ v :: rest} = insert v {u : G.V | u ∈ rest} := by
        ext u; simp [List.mem_cons, Set.mem_insert_iff]
      rw [hset]
      exact (connectedOn_of_chainConn hrest).insert hu hvu

/-- A list is a *legal* pick order for the search when it is a record of building the set one
vertex at a time: each vertex is adjacent to the ones after it, and — this is the part that keeps
the same set from being built in all `k!` of its orders — it comes no earlier in the search order
`rank` than the vertex added just before it, unless that vertex is what made it adjacent to the
set at all.

`att` marks the vertices the set is *allowed to start at*: the seed must be one of them, and the
seed is the least-ranked of them in the set.  Vertices outside `att` are unconstrained by the seed
rule, since making them the seed was never an option. -/
def PickChain (G : CGraph) (rank : G.V → ℕ) (att : G.V → Bool) : List G.V → Bool
  | [] => false
  | [v] => att v
  | v :: u :: T =>
    (u :: T).any (G.Adj v) && (!att v || decide (rank (T.getLastD u) ≤ rank v)) &&
      (decide (rank u ≤ rank v) || !T.any (G.Adj v)) && PickChain G rank att (u :: T)

theorem pickChain_ne_nil {rank : G.V → ℕ} {att : G.V → Bool} {l : List G.V}
    (h : PickChain G rank att l = true) : l ≠ [] := by
  rintro rfl; simp [PickChain] at h

theorem chainConn_of_pickChain {rank : G.V → ℕ} {att : G.V → Bool} :
    ∀ {l : List G.V}, PickChain G rank att l = true → ChainConn G l = true
  | [], h => by simp [PickChain] at h
  | [_], _ => by simp [ChainConn]
  | _ :: u :: T, h => by
    rw [PickChain, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    rw [ChainConn]
    simp only [List.isEmpty_cons, Bool.false_or, Bool.and_eq_true]
    exact ⟨h.1.1.1, chainConn_of_pickChain h.2⟩

/-- The greedy step: taking always the frontier vertex of least `rank` keeps the order legal.
`u :: T` is what has been picked so far, `R` what is left of the graph. -/
theorem exists_pickChain_aux {s : Set G.V} (hs : G.ConnectedOn s) [DecidablePred (· ∈ s)]
    (rank : G.V → ℕ) (att : G.V → Bool) :
    ∀ (n : ℕ) (u : G.V) (T R : List G.V), (u :: T).Nodup → (∀ v ∈ u :: T, v ∈ s) →
      PickChain G rank att (u :: T) = true → (∀ v ∈ s, v ∈ u :: T ∨ v ∈ R) →
      (∀ v ∈ R, v ∉ u :: T) → R.length ≤ n →
      (∀ w ∈ s, att w = true → rank (T.getLastD u) ≤ rank w) →
      (∀ w ∈ s, w ∉ u :: T → T.any (G.Adj w) = true → rank u ≤ rank w) →
      ∃ l : List G.V, l.Nodup ∧ (∀ v, v ∈ l ↔ v ∈ s) ∧ PickChain G rank att l = true := by
  intro n
  induction n with
  | zero =>
    intro u T R hnd hsub hpc hcov _ hlen _ _
    obtain rfl : R = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    exact ⟨u :: T, hnd, fun v ↦ ⟨hsub v, fun hv ↦ (hcov v hv).resolve_right (by simp)⟩, hpc⟩
  | succ n ih =>
    intro u T R hnd hsub hpc hcov hdisj hlen hseed hmin
    by_cases hdone : ∀ v ∈ s, v ∈ u :: T
    · exact ⟨u :: T, hnd, fun v ↦ ⟨hsub v, fun hv ↦ hdone v hv⟩, hpc⟩
    push_neg at hdone
    obtain ⟨w, hws, hwl⟩ := hdone
    have hmemF : ∀ v, v ∈ R.filter (fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)) ↔
        (v ∈ R ∧ v ∈ s ∧ (u :: T).any (G.Adj v) = true) := by
      intro v; rw [List.mem_filter]; simp
    have hFne : R.filter (fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)) ≠ [] := by
      obtain ⟨a, ha, b, hbs, hbl, hab⟩ :=
        hs.exists_adj_of_ssubset (t := {v | v ∈ u :: T}) hsub (List.mem_cons_self ..) hws hwl
      intro hnil
      have hb := (hmemF b).mpr ⟨(hcov b hbs).resolve_left hbl, hbs,
        List.any_eq_true.mpr ⟨a, ha, by rw [G.symm b a]; exact hab⟩⟩
      rw [hnil] at hb
      simp at hb
    obtain ⟨b, hb⟩ : ∃ b, (R.filter fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)).argmin
        rank = some b := by
      cases hA : (R.filter fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)).argmin rank with
      | none => exact absurd (List.argmin_eq_none.mp hA) hFne
      | some b => exact ⟨b, rfl⟩
    obtain ⟨hbR, hbs, hbadj⟩ := (hmemF b).mp (List.argmin_mem hb)
    have hbl : b ∉ u :: T := hdisj b hbR
    refine ih b (u :: T) (R.filter fun v ↦ decide (v ≠ b))
      (List.nodup_cons.mpr ⟨hbl, hnd⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hbs
      · exact hsub v hv
    · rw [PickChain, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨⟨hbadj, ?_⟩, ?_⟩, hpc⟩
      · cases hatt : att b
        · simp
        · simpa using hseed b hbs hatt
      · cases hT : T.any (G.Adj b)
        · simp
        · simp [hmin b hbs hbl hT]
    · intro v hv
      rcases hcov v hv with hvl | hvR
      · exact Or.inl (List.mem_cons_of_mem _ hvl)
      · by_cases hvb : v = b
        · exact Or.inl (hvb ▸ List.mem_cons_self ..)
        · exact Or.inr (List.mem_filter.mpr ⟨hvR, by simpa using hvb⟩)
    · intro v hv
      obtain ⟨hvR, hvb⟩ := List.mem_filter.mp hv
      simp only [decide_eq_true_eq] at hvb
      rw [List.mem_cons, not_or]
      exact ⟨hvb, hdisj v hvR⟩
    · have : (R.filter fun v ↦ decide (v ≠ b)).length < R.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨b, hbR, by simp⟩
      omega
    · rw [List.getLastD_cons]; exact hseed
    · intro z hzs hzl hzadj
      simp only [List.mem_cons, not_or] at hzl
      exact List.le_of_mem_argmin
        ((hmemF z).mpr ⟨(hcov z hzs).resolve_left (by simp [hzl.2.1, hzl.2.2]), hzs, hzadj⟩) hb

/-- **A connected set can be enumerated in a legal pick order.**  This is what makes the search's
canonicalisation of the order lose nothing: whatever the branch sets of a minor are, there is a
run of the search that builds them.  The one thing asked of `att` is that the set contains a
vertex the search would let it start at. -/
theorem exists_pickChain {s : Set G.V} [DecidablePred (· ∈ s)] (hs : G.ConnectedOn s)
    (rank : G.V → ℕ) (att : G.V → Bool) (gs : List G.V) (hgs : ∀ v ∈ s, v ∈ gs)
    (hatt : ∃ v ∈ s, att v = true) :
    ∃ l : List G.V, l.Nodup ∧ (∀ v, v ∈ l ↔ v ∈ s) ∧ PickChain G rank att l = true := by
  obtain ⟨u₀, hu₀, hu₀a⟩ := hatt
  have hne : gs.filter (fun z ↦ decide (z ∈ s) && att z) ≠ [] := by
    intro hnil
    have : u₀ ∈ gs.filter fun z ↦ decide (z ∈ s) && att z :=
      List.mem_filter.mpr ⟨hgs u₀ hu₀, by simp [hu₀, hu₀a]⟩
    rw [hnil] at this
    simp at this
  obtain ⟨u, hu⟩ : ∃ u, (gs.filter fun z ↦ decide (z ∈ s) && att z).argmin rank = some u := by
    cases hA : (gs.filter fun z ↦ decide (z ∈ s) && att z).argmin rank with
    | none => exact absurd (List.argmin_eq_none.mp hA) hne
    | some u => exact ⟨u, rfl⟩
  obtain ⟨hus, hua⟩ : u ∈ s ∧ att u = true := by
    simpa using (List.mem_filter.mp (List.argmin_mem hu)).2
  have hmin : ∀ w ∈ s, att w = true → rank u ≤ rank w := fun w hw hwa ↦
    List.le_of_mem_argmin (List.mem_filter.mpr ⟨hgs w hw, by simp [hw, hwa]⟩) hu
  refine exists_pickChain_aux hs rank att (gs.filter fun v ↦ decide (v ≠ u)).length u []
    (gs.filter fun v ↦ decide (v ≠ u)) (by simp) ?_ hua ?_ ?_ le_rfl hmin (by simp)
  · intro v hv; rw [List.mem_singleton] at hv; exact hv ▸ hus
  · intro v hv
    by_cases hvu : v = u
    · exact Or.inl (by simp [hvu])
    · exact Or.inr (List.mem_filter.mpr ⟨hgs v hv, by simpa using hvu⟩)
  · intro v hv
    have := (List.mem_filter.mp hv).2
    simp only [decide_eq_true_eq] at this
    simpa using this

/-- A legal pick order records the vertex the set was seeded at as its last entry, and the seed
satisfies `att`. -/
theorem att_getLast_of_pickChain {rank : G.V → ℕ} {att : G.V → Bool} :
    ∀ {l : List G.V}, PickChain G rank att l = true → ∀ u, l.getLast? = some u → att u = true
  | [], h, _, _ => by simp [PickChain] at h
  | [v], h, u, hu => by
    rw [PickChain] at h
    rw [List.getLast?_singleton] at hu
    exact Option.some_inj.mp hu ▸ h
  | _ :: w :: T, h, u, hu => by
    rw [PickChain, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    exact att_getLast_of_pickChain h.2 u (by rwa [List.getLast?_cons_cons] at hu)

/-- **Deleting a leaf of a chain keeps it a chain.**  If `v` is not the vertex the list was seeded
at, and the only vertex of the list it is adjacent to is that seed — which comes after it — then
nothing in the list was relying on `v`, so dropping it leaves the rest connected. -/
theorem chainConn_filter_ne (v : G.V) : ∀ {l : List G.V} {u : G.V}, ChainConn G l = true →
    l.Nodup → l.getLast? = some u → v ≠ u → (∀ w ∈ l, G.Adj v w = true → w = u) →
      ChainConn G (l.filter fun z ↦ decide (z ≠ v)) = true
  | [], _, h, _, _, _, _ => by simp [ChainConn] at h
  | [a], u, _, _, hlast, hvu, _ => by
    rw [List.getLast?_singleton, Option.some_inj] at hlast
    subst hlast
    rw [List.filter_cons_of_pos (by simpa using fun e ↦ hvu e.symm)]
    simp [ChainConn]
  | a :: b :: T, u, h, hnd, hlast, hvu, honly => by
    rw [ChainConn, List.isEmpty_cons, Bool.false_or, Bool.and_eq_true] at h
    rw [List.getLast?_cons_cons] at hlast
    have hu : u ∈ b :: T := List.mem_of_getLast? hlast
    have ih := chainConn_filter_ne v h.2 (List.Nodup.of_cons hnd) hlast hvu
      (fun w hw ↦ honly w (List.mem_cons_of_mem _ hw))
    by_cases hav : a = v
    · rw [List.filter_cons_of_neg (by simpa using hav)]
      exact ih
    · rw [List.filter_cons_of_pos (by simpa using hav)]
      obtain ⟨w, hw, haw⟩ := List.any_eq_true.mp h.1
      have hwv : w ≠ v := by
        rintro rfl
        have : a = u := honly a (List.mem_cons_self ..) (by rw [G.symm]; exact haw)
        exact (List.nodup_cons.mp hnd).1 (this ▸ hu)
      rw [ChainConn, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨List.any_eq_true.mpr
        ⟨w, List.mem_filter.mpr ⟨hw, by simpa using hwv⟩, haw⟩, ih⟩

/-! ## Shrinking the host

A vertex of the host with at most one neighbour left in the pool cannot be used by a model of a
graph whose every vertex has two neighbours of its own, so it — and then whatever it was propping
up — can be deleted before the search starts.  For a forest this deletes everything, which is what
makes "is this graph a forest?", asked as "is `C₃` a minor of it?", cheap. -/

section Shrink

/-- Two different vertices of a list satisfying a predicate make its count at least two. -/
theorem two_le_countP {l : List G.V} {p : G.V → Bool} {a b : G.V} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (hpa : p a = true) (hpb : p b = true) : 2 ≤ l.countP p := by
  have hsub : ([a, b] : List G.V).Subperm (l.filter p) := by
    refine List.Nodup.subperm (by simp [hab]) ?_
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_filter.mpr ⟨ha, hpa⟩
    · rw [List.mem_singleton] at hc
      exact hc ▸ List.mem_filter.mpr ⟨hb, hpb⟩
  simpa [List.countP_eq_length_filter] using hsub.length_le

variable (G) in
/-- A vertex of the pool with at most one neighbour in it, if there is one. -/
def lowDeg (gs : List G.V) : Option G.V :=
  gs.find? fun v ↦ decide (gs.countP (G.Adj v) ≤ 1)

variable (G) in
/-- The *two-core* of the pool: peel vertices of pool-degree at most one, one per unit of fuel,
until none is left.  Fuel of `gs.length` is always enough, since each round removes a vertex. -/
def twoCore : ℕ → List G.V → List G.V
  | 0, gs => gs
  | n + 1, gs =>
    match lowDeg G gs with
    | none => gs
    | some v => twoCore n (gs.erase v)

theorem twoCore_nodup : ∀ (n : ℕ) {gs : List G.V}, gs.Nodup → (twoCore G n gs).Nodup
  | 0, _, h => h
  | n + 1, gs, h => by
    rw [twoCore]
    cases hlow : lowDeg G gs with
    | none => exact h
    | some v => exact twoCore_nodup n (h.erase v)

theorem twoCore_subset : ∀ (n : ℕ) {gs : List G.V} {v : G.V}, v ∈ twoCore G n gs → v ∈ gs
  | 0, _, _, h => h
  | n + 1, gs, v, h => by
    rw [twoCore] at h
    cases hlow : lowDeg G gs with
    | none => rwa [hlow] at h
    | some w =>
      rw [hlow] at h
      exact List.mem_of_mem_erase (twoCore_subset n h)

variable {H : CGraph}

/-- **A vertex with at most one neighbour left is of no use.**  If every vertex of `H` has two
neighbours, then a model of `H` inside `gs` can be pushed off any vertex `v` of pool-degree at
most one: `v`'s branch set, if it has one, has another vertex, so `v` is a leaf of it and no edge
of `H` runs through `v`. -/
theorem exists_model_erase (hH : ∀ x : H.V, ∃ y z, y ≠ z ∧ H.Adj x y = true ∧ H.Adj x z = true)
    (f : H.MinorOf G) {gs : List G.V}
    (hsupp : ∀ (w : G.V) (x : H.V), f.branch w = some x → w ∈ gs)
    {v : G.V} (hv : gs.countP (G.Adj v) ≤ 1) :
    ∃ g : H.MinorOf G, ∀ (w : G.V) (x : H.V), g.branch w = some x → w ∈ gs.erase v := by
  have huniq : ∀ w ∈ gs, ∀ w' ∈ gs, G.Adj v w = true → G.Adj v w' = true → w = w' := by
    intro w hw w' hw' hvw hvw'
    by_contra hne
    exact absurd hv (by have := two_le_countP hne hw hw' hvw hvw'; omega)
  cases hbv : f.branch v with
  | none =>
    refine ⟨f, fun w x hw ↦ ?_⟩
    have hwv : w ≠ v := by rintro rfl; rw [hbv] at hw; exact absurd hw (by simp)
    exact (List.mem_erase_of_ne hwv).mpr (hsupp w x hw)
  | some x =>
    -- `v`'s branch set has a second vertex, since otherwise `v` alone would have to meet the two
    -- branch sets of `x`'s two neighbours.
    obtain ⟨q, hqs, hqv⟩ : ∃ q, f.branch q = some x ∧ q ≠ v := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨y, z, hyz, hxy, hxz⟩ := hH x
      obtain ⟨a, b, ha, hb, hab⟩ := f.map_adj hxy
      obtain ⟨a', b', ha', hb', hab'⟩ := f.map_adj hxz
      have hbb' : b ≠ b' := by
        rintro rfl
        exact hyz (Option.some_inj.mp (hb.symm.trans hb'))
      rw [hcon a ha] at hab
      rw [hcon a' ha'] at hab'
      exact absurd hv (by
        have := two_le_countP hbb' (hsupp b y hb) (hsupp b' z hb') hab hab'; omega)
    -- so `v` has a neighbour `u` inside its own branch set, and that is its only neighbour left.
    obtain ⟨p, hp, u, hus, hut, hpu⟩ := (f.connectedOn x).exists_adj_of_ssubset
      (t := {v}) (fun w hw ↦ by rw [Set.mem_singleton_iff] at hw; exact hw ▸ hbv)
      (Set.mem_singleton v) hqs hqv
    rw [Set.mem_singleton_iff] at hp
    rw [hp] at hpu
    have hun : u ∈ gs := hsupp u x hus
    have hvu : v ≠ u := fun e ↦ hut (Set.mem_singleton_iff.mpr e.symm)
    haveI : DecidablePred (· ∈ {w : G.V | f.branch w = some x}) :=
      fun w ↦ inferInstanceAs (Decidable (f.branch w = some x))
    obtain ⟨l, hlnd, hlmem, hlpc⟩ := exists_pickChain (f.connectedOn x)
      (fun z ↦ if z = u then 0 else 1) (fun z ↦ decide (z = u)) gs
      (fun w hw ↦ hsupp w x hw) ⟨u, hus, by simp⟩
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, l.getLast? = some w₀ := by
      cases hg : l.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hg) (pickChain_ne_nil hlpc)
      | some w₀ => exact ⟨w₀, rfl⟩
    have hw₀u : w₀ = u := by simpa using att_getLast_of_pickChain hlpc w₀ hw₀
    subst hw₀u
    have honly : ∀ w ∈ l, G.Adj v w = true → w = w₀ :=
      fun w hw hvw ↦ huniq w (hsupp w x ((hlmem w).mp hw)) w₀ hun hvw hpu
    have hcc := chainConn_filter_ne v (chainConn_of_pickChain hlpc) hlnd hw₀ hvu honly
    have hmemf : ∀ w : G.V, w ∈ l.filter (fun z ↦ decide (z ≠ v)) ↔
        (f.branch w = some x ∧ w ≠ v) := by
      intro w
      rw [List.mem_filter, hlmem]
      simp [Set.mem_setOf_eq]
    refine ⟨⟨fun w ↦ if w = v then none else f.branch w, fun x' ↦ ?_, fun x₁ x₂ hadj ↦ ?_⟩,
      fun w x' hw ↦ ?_⟩
    · by_cases hx' : x' = x
      · subst hx'
        have hset : {w : G.V | (if w = v then none else f.branch w) = some x'} =
            {w : G.V | w ∈ l.filter fun z ↦ decide (z ≠ v)} := by
          ext w
          rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hmemf]
          by_cases hwv : w = v
          · simp [hwv]
          · simp [hwv]
        rw [hset]
        exact connectedOn_of_chainConn hcc
      · have hset : {w : G.V | (if w = v then none else f.branch w) = some x'} =
            {w : G.V | f.branch w = some x'} := by
          ext w
          rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
          by_cases hwv : w = v
          · subst hwv
            rw [if_pos rfl, hbv]
            constructor
            · intro h; exact absurd h (by simp)
            · intro h; exact absurd (Option.some_inj.mp h).symm hx'
          · rw [if_neg hwv]
        rw [hset]
        exact f.connectedOn x'
    · obtain ⟨a, b, ha, hb, hab⟩ := f.map_adj hadj
      have hne : x₁ ≠ x₂ := fun e ↦ H.loopless x₁ (e ▸ hadj)
      have hav : a ≠ v := by
        rintro rfl
        rw [hbv, Option.some_inj] at ha
        subst ha
        have : b = w₀ := huniq b (hsupp b x₂ hb) w₀ hun hab hpu
        subst this
        exact hne (Option.some_inj.mp (hus.symm.trans hb))
      have hbv' : b ≠ v := by
        rintro rfl
        rw [hbv, Option.some_inj] at hb
        subst hb
        have : a = w₀ := huniq a (hsupp a x₁ ha) w₀ hun (by rw [G.symm]; exact hab) hpu
        subst this
        exact hne (Option.some_inj.mp (ha.symm.trans hus))
      exact ⟨a, b, by simp only [if_neg hav]; exact ha, by simp only [if_neg hbv']; exact hb, hab⟩
    · by_cases hwv : w = v
      · simp only [if_pos hwv] at hw; exact absurd hw (by simp)
      · simp only [if_neg hwv] at hw
        exact (List.mem_erase_of_ne hwv).mpr (hsupp w x' hw)

/-- **Peeling loses no model**: if every vertex of `H` has two neighbours, a model of `H` inside
`gs` can be moved into the two-core of `gs`. -/
theorem exists_model_twoCore (hH : ∀ x : H.V, ∃ y z, y ≠ z ∧ H.Adj x y = true ∧ H.Adj x z = true) :
    ∀ (n : ℕ) {gs : List G.V} (f : H.MinorOf G),
      (∀ (w : G.V) (x : H.V), f.branch w = some x → w ∈ gs) →
      ∃ g : H.MinorOf G, ∀ (w : G.V) (x : H.V), g.branch w = some x → w ∈ twoCore G n gs
  | 0, _, f, hsupp => ⟨f, hsupp⟩
  | n + 1, gs, f, hsupp => by
    rw [twoCore]
    cases hlow : lowDeg G gs with
    | none => exact ⟨f, hsupp⟩
    | some v =>
      have hv : gs.countP (G.Adj v) ≤ 1 := by
        simpa using (List.find?_eq_some_iff_getElem.mp hlow).1
      obtain ⟨g, hg⟩ := exists_model_erase hH f hsupp hv
      exact exists_model_twoCore hH n g hg

/-- Does every vertex of `H` have two neighbours?  This is the side condition on `H` that lets the
host be shrunk to its two-core. -/
def minDegTwo (H : CGraph) (hs : List H.V) : Bool :=
  hs.all fun x ↦ decide (2 ≤ hs.countP (H.Adj x))

/-- The converse of `two_le_countP` for a list without repeats. -/
theorem exists_two_of_two_le_countP {l : List H.V} {p : H.V → Bool} (hnd : l.Nodup)
    (h : 2 ≤ l.countP p) : ∃ a b, a ≠ b ∧ p a = true ∧ p b = true := by
  rw [List.countP_eq_length_filter] at h
  have hnd' : (l.filter p).Nodup := hnd.filter p
  cases hf : l.filter p with
  | nil => rw [hf] at h; simp at h
  | cons a t =>
    cases t with
    | nil => rw [hf] at h; simp at h
    | cons b t =>
      rw [hf] at hnd'
      have ha : a ∈ l.filter p := by rw [hf]; simp
      have hb : b ∈ l.filter p := by rw [hf]; simp
      exact ⟨a, b, fun e ↦ (List.nodup_cons.mp hnd').1 (e ▸ List.mem_cons_self ..),
        (List.mem_filter.mp ha).2, (List.mem_filter.mp hb).2⟩

/-- What `minDegTwo` is checking. -/
theorem exists_two_adj_of_minDegTwo {hs : List H.V} (hnd : hs.Nodup) (hhs : ∀ x : H.V, x ∈ hs)
    (h : minDegTwo H hs = true) (x : H.V) :
    ∃ y z, y ≠ z ∧ H.Adj x y = true ∧ H.Adj x z = true :=
  exists_two_of_two_le_countP hnd (by simpa using List.all_eq_true.mp h x (hhs x))

end Shrink

namespace MinorSearch

variable (H G : CGraph) (rank : G.V → ℕ)

/-- A step of the search. -/
inductive Move (G : CGraph) where
  /-- Add a vertex to the branch set under construction, starting one if there is none. -/
  | pick (v : G.V)
  /-- Finish the branch set under construction; when there is none and every vertex of `H` has
  one, do nothing. -/
  | stop

/-- The state of the search. -/
structure State (H G : CGraph) where
  /-- The vertices of `H` that have no branch set yet, in the order they will get one. -/
  todo : List H.V
  /-- The branch set under construction, newest vertex first. -/
  cur : Option (H.V × List G.V)
  /-- The finished branch sets, most recent first. -/
  done : List (H.V × List G.V)
  /-- The vertices of `G` that no branch set uses. -/
  avail : List G.V
  deriving DecidableEq

/-- Is there an edge of `G` between these two sets of vertices? -/
def linked (S T : List G.V) : Bool := S.any fun u ↦ T.any fun w ↦ G.Adj u w

theorem linked_iff {S T : List G.V} : linked G S T = true ↔ ∃ u ∈ S, ∃ w ∈ T, G.Adj u w := by
  simp [linked]

/-- The vertices `x`'s branch set is allowed to start at.  If a vertex of `H` next to `x` already
has a branch set, the set for `x` will have to touch the most recent of those, so the search makes
it *start* there: this replaces "any vertex of `G`" by "a vertex on the border of one set", and is
what keeps the search from wandering over the whole host once it has a foothold. -/
def attOf (x : H.V) (done : List (H.V × List G.V)) (v : G.V) : Bool :=
  match done.find? fun q ↦ H.Adj x q.1 with
  | none => true
  | some q => q.2.any (G.Adj v)

/-- Can the vertices still waiting for a branch set be reached from a set started at `v`?  One
that has to touch `x`'s set is confined to `seedReach`, so if from there it cannot also touch the
sets it is required to touch, starting `x` at `v` is hopeless.  This is what stops the search from
starting a set in a corner of the host it can never get back from; the guard in front keeps the
component computation out of the way when nothing is constrained. -/
def feasibleSeed (x : H.V) (v : G.V) (rest : List H.V) (done : List (H.V × List G.V))
    (avail : List G.V) : Bool :=
  let need := rest.filter fun z ↦ H.Adj x z && done.any fun q ↦ H.Adj z q.1
  need.isEmpty ||
    (let R := seedReach G v avail
     need.all fun z ↦ done.all fun q ↦ !H.Adj z q.1 || linked G R q.2)

/-- Make a move, or report that it is illegal. -/
def step (m : Move G) (st : State H G) : Option (State H G) :=
  match m with
  | .pick v =>
    if st.avail.contains v then
      match st.cur with
      | some (_, []) => none
      | some (x, u :: T) =>
        if (u :: T).any (G.Adj v) &&
            (!attOf H G x st.done v || decide (rank (T.getLastD u) ≤ rank v)) &&
            (decide (rank u ≤ rank v) || !T.any (G.Adj v)) then
          some ⟨st.todo, some (x, v :: u :: T), st.done, st.avail.erase v⟩
        else none
      | none =>
        match st.todo with
        | [] => none
        | x :: rest =>
          if attOf H G x st.done v && feasibleSeed H G x v rest st.done st.avail then
            some ⟨rest, some (x, [v]), st.done, st.avail.erase v⟩
          else none
    else none
  | .stop =>
    match st.cur with
    | some (x, S) =>
      if st.done.all (fun p ↦ !H.Adj x p.1 || linked G S p.2) &&
          decide (st.todo.length ≤ st.avail.length) &&
          decide (st.todo.countP (H.Adj x) ≤ st.avail.countP fun u ↦ S.any (G.Adj u)) then
        some ⟨st.todo, none, (x, S) :: st.done, st.avail⟩
      else none
    | none => if st.todo.isEmpty then some st else none

/-- The states one legal move away. -/
def candList (st : State H G) : List (State H G) :=
  (step H G rank .stop st).toList ++ st.avail.filterMap fun v ↦ step H G rank (.pick v) st

theorem mem_candList {m : Move G} {st st' : State H G} (h : step H G rank m st = some st') :
    st' ∈ candList H G rank st := by
  cases m with
  | stop => exact List.mem_append_left _ (by rw [h]; exact List.mem_singleton_self _)
  | pick v =>
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨v, ?_, h⟩)
    rw [step] at h
    split at h
    · rename_i hv; exact List.contains_iff_mem.mp hv
    · exact absurd h (by simp)

/-- The state a search has reached: the most recent one, or the initial one. -/
def headSt (init : State H G) : List (Unit × State H G) → State H G
  | [] => init
  | (_, st) :: _ => st

/-- Every state in the list follows from the one before by a legal move. -/
def chainOk (init : State H G) : List (Unit × State H G) → Bool
  | [] => true
  | (_, st) :: rest => (candList H G rank (headSt H G init rest)).contains st && chainOk init rest

theorem chainOk_of_append {init : State H G} {l r : List (Unit × State H G)}
    (h : chainOk H G rank init (l ++ r) = true) : chainOk H G rank init r = true := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    obtain ⟨_, st⟩ := p
    rw [List.cons_append, chainOk, Bool.and_eq_true] at h
    exact ih h.2

/-- The branch set of `x`. -/
def getSet : List (H.V × List G.V) → H.V → List G.V
  | [], _ => []
  | (y, S) :: rest, x => if y = x then S else getSet rest x

/-- The vertex of `H` whose branch set contains `v`, if any. -/
def branchOf : List (H.V × List G.V) → G.V → Option H.V
  | [], _ => none
  | (y, S) :: rest, v => if S.contains v then some y else branchOf rest v

/-- Does the state describe a minor?  Everything the answer needs is checked here, so the search
itself is free to prune as it likes. -/
def finalOk (hs : List H.V) (st : State H G) : Bool :=
  st.cur.isNone && st.todo.isEmpty &&
    decide (st.done.map Prod.fst).Nodup && decide (st.done.flatMap Prod.snd).Nodup &&
    hs.all (fun x ↦ (st.done.map Prod.fst).contains x) &&
    st.done.all (fun p ↦ ChainConn G p.2) &&
    hs.all fun x ↦ hs.all fun y ↦
      !H.Adj x y || linked G (getSet H G st.done x) (getSet H G st.done y)

/-- A complete run of the search is a solution when every move was legal and the state it ends in
describes a minor. -/
def goal (hs : List H.V) (init : State H G) (r : List (Unit × State H G)) : Bool :=
  chainOk H G rank init r && finalOk H G hs (headSt H G init r)

/-! ## Soundness -/

theorem getSet_eq_nil {bs : List (H.V × List G.V)} {x : H.V} (h : x ∉ bs.map Prod.fst) :
    getSet H G bs x = [] := by
  induction bs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [getSet, if_neg fun hy ↦ h.1 hy.symm]
    exact ih h.2

theorem mem_flatMap_of_mem_getSet {bs : List (H.V × List G.V)} {x : H.V} {v : G.V}
    (h : v ∈ getSet H G bs x) : v ∈ bs.flatMap Prod.snd := by
  induction bs with
  | nil => exact absurd h (by simp [getSet])
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    rw [List.flatMap_cons, List.mem_append]
    rw [getSet] at h
    split at h
    · exact Or.inl h
    · exact Or.inr (ih h)

theorem mem_getSet {bs : List (H.V × List G.V)} {x : H.V} (h : x ∈ bs.map Prod.fst) :
    (x, getSet H G bs x) ∈ bs := by
  induction bs with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    rw [getSet]
    split
    · rename_i hy; subst hy; exact List.mem_cons_self ..
    · rename_i hy
      simp only [List.map_cons, List.mem_cons] at h
      exact List.mem_cons_of_mem _ (ih (h.resolve_left (Ne.symm hy)))

/-- With distinct keys and disjoint branch sets, the two ways of reading the table agree. -/
theorem branchOf_eq_some_iff {bs : List (H.V × List G.V)} (hk : (bs.map Prod.fst).Nodup)
    (hf : (bs.flatMap Prod.snd).Nodup) {v : G.V} {x : H.V} :
    branchOf H G bs v = some x ↔ v ∈ getSet H G bs x := by
  induction bs with
  | nil => simp [branchOf, getSet]
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    rw [List.map_cons, List.nodup_cons] at hk
    rw [List.flatMap_cons, List.nodup_append] at hf
    rw [branchOf, getSet]
    by_cases hyx : y = x
    · subst hyx
      rw [if_pos rfl]
      by_cases hvS : S.contains v
      · rw [if_pos hvS]
        exact ⟨fun _ ↦ List.contains_iff_mem.mp hvS, fun _ ↦ rfl⟩
      · rw [if_neg hvS, ih hk.2 hf.2.1, getSet_eq_nil H G hk.1]
        simp only [List.not_mem_nil, false_iff]
        exact fun hv ↦ hvS (List.contains_iff_mem.mpr hv)
    · rw [if_neg hyx]
      by_cases hvS : S.contains v
      · rw [if_pos hvS]
        simp only [Option.some_inj]
        refine ⟨fun hxy ↦ absurd hxy hyx, fun hv ↦ ?_⟩
        exact absurd rfl (hf.2.2 v (List.contains_iff_mem.mp hvS) v
          (mem_flatMap_of_mem_getSet H G hv))
      · rw [if_neg hvS]
        exact ih hk.2 hf.2.1

/-- The minor that a successful search describes. -/
def ofFinal (hs : List H.V) (st : State H G) (hcov : ∀ x : H.V, x ∈ hs)
    (h : finalOk H G hs st = true) : H.MinorOf G := by
  rw [finalOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hkey⟩, hflat⟩, hmem⟩, hconn⟩, hedge⟩ := h
  have hiff : ∀ (v : G.V) (x : H.V), branchOf H G st.done v = some x ↔ v ∈ getSet H G st.done x :=
    fun _ _ ↦ branchOf_eq_some_iff H G hkey hflat
  refine ⟨branchOf H G st.done, fun x ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [show {v : G.V | branchOf H G st.done v = some x} = {v | v ∈ getSet H G st.done x} from
      Set.ext fun v ↦ hiff v x]
    exact connectedOn_of_chainConn
      (hconn _ (mem_getSet H G (List.contains_iff_mem.mp (hmem x (hcov x)))))
  · have := (hedge x (hcov x) y (hcov y)).resolve_left (by simp [hxy])
    rw [linked, List.any_eq_true] at this
    obtain ⟨u, hu, hw⟩ := this
    rw [List.any_eq_true] at hw
    obtain ⟨w, hw, huw⟩ := hw
    exact ⟨u, w, (hiff u x).mpr hu, (hiff w y).mpr hw, huw⟩

/-! ## The search -/

/-- The state a search starts from. -/
def initState (hs : List H.V) (gs : List G.V) : State H G := ⟨hs, none, [], gs⟩

/-- Search for a model of `H` in `G`, given the vertices of each.  A run is `gs.length +
hs.length` moves long: at most one `pick` per vertex of `G` and one `stop` per vertex of `H`,
padded out with idle moves once everything is placed. -/
def searchFrom (hs : List H.V) (gs : List G.V) : Option (State H G) :=
  let init := initState H G hs gs
  (Backtrack.dfs (fun _ pre ↦ candList H G rank (headSt H G init pre)) (goal H G rank hs init)
    (List.replicate (gs.length + hs.length) ()) []).map (headSt H G init)

theorem finalOk_of_searchFrom {hs : List H.V} {gs : List G.V} {st : State H G}
    (h : searchFrom H G rank hs gs = some st) : finalOk H G hs st = true := by
  simp only [searchFrom, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact (Bool.and_eq_true .. |>.mp (Backtrack.goal_of_dfs_eq_some hr)).2

/-! ## Completeness -/

/-- Erase each of `L` from `avail`. -/
def eraseAll (avail : List G.V) : List G.V → List G.V
  | [] => avail
  | v :: L => (eraseAll avail L).erase v

theorem nodup_eraseAll {avail : List G.V} (h : avail.Nodup) : ∀ L, (eraseAll G avail L).Nodup
  | [] => h
  | _ :: L => (nodup_eraseAll h L).erase _

theorem mem_eraseAll {avail : List G.V} (h : avail.Nodup) : ∀ (L : List G.V) (v : G.V),
    v ∈ eraseAll G avail L ↔ v ∈ avail ∧ v ∉ L
  | [], v => by simp [eraseAll]
  | w :: L, v => by
    rw [eraseAll, (nodup_eraseAll G h L).mem_erase_iff, mem_eraseAll h L]
    simp only [List.mem_cons, not_or]
    tauto

/-- Run a list of moves, most recent first, recording the state after each. -/
def trace (init : State H G) : List (Move G) → Option (List (Unit × State H G))
  | [] => some []
  | m :: ms => (trace init ms).bind fun r ↦
      (step H G rank m (headSt H G init r)).map fun st ↦ ((), st) :: r

theorem headSt_append (init : State H G) (r₁ r₂ : List (Unit × State H G)) :
    headSt H G init (r₁ ++ r₂) = headSt H G (headSt H G init r₂) r₁ := by
  cases r₁ with
  | nil => rfl
  | cons p r₁ => obtain ⟨_, st⟩ := p; rfl

theorem trace_append {init : State H G} {ms₁ ms₂ : List (Move G)} {r₂ : List (Unit × State H G)}
    (h₂ : trace H G rank init ms₂ = some r₂) :
    trace H G rank init (ms₁ ++ ms₂) = (trace H G rank (headSt H G init r₂) ms₁).map (· ++ r₂) := by
  induction ms₁ with
  | nil => simp [trace, h₂]
  | cons m ms ih =>
    rw [List.cons_append, trace, ih, trace]
    cases htr : trace H G rank (headSt H G init r₂) ms with
    | none => simp
    | some r₁ =>
      simp only [Option.map_some, Option.bind_some, headSt_append]
      cases step H G rank m (headSt H G (headSt H G init r₂) r₁) <;> simp

/-- A traced run is a legal one. -/
theorem trace_chainOk {init : State H G} {ms : List (Move G)} {r : List (Unit × State H G)}
    (h : trace H G rank init ms = some r) :
    chainOk H G rank init r = true ∧ r.length = ms.length := by
  induction ms generalizing r with
  | nil => rw [trace, Option.some_inj] at h; subst h; exact ⟨rfl, rfl⟩
  | cons m ms ih =>
    rw [trace, Option.bind_eq_some_iff] at h
    obtain ⟨r', hr', h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨st, hst, rfl⟩ := h
    obtain ⟨hchain, hlen⟩ := ih hr'
    refine ⟨?_, by simp [hlen]⟩
    rw [chainOk, Bool.and_eq_true]
    exact ⟨List.contains_iff_mem.mpr (mem_candList H G rank hst), hchain⟩

/-- Idling once everything is placed changes nothing. -/
theorem trace_pad {st : State H G} (hcur : st.cur = none) (htodo : st.todo = []) :
    ∀ k, ∃ r, trace H G rank st (List.replicate k Move.stop) = some r ∧ r.length = k ∧
      headSt H G st r = st
  | 0 => ⟨[], rfl, rfl, rfl⟩
  | k + 1 => by
    obtain ⟨r, hr, hlen, hhead⟩ := trace_pad hcur htodo k
    refine ⟨((), st) :: r, ?_, by simp [hlen], rfl⟩
    rw [List.replicate_succ, trace, hr, Option.bind_some, hhead, step]
    simp [hcur, htodo]

section Complete

variable {H G} (l : H.V → List G.V)

/-- The vertex of `H` whose branch set the search will make `x`'s set start next to: the last one
before `x` in the placement order `hs` that is adjacent to it. -/
def refOf (hs : List H.V) (x : H.V) : Option H.V :=
  (hs.takeWhile fun y ↦ decide (y ≠ x)).reverse.find? fun y ↦ H.Adj x y

/-- `attOf` read off the minor instead of off the search.  Unlike `attOf` it does not mention the
branch sets, so a model can be built one vertex of `H` at a time without looking back at the ones
already built. -/
def attMinor (f : H.MinorOf G) (hs : List H.V) (x : H.V) (v : G.V) : Bool :=
  match refOf hs x with
  | none => true
  | some y => decide (∃ w, f.branch w = some y ∧ G.Adj v w = true)

theorem takeWhile_ne {α : Type*} [DecidableEq α] (x : α) : ∀ (pre t : List α), x ∉ pre →
    (pre ++ x :: t).takeWhile (fun y ↦ decide (y ≠ x)) = pre
  | [], _, _ => by simp
  | a :: pre, t, h => by
    simp only [List.mem_cons, not_or] at h
    rw [List.cons_append, List.takeWhile_cons_of_pos (by simpa using fun e ↦ h.1 e.symm),
      takeWhile_ne x pre t h.2]

/-- The two readings of the seed rule agree, at the point of the run where `x` is placed. -/
theorem attOf_eq {f : H.MinorOf G} (hl : ∀ (x : H.V) (v : G.V), v ∈ l x ↔ f.branch v = some x)
    {hs : List H.V} (hhsnd : hs.Nodup) {x : H.V} {xs p : List H.V}
    (hpre : hs = p.reverse ++ x :: xs) :
    attOf H G x (p.map fun y ↦ (y, l y)) = attMinor f hs x := by
  have hxp : x ∉ p.reverse := fun h ↦ by
    rw [hpre, List.nodup_append] at hhsnd
    exact hhsnd.2.2 x h x (List.mem_cons_self ..) rfl
  have htw : hs.takeWhile (fun y ↦ decide (y ≠ x)) = p.reverse := by
    rw [hpre]; exact takeWhile_ne x p.reverse xs hxp
  funext v
  simp only [attOf, attMinor, refOf, htw, List.reverse_reverse, List.find?_map, Function.comp_def]
  cases hfind : p.find? fun y ↦ H.Adj x y with
  | none => simp
  | some y =>
    simp only [Option.map_some]
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨w, hw, hvw⟩ ↦ ⟨w, (hl y w).mp hw, hvw⟩,
      fun ⟨w, hw, hvw⟩ ↦ ⟨w, (hl y w).mpr hw, hvw⟩⟩

/-- The moves that give `x` its branch set: pick its vertices, then close the set. -/
def blockOf (x : H.V) : List (Move G) := Move.stop :: (l x).map Move.pick

/-- The moves that give every vertex of `xs` a branch set, most recent first. -/
def blocks : List H.V → List (Move G)
  | [] => []
  | x :: xs => blocks xs ++ blockOf l x

/-- The search state records the branch sets of `p`, and has `xs` left to place. -/
structure Ok (st : State H G) (xs p : List H.V) : Prop where
  /-- Nothing is under construction. -/
  cur : st.cur = none
  /-- The vertices left to place. -/
  todo : st.todo = xs
  /-- The branch sets built so far are the intended ones. -/
  done : st.done = p.map fun y ↦ (y, l y)
  /-- The branch sets still to come are still available. -/
  sub : ∀ y ∈ xs, ∀ v ∈ l y, v ∈ st.avail
  /-- No vertex is available twice. -/
  nodup : st.avail.Nodup

/-- Picking the vertices of a chain-connected list, from the right, builds it as a branch set. -/
theorem trace_picks {x : H.V} {rest : List H.V} :
    ∀ (L : List G.V) (st : State H G), st.cur = none → st.todo = x :: rest →
      PickChain G rank (attOf H G x st.done) L = true →
      (∀ u, L.getLast? = some u → feasibleSeed H G x u rest st.done st.avail = true) →
      L.Nodup → (∀ v ∈ L, v ∈ st.avail) → st.avail.Nodup →
      ∃ r, trace H G rank st (L.map Move.pick) = some r ∧ r.length = L.length ∧
        headSt H G st r = ⟨rest, some (x, L), st.done, eraseAll G st.avail L⟩ := by
  intro L
  induction L with
  | nil => intro st _ _ hL _ _ _ _; simp [PickChain] at hL
  | cons v L ih =>
    intro st hcur htodo hL hfeas hnd hsub hav
    have hvL : v ∉ L := (List.nodup_cons.mp hnd).1
    have hvav : v ∈ st.avail := hsub v (List.mem_cons_self ..)
    rcases L with _ | ⟨w, L⟩
    · rw [PickChain] at hL
      have hfv : feasibleSeed H G x v rest st.done st.avail = true := hfeas v rfl
      refine ⟨[((), ⟨rest, some (x, [v]), st.done, st.avail.erase v⟩)], ?_, rfl, rfl⟩
      rw [List.map_cons, List.map_nil, trace, trace, Option.bind_some]
      simp only [headSt, step, List.contains_iff_mem, hvav, if_pos, hcur, htodo, hL, hfv,
        Bool.and_self]
      rfl
    · rw [PickChain] at hL
      simp only [Bool.and_eq_true] at hL
      obtain ⟨⟨⟨hadj, hseed⟩, hrank⟩, hLc⟩ := hL
      obtain ⟨r, hr, hlen, hhead⟩ := ih st hcur htodo hLc
        (fun u hu ↦ hfeas u (by simpa using hu)) (List.Nodup.of_cons hnd)
        (fun u hu ↦ hsub u (List.mem_cons_of_mem _ hu)) hav
      refine ⟨((), ⟨rest, some (x, v :: w :: L), st.done, eraseAll G st.avail (v :: w :: L)⟩) :: r,
        ?_, by simp [hlen], rfl⟩
      have hmem : v ∈ eraseAll G st.avail (w :: L) := (mem_eraseAll G hav _ v).mpr ⟨hvav, hvL⟩
      rw [List.map_cons, trace, hr, Option.bind_some, hhead, step]
      simp only [List.contains_iff_mem, hmem, if_pos, hadj, hseed, hrank, Bool.and_self]
      rfl

variable (f : H.MinorOf G) (hl : ∀ (x : H.V) (v : G.V), v ∈ l x ↔ f.branch v = some x)
  (hnd : ∀ x, (l x).Nodup) (hcc : ∀ x, ChainConn G (l x) = true) (hs : List H.V)
  (hhsnd : hs.Nodup) (hch : ∀ x, PickChain G rank (attMinor f hs x) (l x) = true)

include hl in
/-- Distinct vertices of `H` have disjoint branch sets. -/
theorem not_mem_l {x y : H.V} (hxy : x ≠ y) {v : G.V} (hv : v ∈ l x) : v ∉ l y := fun hw ↦
  hxy (Option.some_inj.mp (((hl x v).mp hv).symm.trans ((hl y v).mp hw)))

include f hl in
/-- Adjacent vertices of `H` have branch sets joined by an edge. -/
theorem linked_l {x y : H.V} (hxy : H.Adj x y = true) : linked G (l x) (l y) = true := by
  obtain ⟨u, w, hu, hw, huw⟩ := f.map_adj hxy
  exact (linked_iff G).mpr ⟨u, (hl x u).mpr hu, w, (hl y w).mpr hw, huw⟩

include f hl in
/-- Every vertex of `H` next to `x` has a vertex of its own branch set next to `x`'s, and those
vertices are all different because the branch sets are. -/
theorem countP_le_flatMap (x : H.V) : ∀ xs : List H.V,
    xs.countP (H.Adj x) ≤ (xs.flatMap l).countP (fun u ↦ (l x).any (G.Adj u))
  | [] => le_rfl
  | y :: ys => by
    have hys := countP_le_flatMap x ys
    rw [List.flatMap_cons, List.countP_append, List.countP_cons]
    cases hadj : H.Adj x y
    · simp only [Bool.false_eq_true, if_false]
      omega
    · obtain ⟨u, hu, w, hw, huw⟩ := (linked_iff G).mp (linked_l l f hl hadj)
      have hpos : 0 < (l y).countP fun u ↦ (l x).any (G.Adj u) :=
        List.countP_pos_iff.mpr ⟨w, hw, List.any_eq_true.mpr ⟨u, hu, by rw [G.symm]; exact huw⟩⟩
      simp only [if_true]
      omega

include hl hnd in
theorem nodup_flatMap : ∀ {xs : List H.V}, xs.Nodup → (xs.flatMap l).Nodup
  | [], _ => by simp
  | x :: xs, h => by
    rw [List.nodup_cons] at h
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hnd x, nodup_flatMap h.2, fun a ha b hb hab ↦ ?_⟩
    obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
    exact not_mem_l l f hl (fun e ↦ h.1 (by rw [e]; exact hy)) ha (hab ▸ hb)

theorem length_flatMap_add (xs : List H.V) :
    (xs.map fun y ↦ (l y).length + 1).sum = (xs.flatMap l).length + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.length_append,
      List.length_cons]; omega

include hcc in
theorem length_le_flatMap : ∀ xs : List H.V, xs.length ≤ (xs.flatMap l).length
  | [] => le_rfl
  | x :: xs => by
    have h1 := length_le_flatMap xs
    have h2 : 0 < (l x).length := List.length_pos_of_ne_nil (chainConn_ne_nil (hcc x))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    omega

include f hl hnd hcc hhsnd hch in
/-- One block of moves gives `x` its branch set. -/
theorem trace_block (x : H.V) (xs p : List H.V) (st : State H G) (hok : Ok l st (x :: xs) p)
    (hxs : (x :: xs).Nodup) (hpre : hs = p.reverse ++ x :: xs) :
    ∃ r, trace H G rank st (blockOf l x) = some r ∧ r.length = (l x).length + 1 ∧
      Ok l (headSt H G st r) xs (x :: p) := by
  obtain ⟨hcur, htodo, hdone, hsub, hav⟩ := hok
  have hfeas : ∀ u, (l x).getLast? = some u →
      feasibleSeed H G x u xs st.done st.avail = true := by
    intro u hu
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hu
    have hux : u ∈ l x := by rw [hys]; simp
    rw [feasibleSeed, Bool.or_eq_true]
    refine Or.inr ?_
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.mem_filter, Bool.and_eq_true]
    rintro z ⟨hz, hxz, -⟩ q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp (hdone ▸ hq)
    cases hzy : H.Adj z y
    · exact Or.inl rfl
    refine Or.inr ?_
    obtain ⟨c, hc, w, hw, hcw⟩ := (linked_iff G).mp (linked_l l f hl hzy)
    obtain ⟨d, hd, e, he, hde⟩ := (linked_iff G).mp (linked_l l f hl hxz)
    refine (linked_iff G).mpr ⟨c, ?_, w, hw, hcw⟩
    refine subset_seedReach (connectedOn_of_chainConn (hcc x)) (connectedOn_of_chainConn (hcc z))
      hav hux (hsub x (List.mem_cons_self ..)) (hsub z (List.mem_cons_of_mem _ hz)) ?_ he hd
      (by rw [G.symm]; exact hde) c hc
    exact not_mem_l l f hl (by rintro rfl; exact (List.nodup_cons.mp hxs).1 hz) hux
  obtain ⟨r, hr, hlen, hhead⟩ := trace_picks rank (l x) st hcur htodo
    (by rw [hdone, attOf_eq l hl hhsnd hpre]; exact hch x) hfeas
    (hnd x) (hsub x (List.mem_cons_self ..)) hav
  have havail : ∀ y ∈ xs, ∀ v ∈ l y, v ∈ eraseAll G st.avail (l x) := by
    intro y hy v hv
    refine (mem_eraseAll G hav _ v).mpr ⟨hsub y (List.mem_cons_of_mem _ hy) v hv, ?_⟩
    exact not_mem_l l f hl (by rintro rfl; exact (List.nodup_cons.mp hxs).1 hy) hv
  have hc1 : st.done.all (fun q ↦ !H.Adj x q.1 || linked G (l x) q.2) = true := by
    rw [hdone, List.all_eq_true]
    intro q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hq
    cases hadj : H.Adj x y
    · simp
    · simp [linked_l l f hl hadj]
  have hsubperm : (xs.flatMap l).Subperm (eraseAll G st.avail (l x)) := by
    refine (nodup_flatMap l f hl hnd (List.Nodup.of_cons hxs)).subperm ?_
    intro v hv
    obtain ⟨y, hy, hv⟩ := List.mem_flatMap.mp hv
    exact havail y hy v hv
  have hc2 : xs.length ≤ (eraseAll G st.avail (l x)).length :=
    le_trans (length_le_flatMap l hcc xs) hsubperm.length_le
  -- Each vertex of `H` still to come that is next to `x` puts a *different* vertex of its own
  -- branch set next to `x`'s, so there must be at least that many left over to go round.
  have hc3 : xs.countP (H.Adj x) ≤
      (eraseAll G st.avail (l x)).countP (fun u ↦ (l x).any (G.Adj u)) :=
    le_trans (countP_le_flatMap l f hl x xs) (List.Subperm.countP_le _ hsubperm)
  refine ⟨((), ⟨xs, none, (x, l x) :: st.done, eraseAll G st.avail (l x)⟩) :: r, ?_,
    by simp [hlen], ⟨rfl, rfl, by rw [hdone]; rfl, havail, nodup_eraseAll G hav _⟩⟩
  rw [blockOf, trace, hr, Option.bind_some, hhead, step]
  simp only [hc1, hc2, hc3, decide_true, Bool.and_true, if_pos]
  rfl

include f hl hnd hcc hhsnd hch in
/-- The whole run: every vertex of `xs` gets its branch set. -/
theorem trace_blocks : ∀ (xs p : List H.V) (st : State H G), Ok l st xs p → xs.Nodup →
    hs = p.reverse ++ xs →
    ∃ r, trace H G rank st (blocks l xs) = some r ∧
      r.length = (xs.map fun y ↦ (l y).length + 1).sum ∧
      Ok l (headSt H G st r) [] (xs.reverse ++ p)
  | [], p, st, hok, _, _ => ⟨[], rfl, rfl, by simpa using hok⟩
  | x :: xs, p, st, hok, hxs, hpre => by
    obtain ⟨r₁, hr₁, hlen₁, hok₁⟩ :=
      trace_block rank l f hl hnd hcc hs hhsnd hch x xs p st hok hxs hpre
    obtain ⟨r₂, hr₂, hlen₂, hok₂⟩ := trace_blocks xs (x :: p) _ hok₁ (List.Nodup.of_cons hxs)
      (by rw [hpre]; simp)
    refine ⟨r₂ ++ r₁, ?_, ?_, ?_⟩
    · rw [blocks, trace_append H G rank hr₁, hr₂]; rfl
    · rw [List.length_append, hlen₁, hlen₂, List.map_cons, List.sum_cons]; omega
    · rw [headSt_append]; simpa using hok₂

theorem getSet_map {ys : List H.V} {x : H.V} (h : x ∈ ys) :
    getSet H G (ys.map fun y ↦ (y, l y)) x = l x := by
  induction ys with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.map_cons, getSet]
    split
    · rename_i hy; rw [hy]
    · rename_i hy; exact ih ((List.mem_cons.mp h).resolve_left fun e ↦ hy e.symm)

include f hl hnd hcc hhsnd in
/-- A finished run passes every test. -/
theorem finalOk_of_ok {st : State H G} (hok : Ok l st [] hs.reverse) :
    finalOk H G hs st = true := by
  obtain ⟨hcur, htodo, hdone, -, -⟩ := hok
  have e1 : ((hs.reverse.map fun y ↦ (y, l y)).map Prod.fst) = hs.reverse := by
    simp [Function.comp_def]
  have e2 : ((hs.reverse.map fun y ↦ (y, l y)).flatMap Prod.snd) = hs.reverse.flatMap l := by
    rw [List.flatMap_map]
  rw [finalOk, hcur, htodo, hdone, e1, e2]
  have h1 : hs.reverse.Nodup := List.nodup_reverse.mpr hhsnd
  have h2 : (hs.reverse.flatMap l).Nodup := nodup_flatMap l f hl hnd h1
  have h3 : ∀ x ∈ hs, hs.reverse.contains x :=
    fun x hx ↦ List.contains_iff_mem.mpr (List.mem_reverse.mpr hx)
  have h4 : ∀ q ∈ hs.reverse.map fun y ↦ (y, l y), ChainConn G q.2 = true := by
    intro q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hq
    exact hcc y
  have h5 : ∀ x ∈ hs, ∀ y ∈ hs, (!H.Adj x y ||
      linked G (getSet H G (hs.reverse.map fun z ↦ (z, l z)) x)
        (getSet H G (hs.reverse.map fun z ↦ (z, l z)) y)) = true := by
    intro x hx y hy
    rw [getSet_map l (List.mem_reverse.mpr hx), getSet_map l (List.mem_reverse.mpr hy)]
    cases hadj : H.Adj x y
    · simp
    · simp [linked_l l f hl hadj]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

/-- **Every minor is described by a chain-ordered model**, which is what the search looks for. -/
theorem exists_chain_model (f : H.MinorOf G) (rank : G.V → ℕ) (hs : List H.V) {gs : List G.V}
    (hgs : ∀ (v : G.V) (x : H.V), f.branch v = some x → v ∈ gs) :
    ∃ L : H.V → List G.V, (∀ (x : H.V) (v : G.V), v ∈ L x ↔ f.branch v = some x) ∧
      (∀ x, (L x).Nodup) ∧ (∀ x, ChainConn G (L x) = true) ∧
      (∀ x, PickChain G rank (attMinor f hs x) (L x) = true) := by
  haveI : ∀ x : H.V, DecidablePred (· ∈ {v : G.V | f.branch v = some x}) :=
    fun x v ↦ inferInstanceAs (Decidable (f.branch v = some x))
  have key : ∀ x : H.V, ∃ L : List G.V, L.Nodup ∧
      (∀ v, v ∈ L ↔ v ∈ {v : G.V | f.branch v = some x}) ∧
      PickChain G rank (attMinor f hs x) L = true := by
    intro x
    refine exists_pickChain (f.connectedOn x) rank (attMinor f hs x) gs (fun v hv ↦ hgs v x hv) ?_
    cases href : refOf hs x with
    | none =>
      obtain ⟨v, hv⟩ := (f.connectedOn x).nonempty
      exact ⟨v, hv, by simp [attMinor, href]⟩
    | some y =>
      have hadj : H.Adj x y = true := by rw [refOf] at href; exact List.find?_some href
      obtain ⟨u, w, hu, hw, huw⟩ := f.map_adj hadj
      exact ⟨u, hu, by simp only [attMinor, href, decide_eq_true_eq]; exact ⟨w, hw, huw⟩⟩
  choose L h1 h2 h3 using key
  exact ⟨L, fun x v ↦ h2 x v, h1, fun x ↦ chainConn_of_pickChain (h3 x), h3⟩

end Complete

variable {H G}

/-- **Completeness**: a search that comes back empty has ruled out every minor whose branch sets
lie inside the pool it searched.  The pool need not be all of `G`: it is legitimate to shrink it
first, as long as no model is lost — see `exists_model_core`. -/
theorem not_minorOf_of_searchFrom {hs : List H.V} {gs : List G.V}
    (hhsnd : hs.Nodup) (hgsnd : gs.Nodup) (h : searchFrom H G rank hs gs = none)
    (f : H.MinorOf G) (hgs : ∀ (v : G.V) (x : H.V), f.branch v = some x → v ∈ gs) : False := by
  obtain ⟨l, hl, hnd, hcc, hch⟩ := exists_chain_model f rank hs hgs
  have hsupp : ∀ (y : H.V), ∀ v ∈ l y, v ∈ gs := fun y v hv ↦ hgs v y ((hl y v).mp hv)
  have hok : Ok l (initState H G hs gs) hs [] :=
    ⟨rfl, rfl, rfl, fun y _ v hv ↦ hsupp y v hv, hgsnd⟩
  obtain ⟨r₁, hr₁, hlen₁, hok₁⟩ :=
    trace_blocks rank l f hl hnd hcc hs hhsnd hch hs [] _ hok hhsnd rfl
  have hbound : r₁.length ≤ gs.length + hs.length := by
    have : (hs.flatMap l).length ≤ gs.length :=
      ((nodup_flatMap l f hl hnd hhsnd).subperm fun v hv ↦ by
        obtain ⟨y, -, hv⟩ := List.mem_flatMap.mp hv
        exact hsupp y v hv).length_le
    rw [hlen₁, length_flatMap_add l hs]
    omega
  obtain ⟨r₂, hr₂, hlen₂, hhead₂⟩ :=
    trace_pad H G rank hok₁.cur hok₁.todo (gs.length + hs.length - r₁.length)
  have htr : trace H G rank (initState H G hs gs)
      (List.replicate (gs.length + hs.length - r₁.length) Move.stop ++ blocks l hs)
      = some (r₂ ++ r₁) := by rw [trace_append H G rank hr₁, hr₂]; rfl
  obtain ⟨hchain, -⟩ := trace_chainOk H G rank htr
  have hgoal : goal H G rank hs (initState H G hs gs) (r₂ ++ r₁) = true := by
    rw [goal, Bool.and_eq_true, headSt_append, hhead₂]
    exact ⟨hchain, finalOk_of_ok l f hl hnd hcc hs hhsnd (by simpa using hok₁)⟩
  have hcand : ∀ (a : Unit) (pre : List (Unit × State H G)) (b : State H G)
      (u : List (Unit × State H G)),
      goal H G rank hs (initState H G hs gs) (u ++ (a, b) :: pre) = true →
      b ∈ candList H G rank (headSt H G (initState H G hs gs) pre) := by
    intro _ pre b u hg
    rw [goal, Bool.and_eq_true] at hg
    have hc := chainOk_of_append H G rank hg.1
    rw [chainOk, Bool.and_eq_true] at hc
    exact List.contains_iff_mem.mp hc.1
  have hsol : ((r₂ ++ r₁).reverse).map Prod.fst = List.replicate (gs.length + hs.length) () := by
    rw [List.eq_replicate_iff]
    refine ⟨?_, fun b _ ↦ rfl⟩
    rw [List.length_map, List.length_reverse, List.length_append, hlen₂]
    omega
  rw [searchFrom, Option.map_eq_none_iff] at h
  have := Backtrack.dfs_eq_none hcand h hsol
  rw [List.reverse_reverse, List.append_nil, hgoal] at this
  exact absurd this (by simp)

/-- **Completeness** over the whole of `G`: a search that comes back empty has ruled out every
minor. -/
theorem isEmpty_minorOf_of_searchFrom {hs : List H.V} {gs : List G.V} (hgs : ∀ v, v ∈ gs)
    (hhsnd : hs.Nodup) (hgsnd : gs.Nodup) (h : searchFrom H G rank hs gs = none) :
    IsEmpty (H.MinorOf G) :=
  ⟨fun f ↦ not_minorOf_of_searchFrom rank hhsnd hgsnd h f fun v _ _ ↦ hgs v⟩

end MinorSearch

/-! ## The search -/

section Search

open MinorSearch

variable (H G : CGraph)

/-- The vertex of `b :: rest` with the most neighbours among `chosen`, earliest one winning. -/
def bestNext (chosen : List H.V) : H.V → List H.V → H.V
  | b, [] => b
  | b, z :: rest =>
    bestNext chosen (if chosen.countP (H.Adj b) < chosen.countP (H.Adj z) then z else b) rest

theorem mem_bestNext (chosen : List H.V) : ∀ (b : H.V) (rest : List H.V),
    bestNext H chosen b rest ∈ b :: rest
  | b, [] => List.mem_cons_self ..
  | b, z :: rest => by
    rw [bestNext]
    split
    · exact List.mem_cons_of_mem _ (mem_bestNext chosen z rest)
    · rcases List.mem_cons.mp (mem_bestNext chosen b rest) with h | h
      · rw [h]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Order the vertices of `H` so that each one is next to as many earlier ones as possible.  The
search prunes hardest when a new branch set has to attach to one that is already placed, so an
order that keeps `H` connected as it goes is worth much more than the order it came in. -/
def connOrder : ℕ → List H.V → List H.V → List H.V
  | 0, rest, _ => rest
  | _ + 1, [], _ => []
  | n + 1, z :: rest, chosen =>
    let b := bestNext H chosen z rest
    b :: connOrder n ((z :: rest).erase b) (b :: chosen)

theorem connOrder_perm : ∀ (n : ℕ) (rest chosen : List H.V), rest.length ≤ n →
    (connOrder H n rest chosen).Perm rest
  | 0, rest, _, h => by rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)]; rfl
  | _ + 1, [], _, _ => .refl _
  | n + 1, z :: rest, chosen, h => by
    have hb := mem_bestNext H chosen z rest
    have hlen : ((z :: rest).erase (bestNext H chosen z rest)).length ≤ n := by
      rw [List.length_erase_of_mem hb]
      rw [List.length_cons] at h ⊢
      omega
    exact .trans (.cons _ (connOrder_perm n _ _ hlen)) (List.perm_cons_erase hb).symm

/-- The vertices of `H`, in the order the search places them. -/
def hsOrder (rH : Roster H.V) : List H.V :=
  connOrder H rH.toList.dedup.length rH.toList.dedup []

theorem hsOrder_perm (rH : Roster H.V) : (hsOrder H rH).Perm rH.toList.dedup :=
  connOrder_perm H _ _ _ le_rfl

theorem hsOrder_nodup (rH : Roster H.V) : (hsOrder H rH).Nodup :=
  (hsOrder_perm H rH).nodup_iff.mpr (List.nodup_dedup _)

theorem mem_hsOrder (rH : Roster H.V) (x : H.V) : x ∈ hsOrder H rH :=
  (hsOrder_perm H rH).mem_iff.mpr (List.mem_dedup.mpr (rH.mem_toList x))

/-- The vertices of `G` the search may use.  When every vertex of `H` has two neighbours, a vertex
of `G` with at most one neighbour left is in no branch set (`exists_model_twoCore`), so the host is
peeled down to its two-core first — which for a forest, and `H = C₃`, leaves nothing at all. -/
def hostPool (rH : Roster H.V) (rG : Roster G.V) : List G.V :=
  if minDegTwo H (hsOrder H rH) then
    twoCore G rG.toList.dedup.length rG.toList.dedup
  else rG.toList.dedup

/-- The finished state the search finds, before it is turned into a `MinorOf`.

The guard in front is the cheap necessary condition: a minor has no more vertices and no more
edges than its host, so a search that cannot possibly succeed is not started. -/
def searchMinor (rH : Roster H.V) (rG : Roster G.V) : Option (State H G) :=
  if Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E then
    searchFrom H G (fun v ↦ rG.toList.idxOf v) (hsOrder H rH) (hostPool H G rH rG)
  else none

theorem finalOk_of_searchMinor {rH : Roster H.V} {rG : Roster G.V} {st : State H G}
    (h : searchMinor H G rH rG = some st) : finalOk H G (hsOrder H rH) st = true := by
  rw [searchMinor] at h
  split at h
  · exact finalOk_of_searchFrom H G _ h
  · exact absurd h (by simp)

/-- **Is `H` a minor of `G`?**  Returns a witness if so.  See
`isEmpty_minorOf_of_findMinor_eq_none` for the other half of the answer. -/
def findMinor (rH : Roster H.V) (rG : Roster G.V) : Option (H.MinorOf G) :=
  Option.pmap (p := fun st ↦ finalOk H G (hsOrder H rH) st = true)
    (fun st hst ↦ ofFinal H G (hsOrder H rH) st (mem_hsOrder H rH) hst)
    (searchMinor H G rH rG) (fun _ hst ↦ finalOk_of_searchMinor H G hst)

theorem findMinor_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findMinor H G rH rG = none ↔ searchMinor H G rH rG = none :=
  Option.pmap_eq_none_iff

variable {H G}

/-- **Completeness**: when the search comes back empty, `H` is not a minor of `G`. -/
theorem isEmpty_minorOf_of_findMinor_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findMinor H G rH rG = none) : IsEmpty (H.MinorOf G) := by
  rw [findMinor_eq_none_iff, searchMinor] at h
  split at h
  · refine ⟨fun f ↦ ?_⟩
    have hall : ∀ (w : G.V) (x : H.V), f.branch w = some x → w ∈ rG.toList.dedup :=
      fun w _ _ ↦ List.mem_dedup.mpr (rG.mem_toList w)
    rw [hostPool] at h
    split at h
    · obtain ⟨g, hg⟩ := exists_model_twoCore
        (exists_two_adj_of_minDegTwo (hsOrder_nodup H rH) (mem_hsOrder H rH) ‹_›) _ f hall
      exact not_minorOf_of_searchFrom _ (hsOrder_nodup H rH)
        (twoCore_nodup _ (List.nodup_dedup _)) h g hg
    · exact not_minorOf_of_searchFrom _ (hsOrder_nodup H rH) (List.nodup_dedup _) h f hall
  · exact ⟨fun f ↦ absurd (show Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E from
      ⟨f.card_le, f.E_le⟩) ‹_›⟩

/-- `H` is a minor of `G` exactly when the search finds one. -/
theorem isEmpty_minorOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.MinorOf G) ↔ findMinor H G rH rG = none := by
  refine ⟨fun h ↦ ?_, isEmpty_minorOf_of_findMinor_eq_none⟩
  rcases hm : findMinor H G rH rG with _ | f
  · rfl
  · exact (h.false f).elim

end Search

end CGraph
