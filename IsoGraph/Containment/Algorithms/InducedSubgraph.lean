import IsoGraph.Containment.Defs
import IsoGraph.Containment.Algorithms.Backtrack
import IsoGraph.Containment.Algorithms.Twins

/-!
# Searching for an induced subgraph

`CGraph.findInducedSubgraph H G rH rG` looks for a copy of `H` sitting inside `G` as an induced
subgraph.  It does not return a `Bool`: when it succeeds it returns the witness itself, an
`H.InducedSubgraphOf G`, so there is nothing left to check.  When it fails,
`isEmpty_inducedSubgraphOf_of_eq_none` says there was nothing to find.

`rH` and `rG` are `Backtrack.Roster`s — lists of the vertices, which a `Fintype` instance cannot
computably supply.  For a graph on `Fin n`, `Backtrack.Roster.fin n` is the one to use.

The problem is NP-hard, so the search is a backtracking one, over `Backtrack.dfs`.  Four things
keep it from being the naive enumeration of all `card G.V ^ card H.V` maps.

* **The order.**  `CGraph.searchOrder` picks the vertices of `H` greedily: at each step the vertex
  with the most neighbours already chosen, breaking ties by degree.  After the first vertex, every
  subsequent one is (for a connected `H`) adjacent to something already placed, so its candidates
  are confined to the neighbourhood of a vertex that is already fixed.  Any order at all gives a
  correct search, which is why the order is chosen by a heuristic that is never reasoned about:
  `searchOrder` simply checks at run time that what the heuristic produced is a duplicate-free
  list of every vertex, and falls back on the roster if it is not.
* **Consistency.**  A candidate `b` for `a` must differ from every vertex already used and must
  agree with it on adjacency, in *both* directions — that is `CGraph.compat`.  For an induced
  subgraph this is a much stronger filter than for an ordinary one, since a non-edge of `H` is as
  informative as an edge.
* **Degrees.**  A vertex of `H` of degree `d` can only go to a vertex of `G` of degree at least
  `d`.  This one is not a property of the partial assignment but of the whole embedding, so it
  lives in `goalAsg` and is projected out of it in `mem_candList`.
* **Symmetry.**  Interchangeable vertices of `H` — `Algorithms/Twins.lean` — are made to take
  their images in increasing order of `CGraph.hostRank`, so that of the `|C|!` embeddings a class
  of size `|C|` admits, exactly one is looked for.  Like the degree test this is a condition on
  the whole embedding, `CGraph.sortedAsg` in `goalAsg`, and `mem_candList` projects it out as the
  interval `CGraph.symLo`–`CGraph.symHi` the next image has to fall in.

The candidates a node even looks at are cut down before either test runs: if `a` has a neighbour
already placed, `CGraph.pivot` finds its image `u`, and the candidates are read straight off `u`'s
row of the adjacency table rather than filtered out of all of `G`.  That is not extra pruning —
the consistency test would reject the others anyway — but it is the difference between a node
costing `card G.V` and costing the degree of `u`.

`CGraph.adjTable` and `CGraph.Row` are what make that cheap.  Everything the search asks about a
vertex of `G` is tabulated once, before the search starts: its degree, its neighbours, and the
rows of its neighbours.  This matters more than it looks.  For a graph presented by an edge list —
which is how most of the named graphs here are built — `G.Adj` is a scan of that list, and the
innermost loop of the search asks for adjacency once per placed vertex per candidate per node;
reading it off the candidate's own neighbour list instead took the running time of a
representative search down by an order of magnitude.

Two counting tests — `card H.V ≤ card G.V` and `H.E ≤ G.E` — reject hopeless pairs before the
search starts, which matters because injectivity alone would only make the search fail at depth
`card G.V + 1`.

The same `Backtrack.dfs` with `compat` weakened to "different, and edges go to edges" would search
for an ordinary subgraph; only the induced version is set up here, because the induced one is the
one whose pruning is strong enough to be worth the trouble.

## What it costs

A pattern with edges is cheap, because the pivot confines every vertex after the first to one
neighbourhood: an 8-vertex path in the 5×5 grid takes 1 ms, an 8-cycle in the 24-vertex McGee
graph 3 ms, and ruling `K3,3` out of McGee 3 ms.

The expensive pattern is the one with *no* edges — asking for an independent set of a given size,
which is where the symmetry breaking earns its keep, since a pattern with no edges is one single
class of interchangeable vertices.  On the Heawood graph the tree for `E8` goes from 31487 nodes
to 458, and 457 ms to 12 ms; `E11` in McGee (there is no such set) goes from over twenty minutes
to 1.5 s, and `E14` in the 5×5 grid, which had not finished in fifty, takes 5.6 s.  Finding a set
that does exist stays quick either way — `E13` in the 5×5 grid is 6 ms.  (Best of a few runs on a
loaded shared machine; treat them as ratios.)
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

/-! ## A search order for the vertices of the pattern -/

/-- How much a vertex is worth taking next: first the number of neighbours already taken, then the
degree.  Packed into one natural number so that it can be compared with `<`. -/
private def orderKey (H : CGraph) (acc : List H.V) (v : H.V) : ℕ :=
  (acc.countP fun u ↦ H.Adj v u) * (Fintype.card H.V + 1) + H.toSimple.degree v

/-- Greedily take the vertex of highest `orderKey`, `n` times. -/
private def searchOrderAux (H : CGraph) : ℕ → List H.V → List H.V → List H.V
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | n + 1, v :: rest, acc =>
    let best := rest.foldl (fun b u ↦ if orderKey H acc b < orderKey H acc u then u else b) v
    searchOrderAux H n ((v :: rest).erase best) (best :: acc)

private def rawOrder (H : CGraph) (hs : List H.V) : List H.V := searchOrderAux H hs.length hs []

/-- The order in which the search assigns the vertices of `H`.  The greedy heuristic is checked at
run time rather than reasoned about: if it fails to produce a duplicate-free list of all the
vertices — which it will not — the roster is used instead. -/
def searchOrder (H : CGraph) (hs : List H.V) : List H.V :=
  if (rawOrder H hs).Nodup ∧ ∀ x : H.V, x ∈ rawOrder H hs then rawOrder H hs else hs.dedup

theorem searchOrder_nodup (H : CGraph) (hs : List H.V) : (searchOrder H hs).Nodup := by
  rw [searchOrder]
  split
  · rename_i h; exact h.1
  · exact hs.nodup_dedup

theorem mem_searchOrder (H : CGraph) {hs : List H.V} (hmem : ∀ x, x ∈ hs) (x : H.V) :
    x ∈ searchOrder H hs := by
  rw [searchOrder]
  split
  · rename_i h; exact h.2 x
  · exact List.mem_dedup.mpr (hmem x)

/-! ## Consistency of a partial assignment -/

variable (H G : CGraph)

/-- Two assignments `x ↦ u` and `y ↦ v` are compatible when they are injective on the two vertices
and agree on adjacency in both directions. -/
def compat (p q : H.V × G.V) : Bool :=
  decide (p.2 ≠ q.2) && (H.Adj p.1 q.1 == G.Adj p.2 q.2)

theorem compat_comm (p q : H.V × G.V) : compat H G p q = compat H G q p := by
  have h : (p.2 ≠ q.2) = (q.2 ≠ p.2) := propext ne_comm
  simp only [compat, h, H.symm p.1 q.1, G.symm p.2 q.2]

/-- Every two assignments in the list are compatible. -/
def validAsg : List (H.V × G.V) → Bool
  | [] => true
  | p :: rest => rest.all (compat H G p) && validAsg rest

theorem validAsg_iff (l : List (H.V × G.V)) :
    validAsg H G l = true ↔ l.Pairwise fun p q ↦ compat H G p q = true := by
  induction l with
  | nil => simp [validAsg]
  | cons p rest ih => simp [validAsg, List.pairwise_cons, ih]

theorem validAsg_of_append {l m : List (H.V × G.V)} (h : validAsg H G (l ++ m) = true) :
    validAsg H G m = true := by
  induction l with
  | nil => simpa using h
  | cons p l ih => rw [List.cons_append, validAsg, Bool.and_eq_true] at h; exact ih h.2

/-- The order symmetry breaking imposes: whenever both members of a pair of interchangeable
vertices are placed, their images come in increasing order of `rank`.  Only solutions in that
order are looked for, and `exists_sorted_pairs` says that costs nothing. -/
def sortedAsg (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (asg : List (H.V × G.V)) : Bool :=
  pairs.all fun p ↦ asg.all fun q ↦ asg.all fun r ↦
    !decide (q.1 = p.1) || !decide (r.1 = p.2) || decide (rank q.2 ≤ rank r.2)

theorem sortedAsg_le {rank : G.V → ℕ} {pairs : List (H.V × H.V)} {asg : List (H.V × G.V)}
    (h : sortedAsg H G rank pairs asg = true) {p : H.V × H.V} (hp : p ∈ pairs)
    {q r : H.V × G.V} (hq : q ∈ asg) (hr : r ∈ asg) (hq1 : q.1 = p.1) (hr1 : r.1 = p.2) :
    rank q.2 ≤ rank r.2 := by
  rw [sortedAsg, List.all_eq_true] at h
  have hqr := List.all_eq_true.mp (List.all_eq_true.mp (h p hp) q hq) r hr
  simpa [hq1, hr1] using hqr

/-- What the search is looking for: a consistent assignment that also respects degrees and the
symmetry-breaking order.  Neither of those is local to a pair, which is why they are stated here
rather than in `compat`; `mem_candList` projects them back out for use as a filter. -/
def goalAsg (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (asg : List (H.V × G.V)) : Bool :=
  validAsg H G asg && asg.all (fun p ↦ decide (H.toSimple.degree p.1 ≤ G.toSimple.degree p.2)) &&
    sortedAsg H G rank pairs asg

/-- The image of some already-placed neighbour of `a`, if `a` has one.  Every candidate for `a`
then has to be a neighbour of that vertex, which is a far shorter list than all of `G`. -/
def pivot (a : H.V) : List (H.V × G.V) → Option G.V
  | [] => none
  | (x, u) :: rest => if H.Adj a x then some u else pivot a rest

theorem pivot_spec {a : H.V} {pre : List (H.V × G.V)} {u : G.V} (h : pivot H G a pre = some u) :
    ∃ x, (x, u) ∈ pre ∧ H.Adj a x = true := by
  induction pre with
  | nil => simp [pivot] at h
  | cons p rest ih =>
    obtain ⟨x, v⟩ := p
    rw [pivot] at h
    split at h
    · rename_i hax
      rw [Option.some_inj] at h
      exact ⟨x, by simp [h], hax⟩
    · obtain ⟨y, hy, hay⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hay⟩

/-! ## Tabulating the host

Everything the search asks about a vertex of `G` — its degree, and whether it is adjacent to some
other vertex — is tabulated before the search starts.  This matters more than it looks: for a
graph presented by an edge list, `G.Adj` is a scan of that list, and the innermost loop of the
search calls it once per already-placed vertex per candidate per node. -/

/-- A vertex of `G` with its degree and its neighbours attached. -/
structure Row where
  /-- The vertex. -/
  vert : G.V
  /-- Its degree. -/
  deg : ℕ
  /-- Its neighbours. -/
  nbrs : List G.V

/-- The row of a vertex, relative to a list `gs` of all the vertices. -/
def row (gs : List G.V) (v : G.V) : Row G := ⟨v, G.toSimple.degree v, gs.filter (G.Adj v)⟩

theorem row_nbrs_contains {gs : List G.V} (hgs : ∀ v, v ∈ gs) (v u : G.V) :
    (row G gs v).nbrs.contains u = G.Adj v u := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem]
  show u ∈ gs.filter (G.Adj v) ↔ _
  rw [List.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hgs u, h⟩⟩

/-- Every vertex of `G` as a row. -/
def rowList (gs : List G.V) : List (Row G) := gs.map (row G gs)

/-- Every vertex of `G` paired with the rows of its neighbours: the adjacency list, tabulated
once.  The search never scans `G` for the neighbours of a vertex, and — for a sparse `G` — never
looks at more than a handful of candidates at a node. -/
def adjTable (gs : List G.V) : List (G.V × List (Row G)) :=
  let rs := rowList G gs
  gs.map fun v ↦ (v, rs.filter fun p ↦ G.Adj v p.vert)

/-- The row list of `adjTable` belonging to `u`. -/
def adjRow (u : G.V) : List (G.V × List (Row G)) → Option (List (Row G))
  | [] => none
  | (v, l) :: rest => if u = v then some l else adjRow u rest

theorem adjRow_map {f : G.V → List (Row G)} {gs : List G.V} {u : G.V}
    {l : List (Row G)} (h : adjRow G u (gs.map fun v ↦ (v, f v)) = some l) : l = f u := by
  induction gs with
  | nil => simp [adjRow] at h
  | cons v rest ih =>
    rw [List.map_cons, adjRow] at h
    split at h
    · rename_i he; subst he; exact (Option.some_inj.mp h).symm
    · exact ih h

theorem mem_adjRow {gs : List G.V} (hgs : ∀ v, v ∈ gs) {u b : G.V} {l : List (Row G)}
    (h : adjRow G u (adjTable G gs) = some l) (hb : G.Adj u b = true) : row G gs b ∈ l := by
  rw [adjTable] at h
  rw [adjRow_map G h]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨b, hgs b, rfl⟩, hb⟩

/-! ## The candidates at a node -/

/-- The ranks symmetry breaking makes `a`'s image rank at or above: the images of the vertices
already placed that come just before `a` in a class of interchangeable vertices.  Computed once at
a node, since it does not depend on the candidate. -/
def symLo (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (a : H.V) (pre : List (H.V × G.V)) :
    List ℕ :=
  pre.filterMap fun q ↦ if pairs.contains (q.1, a) then some (rank q.2) else none

/-- And the ranks it must stay at or below: the images of those that come just after. -/
def symHi (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (a : H.V) (pre : List (H.V × G.V)) :
    List ℕ :=
  pre.filterMap fun q ↦ if pairs.contains (a, q.1) then some (rank q.2) else none

/-- The test a candidate has to pass to be worth trying as the image of `a`: it must be compatible
with everything already placed, its degree must be at least `da = H.toSimple.degree a`, and its
rank must lie between `lo` and `hi`.  All three are passed in so that the list is scanned with
them fixed.  This is `compat` against all of `pre`, except that adjacency in `G` is read off the
candidate's own neighbour list. -/
def candKeep (rank : G.V → ℕ) (a : H.V) (pre : List (H.V × G.V)) (da : ℕ) (lo hi : List ℕ)
    (p : Row G) : Bool :=
  pre.all (fun q ↦ decide (p.vert ≠ q.2) && (H.Adj a q.1 == p.nbrs.contains q.2)) &&
    decide (da ≤ p.deg) && lo.all (fun m ↦ decide (m ≤ rank p.vert)) &&
    hi.all fun m ↦ decide (rank p.vert ≤ m)

theorem candKeep_row {gs : List G.V} (hgs : ∀ v, v ∈ gs) {rank : G.V → ℕ} {a : H.V}
    {pre : List (H.V × G.V)} {da : ℕ} {lo hi : List ℕ} {b : G.V}
    (hc : pre.all (compat H G (a, b)) = true) (hd : da ≤ G.toSimple.degree b)
    (hlo : ∀ m ∈ lo, m ≤ rank b) (hhi : ∀ m ∈ hi, rank b ≤ m) :
    candKeep H G rank a pre da lo hi (row G gs b) = true := by
  rw [candKeep, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, by simpa [row] using hd⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at hc ⊢
    intro q hq
    rw [row_nbrs_contains G hgs]
    exact hc q hq
  · simpa [row] using hlo
  · simpa [row] using hhi

/-- The vertices of `G` worth trying as the image of `a`, given the assignments `pre` already
made: those in the neighbourhood of the pivot, if there is one, that pass `candKeep`. -/
def candList (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (rs : List (Row G))
    (nb : List (G.V × List (Row G))) (a : H.V) (pre : List (H.V × G.V)) : List G.V :=
  let pool := match pivot H G a pre with
    | some u => (adjRow G u nb).getD rs
    | none => rs
  (pool.filter (candKeep H G rank a pre (H.toSimple.degree a)
    (symLo H G rank pairs a pre) (symHi H G rank pairs a pre))).map Row.vert

/-- **The pruning is sound**: a vertex that occurs in a solution is offered as a candidate. -/
theorem mem_candList {gs : List G.V} (hgs : ∀ v, v ∈ gs) (rank : G.V → ℕ)
    (pairs : List (H.V × H.V)) (a : H.V) (pre : List (H.V × G.V))
    (b : G.V) (l : List (H.V × G.V)) (h : goalAsg H G rank pairs (l ++ (a, b) :: pre) = true) :
    b ∈ candList H G rank pairs (rowList G gs) (adjTable G gs) a pre := by
  rw [goalAsg, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hd⟩, hsort⟩ := h
  have hab : (a, b) ∈ l ++ (a, b) :: pre := by simp
  have hpre : ∀ q ∈ pre, q ∈ l ++ (a, b) :: pre := fun q hq ↦ by simp [hq]
  have hlo : ∀ m ∈ symLo H G rank pairs a pre, m ≤ rank b := by
    intro m hm
    obtain ⟨q, hq, hmq⟩ := List.mem_filterMap.mp hm
    split at hmq
    · rename_i hc
      cases hmq
      exact sortedAsg_le H G hsort (List.contains_iff_mem.mp hc) (hpre q hq) hab rfl rfl
    · exact absurd hmq (by simp)
  have hhi : ∀ m ∈ symHi H G rank pairs a pre, rank b ≤ m := by
    intro m hm
    obtain ⟨q, hq, hmq⟩ := List.mem_filterMap.mp hm
    split at hmq
    · rename_i hc
      cases hmq
      exact sortedAsg_le H G hsort (List.contains_iff_mem.mp hc) hab (hpre q hq) rfl rfl
    · exact absurd hmq (by simp)
  have hcompat : pre.all (compat H G (a, b)) = true := by
    have hv' := validAsg_of_append H G hv
    rw [validAsg, Bool.and_eq_true] at hv'
    exact hv'.1
  have hdeg : H.toSimple.degree a ≤ G.toSimple.degree b := by
    rw [List.all_eq_true] at hd
    simpa using hd (a, b) (by simp)
  have hrs : row G gs b ∈ rowList G gs := List.mem_map.mpr ⟨b, hgs b, rfl⟩
  simp only [candList]
  refine List.mem_map.mpr ⟨row G gs b, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · split
    · next u hpv =>
      obtain ⟨x, hx, hax⟩ := pivot_spec H G hpv
      have hc := List.all_eq_true.mp hcompat (x, u) hx
      rw [compat, Bool.and_eq_true, beq_iff_eq] at hc
      have hub : G.Adj u b = true := by rw [G.symm u b, ← hc.2, hax]
      cases hn : adjRow G u (adjTable G gs) with
      | none => simpa only [hn, Option.getD_none] using hrs
      | some m => simpa only [hn, Option.getD_some] using mem_adjRow G hgs hn hub
    · exact hrs
  · exact candKeep_row H G hgs hcompat hdeg hlo hhi

/-! ## Reading an induced subgraph off a complete assignment -/

/-- The value an assignment list gives to `x`, if any. -/
def lookupV (x : H.V) : List (H.V × G.V) → Option G.V
  | [] => none
  | (k, v) :: rest => if x = k then some v else lookupV x rest

theorem lookupV_isSome (r : List (H.V × G.V)) (x : H.V) (h : x ∈ r.map Prod.fst) :
    (lookupV H G x r).isSome := by
  induction r with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    rw [lookupV]
    split
    · simp
    · rename_i hne
      simp only [List.map_cons, List.mem_cons] at h
      exact ih (h.resolve_left hne)

theorem mem_of_lookupV {r : List (H.V × G.V)} {x : H.V} {b : G.V}
    (h : lookupV H G x r = some b) : (x, b) ∈ r := by
  induction r with
  | nil => simp [lookupV] at h
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    rw [lookupV] at h
    split at h
    · rename_i he; subst he; simp only [Option.some_inj] at h; subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- The map on vertices read off a complete assignment. -/
def asgFun (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst) (x : H.V) : G.V :=
  (lookupV H G x r).get (lookupV_isSome H G r x (hcov x))

theorem asgFun_mem (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst) (x : H.V) :
    (x, asgFun H G r hcov x) ∈ r :=
  mem_of_lookupV H G (Option.some_get _).symm

variable {H G}

variable {rank : G.V → ℕ} {pairs : List (H.V × H.V)}

theorem compat_asgFun {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hg : goalAsg H G rank pairs r = true) {x y : H.V} (hxy : x ≠ y) :
    compat H G (x, asgFun H G r hcov x) (y, asgFun H G r hcov y) = true := by
  rw [goalAsg, Bool.and_eq_true, Bool.and_eq_true] at hg
  refine ((validAsg_iff H G r).mp hg.1.1).forall ?_ (asgFun_mem H G r hcov x)
    (asgFun_mem H G r hcov y) ?_
  · intro p q h; rw [compat_comm]; exact h
  · simp [hxy]

theorem asgFun_adj_eq {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hg : goalAsg H G rank pairs r = true) (x y : H.V) :
    G.Adj (asgFun H G r hcov x) (asgFun H G r hcov y) = H.Adj x y := by
  by_cases hxy : x = y
  · subst hxy
    have h1 : G.Adj (asgFun H G r hcov x) (asgFun H G r hcov x) = false := by
      simpa using G.loopless _
    have h2 : H.Adj x x = false := by simpa using H.loopless x
    rw [h1, h2]
  · have h := compat_asgFun (hcov := hcov) hg hxy
    rw [compat, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2.symm

theorem asgFun_injective {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hg : goalAsg H G rank pairs r = true) : Function.Injective (asgFun H G r hcov) := by
  intro x y h
  by_contra hxy
  have hc := compat_asgFun (hcov := hcov) hg hxy
  rw [compat, Bool.and_eq_true] at hc
  exact absurd h (by simpa using hc.1)

/-- The induced subgraph a complete, consistent assignment describes. -/
def ofAsg (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst)
    (hg : goalAsg H G rank pairs r = true) : H.InducedSubgraphOf G where
  toFun := asgFun H G r hcov
  injective' := asgFun_injective hg
  map_adj' x y h := by rw [asgFun_adj_eq hg]; exact h
  adj_map' x y h := by rwa [asgFun_adj_eq hg] at h

/-! ## Symmetry breaking

A class of interchangeable vertices of `H` — see `Algorithms/Twins.lean` — turns one embedding
into `|C|!` of them, all found and rejected separately.  `sortedAsg` keeps only the one whose
images come in increasing order of rank, and the two theorems here say that loses nothing: an
embedding composed with an automorphism of `H` is again an embedding, and the permutation that
sorts a class is such an automorphism.  For a pattern with no edges, where every vertex is
interchangeable with every other, this is the difference between choosing a sequence and choosing
a set. -/

/-- **Relabelling an embedding along an automorphism of the pattern.** -/
def reindex (f : H.InducedSubgraphOf G) {σ : H.V → H.V} (hinj : Function.Injective σ)
    (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) : H.InducedSubgraphOf G where
  toFun x := f (σ x)
  injective' := f.injective.comp hinj
  map_adj' _ _ h := f.map_adj (by rw [hadj]; exact h)
  adj_map' _ _ h := by rw [← hadj]; exact f.adj_map h

/-- **Every embedding can be relabelled so that each class of interchangeable vertices gets its
images in increasing order of rank.** -/
theorem exists_sorted_classes {hs : List H.V} (rank : G.V → ℕ) (hcov : ∀ x : H.V, x ∈ hs) :
    ∀ (cs : List (List H.V)), (∀ C ∈ cs, classOk H hs C = true) →
      List.Pairwise (fun A B ↦ ∀ x ∈ A, x ∉ B) cs → H.InducedSubgraphOf G →
      ∃ g : H.InducedSubgraphOf G, ∀ C ∈ cs,
        List.IsChain (fun a b ↦ rank (g a) ≤ rank (g b)) C
  | [], _, _, f => ⟨f, by simp⟩
  | C :: rest, hok, hdisj, f => by
    obtain ⟨hCrest, hrest⟩ := List.pairwise_cons.mp hdisj
    obtain ⟨g₁, hs₁⟩ :=
      exists_sorted_classes rank hcov rest (fun D hD ↦ hok D (List.mem_cons_of_mem _ hD)) hrest f
    have hCok := hok C (List.mem_cons_self ..)
    have hCnd : C.Nodup := by
      rw [classOk, Bool.and_eq_true, Bool.and_eq_true] at hCok
      exact of_decide_eq_true hCok.1.1
    obtain ⟨σ, hσC, hσout, hinj, hchain⟩ := exists_sort_perm C hCnd fun x ↦ rank (g₁ x)
    refine ⟨reindex g₁ hinj (adj_perm hCok hcov hσC hσout hinj), fun D hD ↦ ?_⟩
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hchain
    · refine (hs₁ D hD).imp_of_mem_imp fun a b ha hb h ↦ ?_
      show rank (g₁ (σ a)) ≤ rank (g₁ (σ b))
      rw [hσout a fun hac ↦ hCrest D hD a hac ha, hσout b fun hbc ↦ hCrest D hD b hbc hb]
      exact h

/-- **The pairs the search keeps in order lose no embedding.** -/
theorem exists_sorted_pairs {hs : List H.V} (rank : G.V → ℕ) (hcov : ∀ x : H.V, x ∈ hs)
    (f : H.InducedSubgraphOf G) :
    ∃ g : H.InducedSubgraphOf G, ∀ p ∈ symPairs H hs, rank (g p.1) ≤ rank (g p.2) := by
  rw [symPairs]
  split
  · rename_i hchk
    rw [Bool.and_eq_true, List.all_eq_true] at hchk
    obtain ⟨g, hsorted⟩ := exists_sorted_classes rank hcov _ hchk.1 (pairwise_of_disjOk hchk.2) f
    refine ⟨g, fun p hp ↦ ?_⟩
    obtain ⟨C, hC, hp⟩ := List.mem_flatMap.mp hp
    exact consecPairs_of_isChain (hsorted C hC) p hp
  · exact ⟨f, by simp⟩

/-! ## The search -/

variable (H G)

/-- The rank the symmetry breaking orders the vertices of `G` by: where the roster lists them. -/
def hostRank (rG : Roster G.V) (v : G.V) : ℕ := rG.toList.idxOf v

/-- The assignment the search finds, before it is turned into an `InducedSubgraphOf`. -/
def searchAsg (rH : Roster H.V) (rG : Roster G.V) : Option (List (H.V × G.V)) :=
  if Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E then
    Backtrack.dfs
      (candList H G (hostRank G rG) (symPairs H (searchOrder H rH.toList))
        (rowList G rG.toList) (adjTable G rG.toList))
      (goalAsg H G (hostRank G rG) (symPairs H (searchOrder H rH.toList)))
      (searchOrder H rH.toList) []
  else none

variable {H G}

theorem searchAsg_goal {rH : Roster H.V} {rG : Roster G.V} {r : List (H.V × G.V)}
    (h : searchAsg H G rH rG = some r) :
    goalAsg H G (hostRank G rG) (symPairs H (searchOrder H rH.toList)) r = true := by
  rw [searchAsg] at h
  split at h
  · exact Backtrack.goal_of_dfs_eq_some h
  · exact absurd h (by simp)

theorem searchAsg_cov {rH : Roster H.V} {rG : Roster G.V} {r : List (H.V × G.V)}
    (h : searchAsg H G rH rG = some r) (x : H.V) : x ∈ r.map Prod.fst := by
  rw [searchAsg] at h
  split at h
  · rw [Backtrack.keys_of_dfs_eq_some h]
    simpa using mem_searchOrder H rH.mem_toList x
  · exact absurd h (by simp)

variable (H G)

/-- **Is `H` an induced subgraph of `G`?**  Returns a witness if so.  See
`isEmpty_inducedSubgraphOf_of_eq_none` for the other half of the answer. -/
def findInducedSubgraph (rH : Roster H.V) (rG : Roster G.V) : Option (H.InducedSubgraphOf G) :=
  Option.pmap (p := fun r ↦ (∀ x : H.V, x ∈ r.map Prod.fst) ∧
      goalAsg H G (hostRank G rG) (symPairs H (searchOrder H rH.toList)) r = true)
    (fun r hr ↦ ofAsg r hr.1 hr.2) (searchAsg H G rH rG)
    (fun _ hr ↦ ⟨searchAsg_cov hr, searchAsg_goal hr⟩)

theorem findInducedSubgraph_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findInducedSubgraph H G rH rG = none ↔ searchAsg H G rH rG = none :=
  Option.pmap_eq_none_iff

/-! ## Completeness -/

variable {H G}

/-- A vertex of an induced subgraph has no more neighbours than its image. -/
theorem degree_le_of_inducedSubgraphOf (f : H.InducedSubgraphOf G) (x : H.V) :
    H.toSimple.degree x ≤ G.toSimple.degree (f x) := by
  refine Finset.card_le_card_of_injOn ⇑f ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy ⊢
    exact f.map_adj hy
  · intro a _ b _ hab; exact f.injective hab

/-- An induced subgraph whose classes are in order really does satisfy the search's `goalAsg`,
degree condition and all. -/
theorem goalAsg_of_inducedSubgraphOf (rank : G.V → ℕ) (pairs : List (H.V × H.V))
    (f : H.InducedSubgraphOf G) (hs : List H.V) (hnd : hs.Nodup)
    (hsort : ∀ p ∈ pairs, rank (f p.1) ≤ rank (f p.2)) :
    goalAsg H G rank pairs ((hs.map fun x ↦ (x, f x)).reverse) = true := by
  rw [goalAsg, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [validAsg_iff, List.pairwise_reverse, List.pairwise_map]
    refine hnd.imp ?_
    intro x y hxy
    rw [compat, Bool.and_eq_true]
    refine ⟨by simpa using fun h ↦ hxy (f.injective h).symm, ?_⟩
    rw [beq_iff_eq]
    exact (f.adj_eq y x).symm
  · rw [List.all_eq_true]
    intro p hp
    simp only [List.mem_reverse, List.mem_map] at hp
    obtain ⟨x, _, rfl⟩ := hp
    simpa using degree_le_of_inducedSubgraphOf f x
  · rw [sortedAsg, List.all_eq_true]
    intro p hp
    rw [List.all_eq_true]
    rintro q hq
    rw [List.all_eq_true]
    rintro r hr
    simp only [List.mem_reverse, List.mem_map] at hq hr
    obtain ⟨x, -, rfl⟩ := hq
    obtain ⟨y, -, rfl⟩ := hr
    by_cases hx : x = p.1
    · by_cases hy : y = p.2
      · subst hx; subst hy; simp [hsort p hp]
      · simp [hy]
    · simp [hx]

/-- **Completeness**: when the search comes back empty, `H` is not an induced subgraph of `G`. -/
theorem isEmpty_inducedSubgraphOf_of_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findInducedSubgraph H G rH rG = none) : IsEmpty (H.InducedSubgraphOf G) := by
  rw [findInducedSubgraph_eq_none_iff, searchAsg] at h
  refine ⟨fun f ↦ ?_⟩
  split at h
  · -- the embedding is first relabelled to one the symmetry test accepts
    obtain ⟨g, hg⟩ := exists_sorted_pairs (hs := searchOrder H rH.toList) (hostRank G rG)
      (mem_searchOrder H rH.mem_toList) f
    have hsol : ((searchOrder H rH.toList).map fun x ↦ (x, g x)).map Prod.fst =
        searchOrder H rH.toList := by
      simp [Function.comp_def]
    have hn := Backtrack.dfs_eq_none (mem_candList H G rG.mem_toList _ _) h hsol
    rw [List.append_nil,
      goalAsg_of_inducedSubgraphOf _ _ g _ (searchOrder_nodup H rH.toList) hg] at hn
    exact absurd hn (by simp)
  · exact absurd (show Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E from
      ⟨f.toSubgraphOf.card_le, f.toSubgraphOf.E_le⟩) ‹_›

/-- `H` is an induced subgraph of `G` exactly when the search fails to find one. -/
theorem isEmpty_inducedSubgraphOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.InducedSubgraphOf G) ↔ findInducedSubgraph H G rH rG = none := by
  refine ⟨fun h ↦ ?_, isEmpty_inducedSubgraphOf_of_eq_none⟩
  rcases hm : findInducedSubgraph H G rH rG with _ | f
  · rfl
  · exact (h.false f).elim

end CGraph
