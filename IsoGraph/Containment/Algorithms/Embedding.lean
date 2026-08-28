import IsoGraph.Containment.Defs
import IsoGraph.Containment.Algorithms.Backtrack
import IsoGraph.Containment.Algorithms.Twins

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Searching for a copy of one graph inside another

Two of the containment relations are an injection `H.V → G.V` with a condition on each pair of
vertices, and differ only in what that condition is:

* for an **induced subgraph**, the two graphs must agree — a non-edge of `H` is as informative as
  an edge;
* for an ordinary **subgraph**, only an edge of `H` has to be matched by an edge of `G`.

This module is the search both of them run, with the difference isolated in `CGraph.edgeOk`, a
single `Bool` test taken by a flag `ind`.  `Algorithms/InducedSubgraph.lean` and
`Algorithms/Subgraph.lean` are the two callers; each turns a finished assignment into its own
witness type and proves its own completeness statement, and everything between the two — the
search order, the pruning, the tabulated host, the symmetry breaking — is here and is shared.

The problem is NP-hard either way, so the search is a backtracking one, over `Backtrack.dfs`.
Five things keep it from being the naive enumeration of all `card G.V ^ card H.V` maps.

* **The order.**  `CGraph.searchOrder` picks the vertices of `H` greedily: at each step the vertex
  with the most neighbours already chosen, breaking ties by degree.  After the first vertex, every
  subsequent one is (for a connected `H`) adjacent to something already placed, so its candidates
  are confined to the neighbourhood of a vertex that is already fixed.  Any order at all gives a
  correct search, which is why the order is chosen by a heuristic that is never reasoned about:
  `searchOrder` simply checks at run time that what the heuristic produced is a duplicate-free
  list of every vertex, and falls back on the roster if it is not.
* **Consistency.**  A candidate `b` for `a` must differ from every vertex already used and must
  pass `CGraph.edgeOk` against it — that is `CGraph.compat`.  For an induced subgraph this is a
  much stronger filter, since it rejects a candidate for having an edge as readily as for lacking
  one; for an ordinary subgraph only the edges of `H` constrain anything.
* **Degrees.**  A vertex of `H` of degree `d` can only go to a vertex of `G` of degree at least
  `d`.  This one is not a property of the partial assignment but of the whole embedding, so it
  lives in `goalAsg` and is projected out of it in `mem_candList`.
* **Symmetry.**  Interchangeable vertices of `H` — `Algorithms/Twins.lean` — are made to take
  their images in increasing order of `CGraph.hostRank`, so that of the `|C|!` embeddings a class
  of size `|C|` admits, exactly one is looked for.  Like the degree test this is a condition on
  the whole embedding, `CGraph.sortedAsg` in `goalAsg`, and `mem_candList` projects it out as the
  interval `CGraph.symLo`–`CGraph.symHi` the next image has to fall in.
* **Room to finish.**  Once a class is ordered, the images of the vertices still to come in it are
  all distinct and all outrank the one being placed now, so `a`'s image has to leave
  `CGraph.tailCount` ranks free above it.  This is the prune that stops the search from exploring
  prefixes that are perfectly consistent but can never be completed, and on the pattern with no
  edges it is worth more than everything else here put together.  `rank_add_tailCount_lt` is the
  proof that a genuine embedding satisfies it.

The candidates a node even looks at are cut down before any of the tests run.  `CGraph.preAdj`
and `CGraph.preOther` sort the assignments already made into the images of `a`'s neighbours and
the images to test against — a question about `H` alone, so it is asked once at the node rather
than once per candidate — and if `a` has a neighbour already placed at `u`, the candidates are
read straight off `u`'s row of the adjacency table rather than filtered out of all of `G`.  That
is sound for both relations, since an edge of `H` is an edge of `G` under either one.  It is not
extra pruning — the consistency test would reject the others anyway — but it is the difference
between a node costing `card G.V` and costing the degree of `u`, and what comes out of `u`'s row
needs no further testing against `u`.  For the same reason the pool is cut off below
`symLo` with a `dropWhile` before it is filtered: `rowList` happens to list the rows in rank
order, so the rows below the floor are a prefix.  Soundness does not depend on that happening —
everything a `dropWhile` drops has too low a rank to be the answer whatever the order.

`CGraph.adjTable` and `CGraph.Row` are what make that cheap.  Everything the search asks about a
vertex of `G` is tabulated once, before the search starts: its degree, its neighbours, and the
rows of its neighbours.  This matters more than it looks.  For a graph presented by an edge list —
which is how most of the named graphs here are built — `G.Adj` is a scan of that list, and the
innermost loop of the search asks for adjacency once per placed vertex per candidate per node;
reading it off the candidate's own neighbour list instead took the running time of a
representative search down by an order of magnitude.

The two things the search asks about a vertex of the *pattern* are tabulated for the same reason
and by the same means, `Backtrack.tabulate`: its degree, which is a count along the enumeration,
and `CGraph.tailCount`, which walks a chain of interchangeable vertices and re-filters all of them
at every step.  Neither depends on the partial assignment, so both are one number per vertex of
`H`; asked where they are used they are a scan per node instead, and taking them out of the node
halves `C₂₄ ⊑ McGee` and `C₂₅ ⊆ grid 5×5` and takes 55% off `E₁₉ ⊑ grid 6×6`, where the class of
interchangeable vertices is the whole pattern and the chain is as long as it can be.

Two counting tests — `card H.V ≤ card G.V` and `H.E ≤ G.E` — reject hopeless pairs before the
search starts, which matters because injectivity alone would only make the search fail at depth
`card G.V + 1`.  Both hold of a subgraph as well as of an induced one.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

/-! ## A search order for the vertices of the pattern -/

/-- How much a vertex is worth taking next: first the number of neighbours already taken, then the
degree.  Packed into one natural number so that it can be compared with `<`.

The vertex list `vs` and `nn = card H.V + 1` are passed in rather than read off `H`, and the
degree is counted along `vs` rather than taken as `H.toSimple.degree`.  This is evaluated `O(n²)`
times per call of `searchOrder`, and the `Finset` degree — which builds `univ`, filters it and
counts the result — was three times the cost of the `countP` on its own. -/
private def orderKey (H : CGraph) (vs : List H.V) (nn : ℕ) (acc : List H.V) (v : H.V) : ℕ :=
  (acc.countP fun u ↦ H.Adj v u) * nn + vs.countP (H.Adj v)

/-- The entry of `b :: rest` with the highest `orderKey`, ties going to the earliest.  The
incumbent's key is carried along rather than recomputed at every step, which halves the number of
keys the greedy pass evaluates. -/
private def bestKey (H : CGraph) (vs : List H.V) (nn : ℕ) (acc : List H.V) :
    H.V → ℕ → List H.V → H.V
  | b, _, [] => b
  | b, kb, u :: rest =>
    let ku := orderKey H vs nn acc u
    if kb < ku then bestKey H vs nn acc u ku rest else bestKey H vs nn acc b kb rest

/-- Greedily take the vertex of highest `orderKey`, `n` times. -/
private def searchOrderAux (H : CGraph) (vs : List H.V) (nn : ℕ) :
    ℕ → List H.V → List H.V → List H.V
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | n + 1, v :: rest, acc =>
    let best := bestKey H vs nn acc v (orderKey H vs nn acc v) rest
    searchOrderAux H vs nn n ((v :: rest).erase best) (best :: acc)

/-- The order in which the search assigns the vertices of `H`.  The greedy heuristic is checked at
run time rather than reasoned about: if it fails to produce a duplicate-free list of all the
vertices — which it will not — the roster is used instead.

The heuristic's output is `let`-bound, and the coverage test is a `List.all` over the enumeration
rather than the `Fintype` `∀`.  Both matter: written as three occurrences of the same call, with
one of them under a binder, the check re-ran the whole greedy pass once per vertex, which at order
six cost a factor of twenty-five. -/
def searchOrder (H : CGraph) (hs : List H.V) : List H.V :=
  let vs := FinEnum.toList H.V
  let raw := searchOrderAux H vs (FinEnum.card H.V + 1) hs.length hs []
  if decide raw.Nodup && vs.all (fun x ↦ raw.contains x) then raw else hs.dedup

theorem searchOrder_nodup (H : CGraph) (hs : List H.V) : (searchOrder H hs).Nodup := by
  simp only [searchOrder]
  split
  · rename_i h
    rw [Bool.and_eq_true] at h
    exact of_decide_eq_true h.1
  · exact hs.nodup_dedup

theorem mem_searchOrder (H : CGraph) {hs : List H.V} (hmem : ∀ x, x ∈ hs) (x : H.V) :
    x ∈ searchOrder H hs := by
  simp only [searchOrder]
  split
  · rename_i h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    exact List.contains_iff_mem.mp (h.2 x (H.mem_toList x))
  · exact List.mem_dedup.mpr (hmem x)

/-! ## The one thing the two searches disagree about -/

/-- What an edge of `H` and the corresponding edge of `G` must satisfy.  With `ind` the two have to
agree, which is the induced subgraph relation; without it an edge of `H` has to be matched but a
non-edge is free, which is the ordinary subgraph relation.

Written to branch on `h` first, because the search's inner loop knows `h` — whether two vertices
of the *pattern* are adjacent — long before it knows `g`, and looking `g` up is the expensive
half.  A caller that guards the lookup this way never pays for it on a non-edge of `H` when `ind`
is false, which on a sparse pattern is nearly every pair. -/
def edgeOk (ind : Bool) (h g : Bool) : Bool := if h then g else !ind || !g

theorem edgeOk_of_eq {ind h g : Bool} (he : h = g) : edgeOk ind h g = true := by
  subst he; cases ind <;> cases h <;> rfl

/-- Under either relation an edge of `H` is an edge of `G`. -/
theorem adj_of_edgeOk {ind h g : Bool} (hok : edgeOk ind h g = true) (hh : h = true) : g = true := by
  subst hh; simpa [edgeOk] using hok

/-- Under the induced relation the two agree outright. -/
theorem eq_of_edgeOk {h g : Bool} (hok : edgeOk true h g = true) : h = g := by
  cases h <;> cases g <;> simp_all [edgeOk]

/-! ## Consistency of a partial assignment -/

variable (H G : CGraph) (ind : Bool)

/-- Two assignments `x ↦ u` and `y ↦ v` are compatible when they are injective on the two vertices
and their adjacency passes `edgeOk`, in both directions. -/
def compat (p q : H.V × G.V) : Bool :=
  decide (p.2 ≠ q.2) && edgeOk ind (H.Adj p.1 q.1) (G.Adj p.2 q.2)

theorem compat_comm (p q : H.V × G.V) : compat H G ind p q = compat H G ind q p := by
  have h : (p.2 ≠ q.2) = (q.2 ≠ p.2) := propext ne_comm
  simp only [compat, h, H.symm p.1 q.1, G.symm p.2 q.2]

/-- Every two assignments in the list are compatible. -/
def validAsg : List (H.V × G.V) → Bool
  | [] => true
  | p :: rest => rest.all (compat H G ind p) && validAsg rest

theorem validAsg_iff (l : List (H.V × G.V)) :
    validAsg H G ind l = true ↔ l.Pairwise fun p q ↦ compat H G ind p q = true := by
  induction l with
  | nil => simp [validAsg]
  | cons p rest ih => simp [validAsg, List.pairwise_cons, ih]

theorem validAsg_of_append {l m : List (H.V × G.V)} (h : validAsg H G ind (l ++ m) = true) :
    validAsg H G ind m = true := by
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

/-- The vertices whose image must rank below `a`'s: those paired with `a` in a class of
interchangeable vertices.  In practice there is at most one. -/
def symBefore (pairs : List (H.V × H.V)) (a : H.V) : List H.V :=
  pairs.filterMap fun p ↦ if p.2 = a then some p.1 else none

/-- And those whose image must rank above it. -/
def symAfter (pairs : List (H.V × H.V)) (a : H.V) : List H.V :=
  pairs.filterMap fun p ↦ if p.1 = a then some p.2 else none

theorem mem_symBefore {pairs : List (H.V × H.V)} {a x : H.V} (hx : x ∈ symBefore H pairs a) :
    (x, a) ∈ pairs := by
  obtain ⟨p, hp, hpx⟩ := List.mem_filterMap.mp hx
  by_cases h2 : p.2 = a
  · rw [if_pos h2] at hpx
    rw [(Option.some.inj hpx).symm, ← h2]
    simpa using hp
  · rw [if_neg h2] at hpx
    exact absurd hpx (by simp)

theorem mem_symAfter {pairs : List (H.V × H.V)} {a x : H.V} (hx : x ∈ symAfter H pairs a) :
    (a, x) ∈ pairs := by
  obtain ⟨p, hp, hpx⟩ := List.mem_filterMap.mp hx
  by_cases h1 : p.1 = a
  · rw [if_pos h1] at hpx
    rw [(Option.some.inj hpx).symm, ← h1]
    simpa using hp
  · rw [if_neg h1] at hpx
    exact absurd hpx (by simp)

/-- How many vertices still have to be placed after `a` in its class: the length of the chain of
`pairs` leading out of `a`.  Their images all outrank `a`'s and are all distinct, so `a`'s image
has to leave that many ranks free above it — which is what `goalAsg` asks for, and it is the prune
that keeps the search from exploring prefixes that can never be finished.  `fuel` bounds the walk;
`pairs.length` is always enough, since the chain never repeats a pair. -/
def tailCount : ℕ → List (H.V × H.V) → H.V → ℕ
  | 0, _, _ => 0
  | fuel + 1, pairs, a =>
    match symAfter H pairs a with
    | x :: _ => tailCount fuel pairs x + 1
    | [] => 0

/-- What the search is looking for: a consistent assignment that also respects the
symmetry-breaking order and the room that order needs above each image.  Neither is local to a
pair, which is why they are stated here rather than in `compat`; `mem_candList` projects them back
out for use as a filter.  `n` is the number of vertices of `G`.

The degree bound the candidate list also filters on is *not* here, though it is a necessary
condition too: a complete consistent assignment satisfies it whether it is tested or not
(`degree_le_of_validAsg`), and a `Finset` degree per assigned vertex per leaf is not cheap. -/
def goalAsg (rank : G.V → ℕ) (n : ℕ) (pairs : List (H.V × H.V)) (asg : List (H.V × G.V)) : Bool :=
  validAsg H G ind asg &&
    sortedAsg H G rank pairs asg &&
    asg.all fun p ↦ decide (rank p.2 + tailCount H pairs.length pairs p.1 < n)

/-- The images of the already-placed neighbours of `a`.  Every candidate for `a` has to be
adjacent to all of them, and to the first of them in particular — which is why the pool of
candidates can be its neighbourhood rather than all of `G`.

Which vertices of `H` these are is a question about the *pattern*, so it does not depend on the
candidate and is asked once at the node.  Asking it per candidate instead, inside the filter, is
what `candKeep` used to do; the filter runs over the whole pool. -/
def preAdj (a : H.V) (pre : List (H.V × G.V)) : List G.V :=
  (pre.filter fun q ↦ H.Adj a q.1).map Prod.snd

/-- The images of the already-placed *non*-neighbours of `a`: what the candidate has to differ
from, and — for an induced search — stay non-adjacent to. -/
def preNon (a : H.V) (pre : List (H.V × G.V)) : List G.V :=
  (pre.filter fun q ↦ !H.Adj a q.1).map Prod.snd

theorem mem_preAdj {a : H.V} {pre : List (H.V × G.V)} {u : G.V} (h : u ∈ preAdj H G a pre) :
    ∃ x, (x, u) ∈ pre ∧ H.Adj a x = true := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  obtain ⟨hq, ha⟩ := List.mem_filter.mp hq
  exact ⟨q.1, hq, ha⟩

theorem mem_preNon {a : H.V} {pre : List (H.V × G.V)} {u : G.V} (h : u ∈ preNon H G a pre) :
    ∃ x, (x, u) ∈ pre ∧ H.Adj a x = false := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  obtain ⟨hq, ha⟩ := List.mem_filter.mp hq
  exact ⟨q.1, hq, by simpa using ha⟩

/-- The images a candidate is tested against.  A non-induced search asks nothing of the images of
`a`'s neighbours beyond being different from the candidate, and injectivity is asked of every
placed vertex alike, so it can skip the sort and take them all — one pass over `pre` at the node
instead of two, and no query of the pattern's adjacency in either. -/
def preOther (a : H.V) (pre : List (H.V × G.V)) : List G.V :=
  if ind then preNon H G a pre else pre.map Prod.snd

theorem mem_preOther {a : H.V} {pre : List (H.V × G.V)} {u : G.V}
    (h : u ∈ preOther H G ind a pre) : ∃ x, (x, u) ∈ pre ∧ (ind = true → H.Adj a x = false) := by
  rw [preOther] at h
  split at h
  · obtain ⟨x, hx, hax⟩ := mem_preNon H G h
    exact ⟨x, hx, fun _ ↦ hax⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact ⟨q.1, hq, by simp_all⟩

/-! ## Tabulating the host

Everything the search asks about a vertex of `G` — its degree, and whether it is adjacent to some
other vertex — is tabulated before the search starts.  This matters more than it looks: for a
graph presented by an edge list, `G.Adj` is a scan of that list, and the innermost loop of the
search calls it once per already-placed vertex per candidate per node. -/

/-- A vertex of `G` with its degree and its neighbours attached. -/
structure Row where
  /-- The vertex. -/
  vert : G.V
  /-- An upper bound for its degree: how many times a neighbour of it is listed in `gs`, which is
  the degree exactly when `gs` lists every vertex once.  The searches only ever ask whether the
  degree is *large enough* for the vertex being placed, so an overestimate is sound; and the count
  is the length of `nbrs`, which is already being built, where `SimpleGraph.degree` builds
  `Finset.univ` and filters it — fifty times dearer on a six-vertex graph, and this runs once per
  vertex per search. -/
  deg : ℕ
  /-- Its neighbours. -/
  nbrs : List G.V
  /-- Its position in `gs`: the rank symmetry breaking orders images by.  Tabulated because
  `List.idxOf` is a scan, and the innermost loop would otherwise run one per candidate per node. -/
  rk : ℕ

/-- The row of a vertex, relative to a list `gs` of all the vertices. -/
def row (gs : List G.V) (v : G.V) : Row G :=
  let nbrs := gs.filter (G.Adj v)
  ⟨v, nbrs.length, nbrs, gs.idxOf v⟩

theorem row_nbrs_contains {gs : List G.V} (hgs : ∀ v, v ∈ gs) (v u : G.V) :
    (row G gs v).nbrs.contains u = G.Adj v u := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem]
  show u ∈ gs.filter (G.Adj v) ↔ _
  rw [List.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hgs u, h⟩⟩

/-- **The tabulated degree is an upper bound for the real one**, which is the direction the degree
prune needs: a vertex offered as an image has `Row.deg` at least the degree asked of it. -/
theorem degree_le_row_deg {gs : List G.V} (hgs : ∀ v, v ∈ gs) (v : G.V) :
    G.toSimple.degree v ≤ (row G gs v).deg := by
  refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
  intro u hu
  rw [SimpleGraph.mem_neighborFinset, toSimple_adj] at hu
  exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hgs u, hu⟩)

/-- Every vertex of `G` as a row. -/
def rowList (gs : List G.V) : List (Row G) := gs.map (row G gs)

/-- The adjacency table built from a row list already in hand.  Taking the rows as an argument is
what lets `searchAsgFast` build them once and use them both as the candidate pool and here;
building them twice is a quarter of what a small search costs. -/
def adjTableOf (rs : List (Row G)) (gs : List G.V) : List (G.V × List (Row G)) :=
  gs.map fun v ↦ (v, rs.filter fun p ↦ G.Adj v p.vert)

/-- Every vertex of `G` paired with the rows of its neighbours: the adjacency list, tabulated
once.  The search never scans `G` for the neighbours of a vertex, and — for a sparse `G` — never
looks at more than a handful of candidates at a node. -/
def adjTable (gs : List G.V) : List (G.V × List (Row G)) := adjTableOf G (rowList G gs) gs

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
  rw [adjTable, adjTableOf] at h
  rw [adjRow_map G h]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨b, hgs b, rfl⟩, hb⟩

/-! ## The candidates at a node -/

/-- The ranks symmetry breaking makes `a`'s image rank at or above: the images of the vertices
already placed that come just before `a` in a class.  Computed once at a node, since it does not
depend on the candidate. -/
def symLo (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (a : H.V) (pre : List (H.V × G.V)) :
    List ℕ :=
  (symBefore H pairs a).filterMap fun x ↦
    (pre.find? fun q ↦ decide (q.1 = x)).map fun q ↦ rank q.2

/-- And the ranks it must stay at or below: the images of those that come just after. -/
def symHi (rank : G.V → ℕ) (pairs : List (H.V × H.V)) (a : H.V) (pre : List (H.V × G.V)) :
    List ℕ :=
  (symAfter H pairs a).filterMap fun x ↦
    (pre.find? fun q ↦ decide (q.1 = x)).map fun q ↦ rank q.2

/-- The test a candidate has to pass to be worth trying as the image of `a`: its degree must be at
least `da = H.toSimple.degree a`, its rank must leave `tl` ranks free below `n` and lie between
`lo` and `hi`, it must be adjacent to every image in `nbrs`, and it must differ from — and for an
induced search be non-adjacent to — every image in `others`.  This is `compat` against all of
`pre`, except that the pattern's own adjacency has been decided in advance by `preAdj`/`preNon`,
and adjacency in `G` is read off the candidate's neighbour list rather than out of `G.Adj`.

Everything is passed in so that the pool is scanned with it fixed, and the tests are in increasing
order of cost: the four that are arithmetic on numbers already tabulated reject most of the pool
before either list of images is walked, and each entry of those lists costs a scan of the
candidate's neighbours.

No injectivity test guards `nbrs`: `G` has no loops, so a candidate adjacent to `u` is not `u`.
Nor would one be needed for soundness — every test here is a prune, and `goalAsg` re-checks the
lot at the leaf. -/
def candKeep (nbrs others : List G.V) (da : ℕ) (lo hi : List ℕ) (tl n : ℕ) (p : Row G) : Bool :=
  decide (da ≤ p.deg) && decide (p.rk + tl < n) &&
    lo.all (fun m ↦ decide (m ≤ p.rk)) && hi.all (fun m ↦ decide (p.rk ≤ m)) &&
    nbrs.all (fun u ↦ p.nbrs.contains u) &&
    others.all (fun u ↦ decide (p.vert ≠ u) && (!ind || !p.nbrs.contains u))

theorem candKeep_row {gs : List G.V} (hgs : ∀ v, v ∈ gs) {nbrs others : List G.V}
    {da : ℕ} {lo hi : List ℕ} {tl n : ℕ} {b : G.V}
    (hnb : ∀ u ∈ nbrs, G.Adj b u = true)
    (hot : ∀ u ∈ others, b ≠ u ∧ edgeOk ind false (G.Adj b u) = true)
    (hd : da ≤ G.toSimple.degree b)
    (hlo : ∀ m ∈ lo, m ≤ gs.idxOf b) (hhi : ∀ m ∈ hi, gs.idxOf b ≤ m)
    (hcap : gs.idxOf b + tl < n) :
    candKeep G ind nbrs others da lo hi tl n (row G gs b) = true := by
  simp only [candKeep, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨decide_eq_true (hd.trans (degree_le_row_deg G hgs b)),
    by simpa [row] using hcap⟩, by simpa [row] using hlo⟩, by simpa [row] using hhi⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro u hu
    rw [row_nbrs_contains G hgs]
    exact hnb u hu
  · rw [List.all_eq_true]
    intro u hu
    obtain ⟨hne, hok⟩ := hot u hu
    rw [Bool.and_eq_true, row_nbrs_contains G hgs]
    exact ⟨decide_eq_true (by simpa [row] using hne), by simpa [edgeOk] using hok⟩

/-- Dropping a prefix of the pool is safe as long as everything dropped fails the test the
candidate we are looking for passes. -/
theorem mem_dropWhile {α : Type} {P : α → Bool} {l : List α} {a : α} (ha : a ∈ l)
    (hP : P a = false) : a ∈ l.dropWhile P := by
  induction l with
  | nil => exact absurd ha (by simp)
  | cons x t ih =>
    by_cases hx : P x = true
    · rw [List.dropWhile_cons_of_pos hx]
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd hx (by simp [hP])
      · exact ih ha'
    · rw [List.dropWhile_cons_of_neg (by simpa using hx)]
      exact ha

theorem foldl_max_le {l : List ℕ} {x : ℕ} :
    ∀ {a : ℕ}, a ≤ x → (∀ m ∈ l, m ≤ x) → l.foldl max a ≤ x := by
  induction l with
  | nil => exact fun ha _ ↦ ha
  | cons y t ih =>
    intro a ha h
    rw [List.foldl_cons]
    exact ih (max_le ha (h y (by simp))) fun m hm ↦ h m (by simp [hm])

/-- The pool to draw candidates from, together with the images that still have to be tested
against.  The first entry of `nbrs` is the *pivot*: its row of the adjacency table is exactly the
vertices adjacent to it, so taking that as the pool both shrinks the pool to a neighbourhood and
discharges the pivot's own test for everything in it.  With no placed neighbour — or no row for
it, which cannot happen for a table built from a complete vertex list — the pool is all of `G`
and nothing is discharged. -/
def candPool (rs : List (Row G)) (nb : List (G.V × List (Row G))) :
    List G.V → List (Row G) × List G.V
  | [] => (rs, [])
  | u :: t =>
    match adjRow G u nb with
    | some l => (l, t)
    | none => (rs, u :: t)

theorem mem_candPool_fst {gs : List G.V} (hgs : ∀ v, v ∈ gs) {nbrs : List G.V} {b : G.V}
    (hb : ∀ u ∈ nbrs, G.Adj b u = true) :
    row G gs b ∈ (candPool G (rowList G gs) (adjTable G gs) nbrs).1 := by
  have hrs : row G gs b ∈ rowList G gs := List.mem_map.mpr ⟨b, hgs b, rfl⟩
  cases nbrs with
  | nil => exact hrs
  | cons u t =>
    rw [candPool]
    split
    · next l hn => exact mem_adjRow G hgs hn (by rw [G.symm u b]; exact hb u (by simp))
    · exact hrs

theorem candPool_snd_subset {rs : List (Row G)} {nb : List (G.V × List (Row G))}
    {nbrs : List G.V} : ∀ u ∈ (candPool G rs nb nbrs).2, u ∈ nbrs := by
  cases nbrs with
  | nil => exact fun _ h ↦ h
  | cons v t =>
    rw [candPool]
    split
    · exact fun _ h ↦ List.mem_cons_of_mem _ h
    · exact fun _ h ↦ h

/-- The vertices of `G` worth trying as the image of `a`, given the assignments `pre` already
made: those in the neighbourhood of the pivot, if there is one, that pass `candKeep`.

Symmetry breaking also puts a floor under the candidate's rank, and `rowList` lists the rows in
rank order, so the pool is cut off below that floor before it is scanned rather than filtered
element by element.  `dropWhile` is sound whatever order the pool happens to be in: everything it
drops has too low a rank to be the answer.

The two things this asks about the *pattern* vertex — its degree `dg a`, and the room `tc a` its
class needs above it — are taken as functions rather than computed here, and `searchAsgFast` hands
over a `Backtrack.tabulate` of each.  Neither depends on `pre`, so each is one number per vertex of
`H` for the whole search, and each is a scan: `deg` counts along the enumeration and `tailCount`
walks the chain of pairs, re-filtering all of them at every step.  Computing them where they are
used instead costs a scan per node, which on a pattern with no edges — every vertex in one class,
so the chain is as long as the pattern — is most of the search. -/
def candList (rank : G.V → ℕ) (n : ℕ) (pairs : List (H.V × H.V)) (rs : List (Row G))
    (nb : List (G.V × List (Row G))) (dg tc : H.V → ℕ) (a : H.V) (pre : List (H.V × G.V)) :
    List G.V :=
  let cp := candPool G rs nb (preAdj H G a pre)
  let lo := symLo H G rank pairs a pre
  let hi := symHi H G rank pairs a pre
  let floor := lo.foldl max 0
  ((cp.1.dropWhile fun p ↦ decide (p.rk < floor)).filter
    (candKeep G ind cp.2 (preOther H G ind a pre) (dg a) lo hi (tc a) n)).map Row.vert

/-! ## Reading a map off a complete assignment -/

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

/-- With no repeated key, the lookup finds what was put in. -/
theorem lookupV_eq_of_mem {r : List (H.V × G.V)} (hnd : (r.map Prod.fst).Nodup)
    {p : H.V × G.V} (hp : p ∈ r) : lookupV H G p.1 r = some p.2 := by
  induction r with
  | nil => simp at hp
  | cons q rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [lookupV]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : q.1 ≠ p.1 := fun h ↦ hnd.1 (h ▸ List.mem_map_of_mem hp)
      rw [if_neg (Ne.symm hne)]
      exact ih hnd.2 hp

/-- The map on vertices read off a complete assignment. -/
def asgFun (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst) (x : H.V) : G.V :=
  (lookupV H G x r).get (lookupV_isSome H G r x (hcov x))

theorem asgFun_mem (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst) (x : H.V) :
    (x, asgFun H G r hcov x) ∈ r :=
  mem_of_lookupV H G (Option.some_get _).symm

/-- With no repeated key, the function agrees with the assignment on the nose. -/
theorem asgFun_eq_of_mem {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hnd : (r.map Prod.fst).Nodup) {p : H.V × G.V} (hp : p ∈ r) :
    asgFun H G r hcov p.1 = p.2 :=
  Option.some.inj ((Option.some_get _).trans (lookupV_eq_of_mem H G hnd hp))

/-! ## What consistency alone already gives

An assignment that is pairwise consistent is an embedding of whatever part of `H` it covers, and
once it covers all of `H` that is all the search was looking for.  In particular it respects
degrees — a vertex is sent somewhere with at least as many neighbours — which the search would
otherwise have to test at every leaf, at the price of a `Finset` degree per assigned vertex. -/

section

variable {H G ind}

theorem validAsg_of_goalAsg {rank : G.V → ℕ} {n : ℕ} {pairs : List (H.V × H.V)}
    {r : List (H.V × G.V)} (hg : goalAsg H G ind rank n pairs r = true) :
    validAsg H G ind r = true := by
  simp only [goalAsg, Bool.and_eq_true] at hg
  exact hg.1.1

theorem compat_asgFun {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hv : validAsg H G ind r = true) {x y : H.V} (hxy : x ≠ y) :
    compat H G ind (x, asgFun H G r hcov x) (y, asgFun H G r hcov y) = true := by
  have : Std.Symm fun p q : H.V × G.V ↦ compat H G ind p q = true :=
    ⟨fun _ _ h ↦ by rwa [compat_comm]⟩
  exact ((validAsg_iff H G ind r).mp hv).forall (asgFun_mem H G r hcov x)
    (asgFun_mem H G r hcov y) (by simp [hxy])

/-- **The map is a homomorphism**, whichever relation is being searched for. -/
theorem asgFun_map_adj {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hv : validAsg H G ind r = true) {x y : H.V} (h : H.Adj x y = true) :
    G.Adj (asgFun H G r hcov x) (asgFun H G r hcov y) = true := by
  have hxy : x ≠ y := by
    rintro rfl
    rw [show H.Adj x x = false from by simpa using H.loopless x] at h
    exact absurd h (by simp)
  have hc := compat_asgFun (hcov := hcov) hv hxy
  rw [compat, Bool.and_eq_true] at hc
  exact adj_of_edgeOk hc.2 h

/-- **And it reflects edges too**, when the search was the induced one. -/
theorem asgFun_adj_map {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hv : validAsg H G true r = true) {x y : H.V}
    (h : G.Adj (asgFun H G r hcov x) (asgFun H G r hcov y) = true) : H.Adj x y = true := by
  by_cases hxy : x = y
  · subst hxy
    rw [show G.Adj (asgFun H G r hcov x) (asgFun H G r hcov x) = false from
      by simpa using G.loopless _] at h
    exact absurd h (by simp)
  · have hc := compat_asgFun (hcov := hcov) hv hxy
    rw [compat, Bool.and_eq_true] at hc
    rw [eq_of_edgeOk hc.2]
    exact h

theorem asgFun_injective {r : List (H.V × G.V)} {hcov : ∀ x : H.V, x ∈ r.map Prod.fst}
    (hv : validAsg H G ind r = true) : Function.Injective (asgFun H G r hcov) := by
  intro x y h
  by_contra hxy
  have hc := compat_asgFun (hcov := hcov) hv hxy
  rw [compat, Bool.and_eq_true] at hc
  exact absurd h (by simpa using hc.1)

/-- A vertex has no more neighbours than its image. -/
theorem degree_le_of_map_adj {emb : H.V → G.V} (hinj : Function.Injective emb)
    (hadj : ∀ {x y : H.V}, H.Adj x y = true → G.Adj (emb x) (emb y) = true) (x : H.V) :
    H.toSimple.degree x ≤ G.toSimple.degree (emb x) := by
  refine Finset.card_le_card_of_injOn emb ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy ⊢
    exact hadj hy
  · intro a _ b _ hab; exact hinj hab

/-- **A consistent assignment of every vertex respects degrees by itself.**  This is the degree
prune, and it is a theorem rather than a test: the search never has to check it, and `goal` is
free of it. -/
theorem degree_le_of_validAsg {r : List (H.V × G.V)} (hv : validAsg H G ind r = true)
    (hcov : ∀ x : H.V, x ∈ r.map Prod.fst) (hnd : (r.map Prod.fst).Nodup)
    {a : H.V} {b : G.V} (hab : (a, b) ∈ r) :
    H.toSimple.degree a ≤ G.toSimple.degree b := by
  have h := degree_le_of_map_adj (emb := asgFun H G r hcov) (asgFun_injective hv)
    (fun {_ _} hxy ↦ asgFun_map_adj hv hxy) a
  rwa [asgFun_eq_of_mem H G (hcov := hcov) hnd hab] at h

end

/-- **The pruning is sound**: a vertex that occurs in a solution is offered as a candidate.  The
degree test the candidate list applies is not part of `goalAsg`; what makes it sound is
`degree_le_of_validAsg`, which needs to know that the solution assigns every vertex of `H` and
each of them once — hence `hkcov` and `hknd`, which `Backtrack.dfs_eq_none_keys` supplies. -/
theorem mem_candList {gs : List G.V} (hgs : ∀ v, v ∈ gs) {rank : G.V → ℕ}
    (hrank : ∀ v, rank v = gs.idxOf v)
    (n : ℕ) (pairs : List (H.V × H.V)) {dg tc : H.V → ℕ} (hdg : ∀ x, dg x = H.deg x)
    (htc : ∀ x, tc x = tailCount H pairs.length pairs x) {keys : List H.V}
    (hkcov : ∀ x : H.V, x ∈ keys)
    (hknd : keys.Nodup) (a : H.V) (pre : List (H.V × G.V))
    (b : G.V) (l : List (H.V × G.V))
    (hk : (l ++ (a, b) :: pre).map Prod.fst = keys)
    (h : goalAsg H G ind rank n pairs (l ++ (a, b) :: pre) = true) :
    b ∈ candList H G ind rank n pairs (rowList G gs) (adjTable G gs) dg tc a pre := by
  simp only [goalAsg, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hsort⟩, hcap⟩ := h
  have hab : (a, b) ∈ l ++ (a, b) :: pre := by simp
  have hpre : ∀ q ∈ pre, q ∈ l ++ (a, b) :: pre := fun q hq ↦ by simp [hq]
  have hsym : ∀ (x : H.V) (m : ℕ),
      ((pre.find? fun q ↦ decide (q.1 = x)).map fun q ↦ rank q.2) = some m →
        ∃ q ∈ pre, q.1 = x ∧ rank q.2 = m := by
    intro x m hx
    cases hf : pre.find? (fun q ↦ decide (q.1 = x)) with
    | none => rw [hf] at hx; exact absurd hx (by simp)
    | some q =>
      rw [hf] at hx
      have hq1 := List.find?_some hf
      simp only [decide_eq_true_eq] at hq1
      exact ⟨q, List.mem_of_find?_eq_some hf, hq1, Option.some.inj hx⟩
  have hlo : ∀ m ∈ symLo H G rank pairs a pre, m ≤ rank b := by
    intro m hm
    obtain ⟨x, hx, hmx⟩ := List.mem_filterMap.mp hm
    obtain ⟨q, hq, hq1, hqm⟩ := hsym x m hmx
    rw [← hqm]
    exact sortedAsg_le H G hsort (mem_symBefore H hx) (hpre q hq) hab hq1 rfl
  have hhi : ∀ m ∈ symHi H G rank pairs a pre, rank b ≤ m := by
    intro m hm
    obtain ⟨x, hx, hmx⟩ := List.mem_filterMap.mp hm
    obtain ⟨q, hq, hq1, hqm⟩ := hsym x m hmx
    rw [← hqm]
    exact sortedAsg_le H G hsort (mem_symAfter H hx) hab (hpre q hq) rfl hq1
  have hcompat : pre.all (compat H G ind (a, b)) = true := by
    have hv' := validAsg_of_append H G ind hv
    rw [validAsg, Bool.and_eq_true] at hv'
    exact hv'.1
  have hdeg : dg a ≤ G.toSimple.degree b := (hdg a).le.trans
    (degree_le_of_validAsg hv (fun x ↦ by rw [hk]; exact hkcov x) (by rw [hk]; exact hknd) hab)
  have hadj : ∀ u ∈ preAdj H G a pre, G.Adj b u = true := by
    intro u hu
    obtain ⟨x, hx, hax⟩ := mem_preAdj H G hu
    have hc := List.all_eq_true.mp hcompat (x, u) hx
    rw [compat, Bool.and_eq_true] at hc
    exact adj_of_edgeOk hc.2 hax
  simp only [candList]
  refine List.mem_map.mpr ⟨row G gs b,
    List.mem_filter.mpr ⟨mem_dropWhile (mem_candPool_fst G hgs hadj) ?_, ?_⟩, rfl⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt, row]
    exact foldl_max_le (Nat.zero_le _) fun m hm ↦ hrank b ▸ hlo m hm
  · refine candKeep_row G ind hgs (fun u hu ↦ hadj u (candPool_snd_subset G u hu)) ?_ hdeg
      (fun m hm ↦ hrank b ▸ hlo m hm) (fun m hm ↦ hrank b ▸ hhi m hm) ?_
    · intro u hu
      obtain ⟨x, hx, hax⟩ := mem_preOther H G ind hu
      have hc := List.all_eq_true.mp hcompat (x, u) hx
      rw [compat, Bool.and_eq_true] at hc
      refine ⟨by simpa using hc.1, ?_⟩
      cases ind
      · simp [edgeOk]
      · exact hax rfl ▸ hc.2
    · rw [List.all_eq_true] at hcap
      have := hcap (a, b) hab
      rw [decide_eq_true_eq] at this
      rw [htc a]
      exact hrank b ▸ this

variable {H G ind}

/-! ## Symmetry breaking

A class of interchangeable vertices of `H` — see `Algorithms/Twins.lean` — turns one embedding
into `|C|!` of them, all found and rejected separately.  `sortedAsg` keeps only the one whose
images come in increasing order of rank, and the two theorems here say that loses nothing: an
embedding composed with an automorphism of `H` is again an embedding, and the permutation that
sorts a class is such an automorphism.  For a pattern with no edges, where every vertex is
interchangeable with every other, this is the difference between choosing a sequence and choosing
a set.

Both are stated for an abstract type `E` of embeddings, given only the map each one induces and
the fact that relabelling along an automorphism of `H` gives another one.  `SubgraphOf` and
`InducedSubgraphOf` each supply that, and neither search has to repeat the argument. -/

/-- **Every embedding can be relabelled so that each class of interchangeable vertices gets its
images in increasing order of rank.** -/
theorem exists_sorted_classes {E : Type} (emb : E → H.V → G.V)
    (hre : ∀ (f : E) {σ : H.V → H.V}, Function.Injective σ →
      (∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) → ∃ g : E, ∀ x, emb g x = emb f (σ x))
    {hs : List H.V} (rank : G.V → ℕ) (hcov : ∀ x : H.V, x ∈ hs) :
    ∀ (cs : List (List H.V)), (∀ C ∈ cs, classOk H hs C = true) →
      List.Pairwise (fun A B ↦ ∀ x ∈ A, x ∉ B) cs → E →
      ∃ g : E, ∀ C ∈ cs, List.IsChain (fun a b ↦ rank (emb g a) ≤ rank (emb g b)) C
  | [], _, _, f => ⟨f, by simp⟩
  | C :: rest, hok, hdisj, f => by
    obtain ⟨hCrest, hrest⟩ := List.pairwise_cons.mp hdisj
    obtain ⟨g₁, hs₁⟩ :=
      exists_sorted_classes emb hre rank hcov rest
        (fun D hD ↦ hok D (List.mem_cons_of_mem _ hD)) hrest f
    have hCok := hok C (List.mem_cons_self ..)
    have hCnd : C.Nodup := by
      rw [classOk, Bool.and_eq_true, Bool.and_eq_true] at hCok
      exact of_decide_eq_true hCok.1.1
    obtain ⟨σ, hσC, hσout, hinj, hchain⟩ := exists_sort_perm C hCnd fun x ↦ rank (emb g₁ x)
    obtain ⟨g, hgx⟩ := hre g₁ hinj (adj_perm hCok hcov hσC hσout hinj)
    refine ⟨g, fun D hD ↦ ?_⟩
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hchain.imp fun {a b} h ↦ by rw [hgx a, hgx b]; exact h
    · refine (hs₁ D hD).imp_of_mem_imp fun a b ha hb h ↦ ?_
      rw [hgx a, hgx b, hσout a fun hac ↦ hCrest D hD a hac ha,
        hσout b fun hbc ↦ hCrest D hD b hbc hb]
      exact h

/-- **The pairs the search keeps in order lose no embedding.** -/
theorem exists_sorted_pairs {E : Type} (emb : E → H.V → G.V)
    (hre : ∀ (f : E) {σ : H.V → H.V}, Function.Injective σ →
      (∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) → ∃ g : E, ∀ x, emb g x = emb f (σ x))
    {hs : List H.V} (rank : G.V → ℕ) (hcov : ∀ x : H.V, x ∈ hs) (f : E) :
    ∃ g : E, ∀ p ∈ symPairs H hs, rank (emb g p.1) ≤ rank (emb g p.2) := by
  rw [symPairs]
  split
  · rename_i hchk
    rw [Bool.and_eq_true, List.all_eq_true] at hchk
    obtain ⟨g, hsorted⟩ :=
      exists_sorted_classes emb hre rank hcov _ hchk.1 (pairwise_of_disjOk hchk.2) f
    refine ⟨g, fun p hp ↦ ?_⟩
    obtain ⟨C, hC, hp⟩ := List.mem_flatMap.mp hp
    exact consecPairs_of_isChain (hsorted C hC) p hp
  · exact ⟨f, by simp⟩

/-! ## The search -/

variable (H G ind)

/-- The rank the symmetry breaking orders the vertices of `G` by: where the roster lists them. -/
def hostRank (rG : Roster G.V) (v : G.V) : ℕ := rG.toList.idxOf v

/-- The assignment the search finds, before it is turned into a witness.  `ind` chooses which of
the two relations is being looked for. -/
def searchAsg (rH : Roster H.V) (rG : Roster G.V) : Option (List (H.V × G.V)) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    let pairs := symPairs H (searchOrder H rH.toList)
    Backtrack.dfs
      (candList H G ind (hostRank G rG) rG.toList.length pairs
        (rowList G rG.toList) (adjTable G rG.toList) H.deg (tailCount H pairs.length pairs))
      (goalAsg H G ind (hostRank G rG) rG.toList.length pairs)
      (searchOrder H rH.toList) []
  else none

/-- What `searchAsg` runs.  Everything the two closures share is computed once — in particular the
row list, which `adjTable` would otherwise build a second time, and the pattern's symmetry, which
costs a `twinClasses` call.  Written out rather than left to the compiler: it shares subterms
inside a basic block, but `adjTable`'s copy of the row list is behind a call.

The two questions about the pattern vertex are tabulated for the same reason, and it is worth more:
they are asked at every node rather than once, and `Backtrack.tabAt_tabulate` is what lets the
specification above ask them the obvious way. -/
def searchAsgFast (rH : Roster H.V) (rG : Roster G.V) : Option (List (H.V × G.V)) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    let hs := searchOrder H rH.toList
    let pairs := symPairs H hs
    let gs := rG.toList
    let rank := hostRank G rG
    let rs := rowList G gs
    let dg := Backtrack.tabAt (Backtrack.tabulate H.deg)
    let tc := Backtrack.tabAt (Backtrack.tabulate (tailCount H pairs.length pairs))
    Backtrack.dfs (candList H G ind rank gs.length pairs rs (adjTableOf G rs gs) dg tc)
      (goalAsg H G ind rank gs.length pairs) hs []
  else none

@[csimp] theorem searchAsg_eq_searchAsgFast : @searchAsg = @searchAsgFast := by
  funext H G ind rH rG
  simp only [searchAsg, searchAsgFast, Backtrack.tabAt_tabulate, adjTable]

variable {H G ind}

theorem searchAsg_goal {rH : Roster H.V} {rG : Roster G.V} {r : List (H.V × G.V)}
    (h : searchAsg H G ind rH rG = some r) :
    goalAsg H G ind (hostRank G rG) rG.toList.length (symPairs H (searchOrder H rH.toList)) r
      = true := by
  rw [searchAsg] at h
  split at h
  · exact Backtrack.goal_of_dfs_eq_some h
  · exact absurd h (by simp)

theorem searchAsg_cov {rH : Roster H.V} {rG : Roster G.V} {r : List (H.V × G.V)}
    (h : searchAsg H G ind rH rG = some r) (x : H.V) : x ∈ r.map Prod.fst := by
  rw [searchAsg] at h
  split at h
  · rw [Backtrack.keys_of_dfs_eq_some h]
    simpa using mem_searchOrder H rH.mem_toList x
  · exact absurd h (by simp)

/-! ## Completeness

What a caller has to supply to turn "the search came back empty" into "there is no such thing" is
`goalAsg_of_emb`: a genuine embedding, relabelled so that its classes are in order, passes every
test the search applies.  The three tests that are not local to a pair are proved here once. -/

/-- The room an ordered class needs: the images of the vertices after `x` in its class outrank
`emb x` and are all distinct, so there are at least that many ranks above it. -/
theorem rank_add_tailCount_lt {rank : G.V → ℕ} {n : ℕ} {pairs : List (H.V × H.V)}
    {emb : H.V → G.V} (hinj : Function.Injective emb) (hri : Function.Injective rank)
    (hrn : ∀ v, rank v < n) (hne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hsort : ∀ p ∈ pairs, rank (emb p.1) ≤ rank (emb p.2)) :
    ∀ (fuel : ℕ) (x : H.V), rank (emb x) + tailCount H fuel pairs x < n
  | 0, x => by simpa [tailCount] using hrn (emb x)
  | fuel + 1, x => by
    rw [tailCount]
    cases hx : symAfter H pairs x with
    | nil => simpa using hrn (emb x)
    | cons y t =>
      have hp := mem_symAfter H (by rw [hx]; exact List.mem_cons_self)
      have hlt : rank (emb x) < rank (emb y) :=
        lt_of_le_of_ne (hsort _ hp) fun he ↦ hne _ hp (hinj (hri he))
      have hih := rank_add_tailCount_lt hinj hri hrn hne hsort fuel y
      show rank (emb x) + (tailCount H fuel pairs y + 1) < n
      omega

/-- **An embedding whose classes are in order really does satisfy the search's `goalAsg`.** -/
theorem goalAsg_of_emb (ind : Bool) (rank : G.V → ℕ) (n : ℕ) (pairs : List (H.V × H.V))
    {emb : H.V → G.V} (hinj : Function.Injective emb)
    (hok : ∀ x y : H.V, x ≠ y → edgeOk ind (H.Adj x y) (G.Adj (emb x) (emb y)) = true)
    (hs : List H.V) (hnd : hs.Nodup) (hri : Function.Injective rank) (hrn : ∀ v, rank v < n)
    (hne : ∀ p ∈ pairs, p.1 ≠ p.2) (hsort : ∀ p ∈ pairs, rank (emb p.1) ≤ rank (emb p.2)) :
    goalAsg H G ind rank n pairs ((hs.map fun x ↦ (x, emb x)).reverse) = true := by
  simp only [goalAsg, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [validAsg_iff, List.pairwise_reverse, List.pairwise_map]
    refine hnd.imp ?_
    intro x y hxy
    rw [compat, Bool.and_eq_true]
    exact ⟨by simpa using fun h ↦ hxy (hinj h).symm, hok y x hxy.symm⟩
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
  · rw [List.all_eq_true]
    intro p hp
    simp only [List.mem_reverse, List.mem_map] at hp
    obtain ⟨x, -, rfl⟩ := hp
    simpa using rank_add_tailCount_lt hinj hri hrn hne hsort pairs.length x

end CGraph
