import IsoGraph.Containment.Algorithms.Embedding
import IsoGraph.Containment.Algorithms.Minor

/-!
# Deciding the contraction relation

`CGraph.findContraction` looks for a partition of `G` into connected blocks whose quotient is `H`,
and returns it if there is one; `CGraph.isEmpty_contractionOf_of_eq_none` is the other half of the
answer, that coming back empty means there is no such partition at all.

A contraction may delete nothing, so — unlike the minor search of `Algorithms/Minor.lean` — this
one cannot peel the host down and cannot build the blocks one at a time and stop when `H` is used
up: *every* vertex of `G` has to end up in a block.  So the search runs the other way round.  It
walks the vertices of `G` in `searchOrder`, which puts each one next to an earlier one whenever
the host is connected, and gives each a vertex of `H` as its label; the blocks are the fibres of
that labelling.  The state is therefore just the list of labels given so far, and the whole search
is `Backtrack.dfs` over it.

`ContractionSearch.finalOk` is the test on a finished labelling, and it is the only thing the
search is allowed to justify a prune by — `Backtrack.dfs_eq_none` takes exactly one implication,
`ContractionSearch.mem_candLab`, and everything below is a clause of it.  `labSource` restricts
the labels tried for `v` to the closed neighbourhood in `H` of an already-labelled neighbour's
label, which is what stops the search wandering, and puts the labels of the blocks `v` touches
first, which is what makes it find a solution early when there is one; `candKeep` then applies
five tests.

* The induced condition, one pair at a time: a labelled neighbour of `v` is in `v`'s block or in
  one adjacent to it in `H`.
* Counting: the labels not yet used need a vertex each, and there are only so many left.
* Connectivity: what is already in a block has to be reachable inside that block together with the
  vertices still unlabelled — a block that has been cut in two can never be repaired.  All of the
  blocks are checked and not just `v`'s, since labelling `v` takes a stepping stone away from every
  one of them.
* Closed blocks: if no unlabelled vertex touches a block, that block is finished, so every edge of
  `H` at its label must already run to another block.  This is what turns the edge condition from
  something only the last vertex can check into something checked all the way down.
* Symmetry: interchangeable vertices of `H` — the twin classes of `Algorithms/Twins.lean` — start
  their blocks in the order of the host, so a labelling and its relabellings are not all tried.
  `CGraph.exists_sorted_model_pairs` is what says that costs no solutions, shared with the minor
  search.

Deciding this relation is NP-hard, and the search space is `|V(H)|^|V(G)|` before pruning, which
is worse in the host than the minor search is.  The prunes are what make it usable: the closed
block test in particular kills a partial labelling as soon as a block is sealed off with an edge
of `H` still unrealised.

## What it costs

Unlike the minor search this one cannot stop early — every vertex of the host has to be labelled —
so the cost follows the size of the *host* much more closely.  Finding a contraction is quick when
the blocks fall out easily: the 4×4 grid gives up a `C4` in 9 ms, a `K4` in 87 ms and a `P4` in
120 ms, the 4-cube a `K4` in 136 ms, and the 24-vertex McGee graph a `K5` in 1.8 s.  A graph is its
own contraction with nothing to search for, so `mcgee ⋏ mcgee` takes no measurable time.

Ruling one out is the expensive direction, as always: `C6` is not a contraction of the 14-vertex
Heawood graph, and saying so takes 2.0 s.  Hosts of McGee's size are past the limit for that — `C6`
against McGee had not answered after ten minutes.

Most of what the search costs is spent in the two block tests, so it matters that they run off one
pass over the fibres instead of recomputing a fibre per test and per neighbour, and that `connVia`
calls `reach` once per block rather than once per vertex of it: together those were worth a factor
of about eight on the McGee case and two on the Heawood one.  Forward checking — asking that the
unlabelled neighbours of `v` still have a label available, the closed neighbourhoods in `H` of
their labelled neighbours' labels having something in common — was tried and dropped, since it
made the grid and Heawood cases about 1.4 times slower and McGee a wash: `labSource` has already
ruled out most of what it would catch.  (Numbers from `MinorBench`, best of several runs; the
machine is shared and the same binary has been seen to vary fourfold with load, so treat them as
ratios rather than absolutes.)
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {H G : CGraph}

/-! ## Connectivity of a block -/

/-- Is this list of vertices nonempty and connected?  Everything after the first vertex has to be
reachable from it without leaving the list. -/
def connOk (G : CGraph) : List G.V → Bool
  | [] => false
  | v :: rest => rest.all fun u ↦ (reach G [v] rest).contains u

theorem connectedOn_of_connOk : ∀ {l : List G.V}, connOk G l = true → G.ConnectedOn {u | u ∈ l}
  | [], h => by simp [connOk] at h
  | v :: rest, h => by
    rw [connOk, List.all_eq_true] at h
    have hset : {u : G.V | u ∈ v :: rest} = {u | u ∈ reach G [v] rest} := by
      ext u
      simp only [Set.mem_setOf_eq, List.mem_cons]
      refine ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩
      · rcases hu with rfl | hu
        · exact mem_reach_of_mem (by simp)
        · exact List.contains_iff_mem.mp (h u hu)
      · rcases mem_or_mem_of_mem_reach hu with hu | hu
        · exact Or.inl (List.mem_singleton.mp hu)
        · exact Or.inr hu
    rw [hset]
    refine connectedOn_reach ?_
    have hsing : {u : G.V | u ∈ [v]} = {v} := by ext u; simp
    rw [hsing]
    exact G.connectedOn_singleton v

/-- Can this list of vertices still be joined up, using the vertices in `pool` as stepping stones?
An empty list passes: a block with nothing in it yet is free to go anywhere. -/
def connVia (G : CGraph) (pool : List G.V) : List G.V → Bool
  | [] => true
  | v :: rest =>
    -- the search runs `reach` once and asks about every vertex of the block against it
    let R := reach G [v] (rest ++ pool)
    rest.all fun u ↦ R.contains u

/-- **A block that will be connected passes `connVia` already.**  The block it will grow into is
connected and lies inside what is there now together with the pool, so `subset_reach` puts all of
it in reach of any one of its vertices. -/
theorem connVia_of_connectedOn {pool S B : List G.V} (hB : G.ConnectedOn {u | u ∈ B})
    (hSB : ∀ u ∈ S, u ∈ B) (hBsub : ∀ u ∈ B, u ∈ S ∨ u ∈ pool) : connVia G pool S = true := by
  cases S with
  | nil => rfl
  | cons w rest =>
    refine List.all_eq_true.mpr fun u hu ↦ List.contains_iff_mem.mpr ?_
    refine subset_reach hB (fun z hz ↦ ?_)
      ⟨w, hSB w (by simp), mem_reach_of_mem (by simp)⟩ u (hSB u (List.mem_cons_of_mem _ hu))
    rcases hBsub z hz with hz | hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl (by simp)
      · exact Or.inr (List.mem_append_left _ hz)
    · exact Or.inr (List.mem_append_right _ hz)

theorem connOk_of_connectedOn : ∀ {l : List G.V}, G.ConnectedOn {u | u ∈ l} → connOk G l = true
  | [], h => by
    obtain ⟨u, hu⟩ := h.nonempty
    simp at hu
  | v :: rest, h => by
    rw [connOk, List.all_eq_true]
    intro u hu
    refine List.contains_iff_mem.mpr (subset_reach h (fun w hw ↦ ?_)
      ⟨v, by simp, mem_reach_of_mem (by simp)⟩ u (by simp [hu]))
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl (by simp)
    · exact Or.inr hw

namespace ContractionSearch

/-! ## Reading a contraction off an assignment

The search gives each vertex of `G` a vertex of `H`, as a list of pairs with the most recent first.
`labOf` reads that assignment as the branch map and `fibre` reads it as the blocks. -/

/-- The vertex of `H` an assignment gives to a vertex of `G`. -/
def labOf : List (G.V × H.V) → G.V → Option H.V
  | [], _ => none
  | q :: r, v => if q.1 = v then some q.2 else labOf r v

theorem isSome_labOf : ∀ {r : List (G.V × H.V)} {v : G.V}, v ∈ r.map Prod.fst →
    (labOf r v).isSome
  | [], v, h => by simp at h
  | q :: r, v, h => by
    rw [labOf]
    split
    · rfl
    · rename_i hne
      rw [List.map_cons, List.mem_cons] at h
      exact isSome_labOf (h.resolve_left fun hq ↦ hne hq.symm)

theorem labOf_eq_some_iff : ∀ {r : List (G.V × H.V)}, (r.map Prod.fst).Nodup →
    ∀ {v : G.V} {x : H.V}, labOf r v = some x ↔ (v, x) ∈ r
  | [], _, v, x => by simp [labOf]
  | (u, y) :: r, hnd, v, x => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [labOf, List.mem_cons, Prod.mk.injEq]
    split
    · rename_i huv
      subst huv
      refine ⟨fun h ↦ Or.inl ⟨rfl, (Option.some_inj.mp h).symm⟩, fun h ↦ ?_⟩
      rcases h with ⟨-, rfl⟩ | h
      · rfl
      · exact absurd (List.mem_map_of_mem (f := Prod.fst) h) hnd.1
    · rename_i huv
      rw [labOf_eq_some_iff hnd.2]
      exact ⟨Or.inr, fun h ↦ h.resolve_left fun h' ↦ huv h'.1.symm⟩

/-- An assignment that lists a vertex of `G` once gives it one label. -/
theorem snd_eq_of_nodup {r : List (G.V × H.V)} (hnd : (r.map Prod.fst).Nodup) {v : G.V}
    {x y : H.V} (hx : (v, x) ∈ r) (hy : (v, y) ∈ r) : x = y :=
  Option.some_inj.mp
    (((labOf_eq_some_iff hnd).mpr hx).symm.trans ((labOf_eq_some_iff hnd).mpr hy))

/-- The block an assignment gives to a vertex of `H`. -/
def fibre (r : List (G.V × H.V)) (x : H.V) : List G.V :=
  (r.filter fun q ↦ decide (q.2 = x)).map Prod.fst

theorem mem_fibre {r : List (G.V × H.V)} {v : G.V} {x : H.V} :
    v ∈ fibre r x ↔ (v, x) ∈ r := by
  simp only [fibre, List.mem_map, List.mem_filter, decide_eq_true_eq]
  refine ⟨fun ⟨q, ⟨hq, hq2⟩, hq1⟩ ↦ ?_, fun h ↦ ⟨(v, x), ⟨h, rfl⟩, rfl⟩⟩
  rw [← hq1, ← hq2]
  exact hq

theorem mem_fibre_of_mem {r r' : List (G.V × H.V)} {v : G.V} {x : H.V} (hr : ∀ q ∈ r, q ∈ r')
    (h : v ∈ fibre r x) : v ∈ fibre r' x :=
  mem_fibre.mpr (hr _ (mem_fibre.mp h))

theorem mem_of_mem_fibre {r : List (G.V × H.V)} {v : G.V} {x : H.V} (h : v ∈ fibre r x) :
    v ∈ r.map Prod.fst :=
  List.mem_map_of_mem (mem_fibre.mp h)

/-! ## The test on a complete assignment

Everything the search prunes with has to follow from this one test, so everything a contraction has
to satisfy is checked here: the assignment labels each vertex of `G` exactly once, every block is
connected — which makes it nonempty, so every vertex of `H` is used — two blocks are joined in `H`
exactly when an edge of `G` runs between them, and interchangeable vertices of `H` take their
blocks in order. -/

/-- Does a complete assignment describe a contraction? -/
def finalOk (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (r : List (G.V × H.V)) : Bool :=
  decide (r.map Prod.fst = gs.reverse) &&
    hs.all (fun x ↦ connOk G (fibre r x)) &&
    (hs.all fun x ↦ hs.all fun y ↦ decide (x = y) ||
      (H.Adj x y == linked G (fibre r x) (fibre r y))) &&
    pairs.all fun p ↦
      decide (minRank gs.idxOf (fibre r p.1) ≤ minRank gs.idxOf (fibre r p.2))

variable {hs : List H.V} {gs : List G.V} {pairs : List (H.V × H.V)} {r : List (G.V × H.V)}

theorem finalOk_keys (h : finalOk H G hs gs pairs r = true) : r.map Prod.fst = gs.reverse := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1

theorem finalOk_conn (h : finalOk H G hs gs pairs r = true) {x : H.V} (hx : x ∈ hs) :
    connOk G (fibre r x) = true := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.2 x hx

theorem finalOk_adj (h : finalOk H G hs gs pairs r = true) {x y : H.V} (hx : x ∈ hs) (hy : y ∈ hs)
    (hxy : x ≠ y) : H.Adj x y = linked G (fibre r x) (fibre r y) := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have hxy' := List.all_eq_true.mp (List.all_eq_true.mp h.1.2 x hx) y hy
  rw [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hxy'
  exact hxy'.resolve_left hxy

theorem finalOk_sym (h : finalOk H G hs gs pairs r = true) {p : H.V × H.V} (hp : p ∈ pairs) :
    minRank gs.idxOf (fibre r p.1) ≤ minRank gs.idxOf (fibre r p.2) := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp h.2 p hp)

/-- A connected block is a nonempty one, so an accepted assignment uses every vertex of `H`. -/
theorem fibre_ne_nil (h : finalOk H G hs gs pairs r = true) {x : H.V} (hx : x ∈ hs) :
    fibre r x ≠ [] := by
  intro hnil
  have hc := finalOk_conn h hx
  rw [hnil] at hc
  exact absurd hc (by simp [connOk])

/-! ## Soundness -/

/-- The contraction a complete, accepted assignment describes. -/
def ofFinal (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (r : List (G.V × H.V)) (hcov : ∀ x : H.V, x ∈ hs) (hgs : ∀ v : G.V, v ∈ gs)
    (hgnd : gs.Nodup) (h : finalOk H G hs gs pairs r = true) : H.ContractionOf G := by
  have hknd : (r.map Prod.fst).Nodup := by rw [finalOk_keys h]; exact List.nodup_reverse.mpr hgnd
  have hbr : ∀ (v : G.V) (x : H.V), labOf r v = some x ↔ v ∈ fibre r x := fun v x ↦
    (labOf_eq_some_iff hknd).trans mem_fibre.symm
  refine
    { branch := labOf r
      connectedOn' := fun x ↦ ?_
      map_adj' := fun x y hxy ↦ ?_
      adj_map' := fun x y hxy hex ↦ ?_
      total' := fun u ↦ ?_ }
  · rw [show {v : G.V | labOf r v = some x} = {v | v ∈ fibre r x} from Set.ext fun v ↦ hbr v x]
    exact connectedOn_of_connOk (finalOk_conn h (hcov x))
  · rw [finalOk_adj h (hcov x) (hcov y) (fun hc ↦ H.loopless x (hc ▸ hxy)), linked_iff] at hxy
    obtain ⟨u, hu, w, hw, huw⟩ := hxy
    exact ⟨u, w, (hbr u x).mpr hu, (hbr w y).mpr hw, huw⟩
  · obtain ⟨u, w, hu, hw, huw⟩ := hex
    rw [finalOk_adj h (hcov x) (hcov y) hxy, linked_iff]
    exact ⟨u, (hbr u x).mp hu, w, (hbr w y).mp hw, huw⟩
  · exact isSome_labOf (by rw [finalOk_keys h]; simpa using hgs u)

/-! ## Where the assignment sits in the host order

The search hands the labels out in the order of `gs`, so an assignment `l ++ (v, x) :: pre` splits
`gs` into the vertices already done, `v` itself, and the vertices still to come.  That is what lets
a candidate test speak about the pool of unassigned vertices, and about the rank of `v` — and all
of it is read off the one check `finalOk` makes on the keys. -/

section Split

variable {l pre : List (G.V × H.V)} {v : G.V} {x : H.V}
  (hgnd : gs.Nodup) (hk : (l ++ (v, x) :: pre).map Prod.fst = gs.reverse)

include hk in
theorem gs_split : gs = (pre.map Prod.fst).reverse ++ v :: (l.map Prod.fst).reverse := by
  have hrev := congrArg List.reverse hk
  rw [List.reverse_reverse] at hrev
  rw [← hrev]
  simp

include hk in
theorem rank_lt_of_mem_pre {u : G.V} (hu : u ∈ pre.map Prod.fst) : gs.idxOf u < pre.length := by
  have hmem : u ∈ (pre.map Prod.fst).reverse := List.mem_reverse.mpr hu
  rw [gs_split hk, List.idxOf_append_of_mem hmem]
  have hlt := List.idxOf_lt_length_iff.mpr hmem
  simpa using hlt

include hgnd hk in
theorem rank_eq_of_key : gs.idxOf v = pre.length := by
  have hnd : ((pre.map Prod.fst).reverse ++ v :: (l.map Prod.fst).reverse).Nodup := by
    rw [← gs_split hk]; exact hgnd
  have hv : v ∉ (pre.map Prod.fst).reverse := fun hv ↦
    (List.disjoint_of_nodup_append hnd) hv (List.mem_cons_self ..)
  rw [gs_split hk, List.idxOf_append_of_notMem hv]
  simp

include hgnd hk in
theorem rank_gt_of_mem_l {u : G.V} (hu : u ∈ l.map Prod.fst) : pre.length < gs.idxOf u := by
  have hnd : ((pre.map Prod.fst).reverse ++ v :: (l.map Prod.fst).reverse).Nodup := by
    rw [← gs_split hk]; exact hgnd
  have hu' : u ∈ (l.map Prod.fst).reverse := List.mem_reverse.mpr hu
  have hnotpre : u ∉ (pre.map Prod.fst).reverse := fun hup ↦
    (List.disjoint_of_nodup_append hnd) hup (List.mem_cons_of_mem _ hu')
  have hne : v ≠ u := by
    intro hvu
    rw [List.nodup_append] at hnd
    exact absurd hu' (hvu ▸ (List.nodup_cons.mp hnd.2.1).1)
  rw [gs_split hk, List.idxOf_append_of_notMem hnotpre, List.idxOf_cons_ne _ hne]
  simp

include hk in
/-- The pool a candidate test uses is exactly the part of the assignment still to come. -/
theorem gs_drop : gs.drop (pre.length + 1) = (l.map Prod.fst).reverse := by
  have hgs : gs = ((pre.map Prod.fst).reverse ++ [v]) ++ (l.map Prod.fst).reverse := by
    rw [gs_split hk]; simp
  rw [hgs]
  exact List.drop_left' (by simp)

include hk in
theorem mem_pool_iff {u : G.V} : u ∈ gs.drop (pre.length + 1) ↔ u ∈ l.map Prod.fst := by
  rw [gs_drop hk, List.mem_reverse]

end Split

/-! ## The candidates

`labSource` narrows the labels worth trying to the closed neighbourhood in `H` of the label of an
already-done neighbour of `v`, and `candKeep` applies the tests a label has to survive.  Each of
them is a necessary condition on a solution, which is what `mem_candLab` proves. -/

/-- Put the labels of the blocks `v` already touches first.  This changes nothing about which
labels are tried, only the order, but a block of a contraction is connected, so a label next to `v`
is much likelier to work out and a solution turns up far sooner when there is one. -/
def labNear (H G : CGraph) (v : G.V) (pre : List (G.V × H.V)) (src : List H.V) : List H.V :=
  let near := (pre.filter fun q ↦ G.Adj v q.1).map Prod.snd
  src.filter (fun x ↦ near.contains x) ++ src.filter (fun x ↦ !near.contains x)

theorem mem_labNear {v : G.V} {pre : List (G.V × H.V)} {src : List H.V} {x : H.V} :
    x ∈ labNear H G v pre src ↔ x ∈ src := (List.filter_append_perm _ _).mem_iff

/-- The labels `v` could take: if a neighbour of `v` is done already, the label of `v` is that
neighbour's label or a neighbour of it in `H`. -/
def labSource (H G : CGraph) (hs : List H.V) (v : G.V) (pre : List (G.V × H.V)) : List H.V :=
  labNear H G v pre <|
    match pre.find? fun q ↦ G.Adj v q.1 with
    | none => hs
    | some q => hs.filter fun x ↦ decide (x = q.2) || H.Adj x q.2

/-- The two tests that look at the blocks, run off one pass that pairs every vertex of `H` with its
block, so that the fibres are computed once and not once per test and per neighbour.

* Every block can still be joined up: what is in it already has to be reachable within that block
  and the unassigned vertices.  This is checked for all of the blocks and not just for the one that
  just grew, because labelling a vertex shrinks the pool, and a block two of whose pieces were
  joined only through that vertex is broken by it even though nothing was added to it.
* A block that no unassigned vertex touches can never grow again, so every edge of `H` at its label
  has to be there already, between it and another block. -/
def blocksOk (H G : CGraph) (pool : List G.V) (fs : List (H.V × List G.V)) : Bool :=
  fs.all fun p ↦
    connVia G pool p.2 &&
      (p.2.isEmpty || pool.any (fun u ↦ p.2.any (G.Adj u)) ||
        fs.all fun q ↦ !H.Adj p.1 q.1 || linked G p.2 q.2)

/-- The tests a label has to pass.

* Every done neighbour of `v` is in the same block or in an adjacent one — the induced condition,
  one pair at a time.
* The vertices of `H` still unused fit into the vertices of `G` still unassigned.
* Interchangeable vertices of `H` start their blocks in order.
* The blocks pass `blocksOk`, which is the dearest of the tests and so is left for last. -/
def candKeep (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (v : G.V) (pre : List (G.V × H.V)) (x : H.V) : Bool :=
  let asg := (v, x) :: pre
  let pool := gs.drop (pre.length + 1)
  pre.all (fun q ↦ !G.Adj v q.1 || decide (q.2 = x) || H.Adj x q.2) &&
    decide (hs.countP (fun y ↦ !(asg.map Prod.snd).contains y) + asg.length ≤ gs.length) &&
    pairs.all (fun p ↦ (fibre asg p.2).isEmpty || (!(fibre asg p.1).isEmpty &&
      decide (minRank gs.idxOf (fibre asg p.1) ≤ minRank gs.idxOf (fibre asg p.2)))) &&
    blocksOk H G pool (hs.map fun y ↦ (y, fibre asg y))

/-- The labels the search tries for `v`. -/
def candLab (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (v : G.V) (pre : List (G.V × H.V)) : List H.V :=
  (labSource H G hs v pre).filter (candKeep H G hs gs pairs v pre)

/-! ## Soundness of the pruning -/

section Cand

variable {l pre : List (G.V × H.V)} {v : G.V} {x : H.V}

/-- The induced condition as the candidate tests see it: adjacent vertices of `G` are in the same
block or in adjacent ones. -/
theorem adj_of_finalOk (hcov : ∀ y : H.V, y ∈ hs) {r : List (G.V × H.V)}
    (h : finalOk H G hs gs pairs r = true) {q q' : G.V × H.V} (hq : q ∈ r) (hq' : q' ∈ r)
    (hadj : G.Adj q.1 q'.1 = true) : q.2 = q'.2 ∨ H.Adj q.2 q'.2 = true := by
  by_cases hqx : q.2 = q'.2
  · exact Or.inl hqx
  refine Or.inr ?_
  rw [finalOk_adj h (hcov q.2) (hcov q'.2) hqx, linked_iff]
  exact ⟨q.1, mem_fibre.mpr hq, q'.1, mem_fibre.mpr hq', hadj⟩

/-- The same for a neighbour of `v` that is done already: it is in `x`'s block or in one next to
it. -/
theorem adj_pre_of_finalOk (hcov : ∀ y : H.V, y ∈ hs)
    (h : finalOk H G hs gs pairs (l ++ (v, x) :: pre) = true) {q : G.V × H.V} (hq : q ∈ pre)
    (hadj : G.Adj v q.1 = true) : q.2 = x ∨ H.Adj x q.2 = true :=
  (adj_of_finalOk hcov h (q := (v, x)) (by simp) (by simp [hq]) hadj).imp Eq.symm id

theorem mem_labSource (hcov : ∀ y : H.V, y ∈ hs)
    (h : finalOk H G hs gs pairs (l ++ (v, x) :: pre) = true) : x ∈ labSource H G hs v pre := by
  rw [labSource, mem_labNear]
  split
  · exact hcov x
  · rename_i q hq
    refine List.mem_filter.mpr ⟨hcov x, ?_⟩
    rcases adj_pre_of_finalOk hcov h (List.mem_of_find?_eq_some hq)
      (List.find?_eq_some_iff_getElem.mp hq).1 with hx | hx
    · simp [hx]
    · simp [hx]

/-- **The pruning throws nothing away.**  This is the one thing `Backtrack.dfs_eq_none` asks of a
search, and every test in `candKeep` is discharged here against `finalOk`. -/
theorem mem_candLab (hcov : ∀ y : H.V, y ∈ hs) (hhnd : hs.Nodup) (hgnd : gs.Nodup)
    (h : finalOk H G hs gs pairs (l ++ (v, x) :: pre) = true) :
    x ∈ candLab H G hs gs pairs v pre := by
  have hk := finalOk_keys h
  have hknd : ((l ++ (v, x) :: pre).map Prod.fst).Nodup := by
    rw [hk]; exact List.nodup_reverse.mpr hgnd
  set r := l ++ (v, x) :: pre with hr
  set asg := (v, x) :: pre with hasg
  set pool := gs.drop (pre.length + 1) with hpool
  have hvx : (v, x) ∈ asg := by rw [hasg]; exact List.mem_cons_self ..
  have hasg_sub : ∀ q ∈ asg, q ∈ r := fun q hq ↦ List.mem_append_right _ hq
  have hpre_sub : ∀ q ∈ pre, q ∈ r := fun q hq ↦
    hasg_sub q (by rw [hasg]; exact List.mem_cons_of_mem _ hq)
  have hmempool : ∀ u : G.V, u ∈ pool ↔ u ∈ l.map Prod.fst := fun u ↦ mem_pool_iff hk
  -- a vertex the assignment mentions is either done or still in the pool
  have hsplit_mem : ∀ u : G.V, u ∈ r.map Prod.fst → u ∈ asg.map Prod.fst ∨ u ∈ pool := by
    intro u hu
    rw [hr, List.map_append, List.mem_append] at hu
    exact hu.symm.imp id fun hh ↦ (hmempool u).mpr hh
  have hkndsplit : (l.map Prod.fst ++ asg.map Prod.fst).Nodup := by
    rw [← List.map_append, ← hr]; exact hknd
  -- and if it is done, its block is already the one it will end in
  have hmemasg : ∀ (w : G.V) (y : H.V), (w, y) ∈ r → w ∈ asg.map Prod.fst → w ∈ fibre asg y := by
    intro w y hwr hwa
    obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hwa
    have hq2 : q.2 = y := snd_eq_of_nodup hknd (hq1 ▸ hasg_sub q hq) hwr
    have hqe : q = (w, y) := Prod.ext hq1 hq2
    exact mem_fibre.mpr (hqe ▸ hq)
  -- the ranks of the vertices already done, and of the ones still to come
  have hrank_le : ∀ u : G.V, u ∈ asg.map Prod.fst → gs.idxOf u ≤ pre.length := by
    intro u hu
    rw [hasg, List.map_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact le_of_eq (rank_eq_of_key hgnd hk)
    · exact le_of_lt (rank_lt_of_mem_pre hk hu)
  have hrank_gt : ∀ u : G.V, u ∈ pool → pre.length < gs.idxOf u := fun u hu ↦
    rank_gt_of_mem_l hgnd hk ((hmempool u).mp hu)
  refine List.mem_filter.mpr ⟨mem_labSource hcov h, ?_⟩
  rw [candKeep, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the induced condition
    rw [List.all_eq_true]
    intro q hq
    cases hadj : G.Adj v q.1
    · simp
    · rcases adj_pre_of_finalOk hcov h hq hadj with hx | hx <;> simp [hx]
  · -- the labels still unused fit in the vertices still unassigned
    rw [decide_eq_true_eq, List.countP_eq_length_filter, ← hasg]
    have hsub : hs.filter (fun y ↦ !(asg.map Prod.snd).contains y) ⊆ l.map Prod.snd := by
      intro y hy
      obtain ⟨hyhs, hynot⟩ := List.mem_filter.mp hy
      rw [Bool.not_eq_eq_eq_not, Bool.not_true, ← Bool.not_eq_true,
        List.contains_iff_mem] at hynot
      obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (fibre_ne_nil h hyhs)
      have hur : (u, y) ∈ r := mem_fibre.mp hu
      rw [hr, List.mem_append] at hur
      rcases hur with hur | hur
      · exact List.mem_map_of_mem hur
      · exact absurd (List.mem_map_of_mem (f := Prod.snd) hur) hynot
    have hlen := ((hhnd.filter _).subperm hsub).length_le
    rw [List.length_map] at hlen
    have hgl : r.length = gs.length := by simpa using congrArg List.length hk
    have hrl : r.length = l.length + asg.length := by rw [hr, List.length_append]
    omega
  · -- interchangeable vertices of `H` start their blocks in order
    rw [List.all_eq_true]
    intro p hp
    rw [Bool.or_eq_true]
    by_cases h2 : (fibre asg p.2).isEmpty = true
    · exact Or.inl h2
    rw [Bool.not_eq_true, List.isEmpty_eq_false_iff] at h2
    obtain ⟨ub, hub, hmb⟩ := exists_minRank_eq (rank := gs.idxOf) h2
    have hubr : ub ∈ fibre r p.2 := mem_fibre_of_mem hasg_sub hub
    have hble : gs.idxOf ub ≤ pre.length := hrank_le ub (mem_of_mem_fibre hub)
    have hchain : minRank gs.idxOf (fibre r p.1) ≤ gs.idxOf ub :=
      le_trans (finalOk_sym h hp) (minRank_le hubr)
    obtain ⟨ua, hua, hma⟩ := exists_minRank_eq (rank := gs.idxOf) (fibre_ne_nil h (hcov p.1))
    have hale : gs.idxOf ua ≤ gs.idxOf ub := by rw [← hma]; exact hchain
    have hua' : ua ∈ fibre asg p.1 := by
      rcases hsplit_mem ua (mem_of_mem_fibre hua) with hwa | hwp
      · exact hmemasg ua p.1 (mem_fibre.mp hua) hwa
      · exact absurd (hrank_gt ua hwp) (by omega)
    refine Or.inr ((Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩)
    · simpa using fun hc ↦ absurd (hc ▸ hua') (by simp)
    · rw [decide_eq_true_eq, hmb]
      exact le_trans (minRank_le hua') hale
  · -- the two tests on the blocks
    refine List.all_eq_true.mpr fun p hp ↦ ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    -- every block can still be joined up
    · exact connVia_of_connectedOn (connectedOn_of_connOk (finalOk_conn h hy))
        (fun u hu ↦ mem_fibre_of_mem hasg_sub hu) fun u hu ↦ by
          rcases hsplit_mem u (mem_of_mem_fibre hu) with hua | hup
          · exact Or.inl (hmemasg u y (mem_fibre.mp hu) hua)
          · exact Or.inr hup
    -- a block nothing can be added to has all its edges already
    show ((fibre asg y).isEmpty || pool.any (fun u ↦ (fibre asg y).any (G.Adj u)) ||
      (hs.map fun z ↦ (z, fibre asg z)).all
        fun q ↦ !H.Adj y q.1 || linked G (fibre asg y) q.2) = true
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hcl : (fibre asg y).isEmpty = true ∨
      (pool.any fun u ↦ (fibre asg y).any (G.Adj u)) = true
    · exact Or.inl hcl
    obtain ⟨hne, hclosed⟩ := not_or.mp hcl
    rw [Bool.not_eq_true, List.isEmpty_eq_false_iff] at hne
    have hclosed' : ∀ u ∈ pool, ∀ w ∈ fibre asg y, G.Adj u w = false := by
      intro u hu w hw
      by_contra hadj
      rw [Bool.not_eq_false] at hadj
      exact hclosed (List.any_eq_true.mpr ⟨u, hu, List.any_eq_true.mpr ⟨w, hw, hadj⟩⟩)
    -- nothing outside the block is next to it, so the block is finished
    have hfin : ∀ w : G.V, (w, y) ∈ r → w ∈ fibre asg y := by
      intro w hwr
      rcases hsplit_mem w (List.mem_map_of_mem hwr) with hwa | hwp
      · exact hmemasg w y hwr hwa
      refine absurd ?_ (fun hh : False ↦ hh)
      obtain ⟨u0, hu0⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨a, ha, b, hb, hbt, hab⟩ :=
        (connectedOn_of_connOk (finalOk_conn h hy)).exists_adj_of_ssubset
          (t := {u : G.V | u ∈ fibre asg y}) (fun u hu ↦ mem_fibre_of_mem hasg_sub hu)
          (show u0 ∈ {u : G.V | u ∈ fibre asg y} from hu0)
          (show w ∈ {u : G.V | u ∈ fibre r y} from mem_fibre.mpr hwr)
          (fun hwt ↦ List.disjoint_of_nodup_append hkndsplit
            ((hmempool w).mp hwp) (mem_of_mem_fibre hwt))
      have hbp : b ∈ pool := by
        rcases hsplit_mem b (mem_of_mem_fibre hb) with hba | hbp
        · exact absurd (hmemasg b y (mem_fibre.mp hb) hba) hbt
        · exact hbp
      exact absurd (hclosed' b hbp a ha) (by rw [G.symm b a, hab]; simp)
    refine Or.inr (List.all_eq_true.mpr fun q hq ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    cases hyz : H.Adj y z
    · simp
    refine (Bool.or_eq_true _ _).mpr (Or.inr ?_)
    have hl : linked G (fibre r y) (fibre r z) = true := by
      rw [← finalOk_adj h hy hz (fun hc ↦ H.loopless y (hc ▸ hyz))]
      exact hyz
    obtain ⟨u, hu, w, hw, huw⟩ := linked_iff.mp hl
    have hu' : u ∈ fibre asg y := hfin u (mem_fibre.mp hu)
    have hw' : w ∈ fibre asg z := by
      rcases hsplit_mem w (mem_of_mem_fibre hw) with hwa | hwp
      · exact hmemasg w z (mem_fibre.mp hw) hwa
      · exact absurd (hclosed' w hwp u hu') (by rw [G.symm w u, huw]; simp)
    exact linked_iff.mpr ⟨u, hu', w, hw', huw⟩
end Cand

/-! ## What a genuine contraction looks like to the search -/

/-- The assignment a contraction gives, in the order the search hands the labels out. -/
def asgOf (f : H.ContractionOf G) (gs : List G.V) : List (G.V × H.V) := gs.map fun v ↦ (v, f v)

theorem keys_asgOf (f : H.ContractionOf G) (gs : List G.V) :
    (asgOf f gs).map Prod.fst = gs := by simp [asgOf, Function.comp_def]

theorem mem_fibre_asgOf {f : H.ContractionOf G} {gs : List G.V} {v : G.V} {x : H.V} :
    v ∈ fibre (asgOf f gs).reverse x ↔ v ∈ gs ∧ f v = x := by
  rw [mem_fibre]
  simp only [asgOf, List.mem_reverse, List.mem_map, Prod.mk.injEq]
  exact ⟨fun ⟨w, hw, hwv, hwx⟩ ↦ ⟨hwv ▸ hw, hwv ▸ hwx⟩, fun ⟨hv, hx⟩ ↦ ⟨v, hv, rfl, hx⟩⟩

/-- **Completeness of the test**: the assignment a contraction gives passes `finalOk`, as long as
it has already been relabelled so that interchangeable vertices of `H` take their blocks in
order. -/
theorem finalOk_asgOf (f : H.ContractionOf G) (hgs : ∀ v : G.V, v ∈ gs)
    (hsym : ∀ p ∈ pairs, modelMin f.branch gs.idxOf gs p.1 ≤ modelMin f.branch gs.idxOf gs p.2) :
    finalOk H G hs gs pairs (asgOf f gs).reverse = true := by
  have hmem : ∀ (v : G.V) (x : H.V), v ∈ fibre (asgOf f gs).reverse x ↔ f v = x := fun v x ↦
    mem_fibre_asgOf.trans (and_iff_right (hgs v))
  have hmin : ∀ x : H.V,
      minRank gs.idxOf (fibre (asgOf f gs).reverse x) = modelMin f.branch gs.idxOf gs x := by
    intro x
    refine minRank_congr fun v ↦ ?_
    rw [hmem, List.mem_filter, decide_eq_true_eq, f.branch_eq_some_iff]
    exact (and_iff_right (hgs v)).symm
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [List.map_reverse, keys_asgOf]
  · refine List.all_eq_true.mpr fun x _ ↦ connOk_of_connectedOn ?_
    rw [show {u : G.V | u ∈ fibre (asgOf f gs).reverse x} = {v | f v = x} from
      Set.ext fun v ↦ hmem v x]
    exact f.connectedOn x
  · refine List.all_eq_true.mpr fun x _ ↦ List.all_eq_true.mpr fun y _ ↦ ?_
    rw [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    by_cases hxy : x = y
    · exact Or.inl hxy
    refine Or.inr (Bool.eq_iff_iff.mpr ⟨fun hadj ↦ ?_, fun hlk ↦ ?_⟩)
    · obtain ⟨u, w, hu, hw, huw⟩ := f.map_adj hadj
      exact linked_iff.mpr ⟨u, (hmem u x).mpr hu, w, (hmem w y).mpr hw, huw⟩
    · obtain ⟨u, hu, w, hw, huw⟩ := linked_iff.mp hlk
      have hux := (hmem u x).mp hu
      have hwy := (hmem w y).mp hw
      have hadj := f.adj_map huw (by rw [hux, hwy]; exact hxy)
      rwa [hux, hwy] at hadj
  · exact List.all_eq_true.mpr fun p hp ↦ decide_eq_true (by rw [hmin, hmin]; exact hsym p hp)

end ContractionSearch

/-- **Relabelling a contraction along an automorphism of the pattern.**  This is what the
symmetry breaking of `exists_sorted_model_pairs` needs of the relation; an automorphism is an
isomorphism, so composing with `ContractionOf.ofIso` is all there is to it. -/
theorem ContractionOf.exists_reindex (f : H.ContractionOf G) {σ : H.V → H.V}
    (hinj : Function.Injective σ) (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    ∃ g : H.ContractionOf G, ∀ (v : G.V) (x : H.V),
      g.branch v = some x ↔ f.branch v = some (σ x) := by
  classical
  let e : H.V ≃ H.V := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  let i : H ≃cg H := ⟨e, fun {a b} ↦ by
    show (H.Adj (σ a) (σ b) = true) ↔ (H.Adj a b = true)
    rw [hadj]⟩
  refine ⟨(ContractionOf.ofIso i).trans f, fun v x ↦ ?_⟩
  rw [ContractionOf.branch_eq_some_iff, ContractionOf.branch_eq_some_iff,
    ContractionOf.trans_apply, ContractionOf.ofIso_apply]
  exact Equiv.symm_apply_eq e

/-! ## The search -/

section Search

open ContractionSearch

variable (H G)

/-- The assignment the search finds, if there is one. -/
def searchLab (rH : Roster H.V) (rG : Roster G.V) : Option (List (G.V × H.V)) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    Backtrack.dfs
      (candLab H G (searchOrder H rH.toList) (searchOrder G rG.toList)
        (symPairs H (searchOrder H rH.toList)))
      (finalOk H G (searchOrder H rH.toList) (searchOrder G rG.toList)
        (symPairs H (searchOrder H rH.toList)))
      (searchOrder G rG.toList) []
  else none

variable {H G}

theorem searchLab_goal {rH : Roster H.V} {rG : Roster G.V} {r : List (G.V × H.V)}
    (h : searchLab H G rH rG = some r) :
    finalOk H G (searchOrder H rH.toList) (searchOrder G rG.toList)
      (symPairs H (searchOrder H rH.toList)) r = true := by
  rw [searchLab] at h
  split at h
  · exact Backtrack.goal_of_dfs_eq_some h
  · exact absurd h (by simp)

variable (H G)

/-- **Is `H` a contraction of `G`?**  Returns a witness if so.  See
`isEmpty_contractionOf_of_eq_none` for the other half of the answer. -/
def findContraction (rH : Roster H.V) (rG : Roster G.V) : Option (H.ContractionOf G) :=
  Option.pmap (p := fun r ↦ finalOk H G (searchOrder H rH.toList) (searchOrder G rG.toList)
      (symPairs H (searchOrder H rH.toList)) r = true)
    (fun r hr ↦ ofFinal H G _ _ _ r (mem_searchOrder H rH.mem_toList)
      (mem_searchOrder G rG.mem_toList) (searchOrder_nodup G rG.toList) hr)
    (searchLab H G rH rG) (fun _ hr ↦ searchLab_goal hr)

theorem findContraction_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findContraction H G rH rG = none ↔ searchLab H G rH rG = none :=
  Option.pmap_eq_none_iff

variable {H G}

/-- **Completeness**: when the search comes back empty, `H` is not a contraction of `G`. -/
theorem isEmpty_contractionOf_of_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findContraction H G rH rG = none) : IsEmpty (H.ContractionOf G) := by
  rw [findContraction_eq_none_iff, searchLab] at h
  refine ⟨fun f ↦ ?_⟩
  split at h
  · -- the contraction is first relabelled to one the symmetry test accepts
    obtain ⟨g, -, hgsym⟩ := exists_sorted_model_pairs (fun f : H.ContractionOf G ↦ f.branch)
      (fun f {_σ} hinj hadj ↦ f.exists_reindex hinj hadj)
      (hs := searchOrder H rH.toList) (gs := searchOrder G rG.toList)
      (rank := (searchOrder G rG.toList).idxOf) (mem_searchOrder H rH.mem_toList) f
      (fun v _ _ ↦ mem_searchOrder G rG.mem_toList v)
    have hn := Backtrack.dfs_eq_none
      (fun _ _ _ _ hh ↦ mem_candLab (mem_searchOrder H rH.mem_toList)
        (searchOrder_nodup H rH.toList) (searchOrder_nodup G rG.toList) hh) h
      (keys_asgOf g (searchOrder G rG.toList))
    rw [List.append_nil, finalOk_asgOf g (mem_searchOrder G rG.mem_toList) hgsym] at hn
    exact absurd hn (by simp)
  · exact absurd (show FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E from
      ⟨f.card_le, f.E_le⟩) ‹_›

/-- `H` is a contraction of `G` exactly when the search finds one. -/
theorem isEmpty_contractionOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.ContractionOf G) ↔ findContraction H G rH rG = none := by
  refine ⟨fun h ↦ ?_, isEmpty_contractionOf_of_eq_none⟩
  rcases hm : findContraction H G rH rG with _ | f
  · rfl
  · exact (h.false f).elim

end Search

end CGraph
