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
six tests.

* Automorphisms: no automorphism of `H` fixing the labels given so far sends this one backwards, so
  of all the labellings that differ only by a symmetry of `H` the search looks at just the
  lexicographically least.  This one goes first, being the cheapest.
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
* Twins: interchangeable vertices of `H` — the twin classes of `Algorithms/Twins.lean` — start
  their blocks in the order of the host, so a labelling and its relabellings are not all tried.
  `CGraph.exists_sorted_model_pairs` is what says that costs no solutions, shared with the minor
  search.  This and the automorphism test take turns: the section "Symmetry breaking on the
  automorphisms of the pattern" below says why the two cannot be run together.

Deciding this relation is NP-hard, and the search space is `|V(H)|^|V(G)|` before pruning, which
is worse in the host than the minor search is.  The prunes are what make it usable: the closed
block test in particular kills a partial labelling as soon as a block is sealed off with an edge
of `H` still unrealised.

## What it costs

Unlike the minor search this one cannot stop early — every vertex of the host has to be labelled —
so the cost follows the size of the *host* much more closely.  Finding a contraction is quick when
the blocks fall out easily: the 4×4 grid gives up a `C4` in 1 ms, a `K4` in 14 ms and a `P4` in
17 ms, the 4-cube a `K4` in 12 ms, and the 24-vertex McGee graph a `K5` in 0.16 s.  A graph is its
own contraction and the search walks straight to it, so `mcgee ⋏ mcgee` is 20 ms.

Ruling one out is the expensive direction, as always: `C6` is not a contraction of the 14-vertex
Heawood graph, and saying so takes 22 ms.  Against McGee, ten vertices larger, the same question
takes 87 s, `C7` 170 s and `C8` 29 s: the longer cycle has more labels to try at every vertex but a
tighter partition to fit them into, and past `C7` the second of those wins.

Most of what the search costs is spent in the two block tests, so it matters that they run off one
pass over the fibres instead of recomputing a fibre per test and per neighbour, and that `connVia`
calls `reach` once per block rather than once per vertex of it: together those were worth a factor
of about eight on the McGee case and two on the Heawood one.  Forward checking — asking that the
unlabelled neighbours of `v` still have a label available, the closed neighbourhoods in `H` of
their labelled neighbours' labels having something in common — was tried and dropped, since it
made the grid and Heawood cases about 1.4 times slower and McGee a wash: `labSource` has already
ruled out most of what it would catch.  (Numbers from `testing/MinorBench.lean`, best of several
runs; the machine is shared and the same binary has been seen to vary fourfold with load, so treat
them as ratios rather than absolutes.)

The same idea one level up: everything `candKeep` asks that does not mention the label being tried
is lifted out of the loop over labels and computed once per node.  `candLabWith` is that, and the
section "What the search runs" below is what it takes to make the hoist pay for itself on the nodes
where nothing survives the cheap tests anyway.  Against `candKeep` run as written, the two
alternating in one process: ruling `C6` out of Heawood came down by a quarter, `K4` into McGee by a
fifth, the two grid cases by about an eighth, and `K4` into the 4-cube — which finds an answer
almost at once, so there is nothing to amortise a table over — was a wash.

Keeping the walk off a block with a single vertex in it, which `connVia` written the obvious way
does not do, took another 6% off Heawood and a fifth off `K4` into the grid: at the shallow levels
of the search almost every block that is not empty is a singleton.  Reading the rank off a table
rather than scanning the search order took a fifth off `K4` into the grid and a tenth off `K5` into
McGee, and did nothing at all to Heawood, where `C6` has no interchangeable vertices and so the
test it feeds never runs.  Two things were tried and dropped: testing the block that just grew
before the others, which is not where the failures are and cost 6% on Heawood to look for; and
stopping the walk as soon as the block's other vertices have turned up, which cost a third there,
since a walk that is going to fail has to finish anyway and now carries a filter through every
round.

Finding the automorphisms happens before the search starts, so it has to be cheap in absolute terms
and not merely relative to what it saves.  Asked of `H` directly it is not: the patterns of
`SmallGraphs` are not `cacheFin`'d, so every `Adj` is a scan, and on McGee the setup cost
0.33 s against the 0.02 s of searching it was there to speed up.  Tabulating that adjacency once and
running the whole of it — the generator, the `isAut` filter, the lookups into `hs` — on ranks rather
than vertices brings the setup to 0.01 s.
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
      simp only [Set.mem_ofPred_eq, List.mem_cons]
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

/-! Both of these read best with the walk written where it is used, and both run badly that way.
`connOk` names it inside the `all`, so it walks the graph once per vertex of the block instead of
once; and either of them, given a block with a single vertex in it, walks the graph and then asks
nothing of the answer, which at the shallow levels of the search is almost every nonempty block. -/

/-- What `connOk` runs. -/
def connOkFast (G : CGraph) : List G.V → Bool
  | [] => false
  | [_] => true
  | v :: rest => let R := reach G [v] rest; rest.all fun u ↦ R.contains u

@[csimp] theorem connOk_eq_connOkFast : @connOk = @connOkFast := by
  funext G l
  match l with
  | [] | [_] | _ :: _ :: _ => rfl

/-- What `connVia` runs. -/
def connViaFast (G : CGraph) (pool : List G.V) : List G.V → Bool
  | [] => true
  | [_] => true
  | v :: rest => let R := reach G [v] (rest ++ pool); rest.all fun u ↦ R.contains u

@[csimp] theorem connVia_eq_connViaFast : @connVia = @connViaFast := by
  funext G pool l
  match l with
  | [] | [_] | _ :: _ :: _ => rfl

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

/-- Labelling one more vertex changes one block, and changes it by a cons. -/
theorem fibre_cons (v : G.V) (x y : H.V) (pre : List (G.V × H.V)) :
    fibre ((v, x) :: pre) y = if x = y then v :: fibre pre y else fibre pre y := by
  simp only [fibre, List.filter_cons, decide_eq_true_eq]
  split <;> simp_all

/-! ## Symmetry breaking on the automorphisms of the pattern

`symPairs` breaks the symmetry between two vertices of `H` with the same neighbours, which is a lot
of symmetry when `H` is a complete graph and none at all when `H` is a cycle — a cycle has no two
vertices alike, and yet every rotation and reflection of it relabels one contraction into another.
What that symmetry is, in general, is the automorphism group of `H` acting on the labellings, and
so the test here is the direct one: of all the labellings in an orbit, look only at the one whose
word of labels comes first.

A labelling is a word: the assignment gives the vertices of `G`, in the order `gs` fixes, their
positions in `hs`.  An automorphism `a` of `H` rewrites that word letter by letter, and the
labelling to keep is the one no automorphism makes smaller — lexicographically, since that is the
order a depth-first search discovers the word in and so the one it can test a letter at a time.
The test on the next letter is `autKeep`: an automorphism that already sent an earlier letter
forwards has lost its say, one that sent an earlier letter backwards had its branch cut then, and
so the ones still constraining the next letter are exactly those fixing every letter so far.

The two symmetry breaks are not run together.  A key-minimal labelling need not satisfy the
`symPairs` condition, so `autList` is consulted only when `symPairs` comes out empty — which is
exactly when this is needed, and never when `symPairs` is doing the work.  Cutting the orbit of the
automorphism group costs a factor of `|Aut H|`: against McGee, `C6` goes from twelve million nodes
to one million. -/

section Autos

variable {hs : List H.V}

/-- An automorphism of `H`, given as the image of `hs`: `relab hs img` sends the `i`th entry of
`hs` to the `i`th of `img`, and anything `hs` misses to itself. -/
def relab (hs img : List H.V) (x : H.V) : H.V := img.getD (hs.idxOf x) x

/-- Is `img` the image of `hs` under an automorphism of `H`?  The labels have to come out distinct
and the adjacency has to agree either side of the map.  Where `img` came from does not matter to
anything downstream: this is all the symmetry breaking is entitled to assume about it. -/
def isAut (H : CGraph) (hs img : List H.V) : Bool :=
  let ps := hs.map fun x ↦ (x, relab hs img x)
  decide (ps.map Prod.snd).Nodup &&
    ps.all fun p ↦ ps.all fun q ↦ H.Adj p.2 q.2 == H.Adj p.1 q.1

theorem isAut_injective {hs img : List H.V} (hhs : ∀ x : H.V, x ∈ hs)
    (h : isAut H hs img = true) : Function.Injective (relab hs img) := by
  rw [isAut, Bool.and_eq_true, decide_eq_true_eq, List.map_map] at h
  exact fun x y hxy ↦ List.inj_on_of_nodup_map h.1 (hhs x) (hhs y) hxy

theorem isAut_adj {hs img : List H.V} (hhs : ∀ x : H.V, x ∈ hs) (h : isAut H hs img = true)
    (x y : H.V) : H.Adj (relab hs img x) (relab hs img y) = H.Adj x y := by
  rw [isAut, Bool.and_eq_true] at h
  have hx := List.all_eq_true.mp h.2 _ (List.mem_map_of_mem (f := fun x ↦ (x, relab hs img x))
    (hhs x))
  exact eq_of_beq (List.all_eq_true.mp hx _ (List.mem_map_of_mem
    (f := fun x ↦ (x, relab hs img x)) (hhs y)))

/-- The adjacency of `hs` with itself, by rank: one row of `Bool` per entry.  The generator below
asks for it once per pair it places, and on a graph whose `Adj` is a scan — which is what the
patterns of `SmallGraphs` are before `cacheFin` — that is the whole cost of the search. -/
private def autAdj (H : CGraph) (hs : List H.V) : Array (Array Bool) :=
  (hs.map fun x ↦ (hs.map fun y ↦ H.Adj x y).toArray).toArray

/-- The automorphisms of `H`, found by extending a partial map one vertex at a time and keeping
only what agrees with `H` on the vertices placed so far, all of it on ranks into `hs` and its
adjacency table.  The fuel bounds the whole search rather than its depth: running out returns some
of the automorphisms instead of all of them, which costs pruning but never a solution, since the
test below is sound against any list of automorphisms — as is, for the same reason, reading the
answers back out of `hs` by rank. -/
private def autsAux (adj : Array (Array Bool)) (all : List ℕ) :
    List ℕ → List (ℕ × ℕ) → ℕ × List (List ℕ) → ℕ × List (List ℕ)
  | _, _, (0, acc) => (0, acc)
  | [], done, (n + 1, acc) => (n, done.reverse.map Prod.snd :: acc)
  | i :: rest, done, (n + 1, acc) =>
    all.foldl (init := (n, acc)) fun st j ↦
      if done.all fun q ↦ !(q.2 == j) && ((adj[q.1]!)[i]! == (adj[q.2]!)[j]!) then
        autsAux adj all rest ((i, j) :: done) st
      else st

private theorem getElem!_autAdj (hhs : ∀ x : H.V, x ∈ hs) (u v : H.V) :
    ((autAdj H hs)[hs.idxOf u]!)[hs.idxOf v]! = H.Adj u v := by
  have h : (autAdj H hs)[hs.idxOf u]! = (hs.map fun y ↦ H.Adj u y).toArray := by
    rw [autAdj, Array.getElem!_eq_getD, getD_toArray, List.getElem?_map,
      List.getElem?_idxOf (hhs u)]
    rfl
  rw [h, Array.getElem!_eq_getD, getD_toArray, List.getElem?_map, List.getElem?_idxOf (hhs v)]
  rfl

/-- The adjacency half of `isAut`, on ranks and a table.

Its own definition, and taking the ranked pairs rather than making them, for one reason: written
inline as the second half of an `&&`, the `Nodup` test in front of it is a pure computation the
compiler is free to sink into the loop, and it does — into the innermost of the two `all`s, where
it runs `|hs|²` times instead of once. -/
private def autAdjOk (adj : Array (Array Bool)) (ps : List (ℕ × ℕ)) : Bool :=
  ps.all fun p ↦ ps.all fun q ↦ (adj[p.2]!)[q.2]! == (adj[p.1]!)[q.1]!

/-- `isAut` on tables: the same two tests, with every `Adj` replaced by two array reads and every
`List.idxOf` — which is a scan carrying `H.V`'s equality — by one.  Checking a list of candidates
this way builds both tables once for all of them instead of once each. -/
private def isAutTab (adj : Array (Array Bool)) (hrk : H.V → ℕ) (hs img : List H.V) : Bool :=
  let ps := hs.map fun x ↦ (hrk x, hrk (img.getD (hrk x) x))
  autAdjOk adj ps && decide (ps.map Prod.snd).Nodup

private theorem isAut_of_isAutTab (hhs : ∀ x : H.V, x ∈ hs) {img : List H.V}
    (h : isAutTab (autAdj H hs) (Backtrack.tabAt (Backtrack.rankTable hs)) hs img = true) :
    isAut H hs img = true := by
  rw [isAutTab, autAdjOk, Backtrack.tabAt_rankTable, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [isAut, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · refine List.Nodup.of_map (fun z ↦ hs.idxOf z) ?_
    have h1 := h.2
    simp only [List.map_map, Function.comp_def, relab] at h1 ⊢
    exact h1
  · have h2 := h.1
    simp only [List.all_map, Function.comp_def, relab, getElem!_autAdj hhs] at h2 ⊢
    exact h2

/-- The automorphisms the symmetry test is run against, each one put through `isAut` so that how it
was found is no part of the proof, and at most `cap` of them so that both the generator and that
check stay cheap even for a pattern whose automorphism group is enormous. -/
def autList (H : CGraph) (hs : List H.V) (fuel cap : ℕ) : List (List H.V) :=
  let ranks := List.range hs.length
  let adj := autAdj H hs
  let hrk := Backtrack.tabAt (Backtrack.rankTable hs)
  (((autsAux adj ranks ranks [] (fuel, [])).2.map fun a ↦
    a.filterMap fun i ↦ hs[i]?).take cap).filter (isAutTab adj hrk hs)

theorem isAut_of_mem_autList (hhs : ∀ x : H.V, x ∈ hs) {fuel cap : ℕ} {a : List H.V}
    (h : a ∈ autList H hs fuel cap) : isAut H hs a = true :=
  isAut_of_isAutTab hhs (List.mem_filter.mp h).2

/-- **The symmetry test.**  An automorphism of `H` fixing every label handed out so far may not
send the next one backwards.

This is one test per automorphism and it stays that cheap however deep the search goes: the
automorphisms that have anything left to say are the ones that fixed the whole assignment, and the
first label they move settles them for good. -/
def autKeep (H G : CGraph) (hs : List H.V) (auts : List (List H.V)) (pre : List (G.V × H.V))
    (x : H.V) : Bool :=
  auts.all fun a ↦ !(pre.all fun q ↦ decide (relab hs a q.2 = q.2)) ||
    decide (hs.idxOf x ≤ hs.idxOf (relab hs a x))

/-- `autKeep` at every step of an assignment, which is what `finalOk` asks of a finished one. -/
def autOkAll (H G : CGraph) (hs : List H.V) (auts : List (List H.V)) :
    List (G.V × H.V) → Bool
  | [] => true
  | q :: pre => autKeep H G hs auts pre q.2 && autOkAll H G hs auts pre

theorem autOkAll_cons {auts : List (List H.V)} {q : G.V × H.V} {pre : List (G.V × H.V)} :
    autOkAll H G hs auts (q :: pre) = (autKeep H G hs auts pre q.2 && autOkAll H G hs auts pre) :=
  rfl

/-- Every step of an assignment passing the test means the step that added `x` did. -/
theorem autKeep_of_autOkAll {auts : List (List H.V)} {pre : List (G.V × H.V)} {v : G.V} {x : H.V} :
    ∀ l : List (G.V × H.V), autOkAll H G hs auts (l ++ (v, x) :: pre) = true →
      autKeep H G hs auts pre x = true
  | [], h => (Bool.and_eq_true .. |>.mp h).1
  | _ :: l, h => autKeep_of_autOkAll l (Bool.and_eq_true .. |>.mp h).2

/-- With no automorphisms there is nothing to break, and the test is vacuous. -/
theorem autOkAll_nil : ∀ r : List (G.V × H.V), autOkAll H G hs [] r = true
  | [] => rfl
  | q :: t => by rw [autOkAll_cons, autOkAll_nil t, autKeep]; rfl

/-- The automorphisms the search breaks the symmetry with.  They are consulted only when `symPairs`
has nothing to say, because the two symmetry breaks are not jointly satisfiable in general: a
labelling with the least label word need not also put interchangeable vertices in order.  Nothing
is lost by the choice, since `symPairs` is empty on exactly the patterns — cycles, cages, paths,
and any graph that is its own contraction — the automorphisms are there for.

The fuel and the cap bound both halves of the cost whatever `H` is, and both can only cost
pruning: fewer automorphisms means `autOkAll` accepts more assignments, never fewer. -/
def searchAuts (H : CGraph) (hs : List H.V) : List (List H.V) :=
  if (symPairs H hs).isEmpty then autList H hs 20000 256 else []

theorem isAut_of_mem_searchAuts (hhs : ∀ x : H.V, x ∈ hs) {a : List H.V}
    (h : a ∈ searchAuts H hs) : isAut H hs a = true := by
  rw [searchAuts] at h
  split at h
  · exact isAut_of_mem_autList hhs h
  · exact absurd h (by simp)

/-- When there are interchangeable vertices to order, the automorphisms stand down. -/
theorem searchAuts_of_symPairs {hs : List H.V} (h : ¬ (symPairs H hs).isEmpty = true) :
    searchAuts H hs = [] := by rw [searchAuts, ite_eq_right h]

end Autos

/-! ## The test on a complete assignment

Everything the search prunes with has to follow from this one test, so everything a contraction has
to satisfy is checked here: the assignment labels each vertex of `G` exactly once, every block is
connected — which makes it nonempty, so every vertex of `H` is used — two blocks are joined in `H`
exactly when an edge of `G` runs between them, interchangeable vertices of `H` take their blocks in
order, and no automorphism of `H` relabels the assignment to an earlier one. -/

/-- Does a complete assignment describe a contraction? -/
def finalOk (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (auts : List (List H.V)) (r : List (G.V × H.V)) : Bool :=
  decide (r.map Prod.fst = gs.reverse) &&
    hs.all (fun x ↦ connOk G (fibre r x)) &&
    (hs.all fun x ↦ hs.all fun y ↦ decide (x = y) ||
      (H.Adj x y == linked G (fibre r x) (fibre r y))) &&
    (pairs.all fun p ↦
      decide (minRank gs.idxOf (fibre r p.1) ≤ minRank gs.idxOf (fibre r p.2))) &&
    autOkAll H G hs auts r

variable {hs : List H.V} {gs : List G.V} {pairs : List (H.V × H.V)} {auts : List (List H.V)}
  {r : List (G.V × H.V)}

theorem finalOk_keys (h : finalOk H G hs gs pairs auts r = true) :
    r.map Prod.fst = gs.reverse := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.1

theorem finalOk_conn (h : finalOk H G hs gs pairs auts r = true) {x : H.V} (hx : x ∈ hs) :
    connOk G (fibre r x) = true := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1.2 x hx

theorem finalOk_adj (h : finalOk H G hs gs pairs auts r = true) {x y : H.V} (hx : x ∈ hs)
    (hy : y ∈ hs) (hxy : x ≠ y) : H.Adj x y = linked G (fibre r x) (fibre r y) := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have hxy' := List.all_eq_true.mp (List.all_eq_true.mp h.1.1.2 x hx) y hy
  rw [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hxy'
  exact hxy'.resolve_left hxy

theorem finalOk_sym (h : finalOk H G hs gs pairs auts r = true) {p : H.V × H.V} (hp : p ∈ pairs) :
    minRank gs.idxOf (fibre r p.1) ≤ minRank gs.idxOf (fibre r p.2) := by
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp h.1.2 p hp)

theorem finalOk_aut (h : finalOk H G hs gs pairs auts r = true) :
    autOkAll H G hs auts r = true := by
  rw [finalOk, Bool.and_eq_true] at h
  exact h.2

/-- A connected block is a nonempty one, so an accepted assignment uses every vertex of `H`. -/
theorem fibre_ne_nil (h : finalOk H G hs gs pairs auts r = true) {x : H.V} (hx : x ∈ hs) :
    fibre r x ≠ [] := by
  intro hnil
  have hc := finalOk_conn h hx
  rw [hnil] at hc
  exact absurd hc (by simp [connOk])

/-! ## Soundness -/

/-- The contraction a complete, accepted assignment describes. -/
def ofFinal (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (auts : List (List H.V)) (r : List (G.V × H.V)) (hcov : ∀ x : H.V, x ∈ hs)
    (hgs : ∀ v : G.V, v ∈ gs) (hgnd : gs.Nodup)
    (h : finalOk H G hs gs pairs auts r = true) : H.ContractionOf G := by
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

* No automorphism of `H` fixing the labels so far sends this one backwards.  This is `autKeep`, and
  it goes first because it is the cheapest of the five and, when there is any symmetry left, the
  one that kills the most.
* Every done neighbour of `v` is in the same block or in an adjacent one — the induced condition,
  one pair at a time.
* The vertices of `H` still unused fit into the vertices of `G` still unassigned.
* Interchangeable vertices of `H` start their blocks in order.
* The blocks pass `blocksOk`, which is the dearest of the tests and so is left for last. -/
def candKeep (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (auts : List (List H.V)) (v : G.V) (pre : List (G.V × H.V)) (x : H.V) : Bool :=
  let asg := (v, x) :: pre
  let pool := gs.drop (pre.length + 1)
  autKeep H G hs auts pre x &&
    pre.all (fun q ↦ !G.Adj v q.1 || decide (q.2 = x) || H.Adj x q.2) &&
    decide (hs.countP (fun y ↦ !(asg.map Prod.snd).contains y) + asg.length ≤ gs.length) &&
    pairs.all (fun p ↦ (fibre asg p.2).isEmpty || (!(fibre asg p.1).isEmpty &&
      decide (minRank gs.idxOf (fibre asg p.1) ≤ minRank gs.idxOf (fibre asg p.2)))) &&
    blocksOk H G pool (hs.map fun y ↦ (y, fibre asg y))

/-- The labels the search tries for `v`. -/
def candLab (H G : CGraph) (hs : List H.V) (gs : List G.V) (pairs : List (H.V × H.V))
    (auts : List (List H.V)) (v : G.V) (pre : List (G.V × H.V)) : List H.V :=
  (labSource H G hs v pre).filter (candKeep H G hs gs pairs auts v pre)

/-! ## What the search runs

`candKeep` reads as one test on one label, which is what the soundness proof below wants, but run
that way it redoes at every label almost everything it did at the last one.  All but one of the
blocks of `(v, x) :: pre` are blocks of `pre`, and so is everything asked of them: which vertex `x`
gets does not change whether the block of some other `y` can still be joined up, or whether an
unlabelled vertex touches it.  Only `x`'s own block moves.

So the work is lifted out of the loop over labels and into the node: build the blocks of `pre`
once, and with them the two answers, then give each label the table with its one entry replaced.
Two things keep that from costing more than it saves on the nodes where the cheap tests kill
everything.  The table is built after the first three tests and not before, so a node with no
survivor never builds it; and the two answers are thunks, so a block whose answer `blocksOkTab`
never looks at — it stops at the first block that fails — is never joined up at all.

The rank comes in as an argument for the same reason it does in the other two searches: `searchLab`
asks for it once per vertex of two blocks per candidate, and `List.idxOf` is a scan, so
`searchLabFast` passes a `Backtrack.rankTable`. -/

/-- The two things `blocksOk` asks of a block that do not depend on the label being tried: can what
is in it still be joined up, and does an unlabelled vertex still touch it? -/
def blockOk (G : CGraph) (pool f : List G.V) : Bool × Bool :=
  (connVia G pool f, pool.any fun u ↦ f.any (G.Adj u))

/-- `blocksOk` reading those two off a table instead of recomputing them. -/
def blocksOkTab (H G : CGraph) (fs : List (H.V × List G.V × Thunk (Bool × Bool))) : Bool :=
  fs.all fun p ↦
    p.2.2.get.1 && (p.2.1.isEmpty || p.2.2.get.2 ||
      fs.all fun q ↦ !H.Adj p.1 q.1 || linked G p.2.1 q.2.1)

theorem blocksOk_eq_blocksOkTab (hs : List H.V) (pool : List G.V) (b : H.V → List G.V) :
    blocksOk H G pool (hs.map fun y ↦ (y, b y)) =
      blocksOkTab H G (hs.map fun y ↦ (y, b y, Thunk.mk fun _ ↦ blockOk G pool (b y))) := by
  rw [blocksOk, blocksOkTab, List.all_map, List.all_map]
  refine List.all_congr rfl fun y ↦ ?_
  simp only [Function.comp_apply, blockOk, List.all_map, Function.comp_def, Thunk.get]

/-- Two tests in a row are two filters in a row. -/
private theorem filter_and {α : Type} (l : List α) (a d : α → Bool) :
    l.filter (fun x ↦ a x && d x) = (l.filter a).filter d := by
  rw [List.filter_filter]
  exact List.filter_congr fun x _ ↦ Bool.and_comm ..

/-- What the search runs in place of `candLab`: the four cheap tests first, then the block table
for whatever got through, then the two block tests off that table. -/
def candLabWith (H G : CGraph) (rank : G.V → ℕ) (hs : List H.V) (gs : List G.V)
    (pairs : List (H.V × H.V)) (auts : List (List H.V)) (v : G.V) (pre : List (G.V × H.V)) :
    List H.V :=
  let used := pre.map Prod.snd
  let len := pre.length + 1
  let rough := (labSource H G hs v pre).filter fun x ↦
    autKeep H G hs auts pre x &&
      pre.all (fun q ↦ !G.Adj v q.1 || decide (q.2 = x) || H.Adj x q.2) &&
        decide (hs.countP (fun y ↦ !(x :: used).contains y) + len ≤ gs.length) &&
        pairs.all (fun p ↦ (fibre ((v, x) :: pre) p.2).isEmpty ||
          (!(fibre ((v, x) :: pre) p.1).isEmpty &&
            decide (minRank rank (fibre ((v, x) :: pre) p.1) ≤
              minRank rank (fibre ((v, x) :: pre) p.2))))
  if rough.isEmpty then [] else
    let pool := gs.drop len
    let tab := hs.map fun y ↦ let f := fibre pre y; (y, f, Thunk.mk fun _ ↦ blockOk G pool f)
    rough.filter fun x ↦ blocksOkTab H G (tab.map fun t ↦
      if x = t.1 then (let f := v :: t.2.1; (t.1, f, Thunk.mk fun _ ↦ blockOk G pool f)) else t)

theorem candLab_eq_candLabWith (H G : CGraph) (hs : List H.V) (gs : List G.V)
    (pairs : List (H.V × H.V)) (auts : List (List H.V)) :
    candLab H G hs gs pairs auts = candLabWith H G (fun v ↦ gs.idxOf v) hs gs pairs auts := by
  funext v pre
  have hk : candKeep H G hs gs pairs auts v pre = fun x ↦
      (autKeep H G hs auts pre x &&
        pre.all (fun q ↦ !G.Adj v q.1 || decide (q.2 = x) || H.Adj x q.2) &&
        decide (hs.countP (fun y ↦ !(x :: pre.map Prod.snd).contains y) + (pre.length + 1) ≤
          gs.length) &&
        pairs.all (fun p ↦ (fibre ((v, x) :: pre) p.2).isEmpty ||
          (!(fibre ((v, x) :: pre) p.1).isEmpty &&
            decide (minRank gs.idxOf (fibre ((v, x) :: pre) p.1) ≤
              minRank gs.idxOf (fibre ((v, x) :: pre) p.2))))) &&
      blocksOk H G (gs.drop (pre.length + 1))
        (hs.map fun y ↦ (y, fibre ((v, x) :: pre) y)) := by
    funext x; rw [candKeep]; rfl
  rw [candLab, hk, filter_and, candLabWith]
  split
  · rename_i hemp
    rw [List.isEmpty_iff.mp hemp]
    rfl
  · refine List.filter_congr fun x _ ↦ ?_
    have hmap : ((hs.map fun y ↦ (y, fibre pre y, Thunk.mk fun _ ↦
          blockOk G (gs.drop (pre.length + 1)) (fibre pre y))).map fun t ↦
          if x = t.1 then (t.1, v :: t.2.1, Thunk.mk fun _ ↦
            blockOk G (gs.drop (pre.length + 1)) (v :: t.2.1)) else t) =
        hs.map fun y ↦ (y, fibre ((v, x) :: pre) y, Thunk.mk fun _ ↦
          blockOk G (gs.drop (pre.length + 1)) (fibre ((v, x) :: pre) y)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ ↦ ?_
      simp only [Function.comp_apply, fibre_cons]
      split <;> rfl
    rw [hmap, ← blocksOk_eq_blocksOkTab]

/-! ## The block tests on masks

`candLabWith` lifts the block tests out of the loop over labels, but what is left at the node is
still list work: `blocksOk` walks each block as a list, `connVia` floods it a list at a time, and
"does an unlabelled vertex still touch this block?" is a scan of the pool per block.  That is where
the search's time goes — on `C6 ⋏ heawood` the three block tests are five sixths of the run.

All three questions are about *sets of vertices of `G`*, and the search already ranks those
vertices: `Row` carries each one's own bit and its neighbourhood as a mask.  So the blocks go in as
words.  A block is a `mask` and its neighbourhood a `nbrMask`; "an unlabelled vertex touches it"
and `linked` become one `&&&` each, against the pool and against another block; and the flood is a
fixed-point loop on words that visits each row once per round.  Building the two tables costs one
pass over the assignment, which the node was making anyway.

Nothing here changes what the search accepts.  Each definition is proved equal to the list one it
replaces, ending at `candLabWith_eq_candLabMask`, and it is still the list version that the
soundness proof below talks about. -/

/-- The bit of each vertex of `gs`, indexed by rank. -/
def bitTab (rs : List (Row G)) : Array ℕ := (rs.map Row.bit).toArray

/-- The neighbour mask of each vertex of `gs`, indexed by rank. -/
def nbTab (rs : List (Row G)) : Array ℕ := (rs.map Row.nb).toArray

theorem getD_bitTab (hgs : ∀ v, v ∈ gs) (u : G.V) :
    (bitTab (rowList G gs)).getD (gs.idxOf u) 0 = mask G gs [u] := by
  rw [bitTab, getD_toArray, rowList, List.map_map, List.getElem?_map,
    List.getElem?_idxOf (hgs u)]
  show (row G gs u).bit = _
  simp [row, mask]

theorem getD_nbTab (hgs : ∀ v, v ∈ gs) (u : G.V) :
    (nbTab (rowList G gs)).getD (gs.idxOf u) 0 = (row G gs u).nb := by
  rw [nbTab, getD_toArray, rowList, List.map_map, List.getElem?_map,
    List.getElem?_idxOf (hgs u)]
  rfl

/-- One pass over the assignment, or-ing a mask per pair into the slot of its label.  Slots are
indexed by the rank of the label; a label with no rank has no slot, and the pair is dropped. -/
def orTab (H G : CGraph) (f : G.V → ℕ) (hrk : H.V → ℕ) (m : ℕ) (pre : List (G.V × H.V)) :
    Array ℕ :=
  pre.foldl (fun t q ↦ t.set! (hrk q.2) (t[hrk q.2]! ||| f q.1)) (Array.replicate m 0)

private theorem getElem!_foldl_or (f : G.V → ℕ) (hrk : H.V → ℕ) {i : ℕ} :
    ∀ (pre : List (G.V × H.V)) (t : Array ℕ), i < t.size →
      (pre.foldl (fun t q ↦ t.set! (hrk q.2) (t[hrk q.2]! ||| f q.1)) t)[i]!
        = (pre.filter fun q ↦ hrk q.2 == i).foldl (fun a q ↦ a ||| f q.1) t[i]!
  | [], _, _ => rfl
  | q :: pre, t, ht => by
    rw [List.foldl_cons, getElem!_foldl_or f hrk pre _ (by rw [Array.size_set!]; exact ht)]
    by_cases hq : hrk q.2 = i
    · rw [List.filter_cons_of_pos (by simp [hq]), List.foldl_cons, ← hq,
        Array.getElem!_set!_self _ _ _ (hq ▸ ht)]
    · rw [List.filter_cons_of_neg (by simp [hq]), Array.getElem!_set!_ne _ _ _ _ hq]

theorem testBit_getElem!_orTab (f : G.V → ℕ) (hrk : H.V → ℕ) {m i k : ℕ} (hi : i < m)
    (pre : List (G.V × H.V)) :
    ((orTab H G f hrk m pre)[i]!).testBit k
      = (pre.filter fun q ↦ hrk q.2 == i).any fun q ↦ (f q.1).testBit k := by
  rw [orTab, getElem!_foldl_or f hrk pre _ (by simpa using hi)]
  rw [show (Array.replicate m 0)[i]! = 0 by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate,
      ite_eq_left hi]
    rfl]
  simpa using testBit_foldl_or (γ := G.V × H.V) (fun q ↦ f q.1) k
    (pre.filter fun q ↦ hrk q.2 == i) 0

/-! ## The flood

`reachAux` grows a set of vertices a front at a time, and `reachMask` is that loop with the set,
the front and the pool as words.  One round is `stepMask`: a pass over the rows that ors in the bit
of every row whose neighbourhood meets the front, cut back down to the pool.  So a round costs one
`&&&`, one `!=` and one `|||` per vertex, where the list version costs a membership test per
neighbour per vertex. -/

theorem mask_eq_zero_iff {l : List G.V} : mask G gs l = 0 ↔ l = [] := by
  cases l with
  | nil => simp [mask]
  | cons u rest =>
    simp only [reduceCtorEq, iff_false]
    intro h
    have hb := testBit_mask_of_mem (gs := gs) (l := u :: rest) (u := u) (by simp)
    rw [h] at hb
    simp at hb

/-- **What the mask of a frontier reaches**: bit `u` of the round's pass over the rows is set
exactly when `u` is next to something in the frontier. -/
theorem testBit_nbrsFold (hgs : ∀ v, v ∈ gs) (front : List G.V) (u : G.V) :
    ((rowList G gs).foldl
        (fun (m : ℕ) (p : Row G) ↦ if mask G gs front &&& p.nb != 0 then m ||| p.bit else m)
        0).testBit (gs.idxOf u) = front.any (G.Adj u) := by
  rw [testBit_foldl_or_if, Nat.zero_testBit, Bool.false_or, Bool.eq_iff_iff, List.any_eq_true,
    List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hb⟩
    obtain ⟨hkeep, hbit⟩ := Bool.and_eq_true .. ▸ hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
    rw [show (row G gs w).bit = 1 <<< gs.idxOf w from rfl, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_eq] at hbit
    obtain rfl := (List.idxOf_inj (hgs w)).mp hbit
    obtain ⟨z, hz, hzf⟩ := (and_mask_ne_zero_iff hgs).mp (bne_iff_ne.mp hkeep)
    exact ⟨z, hz, (List.mem_filter.mp hzf).2⟩
  · rintro ⟨z, hz, hzu⟩
    refine ⟨row G gs u, List.mem_map.mpr ⟨u, hgs u, rfl⟩, Bool.and_eq_true .. ▸ ⟨?_, ?_⟩⟩
    · exact bne_iff_ne.mpr
        ((and_mask_ne_zero_iff hgs).mpr ⟨z, hz, List.mem_filter.mpr ⟨hgs z, hzu⟩⟩)
    · rw [show (row G gs u).bit = 1 <<< gs.idxOf u from rfl, Nat.one_shiftLeft]
      simp

/-- One round of `reachMask`: the pool vertices next to the frontier. -/
def stepMask (rs : List (Row G)) (front pool : ℕ) : ℕ :=
  (rs.foldl (fun m p ↦ if front &&& p.nb != 0 then m ||| p.bit else m) 0) &&& pool

/-- `reachAux` on bitmasks: the set in hand, the frontier and the pool are masks over the ranks,
and a round is one pass over the rows. -/
def reachMask (G : CGraph) (rs : List (Row G)) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, S, _, _ => S
  | n + 1, S, front, pool =>
    let new := stepMask rs front pool
    if new == 0 then S else reachMask G rs n (S ||| new) new (pool ^^^ new)

theorem stepMask_eq (hgs : ∀ v, v ∈ gs) (front pool : List G.V) :
    stepMask (rowList G gs) (mask G gs front) (mask G gs pool)
      = mask G gs (pool.filter fun v ↦ front.any (G.Adj v)) := by
  refine eq_of_testBit_pool (fun k hk ↦ ?_)
    (fun k hk ↦ testBit_mask_mono (fun _ h ↦ List.mem_of_mem_filter h) hk) (fun u hu ↦ ?_)
  · rw [stepMask, Nat.testBit_and, Bool.and_eq_true] at hk
    exact hk.2
  · rw [stepMask, Nat.testBit_and, testBit_nbrsFold hgs, testBit_mask_of_mem hu, Bool.and_true,
      testBit_mask_eq_decide_mem hgs]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.mem_filter]
    exact ⟨fun h ↦ ⟨hu, h⟩, fun h ↦ h.2⟩

private theorem xor_stepMask (hgs : ∀ v, v ∈ gs) (front pool : List G.V) :
    mask G gs pool ^^^ mask G gs (pool.filter fun v ↦ front.any (G.Adj v))
      = mask G gs (pool.filter fun v ↦ !front.any (G.Adj v)) := by
  refine eq_of_testBit_pool (fun k hk ↦ ?_)
    (fun k hk ↦ testBit_mask_mono (fun _ h ↦ List.mem_of_mem_filter h) hk) (fun u hu ↦ ?_)
  · rw [Nat.testBit_xor] at hk
    by_contra hc
    rw [Bool.eq_false_iff.mpr hc, Bool.eq_false_iff.mpr fun h ↦
      hc (testBit_mask_mono (fun _ h' ↦ List.mem_of_mem_filter h') h)] at hk
    simp at hk
  · rw [Nat.testBit_xor, testBit_mask_of_mem hu, testBit_mask_eq_decide_mem hgs,
      testBit_mask_eq_decide_mem hgs]
    by_cases hc : front.any (G.Adj u) <;> simp [List.mem_filter, hu, hc]

theorem reachMask_eq_mask (hgs : ∀ v, v ∈ gs) : ∀ (n : ℕ) (S front pool : List G.V),
    reachMask G (rowList G gs) n (mask G gs S) (mask G gs front) (mask G gs pool)
      = mask G gs (reachAux G n S front pool)
  | 0, _, _, _ => rfl
  | n + 1, S, front, pool => by
    rw [reachMask, reachAux]
    simp only [stepMask_eq hgs]
    by_cases hemp : (pool.filter fun v ↦ front.any (G.Adj v)) = []
    · rw [ite_eq_left (by simp [hemp, mask_eq_zero_iff]), ite_eq_left (by simp [hemp])]
    · rw [ite_eq_right (by simp [mask_eq_zero_iff, hemp]), ite_eq_right (by simp [hemp]),
        ← reachMask_eq_mask hgs n _ _ _, xor_stepMask hgs, mask_append, Nat.lor_comm]

/-- The flood, stopped as soon as it has covered `target`.  `connViaMask` only ever asks whether
the block ended up inside what the flood reached, and that is settled the moment it does — for a
one-vertex block, before the first round. -/
def reachUntil (G : CGraph) (rs : List (Row G)) (target : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, S, _, _ => target &&& S == target
  | n + 1, S, front, pool =>
    if target &&& S == target then true
    else
      let new := stepMask rs front pool
      if new == 0 then false else reachUntil G rs target n (S ||| new) new (pool ^^^ new)

/-- **The flood only grows.** -/
private theorem or_reachMask (rs : List (Row G)) :
    ∀ (n S front pool T : ℕ), T ||| S = S →
      T ||| reachMask G rs n S front pool = reachMask G rs n S front pool
  | 0, _, _, _, _, h => h
  | n + 1, S, front, pool, T, h => by
    rw [reachMask]
    by_cases hz : (stepMask rs front pool == 0) = true
    · rw [ite_eq_left hz]; exact h
    · rw [ite_eq_right hz]
      exact or_reachMask rs n _ _ _ T (by rw [← Nat.lor_assoc, h])

private theorem and_eq_self_trans {a b c : ℕ} (hab : a &&& b = a) (hbc : b ||| c = c) :
    a &&& c = a := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  rw [Nat.testBit_and]
  cases hk : a.testBit k with
  | false => simp
  | true =>
    have h1 : b.testBit k = true := by
      simpa [Nat.testBit_and, hk] using congrArg (fun m ↦ m.testBit k) hab
    have h2 : c.testBit k = true := by
      simpa [Nat.testBit_or, h1] using congrArg (fun m ↦ m.testBit k) hbc
    simp [h2]

/-- **Stopping early answers the same question.** -/
theorem reachUntil_eq (rs : List (Row G)) : ∀ (target n S front pool : ℕ),
    reachUntil G rs target n S front pool = (target &&& reachMask G rs n S front pool == target)
  | _, 0, _, _, _ => rfl
  | target, n + 1, S, front, pool => by
    by_cases ht : (target &&& S == target) = true
    · rw [reachUntil, ite_eq_left ht, eq_comm, beq_iff_eq]
      exact and_eq_self_trans (by simpa using ht)
        (or_reachMask rs (n + 1) S front pool S (Nat.or_self S))
    · rw [reachUntil, ite_eq_right ht, reachMask]
      by_cases hz : (stepMask rs front pool == 0) = true
      · rw [ite_eq_left hz, ite_eq_left hz]
        exact (Bool.eq_false_iff.mpr ht).symm
      · rw [ite_eq_right hz, ite_eq_right hz]
        exact reachUntil_eq rs target n _ _ _

/-- **Spare fuel changes nothing.**  `reachAux` stops of its own accord once nothing new arrives,
and one vertex leaves the pool every round, so any two budgets big enough for the pool agree. -/
theorem reachAux_fuel : ∀ (n m : ℕ) (S front pool : List G.V), pool.length ≤ n → n ≤ m →
    reachAux G n S front pool = reachAux G m S front pool
  | 0, m, S, front, pool, hn, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    cases m with
    | zero => rfl
    | succ m => rw [reachAux, reachAux]; simp
  | n + 1, m, S, front, pool, hn, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [reachAux, reachAux]
    split_ifs with hne
    · rfl
    · refine reachAux_fuel n m _ _ _ ?_ (by omega)
      have hlt : (pool.filter fun v ↦ !front.any (G.Adj v)).length < pool.length := by
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil (pool.filter fun v ↦ front.any (G.Adj v))
          fun h ↦ hne (by rw [h]; rfl)
        obtain ⟨hwp, hwa⟩ := List.mem_filter.mp hw
        exact List.length_filter_lt_length_iff_exists.mpr ⟨w, hwp, by simpa using hwa⟩
      omega

/-! ## `connVia` on masks

The mask version has to start its flood somewhere, and a word does not say which vertex its lowest
set bit belongs to.  So the start comes from the rows instead: `rs.find?` returns the first row
whose bit lies in the block, which is the block's lowest-ranked vertex.  The flood then runs over
the block and the pool together, rather than holding the block's other vertices out of the pool the
way the list version does — that saves a removal a mask cannot do cheaply, and it is sound because
neither the block's order nor the vertex the flood started from survives into what `connVia` means,
which is what `exists_of_connVia` and `connVia_iff_reach` say.

The flood also stops as soon as it has covered the block, rather than running out the component:
the question is only whether the block is inside one component, and once the block is inside what
the flood has reached, it is. -/

theorem mask_singleton (v : G.V) : mask G gs [v] = 1 <<< gs.idxOf v := by simp [mask]

theorem bit_eq_mask_of_mem_rowList {p : Row G} (h : p ∈ rowList G gs) :
    p.bit = mask G gs [p.vert] := by
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp h
  rw [mask_singleton]
  rfl

/-- **What `connVia` really asks**: that the block sits inside a connected set built out of itself
and the pool.  Neither the block's order nor which of its vertices the search grows from shows up
here, which is what lets the mask version start from whichever vertex the lowest bit names. -/
theorem exists_of_connVia {pool f : List G.V} (h : connVia G pool f = true) (hne : f ≠ []) :
    ∃ B : List G.V, G.ConnectedOn {u | u ∈ B} ∧ (∀ u ∈ f, u ∈ B) ∧ ∀ u ∈ B, u ∈ f ∨ u ∈ pool := by
  match f, hne with
  | v :: rest, _ =>
    rw [connVia, List.all_eq_true] at h
    refine ⟨reach G [v] (rest ++ pool), connectedOn_reach ?_, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
    · have hsing : {u : G.V | u ∈ [v]} = {v} := by ext u; simp
      rw [hsing]
      exact G.connectedOn_singleton v
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact mem_reach_of_mem (by simp)
      · exact List.contains_iff_mem.mp (h u hu)
    · rcases mem_or_mem_of_mem_reach hu with hu | hu
      · exact Or.inl (by rw [List.mem_singleton.mp hu]; simp)
      · rcases List.mem_append.mp hu with hu | hu
        · exact Or.inl (List.mem_cons_of_mem _ hu)
        · exact Or.inr hu

/-- **`connVia` from any vertex of the block.**  The search grows the block from whichever vertex
comes first in it; a mask has no first vertex, so it grows the block from whichever one the lowest
bit names, and this says the answer is the same. -/
theorem connVia_iff_reach {pool f : List G.V} {w : G.V} (hw : w ∈ f) :
    connVia G pool f = true ↔ ∀ u ∈ f, u ∈ reach G [w] (f ++ pool) := by
  constructor
  · intro h u hu
    obtain ⟨B, hB, hfB, hBf⟩ := exists_of_connVia h (List.ne_nil_of_mem hw)
    exact subset_reach hB (fun z hz ↦ (hBf z hz).elim
      (fun h ↦ Or.inr (List.mem_append_left _ h)) fun h ↦ Or.inr (List.mem_append_right _ h))
      ⟨w, hfB w hw, mem_reach_of_mem (by simp)⟩ u (hfB u hu)
  · intro h
    refine connVia_of_connectedOn (B := reach G [w] (f ++ pool)) (connectedOn_reach ?_) h
      fun u hu ↦ ?_
    · have hsing : {u : G.V | u ∈ [w]} = {w} := by ext u; simp
      rw [hsing]
      exact G.connectedOn_singleton w
    · rcases mem_or_mem_of_mem_reach hu with hu | hu
      · exact Or.inl (by rw [List.mem_singleton.mp hu]; exact hw)
      · exact List.mem_append.mp hu

/-- `connVia` on masks: grow the block from the vertex its lowest bit names, through the block and
the pool, and ask whether the whole block came back. -/
def connViaMask (G : CGraph) (rs : List (Row G)) (n pm fm : ℕ) : Bool :=
  if fm == 0 then true else
    match rs.find? fun p ↦ fm &&& p.bit != 0 with
    | none => true
    | some p => reachUntil G rs fm n p.bit p.bit (fm ||| pm)

theorem connVia_eq_connViaMask (hgs : ∀ v, v ∈ gs) {n : ℕ} (pool f : List G.V)
    (hn : f.length + pool.length ≤ n) :
    connVia G pool f = connViaMask G (rowList G gs) n (mask G gs pool) (mask G gs f) := by
  rcases eq_or_ne f [] with rfl | hne
  · rw [connViaMask, ite_eq_left (by simp [mask])]
    rfl
  · have h0 : ¬(mask G gs f == 0) = true := by simp [mask_eq_zero_iff, hne]
    rw [connViaMask, ite_eq_right h0]
    -- the row the lowest bit names is a vertex of the block
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil f hne
    cases hf : (rowList G gs).find? fun p ↦ mask G gs f &&& p.bit != 0 with
    | none =>
      have hmem : row G gs v ∈ rowList G gs := List.mem_map.mpr ⟨v, hgs v, rfl⟩
      have hne0 : mask G gs f &&& (row G gs v).bit ≠ 0 := by
        rw [bit_eq_mask_of_mem_rowList hmem, and_mask_ne_zero_iff hgs]
        exact ⟨v, hv, List.mem_singleton.mpr rfl⟩
      exact absurd (show (mask G gs f &&& (row G gs v).bit != 0) = true by simpa using hne0)
        (List.find?_eq_none.mp hf _ hmem)
    | some p =>
      have hp : p ∈ rowList G gs := List.mem_of_find?_eq_some hf
      have hw : p.vert ∈ f := by
        have := List.find?_some hf
        rw [bne_iff_ne, ne_eq, bit_eq_mask_of_mem_rowList hp, ← ne_eq,
          and_mask_ne_zero_iff hgs] at this
        obtain ⟨u, hu, hup⟩ := this
        rwa [List.mem_singleton.mp hup] at hu
      show connVia G pool f = reachUntil G (rowList G gs) (mask G gs f) n p.bit p.bit
        (mask G gs f ||| mask G gs pool)
      rw [reachUntil_eq, bit_eq_mask_of_mem_rowList hp, ← mask_append, reachMask_eq_mask hgs,
        ← reachAux_fuel (f ++ pool).length n [p.vert] [p.vert] (f ++ pool) le_rfl
          (by simpa using hn),
        show reachAux G (f ++ pool).length [p.vert] [p.vert] (f ++ pool)
          = reach G [p.vert] (f ++ pool) from rfl,
        Bool.eq_iff_iff, beq_iff_eq, and_mask_eq_self_iff, connVia_iff_reach hw]
      exact forall₂_congr fun u _ ↦ by rw [testBit_mask_eq_decide_mem hgs, decide_eq_true_eq]

/-! ## The other two block tests

"Some unlabelled vertex still touches this block" and `linked` are the same question asked of two
different sets: does the block's neighbourhood meet them?  With that neighbourhood as a mask, both
are `&&& _ != 0`. -/

/-- The neighbourhood of a block, as a mask over ranks. -/
def nbrMask (G : CGraph) (gs f : List G.V) : ℕ := mask G gs (gs.filter fun w ↦ f.any (G.Adj · w))

theorem testBit_nbrMask (hgs : ∀ v, v ∈ gs) (f : List G.V) (w : G.V) :
    (nbrMask G gs f).testBit (gs.idxOf w) = f.any (G.Adj · w) := by
  rw [nbrMask, testBit_mask_eq_decide_mem hgs, Bool.eq_iff_iff, decide_eq_true_eq,
    List.mem_filter]
  simp [hgs w]

theorem isEmpty_eq_mask_beq_zero (f : List G.V) : f.isEmpty = (mask G gs f == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, mask_eq_zero_iff, List.isEmpty_iff]

/-- **An unlabelled vertex still touches the block** is one `&&&`. -/
theorem touch_eq_mask (hgs : ∀ v, v ∈ gs) (f pool : List G.V) :
    pool.any (fun u ↦ f.any (G.Adj u)) = ((nbrMask G gs f &&& mask G gs pool) != 0) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, nbrMask, and_mask_ne_zero_iff hgs, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hfu⟩
    obtain ⟨z, hz, hzu⟩ := List.any_eq_true.mp hfu
    exact ⟨u, List.mem_filter.mpr ⟨hgs u, List.any_eq_true.mpr ⟨z, hz, by rw [G.symm]; exact hzu⟩⟩,
      hu⟩
  · rintro ⟨w, hwf, hwp⟩
    obtain ⟨z, hz, hzw⟩ := List.any_eq_true.mp (List.mem_filter.mp hwf).2
    exact ⟨w, hwp, List.any_eq_true.mpr ⟨z, hz, by rw [G.symm]; exact hzw⟩⟩

/-- **An edge of `G` runs between two blocks** is one `&&&`. -/
theorem linked_eq_mask (hgs : ∀ v, v ∈ gs) (f t : List G.V) :
    linked G f t = ((nbrMask G gs f &&& mask G gs t) != 0) := by
  rw [Bool.eq_iff_iff, linked_iff, bne_iff_ne, nbrMask, and_mask_ne_zero_iff hgs]
  constructor
  · rintro ⟨u, hu, w, hw, huw⟩
    exact ⟨w, List.mem_filter.mpr ⟨hgs w, List.any_eq_true.mpr ⟨u, hu, huw⟩⟩, hw⟩
  · rintro ⟨w, hwf, hwt⟩
    obtain ⟨u, hu, huw⟩ := List.any_eq_true.mp (List.mem_filter.mp hwf).2
    exact ⟨u, hu, w, hwt, huw⟩

/-! ## Building the table

One fold over the assignment fills both arrays: the pair `(v, x)` ors `v`'s bit into slot `x` of
one and `v`'s neighbourhood into slot `x` of the other.  So a labelled vertex costs two reads, two
`|||`s and two writes, and the table is built once at the node instead of once per label. -/

/-- The block of each label and the neighbourhood of that block, as masks over the ranks of `gs`,
built in one pass over the assignment.  Slot `i` is the label of rank `i`. -/
def maskTab (H G : CGraph) (hrk : H.V → ℕ) (rk : G.V → ℕ) (bits nbrs : Array ℕ) (m : ℕ)
    (pre : List (G.V × H.V)) : Array ℕ × Array ℕ :=
  pre.foldl (fun t q ↦
      (t.1.set! (hrk q.2) (t.1[hrk q.2]! ||| bits[rk q.1]!),
        t.2.set! (hrk q.2) (t.2[hrk q.2]! ||| nbrs[rk q.1]!)))
    (Array.replicate m 0, Array.replicate m 0)

private theorem foldl_pair {α β γ : Type} (f : α → γ → α) (g : β → γ → β) :
    ∀ (l : List γ) (a : α) (b : β),
      l.foldl (fun t q ↦ (f t.1 q, g t.2 q)) (a, b) = (l.foldl f a, l.foldl g b)
  | [], _, _ => rfl
  | q :: l, a, b => by rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, foldl_pair]

theorem maskTab_eq (H G : CGraph) (hrk : H.V → ℕ) (rk : G.V → ℕ) (bits nbrs : Array ℕ) (m : ℕ)
    (pre : List (G.V × H.V)) :
    maskTab H G hrk rk bits nbrs m pre
      = (orTab H G (fun u ↦ bits[rk u]!) hrk m pre, orTab H G (fun u ↦ nbrs[rk u]!) hrk m pre) := by
  rw [maskTab, orTab, orTab]
  exact foldl_pair (fun (t : Array ℕ) q ↦ t.set! (hrk q.2) (t[hrk q.2]! ||| bits[rk q.1]!))
    (fun (t : Array ℕ) q ↦ t.set! (hrk q.2) (t[hrk q.2]! ||| nbrs[rk q.1]!)) pre _ _

theorem getElem!_bitTab (hgs : ∀ v, v ∈ gs) (u : G.V) :
    (bitTab (rowList G gs))[gs.idxOf u]! = mask G gs [u] := by
  rw [Array.getElem!_eq_getD]
  exact getD_bitTab hgs u

theorem getElem!_nbTab (hgs : ∀ v, v ∈ gs) (u : G.V) :
    (nbTab (rowList G gs))[gs.idxOf u]! = (row G gs u).nb := by
  rw [Array.getElem!_eq_getD]
  exact getD_nbTab hgs u

/-- **A slot of the table is a fold over that label's block.**  The pass writes a pair into the
slot of its label's rank, and the ranks tell the labels apart. -/
theorem testBit_getElem!_slot (hhs : ∀ x : H.V, x ∈ hs) (F : G.V → ℕ) (y : H.V)
    (pre : List (G.V × H.V)) (k : ℕ) :
    ((orTab H G F hs.idxOf hs.length pre)[hs.idxOf y]!).testBit k
      = (fibre pre y).any fun u ↦ (F u).testBit k := by
  rw [testBit_getElem!_orTab F _ (List.idxOf_lt_length_of_mem (hhs y)) pre,
    show (pre.filter fun q ↦ hs.idxOf q.2 == hs.idxOf y)
        = pre.filter (fun q ↦ decide (q.2 = y)) from
      List.filter_congr fun q _ ↦ by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, List.idxOf_inj (hhs q.2)],
    fibre, List.any_map]
  rfl

theorem bit_slot (hgs : ∀ v, v ∈ gs) (hhs : ∀ x : H.V, x ∈ hs) (y : H.V)
    (pre : List (G.V × H.V)) :
    (orTab H G (fun u ↦ (bitTab (rowList G gs))[gs.idxOf u]!) hs.idxOf hs.length pre)[hs.idxOf y]!
      = mask G gs (fibre pre y) := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  rw [testBit_getElem!_slot hhs _ y pre k]
  simp only [getElem!_bitTab hgs, testBit_mask, List.any_cons, List.any_nil, Bool.or_false]

theorem nb_slot (hgs : ∀ v, v ∈ gs) (hhs : ∀ x : H.V, x ∈ hs) (y : H.V)
    (pre : List (G.V × H.V)) :
    (orTab H G (fun u ↦ (nbTab (rowList G gs))[gs.idxOf u]!) hs.idxOf hs.length pre)[hs.idxOf y]!
      = nbrMask G gs (fibre pre y) := by
  have hnbmask : ∀ u : G.V, (nbTab (rowList G gs))[gs.idxOf u]! = mask G gs (gs.filter (G.Adj u)) :=
    fun u ↦ getElem!_nbTab hgs u
  refine eq_of_testBit_pool (gs := gs) (pool := gs) (fun k hk ↦ ?_) (fun k hk ↦ ?_) fun w _ ↦ ?_
  · rw [testBit_getElem!_slot hhs _ y pre k, List.any_eq_true] at hk
    obtain ⟨u, -, hu⟩ := hk
    rw [hnbmask] at hu
    exact testBit_mask_mono (fun _ h ↦ (List.mem_filter.mp h).1) hu
  · exact testBit_mask_mono (fun _ h ↦ (List.mem_filter.mp h).1) hk
  · rw [testBit_getElem!_slot hhs _ y pre, testBit_nbrMask hgs]
    simp only [getElem!_nbTab hgs, testBit_row_nb (G := G) hgs]

/-- `blocksOk` with the blocks and their neighbourhoods read off masks. -/
def blocksOkMask (H G : CGraph) (rs : List (Row G)) (n pm : ℕ) (bm nm : Array ℕ)
    (hz : List (H.V × ℕ)) : Bool :=
  hz.all fun p ↦
    connViaMask G rs n pm bm[p.2]! &&
      (bm[p.2]! == 0 || (nm[p.2]! &&& pm) != 0 ||
        hz.all fun q ↦ !H.Adj p.1 q.1 || (nm[p.2]! &&& bm[q.2]!) != 0)

theorem blocksOk_eq_blocksOkMask (hgs : ∀ v, v ∈ gs) {n : ℕ} {bm nm : Array ℕ}
    {b : H.V → List G.V} {hrk : H.V → ℕ} {pool : List G.V}
    (hb : ∀ y, bm[hrk y]! = mask G gs (b y)) (hnb : ∀ y, nm[hrk y]! = nbrMask G gs (b y))
    (hn : ∀ y, (b y).length + pool.length ≤ n) :
    blocksOk H G pool (hs.map fun y ↦ (y, b y))
      = blocksOkMask H G (rowList G gs) n (mask G gs pool) bm nm (hs.map fun y ↦ (y, hrk y)) := by
  rw [blocksOk, blocksOkMask]
  simp only [List.all_map, Function.comp_def, hb, hnb, isEmpty_eq_mask_beq_zero (gs := gs),
    touch_eq_mask hgs, linked_eq_mask hgs,
    show ∀ y, connVia G pool (b y) = connViaMask G (rowList G gs) n (mask G gs pool)
      (mask G gs (b y)) from fun y ↦ connVia_eq_connViaMask hgs pool (b y) (hn y)]

/-! ## The candidate list

`candLabMask` is `candLabWith` with the block tests read off that table.  The only thing a label
changes is its own slot, so trying one costs two `set!`s on top of the shared table. -/

theorem nb_row_eq (u : G.V) : (row G gs u).nb = mask G gs (gs.filter (G.Adj u)) := rfl

theorem nbrMask_cons (hgs : ∀ v, v ∈ gs) (u : G.V) (f : List G.V) :
    nbrMask G gs (u :: f) = (row G gs u).nb ||| nbrMask G gs f := by
  refine eq_of_testBit_pool (gs := gs) (pool := gs) (fun k hk ↦ ?_) (fun k hk ↦ ?_) fun w _ ↦ ?_
  · exact testBit_mask_mono (fun _ h ↦ (List.mem_filter.mp h).1) hk
  · rw [Nat.testBit_or, Bool.or_eq_true, nb_row_eq, nbrMask] at hk
    exact hk.elim (testBit_mask_mono fun _ h ↦ (List.mem_filter.mp h).1)
      (testBit_mask_mono fun _ h ↦ (List.mem_filter.mp h).1)
  · rw [testBit_nbrMask hgs, Nat.testBit_or, testBit_row_nb (G := G) hgs, testBit_nbrMask hgs,
      List.any_cons]

private theorem size_foldl_set! (F : G.V → ℕ) (hrk : H.V → ℕ) :
    ∀ (pre : List (G.V × H.V)) (t : Array ℕ),
      (pre.foldl (fun t q ↦ t.set! (hrk q.2) (t[hrk q.2]! ||| F q.1)) t).size = t.size
  | [], _ => rfl
  | q :: pre, t => by rw [List.foldl_cons, size_foldl_set!, Array.size_set!]

theorem size_orTab (F : G.V → ℕ) (hrk : H.V → ℕ) (m : ℕ) (pre : List (G.V × H.V)) :
    (orTab H G F hrk m pre).size = m := by
  rw [orTab, size_foldl_set!, Array.size_replicate]

private theorem foldl_bits (hgs : ∀ v, v ∈ gs) : ∀ (l : List G.V) (a : ℕ),
    l.foldl (fun m u ↦ m ||| (bitTab (rowList G gs))[gs.idxOf u]!) a
      = l.foldl (fun m u ↦ m ||| 1 <<< gs.idxOf u) a
  | [], _ => rfl
  | u :: l, a => by
    rw [List.foldl_cons, List.foldl_cons, foldl_bits hgs l, getElem!_bitTab hgs, mask_singleton]

theorem foldl_bits_eq_mask (hgs : ∀ v, v ∈ gs) (l : List G.V) :
    l.foldl (fun m u ↦ m ||| (bitTab (rowList G gs))[gs.idxOf u]!) 0 = mask G gs l :=
  foldl_bits hgs l 0

/-! ## The label tests

Two of the cheap tests are still list work per label, and both walk the assignment to do it: the
induced condition asks every already-placed neighbour of `v` about `x`, and the counting test asks
`contains` about every label of `H`.  They are questions about *labels*, so they go the same way
the blocks did — masks, this time over `hs`.

`hclosedTab` is the closed neighbourhood in `H` of each label, so the induced condition is "the
labels of `v`'s placed neighbours all lie in `x`'s closed neighbourhood", which is one `&&&`; and
with the used labels collected into a mask once at the node, the counting test drops the `contains`
and reads a bit. -/

/-- Each label's own bit, as a mask over `hs`, indexed by rank. -/
def hbitTab (H : CGraph) (hs : List H.V) : Array ℕ := (hs.map fun y ↦ mask H hs [y]).toArray

/-- Each label's closed neighbourhood in `H`, as a mask over `hs`, indexed by rank. -/
def hclosedTab (H : CGraph) (hs : List H.V) : Array ℕ :=
  (hs.map fun y ↦ mask H hs (hs.filter fun z ↦ decide (z = y) || H.Adj y z)).toArray

theorem getElem!_hbitTab (hhs : ∀ x : H.V, x ∈ hs) (y : H.V) :
    (hbitTab H hs)[hs.idxOf y]! = mask H hs [y] := by
  rw [hbitTab, Array.getElem!_eq_getD, getD_toArray, List.getElem?_map,
    List.getElem?_idxOf (hhs y)]
  rfl

theorem getElem!_hclosedTab (hhs : ∀ x : H.V, x ∈ hs) (y : H.V) :
    (hclosedTab H hs)[hs.idxOf y]!
      = mask H hs (hs.filter fun z ↦ decide (z = y) || H.Adj y z) := by
  rw [hclosedTab, Array.getElem!_eq_getD, getD_toArray, List.getElem?_map,
    List.getElem?_idxOf (hhs y)]
  rfl

/-- The labels an assignment has used, as a mask over `hs`. -/
def usedMask (H G : CGraph) (hbit : Array ℕ) (hrk : H.V → ℕ) (pre : List (G.V × H.V)) : ℕ :=
  pre.foldl (fun m q ↦ m ||| hbit[hrk q.2]!) 0

/-- The labels of the already-placed neighbours of `v`, as a mask over `hs`. -/
def nbrLabMask (H G : CGraph) (hbit : Array ℕ) (hrk : H.V → ℕ) (v : G.V)
    (pre : List (G.V × H.V)) : ℕ :=
  pre.foldl (fun m q ↦ if G.Adj v q.1 then m ||| hbit[hrk q.2]! else m) 0

theorem usedMask_eq (hhs : ∀ x : H.V, x ∈ hs) (pre : List (G.V × H.V)) :
    usedMask H G (hbitTab H hs) hs.idxOf pre = mask H hs (pre.map Prod.snd) := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  rw [usedMask, testBit_foldl_or, testBit_mask]
  simp [getElem!_hbitTab hhs, testBit_mask, List.any_map, Function.comp_def]

theorem nbrLabMask_eq (hhs : ∀ x : H.V, x ∈ hs) (v : G.V) (pre : List (G.V × H.V)) :
    nbrLabMask H G (hbitTab H hs) hs.idxOf v pre
      = mask H hs ((pre.filter fun q ↦ G.Adj v q.1).map Prod.snd) := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  rw [nbrLabMask, testBit_foldl_or_if, testBit_mask]
  simp [getElem!_hbitTab hhs, testBit_mask, List.any_map, List.any_filter, Function.comp_def]

/-- **The induced condition as one `&&&`.** -/
theorem induced_eq_mask (hhs : ∀ x : H.V, x ∈ hs) (v : G.V) (pre : List (G.V × H.V)) (x : H.V) :
    pre.all (fun q ↦ !G.Adj v q.1 || decide (q.2 = x) || H.Adj x q.2)
      = (nbrLabMask H G (hbitTab H hs) hs.idxOf v pre &&& (hclosedTab H hs)[hs.idxOf x]!
          == nbrLabMask H G (hbitTab H hs) hs.idxOf v pre) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, nbrLabMask_eq hhs, and_mask_eq_self_iff]
  simp only [getElem!_hclosedTab hhs, testBit_mask_eq_decide_mem hhs, decide_eq_true_eq,
    List.mem_filter, List.all_eq_true, List.mem_map, List.mem_filter, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, forall_exists_index, and_imp]
  constructor
  · rintro h u q hq hqv rfl
    exact ⟨hhs q.2, by simpa [hqv] using h q hq⟩
  · rintro h q hq
    by_cases hqv : G.Adj v q.1
    · simpa [hqv] using (h q.2 q hq (by simpa using hqv) rfl).2
    · simp [hqv]

/-- **The counting test off the used mask.**  Which labels are still free is a question about
`hs`, and the mask answers it without walking the assignment again. -/
theorem countP_unused_eq_mask (hhs : ∀ x : H.V, x ∈ hs) (pre : List (G.V × H.V)) (x : H.V) :
    hs.countP (fun y ↦ !(x :: pre.map Prod.snd).contains y)
      = hs.countP (fun y ↦
          !(usedMask H G (hbitTab H hs) hs.idxOf pre ||| (hbitTab H hs)[hs.idxOf x]!).testBit
            (hs.idxOf y)) := by
  refine List.countP_congr fun y _ ↦ ?_
  rw [usedMask_eq hhs, getElem!_hbitTab hhs, ← mask_append, testBit_mask_eq_decide_mem hhs]
  simp [and_comm]

/-! The symmetry test goes the same way, and the shape of it is what makes the masks pay: an
automorphism is still in force exactly when the used labels miss the ones it moves, which is one
`&&&` against the mask the node already built for the counting test, and what it then forbids is a
mask of labels fixed once and for all.  So the whole test is a fold over the automorphisms at the
node and a single bit at each candidate, rather than a walk down the assignment per automorphism
per candidate. -/

/-- Each automorphism as two masks over `hs`: the labels it moves, and the labels it sends
backwards. -/
def autTab (H : CGraph) (hs : List H.V) (auts : List (List H.V)) : List (ℕ × ℕ) :=
  auts.map fun a ↦
    (mask H hs (hs.filter fun y ↦ !decide (relab hs a y = y)),
      mask H hs (hs.filter fun y ↦ decide (hs.idxOf (relab hs a y) < hs.idxOf y)))

/-- The labels forbidden by the automorphisms still in force, as a mask over `hs`. -/
def badLabMask (atab : List (ℕ × ℕ)) (um : ℕ) : ℕ :=
  atab.foldl (fun b p ↦ if um &&& p.1 == 0 then b ||| p.2 else b) 0

private theorem autKeep_one (hhs : ∀ x : H.V, x ∈ hs) (a : List H.V) (pre : List (G.V × H.V))
    (x : H.V) :
    (!(pre.all fun q ↦ decide (relab hs a q.2 = q.2)) ||
        decide (hs.idxOf x ≤ hs.idxOf (relab hs a x)))
      = !((mask H hs (pre.map Prod.snd) &&&
            mask H hs (hs.filter fun y ↦ !decide (relab hs a y = y)) == 0) &&
          (mask H hs (hs.filter fun y ↦ decide (hs.idxOf (relab hs a y) < hs.idxOf y))).testBit
            (hs.idxOf x)) := by
  have hz : (mask H hs (pre.map Prod.snd) &&&
        mask H hs (hs.filter fun y ↦ !decide (relab hs a y = y)) == 0)
      = pre.all fun q ↦ decide (relab hs a q.2 = q.2) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, and_mask_eq_zero_iff hhs, List.all_eq_true]
    constructor
    · intro h q hq
      by_contra hne
      exact h q.2 (List.mem_map_of_mem hq) (List.mem_filter.mpr ⟨hhs q.2, by simpa using hne⟩)
    · intro h u hu hmem
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      have hne := (List.mem_filter.mp hmem).2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hne
      exact hne (of_decide_eq_true (h q hq))
  have hb : (mask H hs (hs.filter fun y ↦ decide (hs.idxOf (relab hs a y) < hs.idxOf y))).testBit
        (hs.idxOf x) = decide (hs.idxOf (relab hs a x) < hs.idxOf x) := by
    rw [testBit_mask_eq_decide_mem hhs]
    simp [List.mem_filter, hhs x]
  rw [hz, hb, Bool.not_and]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]

/-- **The symmetry test as one bit.** -/
theorem autKeep_eq_mask (hhs : ∀ x : H.V, x ∈ hs) (auts : List (List H.V))
    (pre : List (G.V × H.V)) (x : H.V) :
    autKeep H G hs auts pre x
      = !(badLabMask (autTab H hs auts) (usedMask H G (hbitTab H hs) hs.idxOf pre)).testBit
          (hs.idxOf x) := by
  rw [badLabMask, testBit_foldl_or_if, autTab, List.any_map, usedMask_eq hhs, autKeep,
    Nat.zero_testBit, Bool.false_or]
  induction auts with
  | nil => rfl
  | cons a t ih =>
    rw [List.all_cons, List.any_cons, Bool.not_or, ih]
    congr 1
    exact autKeep_one hhs a pre x

/-- What the block tests read, built once for the search.

`rows` is what a round of the connectivity sweep runs over; `bits` and `nbrs` are a vertex's own
bit and its neighbour mask, indexed by rank, so that the pass over the assignment that builds the
blocks costs one array lookup and one `|||` per pair; `hrk` and `rk` are the two rank tables; and
`hz` pairs each label with the slot its block lives in. -/
structure MaskEnv (H G : CGraph) where
  /-- The rows of `G`, in rank order. -/
  rows : List (Row G)
  /-- Each vertex's own bit, indexed by rank. -/
  bits : Array ℕ
  /-- Each vertex's neighbour mask, indexed by rank. -/
  nbrs : Array ℕ
  /-- The rank of a label in `hs`, which is the slot its block lives in. -/
  hrk : H.V → ℕ
  /-- The rank of a vertex of `G` in `gs`. -/
  rk : G.V → ℕ
  /-- The labels, each with its slot. -/
  hz : List (H.V × ℕ)
  /-- Each label's own bit, indexed by its rank in `hs`. -/
  hbit : Array ℕ
  /-- Each label's closed neighbourhood in `H`, indexed by its rank in `hs`. -/
  hclosed : Array ℕ

/-- The environment of a search of `G` for `H` over the orders `hs` and `gs`. -/
def maskEnv (H G : CGraph) (hs : List H.V) (gs : List G.V) : MaskEnv H G :=
  let rows := rowList G gs
  let hrk := Backtrack.tabAt (Backtrack.rankTable hs)
  { rows, bits := bitTab rows, nbrs := nbTab rows, hrk,
    rk := Backtrack.tabAt (Backtrack.rankTable gs), hz := hs.map fun y ↦ (y, hrk y),
    hbit := hbitTab H hs, hclosed := hclosedTab H hs }

/-- `candLabWith` on masks: the blocks and their neighbourhoods are built in one pass over the
assignment, "an unlabelled vertex still touches it" and `linked` are one `&&&` each, the
connectivity sweep runs on words, and the induced and counting tests read the labels of the
assignment out of a mask instead of walking it once per candidate. -/
def candLabMask (H G : CGraph) (env : MaskEnv H G) (hs : List H.V) (gs : List G.V)
    (pairs : List (H.V × H.V)) (atab : List (ℕ × ℕ)) (v : G.V) (pre : List (G.V × H.V)) :
    List H.V :=
  let len := pre.length + 1
  let nbrLab := nbrLabMask H G env.hbit env.hrk v pre
  let um := usedMask H G env.hbit env.hrk pre
  let bad := badLabMask atab um
  let rough := (labSource H G hs v pre).filter fun x ↦
    !bad.testBit (env.hrk x) &&
      (nbrLab &&& env.hclosed[env.hrk x]! == nbrLab) &&
      decide (hs.countP (fun y ↦ !(um ||| env.hbit[env.hrk x]!).testBit (env.hrk y)) + len
        ≤ gs.length) &&
      pairs.all (fun p ↦ (fibre ((v, x) :: pre) p.2).isEmpty ||
        (!(fibre ((v, x) :: pre) p.1).isEmpty &&
          decide (minRank env.rk (fibre ((v, x) :: pre) p.1) ≤
            minRank env.rk (fibre ((v, x) :: pre) p.2))))
  if rough.isEmpty then [] else
    let pm := (gs.drop len).foldl (fun a u ↦ a ||| env.bits[env.rk u]!) 0
    let t := maskTab H G env.hrk env.rk env.bits env.nbrs hs.length pre
    let vb := env.bits[env.rk v]!
    let vn := env.nbrs[env.rk v]!
    rough.filter fun x ↦
      let i := env.hrk x
      blocksOkMask H G env.rows (len + gs.length) pm
        (t.1.set! i (t.1[i]! ||| vb)) (t.2.set! i (t.2[i]! ||| vn)) env.hz

theorem candLabWith_eq_candLabMask (hgs : ∀ v, v ∈ gs) (hhs : ∀ x : H.V, x ∈ hs)
    (pairs : List (H.V × H.V)) (auts : List (List H.V)) :
    candLabWith H G (fun u ↦ gs.idxOf u) hs gs pairs auts
      = candLabMask H G (maskEnv H G hs gs) hs gs pairs (autTab H hs auts) := by
  funext v pre
  simp only [candLabWith, candLabMask, maskEnv, Backtrack.tabAt_rankTable, maskTab_eq,
    induced_eq_mask hhs, countP_unused_eq_mask hhs, autKeep_eq_mask hhs]
  split_ifs with hemp
  · rfl
  · refine List.filter_congr fun x _ ↦ ?_
    set pool := gs.drop (pre.length + 1) with hpool
    -- the pool mask, and the two tables with `x`'s slot grown by `v`
    have hkey : ∀ (F : G.V → ℕ) (M : List G.V → ℕ),
        (∀ y : H.V, (orTab H G F (fun z ↦ hs.idxOf z) hs.length pre)[hs.idxOf y]!
          = M (fibre pre y)) → (∀ f : List G.V, M (v :: f) = F v ||| M f) →
        ∀ y : H.V, ((orTab H G F (fun z ↦ hs.idxOf z) hs.length pre).set! (hs.idxOf x)
            ((orTab H G F (fun z ↦ hs.idxOf z) hs.length pre)[hs.idxOf x]! ||| F v))[hs.idxOf y]!
          = M (fibre ((v, x) :: pre) y) := by
      intro F M hslot hcons y
      rw [fibre_cons]
      by_cases hxy : x = y
      · subst hxy
        rw [Array.getElem!_set!_self _ _ _
            (by rw [size_orTab]; exact List.idxOf_lt_length_of_mem (hhs x)),
          ite_eq_left rfl, hslot x, hcons]
        exact Nat.lor_comm _ _
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun h ↦ hxy ((List.idxOf_inj (hhs x)).mp h)),
          ite_eq_right hxy, hslot y]
    have hb := hkey _ (mask G gs) (bit_slot hgs hhs · pre)
      (fun f ↦ by rw [getElem!_bitTab hgs, show v :: f = [v] ++ f from rfl, mask_append])
    have hnb := hkey _ (nbrMask G gs) (nb_slot hgs hhs · pre)
      (fun f ↦ by rw [getElem!_nbTab hgs, nbrMask_cons hgs])
    have hn : ∀ y : H.V,
        (fibre ((v, x) :: pre) y).length + pool.length ≤ pre.length + 1 + gs.length := by
      intro y
      have h1 : (fibre ((v, x) :: pre) y).length ≤ pre.length + 1 := by
        rw [fibre, List.length_map]
        exact le_trans (List.length_filter_le _ _) (by simp)
      have h2 : pool.length ≤ gs.length := by rw [hpool]; simp
      omega
    rw [foldl_bits_eq_mask hgs, show (hs.map fun y ↦ (y, fibre pre y,
        Thunk.mk fun _ ↦ blockOk G pool (fibre pre y))).map
          (fun t ↦ if x = t.1 then (t.1, v :: t.2.1,
            Thunk.mk fun _ ↦ blockOk G pool (v :: t.2.1)) else t)
        = hs.map fun y ↦ (y, fibre ((v, x) :: pre) y,
            Thunk.mk fun _ ↦ blockOk G pool (fibre ((v, x) :: pre) y)) from ?_,
      ← blocksOk_eq_blocksOkTab, blocksOk_eq_blocksOkMask hgs hb hnb hn]
    rw [List.map_map]
    refine List.map_congr_left fun y _ ↦ ?_
    simp only [Function.comp_apply, fibre_cons]
    split <;> rfl

/-! ## Soundness of the pruning -/

section Cand

variable {l pre : List (G.V × H.V)} {v : G.V} {x : H.V}

/-- The induced condition as the candidate tests see it: adjacent vertices of `G` are in the same
block or in adjacent ones. -/
theorem adj_of_finalOk (hcov : ∀ y : H.V, y ∈ hs) {r : List (G.V × H.V)}
    (h : finalOk H G hs gs pairs auts r = true) {q q' : G.V × H.V} (hq : q ∈ r) (hq' : q' ∈ r)
    (hadj : G.Adj q.1 q'.1 = true) : q.2 = q'.2 ∨ H.Adj q.2 q'.2 = true := by
  by_cases hqx : q.2 = q'.2
  · exact Or.inl hqx
  refine Or.inr ?_
  rw [finalOk_adj h (hcov q.2) (hcov q'.2) hqx, linked_iff]
  exact ⟨q.1, mem_fibre.mpr hq, q'.1, mem_fibre.mpr hq', hadj⟩

/-- The same for a neighbour of `v` that is done already: it is in `x`'s block or in one next to
it. -/
theorem adj_pre_of_finalOk (hcov : ∀ y : H.V, y ∈ hs)
    (h : finalOk H G hs gs pairs auts (l ++ (v, x) :: pre) = true) {q : G.V × H.V} (hq : q ∈ pre)
    (hadj : G.Adj v q.1 = true) : q.2 = x ∨ H.Adj x q.2 = true :=
  (adj_of_finalOk hcov h (q := (v, x)) (by simp) (by simp [hq]) hadj).imp Eq.symm id

theorem mem_labSource (hcov : ∀ y : H.V, y ∈ hs)
    (h : finalOk H G hs gs pairs auts (l ++ (v, x) :: pre) = true) :
    x ∈ labSource H G hs v pre := by
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
    (h : finalOk H G hs gs pairs auts (l ++ (v, x) :: pre) = true) :
    x ∈ candLab H G hs gs pairs auts v pre := by
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
  rw [candKeep, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- the symmetry test against the automorphisms
    exact autKeep_of_autOkAll l (finalOk_aut h)
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
it has already been relabelled so that interchangeable vertices of `H` take their blocks in order
and no automorphism of `H` moves it earlier. -/
theorem finalOk_asgOf (f : H.ContractionOf G) (hgs : ∀ v : G.V, v ∈ gs)
    (hsym : ∀ p ∈ pairs, modelMin f.branch gs.idxOf gs p.1 ≤ modelMin f.branch gs.idxOf gs p.2)
    (haut : autOkAll H G hs auts (asgOf f gs).reverse = true) :
    finalOk H G hs gs pairs auts (asgOf f gs).reverse = true := by
  have hmem : ∀ (v : G.V) (x : H.V), v ∈ fibre (asgOf f gs).reverse x ↔ f v = x := fun v x ↦
    mem_fibre_asgOf.trans (and_iff_right (hgs v))
  have hmin : ∀ x : H.V,
      minRank gs.idxOf (fibre (asgOf f gs).reverse x) = modelMin f.branch gs.idxOf gs x := by
    intro x
    refine minRank_congr fun v ↦ ?_
    rw [hmem, List.mem_filter, decide_eq_true_eq, f.branch_eq_some_iff]
    exact (and_iff_right (hgs v)).symm
  rw [finalOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨decide_eq_true ?_, ?_⟩, ?_⟩, ?_⟩, haut⟩
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

/-- **Relabelling a contraction along an automorphism the other way round.**  Same construction as
`ContractionOf.exists_reindex`, but stated on the total map, which is what the label word of
`ContractionSearch.labKey` is written in terms of. -/
theorem ContractionOf.exists_relabel (f : H.ContractionOf G) {σ : H.V → H.V}
    (hinj : Function.Injective σ) (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    ∃ g : H.ContractionOf G, ∀ v : G.V, g v = σ (f v) := by
  classical
  let e : H.V ≃ H.V := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  let i : H ≃cg H := ⟨e.symm, fun {a b} ↦ by
    show (H.Adj (e.symm a) (e.symm b) = true) ↔ (H.Adj a b = true)
    rw [← hadj (e.symm a) (e.symm b)]
    show (H.Adj (e (e.symm a)) (e (e.symm b)) = true) ↔ _
    rw [e.apply_symm_apply, e.apply_symm_apply]⟩
  refine ⟨(ContractionOf.ofIso i).trans f, fun v ↦ ?_⟩
  rw [ContractionOf.trans_apply, ContractionOf.ofIso_apply]
  show e (f v) = σ (f v)
  rfl

namespace ContractionSearch

variable {hs : List H.V} {gs : List G.V}

/-! ### The label word

The lexicographic order the symmetry test breaks the automorphisms with is easier to argue about as
an order on numbers: read the label word as the digits of a numeral, most significant first, and
lexicographic order on words of a fixed length is the order on the numerals.  So a contraction
whose word is least is one the test accepts, and there is one because the naturals are
well-ordered. -/

/-- The label word of an assignment as a numeral: the position in `hs` of each vertex's label, as
digits in base `hs.length + 1`, most significant first. -/
def labKey (hs : List H.V) (lab : G.V → H.V) : List G.V → ℕ
  | [] => 0
  | v :: rest => hs.idxOf (lab v) * (hs.length + 1) ^ rest.length + labKey hs lab rest

theorem labKey_lt (hs : List H.V) (lab : G.V → H.V) :
    ∀ gs : List G.V, labKey hs lab gs < (hs.length + 1) ^ gs.length
  | [] => Nat.zero_lt_one
  | v :: rest => by
    rw [labKey, List.length_cons, pow_succ']
    calc hs.idxOf (lab v) * (hs.length + 1) ^ rest.length + labKey hs lab rest
        < hs.idxOf (lab v) * (hs.length + 1) ^ rest.length + (hs.length + 1) ^ rest.length :=
          Nat.add_lt_add_left (labKey_lt hs lab rest) _
      _ = (hs.idxOf (lab v) + 1) * (hs.length + 1) ^ rest.length := by ring
      _ ≤ (hs.length + 1) * (hs.length + 1) ^ rest.length :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (List.idxOf_le_length))

/-- Two words agreeing up to a place where the first is smaller give the smaller numeral. -/
theorem labKey_lt_of_prefix {lab lab' : G.V → H.V} {v : G.V} {rest : List G.V}
    (hv : hs.idxOf (lab v) < hs.idxOf (lab' v)) :
    ∀ p : List G.V, (∀ u ∈ p, hs.idxOf (lab u) = hs.idxOf (lab' u)) →
      labKey hs lab (p ++ v :: rest) < labKey hs lab' (p ++ v :: rest)
  | [], _ => by
    rw [List.nil_append, labKey, labKey]
    calc hs.idxOf (lab v) * (hs.length + 1) ^ rest.length + labKey hs lab rest
        < hs.idxOf (lab v) * (hs.length + 1) ^ rest.length + (hs.length + 1) ^ rest.length :=
          Nat.add_lt_add_left (labKey_lt hs lab rest) _
      _ = (hs.idxOf (lab v) + 1) * (hs.length + 1) ^ rest.length := by ring
      _ ≤ hs.idxOf (lab' v) * (hs.length + 1) ^ rest.length := Nat.mul_le_mul_right _ hv
      _ ≤ _ := Nat.le_add_right ..
  | u :: p, h => by
    rw [List.cons_append, labKey, labKey, h u (List.mem_cons_self ..)]
    exact Nat.add_lt_add_left
      (labKey_lt_of_prefix hv p fun w hw ↦ h w (List.mem_cons_of_mem _ hw)) _

/-- Some contraction has the least label word. -/
theorem exists_minKey (f : H.ContractionOf G) :
    ∃ g : H.ContractionOf G, ∀ g' : H.ContractionOf G,
      labKey hs (⇑g) gs ≤ labKey hs (⇑g') gs := by
  classical
  have hne : ∃ n, ∃ g : H.ContractionOf G, labKey hs (⇑g) gs = n := ⟨_, f, rfl⟩
  obtain ⟨g, hg⟩ := Nat.find_spec hne
  exact ⟨g, fun g' ↦ by rw [hg]; exact Nat.find_min' hne ⟨g', rfl⟩⟩

/-- The test at every step of an assignment, from the test at every way of splitting `gs`. -/
theorem autOkAll_asgOf {auts : List (List H.V)} {f : H.ContractionOf G} :
    ∀ gs : List G.V, (∀ (p : List G.V) (v : G.V) (rest : List G.V), gs = p ++ v :: rest →
      autKeep H G hs auts (asgOf f p).reverse (f v) = true) →
      autOkAll H G hs auts (asgOf f gs).reverse = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton p v ih =>
    intro h
    have hrw : (asgOf f (p ++ [v])).reverse = (v, f v) :: (asgOf f p).reverse := by simp [asgOf]
    rw [hrw, autOkAll_cons, Bool.and_eq_true]
    exact ⟨h p v [] rfl, ih fun p' v' rest' hp' ↦ h p' v' (rest' ++ [v]) (by rw [hp']; simp)⟩

/-- **The symmetry break is satisfiable**: whatever automorphisms the search is given, a
contraction with the least label word passes the test at every step, and so is one the search is
still allowed to find.

An automorphism that fixes every label assigned so far and sends the next one backwards would carry
the whole contraction to one with a smaller word: the labels it fixes leave the leading digits
alone, and the one it moves makes the first digit that changes smaller. -/
theorem exists_autOkAll (hhs : ∀ x : H.V, x ∈ hs) {auts : List (List H.V)}
    (hauts : ∀ a ∈ auts, isAut H hs a = true) (f : H.ContractionOf G) :
    ∃ g : H.ContractionOf G, autOkAll H G hs auts (asgOf g gs).reverse = true := by
  obtain ⟨g, hmin⟩ := exists_minKey (hs := hs) (gs := gs) f
  refine ⟨g, autOkAll_asgOf gs fun p v rest hgs ↦ List.all_eq_true.mpr fun a ha ↦ ?_⟩
  rw [Bool.or_eq_true, Bool.not_eq_true', List.all_reverse, asgOf, List.all_map]
  by_cases hfix : ∀ u ∈ p, relab hs a (g u) = g u
  · refine Or.inr (decide_eq_true (Nat.not_lt.mp fun hlt ↦ ?_))
    obtain ⟨g', hg'⟩ := g.exists_relabel (isAut_injective hhs (hauts a ha))
      (isAut_adj hhs (hauts a ha))
    refine absurd (hmin g') (Nat.not_le.mpr ?_)
    rw [hgs]
    refine labKey_lt_of_prefix (by rw [hg']; exact hlt) p fun u hu ↦ ?_
    rw [hg', hfix u hu]
  · refine Or.inl ?_
    push Not at hfix
    obtain ⟨u, hu, hne⟩ := hfix
    exact List.all_eq_false.mpr ⟨u, hu, by simpa using hne⟩

end ContractionSearch

/-! ## The search -/

section Search

open ContractionSearch

variable (H G)

/-- The assignment the search finds, if there is one. -/
def searchLab (rH : Roster H.V) (rG : Roster G.V) : Option (List (G.V × H.V)) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    Backtrack.dfs
      (candLab H G (searchOrder H rH.toList) (searchOrder G rG.toList)
        (symPairs H (searchOrder H rH.toList)) (searchAuts H (searchOrder H rH.toList)))
      (finalOk H G (searchOrder H rH.toList) (searchOrder G rG.toList)
        (symPairs H (searchOrder H rH.toList)) (searchAuts H (searchOrder H rH.toList)))
      (searchOrder G rG.toList) []
  else none

/-- What `searchLab` runs.  Four things are shared that the specification writes out: the two
search orders, each named four times above; the rank, which is a table rather than `List.idxOf`;
the row and mask tables the block tests read; and the two masks per automorphism the symmetry test
reads.  All of them are built once for the whole search. -/
def searchLabFast (rH : Roster H.V) (rG : Roster G.V) : Option (List (G.V × H.V)) :=
  if FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E then
    let hs := searchOrder H rH.toList
    let gs := searchOrder G rG.toList
    let pairs := symPairs H hs
    let auts := searchAuts H hs
    Backtrack.dfs (candLabMask H G (maskEnv H G hs gs) hs gs pairs (autTab H hs auts))
      (finalOk H G hs gs pairs auts) gs []
  else none

@[csimp] theorem searchLab_eq_searchLabFast : @searchLab = @searchLabFast := by
  funext H G rH rG
  simp only [searchLab, searchLabFast, candLab_eq_candLabWith,
    candLabWith_eq_candLabMask (mem_searchOrder G rG.mem_toList) (mem_searchOrder H rH.mem_toList)]

variable {H G}

theorem searchLab_goal {rH : Roster H.V} {rG : Roster G.V} {r : List (G.V × H.V)}
    (h : searchLab H G rH rG = some r) :
    finalOk H G (searchOrder H rH.toList) (searchOrder G rG.toList)
      (symPairs H (searchOrder H rH.toList)) (searchAuts H (searchOrder H rH.toList)) r = true := by
  rw [searchLab] at h
  split at h
  · exact Backtrack.goal_of_dfs_eq_some h
  · exact absurd h (by simp)

variable (H G)

/-- **Is `H` a contraction of `G`?**  Returns a witness if so.  See
`isEmpty_contractionOf_of_eq_none` for the other half of the answer. -/
def findContraction (rH : Roster H.V) (rG : Roster G.V) : Option (H.ContractionOf G) :=
  Option.pmap (p := fun r ↦ finalOk H G (searchOrder H rH.toList) (searchOrder G rG.toList)
      (symPairs H (searchOrder H rH.toList)) (searchAuts H (searchOrder H rH.toList)) r = true)
    (fun r hr ↦ ofFinal H G _ _ _ _ r (mem_searchOrder H rH.mem_toList)
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
  · -- the contraction is first relabelled to one both symmetry tests accept.  Only one of them is
    -- ever asking anything, so there is no need to satisfy them together
    obtain ⟨g, hgsym, hgaut⟩ : ∃ g : H.ContractionOf G,
        (∀ p ∈ symPairs H (searchOrder H rH.toList),
            modelMin g.branch (searchOrder G rG.toList).idxOf (searchOrder G rG.toList) p.1 ≤
              modelMin g.branch (searchOrder G rG.toList).idxOf (searchOrder G rG.toList) p.2) ∧
          autOkAll H G (searchOrder H rH.toList) (searchAuts H (searchOrder H rH.toList))
            (asgOf g (searchOrder G rG.toList)).reverse = true := by
      by_cases hp : (symPairs H (searchOrder H rH.toList)).isEmpty = true
      · obtain ⟨g, hg⟩ := exists_autOkAll (mem_searchOrder H rH.mem_toList)
          (fun _ ha ↦ isAut_of_mem_searchAuts (mem_searchOrder H rH.mem_toList) ha) f
        exact ⟨g, fun p hp' ↦ absurd hp' (by rw [List.isEmpty_iff.mp hp]; simp), hg⟩
      · obtain ⟨g, -, hgsym⟩ := exists_sorted_model_pairs (fun f : H.ContractionOf G ↦ f.branch)
          (fun f {_σ} hinj hadj ↦ f.exists_reindex hinj hadj)
          (hs := searchOrder H rH.toList) (gs := searchOrder G rG.toList)
          (rank := (searchOrder G rG.toList).idxOf) (mem_searchOrder H rH.mem_toList) f
          (fun v _ _ ↦ mem_searchOrder G rG.mem_toList v)
        exact ⟨g, hgsym, by rw [searchAuts_of_symPairs hp]; exact autOkAll_nil _⟩
    have hn := Backtrack.dfs_eq_none
      (fun _ _ _ _ hh ↦ mem_candLab (mem_searchOrder H rH.mem_toList)
        (searchOrder_nodup H rH.toList) (searchOrder_nodup G rG.toList) hh) h
      (keys_asgOf g (searchOrder G rG.toList))
    rw [List.append_nil,
      finalOk_asgOf g (mem_searchOrder G rG.mem_toList) hgsym hgaut] at hn
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
