import IsoGraph.Containment.Algorithms.Embedding

/-!
# Searching for a homomorphism, and for a quotient

Two more of the containment relations are a map with a condition on each pair of vertices, and
neither of them asks for it to be injective:

* a **homomorphism** `H →cg G` carries every edge of `H` to an edge of `G`, and nothing else;
* a **quotient** `H.QuotientOf G` is such a map the other way round, `G.V → H.V`, that is
  surjective.

So both are the same search — over all `card G.V ^ card H.V` maps, before pruning — and this file
runs it once, with the surjectivity test as a flag.  `CGraph.findHom` and `CGraph.findQuotient`
are the two entry points; each returns the witness itself when it succeeds, and
`CGraph.isEmpty_hom_iff` and `CGraph.isEmpty_quotientOf_iff` say that a `none` means there was
nothing to find.

This is not `Algorithms/Embedding.lean` with the injectivity test removed.  Injectivity is what
most of that file's pruning is built on — the twin classes are ordered by the image's rank, the
tail count asks how many ranks a class still needs above it, and the two counting guards
`card H.V ≤ card G.V` and `H.E ≤ G.E` are both false of a homomorphism in general.  What is left
without it is short enough to be its own search:

* **The order.**  `CGraph.searchOrder`, shared with the embedding search: the vertex of `H` with
  the most neighbours already placed goes next, so after the first one every vertex is (for a
  connected `H`) constrained by something already fixed.
* **The pivot.**  If `x` has a neighbour already placed at `u` then the image of `x` is a
  neighbour of `u`, so `CGraph.homPool` reads the candidates off `u`'s row rather than out of all
  of `G`.  On a sparse host that is the difference between a node costing `card G.V` and costing
  the degree of `u`.
* **Consistency.**  What survives must pass `CGraph.homCompat` against every placed vertex: an
  edge of `H` to an edge of `G`.  A non-edge of `H` constrains nothing, which is why this search
  is weaker than the induced one, and why a dense host makes it easy.  Which placements do
  constrain is not a question about the candidate, so `CGraph.homCandFast` asks it once at the
  node rather than once per candidate.

Deciding either relation is NP-hard — `H →cg Kₖ` is `k`-colourability of `H` — so there is no
better shape available.  The hard instances are a sparse pattern against a host with little
structure for the pivot to bite on, `Kₖ` being the extreme case.

## Colouring

`H →cg complete k` *is* a proper `k`-colouring of `H`, so `CGraph.findHom H (complete k)` decides
`k`-colourability and hands back the colouring.  There is no symmetry breaking here, so the search
sees all `k!` relabellings of every colouring; for a chromatic number that would be worth fixing,
but for one question at one `k` the pivot does most of the work.

## What it costs

`testing/CacheBench.lean`, cases `api-hom` and `api-quot`; best of three interleaved rounds, in
milliseconds.  `CGraph.findHom` is the search on the graphs as they are; `CGraph.homOf?` and
`CGraph.quotientOf?`, in `Algorithms/Cached.lean`, are the same search on tabulated copies of both
and are what to reach for:

| job                        | `find…` | cached |
| -------------------------- | ------- | ------ |
| `C₄` a quotient of `tutte` | 868     | 74     |
| `tutte → K₃`               | 29      | 2      |
| `mcgee → K₂`               | 3       | <1     |
| `grotzsch → K₄`            | 1       | <1     |
| `petersen → K₃`            | <1      | <1     |

The quotient is a whole order of magnitude past the rest, and its answer is `none` — the search
closed the entire tree, which is the honest cost of the relation.  It is also the shape the pivot
handles worst: 46 vertices of pattern against 4 of host, so the pool is never smaller than a
quarter of `G` and the pruning has to come from the prefix instead.  `mcgee → K₂` is the other
`none` and costs nothing, because an odd cycle refuses two colours a few steps in.  The successes
are cheap in proportion to the freedom the host leaves: `petersen → K₃` commits on the first
descent, `tutte → K₃` backtracks a while first.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable (H G : CGraph)

/-! ## Consistency of a partial assignment

The one test is on a *pair* of placements, and unlike `CGraph.compat` it says nothing about the
two images being different. -/

/-- Two placements `x ↦ u` and `y ↦ v` are compatible for a homomorphism when an edge of `H`
between `x` and `y` is matched by an edge of `G` between `u` and `v`. -/
def homCompat (p q : H.V × G.V) : Bool := !H.Adj p.1 q.1 || G.Adj p.2 q.2

theorem homCompat_comm (p q : H.V × G.V) : homCompat H G p q = homCompat H G q p := by
  simp only [homCompat, H.symm p.1 q.1, G.symm p.2 q.2]

theorem homCompat_symm : Std.Symm fun p q : H.V × G.V ↦ homCompat H G p q = true :=
  ⟨fun _ _ h ↦ (homCompat_comm H G _ _).trans h⟩

/-- Every two placements in the list are compatible. -/
def validHom : List (H.V × G.V) → Bool
  | [] => true
  | p :: rest => rest.all (homCompat H G p) && validHom rest

theorem validHom_iff (l : List (H.V × G.V)) :
    validHom H G l = true ↔ l.Pairwise fun p q ↦ homCompat H G p q = true := by
  induction l with
  | nil => simp [validHom]
  | cons p rest ih => simp [validHom, List.pairwise_cons, ih]

/-- A genuine homomorphism gives a consistent assignment. -/
theorem validHom_of_hom (f : H →cg G) (l : List H.V) :
    validHom H G (l.map fun x ↦ (x, f x)) = true := by
  rw [validHom_iff, List.pairwise_map]
  refine List.pairwise_of_forall_mem_list fun x _ y _ ↦ ?_
  rw [homCompat]
  cases hxy : H.Adj x y with
  | false => simp
  | true => simpa using f.map_rel (show H.Adj x y from by simp [hxy])

/-! ## Reading the map off a finished assignment

`lookupV`, `asgFun` and the two lemmas that say a nodup-keyed assignment is read back as it was
written are in `Algorithms/Embedding.lean`; the searches there need them too. -/

/-- **The homomorphism a complete, consistent assignment describes.** -/
def homOfAsg (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst)
    (hv : validHom H G r = true) : H →cg G where
  toFun := asgFun H G r hcov
  map_rel' := by
    intro x y hxy
    have hne : x ≠ y := fun h ↦ H.loopless y (h ▸ hxy)
    have := homCompat_symm H G
    have hc := ((validHom_iff H G r).mp hv).forall
      (asgFun_mem H G r hcov x) (asgFun_mem H G r hcov y) (fun h ↦ hne (congrArg Prod.fst h))
    simpa [homCompat, show H.Adj x y = true from hxy] using hc

/-! ## The search -/

/-- The vertices of `G` a candidate for `x` can be looked for in.  If a neighbour of `x` is
already placed at `u`, the image of `x` is a neighbour of `u`; otherwise nothing is known and the
whole roster has to be tried. -/
def homPool (rG : Roster G.V) (x : H.V) (pre : List (H.V × G.V)) : List G.V :=
  match pre.find? fun p ↦ H.Adj x p.1 with
  | none => rG.toList
  | some p => rG.toList.filter (G.Adj p.2)

theorem mem_homPool {rG : Roster G.V} {x : H.V} {pre : List (H.V × G.V)} {u : G.V}
    (h : ∀ p ∈ pre, homCompat H G (x, u) p = true) : u ∈ homPool H G rG x pre := by
  rw [homPool]
  split
  · exact rG.mem_toList u
  · rename_i p hp
    have hadj : H.Adj x p.1 = true := by simpa using List.find?_some hp
    have hc := h p (List.mem_of_find?_eq_some hp)
    rw [homCompat, hadj] at hc
    exact List.mem_filter.mpr ⟨rG.mem_toList u, by rw [G.symm p.2 u]; simpa using hc⟩

/-- The candidates for `x`, given what is already placed. -/
def homCand (rG : Roster G.V) (x : H.V) (pre : List (H.V × G.V)) : List G.V :=
  (homPool H G rG x pre).filter fun u ↦ pre.all fun p ↦ homCompat H G (x, u) p

/-- What `homCand` runs.  A placement constrains the candidate only when it holds a *neighbour* of
`x`, and which placements those are is not a question about the candidate: asked once at the node,
each candidate is then only put to the neighbours.  The first of them is the pivot that `homPool`
already reads the pool off, so it is not asked twice.

The gap is widest where the pattern is large and the host is small, which is what a quotient is:
the prefix grows to the size of the pattern while the pool never exceeds the host, so this is one
scan of the prefix per node instead of one per candidate.  `C₄` as a quotient of `tutte` is
2.2× faster for it. -/
def homCandFast (rG : Roster G.V) (x : H.V) (pre : List (H.V × G.V)) : List G.V :=
  match pre.filter fun p ↦ H.Adj x p.1 with
  | [] => rG.toList
  | q :: rest => (rG.toList.filter (G.Adj q.2)).filter fun u ↦ rest.all fun p ↦ G.Adj u p.2

/-- A `List.all` of implications is a `List.all` over what satisfies the hypothesis. -/
private theorem all_imp_eq_all_filter {α : Type} (q r : α → Bool) (l : List α) :
    (l.all fun a ↦ !q a || r a) = (l.filter q).all r := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.filter_cons, ih]
    cases q a <;> simp

@[csimp] theorem homCand_eq_homCandFast : @homCand = @homCandFast := by
  funext H G rG x pre
  have hall : ∀ u : G.V, (pre.all fun p ↦ homCompat H G (x, u) p)
      = (pre.filter fun p ↦ H.Adj x p.1).all fun p ↦ G.Adj u p.2 :=
    fun u ↦ all_imp_eq_all_filter _ _ pre
  rw [homCand, homCandFast, homPool, ← List.head?_filter]
  simp only [hall]
  generalize pre.filter (fun p ↦ H.Adj x p.1) = nbrs
  cases nbrs with
  | nil => simp
  | cons q rest =>
    simp only [List.head?_cons, List.all_cons, List.filter_filter]
    refine List.filter_congr fun u _ ↦ ?_
    rw [G.symm q.2 u]
    cases G.Adj u q.2 <;> simp

/-- Does the assignment hit every vertex of `G`?  Only ever asked of a finished one. -/
def coversHost (rG : Roster G.V) (r : List (H.V × G.V)) : Bool :=
  rG.toList.all fun v ↦ r.any fun p ↦ decide (p.2 = v)

/-- What a finished assignment has to satisfy: consistency always, and surjectivity as well when
the caller is looking for a quotient. -/
def goalHom (surj : Bool) (rG : Roster G.V) (r : List (H.V × G.V)) : Bool :=
  validHom H G r && (!surj || coversHost H G rG r)

/-- **The one thing the pruning has to satisfy**: a value that occurs in a solution is offered. -/
theorem mem_homCand {surj : Bool} {rG : Roster G.V} {x : H.V} {u : G.V}
    {pre l : List (H.V × G.V)} (h : goalHom H G surj rG (l ++ (x, u) :: pre) = true) :
    u ∈ homCand H G rG x pre := by
  rw [goalHom, Bool.and_eq_true] at h
  have hall : ∀ p ∈ pre, homCompat H G (x, u) p = true :=
    (List.pairwise_cons.mp (List.pairwise_append.mp ((validHom_iff H G _).mp h.1)).2.1).1
  exact List.mem_filter.mpr ⟨mem_homPool H G hall, by simpa using hall⟩

/-- The assignment the search finds, before it is turned into a witness. -/
def searchHom (surj : Bool) (rH : Roster H.V) (rG : Roster G.V) : Option (List (H.V × G.V)) :=
  Backtrack.dfs (homCand H G rG) (goalHom H G surj rG) (searchOrder H rH.toList) []

theorem searchHom_goal {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {r : List (H.V × G.V)} (h : searchHom H G surj rH rG = some r) :
    goalHom H G surj rG r = true :=
  Backtrack.goal_of_dfs_eq_some h

theorem searchHom_keys {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {r : List (H.V × G.V)} (h : searchHom H G surj rH rG = some r) :
    r.map Prod.fst = (searchOrder H rH.toList).reverse := by
  rw [Backtrack.keys_of_dfs_eq_some h, List.map_nil, List.append_nil]

theorem searchHom_cov {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {r : List (H.V × G.V)} (h : searchHom H G surj rH rG = some r) (x : H.V) :
    x ∈ r.map Prod.fst := by
  rw [searchHom_keys H G h, List.mem_reverse]
  exact mem_searchOrder H rH.mem_toList x

theorem searchHom_nodup {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {r : List (H.V × G.V)} (h : searchHom H G surj rH rG = some r) :
    (r.map Prod.fst).Nodup := by
  rw [searchHom_keys H G h, List.nodup_reverse]
  exact searchOrder_nodup H rH.toList

/-- **Completeness of the search**: a map that satisfies the goal contradicts an empty search. -/
theorem searchHom_eq_none {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    (h : searchHom H G surj rH rG = none) (f : H.V → G.V)
    (hgoal : goalHom H G surj rG (((searchOrder H rH.toList).map fun x ↦ (x, f x)).reverse)
      = true) : False := by
  have hsol : ((searchOrder H rH.toList).map fun x ↦ (x, f x)).map Prod.fst
      = searchOrder H rH.toList := by simp [Function.comp_def]
  have hn := Backtrack.dfs_eq_none (fun _ _ _ _ hg ↦ mem_homCand H G hg) h hsol
  rw [List.append_nil] at hn
  rw [hn] at hgoal
  exact absurd hgoal (by simp)

/-! ## Homomorphisms -/

/-- **Is there a homomorphism `H → G`?**  Returns one if so.  See `CGraph.isEmpty_hom_iff` for the
other half of the answer. -/
def findHom (rH : Roster H.V) (rG : Roster G.V) : Option (H →cg G) :=
  Option.pmap (p := fun r ↦ (∀ x : H.V, x ∈ r.map Prod.fst) ∧ validHom H G r = true)
    (fun r hr ↦ homOfAsg H G r hr.1 hr.2) (searchHom H G false rH rG)
    (fun _ hr ↦ ⟨searchHom_cov H G hr, by
      have hg := searchHom_goal H G hr
      rw [goalHom, Bool.and_eq_true] at hg
      exact hg.1⟩)

theorem findHom_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findHom H G rH rG = none ↔ searchHom H G false rH rG = none :=
  Option.pmap_eq_none_iff

/-- **Completeness**: when the search comes back empty, there is no homomorphism at all. -/
theorem isEmpty_hom_of_findHom_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findHom H G rH rG = none) : IsEmpty (H →cg G) := by
  rw [findHom_eq_none_iff] at h
  refine ⟨fun f ↦ searchHom_eq_none H G h f ?_⟩
  rw [goalHom, Bool.and_eq_true]
  refine ⟨?_, by simp⟩
  rw [← List.map_reverse]
  exact validHom_of_hom H G f _

/-- There is a homomorphism `H → G` exactly when the search finds one. -/
theorem isEmpty_hom_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H →cg G) ↔ findHom H G rH rG = none := by
  refine ⟨fun hE ↦ ?_, isEmpty_hom_of_findHom_eq_none H G⟩
  rcases hm : findHom H G rH rG with _ | f
  · rfl
  · exact (hE.false f).elim

/-! ## Quotients

The map runs the other way, so the roles of the two graphs swap: the search assigns a vertex of
`H` to every vertex of `G`, and the extra condition is that it uses all of them. -/

theorem surjective_asgFun {r : List (G.V × H.V)} {hcov : ∀ v : G.V, v ∈ r.map Prod.fst}
    (hnd : (r.map Prod.fst).Nodup) (rH : Roster H.V) (h : coversHost G H rH r = true) :
    Function.Surjective (asgFun G H r hcov) := by
  intro x
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp (List.all_eq_true.mp h x (rH.mem_toList x))
  exact ⟨p.1, (asgFun_eq_of_mem G H hnd hp).trans (of_decide_eq_true hpx)⟩

/-- **The quotient a complete, consistent, surjective assignment describes.** -/
def quotientOfAsg (r : List (G.V × H.V)) (hcov : ∀ v : G.V, v ∈ r.map Prod.fst)
    (hnd : (r.map Prod.fst).Nodup) (rH : Roster H.V) (hv : validHom G H r = true)
    (hs : coversHost G H rH r = true) : H.QuotientOf G where
  toFun := asgFun G H r hcov
  surjective' := surjective_asgFun H G hnd rH hs
  map_adj' _ _ h := (homOfAsg G H r hcov hv).map_rel h

/-- **Is `H` a quotient of `G`?**  Returns a witness if so.  See `CGraph.isEmpty_quotientOf_iff`
for the other half of the answer. -/
def findQuotient (rH : Roster H.V) (rG : Roster G.V) : Option (H.QuotientOf G) :=
  Option.pmap (p := fun r ↦ ((∀ v : G.V, v ∈ r.map Prod.fst) ∧ (r.map Prod.fst).Nodup) ∧
      (validHom G H r = true ∧ coversHost G H rH r = true))
    (fun r hr ↦ quotientOfAsg H G r hr.1.1 hr.1.2 rH hr.2.1 hr.2.2)
    (searchHom G H true rG rH)
    (fun _ hr ↦ by
      have hg := searchHom_goal G H hr
      rw [goalHom, Bool.and_eq_true] at hg
      exact ⟨⟨searchHom_cov G H hr, searchHom_nodup G H hr⟩, hg.1, by simpa using hg.2⟩)

theorem findQuotient_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findQuotient H G rH rG = none ↔ searchHom G H true rG rH = none :=
  Option.pmap_eq_none_iff

/-- **Completeness**: when the search comes back empty, `H` is not a quotient of `G`. -/
theorem isEmpty_quotientOf_of_findQuotient_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findQuotient H G rH rG = none) : IsEmpty (H.QuotientOf G) := by
  rw [findQuotient_eq_none_iff] at h
  refine ⟨fun f ↦ searchHom_eq_none G H h f ?_⟩
  rw [goalHom, Bool.and_eq_true]
  refine ⟨by rw [← List.map_reverse]; exact validHom_of_hom G H f.toHom _, ?_⟩
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  right
  rw [coversHost, List.all_eq_true]
  intro x _
  obtain ⟨v, hv⟩ := f.surjective x
  refine List.any_eq_true.mpr ⟨(v, f v), ?_, by simpa using hv⟩
  rw [List.mem_reverse]
  exact List.mem_map_of_mem (mem_searchOrder G rG.mem_toList v)

/-- `H` is a quotient of `G` exactly when the search finds one. -/
theorem isEmpty_quotientOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.QuotientOf G) ↔ findQuotient H G rH rG = none := by
  refine ⟨fun hE ↦ ?_, isEmpty_quotientOf_of_findQuotient_eq_none H G⟩
  rcases hm : findQuotient H G rH rG with _ | f
  · rfl
  · exact (hE.false f).elim

end CGraph
