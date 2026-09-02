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
* **The host's symmetry.**  An automorphism of `G` carries a homomorphism to another one, so the
  maps come in orbits and only one member of each is worth looking for.  `CGraph.homCandSym` keeps
  the lexicographically least, at a machine word per automorphism per node; `## Breaking the host's
  symmetries` below is what it does and why it is allowed to.  The automorphisms are an argument,
  since only the caller knows what they cost to come by.

Deciding either relation is NP-hard — `H →cg Kₖ` is `k`-colourability of `H` — so there is no
better shape available.  The hard instances are a sparse pattern against a host with little
structure for the pivot to bite on, `Kₖ` being the extreme case.

## Colouring

`H →cg complete k` *is* a proper `k`-colouring of `H`, so `CGraph.findHom H (complete k)` decides
`k`-colourability and hands back the colouring.  `Aut Kₖ` is the whole of `Sₖ`, so the symmetry
breaking above is exactly the classical rule that the colours must be used in order.

## What it costs

`testing/CacheBench.lean`, cases `api-hom`, `api-quot`, `sym-hom` and `sym-quot`; best of three
interleaved rounds, in milliseconds.  `CGraph.findHom` is the search on the graphs as they are and
with no automorphisms supplied; `CGraph.homOf?` and `CGraph.quotientOf?`, in
`Algorithms/Cached.lean`, are the same search on tabulated copies of both, with the host's
automorphisms computed, and are what to reach for:

| job                        | `find…` | cached | cached, no symmetry |
| -------------------------- | ------- | ------ | ------------------- |
| `C₄` a quotient of `tutte` | 868     | 19     | 72                  |
| `tutte → K₃`               | 29      | 2      | 2                   |
| `mcgee → K₂`               | 3       | <1     | <1                  |
| `grotzsch → K₄`            | 1       | <1     | <1                  |
| `petersen → K₃`            | <1      | <1     | <1                  |

The quotient is a whole order of magnitude past the rest, and its answer is `none` — the search
closed the entire tree, which is the honest cost of the relation.  It is also the shape the pivot
handles worst: 46 vertices of pattern against 4 of host, so the pool is never smaller than a
quarter of `G` and the pruning has to come from the prefix instead.  What is left is symmetry:
`C₄` has eight automorphisms and the tree shrinks by exactly eight, from 131069 nodes to 16385
(`cachebench nodes-quot 1 4` and `nodes-quot 1 4 sym`).

`mcgee → K₂` is the other `none` and costs nothing, because an odd cycle refuses two colours a few
steps in.  The successes are cheap in proportion to the freedom the host leaves: `petersen → K₃`
commits on the first descent, `tutte → K₃` backtracks a while first — and neither is measurably
changed by the symmetry breaking, because a search that succeeds pays for the orbits it skips only
in the branches it would have taken anyway.
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

/-! ## Breaking the host's symmetries

An automorphism of the host carries a homomorphism to another one, so the maps come in orbits under
`Aut G` and the search need only look at one member of each.  The cheap member to recognise is the
*lexicographically least*: read the images in the order the search places them and compare their
ranks in the roster.

The condition that picks it out is local.  Let `γ` be an automorphism fixing, pointwise, every
image placed so far.  Then `γ` sends the part of the assignment already made to itself, so the
first place the assignment and its image under `γ` can differ is the vertex being placed now, and
being least asks exactly that its image `u` have `rank u ≤ rank (γ u)`.  An automorphism that
*moves* an image already placed was decided against higher up — what is placed is already strictly
smaller than its image — and constrains nothing below it.

So a node intersects, over the automorphisms that still fix everything placed, the vertices they do
not send to an earlier rank.  Both halves are a machine word: which automorphisms are still active
is one `&&&` each against the mask of the images used, and what they leave is an `&&&` of masks
over ranks, tested against the candidate's own bit.  `CGraph.mask` and its lemmas are
`Algorithms/Embedding.lean`'s.

Nothing here computes `Aut G`.  The caller hands over whatever automorphisms of the host it has,
and the search is correct for any list of them — a longer list prunes more and costs more per node,
and `CGraph.autData G rG []` is the search as it was, at a `List.isEmpty` per node.  What
`CGraph.homOf?` and `CGraph.quotientOf?` in `Algorithms/Cached.lean` pass is the group generated by
what the canonical labelling search turns up, when the host is small enough for that to be worth
running. -/

/-- Does `γ` fix every one of `vs`? -/
def autFixes (γ : G ≃cg G) (vs : List G.V) : Bool := vs.all fun v ↦ decide (γ v = v)

/-- **The candidates the host's symmetries leave**, given the images `vs` already placed: those
that no automorphism still fixing all of `vs` sends to an earlier rank in `gs`. -/
def autAllows (gs : List G.V) (auts : List (G ≃cg G)) (vs : List G.V) (u : G.V) : Bool :=
  auts.all fun γ ↦ !autFixes G γ vs || decide (gs.idxOf u ≤ gs.idxOf (γ u))

/-- `CGraph.autAllows` at every step of a finished assignment, for one automorphism.  Read in
search order — which is `vs` backwards, since an assignment is built up head first — this says the
sequence of ranks is at or below its image under `γ`. -/
def autLexOne (gs : List G.V) (γ : G ≃cg G) : List G.V → Bool
  | [] => true
  | v :: rest =>
    (!autFixes G γ rest || decide (gs.idxOf v ≤ gs.idxOf (γ v))) && autLexOne gs γ rest

/-- **What makes an assignment the one of its orbit the search keeps.** -/
def autLex (gs : List G.V) (auts : List (G ≃cg G)) (vs : List G.V) : Bool :=
  auts.all fun γ ↦ autLexOne G gs γ vs

/-- The condition at one step is a conjunct of the condition on the whole, for one automorphism. -/
theorem autAllows_of_autLexOne {gs : List G.V} {γ : G ≃cg G} {l : List G.V} {u : G.V}
    {rest : List G.V} (h : autLexOne G gs γ (l ++ u :: rest) = true) :
    (!autFixes G γ rest || decide (gs.idxOf u ≤ gs.idxOf (γ u))) = true := by
  induction l with
  | nil => rw [List.nil_append, autLexOne, Bool.and_eq_true] at h; exact h.1
  | cons a l ih => rw [List.cons_append, autLexOne, Bool.and_eq_true] at h; exact ih h.2

/-- The condition at one step is a conjunct of the condition on the whole. -/
theorem autAllows_of_autLex {gs : List G.V} {auts : List (G ≃cg G)} {l : List G.V} {u : G.V}
    {rest : List G.V} (h : autLex G gs auts (l ++ u :: rest) = true) :
    autAllows G gs auts rest u = true := by
  rw [autAllows, List.all_eq_true]
  exact fun γ hγ ↦ autAllows_of_autLexOne G (List.all_eq_true.mp h γ hγ)

/-! ### That there is always a least one

The rank sequence of an assignment, read as a number in base `gs.length`, turns the lexicographic
comparison into `≤` on `ℕ`, and a nonempty finite set of numbers has a least element.  The finite
set is the orbit of a homomorphism under the adjacency-preserving permutations of `G`, which is
closed under composing with anything the caller could have passed. -/

/-- The ranks of `vs`, as a number in base `gs.length`, the head least significant. -/
def rankCode (gs : List G.V) : List G.V → ℕ
  | [] => 0
  | v :: rest => gs.idxOf v + gs.length * rankCode gs rest

theorem rankCode_map_of_autFixes {gs : List G.V} {γ : G ≃cg G} {vs : List G.V}
    (h : autFixes G γ vs = true) : rankCode G gs (vs.map γ) = rankCode G gs vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
    rw [autFixes, List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, rankCode, rankCode, of_decide_eq_true h.1, ih h.2]

/-- **Failing the condition means the image under `γ` is strictly smaller.**  This is the whole of
the symmetry argument: the least code satisfies the condition, because anything that does not has
something below it. -/
theorem rankCode_lt_of_not_autLexOne {gs : List G.V} (hgs : ∀ v, v ∈ gs) {γ : G ≃cg G}
    {vs : List G.V} (h : autLexOne G gs γ vs = false) :
    rankCode G gs (vs.map γ) < rankCode G gs vs := by
  induction vs with
  | nil => rw [autLexOne] at h; exact absurd h (by simp)
  | cons v rest ih =>
    rw [autLexOne, Bool.and_eq_false_iff] at h
    rw [List.map_cons, rankCode, rankCode]
    rcases h with h | h
    · rw [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, not_le] at h
      rw [rankCode_map_of_autFixes G h.1]
      exact Nat.add_lt_add_right h.2 _
    · have hlt := ih h
      have hv : gs.idxOf (γ v) < gs.length := List.idxOf_lt_length_of_mem (hgs _)
      have hmul : gs.length * (rankCode G gs (rest.map γ) + 1) ≤ gs.length * rankCode G gs rest :=
        Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega

/-- **A homomorphism can be taken least in its orbit.**  Composing with an adjacency-preserving
permutation of the host gives another map of the same kind, and of the finitely many the least code
is the one the pruning leaves in the tree. -/
theorem exists_autLex (gs : List G.V) (hgs : ∀ v, v ∈ gs) (auts : List (G ≃cg G))
    (vs : List G.V) :
    ∃ φ : Equiv.Perm G.V, (∀ a b : G.V, G.Adj a b = true → G.Adj (φ a) (φ b) = true) ∧
      autLex G gs auts (vs.map φ) = true := by
  classical
  set A : Finset (Equiv.Perm G.V) :=
    Finset.univ.filter fun φ ↦ ∀ a b : G.V, G.Adj a b = true → G.Adj (φ a) (φ b) = true with hAdef
  have hA : A.Nonempty := ⟨1, by simp [hAdef]⟩
  obtain ⟨φ, hφ, hmin⟩ := A.exists_min_image (fun φ ↦ rankCode G gs (vs.map φ)) hA
  rw [hAdef, Finset.mem_filter] at hφ
  refine ⟨φ, hφ.2, ?_⟩
  rw [autLex, List.all_eq_true]
  intro γ hγ
  by_contra hne
  rw [Bool.not_eq_true] at hne
  have hmem : φ.trans γ.toEquiv ∈ A := by
    rw [hAdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun a b hab ↦ by
      rw [Equiv.trans_apply, Equiv.trans_apply]
      exact (γ.adj_eq _ _).trans (hφ.2 a b hab)⟩
  have hmap : vs.map (φ.trans γ.toEquiv) = (vs.map φ).map γ := by
    rw [List.map_map]; rfl
  have := hmin _ hmem
  rw [hmap] at this
  exact absurd this (by simpa using rankCode_lt_of_not_autLexOne G hgs hne)

/-! ### The tables the test reads -/

/-- What the automorphism test needs at a node, computed once before the search: for each
automorphism, the ranks it moves and the ranks it does not lower; and each vertex's own bit.

The fields are words and the proof beside each one names the list of vertices it is the
`CGraph.mask` of, which is what every lemma below reads.  `1 <<< rank` is stored rather than
shifted for the reason `CGraph.Row.bit` is: `Nat.shiftLeft` goes through GMP whatever it is
given. -/
structure AutData (G : CGraph) (gs : List G.V) where
  /-- The automorphisms themselves. -/
  auts : List (G ≃cg G)
  /-- Each vertex's bit, `1 <<< rank`. -/
  bit : G.V → ℕ
  /-- For each automorphism: the ranks it moves, and the ranks it does not lower. -/
  pairs : List (ℕ × ℕ)
  /-- Every rank. -/
  full : ℕ
  /-- The bits are the bits. -/
  bit_eq : bit = fun v ↦ 1 <<< gs.idxOf v
  /-- The masks are the masks. -/
  pairs_eq : pairs = auts.map fun γ ↦
    (mask G gs (gs.filter fun v ↦ !decide (γ v = v)),
      mask G gs (gs.filter fun v ↦ decide (gs.idxOf v ≤ gs.idxOf (γ v))))
  /-- The full mask is full. -/
  full_eq : full = mask G gs gs

/-- **The tables of a list of automorphisms.**  `CGraph.autData G rG []` is the search without
symmetry breaking. -/
def autData (rG : Roster G.V) (auts : List (G ≃cg G)) : AutData G rG.toList where
  auts := auts
  bit := tabAt (tabulate fun v ↦ 1 <<< rG.toList.idxOf v)
  pairs := auts.map fun γ ↦
    (mask G rG.toList (rG.toList.filter fun v ↦ !decide (γ v = v)),
      mask G rG.toList (rG.toList.filter fun v ↦
        decide (rG.toList.idxOf v ≤ rG.toList.idxOf (γ v))))
  full := mask G rG.toList rG.toList
  bit_eq := tabAt_tabulate _
  pairs_eq := rfl
  full_eq := rfl

/-! ### Closing a generating set

Nothing below has to be proved, since the pruning is correct for whatever list it is given.  It is
here because generators alone prune weakly: the two that generate the eight symmetries of `C₄` cut
the root of the `C₄`-quotient search from four candidates to three, where the group itself cuts it
to one.  So a caller with generators closes them, deduplicating by the action on the roster and
stopping at `cap` elements — a subset of `Aut G` prunes less and stays correct. -/

private def autAddTo (rG : Roster G.V) (cap : ℕ) (st : List (List ℕ) × List (G ≃cg G))
    (γ : G ≃cg G) : List (List ℕ) × List (G ≃cg G) :=
  if st.2.length ≥ cap then st
  else
    let k := rG.toList.map fun v ↦ rG.toList.idxOf (γ v)
    if st.1.contains k then st else (k :: st.1, γ :: st.2)

private def autRound (rG : Roster G.V) (gens : List (G ≃cg G)) (cap : ℕ) :
    ℕ → List (List ℕ) × List (G ≃cg G) → List (List ℕ) × List (G ≃cg G)
  | 0, st => st
  | fuel + 1, st =>
    let st' := st.2.foldl (fun s γ ↦ gens.foldl (fun s δ ↦ autAddTo G rG cap s (γ.trans δ)) s) st
    if st'.2.length == st.2.length then st' else autRound rG gens cap fuel st'

/-- **The group a generating set generates**, or `cap` elements of it, without the identity — which
is in every such group and constrains nothing. -/
def autClosure (rG : Roster G.V) (gens : List (G ≃cg G)) (cap : ℕ) : List (G ≃cg G) :=
  (autRound G rG gens cap cap (autAddTo G rG cap ([], []) (RelIso.refl _))).2.filter
    fun γ ↦ !autFixes G γ rG.toList

/-- The candidates for `x`, with the host's symmetries broken. -/
def homCandSym (rG : Roster G.V) (ad : AutData G rG.toList) (x : H.V)
    (pre : List (H.V × G.V)) : List G.V :=
  (homCand H G rG x pre).filter (autAllows G rG.toList ad.auts (pre.map Prod.snd))

/-- What `homCandSym` runs.  The images already placed go into one word at the node; an
automorphism is still active when that word misses everything it moves, and what the active ones
allow is the `&&&` of their masks, which the candidate meets with its own bit.  So the whole test
is one pass over the assignment and a word per automorphism per node, in place of a pass over the
assignment per automorphism per candidate. -/
def homCandSymFast (rG : Roster G.V) (ad : AutData G rG.toList) (x : H.V)
    (pre : List (H.V × G.V)) : List G.V :=
  let cs := homCand H G rG x pre
  if ad.pairs.isEmpty then cs
  else
    let used : ℕ := pre.foldl (fun m q ↦ m ||| ad.bit q.2) 0
    let allow : ℕ := ad.pairs.foldl (fun m p ↦ if p.1 &&& used == 0 then m &&& p.2 else m) ad.full
    cs.filter fun u ↦ allow &&& ad.bit u != 0

/-- A `Nat` and a single bit share a bit exactly where the bit is. -/
private theorem and_shiftLeft_bne_zero (n k : ℕ) : (n &&& 1 <<< k != 0) = n.testBit k := by
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, ← ne_eq, and_ne_zero_iff_exists_testBit]
  refine ⟨fun ⟨j, hj, hjk⟩ ↦ ?_, fun h ↦ ⟨k, h, by simp [Nat.shiftLeft_eq]⟩⟩
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at hjk
  have hkj : k = j := of_decide_eq_true hjk
  subst hkj
  exact hj

/-- The mask the active automorphisms leave, bit by bit. -/
private theorem testBit_allow_foldl {gs : List G.V} (hgs : ∀ v, v ∈ gs) (vs : List G.V)
    (u : G.V) (auts : List (G ≃cg G)) (m : ℕ) :
    (((auts.map fun γ ↦
        (mask G gs (gs.filter fun v ↦ !decide (γ v = v)),
          mask G gs (gs.filter fun v ↦ decide (gs.idxOf v ≤ gs.idxOf (γ v))))).foldl
      (fun m p ↦ if p.1 &&& mask G gs vs == 0 then m &&& p.2 else m) m)).testBit (gs.idxOf u)
      = (m.testBit (gs.idxOf u) && autAllows G gs auts vs u) := by
  induction auts generalizing m with
  | nil => simp [autAllows]
  | cons γ auts ih =>
    have hact : (mask G gs (gs.filter fun v ↦ !decide (γ v = v)) &&& mask G gs vs == 0)
        = autFixes G γ vs := by
      rw [Bool.eq_iff_iff, beq_iff_eq, and_mask_eq_zero_iff hgs, autFixes, List.all_eq_true]
      constructor
      · intro h v hv
        by_contra hvv
        exact h v (List.mem_filter.mpr ⟨hgs v, by simpa using hvv⟩) hv
      · intro h w hw hv
        rw [List.mem_filter] at hw
        exact absurd (of_decide_eq_true (h w hv)) (by simpa using hw.2)
    have hok : (mask G gs (gs.filter fun v ↦ decide (gs.idxOf v ≤ gs.idxOf (γ v)))).testBit
        (gs.idxOf u) = decide (gs.idxOf u ≤ gs.idxOf (γ u)) := by
      rw [testBit_mask_eq_decide_mem hgs, Bool.eq_iff_iff, decide_eq_true_eq,
        decide_eq_true_eq, List.mem_filter]
      exact ⟨fun h ↦ of_decide_eq_true h.2, fun h ↦ ⟨hgs u, by simpa using h⟩⟩
    rw [List.map_cons, List.foldl_cons, ih]
    simp only [autAllows, List.all_cons]
    cases hf : autFixes G γ vs
    · simp only [hact, hf, Bool.false_eq_true, ite_eq_right, Bool.not_false, Bool.true_or,
        Bool.true_and, not_false_iff]
    · simp only [hact, hf, ite_eq_left, Nat.testBit_and, hok, Bool.not_true, Bool.false_or,
        Bool.and_assoc]

@[csimp] theorem homCandSym_eq_homCandSymFast : @homCandSym = @homCandSymFast := by
  funext H G rG ad x pre
  have hgs : ∀ v, v ∈ rG.toList := rG.mem_toList
  have hsub : ∀ u ∈ homCand H G rG x pre, u ∈ rG.toList := fun u _ ↦ hgs u
  rw [homCandSym, homCandSymFast]
  have hused : pre.foldl (fun m q ↦ m ||| ad.bit q.2) 0
      = mask G rG.toList (pre.map Prod.snd) := by
    rw [mask, ad.bit_eq, List.foldl_map]
  have hall : ∀ u ∈ homCand H G rG x pre,
      (ad.pairs.foldl (fun m p ↦ if p.1 &&& (pre.foldl (fun m q ↦ m ||| ad.bit q.2) 0) == 0
          then m &&& p.2 else m) ad.full &&& ad.bit u != 0)
        = autAllows G rG.toList ad.auts (pre.map Prod.snd) u := by
    intro u _
    rw [hused, ad.pairs_eq, ad.bit_eq, and_shiftLeft_bne_zero,
      testBit_allow_foldl G hgs, ad.full_eq, testBit_mask_of_mem (hgs u), Bool.true_and]
  simp only
  split
  · rename_i hp
    rw [List.isEmpty_iff] at hp
    rw [ad.pairs_eq, List.map_eq_nil_iff] at hp
    rw [hp]
    simp [autAllows]
  · exact (List.filter_congr hall).symm

/-- Does the assignment hit every vertex of `G`?  Only ever asked of a finished one. -/
def coversHost (rG : Roster G.V) (r : List (H.V × G.V)) : Bool :=
  rG.toList.all fun v ↦ r.any fun p ↦ decide (p.2 = v)

/-- What a finished assignment has to satisfy: consistency always, and surjectivity as well when
the caller is looking for a quotient. -/
def goalHom (surj : Bool) (rG : Roster G.V) (r : List (H.V × G.V)) : Bool :=
  validHom H G r && (!surj || coversHost H G rG r)

/-- `CGraph.goalHom`, and the assignment is the one of its orbit the pruning leaves. -/
def goalHomSym (surj : Bool) (rG : Roster G.V) (ad : AutData G rG.toList)
    (r : List (H.V × G.V)) : Bool :=
  goalHom H G surj rG r && autLex G rG.toList ad.auts (r.map Prod.snd)

/-- **The one thing the pruning has to satisfy**: a value that occurs in a solution is offered. -/
theorem mem_homCandSym {surj : Bool} {rG : Roster G.V} {ad : AutData G rG.toList} {x : H.V}
    {u : G.V} {pre l : List (H.V × G.V)}
    (h : goalHomSym H G surj rG ad (l ++ (x, u) :: pre) = true) :
    u ∈ homCandSym H G rG ad x pre := by
  rw [goalHomSym, Bool.and_eq_true, goalHom, Bool.and_eq_true] at h
  have hall : ∀ p ∈ pre, homCompat H G (x, u) p = true :=
    (List.pairwise_cons.mp (List.pairwise_append.mp ((validHom_iff H G _).mp h.1.1)).2.1).1
  refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨mem_homPool H G hall, by simpa using hall⟩, ?_⟩
  refine autAllows_of_autLex G (l := l.map Prod.snd) ?_
  simpa using h.2

/-- The assignment the search finds, before it is turned into a witness. -/
def searchHom (surj : Bool) (rH : Roster H.V) (rG : Roster G.V) (ad : AutData G rG.toList) :
    Option (List (H.V × G.V)) :=
  Backtrack.dfs (homCandSym H G rG ad) (goalHomSym H G surj rG ad) (searchOrder H rH.toList) []

variable {H G}

theorem searchHom_goal {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData G rG.toList} {r : List (H.V × G.V)} (h : searchHom H G surj rH rG ad = some r) :
    goalHom H G surj rG r = true :=
  (Bool.and_eq_true _ _ ▸ Backtrack.goal_of_dfs_eq_some h).1

theorem searchHom_keys {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData G rG.toList} {r : List (H.V × G.V)} (h : searchHom H G surj rH rG ad = some r) :
    r.map Prod.fst = (searchOrder H rH.toList).reverse := by
  rw [Backtrack.keys_of_dfs_eq_some h, List.map_nil, List.append_nil]

theorem searchHom_cov {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData G rG.toList} {r : List (H.V × G.V)} (h : searchHom H G surj rH rG ad = some r)
    (x : H.V) : x ∈ r.map Prod.fst := by
  rw [searchHom_keys h, List.mem_reverse]
  exact mem_searchOrder H rH.mem_toList x

theorem searchHom_nodup {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData G rG.toList} {r : List (H.V × G.V)} (h : searchHom H G surj rH rG ad = some r) :
    (r.map Prod.fst).Nodup := by
  rw [searchHom_keys h, List.nodup_reverse]
  exact searchOrder_nodup H rH.toList

variable (H G)

/-- **Completeness of the search**: a map that satisfies the goal contradicts an empty search.

The goal is asked of every relabelling of the map by a symmetry of the host, because that is what
the search is entitled to assume: it keeps one member of each orbit, so all the caller learns from
an empty search is that no orbit has a member satisfying the goal — and a symmetry carries any map
to another one, which is why the callers below can meet this. -/
theorem searchHom_eq_none {surj : Bool} {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData G rG.toList} (h : searchHom H G surj rH rG ad = none) (f : H.V → G.V)
    (hgoal : ∀ φ : Equiv.Perm G.V, (∀ a b : G.V, G.Adj a b = true → G.Adj (φ a) (φ b) = true) →
      goalHom H G surj rG (((searchOrder H rH.toList).map fun x ↦ (x, φ (f x))).reverse) = true) :
    False := by
  obtain ⟨φ, hφ, hlex⟩ := exists_autLex G rG.toList rG.mem_toList ad.auts
    (((searchOrder H rH.toList).map f).reverse)
  have hsol : ((searchOrder H rH.toList).map fun x ↦ (x, φ (f x))).map Prod.fst
      = searchOrder H rH.toList := by simp [Function.comp_def]
  have hn := Backtrack.dfs_eq_none (fun _ _ _ _ hg ↦ mem_homCandSym H G hg) h hsol
  rw [List.append_nil] at hn
  have hg : goalHomSym H G surj rG ad
      (((searchOrder H rH.toList).map fun x ↦ (x, φ (f x))).reverse) = true := by
    rw [goalHomSym, Bool.and_eq_true]
    refine ⟨hgoal φ hφ, ?_⟩
    have hmap : (((searchOrder H rH.toList).map fun x ↦ (x, φ (f x))).reverse).map Prod.snd
        = (((searchOrder H rH.toList).map f).reverse).map φ := by simp [Function.comp_def]
    rw [hmap]
    exact hlex
  rw [hn] at hg
  exact absurd hg (by simp)

/-! ## Homomorphisms -/

/-- **Is there a homomorphism `H → G`?**  Returns one if so.  See `CGraph.isEmpty_hom_iff` for the
other half of the answer.  `ad` is the host symmetry the search may break; `CGraph.autData G rG []`
breaks none. -/
def findHom (rH : Roster H.V) (rG : Roster G.V) (ad : AutData G rG.toList) : Option (H →cg G) :=
  Option.pmap (p := fun r ↦ (∀ x : H.V, x ∈ r.map Prod.fst) ∧ validHom H G r = true)
    (fun r hr ↦ homOfAsg H G r hr.1 hr.2) (searchHom H G false rH rG ad)
    (fun _ hr ↦ ⟨searchHom_cov hr, by
      have hg := searchHom_goal hr
      rw [goalHom, Bool.and_eq_true] at hg
      exact hg.1⟩)

theorem findHom_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) (ad : AutData G rG.toList) :
    findHom H G rH rG ad = none ↔ searchHom H G false rH rG ad = none :=
  Option.pmap_eq_none_iff

/-- **Completeness**: when the search comes back empty, there is no homomorphism at all. -/
theorem isEmpty_hom_of_findHom_eq_none {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData G rG.toList} (h : findHom H G rH rG ad = none) : IsEmpty (H →cg G) := by
  rw [findHom_eq_none_iff] at h
  refine ⟨fun f ↦ searchHom_eq_none H G h f fun φ hφ ↦ ?_⟩
  rw [goalHom, Bool.and_eq_true]
  refine ⟨?_, by simp⟩
  rw [← List.map_reverse]
  exact validHom_of_hom H G ⟨fun x ↦ φ (f x), fun h ↦ hφ _ _ (f.map_rel h)⟩ _

/-- There is a homomorphism `H → G` exactly when the search finds one. -/
theorem isEmpty_hom_iff (rH : Roster H.V) (rG : Roster G.V) (ad : AutData G rG.toList) :
    IsEmpty (H →cg G) ↔ findHom H G rH rG ad = none := by
  refine ⟨fun hE ↦ ?_, isEmpty_hom_of_findHom_eq_none H G⟩
  rcases hm : findHom H G rH rG ad with _ | f
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
for the other half of the answer.

The host of this search is the *small* graph `H`, so `ad` is its symmetry — which is the case worth
breaking, since `H` being small is what makes its automorphism group cheap to have. -/
def findQuotient (rH : Roster H.V) (rG : Roster G.V) (ad : AutData H rH.toList) :
    Option (H.QuotientOf G) :=
  Option.pmap (p := fun r ↦ ((∀ v : G.V, v ∈ r.map Prod.fst) ∧ (r.map Prod.fst).Nodup) ∧
      (validHom G H r = true ∧ coversHost G H rH r = true))
    (fun r hr ↦ quotientOfAsg H G r hr.1.1 hr.1.2 rH hr.2.1 hr.2.2)
    (searchHom G H true rG rH ad)
    (fun _ hr ↦ by
      have hg := searchHom_goal hr
      rw [goalHom, Bool.and_eq_true] at hg
      exact ⟨⟨searchHom_cov hr, searchHom_nodup hr⟩, hg.1, by simpa using hg.2⟩)

theorem findQuotient_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) (ad : AutData H rH.toList) :
    findQuotient H G rH rG ad = none ↔ searchHom G H true rG rH ad = none :=
  Option.pmap_eq_none_iff

/-- **Completeness**: when the search comes back empty, `H` is not a quotient of `G`. -/
theorem isEmpty_quotientOf_of_findQuotient_eq_none {rH : Roster H.V} {rG : Roster G.V}
    {ad : AutData H rH.toList} (h : findQuotient H G rH rG ad = none) :
    IsEmpty (H.QuotientOf G) := by
  rw [findQuotient_eq_none_iff] at h
  refine ⟨fun f ↦ searchHom_eq_none G H h f fun φ hφ ↦ ?_⟩
  rw [goalHom, Bool.and_eq_true]
  refine ⟨by
    rw [← List.map_reverse]
    exact validHom_of_hom G H ⟨fun v ↦ φ (f v), fun h ↦ hφ _ _ (f.toHom.map_rel h)⟩ _, ?_⟩
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  right
  rw [coversHost, List.all_eq_true]
  intro x _
  obtain ⟨v, hv⟩ := f.surjective (φ.symm x)
  refine List.any_eq_true.mpr ⟨(v, φ (f v)), ?_, by simp [hv]⟩
  rw [List.mem_reverse]
  exact List.mem_map_of_mem (mem_searchOrder G rG.mem_toList v)

/-- `H` is a quotient of `G` exactly when the search finds one. -/
theorem isEmpty_quotientOf_iff (rH : Roster H.V) (rG : Roster G.V) (ad : AutData H rH.toList) :
    IsEmpty (H.QuotientOf G) ↔ findQuotient H G rH rG ad = none := by
  refine ⟨fun hE ↦ ?_, isEmpty_quotientOf_of_findQuotient_eq_none H G⟩
  rcases hm : findQuotient H G rH rG ad with _ | f
  · rfl
  · exact (hE.false f).elim

end CGraph
