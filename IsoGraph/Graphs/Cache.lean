import IsoGraph.Basic

/-!
# Tabulated adjacency

A `CGraph` carries its adjacency as a function, and for most of the gallery that function does
real work on every query: `ofEdges` scans the edge list, `lcf` scans the list its code generates,
a product compares two coordinates, a complement negates a recursive call.  A search that asks
"are these two vertices adjacent?" a few million times pays for all of it a few million times.

Caching fills an `n × n` array of `Bool` once and reads it thereafter, where `n` is
`FinEnum.card G.V` and the array is indexed through `FinEnum.equiv`.  There are two ways to hand
the result back, and both are here because they are not interchangeable:

* `CGraph.cache` keeps the vertex type: `G.cache.V` is `G.V`, and a query maps its two arguments
  through `FinEnum.equiv` before reading the array.  The result is *equal* to `G`
  (`CGraph.cache_eq`), so every fact about `G` — every invariant, every containment, every
  `IsoGraph` class — is a fact about `G.cache` by rewriting, and no interface anywhere has to
  change.  The price is two calls to `FinEnum.equiv` on every query.
* `CGraph.cacheFin` moves to `Fin (FinEnum.card G.V)`, so a query is a bare array read.  The
  price is that the result is only *isomorphic* to `G` (`CGraph.isoCacheFin`), and answers about
  it have to be transported back along that isomorphism.

Which one wins depends entirely on what `FinEnum.equiv` costs for the vertex type; see the table
below.

## Building the table once

The whole point is that the array is filled once and then read, so the shape of the definitions
below is not free to change.  The Lean compiler maximises the arity of a top-level definition: a
`def f (x : α) : β → γ := let a := heavy x; fun b ↦ ⋯` is compiled as a *two*-argument function
with `heavy x` in its body, and then `heavy` runs again on every call.  A definition that means to
share work must therefore not return a function type.  `cacheOfAdj` and `cache` return a `CGraph`,
so the array is built once per call, and the field they store is a partial application —
`matLookup n a` or `matLookupOn α a` — a closure holding the array.  The table itself and its
lookup are `IsoGraph.Canon.adjArray` and `IsoGraph.Canon.matLookup`, which live next to the search
because `CGraph.canonOfArray` tabulates for itself.

That leaves the caller responsible for evaluating `G.cache` once: it is a function call like any
other, and calling it twice fills the array twice.  A top-level `def` (or a `let` outside the
loop) is evaluated once; writing `G.cache` inside the search itself would fill the array at every
node.

## When it pays

Measured by `CacheBench.lean`, best of three interleaved rounds, in milliseconds; the cost of
filling the array is included in every cached figure.  The wins are large wherever the adjacency
function does real work and the search does not finish immediately:

| job                                  | plain  | `cache` | `cacheFin` |
| ------------------------------------ | ------ | ------- | ---------- |
| automorphisms of the Balaban 10-cage | 12160  | 1579    | 1303       |
| `C₄ ⋏ tutte` (contraction)           | 3418   | 526     | 377        |
| automorphisms of the Tutte graph     | 2241   | 529     | 429        |
| automorphisms of `C₄₆`               | 998    | 983     | 747        |
| `mcgee ⋏ mcgee` (both sides cached)  | 376    | 82      | 63         |
| `K₄ ≼ tutte` (minor)                 | 19     | 5       | 4          |
| `petersen ⊆ tutte`                   | 16     | 8       | 6          |
| `C₈ ⊆ tutte`                         | 12     | 6       | 5          |
| canonical form of the Balaban 10-cage | 11    | 13      | 12         |
| canonical form of the Tutte graph    | 6      | 6       | 6          |

The last two rows are the exception that proves the rule, and they used to read 26 | 13 | 13 and
9 | 6 | 6.  `CGraph.canonOfArray` now tabulates for itself — see `IsoGraph/Basic.lean` — so the
plain column already pays for one fill, and caching first only adds a second.

Caching the *pattern* is worth as much as caching the host, and caching both multiplies.  Nothing
measured on a `Fin n` vertex type got materially slower: even a host whose adjacency is a formula
rather than a list — the canonical form of `K₄₀`, 23 ms either way — is a wash, because an array
read beats a `Nat` comparison too.  The only losses are jobs shorter than the `n²` fill itself.
The rule of thumb is that the fill costs one full sweep of the adjacency function, so anything
that would touch every pair more than once is already ahead.

## Which variant

For a vertex type that is already `Fin n` the two are within a few percent of each other, and
`cache` is the one to reach for: it is an equality, so nothing downstream has to know.  For any
other vertex type the two `FinEnum.equiv` calls per query dominate, and `cache` can be *slower*
than no cache at all — on the Kneser graph `K(10,5)`, whose vertices are the 5-element subsets of
`Fin 10`:

| job                | plain | `cache` | `cacheFin` |
| ------------------ | ----- | ------- | ---------- |
| automorphisms of `K(7,3)` | 3302 | 10332 | 460  |
| `C₆ ⊆ K(10,5)`     | 409   | 1576    | 124        |
| canonical form     | 1066  | 1581    | 1131       |
| degree sum         | 65    | 362     | 106        |

The canonical-form row is again one where the plain column already tabulates, so neither variant
has anything left to win.

So: `cache` on `Fin n`, `cacheFin` everywhere else.  (These figures are already with the
memoised subset enumeration of `IsoGraph.ForMathlib.FinEnum`; against Mathlib's instance, whose
`equiv` is a list scan, `cache` on `K(10,5)` costs 4171 ms rather than 362 ms.)
-/

namespace CGraph

open IsoGraph.Canon (adjArray matLookup matLookup_adjArray matLookup_adjArray_eq)

/-! ### Keeping the vertex type -/

/-- Read the entry of an adjacency matrix at a pair of vertices of an enumerated type, indexing
through `FinEnum.equiv`.  Top-level and applied to the array alone, for the reason above. -/
def matLookupOn (α : Type) [FinEnum α] (a : Array (Array Bool)) (x y : α) : Bool :=
  matLookup (FinEnum.card α) a (FinEnum.equiv x) (FinEnum.equiv y)

/-- The matrix of `f`, indexed by `FinEnum.equiv`. -/
def adjArrayOn (α : Type) [FinEnum α] (f : α → α → Bool) : Array (Array Bool) :=
  adjArray (FinEnum.card α) fun i j ↦ f (FinEnum.equiv.symm i) (FinEnum.equiv.symm j)

@[simp] theorem matLookupOn_adjArrayOn {α : Type} [FinEnum α] (f : α → α → Bool) (x y : α) :
    matLookupOn α (adjArrayOn α f) x y = f x y := by
  simp [matLookupOn, adjArrayOn, Equiv.symm_apply_apply]

/-- `G`, with its adjacency matrix precomputed and its vertex type kept.

Every query costs two calls to `FinEnum.equiv`, which for a vertex type whose enumeration is a
list scan is not cheap; `CGraph.cacheFin` is the variant that avoids them. -/
def cache (G : CGraph) : CGraph where
  V := G.V
  enum := G.enum
  Adj := matLookupOn G.V (adjArrayOn G.V G.Adj)
  symm x y := by rw [matLookupOn_adjArrayOn, matLookupOn_adjArrayOn]; exact G.symm x y
  loopless x := by rw [matLookupOn_adjArrayOn]; exact G.loopless x

@[simp] theorem cache_adj (G : CGraph) (x y : G.V) : G.cache.Adj x y = G.Adj x y :=
  matLookupOn_adjArrayOn ..

@[simp] theorem card_cache (G : CGraph) : FinEnum.card G.cache.V = FinEnum.card G.V := rfl

/-- **Caching changes nothing.**  The cached graph is not merely isomorphic to `G`: it is `G`.
Every fact about `G` — every invariant, every containment, every `IsoGraph` class — is a fact
about `G.cache` by rewriting along this. -/
theorem cache_eq (G : CGraph) : G.cache = G :=
  CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ G.cache_adj x y))

/-! ### Moving to `Fin n` -/

/-- The graph on `Fin n` with adjacency `adj`, tabulated: `adj` is called `n²` times here and
never again. -/
def cacheOfAdj (n : ℕ) (adj : Fin n → Fin n → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, ¬adj i i) : CGraph where
  V := Fin n
  Adj := matLookup n (adjArray n adj)
  symm i j := by rw [matLookup_adjArray, matLookup_adjArray]; exact hs i j
  loopless i := by rw [matLookup_adjArray]; exact hl i

@[simp] theorem cacheOfAdj_adj (n : ℕ) (adj : Fin n → Fin n → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, ¬adj i i) (i j : Fin n) :
    (cacheOfAdj n adj hs hl).Adj i j = adj i j :=
  matLookup_adjArray n adj i j

@[simp] theorem card_cacheOfAdj (n : ℕ) (adj : Fin n → Fin n → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, ¬adj i i) :
    FinEnum.card (cacheOfAdj n adj hs hl).V = n := rfl

/-- `G`, relabelled onto `Fin (FinEnum.card G.V)` with its adjacency matrix precomputed.

A query is a bare array read, with no `FinEnum.equiv` in the way.  The cost is that this is only
isomorphic to `G` (`CGraph.isoCacheFin`), not equal to it. -/
def cacheFin (G : CGraph) : CGraph :=
  cacheOfAdj (FinEnum.card G.V) (fun i j ↦ G.Adj (FinEnum.equiv.symm i) (FinEnum.equiv.symm j))
    (fun _ _ ↦ G.symm _ _) (fun _ ↦ G.loopless _)

@[simp] theorem cacheFin_adj (G : CGraph) (i j : Fin (FinEnum.card G.V)) :
    G.cacheFin.Adj i j = G.Adj (FinEnum.equiv.symm i) (FinEnum.equiv.symm j) :=
  cacheOfAdj_adj ..

@[simp] theorem card_cacheFin (G : CGraph) : FinEnum.card G.cacheFin.V = FinEnum.card G.V := rfl

theorem cacheFin_adj_equiv (G : CGraph) (x y : G.V) :
    G.cacheFin.Adj (FinEnum.equiv x : Fin (FinEnum.card G.V)) (FinEnum.equiv y) = G.Adj x y := by
  rw [cacheFin_adj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The relabelling, as an isomorphism. -/
def isoCacheFin (G : CGraph) : G ≃cg G.cacheFin where
  toEquiv := FinEnum.equiv
  map_rel_iff' := Bool.eq_iff_iff.1 (G.cacheFin_adj_equiv _ _)

@[simp] theorem isoCacheFin_apply (G : CGraph) (x : G.V) : G.isoCacheFin x = FinEnum.equiv x :=
  rfl

@[simp] theorem isoCacheFin_symm_apply (G : CGraph) (i : Fin (FinEnum.card G.V)) :
    G.isoCacheFin.symm i = FinEnum.equiv.symm i := rfl

end CGraph
