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
share work must therefore not return a function type.  `cacheOfAdj`, `cacheOfArray` and `cache`
return a `CGraph`, so the array is built once per call, and the field they store is a partial
application — `matLookup n a` or `matLookupOn α a` — a closure holding the array.  The table
itself and its lookup are `IsoGraph.Canon.adjArray` and `IsoGraph.Canon.matLookup`, which live
next to the search because `CGraph.canonOfArray` tabulates for itself.

The entries are indexed by `Fin n` and the adjacency function is not, so filling the table calls
`FinEnum.equiv.symm` — which, for every enumeration that is not already `Fin n`, is a walk down a
list.  Two of them at each of the `n²` entries turns a fill that should cost `n²` into one that
costs `n²√n`, and on the Kneser graph `K(10, 5)` that was most of a second.  `vertexArray` does
the `n` decodes once and both loops of `adjArrayOn` read it, so the fill really is one sweep of
the adjacency function and nothing else.

That leaves the caller responsible for evaluating `G.cache` once: it is a function call like any
other, and calling it twice fills the array twice.  A top-level `def` (or a `let` outside the
loop) is evaluated once; writing `G.cache` inside the search itself would fill the array at every
node.

## When it pays

Measured by `testing/CacheBench.lean`, best of three interleaved rounds, in milliseconds; the
cost of filling the array is included in every cached figure.  The wins are large wherever the
adjacency function does real work and the search does not finish immediately:

| job                                  | plain  | `cache` | `cacheFin` |
| ------------------------------------ | ------ | ------- | ---------- |
| automorphisms of the Balaban 10-cage | 236    | 34      | 27         |
| automorphisms of the Tutte graph     | 113    | 27      | 22         |
| `C₄ ⋏ tutte` (contraction)           | 37     | 6       | 4          |
| `mcgee ⋏ mcgee` (both sides cached)  | 19     | 10      | 9          |
| `K₄ ≼ tutte` (minor)                 | 12     | 2       | 2          |
| automorphisms of `C₄₆`               | 9      | 10      | 7          |
| `petersen ⊆ tutte`                   | 4      | 2       | 1          |
| `C₈ ⊆ tutte`                         | 3      | 1       | 1          |
| canonical form of the Balaban 10-cage | 5     | 5       | 5          |
| canonical form of the Tutte graph    | 2      | 2       | 2          |

The last two rows are the exception that proves the rule: `CGraph.canonOfArray` tabulates for
itself — see `IsoGraph/Basic.lean` — so the plain column already pays for one fill, and caching
first only adds a second.

Caching the *pattern* is worth as much as caching the host, and caching both multiplies.  Nothing
measured on a `Fin n` vertex type got materially slower: even a host whose adjacency is a formula
rather than a list — the canonical form of `K₄₀`, 6 ms either way — is a wash, because an array
read beats a `Nat` comparison too.  The only losses are jobs shorter than the `n²` fill itself.
The rule of thumb is that the fill costs *half* a sweep of the adjacency function — the pairs
`i ≤ j` are the only ones asked about, see `CGraph.adjArrayOnSymm` below — so anything that would
touch every pair even once is already ahead.

## Which variant

For a vertex type that is already `Fin n` the two are within a few percent of each other, and
`cache` is the one to reach for: it is an equality, so nothing downstream has to know.  For any
other vertex type the two `FinEnum.equiv` calls per query dominate, and `cache` can be *slower*
than no cache at all — on the Kneser graph `K(10,5)`, whose vertices are the 5-element subsets of
`Fin 10`:

| job                | plain | `cache` | `cacheFin` |
| ------------------ | ----- | ------- | ---------- |
| canonical form     | 224   | 338     | 225        |
| `C₆ ⊆ K(10,5)`     | 154   | 701     | 40         |
| automorphisms of `K(7,3)` | 62 | 253  | 10         |
| degree sum         | 46    | 242     | 26         |

The canonical-form row is again one where the plain column already tabulates, so neither variant
has anything left to win.  The degree-sum row is the shortest job there is — it asks about every
pair exactly once — and `cacheFin` still comes out ahead of it, because the fill asks about half
of them.

So: `cache` on `Fin n`, `cacheFin` everywhere else.  (These figures are already with the
memoised subset enumeration of `IsoGraph.ForMathlib.FinEnum`; against Mathlib's instance, whose
`equiv` is a list scan, `cache` on `K(10,5)` costs 4121 ms rather than 242.)
-/

namespace CGraph

open IsoGraph.Canon (adjArray matLookup matLookup_adjArray matLookup_adjArray_eq matOfArray
  symmMatOfArray symmMatOfArray_eq symmAdjArray symmAdjArray_eq matLookup_symmAdjArray)

/-! ### Keeping the vertex type -/

/-- Read the entry of an adjacency matrix at a pair of vertices of an enumerated type, indexing
through `FinEnum.equiv`.  Top-level and applied to the array alone, for the reason above. -/
def matLookupOn (α : Type) [FinEnum α] (a : Array (Array Bool)) (x y : α) : Bool :=
  matLookup (FinEnum.card α) a (FinEnum.equiv x) (FinEnum.equiv y)

/-- The elements of `α` in the order `FinEnum.equiv` puts them, as an array.

Decoding an index is a walk down a list for every enumeration that is not already `Fin n`, so the
tabulation below reads its `n` vertices out of here once rather than decoding an index at each of
the `n²` entries — which would make filling the matrix cost `n²√n` steps and not `n²`. -/
def vertexArray (α : Type) [FinEnum α] : Array α := (FinEnum.toList α).toArray

@[simp] theorem size_vertexArray (α : Type) [FinEnum α] :
    (vertexArray α).size = FinEnum.card α := by
  simp [vertexArray, FinEnum.toList]

@[simp] theorem getElem_vertexArray (α : Type) [FinEnum α] (i : ℕ)
    (h : i < (vertexArray α).size) :
    (vertexArray α)[i] = FinEnum.equiv.symm ⟨i, by simpa using h⟩ := by
  simp [vertexArray, FinEnum.toList]

/-- The matrix of `f`, indexed by `FinEnum.equiv`.  Both loops read `vertexArray`, so `f` is called
`n²` times and `FinEnum.equiv.symm` only `n`. -/
def adjArrayOn (α : Type) [FinEnum α] (f : α → α → Bool) : Array (Array Bool) :=
  matOfArray (vertexArray α) f

/-- Reading the matrix at a pair of *indices* decodes them: this is what makes it the tabulation
of `f` and not of something else. -/
@[simp] theorem matLookup_adjArrayOn {α : Type} [FinEnum α] (f : α → α → Bool)
    (i j : Fin (FinEnum.card α)) :
    matLookup (FinEnum.card α) (adjArrayOn α f) i j =
      f (FinEnum.equiv.symm i) (FinEnum.equiv.symm j) := by
  simp [matLookup, adjArrayOn, matOfArray, Array.getD]

@[simp] theorem matLookupOn_adjArrayOn {α : Type} [FinEnum α] (f : α → α → Bool) (x y : α) :
    matLookupOn α (adjArrayOn α f) x y = f x y := by
  rw [matLookupOn, matLookup_adjArrayOn, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- **`CGraph.adjArrayOn` for a symmetric `f`**, at half the calls to `f`.

`IsoGraph.Canon.symmMatOfArray` fills only the pairs `i ≤ j` and mirrors the rest; the section
`### Half of the sweep` in `Canon/Spec.lean` is what it costs and why it is sound.  Since that is
an equality of arrays, every lemma about the full fill holds of this one by rewriting. -/
def adjArrayOnSymm (α : Type) [FinEnum α] (f : α → α → Bool) : Array (Array Bool) :=
  symmMatOfArray (vertexArray α) f

theorem adjArrayOnSymm_eq {α : Type} [FinEnum α] {f : α → α → Bool} (hs : ∀ x y, f x y = f y x) :
    adjArrayOnSymm α f = adjArrayOn α f :=
  symmMatOfArray_eq _ hs

@[simp] theorem matLookup_adjArrayOnSymm {α : Type} [FinEnum α] {f : α → α → Bool}
    (hs : ∀ x y, f x y = f y x) (i j : Fin (FinEnum.card α)) :
    matLookup (FinEnum.card α) (adjArrayOnSymm α f) i j =
      f (FinEnum.equiv.symm i) (FinEnum.equiv.symm j) := by
  rw [adjArrayOnSymm_eq hs, matLookup_adjArrayOn]

@[simp] theorem matLookupOn_adjArrayOnSymm {α : Type} [FinEnum α] {f : α → α → Bool}
    (hs : ∀ x y, f x y = f y x) (x y : α) : matLookupOn α (adjArrayOnSymm α f) x y = f x y := by
  rw [adjArrayOnSymm_eq hs, matLookupOn_adjArrayOn]

/-- `G`, with its adjacency matrix precomputed and its vertex type kept.

Every query costs two calls to `FinEnum.equiv`, which for a vertex type whose enumeration is a
list scan is not cheap; `CGraph.cacheFin` is the variant that avoids them. -/
def cache (G : CGraph) : CGraph where
  V := G.V
  enum := G.enum
  Adj := matLookupOn G.V (adjArrayOnSymm G.V G.Adj)
  symm x y := by
    rw [matLookupOn_adjArrayOnSymm G.symm, matLookupOn_adjArrayOnSymm G.symm]; exact G.symm x y
  loopless x := by rw [matLookupOn_adjArrayOnSymm G.symm]; exact G.loopless x

@[simp] theorem cache_adj (G : CGraph) (x y : G.V) : G.cache.Adj x y = G.Adj x y :=
  matLookupOn_adjArrayOnSymm G.symm ..

@[simp] theorem card_cache (G : CGraph) : FinEnum.card G.cache.V = FinEnum.card G.V := rfl

/-- **Caching changes nothing.**  The cached graph is not merely isomorphic to `G`: it is `G`.
Every fact about `G` — every invariant, every containment, every `IsoGraph` class — is a fact
about `G.cache` by rewriting along this. -/
theorem cache_eq (G : CGraph) : G.cache = G :=
  CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ G.cache_adj x y))

/-! ### Moving to `Fin n` -/

/-- The graph on `Fin n` with adjacency `adj`, tabulated: `adj` is called on the `n(n+1)/2` pairs
`i ≤ j` here and never again. -/
def cacheOfAdj (n : ℕ) (adj : Fin n → Fin n → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, ¬adj i i) : CGraph where
  V := Fin n
  Adj := matLookup n (symmAdjArray n adj)
  symm i j := by rw [matLookup_symmAdjArray n hs, matLookup_symmAdjArray n hs]; exact hs i j
  loopless i := by rw [matLookup_symmAdjArray n hs]; exact hl i

@[simp] theorem cacheOfAdj_adj (n : ℕ) (adj : Fin n → Fin n → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, ¬adj i i) (i j : Fin n) :
    (cacheOfAdj n adj hs hl).Adj i j = adj i j :=
  matLookup_symmAdjArray n hs i j

@[simp] theorem card_cacheOfAdj (n : ℕ) (adj : Fin n → Fin n → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, ¬adj i i) :
    FinEnum.card (cacheOfAdj n adj hs hl).V = n := rfl

/-- The graph on `Fin n` reading a matrix that has already been filled.  `cacheOfAdj` is this with
the filling folded in; the two are separate because `CGraph.cacheFin` has an array in hand and
would otherwise decode an index at every entry to build the function that builds it back. -/
def cacheOfArray (n : ℕ) (a : Array (Array Bool))
    (hs : ∀ i j : Fin n, matLookup n a i j = matLookup n a j i)
    (hl : ∀ i : Fin n, ¬matLookup n a i i) : CGraph where
  V := Fin n
  Adj := matLookup n a
  symm := hs
  loopless := hl

@[simp] theorem cacheOfArray_adj (n : ℕ) (a : Array (Array Bool))
    (hs : ∀ i j : Fin n, matLookup n a i j = matLookup n a j i)
    (hl : ∀ i : Fin n, ¬matLookup n a i i) (i j : Fin n) :
    (cacheOfArray n a hs hl).Adj i j = matLookup n a i j := rfl

@[simp] theorem card_cacheOfArray (n : ℕ) (a : Array (Array Bool))
    (hs : ∀ i j : Fin n, matLookup n a i j = matLookup n a j i)
    (hl : ∀ i : Fin n, ¬matLookup n a i i) :
    FinEnum.card (cacheOfArray n a hs hl).V = n := rfl

/-- `G`, relabelled onto `Fin (FinEnum.card G.V)` with its adjacency matrix precomputed.

A query is a bare array read, with no `FinEnum.equiv` in the way.  The cost is that this is only
isomorphic to `G` (`CGraph.isoCacheFin`), not equal to it. -/
def cacheFin (G : CGraph) : CGraph :=
  cacheOfArray (FinEnum.card G.V) (adjArrayOnSymm G.V G.Adj)
    (fun i j ↦ by
      rw [matLookup_adjArrayOnSymm G.symm, matLookup_adjArrayOnSymm G.symm]; exact G.symm _ _)
    (fun i ↦ by rw [matLookup_adjArrayOnSymm G.symm]; exact G.loopless _)

@[simp] theorem cacheFin_adj (G : CGraph) (i j : Fin (FinEnum.card G.V)) :
    G.cacheFin.Adj i j = G.Adj (FinEnum.equiv.symm i) (FinEnum.equiv.symm j) :=
  matLookup_adjArrayOnSymm G.symm i j

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
