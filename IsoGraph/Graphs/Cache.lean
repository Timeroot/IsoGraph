import IsoGraph.Basic

/-!
# Tabulated adjacency

A `CGraph` carries its adjacency as a function, and for most of the gallery that function does
real work on every query: `ofEdges` scans the edge list, `lcf` scans the list its code generates,
a product compares two coordinates, a complement negates a recursive call.  A search that asks
"are these two vertices adjacent?" a few million times pays for all of it a few million times.

`CGraph.cache` removes that cost for a graph whose vertex type is literally `Fin n`: it fills an
`n × n` array of `Bool` once and hands back the same graph with `Adj` a lookup into the array.
Same graph, not merely an isomorphic one — `CGraph.cache_eq` is an equation between `CGraph`s, so
anything proved of `G` holds of `G.cache n h` by rewriting, and a search run on the cached graph
answers the question about `G`.

## Building the table once

The whole point is that the array is filled once and then read, so the shape of the definitions
below is not free to change.  The Lean compiler maximises the arity of a top-level definition: a
`def f (x : α) : β → γ := let a := heavy x; fun b ↦ ⋯` is compiled as a *two*-argument function
with `heavy x` in its body, and then `heavy` runs again on every call.  A definition that means to
share work must therefore not return a function type.  `cacheOfAdj` returns a `CGraph`, so the
array it builds is built once per call, and the field it stores is the partial application
`matLookup n a`, a closure holding the array.  `cache` is the same shape, one layer up.

That leaves the caller responsible for evaluating `G.cache n h` once: it is a function call like
any other, and calling it twice fills the array twice.  A top-level `def` (or a `let` outside the
loop) is evaluated once; writing `G.cache n h` inside the search itself would fill the array at
every node.

## When it pays

Measured by `CacheBench.lean`, best of three, the cost of filling the array included in every
`cached` figure.  The wins are large wherever the adjacency function does real work and the search
does not finish immediately:

| job                                     | plain    | cached  |
| --------------------------------------- | -------- | ------- |
| automorphisms of the Balaban 10-cage     | 38.6 s   | 2.7 s   |
| automorphisms of the Tutte graph         | 3.46 s   | 0.31 s  |
| `C₄ ⋏ tutte` (contraction)               | 13.6 s   | 0.85 s  |
| `mcgee ⋏ mcgee` (both sides cached)      | 1.47 s   | 0.15 s  |
| `K₄ ≼ tutte` (minor)                     | 62 ms    | 14 ms   |
| `petersen ⊆ tutte`, host / pattern / both | 52 ms    | 36 / 35 / 18 ms |
| canonical form of the Balaban 10-cage    | 56 ms    | 13 ms   |

Caching the *pattern* is worth as much as caching the host, and caching both multiplies.  Nothing
measured got materially slower: even a host whose adjacency is a formula rather than a list —
`E₁₆ ⊑ C₃₀`, 1.21 s against 1.06 s; the canonical form of `K₄₀`, 64 ms either way — is a wash or a
small win, because an array read beats a `Nat` comparison too.  The only losses are jobs shorter
than the `n²` fill itself: the canonical form of the McGee graph is 2 ms plain and 4 ms cached.
The rule of thumb is that the fill costs one full sweep of the adjacency function, so anything
that would touch every pair more than once is already ahead.
-/

namespace CGraph

/-- The adjacency matrix of `adj`, as an array of rows. -/
def adjArray (n : ℕ) (adj : Fin n → Fin n → Bool) : Array (Array Bool) :=
  Array.ofFn fun i : Fin n ↦ Array.ofFn fun j : Fin n ↦ adj i j

/-- Read the entry of an adjacency matrix at `(i, j)`.

Kept as a separate top-level definition, and applied to the array alone: the closure that results
holds the table, where a `fun i j ↦ ⋯` written in place would rebuild it. -/
def matLookup (n : ℕ) (a : Array (Array Bool)) (i j : Fin n) : Bool :=
  (a.getD i.1 #[]).getD j.1 false

@[simp] theorem matLookup_adjArray (n : ℕ) (adj : Fin n → Fin n → Bool) (i j : Fin n) :
    matLookup n (adjArray n adj) i j = adj i j := by
  simp [matLookup, adjArray, Array.getD, i.isLt, j.isLt]

theorem matLookup_adjArray_eq (n : ℕ) (adj : Fin n → Fin n → Bool) :
    matLookup n (adjArray n adj) = adj :=
  funext fun i ↦ funext fun j ↦ matLookup_adjArray n adj i j

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
    Fintype.card (cacheOfAdj n adj hs hl).V = n := Fintype.card_fin n

/-- `G`, with its adjacency matrix precomputed.

The hypothesis is the first pass promised in the module header: the vertex type has to be `Fin n`
already, which for everything built by `ofEdges`, `lcf`, `gp` or `ofFn` it is, and the default
`by rfl` discharges it. -/
def cache (G : CGraph) (n : ℕ) (h : G.V = Fin n := by rfl) : CGraph :=
  cacheOfAdj n (fun i j ↦ G.Adj (cast h.symm i) (cast h.symm j))
    (fun _ _ ↦ G.symm _ _) (fun _ ↦ G.loopless _)

@[simp] theorem cache_adj (G : CGraph) (n : ℕ) (h : G.V = Fin n) (i j : Fin n) :
    (G.cache n h).Adj i j = G.Adj (cast h.symm i) (cast h.symm j) :=
  cacheOfAdj_adj ..

@[simp] theorem card_cache (G : CGraph) (n : ℕ) (h : G.V = Fin n) :
    Fintype.card (G.cache n h).V = n := Fintype.card_fin n

/-- Transporting a two-argument function along an equality of its domain changes nothing. -/
private theorem heq_cast_fun {α β : Type} (h : α = β) (f : α → α → Bool) :
    HEq (fun i j : β ↦ f (cast h.symm i) (cast h.symm j)) f := by
  subst h; rfl

/-- **Caching changes nothing.**  The cached graph is not merely isomorphic to `G`: it is `G`.
Every fact about `G` — every invariant, every containment, every `IsoGraph` class — is a fact
about `G.cache n h` by rewriting along this. -/
theorem cache_eq (G : CGraph) (n : ℕ) (h : G.V = Fin n) : G.cache n h = G := by
  refine CGraph.ext' h.symm ?_
  rw [show (G.cache n h).Adj = _ from matLookup_adjArray_eq ..]
  exact heq_cast_fun h G.Adj

end CGraph
