import IsoGraph.Canon.Group
import IsoGraph.Canon.Transitive
import IsoGraph.Cache
import IsoGraph.Invariants.Basic

/-!
# Automorphisms of a `CGraph`, computed

`IsoGraph.Canon.Group` computes generators of the automorphism group of a graph on `Fin n`, and
`IsoGraph.Canon.Transitive` decides transitivity from a complete set of them.  This file moves
both to `CGraph`, whose vertex type is arbitrary.

## Getting to `Fin n`

Everything here needs a computable indexing `e : G.V ≃ Fin n` of the vertices.  It cannot be
manufactured: `Fintype.equivFin` is noncomputable, and the computable `Fintype.truncEquivFin`
lands in `Trunc`, out of which no data may be extracted.  So there are two flavours of each entry
point:

* `…OfEquiv e`, taking the indexing as an argument — for the usual case where `G.V` is `Fin n` or
  something with an obvious equivalence to it, and the fast one;
* the plain version, which goes through `G.cacheFin` (whose vertex type *is*
  `Fin (FinEnum.card G.V)`) and transports the answer back along `CGraph.isoCacheFin`.  Always
  available, at the cost of one sweep of the adjacency function.

## Tabulating the model

The search asks `adj i j` a great many times, and `G.finAdj e` answers each one with two calls to
`e.symm` and one to `G.Adj`, which for most of the gallery is a scan of an edge list.  Every entry
point below therefore tabulates the model first — `Fin n × Fin n` queries, once — and hands the
search an array read.  `CacheBench.lean`, cases `api-vt`, `api-order` and `api-aut`, best of three
interleaved rounds, in milliseconds:

| job                                    | untabulated | tabulated |
| -------------------------------------- | ----------- | --------- |
| `vertexTransitiveB` of the Balaban 10-cage | 11517   | 619       |
| `vertexTransitiveB` of `K(7,3)`        | 3384        | 278       |
| `autGroupOrder?` of the Balaban 10-cage | 26         | 15        |
| `autGens` of the Balaban 10-cage       | 22          | 12        |

The transitivity tests are the ones that move, because they need a generating set that is *proved*
complete — the stabiliser chain of `Canon/Chain.lean` — where `autGens` and `autGroupOrder?` take
what the canonical labelling search harvested on its way past, which is far less work.

The tabulation is an `Array`, not a function: a definition whose result type is a function is
compiled with maximal arity, so a `def … : Fin n → Fin n → Bool := matLookup n (adjArray n ⋯)`
would rebuild the array on every single query.  `finAdjArray` returns the array and the entry
points apply `matLookup n` to it, which is a closure holding the table.

## Deciding transitivity

`Canon/Transitive.lean` decides vertex- and arc-transitivity of a graph on `Fin n` from a
generating set that is *proved* to generate the whole automorphism group, so a `false` is a
disproof and not just a failure to find a witness.  This file transports both directions to
`CGraph`, giving `vertexTransitiveB` and `arcTransitiveB` and the two iffs that say what they
mean.  One idiom covers both answers:

```
example : G.IsVertexTransitive := by rw [← CGraph.vertexTransitiveB_iff]; native_decide
example : ¬ H.IsArcTransitive := by rw [← CGraph.arcTransitiveB_iff]; native_decide
```

`CGraph.IsVertexTransitive` also has a `Decidable` instance (in `Invariants/Basic.lean`) which
enumerates all `n!` permutations; that is the one `decide` uses, and it is the right choice only
for very small graphs.
-/

set_option autoImplicit false

open IsoGraph.Canon

namespace CGraph

variable {n : Nat} (G : CGraph)

/-! ## The `Fin n` model of a graph -/

/-- `G`'s adjacency, read through an indexing `e` of its vertices. -/
def finAdj (e : G.V ≃ Fin n) : Fin n → Fin n → Bool := fun i j ↦ G.Adj (e.symm i) (e.symm j)

@[simp] theorem finAdj_apply (e : G.V ≃ Fin n) (u v : G.V) :
    G.finAdj e (e u) (e v) = G.Adj u v := by simp [finAdj]

/-- **The `Fin n` model of `G`, tabulated.**  An array rather than a function, for the reason in
the header: what the entry points below pass to the search is `matLookup n (G.finAdjArray e)`, a
closure holding this table. -/
def finAdjArray (e : G.V ≃ Fin n) : Array (Array Bool) := adjArray n (G.finAdj e)

@[simp] theorem matLookup_finAdjArray (e : G.V ≃ Fin n) :
    matLookup n (G.finAdjArray e) = G.finAdj e :=
  matLookup_adjArray_eq n (G.finAdj e)

/-- An automorphism of the `Fin n` model is an automorphism of `G`. -/
def autoOfFin (e : G.V ≃ Fin n) (σ : autGroup n (G.finAdj e)) : G ≃cg G :=
  autoOfPerm ((e.trans (σ : Equiv.Perm (Fin n))).trans e.symm) fun x y ↦ by
    have := σ.2 (e x) (e y)
    simpa [finAdj] using this

@[simp] theorem autoOfFin_apply (e : G.V ≃ Fin n) (σ : autGroup n (G.finAdj e)) (x : G.V) :
    G.autoOfFin e σ x = e.symm ((σ : Equiv.Perm (Fin n)) (e x)) := rfl

/-- An automorphism of a model equal to `G.finAdj e` is an automorphism of `G`.  The tabulated
model is only *propositionally* equal to `G.finAdj e`, and `autGroup n adj` depends on `adj`, so
the membership proof has to be moved across by hand. -/
def autoOfTab (e : G.V ≃ Fin n) {adj : Fin n → Fin n → Bool} (h : adj = G.finAdj e)
    (σ : autGroup n adj) : G ≃cg G :=
  G.autoOfFin e ⟨σ.1, fun i j ↦ by rw [← h]; exact σ.2 i j⟩

@[simp] theorem autoOfTab_apply (e : G.V ≃ Fin n) {adj : Fin n → Fin n → Bool}
    (h : adj = G.finAdj e) (σ : autGroup n adj) (x : G.V) :
    G.autoOfTab e h σ x = e.symm ((σ : Equiv.Perm (Fin n)) (e x)) := rfl

/-- **Generators of the automorphism group of `G`**, harvested by the canonical labelling search.
-/
def autGens (e : G.V ≃ Fin n) : Array (G ≃cg G) :=
  (_root_.IsoGraph.Canon.autGens n (matLookup n (G.finAdjArray e))).map
    (G.autoOfTab e (G.matLookup_finAdjArray e))

/-- **The pair entry point at the level of `CGraph`**: the canonical form of `G` and generators of
its automorphism group, from a single run of the search. -/
def canonMatrixAndAutos (e : G.V ≃ Fin n) : _root_.IsoGraph.Canon.AdjMatrix n × Array (G ≃cg G) :=
  let (M, gens) := canonMatrixAndGens n (matLookup n (G.finAdjArray e))
  (M, gens.map (G.autoOfTab e (G.matLookup_finAdjArray e)))

theorem canonMatrixAndAutos_fst (e : G.V ≃ Fin n) :
    (G.canonMatrixAndAutos e).1 = canonMatrix n (G.finAdj e) := by
  show canonMatrix n (matLookup n (G.finAdjArray e)) = _
  rw [matLookup_finAdjArray]

theorem canonMatrixAndAutos_snd (e : G.V ≃ Fin n) :
    (G.canonMatrixAndAutos e).2 = G.autGens e := rfl

/-! ## Transitivity

The tests below come from `Canon/Transitive.lean`, which saturates the orbit of a point under a
generating set that is proved complete.  So each of them decides: `true` gives the proposition and
`false` refutes it. -/

theorem isVertexTransitive_of_fin (e : G.V ≃ Fin n)
    (h : ∀ i j : Fin n, ∃ σ ∈ autGroup n (G.finAdj e), σ i = j) : G.IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ, hij⟩ := h (e u) (e v)
  exact ⟨G.autoOfFin e ⟨σ, hσ⟩, by simp [hij]⟩

theorem isArcTransitive_of_fin (e : G.V ≃ Fin n)
    (h : ∀ i j k l : Fin n, G.finAdj e i j = true → G.finAdj e k l = true →
      ∃ σ ∈ autGroup n (G.finAdj e), σ i = k ∧ σ j = l) : G.IsArcTransitive := by
  intro u v u' v' huv hu'v'
  obtain ⟨σ, hσ, h₁, h₂⟩ := h (e u) (e v) (e u') (e v') (by simpa using huv) (by simpa using hu'v')
  exact ⟨G.autoOfFin e ⟨σ, hσ⟩, by simp [h₁], by simp [h₂]⟩

/-- An automorphism of `G`, read as a permutation of the `Fin n` model.  The converse direction of
`autoOfFin`. -/
def finAuto (e : G.V ≃ Fin n) (φ : G ≃cg G) : Equiv.Perm (Fin n) := (e.symm.trans φ.toEquiv).trans e

@[simp] theorem finAuto_apply (e : G.V ≃ Fin n) (φ : G ≃cg G) (i : Fin n) :
    G.finAuto e φ i = e (φ (e.symm i)) := rfl

theorem finAuto_mem (e : G.V ≃ Fin n) (φ : G ≃cg G) :
    G.finAuto e φ ∈ autGroup n (G.finAdj e) := by
  intro i j
  simp [finAdj, φ.adj_eq]

/-- **Vertex-transitivity, in the `Fin n` model.**  The direction that matters for a *dis*proof is
the forward one: an automorphism of `G` is a permutation of `Fin n` in `autGroup`. -/
theorem isVertexTransitive_iff_fin (e : G.V ≃ Fin n) :
    G.IsVertexTransitive ↔ ∀ i j : Fin n, ∃ σ ∈ autGroup n (G.finAdj e), σ i = j := by
  refine ⟨fun h i j => ?_, G.isVertexTransitive_of_fin e⟩
  obtain ⟨φ, hφ⟩ := h (e.symm i) (e.symm j)
  exact ⟨G.finAuto e φ, G.finAuto_mem e φ, by simp [hφ]⟩

/-- **Arc-transitivity, in the `Fin n` model.** -/
theorem isArcTransitive_iff_fin (e : G.V ≃ Fin n) :
    G.IsArcTransitive ↔ ∀ i j k l : Fin n, G.finAdj e i j = true → G.finAdj e k l = true →
      ∃ σ ∈ autGroup n (G.finAdj e), σ i = k ∧ σ j = l := by
  refine ⟨fun h i j k l hij hkl => ?_, G.isArcTransitive_of_fin e⟩
  obtain ⟨φ, h₁, h₂⟩ := h (e.symm i) (e.symm j) (e.symm k) (e.symm l) hij hkl
  exact ⟨G.finAuto e φ, G.finAuto_mem e φ, by simp [h₁], by simp [h₂]⟩

/-- **Is `G` vertex-transitive?** -/
def vertexTransitiveBOfEquiv (e : G.V ≃ Fin n) : Bool :=
  _root_.IsoGraph.Canon.vertexTransitiveB n (matLookup n (G.finAdjArray e))

theorem vertexTransitiveBOfEquiv_iff (e : G.V ≃ Fin n) :
    G.vertexTransitiveBOfEquiv e = true ↔ G.IsVertexTransitive := by
  rw [vertexTransitiveBOfEquiv, matLookup_finAdjArray]
  exact (_root_.IsoGraph.Canon.vertexTransitiveB_iff n (G.finAdj e)).trans
    (G.isVertexTransitive_iff_fin e).symm

/-- **Is `G` arc-transitive?** -/
def arcTransitiveBOfEquiv (e : G.V ≃ Fin n) : Bool :=
  _root_.IsoGraph.Canon.arcTransitiveB n (matLookup n (G.finAdjArray e))

theorem arcTransitiveBOfEquiv_iff (e : G.V ≃ Fin n) :
    G.arcTransitiveBOfEquiv e = true ↔ G.IsArcTransitive := by
  rw [arcTransitiveBOfEquiv, matLookup_finAdjArray]
  exact (_root_.IsoGraph.Canon.arcTransitiveB_iff n (G.finAdj e)).trans
    (G.isArcTransitive_iff_fin e).symm

/-- The canonical representative of `G`, indexed by `Fin (FinEnum.card G.V)` on the nose. -/
def canonicalizeEquiv : G.canonicalize.V ≃ Fin (FinEnum.card G.V) := Equiv.refl _

/-- The tabulated copy of `G`, indexed by `Fin (FinEnum.card G.V)` on the nose. -/
def cacheFinEquiv : G.cacheFin.V ≃ Fin (FinEnum.card G.V) := Equiv.refl _

/-- Transitivity of `G` and of its tabulated copy are the same question. -/
theorem isVertexTransitive_cacheFin :
    G.cacheFin.IsVertexTransitive ↔ G.IsVertexTransitive :=
  ⟨isVertexTransitive_of_iso G.isoCacheFin.symm, isVertexTransitive_of_iso G.isoCacheFin⟩

theorem isArcTransitive_cacheFin :
    G.cacheFin.IsArcTransitive ↔ G.IsArcTransitive :=
  ⟨isArcTransitive_of_iso G.isoCacheFin.symm, isArcTransitive_of_iso G.isoCacheFin⟩

/-- Transitivity of `G` and of its canonical representative are the same question. -/
theorem isVertexTransitive_canonicalize :
    G.canonicalize.IsVertexTransitive ↔ G.IsVertexTransitive :=
  ⟨isVertexTransitive_of_iso G.nonempty_iso_canonicalize.some.symm,
    isVertexTransitive_of_iso G.nonempty_iso_canonicalize.some⟩

theorem isArcTransitive_canonicalize :
    G.canonicalize.IsArcTransitive ↔ G.IsArcTransitive :=
  ⟨isArcTransitive_of_iso G.nonempty_iso_canonicalize.some.symm,
    isArcTransitive_of_iso G.nonempty_iso_canonicalize.some⟩

/-- **Is `G` vertex-transitive?**, with no indexing of `G.V` supplied: ask of the tabulated copy,
which is indexed by `Fin (FinEnum.card G.V)`, and transport back.

`G.canonicalize` would serve just as well as the indexed copy, and used to; `G.cacheFin` is the
same relabelling done by one sweep of the adjacency function instead of a whole canonical
labelling search. -/
def vertexTransitiveB : Bool := G.cacheFin.vertexTransitiveBOfEquiv G.cacheFinEquiv

theorem vertexTransitiveB_iff : G.vertexTransitiveB = true ↔ G.IsVertexTransitive :=
  (G.cacheFin.vertexTransitiveBOfEquiv_iff G.cacheFinEquiv).trans G.isVertexTransitive_cacheFin

/-- **Is `G` arc-transitive?**, with no indexing of `G.V` supplied. -/
def arcTransitiveB : Bool := G.cacheFin.arcTransitiveBOfEquiv G.cacheFinEquiv

theorem arcTransitiveB_iff : G.arcTransitiveB = true ↔ G.IsArcTransitive :=
  (G.cacheFin.arcTransitiveBOfEquiv_iff G.cacheFinEquiv).trans G.isArcTransitive_cacheFin

/-- The order of the automorphism group of `G`, or `none` if it exceeds `limit`.  Unverified: a
diagnostic, see `Canon.groupOrder?`. -/
def autGroupOrder? (e : G.V ≃ Fin n) (limit : Nat := 100000) : Option Nat :=
  _root_.IsoGraph.Canon.autGroupOrder? n (matLookup n (G.finAdjArray e)) limit

/-- **The order of the automorphism group of `G`**, with no indexing of `G.V` supplied. -/
def autOrder? (limit : Nat := 100000) : Option Nat :=
  G.cacheFin.autGroupOrder? G.cacheFinEquiv limit

end CGraph

/-! ## The quotient

Generators of the automorphism group are not an isomorphism invariant — they live on the vertex
set — so there is nothing to lift to `IsoGraph`.  Transitivity *is* invariant, and its test
transports through `IsoGraph.toCGraph`. -/

namespace IsoGraph

theorem isVertexTransitive_toCGraph (G : IsoGraph) :
    G.toCGraph.IsVertexTransitive ↔ G.IsVertexTransitive := by
  induction G using Quotient.inductionOn with
  | h g =>
    exact ⟨CGraph.isVertexTransitive_of_iso g.nonempty_iso_canonicalize.some.symm,
      CGraph.isVertexTransitive_of_iso g.nonempty_iso_canonicalize.some⟩

theorem isArcTransitive_toCGraph (G : IsoGraph) :
    G.toCGraph.IsArcTransitive ↔ G.IsArcTransitive := by
  induction G using Quotient.inductionOn with
  | h g =>
    exact ⟨CGraph.isArcTransitive_of_iso g.nonempty_iso_canonicalize.some.symm,
      CGraph.isArcTransitive_of_iso g.nonempty_iso_canonicalize.some⟩

/-- **Is this isomorphism class vertex-transitive?**, tested on its canonical representative. -/
def vertexTransitiveB (G : IsoGraph) : Bool := G.toCGraph.vertexTransitiveB

theorem vertexTransitiveB_iff (G : IsoGraph) :
    G.vertexTransitiveB = true ↔ G.IsVertexTransitive :=
  G.toCGraph.vertexTransitiveB_iff.trans G.isVertexTransitive_toCGraph

/-- **Is this isomorphism class arc-transitive?** -/
def arcTransitiveB (G : IsoGraph) : Bool := G.toCGraph.arcTransitiveB

theorem arcTransitiveB_iff (G : IsoGraph) :
    G.arcTransitiveB = true ↔ G.IsArcTransitive :=
  G.toCGraph.arcTransitiveB_iff.trans G.isArcTransitive_toCGraph

end IsoGraph
