import IsoGraph.Canon.Group
import IsoGraph.Invariants.Basic

/-!
# Automorphisms of a `CGraph`, computed

`IsoGraph.Canon.Group` computes generators of the automorphism group of a graph on `Fin n`.  This
file moves that to `CGraph`, whose vertex type is arbitrary, and uses it to *prove* vertex- and
arc-transitivity.

## Getting to `Fin n`

Everything here needs a computable indexing `e : G.V ≃ Fin n` of the vertices.  It cannot be
manufactured: `Fintype.equivFin` is noncomputable, and the computable `Fintype.truncEquivFin`
lands in `Trunc`, out of which no data may be extracted.  So there are two flavours of each entry
point:

* `…OfEquiv e`, taking the indexing as an argument — for the usual case where `G.V` is `Fin n` or
  something with an obvious equivalence to it, and the fast one;
* the plain version, which goes through `G.canonicalize` (whose vertex type *is*
  `Fin (Fintype.card G.V)`) and transports the answer back along `nonempty_iso_canonicalize`.
  Always available, at the cost of a second run of the canonical labelling.

## Certificates

The transitivity entry points return `Canon.Cert P`: a proof of `P`, or nothing.  Use them as

```
example : G.IsVertexTransitive := (G.vertexTransitiveCert).out (by native_decide)
```

A `Cert.no` means the automorphisms found were not enough — which, since the search's generators
generate the whole group in practice, means the graph really is not transitive; but that
direction is not proved, so a `Cert.no` is not a disproof.  For the (exponentially slower)
complete decision procedure, `CGraph.IsVertexTransitive` also has a `Decidable` instance, which
enumerates all `n!` permutations.  (`Canon/Chain.lean` does compute a generating set that is
*proved* complete, but it is not wired up here: it costs a subtree search per candidate point.)
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

/-- An automorphism of the `Fin n` model is an automorphism of `G`. -/
def autoOfFin (e : G.V ≃ Fin n) (σ : autGroup n (G.finAdj e)) : G ≃cg G :=
  autoOfPerm ((e.trans (σ : Equiv.Perm (Fin n))).trans e.symm) fun x y ↦ by
    have := σ.2 (e x) (e y)
    simpa [finAdj] using this

@[simp] theorem autoOfFin_apply (e : G.V ≃ Fin n) (σ : autGroup n (G.finAdj e)) (x : G.V) :
    G.autoOfFin e σ x = e.symm ((σ : Equiv.Perm (Fin n)) (e x)) := rfl

/-- **Generators of the automorphism group of `G`**, harvested by the canonical labelling search.
-/
def autGens (e : G.V ≃ Fin n) : Array (G ≃cg G) :=
  (_root_.IsoGraph.Canon.autGens n (G.finAdj e)).map (G.autoOfFin e)

/-- **The pair entry point at the level of `CGraph`**: the canonical form of `G` and generators of
its automorphism group, from a single run of the search. -/
def canonMatrixAndAutos (e : G.V ≃ Fin n) : _root_.IsoGraph.Canon.AdjMatrix n × Array (G ≃cg G) :=
  let (M, gens) := canonMatrixAndGens n (G.finAdj e)
  (M, gens.map (G.autoOfFin e))

theorem canonMatrixAndAutos_fst (e : G.V ≃ Fin n) :
    (G.canonMatrixAndAutos e).1 = canonMatrix n (G.finAdj e) := rfl

theorem canonMatrixAndAutos_snd (e : G.V ≃ Fin n) :
    (G.canonMatrixAndAutos e).2 = G.autGens e := rfl

/-! ## Transitivity -/

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

/-- **Vertex-transitivity of `G`**, via the automorphisms the canonical labelling search finds. -/
def vertexTransitiveCertOfEquiv (e : G.V ≃ Fin n) : Cert G.IsVertexTransitive :=
  (_root_.IsoGraph.Canon.vertexTransitiveCert n (G.finAdj e)).map (G.isVertexTransitive_of_fin e)

/-- **Arc-transitivity of `G`**, via the automorphisms the canonical labelling search finds. -/
def arcTransitiveCertOfEquiv (e : G.V ≃ Fin n) : Cert G.IsArcTransitive :=
  (_root_.IsoGraph.Canon.arcTransitiveCert n (G.finAdj e)).map (G.isArcTransitive_of_fin e)

/-- The canonical representative of `G`, indexed by `Fin (Fintype.card G.V)` on the nose. -/
def canonicalizeEquiv : G.canonicalize.V ≃ Fin (Fintype.card G.V) := Equiv.refl _

/-- **Vertex-transitivity of `G`**, with no indexing of `G.V` supplied: run the test on the
canonical representative, which is indexed by `Fin (Fintype.card G.V)`, and transport back. -/
def vertexTransitiveCert : Cert G.IsVertexTransitive :=
  (G.canonicalize.vertexTransitiveCertOfEquiv G.canonicalizeEquiv).map fun h ↦
    isVertexTransitive_of_iso G.nonempty_iso_canonicalize.some.symm h

/-- **Arc-transitivity of `G`**, with no indexing of `G.V` supplied. -/
def arcTransitiveCert : Cert G.IsArcTransitive :=
  (G.canonicalize.arcTransitiveCertOfEquiv G.canonicalizeEquiv).map fun h ↦
    isArcTransitive_of_iso G.nonempty_iso_canonicalize.some.symm h

/-- The order of the automorphism group of `G`, or `none` if it exceeds `limit`.  Unverified: a
diagnostic, see `Canon.groupOrder?`. -/
def autGroupOrder? (e : G.V ≃ Fin n) (limit : Nat := 100000) : Option Nat :=
  _root_.IsoGraph.Canon.autGroupOrder? n (G.finAdj e) limit

end CGraph

/-! ## The quotient

Generators of the automorphism group are not an isomorphism invariant — they live on the vertex
set — so there is nothing to lift to `IsoGraph`.  Transitivity *is* invariant, and its
certificates transport through `IsoGraph.toCGraph`. -/

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

/-- Vertex-transitivity of an isomorphism class, tested on its canonical representative. -/
def vertexTransitiveCert (G : IsoGraph) : Cert G.IsVertexTransitive :=
  G.toCGraph.vertexTransitiveCert.map G.isVertexTransitive_toCGraph.1

/-- Arc-transitivity of an isomorphism class, tested on its canonical representative. -/
def arcTransitiveCert (G : IsoGraph) : Cert G.IsArcTransitive :=
  G.toCGraph.arcTransitiveCert.map G.isArcTransitive_toCGraph.1

end IsoGraph
