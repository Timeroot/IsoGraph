import IsoGraph.Decompose.Spectrum
import IsoGraph.SmallGraphs.SolidValues

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# A gallery of decompositions

`IsoGraph/Decompose/Atlas.lean` searches for a description of a graph in terms of named graphs;
`IsoGraph/Decompose/Tactic.lean` turns the description into a kernel-checked isomorphism, and
`IsoGraph/Decompose/Spectrum.lean` uses it to compute a Laplacian spectrum.  This file is what
that machinery is *for*: a gallery of graphs constructed one way and recognised as another.

Each example below is a theorem, and each is proved by naming the graph and letting the search
find the other side of the equation.  Nothing is postulated: the tactic emits a certificate and
the kernel checks it, so `CGraph.lineGraph (CGraph.hypercube 3) ≃cg cuboctahedron` is a proof
about the two adjacency tables, not a claim about what the search believes.

## What is here

* line graphs of the cubic Platonic solids, which are their medial graphs;
* bipartite double covers, `G ⊗g K₂`, which turn out to be famous graphs surprisingly often;
* graphs that belong to two families at once, and the order the atlas resolves that in;
* self-complementary graphs, joins, and complete multipartite graphs;
* cartesian products, and what Sabidussi–Vizing does and does not say about them;
* Laplacian spectra of graphs whose spectrum is only known to the library under another name;
* two invariants — Hamiltonicity and an edge chromatic number — transported along a decomposition.

The examples in `Tactic.lean` are its regression test, one per rule of the search.  These are
chosen for the mathematics instead, and every one of them is a fact one would otherwise look up.
-/

set_option autoImplicit false

open CGraph

/-! ## Line graphs

For a cubic planar graph the line graph is the medial graph, so the line graphs of the
tetrahedron, the cube and the dodecahedron are the octahedron, the cuboctahedron and the
icosidodecahedron.  (The first of the three is in `Tactic.lean`.) -/

/-- The line graph of the cube is the cuboctahedron. -/
example : Nonempty (CGraph.lineGraph (CGraph.hypercube 3) ≃cg NamedGraphs.cuboctahedron) := by
  generate_graph_iso (CGraph.lineGraph (CGraph.hypercube 3)) with e
  exact ⟨e⟩

/-- The line graph of the dodecahedron is the icosidodecahedron.  Thirty vertices, each of them an
edge of a twenty-vertex graph, and the certificate is still one `decide`; it is the most expensive
example in the file, and the only one that takes seconds rather than milliseconds. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph NamedGraphs.dodecahedron) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid NamedGraphs.icosidodecahedron := by
  decompose_graph (CGraph.lineGraph NamedGraphs.dodecahedron)

/-- The line graph of `K_{3,3}` is the `3 × 3` rook's graph — the edges of `K_{3,3}` are the cells
of a `3 × 3` grid, and two of them meet exactly when they share a row or a column. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph (CGraph.bipartite 3 3)) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.rook 3 3) := by
  decompose_graph (CGraph.lineGraph (CGraph.bipartite 3 3))

/-- The line graph of `K₅` is the triangular graph `T(5)`, which is what `triangular` means. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph (CGraph.complete 5)) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.triangular 5) := by
  decompose_graph (CGraph.lineGraph (CGraph.complete 5))

/-! ## Bipartite double covers

`G ⊗g K₂` is the bipartite double cover of `G`: two copies of the vertex set, with `(u, 0)` and
`(v, 1)` adjacent when `u` and `v` are.  It is connected exactly when `G` is connected and not
bipartite, and for several small graphs it has a name of its own. -/

/-- The bipartite double cover of `K₄` is the cube. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.complete 4 ⊗g CGraph.complete 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3) := by
  decompose_graph (CGraph.complete 4 ⊗g CGraph.complete 2)

/-- The bipartite double cover of the Petersen graph is the Desargues graph. -/
example : Nonempty (CGraph.petersen ⊗g CGraph.complete 2 ≃cg NamedGraphs.desargues) := by
  generate_graph_iso (CGraph.petersen ⊗g CGraph.complete 2) with e
  exact ⟨e⟩

/-- The bipartite double cover of `K₅` is the crown `S₅⁰`, that is `K_{5,5}` less a perfect
matching. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.complete 5 ⊗g CGraph.complete 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.crown 5) := by
  decompose_graph (CGraph.complete 5 ⊗g CGraph.complete 2)

/-- An odd cycle is doubled into a cycle of twice the length. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.cycle 5 ⊗g CGraph.complete 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.cycle 10) := by
  decompose_graph (CGraph.cycle 5 ⊗g CGraph.complete 2)

/-- Doubling a graph that is *already* bipartite disconnects it, into two copies of the graph. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3 ⊗g CGraph.complete 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3 ⊕g CGraph.hypercube 3) := by
  decompose_graph (CGraph.hypercube 3 ⊗g CGraph.complete 2)

/-! ## One graph, several names

A graph can belong to two families at once, and then the atlas has to choose.  Individual names
come before families and families are searched in the order they are listed, so the answer is the
most specific name the library has. -/

/-- The generalised Petersen graph `GP(10, 2)` is the dodecahedron. -/
example : Nonempty (CGraph.gp 10 2 ≃cg NamedGraphs.dodecahedron) := by
  generate_graph_iso (CGraph.gp 10 2) with e
  exact ⟨e⟩

/-- `GP(8, 3)` is the Möbius–Kantor graph and `GP(12, 5)` is the Nauru graph. -/
example : Nonempty (CGraph.gp 8 3 ≃cg NamedGraphs.mobiusKantor) := by
  generate_graph_iso (CGraph.gp 8 3) with e
  exact ⟨e⟩

example : Nonempty (CGraph.gp 12 5 ≃cg NamedGraphs.nauru) := by
  generate_graph_iso (CGraph.gp 12 5) with e
  exact ⟨e⟩

/-- The Johnson graph `J(5, 2)` is the triangular graph `T(5)`; both are the line graph of `K₅`,
and `triangular` is listed first. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.johnson 5 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.triangular 5) := by
  decompose_graph (CGraph.johnson 5 2)

/-- `T(4)` is the octahedron, which has a name of its own. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.triangular 4) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid SmallGraphs.octahedron := by
  decompose_graph (CGraph.triangular 4)

/-- The crown `S₄⁰` — `K_{4,4}` less a perfect matching — is the cube. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.crown 4) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3) := by
  decompose_graph (CGraph.crown 4)

/-- The tensor square of `K₃` is the `3 × 3` rook's graph, which is also `K₃ □g K₃`: the two
products agree here, and neither of them is how the atlas names the answer. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.complete 3 ⊗g CGraph.complete 3) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.rook 3 3) := by
  decompose_graph (CGraph.complete 3 ⊗g CGraph.complete 3)

/-! ## Complements

The search looks at the complement when the graph itself is not named and is not a join, which is
how it recognises a graph whose complement is famous.  The first two graphs below are their own
complements.  What makes any of this safe is that the canonical code is a complete invariant, not
a heuristic: the Shrikhande graph and `K₄ □g K₄` have the same strongly regular parameters
`(16, 6, 2, 2)` and the search does not confuse them, and if it ever did the certificate would
fail in the kernel rather than produce a false theorem. -/

/-- The `3 × 3` rook's graph is self-complementary: it is the strongly regular graph on the
parameters `(9, 4, 1, 2)`, and so is its complement. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.rook 3 3)ᶜ : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.rook 3 3) := by
  decompose_graph ((CGraph.rook 3 3)ᶜ)

/-- So is the Paley graph on thirteen vertices — as every Paley graph is, `x ↦ nx` for a non-residue
`n` being an isomorphism onto the complement. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.paley 13)ᶜ : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.paley 13) := by
  decompose_graph ((CGraph.paley 13)ᶜ)

/-- The complement of the cube is the `2 × 4` rook's graph, that is `K₄ □g K₂` — a complement of a
cartesian product that is again a cartesian product, which is not something to expect. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3)ᶜ : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.rook 2 4) := by
  decompose_graph ((CGraph.hypercube 3)ᶜ)

/-- The complement of a cocktail party graph is a perfect matching, and a disconnected graph is
described component by component. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.cocktailParty 4)ᶜ : IsoGraph)
    = Quotient.mk CGraph.isoSetoid
      (CGraph.complete 2 ⊕g CGraph.complete 2 ⊕g CGraph.complete 2 ⊕g CGraph.complete 2) := by
  decompose_graph ((CGraph.cocktailParty 4)ᶜ)

/-! ## Joins and multipartite graphs

A join is a graph whose complement is disconnected, so the search finds one by complementing.  The
complete multipartite graphs are exactly the joins of empty graphs, and they have their own names
in the atlas. -/

/-- Joining two complete graphs gives a complete graph. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.complete 3 ∇g CGraph.complete 4) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.complete 7) := by
  decompose_graph (CGraph.complete 3 ∇g CGraph.complete 4)

/-- Joining two empty graphs gives a complete bipartite graph. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.empty 3 ∇g CGraph.empty 4) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.bipartite 3 4) := by
  decompose_graph (CGraph.empty 3 ∇g CGraph.empty 4)

/-- Three disjoint triangles, complemented, are the Turán graph `T(9, 3) = K_{3,3,3}`. -/
example : (Quotient.mk CGraph.isoSetoid
      (CGraph.complete 3 ⊕g CGraph.complete 3 ⊕g CGraph.complete 3)ᶜ : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.turan 9 3) := by
  decompose_graph ((CGraph.complete 3 ⊕g CGraph.complete 3 ⊕g CGraph.complete 3)ᶜ)

/-- `C₄ ∇g C₄` is the cocktail party graph `K_{2,2,2,2}`: each `C₄` is a pair of non-edges, and
joining the two leaves four non-edges in all. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.cycle 4 ∇g CGraph.cycle 4) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.cocktailParty 4) := by
  decompose_graph (CGraph.cycle 4 ∇g CGraph.cycle 4)

/-- A wheel is a cycle joined to a point, and is named as a wheel rather than as that join. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.cycle 6 ∇g CGraph.complete 1) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.wheel 6) := by
  decompose_graph (CGraph.cycle 6 ∇g CGraph.complete 1)

/-! ## Cartesian products -/

/-- `K₃ □g K₄` is the `3 × 4` rook's graph: a rook's graph *is* a product of complete graphs, and
the atlas name comes before the product rule. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.complete 3 □g CGraph.complete 4) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.rook 3 4) := by
  decompose_graph (CGraph.complete 3 □g CGraph.complete 4)

/-- The square of the square is the four-dimensional cube. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.hypercube 2 □g CGraph.hypercube 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.hypercube 4) := by
  decompose_graph (CGraph.hypercube 2 □g CGraph.hypercube 2)

/-- A grid is not in the atlas, and is described as the product it is — the statement below would
not typecheck if the search named anything else. -/
example : Nonempty (CGraph.path 3 □g CGraph.path 4 ≃cg CGraph.path 3 □g CGraph.path 4) := by
  generate_graph_iso (CGraph.path 3 □g CGraph.path 4) with e
  exact ⟨e⟩

/-- The description of a product is not unique as an *expression*: the search factors `C₄ □g C₅`
as `K₂ □g (K₂ □g C₅)`, having found the pentagonal prism first.  What Sabidussi–Vizing says —
`IsoGraph.CartesianProduct.multiset_eq_of_prod_eq` — is that the multiset of prime factors is
unique, and the two readings of this graph give the same one, `{K₂, K₂, C₅}`. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.cycle 4 □g CGraph.cycle 5) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.complete 2 □g CGraph.prism 5) := by
  decompose_graph (CGraph.cycle 4 □g CGraph.cycle 5)

/-! ## Spectra

`compute_lapSpectrum` runs the decomposition and then the spectrum rules, so a graph whose
Laplacian spectrum the library knows only under another name gets it anyway. -/

/-- `C₄ ∇g C₄` is `K_{2,2,2,2}`, whose Laplacian spectrum is `0`, `6` four times and `8` three
times.  Nothing about the join is used: the graph is recognised as a cocktail party graph and the
cocktail party rule applies. -/
example : IsoGraph.lapSpectrum
    (Quotient.mk CGraph.isoSetoid (CGraph.cycle 4 ∇g CGraph.cycle 4))
      = 0 ::ₘ (Multiset.replicate 4 6 + Multiset.replicate 3 8) := by
  compute_lapSpectrum (CGraph.cycle 4 ∇g CGraph.cycle 4)

/-- The tensor square of `K₃` is the rook's graph `K₃ □g K₃`, and the Laplacian spectrum that comes
out is the rook's: `0`, `3` four times and `6` four times.  There is no rule for the spectrum of a
tensor product — this is the decomposition doing the work. -/
example : IsoGraph.lapSpectrum
    (Quotient.mk CGraph.isoSetoid (CGraph.complete 3 ⊗g CGraph.complete 3))
      = 0 ::ₘ (Multiset.replicate 4 3 + Multiset.replicate 4 6) := by
  compute_lapSpectrum (CGraph.complete 3 ⊗g CGraph.complete 3)

/-- A grid: the product survives the decomposition and the grid rule adds the two paths'
eigenvalues in pairs. -/
example : IsoGraph.lapSpectrum
    (Quotient.mk CGraph.isoSetoid (CGraph.path 3 □g CGraph.path 4))
      = Finset.univ.val.map (fun p : Fin 3 × Fin 4 ↦
          (2 - 2 * Real.cos (Real.pi * p.1.1 / 3)) + (2 - 2 * Real.cos (Real.pi * p.2.1 / 4))) := by
  compute_lapSpectrum (CGraph.path 3 □g CGraph.path 4)

/-! ## Using the isomorphism

The tactic hands back an isomorphism, and an isomorphism transports everything.  These are facts
about a graph given by a construction, proved from the library's knowledge of the graph it turns
out to be. -/

/-- `GP(10, 2)` is Hamiltonian, because it is the dodecahedron and the dodecahedron is. -/
example : (CGraph.gp 10 2).IsHamiltonian := by
  generate_graph_iso (CGraph.gp 10 2) with e
  exact CGraph.isHamiltonian_of_iso e.symm isHamiltonian_dodecahedron

/-- The bipartite double cover of the Petersen graph is Hamiltonian — the Petersen graph itself
famously is not. -/
example : (CGraph.petersen ⊗g CGraph.complete 2).IsHamiltonian := by
  generate_graph_iso (CGraph.petersen ⊗g CGraph.complete 2) with e
  exact CGraph.isHamiltonian_of_iso e.symm isHamiltonian_desargues

/-- The cube is `3`-edge-colourable.  The edge chromatic number is the chromatic number of the line
graph, the line graph is the cuboctahedron, and the cuboctahedron is `3`-chromatic. -/
example : IsoGraph.edgeChromNum (Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3)) = 3 := by
  rw [IsoGraph.edgeChromNum_eq, IsoGraph.lineGraph_mk]
  decompose_graph (CGraph.lineGraph (CGraph.hypercube 3))
  simp
