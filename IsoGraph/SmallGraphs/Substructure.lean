import IsoGraph.Containment
import IsoGraph.SmallGraphs.Defs

/-!
# What sits inside what

The gallery, crossed with the containment relations of `IsoGraph/Containment/`: which named graph
is a subgraph, an induced subgraph, a minor, a topological minor, an immersion, a contraction or a
quotient of which other.  Every proof is the same one — run the search of
`Containment/Algorithms/Cached.lean` on the two graphs and read the answer — so what a statement
here costs is the search, and what it says is a fact about the two graphs and nothing else.

The searches are exponential in the *pattern*, so the useful statements are the ones with a small
pattern and any host at all: `C₁₂` inside the 126-vertex Tutte 12-cage is five seconds, while the
Petersen graph inside the Desargues graph is sixteen — and the Balaban 11-cage inside the Tutte
12-cage, which is a real theorem (the 11-cage is got from the 12-cage by excision: delete a
subtree, then suppress the degree-two vertices left behind, so the 11-cage is a *topological
minor* of the 12-cage), is out of reach, since the search would have to place 112 branch
vertices.  Nothing here runs for longer than that sixteen seconds, and nearly everything is
under a second.

Four kinds of statement, in order:

| section | pattern | says |
| --- | --- | --- |
| Girth | `cycle k` | the cage property: the shortest cycle is there, and is induced, and nothing shorter is |
| Claws | `claw` | a triangle-free cubic graph has an induced claw — the neighbours of any vertex |
| Kuratowski | `K₅`, `K₃,₃` | which of the named graphs are planar, and which of the two obstructions each nonplanar one carries |
| The gallery | a named graph | the Petersen graph inside the Kneser, Hoffman–Singleton and Desargues graphs |

and then the two four-chromatic triangle-free graphs, whose chromatic number is a statement about
homomorphisms into `complete k`, and so belongs here as much as in `SmallGraphs/Colouring.lean`.

The girth and the chromatic numbers themselves are in `SmallGraphs/Defs/` and
`SmallGraphs/Colouring.lean`; what is new here is that the cycle, or the colouring, is exhibited
as a *containment*, which is not something the invariants give back.
-/

set_option autoImplicit false

namespace IsoGraph

open NamedGraphs SmallGraphs

/-! ## Girth, as a containment

A graph of girth `g` contains `C_g` and no shorter cycle, and the `C_g` it contains has to be
induced — a chord would close a shorter one.  That is the whole content of a cage. -/

/-- The Petersen graph has an induced pentagon. -/
theorem cycle_five_induced_petersen : cycle 5 ≤ᵢₛ petersen := by native_decide

/-- The Petersen graph is triangle-free. -/
theorem not_cycle_three_subgraph_petersen : ¬ (cycle 3 ≤ₛ petersen) := by native_decide

/-- The Petersen graph has no square, so with the pentagon above its girth is five. -/
theorem not_cycle_four_subgraph_petersen : ¬ (cycle 4 ≤ₛ petersen) := by native_decide

/-- The Heawood graph, the `(3,6)`-cage, has an induced hexagon. -/
theorem cycle_six_induced_heawood : cycle 6 ≤ᵢₛ ⟦heawood⟧ := by native_decide

/-- …and no pentagon. -/
theorem not_cycle_five_subgraph_heawood : ¬ (cycle 5 ≤ₛ ⟦heawood⟧) := by native_decide

/-- The McGee graph, the `(3,7)`-cage, has an induced heptagon. -/
theorem cycle_seven_induced_mcgee : cycle 7 ≤ᵢₛ ⟦mcgee⟧ := by native_decide

/-- …and no hexagon. -/
theorem not_cycle_six_subgraph_mcgee : ¬ (cycle 6 ≤ₛ ⟦mcgee⟧) := by native_decide

/-- The Tutte–Coxeter graph, the `(3,8)`-cage, has an induced octagon. -/
theorem cycle_eight_induced_tutteCoxeter : cycle 8 ≤ᵢₛ ⟦tutteCoxeter⟧ := by native_decide

/-- …and no heptagon. -/
theorem not_cycle_seven_subgraph_tutteCoxeter : ¬ (cycle 7 ≤ₛ ⟦tutteCoxeter⟧) := by native_decide

/-- The faces of the dodecahedron are induced pentagons. -/
theorem cycle_five_induced_dodecahedron : cycle 5 ≤ᵢₛ ⟦dodecahedron⟧ := by native_decide

/-- …and it has no square. -/
theorem not_cycle_four_subgraph_dodecahedron : ¬ (cycle 4 ≤ₛ ⟦dodecahedron⟧) := by native_decide

/-- The Balaban 11-cage has an induced eleven-cycle — an odd cycle in a 112-vertex cubic graph,
found in three seconds. -/
theorem cycle_eleven_induced_balaban11Cage : cycle 11 ≤ᵢₛ ⟦balaban11Cage⟧ := by native_decide

/-- The Tutte 12-cage has an induced twelve-cycle.  The largest search in this file that is not
the Desargues graph: 126 vertices, and a pattern of twelve. -/
theorem cycle_twelve_induced_tutte12Cage : cycle 12 ≤ᵢₛ ⟦tutte12Cage⟧ := by native_decide

/-! ## Claws

The three neighbours of a vertex of a triangle-free cubic graph are pairwise non-adjacent, so
every such graph has an induced `K₁,₃` — none of the gallery's cubic graphs is claw-free. -/

/-- The Petersen graph has an induced claw. -/
theorem claw_induced_petersen : ⟦claw⟧ ≤ᵢₛ petersen := by native_decide

/-- The Heawood graph has an induced claw. -/
theorem claw_induced_heawood : ⟦claw⟧ ≤ᵢₛ ⟦heawood⟧ := by native_decide

/-- The dodecahedron has an induced claw. -/
theorem claw_induced_dodecahedron : ⟦claw⟧ ≤ᵢₛ ⟦dodecahedron⟧ := by native_decide

/-! ## Kuratowski and Wagner

A graph is planar exactly when it has neither `K₅` nor `K₃,₃` as a minor, so each of the following
is one half of a planarity certificate.  The library has no notion of planarity, and these are
what stand in for it.

The negative statements are the expensive ones — a `none` from the minor search is an exhausted
search tree — which is why the planar graph here is the seven-vertex Moser spindle rather than a
polyhedron. -/

/-- The Petersen graph has a `K₅` minor: contract the five spokes. -/
theorem complete_five_minor_petersen : complete 5 ≤ₘ petersen := by native_decide

/-- The Petersen graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_petersen : bipartite 3 3 ≤ₘ petersen := by native_decide

/-- The Heawood graph has a `K₅` minor. -/
theorem complete_five_minor_heawood : complete 5 ≤ₘ ⟦heawood⟧ := by native_decide

/-- The Heawood graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_heawood : bipartite 3 3 ≤ₘ ⟦heawood⟧ := by native_decide

/-- The Grötzsch graph has a `K₅` minor. -/
theorem complete_five_minor_grotzsch : complete 5 ≤ₘ grotzsch := by native_decide

/-- The Grötzsch graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_grotzsch : bipartite 3 3 ≤ₘ grotzsch := by native_decide

/-- Tietze's graph has a `K₅` minor. -/
theorem complete_five_minor_tietze : complete 5 ≤ₘ ⟦tietze⟧ := by native_decide

/-- Tietze's graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_tietze : bipartite 3 3 ≤ₘ ⟦tietze⟧ := by native_decide

/-- **The Wagner graph is nonplanar because of `K₃,₃` alone.**  `V₈` is the Möbius–Kantor
configuration on eight vertices, and it is the graph Wagner's theorem has to name: a nonplanar
graph with no `K₅` minor at all. -/
theorem bipartite_three_three_minor_wagner : bipartite 3 3 ≤ₘ ⟦wagner⟧ := by native_decide

/-- …and it has no `K₅` minor, which is the point of it. -/
theorem not_complete_five_minor_wagner : ¬ (complete 5 ≤ₘ ⟦wagner⟧) := by native_decide

/-- **The Moser spindle is planar.**  Half of the certificate: no `K₅` minor. -/
theorem not_complete_five_minor_moserSpindle : ¬ (complete 5 ≤ₘ ⟦moserSpindle⟧) := by
  native_decide

/-- …and the other half: no `K₃,₃` minor either, so the spindle is planar.  Together with
`not_moserSpindle_hom_complete_three` below that makes it a planar graph needing four colours —
the four-colour theorem's bound, attained by seven vertices. -/
theorem not_bipartite_three_three_minor_moserSpindle : ¬ (bipartite 3 3 ≤ₘ ⟦moserSpindle⟧) := by
  native_decide

/-! ## Minor, topological minor, immersion, contraction

The Petersen graph is the standard example of the gap between the two obstruction relations: it
has a `K₅` minor, got by contracting the five spokes, but no `K₅` *subdivision*, since a branch
vertex of a subdivision keeps its degree and the Petersen graph is cubic.  `K₃,₃` has maximum
degree three and does sit inside it as a subdivision. -/

/-- **No `K₅` subdivision in the Petersen graph**: a `K₅` subdivision needs five vertices of
degree four, and every vertex here has degree three. -/
theorem not_complete_five_topMinor_petersen : ¬ (complete 5 ≤ₜₘ petersen) := by native_decide

/-- **A `K₃,₃` subdivision in the Petersen graph.**  With the two statements above, the Petersen
graph is nonplanar in both of Kuratowski's senses and in only one of Wagner's. -/
theorem bipartite_three_three_topMinor_petersen : bipartite 3 3 ≤ₜₘ petersen := by native_decide

/-- A `K₄` subdivision in the Petersen graph. -/
theorem complete_four_topMinor_petersen : complete 4 ≤ₜₘ petersen := by native_decide

/-- A `K₄` subdivision in the Heawood graph. -/
theorem complete_four_topMinor_heawood : complete 4 ≤ₜₘ ⟦heawood⟧ := by native_decide

/-- `K₄` is immersed in the Petersen graph: four vertices joined by six *edge*-disjoint trails,
which may share vertices where a subdivision's paths may not. -/
theorem complete_four_immersion_petersen : complete 4 ≤ₑ petersen := by native_decide

/-- `K₄` is immersed in the Heawood graph. -/
theorem complete_four_immersion_heawood : complete 4 ≤ₑ ⟦heawood⟧ := by native_decide

/-- **The Petersen graph contracts onto `K₅`**, which is stronger than having it as a minor:
the five spokes partition all ten vertices into connected blocks, so nothing is deleted. -/
theorem complete_five_contraction_petersen : complete 5 ≤ₚ petersen := by native_decide

/-! ## The gallery inside the gallery -/

/-- **The Petersen graph is an induced subgraph of `K(6,2)`**: the ten pairs that miss a fixed
element of the six span a copy of `K(5,2)`, and disjointness of pairs does not care what the rest
of the graph does. -/
theorem petersen_induced_kneser_six : petersen ≤ᵢₛ kneser 6 2 := by native_decide

/-- **The Petersen graph is an induced subgraph of the Hoffman–Singleton graph.**  Both are Moore
graphs — girth five and diameter two — and the 50-vertex one is full of copies of the ten-vertex
one. -/
theorem petersen_induced_hoffmanSingleton : petersen ≤ᵢₛ hoffmanSingleton := by native_decide

/-- **The Petersen graph is a quotient of the Desargues graph**, which is its bipartite double
cover: the covering map identifies the two vertices over each vertex of the Petersen graph.  The
most expensive search in this file, at about sixteen seconds. -/
theorem petersen_quotient_desargues : petersen ≤/ ⟦desargues⟧ := by native_decide

/-- It is not an induced subgraph of the Desargues graph, though — the double cover is bipartite
and the Petersen graph is not. -/
theorem not_petersen_induced_desargues : ¬ (petersen ≤ᵢₛ ⟦desargues⟧) := by native_decide

/-! ## Chromatic number, as a homomorphism

`G ≤ₕ complete k` is `k`-colourability with the colouring, so the two famous triangle-free
four-chromatic graphs can be stated here without mentioning `chromNum` at all. -/

/-- **The Grötzsch graph is not three-colourable.** -/
theorem not_grotzsch_hom_complete_three : ¬ (grotzsch ≤ₕ complete 3) := by native_decide

/-- …but it is four-colourable. -/
theorem grotzsch_hom_complete_four : grotzsch ≤ₕ complete 4 := by native_decide

/-- …and it is triangle-free, which is what makes it interesting: four colours are needed by a
graph with no `K₃` in it at all. -/
theorem not_complete_three_subgraph_grotzsch : ¬ (complete 3 ≤ₛ grotzsch) := by native_decide

/-- **The Moser spindle is not three-colourable**, which with `not_complete_five_minor_moserSpindle`
above is the standard lower bound of four for the chromatic number of the plane. -/
theorem not_moserSpindle_hom_complete_three : ¬ (⟦moserSpindle⟧ ≤ₕ complete 3) := by native_decide

/-- …and it is four-colourable. -/
theorem moserSpindle_hom_complete_four : ⟦moserSpindle⟧ ≤ₕ complete 4 := by native_decide

end IsoGraph
