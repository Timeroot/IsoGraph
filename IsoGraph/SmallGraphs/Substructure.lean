import IsoGraph.Containment
import IsoGraph.SmallGraphs.Defs

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# What sits inside what

The gallery, crossed with the containment relations of `IsoGraph/Containment/`: which named graph
is a subgraph, an induced subgraph, a minor, a topological minor, an immersion, a contraction or a
quotient of which other.

Every positive statement here carries its witness.  The searches of
`Containment/Algorithms/Cached.lean` found the maps, but what is checked at compile time is the
map: a table of vertices, a list of branch sets, a list of subdivision paths, a colouring — and
`decide +kernel` on the finitely many conditions the witness has to meet, evaluating each table
once, in the kernel, rather than once in the elaborator and again in the kernel.  So a positive
statement costs what its *witness* costs to check, which is a handful of adjacency lookups, and
not what the search cost to run.  The negative statements have no witness to give and stay on
`native_decide`, where what is run is the exhausted search tree.

Four kinds of statement, in order:

| section | pattern | says |
| --- | --- | --- |
| Girth | `cycle k` | the cage property: the shortest cycle is there, and is induced, and nothing shorter is |
| Claws | `claw` | a triangle-free cubic graph has an induced claw — the neighbours of any vertex |
| Kuratowski | `K₅`, `K₃,₃` | which of the named graphs are planar, and which of the two obstructions each nonplanar one carries |
| The gallery | a named graph | the Petersen graph inside the Kneser, Hoffman–Singleton and Desargues graphs, and the Balaban 11-cage inside the Tutte 12-cage |

and then the two four-chromatic triangle-free graphs, whose chromatic number is a statement about
homomorphisms into `complete k`, and so belongs here as much as in `SmallGraphs/Colouring.lean`.

The girth and the chromatic numbers themselves are in `SmallGraphs/Defs/` and
`SmallGraphs/Colouring.lean`; what is new here is that the cycle, or the colouring, is exhibited
as a *containment*, which is not something the invariants give back.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
-- The `disj` field of a `CGraph.TopModel` binds four vertices, and the default budget for
-- synthesising a `Decidable` instance runs out over that many nested binders.
set_option synthInstance.maxSize 400

namespace IsoGraph

-- `_root_`, because `@[toIsoGraph]` puts its restatements of the gallery's facts in
-- `IsoGraph.NamedGraphs` and `IsoGraph.SmallGraphs`, and a bare `open` inside `namespace IsoGraph`
-- would pick up those instead of the graphs themselves.
open _root_.NamedGraphs _root_.SmallGraphs

/-! ## Reading the witnesses

A witness is a table of numbers, and a number names a vertex by its place in the enumeration of
the graph's vertex type.  For the graphs built by `ofEdges` that place *is* the vertex, and the
table can be written as a `Fin n → Fin m` matrix literal; for the Kneser graph, whose vertices are
two-element subsets, and for the Grötzsch graph, whose vertices are a sum of an option of a sum,
`FinEnum.equiv` does the translating.

`ord` is the same numbering read the other way, and is what orients the edges of a pattern for
`CGraph.TopModel`: the path of an edge is stored once, at the end with the larger `ord`. -/

/-- The vertex of the Petersen graph at position `i` of its enumeration. -/
private def pv (i : Fin 10) : (CGraph.kneser 5 2).V := FinEnum.equiv.symm i

/-- The vertex of `K(6,2)` at position `i` of its enumeration. -/
private def pv6 (i : Fin 15) : (CGraph.kneser 6 2).V := FinEnum.equiv.symm i

/-- The vertex of the Grötzsch graph at position `i` of its enumeration. -/
private def gv (i : Fin 11) : NamedGraphs.grotzsch.V := FinEnum.equiv.symm i

/-- The position of a vertex in the enumeration of its graph. -/
private def ord {G : CGraph} (v : G.V) : ℕ := (FinEnum.equiv v).val

private theorem ord_inj {G : CGraph} : Function.Injective (ord (G := G)) :=
  fun _ _ h ↦ FinEnum.equiv.injective (Fin.ext h)

/-- The Grötzsch graph, as a class, is the Mycielskian of the pentagon. -/
private theorem grotzsch_eq : (grotzsch : IsoGraph) = ⟦NamedGraphs.grotzsch⟧ := by
  rw [show (grotzsch : IsoGraph) = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk]

/-- The Petersen graph, as a class, is the Kneser graph `K(5,2)`. -/
private theorem petersen_eq : (petersen : IsoGraph) = ⟦CGraph.kneser 5 2⟧ := kneser_def 5 2

/-! ## Girth, as a containment

A graph of girth `g` contains `C_g` and no shorter cycle, and the `C_g` it contains has to be
induced — a chord would close a shorter one.  That is the whole content of a cage.  The witness is
the cycle itself, listed vertex by vertex. -/

/-- The Petersen graph has an induced pentagon. -/
theorem cycle_five_induced_petersen : cycle 5 ≤ᵢₛ petersen := by
  rw [petersen_eq, cycle_def]
  exact ⟨{ toFun := fun i ↦ pv ((![0, 5, 6, 2, 9] : Fin 5 → Fin 10) i)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- The Petersen graph is triangle-free. -/
theorem not_cycle_three_subgraph_petersen : ¬ (cycle 3 ≤ₛ petersen) := by native_decide

/-- The Petersen graph has no square, so with the pentagon above its girth is five. -/
theorem not_cycle_four_subgraph_petersen : ¬ (cycle 4 ≤ₛ petersen) := by native_decide

/-- The Heawood graph, the `(3,6)`-cage, has an induced hexagon. -/
theorem cycle_six_induced_heawood : cycle 6 ≤ᵢₛ ⟦heawood⟧ := by
  rw [cycle_def]
  exact ⟨{ toFun := (![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 14)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- …and no pentagon. -/
theorem not_cycle_five_subgraph_heawood : ¬ (cycle 5 ≤ₛ ⟦heawood⟧) := by native_decide

/-- The McGee graph, the `(3,7)`-cage, has an induced heptagon. -/
theorem cycle_seven_induced_mcgee : cycle 7 ≤ᵢₛ ⟦mcgee⟧ := by
  rw [cycle_def]
  exact ⟨{ toFun := (![0, 1, 2, 3, 4, 11, 12] : Fin 7 → Fin 24)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- …and no hexagon. -/
theorem not_cycle_six_subgraph_mcgee : ¬ (cycle 6 ≤ₛ ⟦mcgee⟧) := by native_decide

/-- The Tutte–Coxeter graph, the `(3,8)`-cage, has an induced octagon. -/
theorem cycle_eight_induced_tutteCoxeter : cycle 8 ≤ᵢₛ ⟦tutteCoxeter⟧ := by
  rw [cycle_def]
  exact ⟨{ toFun := (![0, 1, 2, 3, 4, 5, 18, 17] : Fin 8 → Fin 30)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- …and no heptagon. -/
theorem not_cycle_seven_subgraph_tutteCoxeter : ¬ (cycle 7 ≤ₛ ⟦tutteCoxeter⟧) := by native_decide

/-- The faces of the dodecahedron are induced pentagons. -/
theorem cycle_five_induced_dodecahedron : cycle 5 ≤ᵢₛ ⟦dodecahedron⟧ := by
  rw [cycle_def]
  exact ⟨{ toFun := (![0, 1, 2, 12, 10] : Fin 5 → Fin 20)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- …and it has no square. -/
theorem not_cycle_four_subgraph_dodecahedron : ¬ (cycle 4 ≤ₛ ⟦dodecahedron⟧) := by native_decide

/-- The Balaban 11-cage has an induced eleven-cycle — an odd cycle in a 112-vertex cubic graph. -/
theorem cycle_eleven_induced_balaban11Cage : cycle 11 ≤ᵢₛ ⟦balaban11Cage⟧ := by
  rw [cycle_def]
  exact ⟨{ toFun := (![0, 1, 2, 3, 4, 5, 6, 17, 16, 15, 111] : Fin 11 → Fin 112)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- The Tutte 12-cage has an induced twelve-cycle. -/
theorem cycle_twelve_induced_tutte12Cage : cycle 12 ≤ᵢₛ ⟦tutte12Cage⟧ := by
  rw [cycle_def]
  exact ⟨{ toFun := (![0, 1, 2, 3, 4, 5, 6, 7, 20, 19, 18, 17] : Fin 12 → Fin 126)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-! ## Claws

The three neighbours of a vertex of a triangle-free cubic graph are pairwise non-adjacent, so
every such graph has an induced `K₁,₃` — none of the gallery's cubic graphs is claw-free.  The
witness is a vertex and its three neighbours. -/

/-- The Petersen graph has an induced claw. -/
theorem claw_induced_petersen : ⟦claw⟧ ≤ᵢₛ petersen := by
  rw [petersen_eq]
  exact ⟨{ toFun := Sum.elim (fun _ ↦ pv 0) (fun i ↦ pv ((![5, 8, 9] : Fin 3 → Fin 10) i))
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- The Heawood graph has an induced claw. -/
theorem claw_induced_heawood : ⟦claw⟧ ≤ᵢₛ ⟦heawood⟧ :=
  ⟨{ toFun := Sum.elim (fun _ ↦ (0 : Fin 14)) (fun i ↦ (![1, 5, 13] : Fin 3 → Fin 14) i)
     injective' := by decide +kernel
     map_adj' := by decide +kernel
     adj_map' := by decide +kernel }⟩

/-- The dodecahedron has an induced claw. -/
theorem claw_induced_dodecahedron : ⟦claw⟧ ≤ᵢₛ ⟦dodecahedron⟧ :=
  ⟨{ toFun := Sum.elim (fun _ ↦ (0 : Fin 20)) (fun i ↦ (![1, 9, 10] : Fin 3 → Fin 20) i)
     injective' := by decide +kernel
     map_adj' := by decide +kernel
     adj_map' := by decide +kernel }⟩

/-! ## Kuratowski and Wagner

A graph is planar exactly when it has neither `K₅` nor `K₃,₃` as a minor, so each of the following
is one half of a planarity certificate.  The library has no notion of planarity, and these are
what stand in for it.

The witness of a minor is its branch sets, one list of vertices per vertex of the pattern, in an
order that makes each one visibly connected: `CGraph.MinorSearch.finalOk` asks for
`CGraph.ChainConn`, that every vertex of a branch set be adjacent to a later one.  The negative
statements are the ones with nothing to exhibit — a `none` from the minor search is an exhausted
search tree — which is why the planar graph here is the seven-vertex Moser spindle rather than a
polyhedron.  The Petersen graph's two minors are in the next section, where the stronger
containments they come from are proved. -/

/-- The Heawood graph has a `K₅` minor. -/
theorem complete_five_minor_heawood : complete 5 ≤ₘ ⟦heawood⟧ := by
  rw [complete_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.complete 5).V)
    ⟨[], none, ([(0, [1, 0]), (1, [3, 2]), (2, [5, 4]), (3, [13, 8, 7, 6]), (4, [12, 11, 10, 9])] :
      List (Fin 5 × List (Fin 14))), []⟩ (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

/-- The Heawood graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_heawood : bipartite 3 3 ≤ₘ ⟦heawood⟧ := by
  rw [bipartite_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.bipartite 3 3).V)
    ⟨[], none, ([(.inl 0, [0]), (.inl 1, [2]), (.inl 2, [10, 11, 6]),
      (.inr 0, [1]), (.inr 1, [5, 4, 3]), (.inr 2, [13, 9, 8, 7])] :
      List ((Fin 3 ⊕ Fin 3) × List (Fin 14))), []⟩
    (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

/-- The Grötzsch graph has a `K₅` minor. -/
theorem complete_five_minor_grotzsch : complete 5 ≤ₘ grotzsch := by
  rw [grotzsch_eq, complete_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.complete 5).V)
    ⟨[], none, ([(0, [gv 0]), (1, [gv 1]), (2, [gv 6, gv 3, gv 2]), (3, [gv 5, gv 4]),
      (4, [gv 9, gv 8, gv 10, gv 7])] : List (Fin 5 × List NamedGraphs.grotzsch.V)), []⟩
    (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

/-- The Grötzsch graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_grotzsch : bipartite 3 3 ≤ₘ grotzsch := by
  rw [grotzsch_eq, bipartite_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.bipartite 3 3).V)
    ⟨[], none, ([(.inl 0, [gv 0]), (.inl 1, [gv 2]), (.inl 2, [gv 5]),
      (.inr 0, [gv 1]), (.inr 1, [gv 4, gv 3]), (.inr 2, [gv 10, gv 6])] :
      List ((Fin 3 ⊕ Fin 3) × List NamedGraphs.grotzsch.V)), []⟩
    (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

/-- Tietze's graph has a `K₅` minor. -/
theorem complete_five_minor_tietze : complete 5 ≤ₘ ⟦tietze⟧ := by
  rw [complete_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.complete 5).V)
    ⟨[], none, ([(0, [1, 0]), (1, [6, 2]), (2, [11, 9, 3]), (3, [8, 10, 4]), (4, [7, 5])] :
      List (Fin 5 × List (Fin 12))), []⟩ (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

/-- Tietze's graph has a `K₃,₃` minor. -/
theorem bipartite_three_three_minor_tietze : bipartite 3 3 ≤ₘ ⟦tietze⟧ := by
  rw [bipartite_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.bipartite 3 3).V)
    ⟨[], none, ([(.inl 0, [0]), (.inl 1, [4]), (.inl 2, [7, 5]),
      (.inr 0, [1]), (.inr 1, [6, 2]), (.inr 2, [10, 8, 3])] :
      List ((Fin 3 ⊕ Fin 3) × List (Fin 12))), []⟩
    (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

/-- **The Wagner graph is nonplanar because of `K₃,₃` alone.**  `V₈` is the Möbius–Kantor
configuration on eight vertices, and it is the graph Wagner's theorem has to name: a nonplanar
graph with no `K₅` minor at all. -/
theorem bipartite_three_three_minor_wagner : bipartite 3 3 ≤ₘ ⟦wagner⟧ := by
  rw [bipartite_def]
  exact ⟨CGraph.MinorSearch.ofFinal _ _ false (FinEnum.toList (CGraph.bipartite 3 3).V)
    ⟨[], none, ([(.inl 0, [0]), (.inl 1, [2]), (.inl 2, [5]),
      (.inr 0, [1]), (.inr 1, [4, 3]), (.inr 2, [7, 6])] :
      List ((Fin 3 ⊕ Fin 3) × List (Fin 8))), []⟩
    (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)⟩

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
degree three and does sit inside it as a subdivision.

The witness of a subdivision is a `CGraph.TopModel`: where each vertex of the pattern goes, and,
for each edge of the pattern, the list of vertices its path visits.  Each edge is stored once,
from the end with the larger `ord`, and the tables below are indexed that way. -/

/-- **No `K₅` subdivision in the Petersen graph**: a `K₅` subdivision needs five vertices of
degree four, and every vertex here has degree three. -/
theorem not_complete_five_topMinor_petersen : ¬ (complete 5 ≤ₜₘ petersen) := by native_decide

/-- The paths of the `K₃,₃` subdivision in the Petersen graph, indexed by `ord`. -/
private def k33PetersenSeg : ℕ → ℕ → List (Fin 10)
  | 3, 0 => [9, 0]
  | 3, 1 => [7, 3]
  | 3, 2 => [4]
  | 4, 0 => [5, 0]
  | 4, 1 => [2, 3]
  | 4, 2 => [4]
  | 5, 0 => [0]
  | 5, 1 => [3]
  | 5, 2 => [4]
  | _, _ => []

/-- **A `K₃,₃` subdivision in the Petersen graph.**  With the statement above, the Petersen graph
is nonplanar in one of Kuratowski's two senses and not the other. -/
theorem bipartite_three_three_topMinor_petersen : bipartite 3 3 ≤ₜₘ petersen := by
  rw [petersen_eq, bipartite_def]
  exact ⟨CGraph.TopModel.toTopMinorOf
    { ord := ord
      ord_inj := ord_inj
      f := fun x ↦ pv ((![0, 3, 4, 1, 6, 8] : Fin 6 → Fin 10) (FinEnum.equiv x))
      f_inj := by decide +kernel
      seg := fun x y ↦ (k33PetersenSeg (ord x) (ord y)).map pv
      isWalk := by decide +kernel
      ends := by decide +kernel
      nodup := by decide +kernel
      interior := by decide +kernel
      disj := by decide +kernel }⟩

/-- The paths of the `K₄` subdivision in the Petersen graph, indexed by `ord`. -/
private def k4PetersenSeg : ℕ → ℕ → List (Fin 10)
  | 1, 0 => [4, 6, 5, 0]
  | 2, 0 => [8, 0]
  | 2, 1 => [7, 1]
  | 3, 0 => [0]
  | 3, 1 => [1]
  | 3, 2 => [2, 3]
  | _, _ => []

/-- A `K₄` subdivision in the Petersen graph. -/
theorem complete_four_topMinor_petersen : complete 4 ≤ₜₘ petersen := by
  rw [petersen_eq, complete_def]
  exact ⟨CGraph.TopModel.toTopMinorOf
    { ord := ord
      ord_inj := ord_inj
      f := fun x ↦ pv ((![0, 1, 3, 9] : Fin 4 → Fin 10) x)
      f_inj := by decide +kernel
      seg := fun x y ↦ (k4PetersenSeg (ord x) (ord y)).map pv
      isWalk := by decide +kernel
      ends := by decide +kernel
      nodup := by decide +kernel
      interior := by decide +kernel
      disj := by decide +kernel }⟩

/-- The paths of the `K₄` subdivision in the Heawood graph, indexed by `ord`. -/
private def k4HeawoodSeg : ℕ → ℕ → List (Fin 14)
  | 1, 0 => [0]
  | 2, 0 => [3, 4, 5, 0]
  | 2, 1 => [1]
  | 3, 0 => [6, 11, 12, 13, 0]
  | 3, 1 => [8, 9, 10, 1]
  | 3, 2 => [2]
  | _, _ => []

/-- A `K₄` subdivision in the Heawood graph. -/
theorem complete_four_topMinor_heawood : complete 4 ≤ₜₘ ⟦heawood⟧ := by
  rw [complete_def]
  exact ⟨CGraph.TopModel.toTopMinorOf
    { ord := ord
      ord_inj := ord_inj
      f := (![0, 1, 2, 7] : Fin 4 → Fin 14)
      f_inj := by decide +kernel
      seg := fun x y ↦ k4HeawoodSeg (ord x) (ord y)
      isWalk := by decide +kernel
      ends := by decide +kernel
      nodup := by decide +kernel
      interior := by decide +kernel
      disj := by decide +kernel }⟩

/-- `K₄` is immersed in the Petersen graph: four vertices joined by six *edge*-disjoint trails,
which may share vertices where a subdivision's paths may not.  The subdivision above is one. -/
theorem complete_four_immersion_petersen : complete 4 ≤ₑ petersen :=
  complete_four_topMinor_petersen.isImmersionMinorOf

/-- `K₄` is immersed in the Heawood graph. -/
theorem complete_four_immersion_heawood : complete 4 ≤ₑ ⟦heawood⟧ :=
  complete_four_topMinor_heawood.isImmersionMinorOf

/-- **The Petersen graph contracts onto `K₅`**, which is stronger than having it as a minor:
the five spokes partition all ten vertices into connected blocks, so nothing is deleted. -/
theorem complete_five_contraction_petersen : complete 5 ≤ₚ petersen := by
  rw [petersen_eq, complete_def]
  exact ⟨{ toInducedMinorOf := CGraph.MinorSearch.ofFinalInd _ _
             (FinEnum.toList (CGraph.complete 5).V)
             ⟨[], none, ([(0, [pv 5, pv 0]), (1, [pv 6, pv 2]), (2, [pv 9, pv 1]),
               (3, [pv 8, pv 4]), (4, [pv 7, pv 3])] :
               List (Fin 5 × List (CGraph.kneser 5 2).V)), []⟩
             (fun x ↦ FinEnum.mem_toList x) (by decide +kernel)
           total' := by decide +kernel }⟩

/-- The Petersen graph has a `K₅` minor — the contraction above, with nothing deleted. -/
theorem complete_five_minor_petersen : complete 5 ≤ₘ petersen :=
  complete_five_contraction_petersen.isMinorOf

/-- The Petersen graph has a `K₃,₃` minor — the subdivision above, with its paths contracted. -/
theorem bipartite_three_three_minor_petersen : bipartite 3 3 ≤ₘ petersen :=
  bipartite_three_three_topMinor_petersen.isMinorOf

/-! ## The gallery inside the gallery -/

/-- **The Petersen graph is an induced subgraph of `K(6,2)`**: the ten pairs that miss a fixed
element of the six span a copy of `K(5,2)`, and disjointness of pairs does not care what the rest
of the graph does. -/
theorem petersen_induced_kneser_six : petersen ≤ᵢₛ kneser 6 2 := by
  rw [petersen_eq, kneser_def]
  exact ⟨{ toFun := fun v ↦
             pv6 ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 10 → Fin 15) (FinEnum.equiv v))
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- **The Petersen graph is an induced subgraph of the Hoffman–Singleton graph.**  Both are Moore
graphs — girth five and diameter two — and the 50-vertex one is full of copies of the ten-vertex
one. -/
theorem petersen_induced_hoffmanSingleton : petersen ≤ᵢₛ hoffmanSingleton := by
  rw [petersen_eq, hoffmanSingleton_def]
  exact ⟨{ toFun := fun v ↦
             (![0, 29, 3, 28, 27, 1, 2, 26, 25, 4] : Fin 10 → Fin 50) (FinEnum.equiv v)
           injective' := by decide +kernel
           map_adj' := by decide +kernel
           adj_map' := by decide +kernel }⟩

/-- **The Petersen graph is a quotient of the Desargues graph**, which is its bipartite double
cover: the covering map identifies the two vertices over each vertex of the Petersen graph. -/
theorem petersen_quotient_desargues : petersen ≤/ ⟦desargues⟧ := by
  rw [petersen_eq]
  exact ⟨{ toFun := fun v ↦ pv ((![0, 5, 0, 5, 6, 2, 3, 7, 1, 9,
                                  8, 6, 5, 0, 2, 6, 8, 3, 4, 0] : Fin 20 → Fin 10) v)
           surjective' := by decide +kernel
           map_adj' := by decide +kernel }⟩

/-- It is not an induced subgraph of the Desargues graph, though — the double cover is bipartite
and the Petersen graph is not. -/
theorem not_petersen_induced_desargues : ¬ (petersen ≤ᵢₛ ⟦desargues⟧) := by native_decide

/-! ### The Balaban 11-cage inside the Tutte 12-cage

Balaban found the first 11-cage by **excision** from the Tutte 12-cage.  Delete six vertices
spanning a tree — below, `0, 1, 2, 27, 28, 29`: an edge of the 12-cage together with the four
other neighbours of its two ends — and of the 120 vertices left, 112 still have degree three and
eight have lost a neighbour.  Suppress those eight, replacing each by an edge between its two
surviving neighbours, and what remains is 112 vertices and 168 edges: the Balaban 11-cage.

Read backwards that is a subdivision of the Balaban 11-cage drawn inside the Tutte 12-cage, and so
a topological minor.  Of its 168 edges, 160 are edges of the 12-cage outright and 8 are paths of
length two through the suppressed vertices `3, 17, 26, 30, 50, 80, 115, 125`.

Nothing here is searched for at compile time.  The tables below are the whole model, and what is
checked is that they fit: `CGraph.PathTwoModel` asks for the 168 walks, for the midpoints to be
distinct and to miss the 112 branch vertices, and for nothing else.  Even so the 168 walks are 176
adjacency tests in a 126-vertex graph whose edges are a list, so the check is not free — it is
about a minute.  Running down the Balaban 11-cage's own edge list with `CGraph.forall_adj_ofEdges`,
rather than over all `112²` pairs of its vertices, is what keeps it to that. -/

/-- Where the 112 branch vertices go: the vertex of the Tutte 12-cage that stands for the vertex
`i` of the Balaban 11-cage. -/
private def balF : Fin 112 → Fin 126 :=
  ![108, 109, 10, 9, 8, 7, 6, 5, 40, 41, 76, 77, 78, 67, 66, 123, 122, 121, 120, 119, 118, 117,
    116, 114, 113, 112, 111, 110, 97, 98, 99, 25, 24, 13, 14, 15, 84, 83, 82, 81, 79, 92, 91, 90,
    107, 106, 39, 38, 37, 36, 35, 18, 16, 75, 74, 73, 100, 101, 102, 103, 104, 105, 48, 47, 68, 69,
    12, 11, 32, 33, 34, 93, 94, 59, 58, 23, 22, 21, 20, 19, 46, 45, 44, 43, 42, 31, 87, 88, 89, 72,
    71, 70, 4, 95, 96, 85, 86, 65, 64, 63, 62, 61, 60, 49, 51, 52, 53, 54, 55, 56, 57, 124]

/-- The eight suppressed vertices of the Tutte 12-cage, in the order of the edges they subdivide. -/
private def balMidVtx : Fin 8 → Fin 126 := ![3, 17, 26, 30, 50, 80, 115, 125]

/-- The eight edges of the Balaban 11-cage that are subdivided, each as its pair of ends in
increasing order. -/
private def balMidKey : Fin 8 → ℕ × ℕ :=
  ![(91, 92), (51, 52), (30, 31), (85, 86), (103, 104), (39, 40), (22, 23), (0, 111)]

/-- Which of the eight, if any, the edge with ends `a ≤ b` is. -/
private def balMidOf (a b : ℕ) : Option (Fin 8) :=
  (List.finRange 8).find? fun k ↦ balMidKey k == (a, b)

/-- The suppressed vertex the edge `x`–`y` runs through, if it runs through one. -/
private def balMid (x y : Fin 112) : Option (Fin 126) :=
  (balMidOf (min x.1 y.1) (max x.1 y.1)).map balMidVtx

/-- What the walk of the edge `x`–`y` has to check: one adjacency, or two. -/
private def balStep (x y : Fin 112) : Bool :=
  (balMid x y).elim (tutte12Cage.Adj (balF x) (balF y))
    fun w ↦ tutte12Cage.Adj (balF x) w && tutte12Cage.Adj w (balF y)

private theorem balF_ne_mid (z : Fin 112) (k : Fin 8) : balF z ≠ balMidVtx k := by
  revert z k; decide

private theorem balMidVtx_inj : Function.Injective balMidVtx := by decide +kernel

/-- Two pairs of vertices with the same smaller and the same larger end are the same pair. -/
private theorem sym2_of_minmax {n : ℕ} {x y x' y' : Fin n} (h1 : min x.1 y.1 = min x'.1 y'.1)
    (h2 : max x.1 y.1 = max x'.1 y'.1) : s(x, y) = s(x', y') := by
  have h : (x.1 = x'.1 ∧ y.1 = y'.1) ∨ (x.1 = y'.1 ∧ y.1 = x'.1) := by
    simp only [Nat.min_def, Nat.max_def] at h1 h2
    split_ifs at h1 h2 <;> omega
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Sym2.eq_iff.2 (Or.inl ⟨Fin.ext ha, Fin.ext hb⟩)
  · exact Sym2.eq_iff.2 (Or.inr ⟨Fin.ext ha, Fin.ext hb⟩)

/-- **The subdivision of the Balaban 11-cage that the Tutte 12-cage contains.** -/
private def balExcision : balaban11Cage.PathTwoModel tutte12Cage where
  f := balF
  f_inj := List.nodup_ofFn.1 (by decide +kernel)
  mid := balMid
  mid_symm x y := by simp only [balMid, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]
  step x y h := by
    show balStep x y = true
    exact CGraph.forall_adj_ofEdges balStep (by decide +kernel) h
  mid_ne_f := by
    rintro x y w hw z
    obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 hw
    exact balF_ne_mid z k
  mid_inj := by
    rintro x y x' y' w hw hw'
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨k', hk', hv⟩ := Option.map_eq_some_iff.1 hw'
    have hkk : k' = k := balMidVtx_inj hv
    subst hkk
    have hx := List.find?_some hk
    have hx' := List.find?_some hk'
    simp only [beq_iff_eq] at hx hx'
    have heq := hx.symm.trans hx'
    exact sym2_of_minmax (congrArg Prod.fst heq) (congrArg Prod.snd heq)

/-- **The Balaban 11-cage is a topological minor of the Tutte 12-cage** — the excision that first
produced it, read as a containment. -/
theorem balaban11Cage_topMinor_tutte12Cage : ⟦balaban11Cage⟧ ≤ₜₘ ⟦tutte12Cage⟧ :=
  ⟨CGraph.TopModel.toTopMinorOf (balExcision.toTopModel ord ord_inj)⟩

/-- …hence a minor of it, and an immersion in it. -/
theorem balaban11Cage_minor_tutte12Cage : ⟦balaban11Cage⟧ ≤ₘ ⟦tutte12Cage⟧ :=
  balaban11Cage_topMinor_tutte12Cage.isMinorOf

@[inherit_doc balaban11Cage_minor_tutte12Cage]
theorem balaban11Cage_immersion_tutte12Cage : ⟦balaban11Cage⟧ ≤ₑ ⟦tutte12Cage⟧ :=
  balaban11Cage_topMinor_tutte12Cage.isImmersionMinorOf

/-! ## Chromatic number, as a homomorphism

`G ≤ₕ complete k` is `k`-colourability with the colouring, so the two famous triangle-free
four-chromatic graphs can be stated here without mentioning `chromNum` at all.  The witness of a
`k`-colouring is the list of colours. -/

/-- **The Grötzsch graph is not three-colourable.** -/
theorem not_grotzsch_hom_complete_three : ¬ (grotzsch ≤ₕ complete 3) := by native_decide

/-- …but it is four-colourable. -/
theorem grotzsch_hom_complete_four : grotzsch ≤ₕ complete 4 := by
  rw [grotzsch_eq, complete_def]
  exact ⟨⟨fun v ↦ (![1, 0, 1, 2, 0, 1, 2, 1, 2, 3, 0] : Fin 11 → Fin 4) (FinEnum.equiv v),
    by intro a b h; revert a b h; decide⟩⟩

/-- …and it is triangle-free, which is what makes it interesting: four colours are needed by a
graph with no `K₃` in it at all. -/
theorem not_complete_three_subgraph_grotzsch : ¬ (complete 3 ≤ₛ grotzsch) := by native_decide

/-- **The Moser spindle is not three-colourable**, which with `not_complete_five_minor_moserSpindle`
above is the standard lower bound of four for the chromatic number of the plane. -/
theorem not_moserSpindle_hom_complete_three : ¬ (⟦moserSpindle⟧ ≤ₕ complete 3) := by native_decide

/-- …and it is four-colourable. -/
theorem moserSpindle_hom_complete_four : ⟦moserSpindle⟧ ≤ₕ complete 4 := by
  rw [complete_def]
  exact ⟨⟨(![0, 1, 2, 0, 1, 2, 3] : Fin 7 → Fin 4), by intro a b h; revert a b h; decide⟩⟩

end IsoGraph
