import IsoGraph.Invariants.Certificates
import IsoGraph.Graphs.SRG
import IsoGraph.Graphs.Polyhedra

/-!
# A gallery of named graphs

The graphs that have proper names but are too big for `IsoGraph/Graphs/NamedSmallGraphs.lean` and
are not strongly regular, so miss `IsoGraph/Graphs/SRG.lean` as well: the cubic cages, the
generalized Petersen graphs, two Platonic solids, and a handful of sporadic graphs.  For each one
the gallery records the order, the number of edges, the degree, connectivity, whether the graph is
bipartite, and the girth.

The gallery is five modules, all of them in the `NamedGraphs` namespace.  This one holds the cages
up to `balaban10Cage`, the generalized Petersen graphs, the sporadic graphs and four last graphs
with names; `IsoGraph/Graphs/NamedSolids.lean` holds the Archimedean and Catalan solids;
`IsoGraph/Graphs/NamedCages.lean` the Harries, Harries–Wong, Gray and Foster graphs; and
`IsoGraph/Graphs/Balaban11Cage.lean` and `IsoGraph/Graphs/Tutte12Cage.lean` one graph each.  The
split is for build time: the girth proofs of the last three dominate it, and as separate modules
they are checked in parallel.  The table below indexes all five.

| graph                    |   n |   E | degree | girth | bipartite |
|--------------------------|-----|-----|--------|-------|-----------|
| `heawood`                |  14 |  21 |      3 |     6 | yes       |
| `mcgee`                  |  24 |  36 |      3 |     7 | no        |
| `tutteCoxeter`           |  30 |  45 |      3 |     8 | yes       |
| `franklin`               |  12 |  18 |      3 |     4 | yes       |
| `pappus`                 |  18 |  27 |      3 |     6 | yes       |
| `folkman`                |  20 |  40 |      4 |     4 | yes       |
| `frucht`                 |  12 |  18 |      3 |     3 | no        |
| `durer`                  |  12 |  18 |      3 |     3 | no        |
| `mobiusKantor`           |  16 |  24 |      3 |     6 | yes       |
| `dodecahedron`           |  20 |  30 |      3 |     5 | no        |
| `desargues`              |  20 |  30 |      3 |     6 | yes       |
| `nauru`                  |  24 |  36 |      3 |     6 | yes       |
| `coxeter`                |  28 |  42 |      3 |     7 | no        |
| `wagner`                 |   8 |  12 |      3 |     4 | no        |
| `chvatal`                |  12 |  24 |      4 |     4 | no        |
| `icosahedron`            |  12 |  30 |      5 |     3 | no        |
| `tutte`                  |  46 |  69 |      3 |     4 | no        |
| `moserSpindle`           |   7 |  11 |    3–4 |     3 | no        |
| `grotzsch`               |  11 |  20 |    3–5 |     4 | no        |
| `herschel`               |  11 |  18 |    3–4 |     4 | yes       |
| `tietze`                 |  12 |  18 |      3 |     3 | no        |
| `truncatedTetrahedron`   |  12 |  18 |      3 |     3 | no        |
| `bidiakisCube`           |  12 |  18 |      3 |     4 | no        |
| `robertson`              |  19 |  38 |      4 |     5 | no        |
| `dyck`                   |  32 |  48 |      3 |     6 | yes       |
| `balaban10Cage`          |  70 | 105 |      3 |    10 | yes       |
| `cuboctahedron`          |  12 |  24 |      4 |     3 | no        |
| `truncatedCube`          |  24 |  36 |      3 |     3 | no        |
| `truncatedOctahedron`    |  24 |  36 |      3 |     4 | yes       |
| `icosidodecahedron`      |  30 |  60 |      4 |     3 | no        |
| `truncatedIcosahedron`   |  60 |  90 |      3 |     5 | no        |
| `gray`                   |  54 |  81 |      3 |     8 | yes       |
| `harries`                |  70 | 105 |      3 |    10 | yes       |
| `harriesWong`            |  70 | 105 |      3 |    10 | yes       |
| `foster`                 |  90 | 135 |      3 |    10 | yes       |
| `balaban11Cage`          | 112 | 168 |      3 |    11 | no        |
| `tutte12Cage`            | 126 | 189 |      3 |    12 | yes       |
| `holt`                   |  27 |  54 |      4 |     5 | no        |
| `flowerSnark`            |  20 |  30 |      3 |     5 | no        |
| `biggsSmith`             | 102 | 153 |      3 |     9 | no        |
| `ljubljana`              | 112 | 168 |      3 |    10 | yes       |
| `triakisTetrahedron`     |   8 |  18 |    3–6 |     3 | no        |
| `rhombicDodecahedron`    |  14 |  24 |    3–4 |     4 | yes       |
| `triakisOctahedron`      |  14 |  36 |    3–8 |     3 | no        |
| `tetrakisHexahedron`     |  14 |  36 |    4–6 |     3 | no        |
| `rhombicTriacontahedron` |  32 |  60 |    3–5 |     4 | yes       |
| `pentakisDodecahedron`   |  32 |  90 |    5–6 |     3 | no        |

Three remarks on what is and is not here.

* A *`(k, g)`-cage* is a smallest `k`-regular graph of girth `g`.  A cubic cage is known for every
  girth from three to twelve, and all of them are here except the `(3, 9)`-cage on fifty-eight
  vertices: `complete 4`, `bipartite 3 3`, `SRG.petersen`, `heawood`, `mcgee`, `tutteCoxeter`,
  `balaban10Cage`, `balaban11Cage` and `tutte12Cage`, the first three defined elsewhere.  Girth
  ten is the one place where the cage is not unique: `balaban10Cage`, `harries` and `harriesWong`
  are three different graphs on seventy vertices, told apart by the orders of their automorphism
  groups, 120, 24 and 80.  `robertson` is the cage of the next degree up, `(4, 5)`.  Three cubic
  graphs here are famous without being cages: `coxeter`, of girth seven, where `mcgee` is
  smaller; `gray`, the smallest cubic semisymmetric graph, edge-transitive but not
  vertex-transitive; and `foster`, the cubic distance-transitive graph on ninety vertices.
  Minimality is a statement about *all* graphs of a given order and so is out of reach here; what
  the file proves is that each of these graphs is regular of the right degree and of the right
  girth.  Girth nine is the one gap, and `biggsSmith` is as close as a name gets to it: the
  eighteen `(3, 9)`-cages on fifty-eight vertices are anonymous, while the Biggs–Smith graph is
  the cubic distance-transitive graph of girth nine.
* The other three sporadic additions are chosen for a symmetry property each.  `holt` is the
  smallest half-transitive graph — vertex- and edge-transitive but not arc-transitive, since its
  automorphism group has order fifty-four and an arc-transitive graph on twenty-seven vertices of
  degree four would need at least a hundred and eight.  `ljubljana` is semi-symmetric, like
  `gray`.  And `flowerSnark` is the smallest flower snark: a bridgeless cubic graph whose edges
  need four colours, as `SRG.petersen`, the smallest snark of all, also does.  None of the three
  properties named in this paragraph is proved here — they are what the graphs are *for* — but
  the order, size, degree, connectivity, bipartiteness and girth of each are.
* Of the five Platonic solids, `complete 4` is the tetrahedron, `hypercube 3` the cube,
  `cocktailParty 3` the octahedron, and `dodecahedron` and `icosahedron` are defined here — the
  first as `gp 10 2` and the second from the face list of `IsoGraph/Graphs/Polyhedra.lean`.
  `gp_four_one_iso_hypercube` identifies the cube as a generalized Petersen graph too.  Six of
  the thirteen Archimedean solids follow, `truncatedTetrahedron` here and the rest in
  `IsoGraph/Graphs/NamedSolids.lean`: the four truncations `truncatedTetrahedron`,
  `truncatedCube`, `truncatedOctahedron` and `truncatedIcosahedron` — the last being the football
  — and the two rectifications `cuboctahedron` and `icosidodecahedron`.  Their six duals, the
  Catalan solids `triakisTetrahedron`, `triakisOctahedron`, `tetrakisHexahedron`,
  `pentakisDodecahedron`, `rhombicDodecahedron` and `rhombicTriacontahedron`, close the section.
  `herschel` is the smallest non-Hamiltonian polyhedron.

## Proof style

Two certificates replace the `Decidable` instances that would otherwise be needed.

* `isConnected_of_backEdge`: numbering the vertices so that every vertex other than the first has
  a neighbour with a smaller number is enough for connectivity.  This is checked by a single
  `native_decide` over `n²` adjacency queries — Mathlib's `Decidable Connected` instance, by
  contrast, is unusable at this size.
* `walkOn`, feeding `not_isBipartite_of_odd_walk`: an odd closed walk written as a cyclic list of
  vertex numbers.  For the graphs of girth three a triangle is cheaper, and
  `not_isBipartite_of_triangle` is used instead.

Bipartiteness itself is always witnessed by an explicit two-colouring, never searched for: the
parity of the vertex number works for every graph here given by an LCF code, and
`(i + i / n) % 2` for the bipartite generalized Petersen graphs.

One wrinkle in the girth proofs: the distinctness side conditions of `exists_cycle_of_square` and
`exists_cycle_of_pentagon` are stated at the vertex type `G.V`, where `decide` does not always
find the `DecidableEq` instance, so they go through `Fin.ne_of_val_ne` instead.

Above girth five those per-length lemmas run out, and the cages go through the cycle lists of
`IsoGraph/Invariants/Certificates.lean` instead; see "The girth of the cages" below.  The one thing
that needs care there is *how* the search for a short cycle is phrased.  Written as a
nested `∀` over vertices, the decision procedure enumerates the whole vertex type at every level
— `30⁷` for `tutteCoxeter`, which never finishes.  Written as `∀ b ∈ nb a`, it walks only along
edges, which is `30 · 3⁶` — but recomputing `nb` from the adjacency function costs a millisecond
a call.  Precomputing the neighbour lists once, in a top-level `def`, is what brings the deepest
search down to about two seconds.  The wrappers erase the previous vertex at each step, so a
cubic graph branches two ways rather than three after the first: `126 · 3 · 2¹⁰` for
`tutte12Cage` in place of `126 · 3¹¹`, a factor of about ninety.  Even so, the girth proofs of
`balaban11Cage` and `tutte12Cage` are the only declarations in the gallery that need more than the
default heartbeat budget.
-/

set_option maxRecDepth 4000
-- the girth conditions nest bounded quantifiers over the graph's vertex type, and each level costs
-- a `Fintype` and a `DecidableEq` that now come through the graph's `FinEnum`; the default
-- instance-search budget runs out around the sixth
set_option synthInstance.maxSize 512

namespace NamedGraphs

open CGraph CGraph.Enum

/-! ## The cubic cages

`heawood` is the `(3,6)`-cage — the incidence graph of the Fano plane — `mcgee` the `(3,7)`-cage,
and `tutteCoxeter` the `(3,8)`-cage, also known as the Levi graph of the generalized quadrangle
`GQ(2,2)`.  The `(3,5)`-cage is the Petersen graph, in `IsoGraph/Graphs/SRG.lean`. -/

/-- The Heawood graph: the point–line incidence graph of the Fano plane, and the `(3,6)`-cage. -/
abbrev heawood : CGraph := lcf [5, -5] 7

/-- The McGee graph, the `(3,7)`-cage. -/
abbrev mcgee : CGraph := lcf [12, 7, -7] 8

/-- The Tutte–Coxeter graph, or Levi graph of `GQ(2,2)`: the `(3,8)`-cage. -/
abbrev tutteCoxeter : CGraph := lcf [-13, -9, 7, -7, 9, 13] 5

@[simp] theorem card_heawood : FinEnum.card heawood.V = 14 := card_ofEdges _ _

@[simp] theorem E_heawood : heawood.E = 21 := by native_decide

theorem isRegularWith_heawood : heawood.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 14) (by native_decide)

@[simp] theorem isConnected_heawood : heawood.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_heawood : heawood.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem card_mcgee : FinEnum.card mcgee.V = 24 := card_ofEdges _ _

@[simp] theorem E_mcgee : mcgee.E = 36 := by native_decide

theorem isRegularWith_mcgee : mcgee.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_mcgee : mcgee.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 24)) (by norm_num) (by native_decide)

/-- The McGee graph has odd girth: `0 - 12 - 11 - 4 - 3 - 2 - 1 - 0` is a seven-cycle. -/
@[simp] theorem not_isBipartite_mcgee : ¬ mcgee.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 24 (by norm_num) [0, 12, 11, 4, 3, 2, 1]) 7 rfl
    (by decide) rfl

@[simp] theorem card_tutteCoxeter : FinEnum.card tutteCoxeter.V = 30 := card_ofEdges _ _

@[simp] theorem E_tutteCoxeter : tutteCoxeter.E = 45 := by native_decide

theorem isRegularWith_tutteCoxeter : tutteCoxeter.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 30) (by native_decide)

@[simp] theorem isConnected_tutteCoxeter : tutteCoxeter.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 30)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_tutteCoxeter : tutteCoxeter.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-! ## More graphs from LCF codes -/

/-- The Franklin graph: the `Möbius–Kantor`-like cubic graph on twelve vertices, an embedding of
the Klein bottle with six hexagonal faces. -/
abbrev franklin : CGraph := lcf [5, -5] 6

/-- The Pappus graph: the incidence graph of the Pappus configuration `9₃`. -/
abbrev pappus : CGraph := lcf [5, 7, -7, 7, -7, -5] 3

/-- The Folkman graph: the smallest semi-symmetric graph, that is, the smallest graph which is
edge-transitive and regular but not vertex-transitive. -/
abbrev folkman : CGraph := lcf [5, -7, -7, 5] 5

/-- The Frucht graph: a cubic graph whose only automorphism is the identity. -/
abbrev frucht : CGraph := lcf [-5, -2, -4, 2, 5, -2, 2, 5, -2, -5, 4, 2] 1

@[simp] theorem card_franklin : FinEnum.card franklin.V = 12 := card_ofEdges _ _

@[simp] theorem E_franklin : franklin.E = 18 := by native_decide

theorem isRegularWith_franklin : franklin.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_franklin : franklin.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_franklin : franklin.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem girth_franklin : franklin.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := franklin) (a := vtx 12 0)
    (b := vtx 12 5) (c := vtx 12 6) (d := vtx 12 11) (by decide) (by decide) (by decide)
    (by decide) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_pappus : FinEnum.card pappus.V = 18 := card_ofEdges _ _

@[simp] theorem E_pappus : pappus.E = 27 := by native_decide

theorem isRegularWith_pappus : pappus.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 18) (by native_decide)

@[simp] theorem isConnected_pappus : pappus.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 18)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_pappus : pappus.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem card_folkman : FinEnum.card folkman.V = 20 := card_ofEdges _ _

@[simp] theorem E_folkman : folkman.E = 40 := by native_decide

theorem isRegularWith_folkman : folkman.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_folkman : folkman.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_folkman : folkman.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem girth_folkman : folkman.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := folkman) (a := vtx 20 0)
    (b := vtx 20 5) (c := vtx 20 4) (d := vtx 20 19) (by decide) (by decide) (by decide)
    (by decide) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_frucht : FinEnum.card frucht.V = 12 := card_ofEdges _ _

@[simp] theorem E_frucht : frucht.E = 18 := by native_decide

theorem isRegularWith_frucht : frucht.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_frucht : frucht.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_frucht : ¬ frucht.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 1) (d := vtx 12 11)
    (by decide) (by decide) (by decide)

@[simp] theorem girth_frucht : frucht.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 1) (c := vtx 12 11)
    (by decide) (by decide) (by decide)

/-! ## Generalized Petersen graphs

`GP(n, k)` is the outer `n`-cycle, the inner circulant of step `k`, and the spokes between them.
The Petersen graph itself is `GP(5, 2)`, the `n`-prism is `GP(n, 1)`. -/

/-- The Dürer graph `GP(6, 2)`, from Dürer's *Melencolia I*. -/
abbrev durer : CGraph := gp 6 2

/-- The Möbius–Kantor graph `GP(8, 3)`, the generalized Petersen graph on sixteen vertices. -/
abbrev mobiusKantor : CGraph := gp 8 3

/-- The dodecahedron `GP(10, 2)`, the skeleton of the Platonic solid. -/
abbrev dodecahedron : CGraph := gp 10 2

/-- The Desargues graph `GP(10, 3)`: the bipartite double cover of the Petersen graph, and the
incidence graph of the Desargues configuration `10₃`. -/
abbrev desargues : CGraph := gp 10 3

/-- The Nauru graph `GP(12, 5)`, the Levi graph of the Möbius–Kantor configuration `12₃`. -/
abbrev nauru : CGraph := gp 12 5

/-- `GP(5, 2)` is the Petersen graph, the graph the family is named after. -/
@[toIsoGraph gp_five_two_iso_petersen]
noncomputable def gpFiveTwoIso : gp 5 2 ≃cg SRG.petersen := isoOfKeyEq (by native_decide)

/-- `GP(6, 1)` is the hexagonal prism: the spokes are the rungs and `k = 1` makes the inner cycle a
copy of the outer one. -/
@[toIsoGraph gp_six_one_iso_prism]
noncomputable def gpSixOneIso : gp 6 1 ≃cg prism 6 := isoOfKeyEq (by native_decide)

/-- `GP(4, 1)` is the cube. -/
@[toIsoGraph gp_four_one_iso_hypercube]
noncomputable def gpFourOneIso : gp 4 1 ≃cg hypercube 3 := isoOfKeyEq (by native_decide)

/-- The face list `dodecahedronFaces` really does describe the dodecahedron.  The icosahedron
below is *defined* from its faces and so needs no such check, and the other three Platonic face
lists are checked in `IsoGraph/Graphs/Polyhedra.lean`. -/
noncomputable def dodecahedronFacesIso :
    ofEdges 20 (faceEdges dodecahedronFaces) ≃cg dodecahedron := isoOfKeyEq (by native_decide)

@[simp] theorem card_durer : FinEnum.card durer.V = 12 := card_ofEdges _ _

@[simp] theorem E_durer : durer.E = 18 := by native_decide

theorem isRegularWith_durer : durer.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_durer : durer.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_durer : ¬ durer.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 6) (b := vtx 12 8) (d := vtx 12 10)
    (by decide) (by decide) (by decide)

/-- The inner triangle `6 - 8 - 10` of the Dürer graph. -/
@[simp] theorem girth_durer : durer.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 6) (b := vtx 12 8) (c := vtx 12 10)
    (by decide) (by decide) (by decide)

@[simp] theorem card_mobiusKantor : FinEnum.card mobiusKantor.V = 16 := card_ofEdges _ _

@[simp] theorem E_mobiusKantor : mobiusKantor.E = 24 := by native_decide

theorem isRegularWith_mobiusKantor : mobiusKantor.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 16) (by native_decide)

@[simp] theorem isConnected_mobiusKantor : mobiusKantor.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 16)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_mobiusKantor : mobiusKantor.IsBipartite :=
  ⟨fun v ↦ decide ((v.1 + v.1 / 8) % 2 = 1), by native_decide⟩

@[simp] theorem card_dodecahedron : FinEnum.card dodecahedron.V = 20 := card_ofEdges _ _

@[simp] theorem E_dodecahedron : dodecahedron.E = 30 := by native_decide

theorem isRegularWith_dodecahedron : dodecahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_dodecahedron : dodecahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_dodecahedron : ¬ dodecahedron.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 20 (by norm_num) [0, 10, 18, 8, 9]) 5 rfl (by decide) rfl

/-- The dodecahedron has girth five: its faces are pentagons. -/
@[simp] theorem girth_dodecahedron : dodecahedron.girth = 5 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_pentagon (G := dodecahedron) (a := vtx 20 0)
    (b := vtx 20 10) (c := vtx 20 18) (d := vtx 20 8) (e := vtx 20 9) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Fin.ne_of_val_ne (by decide))
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (five_le_girth (by native_decide) (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_desargues : FinEnum.card desargues.V = 20 := card_ofEdges _ _

@[simp] theorem E_desargues : desargues.E = 30 := by native_decide

theorem isRegularWith_desargues : desargues.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_desargues : desargues.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_desargues : desargues.IsBipartite :=
  ⟨fun v ↦ decide ((v.1 + v.1 / 10) % 2 = 1), by native_decide⟩

@[simp] theorem card_nauru : FinEnum.card nauru.V = 24 := card_ofEdges _ _

@[simp] theorem E_nauru : nauru.E = 36 := by native_decide

theorem isRegularWith_nauru : nauru.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_nauru : nauru.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 24)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_nauru : nauru.IsBipartite :=
  ⟨fun v ↦ decide ((v.1 + v.1 / 12) % 2 = 1), by native_decide⟩

/-! ## Sporadic graphs -/

/-- The edges of the Coxeter graph: a seven-cycle `0 … 6` of step one, a hub `7 … 13` joined to
it, and two more heptagons `14 … 20` and `21 … 27` of steps two and three, each joined to the hub
in the same way.  Numbered so that the back-edge certificate holds. -/
def coxeterEdges : List (ℕ × ℕ) :=
  (List.range 7).flatMap fun i ↦
    [(i, (i + 1) % 7), (i, 7 + i), (7 + i, 14 + i), (7 + i, 21 + i),
      (14 + i, 14 + (i + 2) % 7), (21 + i, 21 + (i + 3) % 7)]

/-- The Coxeter graph: a cubic distance-regular graph of girth seven on 28 vertices, one of the
thirteen known cubic symmetric graphs that are not Hamiltonian. -/
abbrev coxeter : CGraph := ofEdges 28 coxeterEdges

/-- The Wagner graph, or Möbius–Kantor ladder `V₈`: the circulant on eight vertices joining each
vertex to its neighbours and its antipode. -/
abbrev wagner : CGraph := circulant 8 [1, 4]

/-- The edges of the Chvátal graph. -/
def chvatalEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 4), (0, 6), (0, 9), (1, 2), (1, 5), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4),
    (3, 7), (3, 9), (4, 5), (4, 8), (5, 10), (5, 11), (6, 10), (6, 11), (7, 8), (7, 11),
    (8, 10), (9, 10), (9, 11)]

/-- The Chvátal graph: the smallest triangle-free four-regular graph with chromatic number four. -/
abbrev chvatal : CGraph := ofEdges 12 chvatalEdges

/-- The icosahedron, the skeleton of the Platonic solid: five-regular on twelve vertices.  Its
twenty faces are `icosahedronFaces`, so `0` is the north pole, `1, …, 5` the northern ring,
`6, …, 10` the southern one and `11` the south pole. -/
abbrev icosahedron : CGraph := ofEdges 12 (faceEdges icosahedronFaces)

/-- The edges of the Tutte graph. -/
def tutteEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 26), (2, 10), (2, 11), (3, 18), (3, 19), (4, 5), (4, 33),
    (5, 6), (5, 29), (6, 7), (6, 27), (7, 8), (7, 14), (8, 9), (8, 38), (9, 10), (9, 37),
    (10, 39), (11, 12), (11, 39), (12, 13), (12, 35), (13, 14), (13, 15), (14, 34), (15, 16),
    (15, 22), (16, 17), (16, 44), (17, 18), (17, 43), (18, 45), (19, 20), (19, 45), (20, 21),
    (20, 41), (21, 22), (21, 23), (22, 40), (23, 24), (23, 27), (24, 25), (24, 32), (25, 26),
    (25, 31), (26, 33), (27, 28), (28, 29), (28, 32), (29, 30), (30, 31), (30, 33), (31, 32),
    (34, 35), (34, 38), (35, 36), (36, 37), (36, 39), (37, 38), (40, 41), (40, 44), (41, 42),
    (42, 43), (42, 45), (43, 44)]

/-- The Tutte graph: a cubic planar three-connected graph with no Hamiltonian cycle, Tutte's 1946
counterexample to Tait's conjecture. -/
abbrev tutte : CGraph := ofEdges 46 tutteEdges

/-- The edges of the Moser spindle: two rhombi `0-1-3-2` and `0-4-6-5` sharing the vertex `0`,
with the far vertices `3` and `6` joined. -/
def moserSpindleEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (0, 4), (0, 5), (4, 5), (4, 6), (5, 6), (3, 6)]

/-- The Moser spindle: a unit-distance graph in the plane with chromatic number four, the classic
lower bound for the Hadwiger–Nelson problem. -/
abbrev moserSpindle : CGraph := ofEdges 7 moserSpindleEdges

/-- The Grötzsch graph, the Mycielskian of the pentagon: triangle-free with chromatic number
four, and the smallest such graph. -/
abbrev grotzsch : CGraph := mycielskian (cycle 5)

@[simp] theorem card_coxeter : FinEnum.card coxeter.V = 28 := card_ofEdges _ _

@[simp] theorem E_coxeter : coxeter.E = 42 := by native_decide

theorem isRegularWith_coxeter : coxeter.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 28) (by native_decide)

@[simp] theorem isConnected_coxeter : coxeter.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 28)) (by norm_num) (by native_decide)

/-- The first heptagon of the Coxeter graph is an odd cycle. -/
@[simp] theorem not_isBipartite_coxeter : ¬ coxeter.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 28 (by norm_num) [0, 1, 2, 3, 4, 5, 6]) 7 rfl
    (by decide) rfl

@[simp] theorem card_wagner : FinEnum.card wagner.V = 8 := card_circulant _ _

@[simp] theorem E_wagner : wagner.E = 12 := by native_decide

theorem isRegularWith_wagner : wagner.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 8) (by native_decide)

@[simp] theorem isConnected_wagner : wagner.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 8)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_wagner : ¬ wagner.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 8 (by norm_num) [0, 1, 2, 3, 7]) 5 rfl (by decide) rfl

@[simp] theorem girth_wagner : wagner.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := wagner) (a := vtx 8 0) (b := vtx 8 1)
    (c := vtx 8 5) (d := vtx 8 4) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_chvatal : FinEnum.card chvatal.V = 12 := card_ofEdges _ _

@[simp] theorem E_chvatal : chvatal.E = 24 := by native_decide

theorem isRegularWith_chvatal : chvatal.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_chvatal : chvatal.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_chvatal : ¬ chvatal.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 12 (by norm_num) [0, 1, 2, 3, 4]) 5 rfl (by decide) rfl

/-- The Chvátal graph is triangle-free, and `0 - 1 - 2 - 6 - 0` is a square. -/
@[simp] theorem girth_chvatal : chvatal.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := chvatal) (a := vtx 12 0) (b := vtx 12 1)
    (c := vtx 12 2) (d := vtx 12 6) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_icosahedron : FinEnum.card icosahedron.V = 12 := card_ofEdges _ _

@[simp] theorem E_icosahedron : icosahedron.E = 30 := by native_decide

theorem isRegularWith_icosahedron : icosahedron.IsRegularWith 5 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_icosahedron : icosahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

/-- The icosahedron has triangular faces. -/
@[simp] theorem not_isBipartite_icosahedron : ¬ icosahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 1) (d := vtx 12 2)
    (by native_decide) (by native_decide) (by native_decide)

/-- The icosahedron has girth three: `0 - 1 - 2 - 0` is the first of the faces round the north
pole. -/
@[simp] theorem girth_icosahedron : icosahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 1) (c := vtx 12 2)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_tutte : FinEnum.card tutte.V = 46 := card_ofEdges _ _

@[simp] theorem E_tutte : tutte.E = 69 := by native_decide

theorem isRegularWith_tutte : tutte.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 46) (by native_decide)

@[simp] theorem isConnected_tutte : tutte.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 46)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_tutte : ¬ tutte.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 46 (by norm_num) [4, 5, 29, 30, 33]) 5 rfl (by decide) rfl

@[simp] theorem girth_tutte : tutte.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := tutte) (a := vtx 46 1) (b := vtx 46 4)
    (c := vtx 46 33) (d := vtx 46 26) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_moserSpindle : FinEnum.card moserSpindle.V = 7 := card_ofEdges _ _

@[simp] theorem E_moserSpindle : moserSpindle.E = 11 := by native_decide

@[simp] theorem degSequence_moserSpindle :
    moserSpindle.degSequence = [3, 3, 3, 3, 3, 3, 4] := by native_decide

@[simp] theorem isConnected_moserSpindle : moserSpindle.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 7)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_moserSpindle : ¬ moserSpindle.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 7 0) (b := vtx 7 1) (d := vtx 7 2)
    (by decide) (by decide) (by decide)

@[simp] theorem girth_moserSpindle : moserSpindle.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 7 0) (b := vtx 7 1) (c := vtx 7 2)
    (by decide) (by decide) (by decide)

@[simp] theorem card_grotzsch : FinEnum.card grotzsch.V = 11 := by native_decide

@[simp] theorem E_grotzsch : grotzsch.E = 20 := by native_decide

/-- The Grötzsch graph is not regular: the pentagon has degree four, its shadows degree three,
and the apex degree five. -/
@[simp] theorem degSequence_grotzsch :
    grotzsch.degSequence = [3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5] := by native_decide

@[simp] theorem isConnected_grotzsch : grotzsch.IsConnected :=
  isConnected_mycielskian (by decide)

@[simp] theorem not_isBipartite_grotzsch : ¬ grotzsch.IsBipartite :=
  not_isBipartite_mycielskian (a := vtx 5 0) (b := vtx 5 1) (by decide)

/-- The Grötzsch graph is triangle-free — that is the point of the Mycielskian — and
`apex - 0' - 1 - 2' - apex` is a square. -/
@[simp] theorem girth_grotzsch : grotzsch.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := grotzsch) (a := none)
    (b := some (Sum.inr (vtx 5 0))) (c := some (Sum.inl (vtx 5 1)))
    (d := some (Sum.inr (vtx 5 2)))
    (by decide) (by decide) (by decide) (by decide)
    (Ne.symm (Option.some_ne_none _))
    (fun h ↦ absurd (Sum.inr.inj (Option.some.inj h)) (Fin.ne_of_val_ne (by decide)))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

/-! ## Coincidences

Several of the graphs above have a second standard description; the canonical keys of
`IsoGraph/Enum` decide the isomorphisms. -/

/-- The Möbius–Kantor graph in LCF notation. -/
@[toIsoGraph mobiusKantor_lcf]
noncomputable def mobiusKantorLcfIso : lcf [5, -5] 8 ≃cg mobiusKantor :=
  isoOfKeyEq (by native_decide)

/-- The Desargues graph in LCF notation. -/
@[toIsoGraph desargues_lcf]
noncomputable def desarguesLcfIso : lcf [5, -5, 9, -9] 5 ≃cg desargues :=
  isoOfKeyEq (by native_decide)

/-- The dodecahedron in LCF notation. -/
@[toIsoGraph dodecahedron_lcf]
noncomputable def dodecahedronLcfIso :
    lcf [10, 7, 4, -4, -7, 10, -4, 7, -7, 4] 2 ≃cg dodecahedron := isoOfKeyEq (by native_decide)

/-- The Nauru graph in LCF notation. -/
@[toIsoGraph nauru_lcf]
noncomputable def nauruLcfIso : lcf [5, -9, 7, -7, 9, -5] 4 ≃cg nauru :=
  isoOfKeyEq (by native_decide)

/-! ## More named graphs

Seven more graphs with proper names: a polyhedron, a snark-adjacent cubic graph, an Archimedean
solid, the smallest four-regular graph of girth five, and three more cubic graphs, the last of
them a `(3, 10)`-cage. -/

/-- The edges of the Herschel graph, numbered so that the back-edge certificate holds. -/
def herschelEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (2, 5), (2, 7), (3, 7), (3, 8), (4, 6), (4, 8),
   (5, 9), (5, 10), (6, 10), (7, 9), (8, 9), (8, 10)]

/-- The Herschel graph: the smallest non-Hamiltonian polyhedral graph, on eleven vertices. -/
abbrev herschel : CGraph := ofEdges 11 herschelEdges

/-- The edges of Tietze's graph: the Petersen graph with one vertex blown up into a triangle. -/
def tietzeEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7), (3, 8), (3, 9), (4, 6), (4, 10), (5, 7),
   (5, 11), (6, 11), (7, 10), (8, 9), (8, 10), (9, 11)]

/-- Tietze's graph: the cubic graph whose embedding in the Möbius strip subdivides it into six
mutually adjacent regions. -/
abbrev tietze : CGraph := ofEdges 12 tietzeEdges

/-- The truncated tetrahedron: the Archimedean solid with four hexagonal and four triangular
faces, and the smallest of the thirteen.  It is the tetrahedron with its corners cut off, so its
twelve vertices are the twelve arcs of `tetrahedronFaces`. -/
abbrev truncatedTetrahedron : CGraph := ofEdges 12 (truncEdges tetrahedronFaces)

/-- The edges of the Robertson graph, numbered so that the back-edge certificate holds. -/
def robertsonEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 4), (0, 15), (0, 18), (1, 2), (1, 8), (1, 12), (2, 3), (2, 6), (2, 17), (3, 4),
   (3, 11), (3, 14), (4, 5), (4, 9), (5, 6), (5, 12), (5, 16), (6, 7), (6, 10), (7, 8), (7, 14),
   (7, 18), (8, 9), (8, 16), (9, 10), (9, 13), (10, 11), (10, 15), (11, 12), (11, 18), (12, 13),
   (13, 14), (13, 17), (14, 15), (15, 16), (16, 17), (17, 18)]

/-- The Robertson graph: the unique `(4, 5)`-cage, the smallest four-regular graph of girth
five. -/
abbrev robertson : CGraph := ofEdges 19 robertsonEdges

/-- The Bidiakis cube: the cube with two opposite faces subdivided by a chord each. -/
abbrev bidiakisCube : CGraph := lcf [-6, 4, -4] 4

/-- The Dyck graph: the cubic symmetric graph on thirty-two vertices. -/
abbrev dyck : CGraph := lcf [5, -5, 13, -13] 8

/-- The LCF code of the Balaban 10-cage. -/
def balabanCode : List ℤ :=
  [-9, -25, -19, 29, 13, 35, -13, -29, 19, 25, 9, -29, 29, 17, 33, 21, 9, -13, -31, -9, 25, 17, 9,
    -31, 27, -9, 17, -19, -29, 27, -17, -9, -29, 33, -25, 25, -21, 17, -17, 29, 35, -29, 17, -17,
    21, -25, 25, -33, 29, 9, 17, -27, 29, 19, -17, 9, -27, 31, -9, -17, -25, 9, 31, 13, -9, -21,
    -33, -17, -29, 29]

/-- The Balaban 10-cage: one of the three `(3, 10)`-cages, told apart from the Harries and
Harries–Wong graphs by its automorphism group of order eighty.  Spelled out as `ofEdges 70` rather
than as `lcf balabanCode 1` so that the vertex type is literally `Fin 70`; the two are the same
graph. -/
abbrev balaban10Cage : CGraph := ofEdges 70 (lcfEdges balabanCode 1)

@[simp] theorem card_herschel : FinEnum.card herschel.V = 11 := card_ofEdges _ _

@[simp] theorem E_herschel : herschel.E = 18 := by native_decide

/-- The Herschel graph is not regular: it has three vertices of degree four. -/
@[simp] theorem degSequence_herschel :
    herschel.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4] := by native_decide

@[simp] theorem isConnected_herschel : herschel.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 11)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_herschel : herschel.IsBipartite :=
  ⟨fun v ↦ decide (v.1 ∈ [0, 5, 6, 7, 8]), by native_decide⟩

/-- The Herschel graph has girth four: `0 - 1 - 5 - 2 - 0` is a square. -/
@[simp] theorem girth_herschel : herschel.girth = 4 := by
  have hnac : ¬ herschel.IsAcyclic :=
    not_isAcyclic_of_cycleList (vtx 11 0) [vtx 11 1, vtx 11 5, vtx 11 2]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  refine le_antisymm ?_ (four_le_girth (by native_decide) hnac)
  exact girth_le_of_cycleList (vtx 11 0) [vtx 11 1, vtx 11 5, vtx 11 2]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_tietze : FinEnum.card tietze.V = 12 := card_ofEdges _ _

@[simp] theorem E_tietze : tietze.E = 18 := by native_decide

theorem isRegularWith_tietze : tietze.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_tietze : tietze.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_tietze : ¬ tietze.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 3) (b := vtx 12 8) (d := vtx 12 9)
    (by decide) (by decide) (by decide)

@[simp] theorem girth_tietze : tietze.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 3) (b := vtx 12 8) (c := vtx 12 9)
    (by decide) (by decide) (by decide)

@[simp] theorem card_truncatedTetrahedron : FinEnum.card truncatedTetrahedron.V = 12 :=
  card_ofEdges _ _

@[simp] theorem E_truncatedTetrahedron : truncatedTetrahedron.E = 18 := by native_decide

theorem isRegularWith_truncatedTetrahedron : truncatedTetrahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_truncatedTetrahedron : truncatedTetrahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

/-- The truncated tetrahedron has triangular faces. -/
@[simp] theorem not_isBipartite_truncatedTetrahedron : ¬ truncatedTetrahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 4) (d := vtx 12 8)
    (by native_decide) (by native_decide) (by native_decide)

/-- The truncated tetrahedron has girth three: `0 - 4 - 8 - 0` is one of the triangles cut off the
corners. -/
@[simp] theorem girth_truncatedTetrahedron : truncatedTetrahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 4) (c := vtx 12 8)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_robertson : FinEnum.card robertson.V = 19 := card_ofEdges _ _

@[simp] theorem E_robertson : robertson.E = 38 := by native_decide

theorem isRegularWith_robertson : robertson.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 19) (by native_decide)

@[simp] theorem isConnected_robertson : robertson.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 19)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_robertson : ¬ robertson.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 19 (by norm_num) [0, 1, 2, 3, 4]) 5 rfl (by decide) rfl

/-- The Robertson graph has girth five: `0 - 1 - 2 - 3 - 4 - 0` is a pentagon. -/
@[simp] theorem girth_robertson : robertson.girth = 5 := by
  have hnac : ¬ robertson.IsAcyclic :=
    not_isAcyclic_of_cycleList (vtx 19 0) [vtx 19 1, vtx 19 2, vtx 19 3, vtx 19 4]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  refine le_antisymm ?_ (five_le_girth (by native_decide) (by native_decide) hnac)
  exact girth_le_of_cycleList (vtx 19 0) [vtx 19 1, vtx 19 2, vtx 19 3, vtx 19 4]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_bidiakisCube : FinEnum.card bidiakisCube.V = 12 := card_ofEdges _ _

@[simp] theorem E_bidiakisCube : bidiakisCube.E = 18 := by native_decide

theorem isRegularWith_bidiakisCube : bidiakisCube.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_bidiakisCube : bidiakisCube.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_bidiakisCube : ¬ bidiakisCube.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 12 (by norm_num) [0, 1, 2, 10, 11]) 5 rfl (by decide) rfl

/-- The Bidiakis cube has girth four: `0 - 1 - 5 - 6 - 0` is a square. -/
@[simp] theorem girth_bidiakisCube : bidiakisCube.girth = 4 := by
  have hnac : ¬ bidiakisCube.IsAcyclic :=
    not_isAcyclic_of_cycleList (vtx 12 0) [vtx 12 1, vtx 12 5, vtx 12 6]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  refine le_antisymm ?_ (four_le_girth (by native_decide) hnac)
  exact girth_le_of_cycleList (vtx 12 0) [vtx 12 1, vtx 12 5, vtx 12 6]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_dyck : FinEnum.card dyck.V = 32 := card_ofEdges _ _

@[simp] theorem E_dyck : dyck.E = 48 := by native_decide

theorem isRegularWith_dyck : dyck.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 32) (by native_decide)

@[simp] theorem isConnected_dyck : dyck.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 32)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_dyck : dyck.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem card_balaban10Cage : FinEnum.card balaban10Cage.V = 70 := card_ofEdges _ _

@[simp] theorem E_balaban10Cage : balaban10Cage.E = 105 := by native_decide

theorem isRegularWith_balaban10Cage : balaban10Cage.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 70) (by native_decide)

@[simp] theorem isConnected_balaban10Cage : balaban10Cage.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 70)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_balaban10Cage : balaban10Cage.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-! ## The girth of the cages

Every graph above of girth at most five got it from the hand-written ladder of
`IsoGraph/Values/Identities.lean`.  The graphs of girth six and beyond go through the cycle-list
machinery instead: `girth_le_of_cycleList` turns an explicit list of vertices into an upper
bound, and `six_le_girth_of_nbrList`, `seven_le_girth_of_nbrList`, `eight_le_girth_of_nbrList`
and `ten_le_girth_of_nbrList` turn an exhaustive search along a neighbour table into a lower
bound.  The last of them, at the Balaban 10-cage, searches seventy vertices to depth nine. -/

/-- The neighbour table of the heawood graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def heawoodTbl : List (List heawood.V) := heawood.nbrTable (List.finRange 14)

/-- The neighbours of `a` in the heawood graph. -/
def heawoodNb (a : heawood.V) : List heawood.V := heawoodTbl.getD a.1 []

theorem heawood_nb : ∀ a b : heawood.V, b ∈ heawoodNb a ↔ heawood.Adj a b := by
  native_decide

/-- The Heawood graph, the `(3, 6)`-cage, has girth six: `0 - 1 - 2 - 3 - 4 - 5 - 0` is a
six-cycle, and a search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_heawood : heawood.girth = 6 := by
  have hcyc : heawood.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 14 0) [vtx 14 1, vtx 14 2, vtx 14 3, vtx 14 4, vtx 14 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ heawood.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 14 0) [vtx 14 1, vtx 14 2, vtx 14 3, vtx 14 4, vtx 14 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList heawood_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the pappus graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def pappusTbl : List (List pappus.V) := pappus.nbrTable (List.finRange 18)

/-- The neighbours of `a` in the pappus graph. -/
def pappusNb (a : pappus.V) : List pappus.V := pappusTbl.getD a.1 []

theorem pappus_nb : ∀ a b : pappus.V, b ∈ pappusNb a ↔ pappus.Adj a b := by
  native_decide

/-- The Pappus graph has girth six: `0 - 1 - 2 - 3 - 4 - 5 - 0` is a six-cycle, and a search along
the
neighbour table finds no shorter one. -/
@[simp] theorem girth_pappus : pappus.girth = 6 := by
  have hcyc : pappus.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 18 0) [vtx 18 1, vtx 18 2, vtx 18 3, vtx 18 4, vtx 18 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ pappus.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 18 0) [vtx 18 1, vtx 18 2, vtx 18 3, vtx 18 4, vtx 18 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList pappus_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the mobiusKantor graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def mobiusKantorTbl : List (List mobiusKantor.V) := mobiusKantor.nbrTable (List.finRange 16)

/-- The neighbours of `a` in the mobiusKantor graph. -/
def mobiusKantorNb (a : mobiusKantor.V) : List mobiusKantor.V := mobiusKantorTbl.getD a.1 []

theorem mobiusKantor_nb : ∀ a b : mobiusKantor.V, b ∈ mobiusKantorNb a ↔ mobiusKantor.Adj a b := by
  native_decide

/-- The Möbius–Kantor graph has girth six: `0 - 1 - 2 - 3 - 11 - 8 - 0` is a six-cycle, and a
search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_mobiusKantor : mobiusKantor.girth = 6 := by
  have hcyc : mobiusKantor.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 16 0) [vtx 16 1, vtx 16 2, vtx 16 3, vtx 16 11, vtx 16 8]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ mobiusKantor.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 16 0) [vtx 16 1, vtx 16 2, vtx 16 3, vtx 16 11, vtx 16 8]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList mobiusKantor_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the desargues graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def desarguesTbl : List (List desargues.V) := desargues.nbrTable (List.finRange 20)

/-- The neighbours of `a` in the desargues graph. -/
def desarguesNb (a : desargues.V) : List desargues.V := desarguesTbl.getD a.1 []

theorem desargues_nb : ∀ a b : desargues.V, b ∈ desarguesNb a ↔ desargues.Adj a b := by
  native_decide

/-- The Desargues graph has girth six: `0 - 1 - 2 - 3 - 13 - 10 - 0` is a six-cycle, and a search
along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_desargues : desargues.girth = 6 := by
  have hcyc : desargues.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 20 0) [vtx 20 1, vtx 20 2, vtx 20 3, vtx 20 13, vtx 20 10]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ desargues.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 20 0) [vtx 20 1, vtx 20 2, vtx 20 3, vtx 20 13, vtx 20 10]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList desargues_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the nauru graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def nauruTbl : List (List nauru.V) := nauru.nbrTable (List.finRange 24)

/-- The neighbours of `a` in the nauru graph. -/
def nauruNb (a : nauru.V) : List nauru.V := nauruTbl.getD a.1 []

theorem nauru_nb : ∀ a b : nauru.V, b ∈ nauruNb a ↔ nauru.Adj a b := by
  native_decide

/-- The Nauru graph has girth six: `0 - 1 - 2 - 14 - 19 - 12 - 0` is a six-cycle, and a search
along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_nauru : nauru.girth = 6 := by
  have hcyc : nauru.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 14, vtx 24 19, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ nauru.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 14, vtx 24 19, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList nauru_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the mcgee graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def mcgeeTbl : List (List mcgee.V) := mcgee.nbrTable (List.finRange 24)

/-- The neighbours of `a` in the mcgee graph. -/
def mcgeeNb (a : mcgee.V) : List mcgee.V := mcgeeTbl.getD a.1 []

theorem mcgee_nb : ∀ a b : mcgee.V, b ∈ mcgeeNb a ↔ mcgee.Adj a b := by
  native_decide

/-- The McGee graph has girth seven: `0 - 1 - 2 - 3 - 4 - 11 - 12 - 0` is a seven-cycle, and a
search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_mcgee : mcgee.girth = 7 := by
  have hcyc : mcgee.girth ≤ 7 :=
    girth_le_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 3, vtx 24 4, vtx 24 11, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ mcgee.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 3, vtx 24 4, vtx 24 11, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (seven_le_girth_of_nbrList mcgee_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the coxeter graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def coxeterTbl : List (List coxeter.V) := coxeter.nbrTable (List.finRange 28)

/-- The neighbours of `a` in the coxeter graph. -/
def coxeterNb (a : coxeter.V) : List coxeter.V := coxeterTbl.getD a.1 []

theorem coxeter_nb : ∀ a b : coxeter.V, b ∈ coxeterNb a ↔ coxeter.Adj a b := by
  native_decide

/-- The Coxeter graph has girth seven: `0 - 1 - 2 - 3 - 4 - 5 - 6 - 0` is a seven-cycle, and a
search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_coxeter : coxeter.girth = 7 := by
  have hcyc : coxeter.girth ≤ 7 :=
    girth_le_of_cycleList
      (vtx 28 0) [vtx 28 1, vtx 28 2, vtx 28 3, vtx 28 4, vtx 28 5, vtx 28 6]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ coxeter.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 28 0) [vtx 28 1, vtx 28 2, vtx 28 3, vtx 28 4, vtx 28 5, vtx 28 6]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (seven_le_girth_of_nbrList coxeter_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the tutteCoxeter graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def tutteCoxeterTbl : List (List tutteCoxeter.V) := tutteCoxeter.nbrTable (List.finRange 30)

/-- The neighbours of `a` in the tutteCoxeter graph. -/
def tutteCoxeterNb (a : tutteCoxeter.V) : List tutteCoxeter.V := tutteCoxeterTbl.getD a.1 []

theorem tutteCoxeter_nb : ∀ a b : tutteCoxeter.V, b ∈ tutteCoxeterNb a ↔ tutteCoxeter.Adj a b := by
  native_decide

/-- The Tutte–Coxeter graph, the `(3, 8)`-cage, has girth eight: `0 - 1 - 2 - 3 - 4 - 5 - 18 - 17 -
0` is an eight-cycle, and a search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_tutteCoxeter : tutteCoxeter.girth = 8 := by
  have hcyc : tutteCoxeter.girth ≤ 8 :=
    girth_le_of_cycleList
      (vtx 30 0) [vtx 30 1, vtx 30 2, vtx 30 3, vtx 30 4, vtx 30 5, vtx 30 18, vtx 30 17]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ tutteCoxeter.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 30 0) [vtx 30 1, vtx 30 2, vtx 30 3, vtx 30 4, vtx 30 5, vtx 30 18, vtx 30 17]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (eight_le_girth_of_nbrList tutteCoxeter_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

def dyckTbl : List (List dyck.V) := dyck.nbrTable (List.finRange 32)

def dyckNb (a : dyck.V) : List dyck.V := dyckTbl.getD a.1 []

theorem dyck_nb : ∀ a b : dyck.V, b ∈ dyckNb a ↔ dyck.Adj a b := by
  native_decide

@[simp] theorem girth_dyck : dyck.girth = 6 := by
  have hcyc : dyck.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 32 0) [vtx 32 1, vtx 32 2, vtx 32 3, vtx 32 4, vtx 32 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ dyck.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 32 0) [vtx 32 1, vtx 32 2, vtx 32 3, vtx 32 4, vtx 32 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList dyck_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

def balabanTbl : List (List balaban10Cage.V) := balaban10Cage.nbrTable (List.finRange 70)

def balabanNb (a : balaban10Cage.V) : List balaban10Cage.V := balabanTbl.getD a.1 []

theorem balaban_nb : ∀ a b : balaban10Cage.V, b ∈ balabanNb a ↔ balaban10Cage.Adj a b := by
  native_decide

@[simp] theorem girth_balaban10Cage : balaban10Cage.girth = 10 := by
  have hcyc : balaban10Cage.girth ≤ 10 :=
    girth_le_of_cycleList
      (vtx 70 0) [vtx 70 1, vtx 70 2, vtx 70 3, vtx 70 4, vtx 70 5, vtx 70 6, vtx 70 63,
        vtx 70 62, vtx 70 61]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ balaban10Cage.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 70 0) [vtx 70 1, vtx 70 2, vtx 70 3, vtx 70 4, vtx 70 5, vtx 70 6, vtx 70 63,
        vtx 70 62, vtx 70 61]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (ten_le_girth_of_nbrList balaban_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-! ## Four more graphs with names

Two of these fill gaps in the symmetry table.  The Holt graph is the smallest
*half-transitive* graph: vertex- and edge-transitive, but not arc-transitive, so no
automorphism reverses an edge.  The Ljubljana graph is another cubic semi-symmetric
graph, larger than the Gray graph above and, like it, the incidence graph of a
configuration.

The Biggs–Smith graph is the cubic distance-transitive graph of girth nine, the one girth
for which the cage itself has no name.  The flower snark `J₅` is the smallest of the
flower snarks: bridgeless, cubic, and needing four colours on its edges, like the Petersen
graph, which is the smallest snark of all. -/

/-- The edges of the Holt graph: the vertex set is `ℤ/9 × ℤ/3`, the pair `(x, y)` numbered
`3x + y`, and `(x, y)` is joined to `(4x ± 1, y - 1)`. -/
def holtEdges : List (ℕ × ℕ) :=
  (List.range 9).flatMap fun x ↦ (List.range 3).flatMap fun y ↦
    [1, 8].map fun s ↦ (3 * x + y, 3 * ((4 * x + s) % 9) + (y + 2) % 3)

/-- The Holt graph, also called the Doyle graph: the smallest half-transitive graph, on
twenty-seven vertices.  It is vertex- and edge-transitive, but its automorphism group has
order fifty-four and so is too small to reverse an edge. -/
abbrev holt : CGraph := ofEdges 27 holtEdges

/-- The edges of the flower snark `J₅`: the five-cycle on `0, …, 4`, the claw centres `5, …, 9`
joined to it and to the ten-cycle on `10, …, 19`. -/
def flowerSnarkEdges : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun i ↦
      [(i, (i + 1) % 5), (i, 5 + i), (5 + i, 10 + i), (5 + i, 15 + i)]) ++
    (List.range 10).map fun j ↦ (10 + j, 10 + (j + 1) % 10)

/-- The flower snark `J₅`: five copies of a claw, their centres left alone, their first leaves
joined in a five-cycle and their other leaves in a ten-cycle. -/
abbrev flowerSnark : CGraph := ofEdges 20 flowerSnarkEdges

/-- The LCF code of the Biggs–Smith graph. -/
def biggsSmithCode : List ℤ :=
  [16, 24, -38, 17, 34, 48, -19, 41, -35, 47, -20, 34, -36, 21, 14, 48, -16, -36, -43, 28, -17, 21,
    29, -43, 46, -24, 28, -38, -14, -50, -45, 21, 8, 27, -21, 20, -37, 39, -34, -44, -8, 38, -21,
    25, 15, -34, 18, -28, -41, 36, 8, -29, -21, -48, -28, -20, -47, 14, -8, -15, -27, 38, 24, -48,
    -18, 25, 38, 31, -25, 24, -46, -14, 28, 11, 21, 35, -39, 43, 36, -38, 14, 50, 43, 36, -11, -36,
    -24, 45, 8, 19, -25, 38, 20, -24, -14, -21, -8, 44, -31, -38, -28, 37]

/-- The Biggs–Smith graph: the cubic distance-transitive graph on a hundred and two vertices, and
the only one of girth nine. -/
abbrev biggsSmith : CGraph := ofEdges 102 (lcfEdges biggsSmithCode 1)

/-- The LCF code of the Ljubljana graph. -/
def ljubljanaCode : List ℤ :=
  [47, -23, -31, 39, 25, -21, -31, -41, 25, 15, 29, -41, -19, 15, -49, 33, 39, -35, -21, 17, -33,
    49, 41, 31, -15, -29, 41, 31, -15, -25, 21, 31, -51, -25, 23, 9, -17, 51, 35, -29, 21, -51, -39,
    33, -9, -51, 51, -47, -33, 19, 51, -21, 29, 21, -31, -39]

/-- The Ljubljana graph: the cubic semi-symmetric graph on a hundred and twelve vertices, the
incidence graph of the Ljubljana configuration `56₃`. -/
abbrev ljubljana : CGraph := ofEdges 112 (lcfEdges ljubljanaCode 2)

@[simp] theorem card_holt : FinEnum.card holt.V = 27 := card_ofEdges _ _

@[simp] theorem E_holt : holt.E = 54 := by native_decide

theorem isRegularWith_holt : holt.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 27) (by native_decide)

/-- The numbering `3x + y` has no back edge at `1` or `2`, so connectivity is certified by the
order a breadth-first search from `0` finds the vertices in. -/
@[simp] theorem isConnected_holt : holt.IsConnected :=
  isConnected_of_bfsOrder (holt.bfsOrder (List.finRange 27) (vtx 27 0)) (vtx 27 0)
    (by native_decide)

/-- The Holt graph has an odd cycle, so it is not bipartite. -/
@[simp] theorem not_isBipartite_holt : ¬ holt.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 27 (by norm_num) [0, 5, 10, 6, 22]) 5 rfl
    (by native_decide) rfl

/-- The neighbour table of the Holt graph. -/
def holtTbl : List (List holt.V) := holt.nbrTable (List.finRange 27)

/-- The neighbours of `a` in the Holt graph. -/
def holtNb (a : holt.V) : List holt.V := holtTbl.getD a.1 []

theorem holt_nb : ∀ a b : holt.V, b ∈ holtNb a ↔ holt.Adj a b := by
  native_decide

/-- The Holt graph has girth five. -/
@[simp] theorem girth_holt : holt.girth = 5 := by
  have hcyc : holt.girth ≤ 5 :=
    girth_le_of_cycleList
      (vtx 27 0) [vtx 27 5, vtx 27 10, vtx 27 6, vtx 27 22]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ holt.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 27 0) [vtx 27 5, vtx 27 10, vtx 27 6, vtx 27 22]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (five_le_girth_of_nbrList holt_nb
      (by native_decide)
      (by native_decide) hnac)

@[simp] theorem card_flowerSnark : FinEnum.card flowerSnark.V = 20 := card_ofEdges _ _

@[simp] theorem E_flowerSnark : flowerSnark.E = 30 := by native_decide

theorem isRegularWith_flowerSnark : flowerSnark.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_flowerSnark : flowerSnark.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

/-- The five-cycle on the first leaves is odd, so the flower snark is not bipartite. -/
@[simp] theorem not_isBipartite_flowerSnark : ¬ flowerSnark.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 20 (by norm_num) [0, 1, 2, 3, 4]) 5 rfl
    (by native_decide) rfl

/-- The neighbour table of the flower snark `J₅`. -/
def flowerSnarkTbl : List (List flowerSnark.V) := flowerSnark.nbrTable (List.finRange 20)

/-- The neighbours of `a` in the flower snark `J₅`. -/
def flowerSnarkNb (a : flowerSnark.V) : List flowerSnark.V := flowerSnarkTbl.getD a.1 []

theorem flowerSnark_nb : ∀ a b : flowerSnark.V, b ∈ flowerSnarkNb a ↔ flowerSnark.Adj a b := by
  native_decide

/-- The flower snark `J₅` has girth five: the five-cycle on the first leaves is shortest. -/
@[simp] theorem girth_flowerSnark : flowerSnark.girth = 5 := by
  have hcyc : flowerSnark.girth ≤ 5 :=
    girth_le_of_cycleList
      (vtx 20 0) [vtx 20 1, vtx 20 2, vtx 20 3, vtx 20 4]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ flowerSnark.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 20 0) [vtx 20 1, vtx 20 2, vtx 20 3, vtx 20 4]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (five_le_girth_of_nbrList flowerSnark_nb
      (by native_decide)
      (by native_decide) hnac)

@[simp] theorem card_biggsSmith : FinEnum.card biggsSmith.V = 102 := card_ofEdges _ _

@[simp] theorem E_biggsSmith : biggsSmith.E = 153 := by native_decide

theorem isRegularWith_biggsSmith : biggsSmith.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 102) (by native_decide)

@[simp] theorem isConnected_biggsSmith : biggsSmith.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 102)) (by norm_num) (by native_decide)

/-- The Biggs–Smith graph has an odd cycle, so it is not bipartite. -/
@[simp] theorem not_isBipartite_biggsSmith : ¬ biggsSmith.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 102 (by norm_num) [0, 101, 36, 37, 38, 4, 3, 2, 1])
    9 rfl (by decide) rfl

/-- The neighbour table of the Biggs–Smith graph. -/
def biggsSmithTbl : List (List biggsSmith.V) := biggsSmith.nbrTable (List.finRange 102)

/-- The neighbours of `a` in the Biggs–Smith graph. -/
def biggsSmithNb (a : biggsSmith.V) : List biggsSmith.V := biggsSmithTbl.getD a.1 []

theorem biggsSmith_nb : ∀ a b : biggsSmith.V, b ∈ biggsSmithNb a ↔ biggsSmith.Adj a b := by
  native_decide

/-- The Biggs–Smith graph has girth nine. -/
@[simp] theorem girth_biggsSmith : biggsSmith.girth = 9 := by
  have hcyc : biggsSmith.girth ≤ 9 :=
    girth_le_of_cycleList
      (vtx 102 0) [vtx 102 101, vtx 102 36, vtx 102 37, vtx 102 38, vtx 102 4, vtx 102 3, vtx 102 2,
        vtx 102 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ biggsSmith.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 102 0) [vtx 102 101, vtx 102 36, vtx 102 37, vtx 102 38, vtx 102 4, vtx 102 3, vtx 102 2,
        vtx 102 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (nine_le_girth_of_nbrList biggsSmith_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

@[simp] theorem card_ljubljana : FinEnum.card ljubljana.V = 112 := card_ofEdges _ _

@[simp] theorem E_ljubljana : ljubljana.E = 168 := by native_decide

theorem isRegularWith_ljubljana : ljubljana.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 112) (by native_decide)

@[simp] theorem isConnected_ljubljana : ljubljana.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 112)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_ljubljana : ljubljana.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-- The neighbour table of the Ljubljana graph. -/
def ljubljanaTbl : List (List ljubljana.V) := ljubljana.nbrTable (List.finRange 112)

/-- The neighbours of `a` in the Ljubljana graph. -/
def ljubljanaNb (a : ljubljana.V) : List ljubljana.V := ljubljanaTbl.getD a.1 []

theorem ljubljana_nb : ∀ a b : ljubljana.V, b ∈ ljubljanaNb a ↔ ljubljana.Adj a b := by
  native_decide

/-- The Ljubljana graph has girth ten. -/
@[simp] theorem girth_ljubljana : ljubljana.girth = 10 := by
  have hcyc : ljubljana.girth ≤ 10 :=
    girth_le_of_cycleList
      (vtx 112 0) [vtx 112 47, vtx 112 46, vtx 112 45, vtx 112 44, vtx 112 43, vtx 112 42,
        vtx 112 3, vtx 112 2, vtx 112 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ ljubljana.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 112 0) [vtx 112 47, vtx 112 46, vtx 112 45, vtx 112 44, vtx 112 43, vtx 112 42,
        vtx 112 3, vtx 112 2, vtx 112 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (ten_le_girth_of_nbrList ljubljana_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

end NamedGraphs
