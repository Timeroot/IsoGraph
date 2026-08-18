import IsoGraph.Invariants.Certificates
import IsoGraph.Graphs.SRG
import IsoGraph.Graphs.Polyhedra

/-!
# The Archimedean and Catalan solids

The one-skeletons of six of the thirteen Archimedean solids — three truncations and the two
rectifications here, and `truncatedTetrahedron`, the smallest of the thirteen, with the sporadic
graphs of `IsoGraph/Graphs/NamedGraphs.lean` — and of their six duals, the Catalan solids that go
with them.  The five Platonic solids are elsewhere: `complete 4` is the tetrahedron, `hypercube 3`
the cube, `cocktailParty 3` the octahedron, and `dodecahedron` and `icosahedron` are in
`IsoGraph/Graphs/NamedGraphs.lean`.

Not one of these graphs is an edge list.  Each is a Platonic face list from
`IsoGraph/Graphs/Polyhedra.lean` with one of the operations of that module applied to it: the
truncations are `truncEdges`, the two quasiregular solids are `rectEdges`, the four kis solids are
`kisEdges` and the two rhombic ones are `incidenceEdges`.  The numbering of the vertices is
therefore whatever the operation produces — for a truncation, two vertices per edge of the
original, in the order the edges come — and where that numbering does not happen to have a back
edge at every vertex, connectivity is certified by the order a breadth-first search finds the
vertices in instead.

For each solid the module records the order, the number of edges, the degree or the degree
sequence, connectivity, bipartiteness and the girth.
-/

set_option maxRecDepth 4000

namespace NamedGraphs

open CGraph CGraph.Enum

/-! ## The Archimedean solids

`truncatedTetrahedron`, in `IsoGraph/Graphs/NamedGraphs.lean`, is the smallest of the thirteen
Archimedean solids.  Five more of them are here: two quasiregular ones, the cuboctahedron and the
icosidodecahedron, and three truncations, of the cube, the octahedron and the icosahedron.  The
last is the football, and the carbon skeleton of buckminsterfullerene. -/

/-- The cuboctahedron: the cube rectified, and the quasiregular solid with eight triangular and
six square faces. -/
abbrev cuboctahedron : CGraph := ofEdges 12 (rectEdges cubeFaces)

/-- The truncated cube: eight triangles and six octagons. -/
abbrev truncatedCube : CGraph := ofEdges 24 (truncEdges cubeFaces)

/-- The truncated octahedron: six squares and eight hexagons.  Its vertices are the twenty-four
permutations of `(0, 1, 2, 3)`, adjacent when they differ by a transposition of neighbouring
entries, so it is also the permutohedron of order four. -/
abbrev truncatedOctahedron : CGraph := ofEdges 24 (truncEdges octahedronFaces)

/-- The icosidodecahedron: the dodecahedron rectified, and the quasiregular solid with twenty
triangular and twelve pentagonal faces. -/
abbrev icosidodecahedron : CGraph := ofEdges 30 (rectEdges dodecahedronFaces)

/-- The truncated icosahedron: twelve pentagons and twenty hexagons.  This is the football, and
the carbon skeleton of buckminsterfullerene. -/
abbrev truncatedIcosahedron : CGraph := ofEdges 60 (truncEdges icosahedronFaces)

@[simp] theorem card_cuboctahedron : FinEnum.card cuboctahedron.V = 12 := card_ofEdges _ _

@[simp] theorem E_cuboctahedron : cuboctahedron.E = 24 := by native_decide

theorem isRegularWith_cuboctahedron : cuboctahedron.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_cuboctahedron : cuboctahedron.IsConnected :=
  isConnected_of_bfsOrder (cuboctahedron.bfsOrder (List.finRange 12) (vtx 12 0)) (vtx 12 0)
    (by native_decide)

/-- The cuboctahedron has triangular faces. -/
@[simp] theorem not_isBipartite_cuboctahedron : ¬ cuboctahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 1) (d := vtx 12 10)
    (by native_decide) (by native_decide) (by native_decide)

/-- The cuboctahedron has girth three: `0 - 1 - 10 - 0` is a triangle. -/
@[simp] theorem girth_cuboctahedron : cuboctahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 1) (c := vtx 12 10)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_truncatedCube : FinEnum.card truncatedCube.V = 24 := card_ofEdges _ _

@[simp] theorem E_truncatedCube : truncatedCube.E = 36 := by native_decide

theorem isRegularWith_truncatedCube : truncatedCube.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_truncatedCube : truncatedCube.IsConnected :=
  isConnected_of_bfsOrder (truncatedCube.bfsOrder (List.finRange 24) (vtx 24 0)) (vtx 24 0)
    (by native_decide)

/-- The truncated cube has triangular faces. -/
@[simp] theorem not_isBipartite_truncatedCube : ¬ truncatedCube.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 24 0) (b := vtx 24 8) (d := vtx 24 16)
    (by native_decide) (by native_decide) (by native_decide)

/-- The truncated cube has girth three: `0 - 8 - 16 - 0` is one of the triangles cut off the
corners of the cube. -/
@[simp] theorem girth_truncatedCube : truncatedCube.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 24 0) (b := vtx 24 8) (c := vtx 24 16)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_truncatedOctahedron : FinEnum.card truncatedOctahedron.V = 24 :=
  card_ofEdges _ _

@[simp] theorem E_truncatedOctahedron : truncatedOctahedron.E = 36 := by native_decide

theorem isRegularWith_truncatedOctahedron : truncatedOctahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_truncatedOctahedron : truncatedOctahedron.IsConnected :=
  isConnected_of_bfsOrder (truncatedOctahedron.bfsOrder (List.finRange 24) (vtx 24 0)) (vtx 24 0)
    (by native_decide)

@[simp] theorem isBipartite_truncatedOctahedron : truncatedOctahedron.IsBipartite :=
  ⟨fun v ↦ decide (v.1 ∈ [1, 3, 4, 7, 9, 10, 12, 14, 17, 18, 21, 23]), by native_decide⟩

/-- The truncated octahedron has girth four: its shortest faces are squares. -/
@[simp] theorem girth_truncatedOctahedron : truncatedOctahedron.girth = 4 := by
  have hnac : ¬ truncatedOctahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 24 0) [vtx 24 10, vtx 24 20, vtx 24 14]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hcyc : truncatedOctahedron.girth ≤ 4 :=
    girth_le_of_cycleList
      (vtx 24 0) [vtx 24 10, vtx 24 20, vtx 24 14]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (four_le_girth (by native_decide) hnac)

@[simp] theorem card_icosidodecahedron : FinEnum.card icosidodecahedron.V = 30 := card_ofEdges _ _

@[simp] theorem E_icosidodecahedron : icosidodecahedron.E = 60 := by native_decide

theorem isRegularWith_icosidodecahedron : icosidodecahedron.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 30) (by native_decide)

@[simp] theorem isConnected_icosidodecahedron : icosidodecahedron.IsConnected :=
  isConnected_of_bfsOrder (icosidodecahedron.bfsOrder (List.finRange 30) (vtx 30 0)) (vtx 30 0)
    (by native_decide)

/-- The icosidodecahedron has triangular faces. -/
@[simp] theorem not_isBipartite_icosidodecahedron : ¬ icosidodecahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 30 0) (b := vtx 30 1) (d := vtx 30 7)
    (by native_decide) (by native_decide) (by native_decide)

/-- The icosidodecahedron has girth three: `0 - 1 - 7 - 0` is a triangle. -/
@[simp] theorem girth_icosidodecahedron : icosidodecahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 30 0) (b := vtx 30 1) (c := vtx 30 7)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_truncatedIcosahedron : FinEnum.card truncatedIcosahedron.V = 60 :=
  card_ofEdges _ _

@[simp] theorem E_truncatedIcosahedron : truncatedIcosahedron.E = 90 := by native_decide

theorem isRegularWith_truncatedIcosahedron : truncatedIcosahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 60) (by native_decide)

/-- The vertices of the truncated icosahedron in the order a breadth-first search from `0` finds
them, which is the certificate that it is connected. -/
def truncatedIcosahedronOrder : List truncatedIcosahedron.V :=
  truncatedIcosahedron.bfsOrder (List.finRange 60) (vtx 60 0)

@[simp] theorem isConnected_truncatedIcosahedron : truncatedIcosahedron.IsConnected :=
  isConnected_of_bfsOrder truncatedIcosahedronOrder (vtx 60 0) (by native_decide)

/-- The truncated icosahedron has pentagonal faces, so it has an odd cycle. -/
@[simp] theorem not_isBipartite_truncatedIcosahedron : ¬ truncatedIcosahedron.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 60 (by norm_num) [0, 4, 8, 12, 16]) 5 rfl (by native_decide)
    rfl

/-- The neighbour table of the truncated icosahedron. -/
def truncatedIcosahedronTbl : List (List truncatedIcosahedron.V) :=
  truncatedIcosahedron.nbrTable (List.finRange 60)

/-- The neighbours of `a` in the truncated icosahedron. -/
def truncatedIcosahedronNb (a : truncatedIcosahedron.V) : List truncatedIcosahedron.V :=
  truncatedIcosahedronTbl.getD a.1 []

theorem truncatedIcosahedron_nb :
    ∀ a b : truncatedIcosahedron.V,
      b ∈ truncatedIcosahedronNb a ↔ truncatedIcosahedron.Adj a b := by
  native_decide

/-- The truncated icosahedron has girth five: its shortest faces are pentagons. -/
@[simp] theorem girth_truncatedIcosahedron : truncatedIcosahedron.girth = 5 := by
  have hcyc : truncatedIcosahedron.girth ≤ 5 :=
    girth_le_of_cycleList
      (vtx 60 0) [vtx 60 4, vtx 60 8, vtx 60 12, vtx 60 16]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ truncatedIcosahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 60 0) [vtx 60 4, vtx 60 8, vtx 60 12, vtx 60 16]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (five_le_girth_of_nbrList truncatedIcosahedron_nb
      (by native_decide)
      (by native_decide) hnac)

/-! ## The Catalan solids

The duals of the six Archimedean solids of the gallery, and so the six Catalan solids that go
with them.  None is regular — that is the point of the duality, since a solid whose faces are all
alike has vertices of two kinds — so each records a degree sequence in place of a degree.
Two of them, the rhombic dodecahedron and the rhombic triacontahedron, are the duals of the
two quasiregular solids, and they are exactly the two that are bipartite: their vertices are
those of a Platonic solid together with those of its dual, and every edge runs between the two.
That is precisely what `incidenceEdges` builds, and the four others are `kisEdges`: the dual of a
truncation is the original with a pyramid raised on each of its faces. -/

/-- The triakis tetrahedron: a tetrahedron with a triangular pyramid raised on each face, and the
dual of the truncated tetrahedron. -/
abbrev triakisTetrahedron : CGraph := ofEdges 8 (kisEdges 4 tetrahedronFaces)

/-- The rhombic dodecahedron, dual to the cuboctahedron: twelve rhombic faces, and the vertices of
a cube together with those of an octahedron, no two of a kind adjacent. -/
abbrev rhombicDodecahedron : CGraph := ofEdges 14 (incidenceEdges 8 cubeFaces)

/-- The triakis octahedron, dual to the truncated cube: an octahedron with a pyramid raised on
each face. -/
abbrev triakisOctahedron : CGraph := ofEdges 14 (kisEdges 6 octahedronFaces)

/-- The tetrakis hexahedron, dual to the truncated octahedron: a cube with a pyramid raised on
each face.  It is also the barycentric-free subdivision that gives the Delaunay triangulation
of the body-centred cubic lattice. -/
abbrev tetrakisHexahedron : CGraph := ofEdges 14 (kisEdges 8 cubeFaces)

/-- The rhombic triacontahedron, dual to the icosidodecahedron: thirty golden rhombi, on the
vertices of a dodecahedron together with those of an icosahedron. -/
abbrev rhombicTriacontahedron : CGraph := ofEdges 32 (incidenceEdges 20 dodecahedronFaces)

/-- The pentakis dodecahedron, dual to the truncated icosahedron: a dodecahedron with a pentagonal
pyramid raised on each face. -/
abbrev pentakisDodecahedron : CGraph := ofEdges 32 (kisEdges 20 dodecahedronFaces)

@[simp] theorem card_triakisTetrahedron : FinEnum.card triakisTetrahedron.V = 8 := card_ofEdges _ _

@[simp] theorem E_triakisTetrahedron : triakisTetrahedron.E = 18 := by native_decide

@[simp] theorem degSequence_triakisTetrahedron :
    triakisTetrahedron.degSequence = [3, 3, 3, 3, 6, 6, 6, 6] := by native_decide

@[simp] theorem isConnected_triakisTetrahedron : triakisTetrahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 8)) (by norm_num) (by native_decide)

/-- The triakis tetrahedron has triangular faces. -/
@[simp] theorem not_isBipartite_triakisTetrahedron : ¬ triakisTetrahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 8 0) (b := vtx 8 1) (d := vtx 8 2)
    (by native_decide) (by native_decide) (by native_decide)

/-- The triakis tetrahedron has girth three: `0 - 1 - 2 - 0` is a face of the tetrahedron under
it. -/
@[simp] theorem girth_triakisTetrahedron : triakisTetrahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 8 0) (b := vtx 8 1) (c := vtx 8 2)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_rhombicDodecahedron : FinEnum.card rhombicDodecahedron.V = 14 :=
  card_ofEdges _ _

@[simp] theorem E_rhombicDodecahedron : rhombicDodecahedron.E = 24 := by native_decide

@[simp] theorem degSequence_rhombicDodecahedron :
    rhombicDodecahedron.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4] := by native_decide

@[simp] theorem isConnected_rhombicDodecahedron : rhombicDodecahedron.IsConnected :=
  isConnected_of_bfsOrder (rhombicDodecahedron.bfsOrder (List.finRange 14) (vtx 14 0)) (vtx 14 0)
    (by native_decide)

/-- The vertices of the cube are one class and the faces are the other. -/
@[simp] theorem isBipartite_rhombicDodecahedron : rhombicDodecahedron.IsBipartite :=
  ⟨fun v ↦ decide (8 ≤ v.1), by native_decide⟩

/-- The rhombic dodecahedron has girth four: its faces are rhombi. -/
@[simp] theorem girth_rhombicDodecahedron : rhombicDodecahedron.girth = 4 := by
  have hnac : ¬ rhombicDodecahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 14 0) [vtx 14 8, vtx 14 1, vtx 14 10]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hcyc : rhombicDodecahedron.girth ≤ 4 :=
    girth_le_of_cycleList
      (vtx 14 0) [vtx 14 8, vtx 14 1, vtx 14 10]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (four_le_girth (by native_decide) hnac)

@[simp] theorem card_triakisOctahedron : FinEnum.card triakisOctahedron.V = 14 := card_ofEdges _ _

@[simp] theorem E_triakisOctahedron : triakisOctahedron.E = 36 := by native_decide

@[simp] theorem degSequence_triakisOctahedron :
    triakisOctahedron.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 8, 8, 8, 8, 8, 8] := by native_decide

@[simp] theorem isConnected_triakisOctahedron : triakisOctahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

/-- The triakis octahedron has triangular faces. -/
@[simp] theorem not_isBipartite_triakisOctahedron : ¬ triakisOctahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 14 0) (b := vtx 14 1) (d := vtx 14 2)
    (by native_decide) (by native_decide) (by native_decide)

/-- The triakis octahedron has girth three: `0 - 1 - 2 - 0` is a face of the octahedron under
it. -/
@[simp] theorem girth_triakisOctahedron : triakisOctahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 14 0) (b := vtx 14 1) (c := vtx 14 2)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_tetrakisHexahedron : FinEnum.card tetrakisHexahedron.V = 14 := card_ofEdges _ _

@[simp] theorem E_tetrakisHexahedron : tetrakisHexahedron.E = 36 := by native_decide

@[simp] theorem degSequence_tetrakisHexahedron :
    tetrakisHexahedron.degSequence = [4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6] := by native_decide

@[simp] theorem isConnected_tetrakisHexahedron : tetrakisHexahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

/-- The tetrakis hexahedron has triangular faces. -/
@[simp] theorem not_isBipartite_tetrakisHexahedron : ¬ tetrakisHexahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 14 0) (b := vtx 14 1) (d := vtx 14 8)
    (by native_decide) (by native_decide) (by native_decide)

/-- The tetrakis hexahedron has girth three: `0 - 1 - 8 - 0` is half of a face of the cube, cut by
the pyramid raised on it. -/
@[simp] theorem girth_tetrakisHexahedron : tetrakisHexahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 14 0) (b := vtx 14 1) (c := vtx 14 8)
    (by native_decide) (by native_decide) (by native_decide)

@[simp] theorem card_rhombicTriacontahedron : FinEnum.card rhombicTriacontahedron.V = 32 :=
  card_ofEdges _ _

@[simp] theorem E_rhombicTriacontahedron : rhombicTriacontahedron.E = 60 := by native_decide

@[simp] theorem degSequence_rhombicTriacontahedron :
    rhombicTriacontahedron.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] := by native_decide

@[simp] theorem isConnected_rhombicTriacontahedron : rhombicTriacontahedron.IsConnected :=
  isConnected_of_bfsOrder (rhombicTriacontahedron.bfsOrder (List.finRange 32) (vtx 32 0))
    (vtx 32 0) (by native_decide)

/-- The vertices of the dodecahedron are one class and its faces — the vertices of the
icosahedron — are the other. -/
@[simp] theorem isBipartite_rhombicTriacontahedron : rhombicTriacontahedron.IsBipartite :=
  ⟨fun v ↦ decide (20 ≤ v.1), by native_decide⟩

/-- The rhombic triacontahedron has girth four: its faces are rhombi. -/
@[simp] theorem girth_rhombicTriacontahedron : rhombicTriacontahedron.girth = 4 := by
  have hnac : ¬ rhombicTriacontahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 32 0) [vtx 32 20, vtx 32 1, vtx 32 21]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hcyc : rhombicTriacontahedron.girth ≤ 4 :=
    girth_le_of_cycleList
      (vtx 32 0) [vtx 32 20, vtx 32 1, vtx 32 21]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (four_le_girth (by native_decide) hnac)

@[simp] theorem card_pentakisDodecahedron : FinEnum.card pentakisDodecahedron.V = 32 :=
  card_ofEdges _ _

@[simp] theorem E_pentakisDodecahedron : pentakisDodecahedron.E = 90 := by native_decide

@[simp] theorem degSequence_pentakisDodecahedron :
    pentakisDodecahedron.degSequence = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by native_decide

@[simp] theorem isConnected_pentakisDodecahedron : pentakisDodecahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 32)) (by norm_num) (by native_decide)

/-- The pentakis dodecahedron has triangular faces. -/
@[simp] theorem not_isBipartite_pentakisDodecahedron : ¬ pentakisDodecahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 32 0) (b := vtx 32 1) (d := vtx 32 20)
    (by native_decide) (by native_decide) (by native_decide)

/-- The pentakis dodecahedron has girth three: `0 - 1 - 20 - 0` is one of the triangles of the
pyramid raised on the top face of the dodecahedron. -/
@[simp] theorem girth_pentakisDodecahedron : pentakisDodecahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 32 0) (b := vtx 32 1) (c := vtx 32 20)
    (by native_decide) (by native_decide) (by native_decide)

end NamedGraphs
