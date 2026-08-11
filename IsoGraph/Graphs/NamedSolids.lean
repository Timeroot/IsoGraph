import IsoGraph.Invariants.Certificates
import IsoGraph.Graphs.SRG

/-!
# The Archimedean and Catalan solids

The one-skeletons of six of the thirteen Archimedean solids — three truncations and the two
rectifications here, and `truncatedTetrahedron`, the smallest of the thirteen, with the sporadic
graphs of `IsoGraph/Graphs/NamedGraphs.lean` — and of their six duals, the Catalan solids that go
with them.  The five Platonic solids are elsewhere: `complete 4` is the tetrahedron, `hypercube 3`
the cube, `cocktailParty 3` the octahedron, and `dodecahedron` and `icosahedron` are in
`IsoGraph/Graphs/NamedGraphs.lean`.

Each solid is given by the edge list of its one-skeleton, and for each the module records the
order, the number of edges, the degree or the degree sequence, connectivity, bipartiteness and
the girth.
-/

set_option maxRecDepth 4000

namespace NamedGraphs

open CGraph CGraph.Enum

/-! ## The Archimedean solids

`truncatedTetrahedron`, in `IsoGraph/Graphs/NamedGraphs.lean`, is the smallest of the thirteen
Archimedean solids.  Five more of them are here: two quasiregular ones, the cuboctahedron and the
icosidodecahedron, and three truncations, of the cube, the octahedron and the
icosahedron.  The last is the football, and the carbon skeleton of buckminsterfullerene.

Each is given by the edge list of its one-skeleton, computed from the usual coordinates
and renumbered breadth-first so that the back-edge certificate applies. -/

/-- The edges of the cuboctahedron. -/
def cuboctahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 5), (1, 6), (2, 4), (2, 5), (2, 7), (3, 8), (3, 9),
   (4, 8), (4, 10), (5, 6), (5, 7), (6, 9), (6, 11), (7, 10), (7, 11), (8, 9), (8, 10), (9, 11),
   (10, 11)]

/-- The cuboctahedron: the quasiregular solid with eight triangular and six square faces. -/
abbrev cuboctahedron : CGraph := ofEdges 12 cuboctahedronEdges

/-- The edges of the truncated cube. -/
def truncatedCubeEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 8), (5, 9), (6, 10),
   (6, 11), (7, 12), (7, 13), (8, 14), (8, 15), (9, 16), (9, 17), (10, 11), (10, 14), (11, 18),
   (12, 13), (12, 16), (13, 19), (14, 15), (15, 20), (16, 17), (17, 21), (18, 19), (18, 22),
   (19, 22), (20, 21), (20, 23), (21, 23), (22, 23)]

/-- The truncated cube: eight triangles and six octagons. -/
abbrev truncatedCube : CGraph := ofEdges 24 truncatedCubeEdges

/-- The edges of the truncated octahedron. -/
def truncatedOctahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 4), (2, 6), (3, 7), (3, 8), (4, 9), (5, 10), (5, 11),
   (6, 12), (6, 13), (7, 10), (7, 14), (8, 12), (8, 14), (9, 15), (9, 16), (10, 17), (11, 15),
   (11, 17), (12, 18), (13, 16), (13, 18), (14, 19), (15, 20), (16, 20), (17, 21), (18, 22),
   (19, 21), (19, 22), (20, 23), (21, 23), (22, 23)]

/-- The truncated octahedron: six squares and eight hexagons.  Its vertices are the twenty-four
permutations of `(0, 1, 2, 3)`, adjacent when they differ by a transposition of neighbouring
entries, so it is also the permutohedron of order four. -/
abbrev truncatedOctahedron : CGraph := ofEdges 24 truncatedOctahedronEdges

/-- The edges of the icosidodecahedron. -/
def icosidodecahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 5), (1, 6), (2, 4), (2, 7), (2, 8), (3, 9), (3, 10),
   (4, 11), (4, 12), (5, 6), (5, 7), (5, 13), (6, 14), (6, 15), (7, 8), (7, 13), (8, 16), (8, 17),
   (9, 10), (9, 11), (9, 18), (10, 14), (10, 19), (11, 12), (11, 18), (12, 16), (12, 20), (13, 21),
   (13, 22), (14, 15), (14, 19), (15, 21), (15, 23), (16, 17), (16, 20), (17, 22), (17, 24),
   (18, 25), (18, 26), (19, 25), (19, 27), (20, 26), (20, 28), (21, 22), (21, 23), (22, 24),
   (23, 27), (23, 29), (24, 28), (24, 29), (25, 26), (25, 27), (26, 28), (27, 29), (28, 29)]

/-- The icosidodecahedron: the quasiregular solid with twenty triangular and twelve pentagonal
faces. -/
abbrev icosidodecahedron : CGraph := ofEdges 30 icosidodecahedronEdges

/-- The edges of the truncated icosahedron. -/
def truncatedIcosahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7), (3, 8), (3, 9), (4, 10), (4, 11),
   (5, 12), (5, 13), (6, 10), (6, 14), (7, 9), (7, 15), (8, 12), (8, 16), (9, 17), (10, 18),
   (11, 13), (11, 19), (12, 20), (13, 21), (14, 22), (14, 23), (15, 23), (15, 24), (16, 25),
   (16, 26), (17, 25), (17, 27), (18, 22), (18, 28), (19, 28), (19, 29), (20, 26), (20, 30),
   (21, 30), (21, 31), (22, 32), (23, 33), (24, 27), (24, 34), (25, 35), (26, 36), (27, 37),
   (28, 38), (29, 31), (29, 39), (30, 40), (31, 41), (32, 42), (32, 43), (33, 34), (33, 42),
   (34, 44), (35, 37), (35, 45), (36, 45), (36, 46), (37, 47), (38, 39), (38, 43), (39, 48),
   (40, 41), (40, 46), (41, 49), (42, 50), (43, 51), (44, 47), (44, 52), (45, 53), (46, 54),
   (47, 55), (48, 49), (48, 56), (49, 57), (50, 51), (50, 52), (51, 56), (52, 58), (53, 54),
   (53, 55), (54, 57), (55, 58), (56, 59), (57, 59), (58, 59)]

/-- The truncated icosahedron: twelve pentagons and twenty hexagons.  This is the football, and
the carbon skeleton of buckminsterfullerene. -/
abbrev truncatedIcosahedron : CGraph := ofEdges 60 truncatedIcosahedronEdges

@[simp] theorem card_cuboctahedron : Fintype.card cuboctahedron.V = 12 := card_ofEdges _ _

@[simp] theorem E_cuboctahedron : cuboctahedron.E = 24 := by native_decide

theorem isRegularWith_cuboctahedron : cuboctahedron.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_cuboctahedron : cuboctahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

/-- The cuboctahedron has triangular faces. -/
@[simp] theorem not_isBipartite_cuboctahedron : ¬ cuboctahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 3) (d := vtx 12 1)
    (by decide) (by decide) (by decide)

/-- The cuboctahedron has girth three: `0 - 3 - 1 - 0` is a triangle. -/
@[simp] theorem girth_cuboctahedron : cuboctahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 3) (c := vtx 12 1)
    (by decide) (by decide) (by decide)

@[simp] theorem card_truncatedCube : Fintype.card truncatedCube.V = 24 := card_ofEdges _ _

@[simp] theorem E_truncatedCube : truncatedCube.E = 36 := by native_decide

theorem isRegularWith_truncatedCube : truncatedCube.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_truncatedCube : truncatedCube.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 24)) (by norm_num) (by native_decide)

/-- The truncated cube has triangular faces. -/
@[simp] theorem not_isBipartite_truncatedCube : ¬ truncatedCube.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 24 0) (b := vtx 24 3) (d := vtx 24 2)
    (by decide) (by decide) (by decide)

/-- The truncated cube has girth three: `0 - 3 - 2 - 0` is a triangle. -/
@[simp] theorem girth_truncatedCube : truncatedCube.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 24 0) (b := vtx 24 3) (c := vtx 24 2)
    (by decide) (by decide) (by decide)

@[simp] theorem card_truncatedOctahedron : Fintype.card truncatedOctahedron.V = 24 :=
  card_ofEdges _ _

@[simp] theorem E_truncatedOctahedron : truncatedOctahedron.E = 36 := by native_decide

theorem isRegularWith_truncatedOctahedron : truncatedOctahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_truncatedOctahedron : truncatedOctahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 24)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_truncatedOctahedron : truncatedOctahedron.IsBipartite :=
  ⟨fun v ↦ decide (v.1 ∈ [0, 4, 5, 6, 7, 8, 15, 16, 17, 18, 19, 23]), by native_decide⟩

/-- The truncated octahedron has girth four: its shortest faces are squares. -/
@[simp] theorem girth_truncatedOctahedron : truncatedOctahedron.girth = 4 := by
  have hnac : ¬ truncatedOctahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 24 0) [vtx 24 2, vtx 24 4, vtx 24 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hcyc : truncatedOctahedron.girth ≤ 4 :=
    girth_le_of_cycleList
      (vtx 24 0) [vtx 24 2, vtx 24 4, vtx 24 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (four_le_girth (by native_decide) hnac)

@[simp] theorem card_icosidodecahedron : Fintype.card icosidodecahedron.V = 30 := card_ofEdges _ _

@[simp] theorem E_icosidodecahedron : icosidodecahedron.E = 60 := by native_decide

theorem isRegularWith_icosidodecahedron : icosidodecahedron.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 30) (by native_decide)

@[simp] theorem isConnected_icosidodecahedron : icosidodecahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 30)) (by norm_num) (by native_decide)

/-- The icosidodecahedron has triangular faces. -/
@[simp] theorem not_isBipartite_icosidodecahedron : ¬ icosidodecahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 30 0) (b := vtx 30 3) (d := vtx 30 1)
    (by decide) (by decide) (by decide)

/-- The icosidodecahedron has girth three: `0 - 3 - 1 - 0` is a triangle. -/
@[simp] theorem girth_icosidodecahedron : icosidodecahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 30 0) (b := vtx 30 3) (c := vtx 30 1)
    (by decide) (by decide) (by decide)

@[simp] theorem card_truncatedIcosahedron : Fintype.card truncatedIcosahedron.V = 60 :=
  card_ofEdges _ _

@[simp] theorem E_truncatedIcosahedron : truncatedIcosahedron.E = 90 := by native_decide

theorem isRegularWith_truncatedIcosahedron : truncatedIcosahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 60) (by native_decide)

@[simp] theorem isConnected_truncatedIcosahedron : truncatedIcosahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 60)) (by norm_num) (by native_decide)

/-- The truncated icosahedron has pentagonal faces, so it has an odd cycle. -/
@[simp] theorem not_isBipartite_truncatedIcosahedron : ¬ truncatedIcosahedron.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 60 (by norm_num) [0, 3, 9, 7, 2]) 5 rfl (by decide) rfl

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
      (vtx 60 0) [vtx 60 3, vtx 60 9, vtx 60 7, vtx 60 2]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ truncatedIcosahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 60 0) [vtx 60 3, vtx 60 9, vtx 60 7, vtx 60 2]
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
those of a Platonic solid together with those of its dual, and every edge runs between the
two.

Each is computed as the face-adjacency graph of the corresponding Archimedean solid, then
renumbered breadth-first so that the back-edge certificate applies. -/

/-- The edges of the triakis tetrahedron. -/
def triakisTetrahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6), (2, 7),
   (3, 5), (3, 6), (3, 7), (4, 6), (5, 6), (6, 7)]

/-- The triakis tetrahedron: a tetrahedron with a triangular pyramid raised on each face, and the
dual of the truncated tetrahedron. -/
abbrev triakisTetrahedron : CGraph := ofEdges 8 triakisTetrahedronEdges

/-- The edges of the rhombic dodecahedron. -/
def rhombicDodecahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (1, 6), (2, 4), (2, 7), (2, 8), (3, 6), (3, 8), (3, 9),
   (4, 10), (5, 10), (5, 11), (6, 11), (7, 10), (7, 12), (8, 12), (9, 11), (9, 12), (10, 13),
   (11, 13), (12, 13)]

/-- The rhombic dodecahedron, dual to the cuboctahedron: twelve rhombic faces, and the vertices of
a cube together with those of an octahedron, no two of a kind adjacent. -/
abbrev rhombicDodecahedron : CGraph := ofEdges 14 rhombicDodecahedronEdges

/-- The edges of the triakis octahedron. -/
def triakisOctahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4),
   (2, 7), (2, 9), (2, 10), (2, 11), (3, 5), (3, 8), (3, 10), (3, 11), (3, 12), (4, 7), (5, 8),
   (6, 7), (6, 8), (7, 8), (7, 9), (7, 11), (7, 13), (8, 11), (8, 12), (8, 13), (9, 11), (10, 11),
   (11, 12), (11, 13)]

/-- The triakis octahedron, dual to the truncated cube: an octahedron with a pyramid raised on
each face. -/
abbrev triakisOctahedron : CGraph := ofEdges 14 triakisOctahedronEdges

/-- The edges of the tetrakis hexahedron. -/
def tetrakisHexahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 8),
   (2, 9), (3, 4), (3, 6), (3, 10), (3, 11), (4, 8), (4, 11), (4, 12), (5, 7), (5, 9), (6, 7),
   (6, 10), (7, 9), (7, 10), (7, 13), (8, 9), (8, 12), (9, 12), (9, 13), (10, 11), (10, 12),
   (10, 13), (11, 12), (12, 13)]

/-- The tetrakis hexahedron, dual to the truncated octahedron: a cube with a pyramid raised on
each face.  It is also the barycentric-free subdivision that gives the Delaunay triangulation
of the body-centred cubic lattice. -/
abbrev tetrakisHexahedron : CGraph := ofEdges 14 tetrakisHexahedronEdges

/-- The edges of the rhombic triacontahedron. -/
def rhombicTriacontahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (1, 7), (2, 6), (2, 8), (3, 7), (3, 9), (4, 8),
   (4, 10), (5, 9), (5, 10), (6, 11), (6, 12), (6, 13), (7, 11), (7, 14), (7, 15), (8, 13), (8, 16),
   (8, 17), (9, 15), (9, 18), (9, 19), (10, 17), (10, 19), (10, 20), (11, 21), (12, 21), (12, 22),
   (13, 22), (14, 21), (14, 23), (15, 23), (16, 22), (16, 24), (17, 24), (18, 23), (18, 25),
   (19, 25), (20, 24), (20, 25), (21, 26), (21, 27), (22, 26), (22, 28), (23, 27), (23, 29),
   (24, 28), (24, 30), (25, 29), (25, 30), (26, 31), (27, 31), (28, 31), (29, 31), (30, 31)]

/-- The rhombic triacontahedron, dual to the icosidodecahedron: thirty golden rhombi, on the
vertices of a dodecahedron together with those of an icosahedron. -/
abbrev rhombicTriacontahedron : CGraph := ofEdges 32 rhombicTriacontahedronEdges

/-- The edges of the pentakis dodecahedron. -/
def pentakisDodecahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 6), (1, 7), (1, 8), (2, 5), (2, 6),
   (2, 9), (2, 10), (3, 4), (3, 5), (3, 11), (3, 12), (3, 13), (4, 7), (4, 12), (4, 14), (5, 9),
   (5, 11), (5, 15), (6, 8), (6, 10), (6, 16), (7, 8), (7, 14), (7, 17), (8, 16), (8, 17), (8, 18),
   (9, 10), (9, 15), (9, 19), (10, 16), (10, 19), (10, 20), (11, 13), (11, 15), (11, 21), (12, 13),
   (12, 14), (12, 22), (13, 21), (13, 22), (13, 23), (14, 17), (14, 22), (14, 24), (15, 19),
   (15, 21), (15, 25), (16, 18), (16, 20), (16, 26), (17, 18), (17, 24), (17, 27), (18, 26),
   (18, 27), (19, 20), (19, 25), (19, 28), (20, 26), (20, 28), (21, 23), (21, 25), (21, 29),
   (22, 23), (22, 24), (22, 30), (23, 29), (23, 30), (24, 27), (24, 30), (25, 28), (25, 29),
   (26, 27), (26, 28), (26, 31), (27, 30), (27, 31), (28, 29), (28, 31), (29, 30), (29, 31),
   (30, 31)]

/-- The pentakis dodecahedron, dual to the truncated icosahedron: a dodecahedron with a pentagonal
pyramid raised on each face. -/
abbrev pentakisDodecahedron : CGraph := ofEdges 32 pentakisDodecahedronEdges

@[simp] theorem card_triakisTetrahedron : Fintype.card triakisTetrahedron.V = 8 := card_ofEdges _ _

@[simp] theorem E_triakisTetrahedron : triakisTetrahedron.E = 18 := by native_decide

@[simp] theorem degSequence_triakisTetrahedron :
    triakisTetrahedron.degSequence = [3, 3, 3, 3, 6, 6, 6, 6] := by native_decide

@[simp] theorem isConnected_triakisTetrahedron : triakisTetrahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 8)) (by norm_num) (by native_decide)

/-- The triakis tetrahedron has triangular faces. -/
@[simp] theorem not_isBipartite_triakisTetrahedron : ¬ triakisTetrahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 8 0) (b := vtx 8 2) (d := vtx 8 1)
    (by decide) (by decide) (by decide)

/-- The triakis tetrahedron has girth three: `0 - 2 - 1 - 0` is a triangle. -/
@[simp] theorem girth_triakisTetrahedron : triakisTetrahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 8 0) (b := vtx 8 2) (c := vtx 8 1)
    (by decide) (by decide) (by decide)

@[simp] theorem card_rhombicDodecahedron : Fintype.card rhombicDodecahedron.V = 14 :=
  card_ofEdges _ _

@[simp] theorem E_rhombicDodecahedron : rhombicDodecahedron.E = 24 := by native_decide

@[simp] theorem degSequence_rhombicDodecahedron :
    rhombicDodecahedron.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4] := by native_decide

@[simp] theorem isConnected_rhombicDodecahedron : rhombicDodecahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_rhombicDodecahedron : rhombicDodecahedron.IsBipartite :=
  ⟨fun v ↦ decide (v.1 ∈ [0, 4, 5, 6, 7, 8, 9, 13]), by native_decide⟩

/-- The rhombic dodecahedron has girth four: its faces are rhombi. -/
@[simp] theorem girth_rhombicDodecahedron : rhombicDodecahedron.girth = 4 := by
  have hnac : ¬ rhombicDodecahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 14 0) [vtx 14 2, vtx 14 4, vtx 14 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hcyc : rhombicDodecahedron.girth ≤ 4 :=
    girth_le_of_cycleList
      (vtx 14 0) [vtx 14 2, vtx 14 4, vtx 14 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (four_le_girth (by native_decide) hnac)

@[simp] theorem card_triakisOctahedron : Fintype.card triakisOctahedron.V = 14 := card_ofEdges _ _

@[simp] theorem E_triakisOctahedron : triakisOctahedron.E = 36 := by native_decide

@[simp] theorem degSequence_triakisOctahedron :
    triakisOctahedron.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 8, 8, 8, 8, 8, 8] := by native_decide

@[simp] theorem isConnected_triakisOctahedron : triakisOctahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

/-- The triakis octahedron has triangular faces. -/
@[simp] theorem not_isBipartite_triakisOctahedron : ¬ triakisOctahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 14 0) (b := vtx 14 2) (d := vtx 14 1)
    (by decide) (by decide) (by decide)

/-- The triakis octahedron has girth three: `0 - 2 - 1 - 0` is a triangle. -/
@[simp] theorem girth_triakisOctahedron : triakisOctahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 14 0) (b := vtx 14 2) (c := vtx 14 1)
    (by decide) (by decide) (by decide)

@[simp] theorem card_tetrakisHexahedron : Fintype.card tetrakisHexahedron.V = 14 := card_ofEdges _ _

@[simp] theorem E_tetrakisHexahedron : tetrakisHexahedron.E = 36 := by native_decide

@[simp] theorem degSequence_tetrakisHexahedron :
    tetrakisHexahedron.degSequence = [4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6] := by native_decide

@[simp] theorem isConnected_tetrakisHexahedron : tetrakisHexahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

/-- The tetrakis hexahedron has triangular faces. -/
@[simp] theorem not_isBipartite_tetrakisHexahedron : ¬ tetrakisHexahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 14 0) (b := vtx 14 2) (d := vtx 14 1)
    (by decide) (by decide) (by decide)

/-- The tetrakis hexahedron has girth three: `0 - 2 - 1 - 0` is a triangle. -/
@[simp] theorem girth_tetrakisHexahedron : tetrakisHexahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 14 0) (b := vtx 14 2) (c := vtx 14 1)
    (by decide) (by decide) (by decide)

@[simp] theorem card_rhombicTriacontahedron : Fintype.card rhombicTriacontahedron.V = 32 :=
  card_ofEdges _ _

@[simp] theorem E_rhombicTriacontahedron : rhombicTriacontahedron.E = 60 := by native_decide

@[simp] theorem degSequence_rhombicTriacontahedron :
    rhombicTriacontahedron.degSequence = [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] := by native_decide

@[simp] theorem isConnected_rhombicTriacontahedron : rhombicTriacontahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 32)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_rhombicTriacontahedron : rhombicTriacontahedron.IsBipartite :=
  ⟨fun v ↦ decide (v.1 ∈ [0, 6, 7, 8, 9, 10, 21, 22, 23, 24, 25, 31]), by native_decide⟩

/-- The rhombic triacontahedron has girth four: its faces are rhombi. -/
@[simp] theorem girth_rhombicTriacontahedron : rhombicTriacontahedron.girth = 4 := by
  have hnac : ¬ rhombicTriacontahedron.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 32 0) [vtx 32 2, vtx 32 6, vtx 32 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hcyc : rhombicTriacontahedron.girth ≤ 4 :=
    girth_le_of_cycleList
      (vtx 32 0) [vtx 32 2, vtx 32 6, vtx 32 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (four_le_girth (by native_decide) hnac)

@[simp] theorem card_pentakisDodecahedron : Fintype.card pentakisDodecahedron.V = 32 :=
  card_ofEdges _ _

@[simp] theorem E_pentakisDodecahedron : pentakisDodecahedron.E = 90 := by native_decide

@[simp] theorem degSequence_pentakisDodecahedron :
    pentakisDodecahedron.degSequence = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] := by native_decide

@[simp] theorem isConnected_pentakisDodecahedron : pentakisDodecahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 32)) (by norm_num) (by native_decide)

/-- The pentakis dodecahedron has triangular faces. -/
@[simp] theorem not_isBipartite_pentakisDodecahedron : ¬ pentakisDodecahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 32 0) (b := vtx 32 2) (d := vtx 32 1)
    (by decide) (by decide) (by decide)

/-- The pentakis dodecahedron has girth three: `0 - 2 - 1 - 0` is a triangle. -/
@[simp] theorem girth_pentakisDodecahedron : pentakisDodecahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 32 0) (b := vtx 32 2) (c := vtx 32 1)
    (by decide) (by decide) (by decide)

end NamedGraphs
