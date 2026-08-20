import IsoGraph.SmallGraphs.Defs.SRG

/-!
# Polyhedra

The five Platonic solids, and the truncation and rectification operations used to reach the
Archimedean ones.
-/

namespace CGraph

/-! ## The operations -/

/-- The edges of a polyhedron given by its faces: the pairs consecutive round a face, kept when
increasing.  A consistently oriented face list traverses each edge once in each direction, so each
edge is collected exactly once. -/
def faceEdges (fs : List (List ℕ)) : List (ℕ × ℕ) :=
  (fs.flatMap fun f ↦ f.zip (f.rotate 1)).filter fun p ↦ p.1 < p.2

/-- The arcs of an edge list: every edge in both directions, the increasing one first.  The arcs
are the corners of the truncation — arc `(u, v)` is the corner cut off the vertex `u` on the side
of `v` — and `arcs es` is what numbers them. -/
def arcs (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.flatMap fun p ↦ [p, (p.2, p.1)]

/-- The edges of the truncation of a polyhedron: one vertex for each arc, that is, two for each
edge of the polyhedron.  The arcs leaving a vertex are joined into a polygon — consecutive round
that polygon are the pairs consecutive round a face, which is where the face list is needed — and
the two arcs of an edge are joined to each other. -/
def truncEdges (fs : List (List ℕ)) : List (ℕ × ℕ) :=
  let es := faceEdges fs
  let as := arcs es
  (fs.flatMap fun f ↦ (f.zip ((f.rotate 1).zip (f.rotate 2))).map fun (a, b, c) ↦
      (as.idxOf (b, a), as.idxOf (b, c)))
    ++ es.map fun p ↦ (as.idxOf p, as.idxOf (p.2, p.1))

/-- The edges of the rectification of a polyhedron: one vertex for each edge, two of them joined
when the edges share an endpoint.  Truncating the corners as far as the edge midpoints leaves
exactly this, and for a polyhedron with three edges at every vertex it is the line graph of the
skeleton. -/
def rectEdges (fs : List (List ℕ)) : List (ℕ × ℕ) :=
  let es := faceEdges fs
  es.zipIdx.flatMap fun (p, i) ↦
    (es.take i).zipIdx.filterMap fun (q, j) ↦
      if p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2 then some (j, i) else none

/-- The edges of the vertex–face incidence graph of a polyhedron on `n` vertices: the vertices of
the polyhedron keep their numbers and face `i` becomes the vertex `n + i`, joined to the vertices
round it.  Geometrically this is the rhombic solid on the vertices of the polyhedron together with
those of its dual, every face of it a quadrilateral. -/
def incidenceEdges (n : ℕ) (fs : List (List ℕ)) : List (ℕ × ℕ) :=
  fs.zipIdx.flatMap fun (f, i) ↦ f.map fun v ↦ (v, n + i)

/-- The edges of the kis of a polyhedron on `n` vertices: the skeleton together with a pyramid
raised on every face, the apex over face `i` being the vertex `n + i`. -/
def kisEdges (n : ℕ) (fs : List (List ℕ)) : List (ℕ × ℕ) :=
  faceEdges fs ++ incidenceEdges n fs

end CGraph

namespace NamedGraphs

section
open CGraph CGraph.Enum

/-! ## The five Platonic solids

Their face lists, which are the only polyhedral data in the library.  The three smallest have
their skeletons elsewhere under other names — `complete 4`, `hypercube 3` and `cocktailParty 3` —
and the isomorphisms below check that the face lists really do describe them.  The dodecahedron
and the icosahedron are in `IsoGraph/SmallGraphs/Defs/Named.lean`. -/

/-- The tetrahedron, by its faces. -/
def tetrahedronFaces : List (List ℕ) := [[0, 1, 2], [0, 2, 3], [0, 3, 1], [1, 3, 2]]

/-- The cube, by its faces: the vertex `4x + 2y + z` is the corner with coordinates `(x, y, z)`,
and the six faces are the six coordinate directions. -/
def cubeFaces : List (List ℕ) :=
  [[0, 1, 3, 2], [4, 6, 7, 5], [0, 4, 5, 1], [2, 3, 7, 6], [0, 2, 6, 4], [1, 5, 7, 3]]

/-- The octahedron, by its faces: `0, 1, 2` are the positive coordinate directions and `3, 4, 5`
the negative ones, so opposite vertices differ by three, and the eight faces are the eight choices
of sign. -/
def octahedronFaces : List (List ℕ) :=
  [[0, 1, 2], [1, 3, 2], [3, 4, 2], [4, 0, 2], [1, 0, 5], [3, 1, 5], [4, 3, 5], [0, 4, 5]]

/-- The icosahedron, by its faces: `0` is the north pole, `1, …, 5` the northern ring, `6, …, 10`
the southern ring and `11` the south pole, so the faces come in four rings of five — the cap at
each pole and the two rings of the antiprism between them. -/
def icosahedronFaces : List (List ℕ) :=
  ((List.range 5).map fun i ↦ [0, i + 1, (i + 1) % 5 + 1]) ++
  ((List.range 5).map fun i ↦ [i + 1, i + 6, (i + 1) % 5 + 1]) ++
  ((List.range 5).map fun i ↦ [i + 6, (i + 1) % 5 + 6, (i + 1) % 5 + 1]) ++
  ((List.range 5).map fun i ↦ [11, (i + 1) % 5 + 6, i + 6])

/-- The dodecahedron, by its faces: `0, …, 4` is the top pentagon, `15, …, 19` the bottom one, and
the ten vertices between them alternate, `5 + 2i` hanging from the top vertex `i` and `6 + 2i`
rising from the bottom vertex `i`. -/
def dodecahedronFaces : List (List ℕ) :=
  [[0, 1, 2, 3, 4]] ++
  ((List.range 5).map fun i ↦ [i, 5 + 2 * i, 6 + 2 * i, 5 + 2 * ((i + 1) % 5), (i + 1) % 5]) ++
  ((List.range 5).map fun i ↦
    [15 + i, 15 + (i + 1) % 5, 6 + 2 * ((i + 1) % 5), 5 + 2 * ((i + 1) % 5), 6 + 2 * i]) ++
  [[19, 18, 17, 16, 15]]

/-- The face list of the tetrahedron describes the tetrahedron. -/
noncomputable def tetrahedronFacesIso :
    ofEdges 4 (faceEdges tetrahedronFaces) ≃cg complete 4 := isoOfKeyEq (by native_decide)

/-- The face list of the cube describes the cube. -/
noncomputable def cubeFacesIso :
    ofEdges 8 (faceEdges cubeFaces) ≃cg hypercube 3 := isoOfKeyEq (by native_decide)

/-- The face list of the octahedron describes the octahedron. -/
noncomputable def octahedronFacesIso :
    ofEdges 6 (faceEdges octahedronFaces) ≃cg cocktailParty 3 := isoOfKeyEq (by native_decide)

end

end NamedGraphs
