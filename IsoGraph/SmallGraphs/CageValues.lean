import IsoGraph.SmallGraphs.Operators

/-!
# The cages and the named cubic graphs: the four co-NP invariants

The independence, clique, chromatic and edge chromatic numbers of the gallery's cages and of the
small named graphs that go with them, in the same style as `SmallGraphs.SatValues`: the refutation
half by `graph_sat native`, the witness half by a table.

Where the library already knows enough the refutation is skipped — a graph of girth greater than
three has `ω = 2` by `cliqueNum_le_two_of_girth_ne_three`, a bipartite graph has `χ = 2` by
`chromNum_eq_two_iff`, and a non-bipartite one has `χ ≥ 3` by `three_le_chromNum`.  What is left
for the solver is every independence number, the two graphs that need four colours, and the one
graph here that is class two: the Holt graph.
-/

namespace NamedGraphs

open CGraph

/-! ## The Moser spindle

Seven points of the plane at unit distance that cannot be two-coloured without a monochromatic
pair, so `χ = 4`: the first lower bound for the Hadwiger–Nelson problem. -/

@[simp] theorem maxDeg_moserSpindle : moserSpindle.maxDeg = 4 := by
  native_decide

/-- **The independence number of the Moser spindle is two.** -/
@[simp] theorem indepNum_moserSpindle : moserSpindle.indepNum = 2 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := moserSpindle)
    (l := ([3, 5] : List (Fin 7)))
    (by decide) (by native_decide)

/-- **The clique number of the Moser spindle is three.** -/
@[simp] theorem cliqueNum_moserSpindle : moserSpindle.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := moserSpindle)
    (l := ([4, 5, 6] : List (Fin 7))) (by decide) (by native_decide)

/-- A proper four-colouring of the Moser spindle. -/
def moserSpindleColTable : List ℕ :=
  [0, 1, 2, 0, 1, 2, 3]

/-- The table `moserSpindleColTable` read as a colouring, clamped into `Fin 4`. -/
def moserSpindleCol (v : moserSpindle.V) : Fin 4 :=
  ⟨min (moserSpindleColTable.getD v.1 0) 3, by omega⟩

theorem moserSpindleCol_proper : ∀ u v : moserSpindle.V,
    moserSpindle.Adj u v = true →
      moserSpindleCol u ≠ moserSpindleCol v := by native_decide

/-- **The Moser spindle needs four colours**, by a SAT refutation of the three-colour system. -/
theorem four_le_chromNum_moserSpindle : 4 ≤ moserSpindle.chromNum := by
  show 3 < moserSpindle.chromNum
  graph_sat native

/-- **The chromatic number of the Moser spindle is four.** -/
@[simp] theorem chromNum_moserSpindle : moserSpindle.chromNum = 4 :=
  le_antisymm (chromNum_le_of_colouring moserSpindleCol moserSpindleCol_proper)
    (four_le_chromNum_moserSpindle)

/-- A proper four-edge-colouring of the Moser spindle, as a symmetric table; the entries off the
edge set are `0`. -/
def moserSpindleEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 0, 2, 3, 0],
   [0, 0, 2, 1, 0, 0, 0],
   [1, 2, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 2],
   [2, 0, 0, 0, 0, 0, 3],
   [3, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 2, 3, 1, 0]]

/-- The table `moserSpindleEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def moserSpindleEdgeCol (x y : moserSpindle.V) : Fin 4 :=
  ⟨min ((moserSpindleEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem moserSpindleEdgeCol_symm : ∀ x y : moserSpindle.V,
    moserSpindleEdgeCol x y = moserSpindleEdgeCol y x := by native_decide

theorem moserSpindleEdgeCol_proper : ∀ u v w : moserSpindle.V,
    moserSpindle.Adj u v = true → moserSpindle.Adj u w = true → v ≠ w →
      moserSpindleEdgeCol u v ≠ moserSpindleEdgeCol u w := by native_decide

/-- **The Moser spindle is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_moserSpindle : moserSpindle.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := moserSpindle)
      moserSpindleEdgeCol moserSpindleEdgeCol_symm
      moserSpindleEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum moserSpindle
    rwa [maxDeg_moserSpindle] at h

/-! ## The Herschel graph

The smallest polyhedral graph with no Hamiltonian cycle: bipartite on eleven vertices, with
three vertices of degree four and eight of degree three. -/

@[simp] theorem maxDeg_herschel : herschel.maxDeg = 4 := by
  native_decide

/-- **The independence number of the Herschel graph is six.** -/
@[simp] theorem indepNum_herschel : herschel.indepNum = 6 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := herschel)
    (l := ([1, 2, 3, 4, 9, 10] : List (Fin 11)))
    (by decide) (by native_decide)

/-- **The Herschel graph has no triangle**, having girth four, so its cliques are its edges. -/
@[simp] theorem cliqueNum_herschel : herschel.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_herschel]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_herschel]; decide))

/-- **The Herschel graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_herschel : herschel.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_herschel, by rw [E_herschel]; decide⟩

/-- A proper four-edge-colouring of the Herschel graph, as a symmetric table; the entries off the
edge set are `0`. -/
def herschelEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3],
   [0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0],
   [0, 0, 0, 0, 0, 2, 1, 0, 3, 0, 0]]

/-- The table `herschelEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def herschelEdgeCol (x y : herschel.V) : Fin 4 :=
  ⟨min ((herschelEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem herschelEdgeCol_symm : ∀ x y : herschel.V,
    herschelEdgeCol x y = herschelEdgeCol y x := by native_decide

theorem herschelEdgeCol_proper : ∀ u v w : herschel.V,
    herschel.Adj u v = true → herschel.Adj u w = true → v ≠ w →
      herschelEdgeCol u v ≠ herschelEdgeCol u w := by native_decide

/-- **The Herschel graph is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_herschel : herschel.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := herschel)
      herschelEdgeCol herschelEdgeCol_symm
      herschelEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum herschel
    rwa [maxDeg_herschel] at h

/-! ## The Franklin graph

The Möbius–Kantor graph's smaller cousin: cubic, bipartite and vertex-transitive on twelve
vertices, and the six-vertex colour classes are the largest independent sets. -/

@[simp] theorem maxDeg_franklin : franklin.maxDeg = 3 :=
  haveI : Nonempty franklin.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_franklin).maxDeg_eq

/-- **The independence number of the Franklin graph is six.** -/
@[simp, toIsoGraph] theorem indepNum_franklin : franklin.indepNum = 6 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := franklin)
    (l := ([1, 3, 5, 7, 9, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The Franklin graph has no triangle**, having girth four, so its cliques are its edges. -/
@[simp] theorem cliqueNum_franklin : franklin.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_franklin]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_franklin]; decide))

/-- **The Franklin graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_franklin : franklin.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_franklin, by rw [E_franklin]; decide⟩

/-- A proper three-edge-colouring of the Franklin graph, as a symmetric table; the entries off
the edge set are `0`. -/
def franklinEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0],
   [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1],
   [0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0],
   [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]

/-- The table `franklinEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def franklinEdgeCol (x y : franklin.V) : Fin 3 :=
  ⟨min ((franklinEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem franklinEdgeCol_symm : ∀ x y : franklin.V,
    franklinEdgeCol x y = franklinEdgeCol y x := by native_decide

theorem franklinEdgeCol_proper : ∀ u v w : franklin.V,
    franklin.Adj u v = true → franklin.Adj u w = true → v ≠ w →
      franklinEdgeCol u v ≠ franklinEdgeCol u w := by native_decide

/-- **The Franklin graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_franklin : franklin.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := franklin)
      franklinEdgeCol franklinEdgeCol_symm
      franklinEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum franklin
    rwa [maxDeg_franklin] at h

/-! ## The Frucht graph

The smallest cubic graph with trivial automorphism group.  Its girth is three, so it has a
triangle, and three colours suffice at both the vertices and the edges. -/

@[simp] theorem maxDeg_frucht : frucht.maxDeg = 3 :=
  haveI : Nonempty frucht.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_frucht).maxDeg_eq

/-- **The independence number of the Frucht graph is five.** -/
@[simp] theorem indepNum_frucht : frucht.indepNum = 5 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := frucht)
    (l := ([2, 5, 7, 9, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The clique number of the Frucht graph is three.** -/
@[simp] theorem cliqueNum_frucht : frucht.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := frucht)
    (l := ([0, 1, 11] : List (Fin 12))) (by decide) (by native_decide)

/-- A proper three-colouring of the Frucht graph. -/
def fruchtColTable : List ℕ :=
  [0, 1, 0, 1, 0, 2, 0, 2, 1, 2, 1, 2]

/-- The table `fruchtColTable` read as a colouring, clamped into `Fin 3`. -/
def fruchtCol (v : frucht.V) : Fin 3 :=
  ⟨min (fruchtColTable.getD v.1 0) 2, by omega⟩

theorem fruchtCol_proper : ∀ u v : frucht.V,
    frucht.Adj u v = true →
      fruchtCol u ≠ fruchtCol v := by native_decide

/-- **The chromatic number of the Frucht graph is three.** -/
@[simp] theorem chromNum_frucht : frucht.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring fruchtCol fruchtCol_proper)
    (three_le_chromNum not_isBipartite_frucht)

/-- A proper three-edge-colouring of the Frucht graph, as a symmetric table; the entries off the
edge set are `0`. -/
def fruchtEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `fruchtEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def fruchtEdgeCol (x y : frucht.V) : Fin 3 :=
  ⟨min ((fruchtEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem fruchtEdgeCol_symm : ∀ x y : frucht.V,
    fruchtEdgeCol x y = fruchtEdgeCol y x := by native_decide

theorem fruchtEdgeCol_proper : ∀ u v w : frucht.V,
    frucht.Adj u v = true → frucht.Adj u w = true → v ≠ w →
      fruchtEdgeCol u v ≠ fruchtEdgeCol u w := by native_decide

/-- **The Frucht graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_frucht : frucht.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := frucht)
      fruchtEdgeCol fruchtEdgeCol_symm
      fruchtEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum frucht
    rwa [maxDeg_frucht] at h

/-! ## The Dürer graph

The generalised Petersen graph `GP(6, 2)`, whose inner star is two triangles; those triangles
are the largest cliques and they cut the independence number down to four. -/

@[simp] theorem maxDeg_durer : durer.maxDeg = 3 :=
  haveI : Nonempty durer.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_durer).maxDeg_eq

/-- **The independence number of the Dürer graph is four.** -/
@[simp] theorem indepNum_durer : durer.indepNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := durer)
    (l := ([1, 4, 8, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The clique number of the Dürer graph is three.** -/
@[simp] theorem cliqueNum_durer : durer.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := durer)
    (l := ([7, 9, 11] : List (Fin 12))) (by decide) (by native_decide)

/-- A proper three-colouring of the Dürer graph. -/
def durerColTable : List ℕ :=
  [0, 1, 0, 2, 1, 2, 1, 2, 2, 0, 0, 1]

/-- The table `durerColTable` read as a colouring, clamped into `Fin 3`. -/
def durerCol (v : durer.V) : Fin 3 :=
  ⟨min (durerColTable.getD v.1 0) 2, by omega⟩

theorem durerCol_proper : ∀ u v : durer.V,
    durer.Adj u v = true →
      durerCol u ≠ durerCol v := by native_decide

/-- **The chromatic number of the Dürer graph is three.** -/
@[simp] theorem chromNum_durer : durer.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring durerCol durerCol_proper)
    (three_le_chromNum not_isBipartite_durer)

/-- A proper three-edge-colouring of the Dürer graph, as a symmetric table; the entries off the
edge set are `0`. -/
def durerEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0],
   [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0]]

/-- The table `durerEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def durerEdgeCol (x y : durer.V) : Fin 3 :=
  ⟨min ((durerEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem durerEdgeCol_symm : ∀ x y : durer.V,
    durerEdgeCol x y = durerEdgeCol y x := by native_decide

theorem durerEdgeCol_proper : ∀ u v w : durer.V,
    durer.Adj u v = true → durer.Adj u w = true → v ≠ w →
      durerEdgeCol u v ≠ durerEdgeCol u w := by native_decide

/-- **The Dürer graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_durer : durer.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := durer)
      durerEdgeCol durerEdgeCol_symm
      durerEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum durer
    rwa [maxDeg_durer] at h

/-! ## The Bidiakis cube

A cubic Hamiltonian graph on twelve vertices, girth four and not bipartite, so `χ = 3`. -/

@[simp] theorem maxDeg_bidiakisCube : bidiakisCube.maxDeg = 3 :=
  haveI : Nonempty bidiakisCube.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_bidiakisCube).maxDeg_eq

/-- **The independence number of the Bidiakis cube is five.** -/
@[simp] theorem indepNum_bidiakisCube : bidiakisCube.indepNum = 5 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := bidiakisCube)
    (l := ([2, 4, 6, 9, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The Bidiakis cube has no triangle**, having girth four, so its cliques are its edges. -/
@[simp] theorem cliqueNum_bidiakisCube : bidiakisCube.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_bidiakisCube]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_bidiakisCube]; decide))

/-- A proper three-colouring of the Bidiakis cube. -/
def bidiakisCubeColTable : List ℕ :=
  [0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2]

/-- The table `bidiakisCubeColTable` read as a colouring, clamped into `Fin 3`. -/
def bidiakisCubeCol (v : bidiakisCube.V) : Fin 3 :=
  ⟨min (bidiakisCubeColTable.getD v.1 0) 2, by omega⟩

theorem bidiakisCubeCol_proper : ∀ u v : bidiakisCube.V,
    bidiakisCube.Adj u v = true →
      bidiakisCubeCol u ≠ bidiakisCubeCol v := by native_decide

/-- **The chromatic number of the Bidiakis cube is three.** -/
@[simp] theorem chromNum_bidiakisCube : bidiakisCube.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring bidiakisCubeCol bidiakisCubeCol_proper)
    (three_le_chromNum not_isBipartite_bidiakisCube)

/-- A proper three-edge-colouring of the Bidiakis cube, as a symmetric table; the entries off the
edge set are `0`. -/
def bidiakisCubeEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

/-- The table `bidiakisCubeEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def bidiakisCubeEdgeCol (x y : bidiakisCube.V) : Fin 3 :=
  ⟨min ((bidiakisCubeEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem bidiakisCubeEdgeCol_symm : ∀ x y : bidiakisCube.V,
    bidiakisCubeEdgeCol x y = bidiakisCubeEdgeCol y x := by native_decide

theorem bidiakisCubeEdgeCol_proper : ∀ u v w : bidiakisCube.V,
    bidiakisCube.Adj u v = true → bidiakisCube.Adj u w = true → v ≠ w →
      bidiakisCubeEdgeCol u v ≠ bidiakisCubeEdgeCol u w := by native_decide

/-- **The Bidiakis cube is class one**: `χ' = Δ = 3`. -/
@[simp, toIsoGraph] theorem edgeChromNum_bidiakisCube : bidiakisCube.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := bidiakisCube)
      bidiakisCubeEdgeCol bidiakisCubeEdgeCol_symm
      bidiakisCubeEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum bidiakisCube
    rwa [maxDeg_bidiakisCube] at h

/-! ## The Heawood graph

The `(3, 6)`-cage — the incidence graph of the Fano plane — bipartite and cubic on fourteen
vertices.  Each side of the bipartition is a maximum independent set. -/

@[simp] theorem maxDeg_heawood : heawood.maxDeg = 3 :=
  haveI : Nonempty heawood.V := ⟨(0 : Fin 14)⟩
  (isRegularWith_heawood).maxDeg_eq

/-- **The independence number of the Heawood graph is seven.** -/
@[simp] theorem indepNum_heawood : heawood.indepNum = 7 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := heawood)
    (l := ([1, 3, 5, 7, 9, 11, 13] : List (Fin 14)))
    (by decide) (by native_decide)

/-- **The Heawood graph has no triangle**, having girth six, so its cliques are its edges. -/
@[simp] theorem cliqueNum_heawood : heawood.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_heawood]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_heawood]; decide))

/-- **The Heawood graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_heawood : heawood.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_heawood, by rw [E_heawood]; decide⟩

/-- A proper three-edge-colouring of the Heawood graph, as a symmetric table; the entries off the
edge set are `0`. -/
def heawoodEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0],
   [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]

/-- The table `heawoodEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def heawoodEdgeCol (x y : heawood.V) : Fin 3 :=
  ⟨min ((heawoodEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem heawoodEdgeCol_symm : ∀ x y : heawood.V,
    heawoodEdgeCol x y = heawoodEdgeCol y x := by native_decide

theorem heawoodEdgeCol_proper : ∀ u v w : heawood.V,
    heawood.Adj u v = true → heawood.Adj u w = true → v ≠ w →
      heawoodEdgeCol u v ≠ heawoodEdgeCol u w := by native_decide

/-- **The Heawood graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_heawood : heawood.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := heawood)
      heawoodEdgeCol heawoodEdgeCol_symm
      heawoodEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum heawood
    rwa [maxDeg_heawood] at h

/-! ## The Möbius–Kantor graph

The generalised Petersen graph `GP(8, 3)`: cubic, bipartite, girth six, and the two sides of
the bipartition are the maximum independent sets. -/

@[simp] theorem maxDeg_mobiusKantor : mobiusKantor.maxDeg = 3 :=
  haveI : Nonempty mobiusKantor.V := ⟨(0 : Fin 16)⟩
  (isRegularWith_mobiusKantor).maxDeg_eq

/-- **The independence number of the Möbius–Kantor graph is eight.** -/
@[simp] theorem indepNum_mobiusKantor : mobiusKantor.indepNum = 8 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := mobiusKantor)
    (l := ([0, 2, 4, 6, 9, 11, 13, 15] : List (Fin 16)))
    (by decide) (by native_decide)

/-- **The Möbius–Kantor graph has no triangle**, having girth six, so its cliques are its edges. -/
@[simp] theorem cliqueNum_mobiusKantor : mobiusKantor.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_mobiusKantor]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_mobiusKantor]; decide))

/-- **The Möbius–Kantor graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_mobiusKantor : mobiusKantor.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_mobiusKantor, by rw [E_mobiusKantor]; decide⟩

/-- A proper three-edge-colouring of the Möbius–Kantor graph, as a symmetric table; the entries
off the edge set are `0`. -/
def mobiusKantorEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0]]

/-- The table `mobiusKantorEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def mobiusKantorEdgeCol (x y : mobiusKantor.V) : Fin 3 :=
  ⟨min ((mobiusKantorEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem mobiusKantorEdgeCol_symm : ∀ x y : mobiusKantor.V,
    mobiusKantorEdgeCol x y = mobiusKantorEdgeCol y x := by native_decide

theorem mobiusKantorEdgeCol_proper : ∀ u v w : mobiusKantor.V,
    mobiusKantor.Adj u v = true → mobiusKantor.Adj u w = true → v ≠ w →
      mobiusKantorEdgeCol u v ≠ mobiusKantorEdgeCol u w := by native_decide

/-- **The Möbius–Kantor graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_mobiusKantor : mobiusKantor.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := mobiusKantor)
      mobiusKantorEdgeCol mobiusKantorEdgeCol_symm
      mobiusKantorEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum mobiusKantor
    rwa [maxDeg_mobiusKantor] at h

/-! ## The Pappus graph

The incidence graph of the Pappus configuration: cubic and bipartite on eighteen vertices,
girth six. -/

@[simp] theorem maxDeg_pappus : pappus.maxDeg = 3 :=
  haveI : Nonempty pappus.V := ⟨(0 : Fin 18)⟩
  (isRegularWith_pappus).maxDeg_eq

/-- **The independence number of the Pappus graph is nine.** -/
@[simp] theorem indepNum_pappus : pappus.indepNum = 9 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := pappus)
    (l := ([1, 3, 5, 7, 9, 11, 13, 15, 17] : List (Fin 18)))
    (by decide) (by native_decide)

/-- **The Pappus graph has no triangle**, having girth six, so its cliques are its edges. -/
@[simp, toIsoGraph] theorem cliqueNum_pappus : pappus.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_pappus]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_pappus]; decide))

/-- **The Pappus graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_pappus : pappus.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_pappus, by rw [E_pappus]; decide⟩

/-- A proper three-edge-colouring of the Pappus graph, as a symmetric table; the entries off the
edge set are `0`. -/
def pappusEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]

/-- The table `pappusEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def pappusEdgeCol (x y : pappus.V) : Fin 3 :=
  ⟨min ((pappusEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem pappusEdgeCol_symm : ∀ x y : pappus.V,
    pappusEdgeCol x y = pappusEdgeCol y x := by native_decide

theorem pappusEdgeCol_proper : ∀ u v w : pappus.V,
    pappus.Adj u v = true → pappus.Adj u w = true → v ≠ w →
      pappusEdgeCol u v ≠ pappusEdgeCol u w := by native_decide

/-- **The Pappus graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_pappus : pappus.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := pappus)
      pappusEdgeCol pappusEdgeCol_symm
      pappusEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum pappus
    rwa [maxDeg_pappus] at h

/-! ## The Desargues graph

The bipartite double cover of the Petersen graph, `GP(10, 3)`: cubic, bipartite, girth six. -/

@[simp] theorem maxDeg_desargues : desargues.maxDeg = 3 :=
  haveI : Nonempty desargues.V := ⟨(0 : Fin 20)⟩
  (isRegularWith_desargues).maxDeg_eq

/-- **The independence number of the Desargues graph is ten.** -/
@[simp] theorem indepNum_desargues : desargues.indepNum = 10 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := desargues)
    (l := ([1, 3, 5, 7, 9, 10, 12, 14, 16, 18] : List (Fin 20)))
    (by decide) (by native_decide)

/-- **The Desargues graph has no triangle**, having girth six, so its cliques are its edges. -/
@[simp] theorem cliqueNum_desargues : desargues.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_desargues]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_desargues]; decide))

/-- **The Desargues graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_desargues : desargues.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_desargues, by rw [E_desargues]; decide⟩

/-- A proper three-edge-colouring of the Desargues graph, as a symmetric table; the entries off
the edge set are `0`. -/
def desarguesEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `desarguesEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def desarguesEdgeCol (x y : desargues.V) : Fin 3 :=
  ⟨min ((desarguesEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem desarguesEdgeCol_symm : ∀ x y : desargues.V,
    desarguesEdgeCol x y = desarguesEdgeCol y x := by native_decide

theorem desarguesEdgeCol_proper : ∀ u v w : desargues.V,
    desargues.Adj u v = true → desargues.Adj u w = true → v ≠ w →
      desarguesEdgeCol u v ≠ desarguesEdgeCol u w := by native_decide

/-- **The Desargues graph is class one**: `χ' = Δ = 3`. -/
@[simp, toIsoGraph] theorem edgeChromNum_desargues : desargues.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := desargues)
      desarguesEdgeCol desarguesEdgeCol_symm
      desarguesEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum desargues
    rwa [maxDeg_desargues] at h

/-! ## The Folkman graph

The smallest edge-transitive but not vertex-transitive graph: four-regular, bipartite, twenty
vertices. -/

@[simp] theorem maxDeg_folkman : folkman.maxDeg = 4 :=
  haveI : Nonempty folkman.V := ⟨(0 : Fin 20)⟩
  (isRegularWith_folkman).maxDeg_eq

/-- **The independence number of the Folkman graph is ten.** -/
@[simp] theorem indepNum_folkman : folkman.indepNum = 10 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := folkman)
    (l := ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19] : List (Fin 20)))
    (by decide) (by native_decide)

/-- **The Folkman graph has no triangle**, having girth four, so its cliques are its edges. -/
@[simp] theorem cliqueNum_folkman : folkman.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_folkman]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_folkman]; decide))

/-- **The Folkman graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_folkman : folkman.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_folkman, by rw [E_folkman]; decide⟩

/-- A proper four-edge-colouring of the Folkman graph, as a symmetric table; the entries off the
edge set are `0`. -/
def folkmanEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0],
   [0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0],
   [0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0],
   [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 1, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0],
   [3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `folkmanEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def folkmanEdgeCol (x y : folkman.V) : Fin 4 :=
  ⟨min ((folkmanEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem folkmanEdgeCol_symm : ∀ x y : folkman.V,
    folkmanEdgeCol x y = folkmanEdgeCol y x := by native_decide

theorem folkmanEdgeCol_proper : ∀ u v w : folkman.V,
    folkman.Adj u v = true → folkman.Adj u w = true → v ≠ w →
      folkmanEdgeCol u v ≠ folkmanEdgeCol u w := by native_decide

/-- **The Folkman graph is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_folkman : folkman.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := folkman)
      folkmanEdgeCol folkmanEdgeCol_symm
      folkmanEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum folkman
    rwa [maxDeg_folkman] at h

/-! ## The McGee graph

The `(3, 7)`-cage: cubic of girth seven on twenty-four vertices, and the smallest cubic cage
of odd girth, so three colours are needed. -/

@[simp] theorem maxDeg_mcgee : mcgee.maxDeg = 3 :=
  haveI : Nonempty mcgee.V := ⟨(0 : Fin 24)⟩
  (isRegularWith_mcgee).maxDeg_eq

/-- **The independence number of the McGee graph is ten.** -/
@[simp] theorem indepNum_mcgee : mcgee.indepNum = 10 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := mcgee)
    (l := ([1, 5, 7, 11, 13, 15, 17, 19, 21, 23] : List (Fin 24)))
    (by decide) (by native_decide)

/-- **The McGee graph has no triangle**, having girth seven, so its cliques are its edges. -/
@[simp] theorem cliqueNum_mcgee : mcgee.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_mcgee]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_mcgee]; decide))

/-- A proper three-colouring of the McGee graph. -/
def mcgeeColTable : List ℕ :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 2, 1, 2, 1, 2, 0, 2]

/-- The table `mcgeeColTable` read as a colouring, clamped into `Fin 3`. -/
def mcgeeCol (v : mcgee.V) : Fin 3 :=
  ⟨min (mcgeeColTable.getD v.1 0) 2, by omega⟩

theorem mcgeeCol_proper : ∀ u v : mcgee.V,
    mcgee.Adj u v = true →
      mcgeeCol u ≠ mcgeeCol v := by native_decide

/-- **The chromatic number of the McGee graph is three.** -/
@[simp] theorem chromNum_mcgee : mcgee.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring mcgeeCol mcgeeCol_proper)
    (three_le_chromNum not_isBipartite_mcgee)

/-- A proper three-edge-colouring of the McGee graph, as a symmetric table; the entries off the
edge set are `0`. -/
def mcgeeEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

/-- The table `mcgeeEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def mcgeeEdgeCol (x y : mcgee.V) : Fin 3 :=
  ⟨min ((mcgeeEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem mcgeeEdgeCol_symm : ∀ x y : mcgee.V,
    mcgeeEdgeCol x y = mcgeeEdgeCol y x := by native_decide

theorem mcgeeEdgeCol_proper : ∀ u v w : mcgee.V,
    mcgee.Adj u v = true → mcgee.Adj u w = true → v ≠ w →
      mcgeeEdgeCol u v ≠ mcgeeEdgeCol u w := by native_decide

/-- **The McGee graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_mcgee : mcgee.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := mcgee)
      mcgeeEdgeCol mcgeeEdgeCol_symm
      mcgeeEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum mcgee
    rwa [maxDeg_mcgee] at h

/-! ## The Nauru graph

The generalised Petersen graph `GP(12, 5)`: cubic, bipartite, girth six, twenty-four vertices. -/

@[simp] theorem maxDeg_nauru : nauru.maxDeg = 3 :=
  haveI : Nonempty nauru.V := ⟨(0 : Fin 24)⟩
  (isRegularWith_nauru).maxDeg_eq

/-- **The independence number of the Nauru graph is twelve.** -/
@[simp, toIsoGraph] theorem indepNum_nauru : nauru.indepNum = 12 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := nauru)
    (l := ([0, 2, 4, 6, 8, 10, 13, 15, 17, 19, 21, 23] : List (Fin 24)))
    (by decide) (by native_decide)

/-- **The Nauru graph has no triangle**, having girth six, so its cliques are its edges. -/
@[simp, toIsoGraph] theorem cliqueNum_nauru : nauru.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_nauru]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_nauru]; decide))

/-- **The Nauru graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_nauru : nauru.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_nauru, by rw [E_nauru]; decide⟩

/-- A proper three-edge-colouring of the Nauru graph, as a symmetric table; the entries off the
edge set are `0`. -/
def nauruEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `nauruEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def nauruEdgeCol (x y : nauru.V) : Fin 3 :=
  ⟨min ((nauruEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem nauruEdgeCol_symm : ∀ x y : nauru.V,
    nauruEdgeCol x y = nauruEdgeCol y x := by native_decide

theorem nauruEdgeCol_proper : ∀ u v w : nauru.V,
    nauru.Adj u v = true → nauru.Adj u w = true → v ≠ w →
      nauruEdgeCol u v ≠ nauruEdgeCol u w := by native_decide

/-- **The Nauru graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_nauru : nauru.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := nauru)
      nauruEdgeCol nauruEdgeCol_symm
      nauruEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum nauru
    rwa [maxDeg_nauru] at h

/-! ## The Holt graph

The smallest half-transitive graph: four-regular on twenty-seven vertices, vertex- and
edge-transitive but not arc-transitive.  Its odd order already rules out a four-edge-colouring —
four matchings on twenty-seven vertices cover at most fifty-two of its fifty-four edges — and the
SAT refutation below confirms it. -/

@[simp] theorem maxDeg_holt : holt.maxDeg = 4 :=
  haveI : Nonempty holt.V := ⟨(0 : Fin 27)⟩
  (isRegularWith_holt).maxDeg_eq

/-- **The independence number of the Holt graph is ten.** -/
@[simp] theorem indepNum_holt : holt.indepNum = 10 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := holt)
    (l := ([5, 9, 11, 17, 21, 22, 23, 24, 25, 26] : List (Fin 27)))
    (by decide) (by native_decide)

/-- **The Holt graph has no triangle**, having girth five, so its cliques are its edges. -/
@[simp] theorem cliqueNum_holt : holt.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_holt]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_holt]; decide))

/-- A proper three-colouring of the Holt graph. -/
def holtColTable : List ℕ :=
  [0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 0, 0, 2, 2, 2, 2, 2, 2]

/-- The table `holtColTable` read as a colouring, clamped into `Fin 3`. -/
def holtCol (v : holt.V) : Fin 3 :=
  ⟨min (holtColTable.getD v.1 0) 2, by omega⟩

theorem holtCol_proper : ∀ u v : holt.V,
    holt.Adj u v = true →
      holtCol u ≠ holtCol v := by native_decide

/-- **The chromatic number of the Holt graph is three.** -/
@[simp] theorem chromNum_holt : holt.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring holtCol holtCol_proper)
    (three_le_chromNum not_isBipartite_holt)

/-- A proper five-edge-colouring of the Holt graph, as a symmetric table; the entries off the
edge set are `0`. -/
def holtEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3],
   [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0],
   [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0],
   [0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0],
   [0, 0, 3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
   [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `holtEdgeColTable` read as an edge colouring, clamped into `Fin 5`. -/
def holtEdgeCol (x y : holt.V) : Fin 5 :=
  ⟨min ((holtEdgeColTable.getD x.1 []).getD y.1 0) 4, by omega⟩

theorem holtEdgeCol_symm : ∀ x y : holt.V,
    holtEdgeCol x y = holtEdgeCol y x := by native_decide

theorem holtEdgeCol_proper : ∀ u v w : holt.V,
    holt.Adj u v = true → holt.Adj u w = true → v ≠ w →
      holtEdgeCol u v ≠ holtEdgeCol u w := by native_decide

/-- **The Holt graph is class two**: four colours do not suffice, by a SAT refutation over the
line graph. -/
theorem five_le_edgeChromNum_holt : 5 ≤ holt.edgeChromNum := by
  show 4 < holt.edgeChromNum
  graph_sat native

/-- **The chromatic index of the Holt graph is five.** -/
@[simp] theorem edgeChromNum_holt : holt.edgeChromNum = 5 := by
  refine le_antisymm ?_ five_le_edgeChromNum_holt
  rw [← IsoGraph.edgeChromNum_mk]
  exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := holt)
    holtEdgeCol holtEdgeCol_symm holtEdgeCol_proper

/-! ## The Coxeter graph

Cubic, distance-regular and vertex-transitive on twenty-eight vertices, girth seven.  It is
one of the few vertex-transitive graphs with no Hamiltonian cycle, and it is class one. -/

@[simp] theorem maxDeg_coxeter : coxeter.maxDeg = 3 :=
  haveI : Nonempty coxeter.V := ⟨(0 : Fin 28)⟩
  (isRegularWith_coxeter).maxDeg_eq

/-- **The independence number of the Coxeter graph is twelve.** -/
@[simp] theorem indepNum_coxeter : coxeter.indepNum = 12 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := coxeter)
    (l := ([2, 4, 6, 7, 8, 10, 16, 19, 20, 25, 26, 27] : List (Fin 28)))
    (by decide) (by native_decide)

/-- **The Coxeter graph has no triangle**, having girth seven, so its cliques are its edges. -/
@[simp] theorem cliqueNum_coxeter : coxeter.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_coxeter]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_coxeter]; decide))

/-- A proper three-colouring of the Coxeter graph. -/
def coxeterColTable : List ℕ :=
  [0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 0, 0, 1, 2, 2, 0, 1, 2, 0, 1, 0, 1, 2, 2, 2]

/-- The table `coxeterColTable` read as a colouring, clamped into `Fin 3`. -/
def coxeterCol (v : coxeter.V) : Fin 3 :=
  ⟨min (coxeterColTable.getD v.1 0) 2, by omega⟩

theorem coxeterCol_proper : ∀ u v : coxeter.V,
    coxeter.Adj u v = true →
      coxeterCol u ≠ coxeterCol v := by native_decide

/-- **The chromatic number of the Coxeter graph is three.** -/
@[simp] theorem chromNum_coxeter : coxeter.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring coxeterCol coxeterCol_proper)
    (three_le_chromNum not_isBipartite_coxeter)

/-- A proper three-edge-colouring of the Coxeter graph, as a symmetric table; the entries off the
edge set are `0`. -/
def coxeterEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]]

/-- The table `coxeterEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def coxeterEdgeCol (x y : coxeter.V) : Fin 3 :=
  ⟨min ((coxeterEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem coxeterEdgeCol_symm : ∀ x y : coxeter.V,
    coxeterEdgeCol x y = coxeterEdgeCol y x := by native_decide

theorem coxeterEdgeCol_proper : ∀ u v w : coxeter.V,
    coxeter.Adj u v = true → coxeter.Adj u w = true → v ≠ w →
      coxeterEdgeCol u v ≠ coxeterEdgeCol u w := by native_decide

/-- **The Coxeter graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_coxeter : coxeter.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coxeter)
      coxeterEdgeCol coxeterEdgeCol_symm
      coxeterEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum coxeter
    rwa [maxDeg_coxeter] at h

/-! ## The Tutte–Coxeter graph

Levi's graph of the generalised quadrangle `W(2)`: the `(3, 8)`-cage, cubic and bipartite on
thirty vertices. -/

@[simp, toIsoGraph] theorem maxDeg_tutteCoxeter : tutteCoxeter.maxDeg = 3 :=
  haveI : Nonempty tutteCoxeter.V := ⟨(0 : Fin 30)⟩
  (isRegularWith_tutteCoxeter).maxDeg_eq

/-- **The independence number of the Tutte–Coxeter graph is fifteen.** -/
@[simp] theorem indepNum_tutteCoxeter : tutteCoxeter.indepNum = 15 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := tutteCoxeter)
    (l := ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29] : List (Fin 30)))
    (by decide) (by native_decide)

/-- **The Tutte–Coxeter graph has no triangle**, having girth eight, so its cliques are its
edges. -/
@[simp] theorem cliqueNum_tutteCoxeter : tutteCoxeter.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_tutteCoxeter]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_tutteCoxeter]; decide))

/-- **The Tutte–Coxeter graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_tutteCoxeter : tutteCoxeter.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_tutteCoxeter, by rw [E_tutteCoxeter]; decide⟩

/-- A proper three-edge-colouring of the Tutte–Coxeter graph, as a symmetric table; the entries
off the edge set are `0`. -/
def tutteCoxeterEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `tutteCoxeterEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def tutteCoxeterEdgeCol (x y : tutteCoxeter.V) : Fin 3 :=
  ⟨min ((tutteCoxeterEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem tutteCoxeterEdgeCol_symm : ∀ x y : tutteCoxeter.V,
    tutteCoxeterEdgeCol x y = tutteCoxeterEdgeCol y x := by native_decide

theorem tutteCoxeterEdgeCol_proper : ∀ u v w : tutteCoxeter.V,
    tutteCoxeter.Adj u v = true → tutteCoxeter.Adj u w = true → v ≠ w →
      tutteCoxeterEdgeCol u v ≠ tutteCoxeterEdgeCol u w := by native_decide

/-- **The Tutte–Coxeter graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_tutteCoxeter : tutteCoxeter.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tutteCoxeter)
      tutteCoxeterEdgeCol tutteCoxeterEdgeCol_symm
      tutteCoxeterEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum tutteCoxeter
    rwa [maxDeg_tutteCoxeter] at h

/-! ## The Dyck graph

Cubic, bipartite and symmetric on thirty-two vertices, girth six — one of the three cubic
symmetric graphs of that order. -/

@[simp] theorem maxDeg_dyck : dyck.maxDeg = 3 :=
  haveI : Nonempty dyck.V := ⟨(0 : Fin 32)⟩
  (isRegularWith_dyck).maxDeg_eq

/-- **The independence number of the Dyck graph is sixteen.** -/
@[simp] theorem indepNum_dyck : dyck.indepNum = 16 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := dyck)
    (l := ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31] : List (Fin 32)))
    (by decide) (by native_decide)

/-- **The Dyck graph has no triangle**, having girth six, so its cliques are its edges. -/
@[simp] theorem cliqueNum_dyck : dyck.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_dyck]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_dyck]; decide))

/-- **The Dyck graph is bipartite**, so two colours do and one does not. -/
@[simp, toIsoGraph] theorem chromNum_dyck : dyck.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_dyck, by rw [E_dyck]; decide⟩

/-- A proper three-edge-colouring of the Dyck graph, as a symmetric table; the entries off the
edge set are `0`. -/
def dyckEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

/-- The table `dyckEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def dyckEdgeCol (x y : dyck.V) : Fin 3 :=
  ⟨min ((dyckEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem dyckEdgeCol_symm : ∀ x y : dyck.V,
    dyckEdgeCol x y = dyckEdgeCol y x := by native_decide

theorem dyckEdgeCol_proper : ∀ u v w : dyck.V,
    dyck.Adj u v = true → dyck.Adj u w = true → v ≠ w →
      dyckEdgeCol u v ≠ dyckEdgeCol u w := by native_decide

/-- **The Dyck graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_dyck : dyck.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := dyck)
      dyckEdgeCol dyckEdgeCol_symm
      dyckEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum dyck
    rwa [maxDeg_dyck] at h

end NamedGraphs
