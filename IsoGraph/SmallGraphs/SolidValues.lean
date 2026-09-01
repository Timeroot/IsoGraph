import IsoGraph.SmallGraphs.Operators

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The solids: independence, clique, chromatic and edge chromatic numbers

The four co-NP invariants for the Platonic, Archimedean and Catalan solids of the gallery.  Each
value needs a bound in both directions, and the two directions are proved by opposite means:

* the refutation — `α ≤ n`, `ω ≤ n`, `k < χ` — goes to `graph_sat native`, which hands the formula
  to a SAT solver, except where girth or a clique already settles it;
* the witness — an independent set, a clique, a colouring, an edge colouring — is a table found by
  machine and checked here, through `le_indepNum_of_nodup`, `le_cliqueNum_of_nodup`,
  `chromNum_le_of_colouring` and `edgeChromNum_mk_le_of_colouring`.

Every solid here is class one, so the chromatic index is `Δ` and the lower bound is
`maxDeg_le_edgeChromNum` rather than a refutation; the `maxDeg` values themselves are recorded
along the way.
-/

namespace NamedGraphs

open CGraph

/-! ## The truncated tetrahedron

Four disjoint triangles joined by a perfect matching: the triangles force `α ≤ 4` and `ω = 3`,
and both are attained. -/

@[simp] theorem maxDeg_truncatedTetrahedron : truncatedTetrahedron.maxDeg = 3 :=
  haveI : Nonempty truncatedTetrahedron.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_truncatedTetrahedron).maxDeg_eq

/-- **The independence number of the truncated tetrahedron is four.** -/
@[simp] theorem indepNum_truncatedTetrahedron : truncatedTetrahedron.indepNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := truncatedTetrahedron)
    (l := ([2, 6, 8, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The clique number of the truncated tetrahedron is three.** -/
@[simp] theorem cliqueNum_truncatedTetrahedron : truncatedTetrahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := truncatedTetrahedron)
    (l := ([7, 9, 11] : List (Fin 12))) (by decide) (by native_decide)

/-- A proper three-colouring of the truncated tetrahedron. -/
def truncatedTetrahedronColTable : List ℕ :=
  [0, 1, 0, 1, 1, 2, 0, 2, 2, 0, 2, 1]

/-- The table `truncatedTetrahedronColTable` read as a colouring, clamped into `Fin 3`. -/
def truncatedTetrahedronCol (v : truncatedTetrahedron.V) : Fin 3 :=
  ⟨min (truncatedTetrahedronColTable.getD v.1 0) 2, by omega⟩

theorem truncatedTetrahedronCol_proper : ∀ u v : truncatedTetrahedron.V,
    truncatedTetrahedron.Adj u v = true →
      truncatedTetrahedronCol u ≠ truncatedTetrahedronCol v := by native_decide

/-- **The chromatic number of the truncated tetrahedron is three.** -/
@[simp] theorem chromNum_truncatedTetrahedron : truncatedTetrahedron.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring truncatedTetrahedronCol truncatedTetrahedronCol_proper)
    (three_le_chromNum not_isBipartite_truncatedTetrahedron)

/-- A proper three-edge-colouring of the truncated tetrahedron, as a symmetric table; the entries
off the edge set are `0`. -/
def truncatedTetrahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0]]

/-- The table `truncatedTetrahedronEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def truncatedTetrahedronEdgeCol (x y : truncatedTetrahedron.V) : Fin 3 :=
  ⟨min ((truncatedTetrahedronEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem truncatedTetrahedronEdgeCol_symm : ∀ x y : truncatedTetrahedron.V,
    truncatedTetrahedronEdgeCol x y = truncatedTetrahedronEdgeCol y x := by native_decide

theorem truncatedTetrahedronEdgeCol_proper : ∀ u v w : truncatedTetrahedron.V,
    truncatedTetrahedron.Adj u v = true → truncatedTetrahedron.Adj u w = true → v ≠ w →
      truncatedTetrahedronEdgeCol u v ≠ truncatedTetrahedronEdgeCol u w := by native_decide

/-- **The truncated tetrahedron is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_truncatedTetrahedron : truncatedTetrahedron.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := truncatedTetrahedron)
      truncatedTetrahedronEdgeCol truncatedTetrahedronEdgeCol_symm
      truncatedTetrahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum truncatedTetrahedron
    rwa [maxDeg_truncatedTetrahedron] at h

/-! ## The cuboctahedron

The line graph of the cube, so its independent sets are the matchings of `Q₃` and `α = 4` is
the perfect matching. -/

@[simp] theorem maxDeg_cuboctahedron : cuboctahedron.maxDeg = 4 :=
  haveI : Nonempty cuboctahedron.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_cuboctahedron).maxDeg_eq

/-- **The independence number of the cuboctahedron is four.** -/
@[simp] theorem indepNum_cuboctahedron : cuboctahedron.indepNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := cuboctahedron)
    (l := ([1, 4, 9, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The clique number of the cuboctahedron is three.** -/
@[simp] theorem cliqueNum_cuboctahedron : cuboctahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := cuboctahedron)
    (l := ([5, 10, 11] : List (Fin 12))) (by decide) (by native_decide)

/-- A proper three-colouring of the cuboctahedron. -/
def cuboctahedronColTable : List ℕ :=
  [0, 1, 2, 0, 1, 0, 0, 2, 2, 1, 2, 1]

/-- The table `cuboctahedronColTable` read as a colouring, clamped into `Fin 3`. -/
def cuboctahedronCol (v : cuboctahedron.V) : Fin 3 :=
  ⟨min (cuboctahedronColTable.getD v.1 0) 2, by omega⟩

theorem cuboctahedronCol_proper : ∀ u v : cuboctahedron.V,
    cuboctahedron.Adj u v = true →
      cuboctahedronCol u ≠ cuboctahedronCol v := by native_decide

/-- **The chromatic number of the cuboctahedron is three.** -/
@[simp] theorem chromNum_cuboctahedron : cuboctahedron.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring cuboctahedronCol cuboctahedronCol_proper)
    (three_le_chromNum not_isBipartite_cuboctahedron)

/-- A proper four-edge-colouring of the cuboctahedron, as a symmetric table; the entries off the
edge set are `0`. -/
def cuboctahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 3, 0],
   [0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 1, 0],
   [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 3],
   [1, 0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 1],
   [0, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0],
   [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2],
   [2, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0],
   [0, 0, 3, 2, 0, 0, 0, 0, 1, 0, 0, 0],
   [3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0]]

/-- The table `cuboctahedronEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def cuboctahedronEdgeCol (x y : cuboctahedron.V) : Fin 4 :=
  ⟨min ((cuboctahedronEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem cuboctahedronEdgeCol_symm : ∀ x y : cuboctahedron.V,
    cuboctahedronEdgeCol x y = cuboctahedronEdgeCol y x := by native_decide

theorem cuboctahedronEdgeCol_proper : ∀ u v w : cuboctahedron.V,
    cuboctahedron.Adj u v = true → cuboctahedron.Adj u w = true → v ≠ w →
      cuboctahedronEdgeCol u v ≠ cuboctahedronEdgeCol u w := by native_decide

/-- **The cuboctahedron is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_cuboctahedron : cuboctahedron.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := cuboctahedron)
      cuboctahedronEdgeCol cuboctahedronEdgeCol_symm
      cuboctahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum cuboctahedron
    rwa [maxDeg_cuboctahedron] at h

/-! ## The icosahedron

Five-regular on twelve vertices, with twenty triangular faces.  It is the one Platonic solid
that needs four colours, and `α = 3` is as small as a twelve-vertex graph of maximum degree five
can manage. -/

@[simp] theorem maxDeg_icosahedron : icosahedron.maxDeg = 5 :=
  haveI : Nonempty icosahedron.V := ⟨(0 : Fin 12)⟩
  (isRegularWith_icosahedron).maxDeg_eq

/-- **The independence number of the icosahedron is three.** -/
@[simp] theorem indepNum_icosahedron : icosahedron.indepNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := icosahedron)
    (l := ([3, 5, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The clique number of the icosahedron is three.** -/
@[simp] theorem cliqueNum_icosahedron : icosahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := icosahedron)
    (l := ([9, 10, 11] : List (Fin 12))) (by decide) (by native_decide)

/-- A proper four-colouring of the icosahedron. -/
def icosahedronColTable : List ℕ :=
  [0, 1, 2, 1, 2, 3, 3, 0, 3, 0, 2, 1]

/-- The table `icosahedronColTable` read as a colouring, clamped into `Fin 4`. -/
def icosahedronCol (v : icosahedron.V) : Fin 4 :=
  ⟨min (icosahedronColTable.getD v.1 0) 3, by omega⟩

theorem icosahedronCol_proper : ∀ u v : icosahedron.V,
    icosahedron.Adj u v = true →
      icosahedronCol u ≠ icosahedronCol v := by native_decide

/-- **The icosahedron needs four colours**, by a SAT refutation of the three-colour system. -/
theorem four_le_chromNum_icosahedron : 4 ≤ icosahedron.chromNum := by
  show 3 < icosahedron.chromNum
  graph_sat native

/-- **The chromatic number of the icosahedron is four.** -/
@[simp] theorem chromNum_icosahedron : icosahedron.chromNum = 4 :=
  le_antisymm (chromNum_le_of_colouring icosahedronCol icosahedronCol_proper)
    (four_le_chromNum_icosahedron)

/-- A proper five-edge-colouring of the icosahedron, as a symmetric table; the entries off the
edge set are `0`. -/
def icosahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 1, 3, 0, 0, 0, 4, 0],
   [1, 2, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0],
   [2, 0, 3, 0, 1, 0, 0, 0, 4, 0, 0, 0],
   [3, 0, 0, 1, 0, 0, 0, 0, 2, 4, 0, 0],
   [4, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0],
   [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 4],
   [0, 0, 4, 0, 0, 0, 1, 0, 3, 0, 0, 2],
   [0, 0, 0, 4, 2, 0, 0, 3, 0, 0, 0, 1],
   [0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 1, 3],
   [0, 4, 0, 0, 0, 3, 2, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 4, 2, 1, 3, 0, 0]]

/-- The table `icosahedronEdgeColTable` read as an edge colouring, clamped into `Fin 5`. -/
def icosahedronEdgeCol (x y : icosahedron.V) : Fin 5 :=
  ⟨min ((icosahedronEdgeColTable.getD x.1 []).getD y.1 0) 4, by omega⟩

theorem icosahedronEdgeCol_symm : ∀ x y : icosahedron.V,
    icosahedronEdgeCol x y = icosahedronEdgeCol y x := by native_decide

theorem icosahedronEdgeCol_proper : ∀ u v w : icosahedron.V,
    icosahedron.Adj u v = true → icosahedron.Adj u w = true → v ≠ w →
      icosahedronEdgeCol u v ≠ icosahedronEdgeCol u w := by native_decide

/-- **The icosahedron is class one**: `χ' = Δ = 5`. -/
@[simp] theorem edgeChromNum_icosahedron : icosahedron.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := icosahedron)
      icosahedronEdgeCol icosahedronEdgeCol_symm
      icosahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum icosahedron
    rwa [maxDeg_icosahedron] at h

/-! ## The dodecahedron

`GP(10, 2)`: cubic of girth five on twenty vertices.  It is not bipartite — the pentagonal
faces are odd — so three colours are needed, and eight is the largest independent set. -/

@[simp, toIsoGraph] theorem maxDeg_dodecahedron : dodecahedron.maxDeg = 3 :=
  haveI : Nonempty dodecahedron.V := ⟨(0 : Fin 20)⟩
  (isRegularWith_dodecahedron).maxDeg_eq

/-- **The independence number of the dodecahedron is eight.** -/
@[simp] theorem indepNum_dodecahedron : dodecahedron.indepNum = 8 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := dodecahedron)
    (l := ([1, 3, 6, 8, 10, 14, 15, 19] : List (Fin 20)))
    (by decide) (by native_decide)

/-- **The dodecahedron has no triangle**, having girth five, so its cliques are its edges. -/
@[simp] theorem cliqueNum_dodecahedron : dodecahedron.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_dodecahedron]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_dodecahedron]; decide))

/-- A proper three-colouring of the dodecahedron. -/
def dodecahedronColTable : List ℕ :=
  [0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 2, 2, 0, 1, 2, 2, 0, 0, 1]

/-- The table `dodecahedronColTable` read as a colouring, clamped into `Fin 3`. -/
def dodecahedronCol (v : dodecahedron.V) : Fin 3 :=
  ⟨min (dodecahedronColTable.getD v.1 0) 2, by omega⟩

theorem dodecahedronCol_proper : ∀ u v : dodecahedron.V,
    dodecahedron.Adj u v = true →
      dodecahedronCol u ≠ dodecahedronCol v := by native_decide

/-- **The chromatic number of the dodecahedron is three.** -/
@[simp, toIsoGraph] theorem chromNum_dodecahedron : dodecahedron.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring dodecahedronCol dodecahedronCol_proper)
    (three_le_chromNum not_isBipartite_dodecahedron)

/-- A proper three-edge-colouring of the dodecahedron, as a symmetric table; the entries off the
edge set are `0`. -/
def dodecahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]

/-- The table `dodecahedronEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def dodecahedronEdgeCol (x y : dodecahedron.V) : Fin 3 :=
  ⟨min ((dodecahedronEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem dodecahedronEdgeCol_symm : ∀ x y : dodecahedron.V,
    dodecahedronEdgeCol x y = dodecahedronEdgeCol y x := by native_decide

theorem dodecahedronEdgeCol_proper : ∀ u v w : dodecahedron.V,
    dodecahedron.Adj u v = true → dodecahedron.Adj u w = true → v ≠ w →
      dodecahedronEdgeCol u v ≠ dodecahedronEdgeCol u w := by native_decide

/-- **The dodecahedron is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_dodecahedron : dodecahedron.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := dodecahedron)
      dodecahedronEdgeCol dodecahedronEdgeCol_symm
      dodecahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum dodecahedron
    rwa [maxDeg_dodecahedron] at h

/-! ## The truncated cube

Eight disjoint triangles joined by a perfect matching, so `α ≤ 8` and `ω = 3`. -/

@[simp] theorem maxDeg_truncatedCube : truncatedCube.maxDeg = 3 :=
  haveI : Nonempty truncatedCube.V := ⟨(0 : Fin 24)⟩
  (isRegularWith_truncatedCube).maxDeg_eq

/-- **The independence number of the truncated cube is eight.** -/
@[simp] theorem indepNum_truncatedCube : truncatedCube.indepNum = 8 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := truncatedCube)
    (l := ([2, 6, 10, 14, 16, 18, 21, 23] : List (Fin 24)))
    (by decide) (by native_decide)

/-- **The clique number of the truncated cube is three.** -/
@[simp] theorem cliqueNum_truncatedCube : truncatedCube.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := truncatedCube)
    (l := ([5, 6, 19] : List (Fin 24))) (by decide) (by native_decide)

/-- A proper three-colouring of the truncated cube. -/
def truncatedCubeColTable : List ℕ :=
  [0, 1, 0, 1, 1, 0, 1, 2, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 2, 2, 1, 2, 1]

/-- The table `truncatedCubeColTable` read as a colouring, clamped into `Fin 3`. -/
def truncatedCubeCol (v : truncatedCube.V) : Fin 3 :=
  ⟨min (truncatedCubeColTable.getD v.1 0) 2, by omega⟩

theorem truncatedCubeCol_proper : ∀ u v : truncatedCube.V,
    truncatedCube.Adj u v = true →
      truncatedCubeCol u ≠ truncatedCubeCol v := by native_decide

/-- **The chromatic number of the truncated cube is three.** -/
@[simp] theorem chromNum_truncatedCube : truncatedCube.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring truncatedCubeCol truncatedCubeCol_proper)
    (three_le_chromNum not_isBipartite_truncatedCube)

/-- A proper three-edge-colouring of the truncated cube, as a symmetric table; the entries off
the edge set are `0`. -/
def truncatedCubeEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]]

/-- The table `truncatedCubeEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def truncatedCubeEdgeCol (x y : truncatedCube.V) : Fin 3 :=
  ⟨min ((truncatedCubeEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem truncatedCubeEdgeCol_symm : ∀ x y : truncatedCube.V,
    truncatedCubeEdgeCol x y = truncatedCubeEdgeCol y x := by native_decide

theorem truncatedCubeEdgeCol_proper : ∀ u v w : truncatedCube.V,
    truncatedCube.Adj u v = true → truncatedCube.Adj u w = true → v ≠ w →
      truncatedCubeEdgeCol u v ≠ truncatedCubeEdgeCol u w := by native_decide

/-- **The truncated cube is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_truncatedCube : truncatedCube.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := truncatedCube)
      truncatedCubeEdgeCol truncatedCubeEdgeCol_symm
      truncatedCubeEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum truncatedCube
    rwa [maxDeg_truncatedCube] at h

/-! ## The truncated octahedron

The permutohedron of order four: cubic, bipartite, girth four, twenty-four vertices. -/

@[simp] theorem maxDeg_truncatedOctahedron : truncatedOctahedron.maxDeg = 3 :=
  haveI : Nonempty truncatedOctahedron.V := ⟨(0 : Fin 24)⟩
  (isRegularWith_truncatedOctahedron).maxDeg_eq

/-- **The independence number of the truncated octahedron is twelve.** -/
@[simp] theorem indepNum_truncatedOctahedron : truncatedOctahedron.indepNum = 12 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := truncatedOctahedron)
    (l := ([1, 3, 4, 7, 9, 10, 12, 14, 17, 18, 21, 23] : List (Fin 24)))
    (by decide) (by native_decide)

/-- **The truncated octahedron has no triangle**, having girth four, so its cliques are its
edges. -/
@[simp] theorem cliqueNum_truncatedOctahedron : truncatedOctahedron.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_truncatedOctahedron]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_truncatedOctahedron]; decide))

/-- **The truncated octahedron is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_truncatedOctahedron : truncatedOctahedron.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_truncatedOctahedron, by rw [E_truncatedOctahedron]; decide⟩

/-- A proper three-edge-colouring of the truncated octahedron, as a symmetric table; the entries
off the edge set are `0`. -/
def truncatedOctahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2],
   [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0]]

/-- The table `truncatedOctahedronEdgeColTable` read as an edge colouring, clamped into `Fin 3`. -/
def truncatedOctahedronEdgeCol (x y : truncatedOctahedron.V) : Fin 3 :=
  ⟨min ((truncatedOctahedronEdgeColTable.getD x.1 []).getD y.1 0) 2, by omega⟩

theorem truncatedOctahedronEdgeCol_symm : ∀ x y : truncatedOctahedron.V,
    truncatedOctahedronEdgeCol x y = truncatedOctahedronEdgeCol y x := by native_decide

theorem truncatedOctahedronEdgeCol_proper : ∀ u v w : truncatedOctahedron.V,
    truncatedOctahedron.Adj u v = true → truncatedOctahedron.Adj u w = true → v ≠ w →
      truncatedOctahedronEdgeCol u v ≠ truncatedOctahedronEdgeCol u w := by native_decide

/-- **The truncated octahedron is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_truncatedOctahedron : truncatedOctahedron.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := truncatedOctahedron)
      truncatedOctahedronEdgeCol truncatedOctahedronEdgeCol_symm
      truncatedOctahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum truncatedOctahedron
    rwa [maxDeg_truncatedOctahedron] at h

/-! ## The icosidodecahedron

The rectification of the dodecahedron: four-regular on thirty vertices, with triangular and
pentagonal faces. -/

@[simp] theorem maxDeg_icosidodecahedron : icosidodecahedron.maxDeg = 4 :=
  haveI : Nonempty icosidodecahedron.V := ⟨(0 : Fin 30)⟩
  (isRegularWith_icosidodecahedron).maxDeg_eq

/-- **The independence number of the icosidodecahedron is ten.** -/
@[simp] theorem indepNum_icosidodecahedron : icosidodecahedron.indepNum = 10 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := icosidodecahedron)
    (l := ([4, 7, 10, 13, 16, 20, 22, 24, 26, 28] : List (Fin 30)))
    (by decide) (by native_decide)

/-- **The clique number of the icosidodecahedron is three.** -/
@[simp] theorem cliqueNum_icosidodecahedron : icosidodecahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := icosidodecahedron)
    (l := ([25, 28, 29] : List (Fin 30))) (by decide) (by native_decide)

/-- A proper three-colouring of the icosidodecahedron. -/
def icosidodecahedronColTable : List ℕ :=
  [0, 1, 0, 1, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 2, 2, 1, 2, 0, 1]

/-- The table `icosidodecahedronColTable` read as a colouring, clamped into `Fin 3`. -/
def icosidodecahedronCol (v : icosidodecahedron.V) : Fin 3 :=
  ⟨min (icosidodecahedronColTable.getD v.1 0) 2, by omega⟩

theorem icosidodecahedronCol_proper : ∀ u v : icosidodecahedron.V,
    icosidodecahedron.Adj u v = true →
      icosidodecahedronCol u ≠ icosidodecahedronCol v := by native_decide

/-- **The chromatic number of the icosidodecahedron is three.** -/
@[simp] theorem chromNum_icosidodecahedron : icosidodecahedron.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring icosidodecahedronCol icosidodecahedronCol_proper)
    (three_le_chromNum not_isBipartite_icosidodecahedron)

/-- A proper four-edge-colouring of the icosidodecahedron, as a symmetric table; the entries off
the edge set are `0`. -/
def icosidodecahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0],
   [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [2, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0],
   [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0],
   [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 3],
   [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0]]

/-- The table `icosidodecahedronEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def icosidodecahedronEdgeCol (x y : icosidodecahedron.V) : Fin 4 :=
  ⟨min ((icosidodecahedronEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem icosidodecahedronEdgeCol_symm : ∀ x y : icosidodecahedron.V,
    icosidodecahedronEdgeCol x y = icosidodecahedronEdgeCol y x := by native_decide

theorem icosidodecahedronEdgeCol_proper : ∀ u v w : icosidodecahedron.V,
    icosidodecahedron.Adj u v = true → icosidodecahedron.Adj u w = true → v ≠ w →
      icosidodecahedronEdgeCol u v ≠ icosidodecahedronEdgeCol u w := by native_decide

/-- **The icosidodecahedron is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_icosidodecahedron : icosidodecahedron.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := icosidodecahedron)
      icosidodecahedronEdgeCol icosidodecahedronEdgeCol_symm
      icosidodecahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum icosidodecahedron
    rwa [maxDeg_icosidodecahedron] at h

/-! ## The triakis tetrahedron

The tetrahedron with a pyramid on each face — eight vertices, and the original `K₄` is still
there, so `ω = χ = 4`. -/

@[simp] theorem maxDeg_triakisTetrahedron : triakisTetrahedron.maxDeg = 6 := by
  native_decide

/-- **The independence number of the triakis tetrahedron is four.** -/
@[simp] theorem indepNum_triakisTetrahedron : triakisTetrahedron.indepNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := triakisTetrahedron)
    (l := ([4, 5, 6, 7] : List (Fin 8)))
    (by decide) (by native_decide)

/-- **The clique number of the triakis tetrahedron is four.** -/
@[simp] theorem cliqueNum_triakisTetrahedron : triakisTetrahedron.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := triakisTetrahedron)
    (l := ([0, 1, 2, 4] : List (Fin 8))) (by decide) (by native_decide)

/-- A proper four-colouring of the triakis tetrahedron. -/
def triakisTetrahedronColTable : List ℕ :=
  [0, 1, 2, 3, 3, 1, 2, 0]

/-- The table `triakisTetrahedronColTable` read as a colouring, clamped into `Fin 4`. -/
def triakisTetrahedronCol (v : triakisTetrahedron.V) : Fin 4 :=
  ⟨min (triakisTetrahedronColTable.getD v.1 0) 3, by omega⟩

theorem triakisTetrahedronCol_proper : ∀ u v : triakisTetrahedron.V,
    triakisTetrahedron.Adj u v = true →
      triakisTetrahedronCol u ≠ triakisTetrahedronCol v := by native_decide

/-- **The chromatic number of the triakis tetrahedron is four.** -/
@[simp] theorem chromNum_triakisTetrahedron : triakisTetrahedron.chromNum = 4 :=
  le_antisymm (chromNum_le_of_colouring triakisTetrahedronCol triakisTetrahedronCol_proper)
    (by have h := cliqueNum_le_chromNum triakisTetrahedron; rwa [cliqueNum_triakisTetrahedron] at h)

/-- A proper six-edge-colouring of the triakis tetrahedron, as a symmetric table; the entries off
the edge set are `0`. -/
def triakisTetrahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 2, 3, 4, 5, 0],
   [0, 0, 2, 4, 1, 0, 3, 5],
   [1, 2, 0, 3, 5, 0, 0, 4],
   [2, 4, 3, 0, 0, 5, 0, 1],
   [3, 1, 5, 0, 0, 0, 0, 0],
   [4, 0, 0, 5, 0, 0, 0, 0],
   [5, 3, 0, 0, 0, 0, 0, 0],
   [0, 5, 4, 1, 0, 0, 0, 0]]

/-- The table `triakisTetrahedronEdgeColTable` read as an edge colouring, clamped into `Fin 6`. -/
def triakisTetrahedronEdgeCol (x y : triakisTetrahedron.V) : Fin 6 :=
  ⟨min ((triakisTetrahedronEdgeColTable.getD x.1 []).getD y.1 0) 5, by omega⟩

theorem triakisTetrahedronEdgeCol_symm : ∀ x y : triakisTetrahedron.V,
    triakisTetrahedronEdgeCol x y = triakisTetrahedronEdgeCol y x := by native_decide

theorem triakisTetrahedronEdgeCol_proper : ∀ u v w : triakisTetrahedron.V,
    triakisTetrahedron.Adj u v = true → triakisTetrahedron.Adj u w = true → v ≠ w →
      triakisTetrahedronEdgeCol u v ≠ triakisTetrahedronEdgeCol u w := by native_decide

/-- **The triakis tetrahedron is class one**: `χ' = Δ = 6`. -/
@[simp] theorem edgeChromNum_triakisTetrahedron : triakisTetrahedron.edgeChromNum = 6 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := triakisTetrahedron)
      triakisTetrahedronEdgeCol triakisTetrahedronEdgeCol_symm
      triakisTetrahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum triakisTetrahedron
    rwa [maxDeg_triakisTetrahedron] at h

/-! ## The rhombic dodecahedron

The Catalan solid dual to the cuboctahedron: bipartite on fourteen vertices, six of degree four
and eight of degree three, and the eight are the maximum independent set. -/

@[simp] theorem maxDeg_rhombicDodecahedron : rhombicDodecahedron.maxDeg = 4 := by
  native_decide

/-- **The independence number of the rhombic dodecahedron is eight.** -/
@[simp] theorem indepNum_rhombicDodecahedron : rhombicDodecahedron.indepNum = 8 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := rhombicDodecahedron)
    (l := ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 14)))
    (by decide) (by native_decide)

/-- **The rhombic dodecahedron has no triangle**, having girth four, so its cliques are its
edges. -/
@[simp] theorem cliqueNum_rhombicDodecahedron : rhombicDodecahedron.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_rhombicDodecahedron]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_rhombicDodecahedron]; decide))

/-- **The rhombic dodecahedron is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_rhombicDodecahedron : rhombicDodecahedron.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_rhombicDodecahedron, by rw [E_rhombicDodecahedron]; decide⟩

/-- A proper four-edge-colouring of the rhombic dodecahedron, as a symmetric table; the entries
off the edge set are `0`. -/
def rhombicDodecahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3],
   [0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 3, 0, 2, 1, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0],
   [2, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0]]

/-- The table `rhombicDodecahedronEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def rhombicDodecahedronEdgeCol (x y : rhombicDodecahedron.V) : Fin 4 :=
  ⟨min ((rhombicDodecahedronEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem rhombicDodecahedronEdgeCol_symm : ∀ x y : rhombicDodecahedron.V,
    rhombicDodecahedronEdgeCol x y = rhombicDodecahedronEdgeCol y x := by native_decide

theorem rhombicDodecahedronEdgeCol_proper : ∀ u v w : rhombicDodecahedron.V,
    rhombicDodecahedron.Adj u v = true → rhombicDodecahedron.Adj u w = true → v ≠ w →
      rhombicDodecahedronEdgeCol u v ≠ rhombicDodecahedronEdgeCol u w := by native_decide

/-- **The rhombic dodecahedron is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_rhombicDodecahedron : rhombicDodecahedron.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := rhombicDodecahedron)
      rhombicDodecahedronEdgeCol rhombicDodecahedronEdgeCol_symm
      rhombicDodecahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum rhombicDodecahedron
    rwa [maxDeg_rhombicDodecahedron] at h

/-! ## The triakis octahedron

The octahedron with a pyramid raised on each face: the six octahedron vertices keep degree
eight, and the four-cliques they sit in force `χ = 4`. -/

@[simp] theorem maxDeg_triakisOctahedron : triakisOctahedron.maxDeg = 8 := by
  native_decide

/-- **The independence number of the triakis octahedron is eight.** -/
@[simp] theorem indepNum_triakisOctahedron : triakisOctahedron.indepNum = 8 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := triakisOctahedron)
    (l := ([6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)))
    (by decide) (by native_decide)

/-- **The clique number of the triakis octahedron is four.** -/
@[simp] theorem cliqueNum_triakisOctahedron : triakisOctahedron.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := triakisOctahedron)
    (l := ([0, 4, 5, 13] : List (Fin 14))) (by decide) (by native_decide)

/-- A proper four-colouring of the triakis octahedron. -/
def triakisOctahedronColTable : List ℕ :=
  [0, 1, 2, 0, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3]

/-- The table `triakisOctahedronColTable` read as a colouring, clamped into `Fin 4`. -/
def triakisOctahedronCol (v : triakisOctahedron.V) : Fin 4 :=
  ⟨min (triakisOctahedronColTable.getD v.1 0) 3, by omega⟩

theorem triakisOctahedronCol_proper : ∀ u v : triakisOctahedron.V,
    triakisOctahedron.Adj u v = true →
      triakisOctahedronCol u ≠ triakisOctahedronCol v := by native_decide

/-- **The chromatic number of the triakis octahedron is four.** -/
@[simp] theorem chromNum_triakisOctahedron : triakisOctahedron.chromNum = 4 :=
  le_antisymm (chromNum_le_of_colouring triakisOctahedronCol triakisOctahedronCol_proper)
    (by have h := cliqueNum_le_chromNum triakisOctahedron; rwa [cliqueNum_triakisOctahedron] at h)

/-- A proper eight-edge-colouring of the triakis octahedron, as a symmetric table; the entries
off the edge set are `0`. -/
def triakisOctahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 0, 2, 3, 4, 0, 0, 5, 6, 0, 0, 7],
   [0, 0, 2, 5, 0, 1, 3, 6, 0, 0, 4, 7, 0, 0],
   [1, 2, 0, 3, 5, 0, 0, 4, 7, 6, 0, 0, 0, 0],
   [0, 5, 3, 0, 1, 4, 0, 7, 2, 0, 0, 6, 0, 0],
   [2, 0, 5, 1, 0, 0, 0, 0, 4, 7, 0, 0, 6, 3],
   [3, 1, 0, 4, 0, 0, 0, 0, 0, 0, 2, 5, 7, 6],
   [4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 6, 4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 7, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [5, 0, 6, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [6, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 7, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0],
   [7, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `triakisOctahedronEdgeColTable` read as an edge colouring, clamped into `Fin 8`. -/
def triakisOctahedronEdgeCol (x y : triakisOctahedron.V) : Fin 8 :=
  ⟨min ((triakisOctahedronEdgeColTable.getD x.1 []).getD y.1 0) 7, by omega⟩

theorem triakisOctahedronEdgeCol_symm : ∀ x y : triakisOctahedron.V,
    triakisOctahedronEdgeCol x y = triakisOctahedronEdgeCol y x := by native_decide

theorem triakisOctahedronEdgeCol_proper : ∀ u v w : triakisOctahedron.V,
    triakisOctahedron.Adj u v = true → triakisOctahedron.Adj u w = true → v ≠ w →
      triakisOctahedronEdgeCol u v ≠ triakisOctahedronEdgeCol u w := by native_decide

/-- **The triakis octahedron is class one**: `χ' = Δ = 8`. -/
@[simp] theorem edgeChromNum_triakisOctahedron : triakisOctahedron.edgeChromNum = 8 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := triakisOctahedron)
      triakisOctahedronEdgeCol triakisOctahedronEdgeCol_symm
      triakisOctahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum triakisOctahedron
    rwa [maxDeg_triakisOctahedron] at h

/-! ## The tetrakis hexahedron

The cube with a pyramid on each face.  Its triangles give `ω = 3`, which the colouring meets. -/

@[simp] theorem maxDeg_tetrakisHexahedron : tetrakisHexahedron.maxDeg = 6 := by
  native_decide

/-- **The independence number of the tetrakis hexahedron is six.** -/
@[simp] theorem indepNum_tetrakisHexahedron : tetrakisHexahedron.indepNum = 6 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := tetrakisHexahedron)
    (l := ([8, 9, 10, 11, 12, 13] : List (Fin 14)))
    (by decide) (by native_decide)

/-- **The clique number of the tetrakis hexahedron is three.** -/
@[simp] theorem cliqueNum_tetrakisHexahedron : tetrakisHexahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := tetrakisHexahedron)
    (l := ([5, 7, 13] : List (Fin 14))) (by decide) (by native_decide)

/-- A proper three-colouring of the tetrakis hexahedron. -/
def tetrakisHexahedronColTable : List ℕ :=
  [0, 1, 1, 0, 1, 0, 0, 1, 2, 2, 2, 2, 2, 2]

/-- The table `tetrakisHexahedronColTable` read as a colouring, clamped into `Fin 3`. -/
def tetrakisHexahedronCol (v : tetrakisHexahedron.V) : Fin 3 :=
  ⟨min (tetrakisHexahedronColTable.getD v.1 0) 2, by omega⟩

theorem tetrakisHexahedronCol_proper : ∀ u v : tetrakisHexahedron.V,
    tetrakisHexahedron.Adj u v = true →
      tetrakisHexahedronCol u ≠ tetrakisHexahedronCol v := by native_decide

/-- **The chromatic number of the tetrakis hexahedron is three.** -/
@[simp] theorem chromNum_tetrakisHexahedron : tetrakisHexahedron.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring tetrakisHexahedronCol tetrakisHexahedronCol_proper)
    (three_le_chromNum not_isBipartite_tetrakisHexahedron)

/-- A proper six-edge-colouring of the tetrakis hexahedron, as a symmetric table; the entries off
the edge set are `0`. -/
def tetrakisHexahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 4, 0, 5, 0],
   [0, 0, 0, 3, 0, 4, 0, 0, 1, 0, 2, 0, 0, 5],
   [1, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 5, 3, 0],
   [0, 3, 0, 0, 0, 0, 0, 5, 4, 0, 0, 1, 0, 2],
   [2, 0, 0, 0, 0, 5, 3, 0, 0, 4, 1, 0, 0, 0],
   [0, 4, 0, 0, 5, 0, 0, 2, 0, 3, 0, 0, 0, 1],
   [0, 0, 4, 0, 3, 0, 0, 0, 0, 5, 0, 2, 1, 0],
   [0, 0, 0, 5, 0, 2, 0, 0, 0, 1, 0, 3, 0, 4],
   [3, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 4, 3, 5, 1, 0, 0, 0, 0, 0, 0],
   [4, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 5, 1, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0],
   [5, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 5, 0, 2, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0]]

/-- The table `tetrakisHexahedronEdgeColTable` read as an edge colouring, clamped into `Fin 6`. -/
def tetrakisHexahedronEdgeCol (x y : tetrakisHexahedron.V) : Fin 6 :=
  ⟨min ((tetrakisHexahedronEdgeColTable.getD x.1 []).getD y.1 0) 5, by omega⟩

theorem tetrakisHexahedronEdgeCol_symm : ∀ x y : tetrakisHexahedron.V,
    tetrakisHexahedronEdgeCol x y = tetrakisHexahedronEdgeCol y x := by native_decide

theorem tetrakisHexahedronEdgeCol_proper : ∀ u v w : tetrakisHexahedron.V,
    tetrakisHexahedron.Adj u v = true → tetrakisHexahedron.Adj u w = true → v ≠ w →
      tetrakisHexahedronEdgeCol u v ≠ tetrakisHexahedronEdgeCol u w := by native_decide

/-- **The tetrakis hexahedron is class one**: `χ' = Δ = 6`. -/
@[simp] theorem edgeChromNum_tetrakisHexahedron : tetrakisHexahedron.edgeChromNum = 6 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tetrakisHexahedron)
      tetrakisHexahedronEdgeCol tetrakisHexahedronEdgeCol_symm
      tetrakisHexahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum tetrakisHexahedron
    rwa [maxDeg_tetrakisHexahedron] at h

/-! ## The pentakis dodecahedron

The dodecahedron with a pyramid on each face: twelve vertices of degree five and twenty of
degree six.  Four colours are needed even though the largest clique is a triangle. -/

@[simp] theorem maxDeg_pentakisDodecahedron : pentakisDodecahedron.maxDeg = 6 := by
  native_decide

/-- **The independence number of the pentakis dodecahedron is twelve.** -/
@[simp] theorem indepNum_pentakisDodecahedron : pentakisDodecahedron.indepNum = 12 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := pentakisDodecahedron)
    (l := ([20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] : List (Fin 32)))
    (by decide) (by native_decide)

/-- **The clique number of the pentakis dodecahedron is three.** -/
@[simp] theorem cliqueNum_pentakisDodecahedron : pentakisDodecahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := pentakisDodecahedron)
    (l := ([18, 19, 29] : List (Fin 32))) (by decide) (by native_decide)

/-- A proper four-colouring of the pentakis dodecahedron. -/
def pentakisDodecahedronColTable : List ℕ :=
  [0, 1, 0, 1, 3, 1, 0, 3, 0, 1, 2, 0, 3, 0, 3, 3, 2, 0, 2, 0, 2, 2, 2, 3, 2, 2, 1, 3, 1, 1, 2, 1]

/-- The table `pentakisDodecahedronColTable` read as a colouring, clamped into `Fin 4`. -/
def pentakisDodecahedronCol (v : pentakisDodecahedron.V) : Fin 4 :=
  ⟨min (pentakisDodecahedronColTable.getD v.1 0) 3, by omega⟩

theorem pentakisDodecahedronCol_proper : ∀ u v : pentakisDodecahedron.V,
    pentakisDodecahedron.Adj u v = true →
      pentakisDodecahedronCol u ≠ pentakisDodecahedronCol v := by native_decide

/-- **The pentakis dodecahedron needs four colours**, by a SAT refutation of the three-colour
system. -/
theorem four_le_chromNum_pentakisDodecahedron : 4 ≤ pentakisDodecahedron.chromNum := by
  show 3 < pentakisDodecahedron.chromNum
  graph_sat native

/-- **The chromatic number of the pentakis dodecahedron is four.** -/
@[simp] theorem chromNum_pentakisDodecahedron : pentakisDodecahedron.chromNum = 4 :=
  le_antisymm (chromNum_le_of_colouring pentakisDodecahedronCol pentakisDodecahedronCol_proper)
    (four_le_chromNum_pentakisDodecahedron)

/-- A proper six-edge-colouring of the pentakis dodecahedron, as a symmetric table; the entries
off the edge set are `0`. -/
def pentakisDodecahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0],
   [0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 3, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0],
   [0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0],
   [0, 4, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0],
   [0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 5, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 5, 0, 0, 0],
   [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 4, 0, 0],
   [0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 1, 0],
   [0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 4],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 3],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5],
   [3, 1, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [4, 2, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 5, 1, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 5, 1, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [5, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 5, 4, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `pentakisDodecahedronEdgeColTable` read as an edge colouring, clamped into `Fin 6`. -/
def pentakisDodecahedronEdgeCol (x y : pentakisDodecahedron.V) : Fin 6 :=
  ⟨min ((pentakisDodecahedronEdgeColTable.getD x.1 []).getD y.1 0) 5, by omega⟩

theorem pentakisDodecahedronEdgeCol_symm : ∀ x y : pentakisDodecahedron.V,
    pentakisDodecahedronEdgeCol x y = pentakisDodecahedronEdgeCol y x := by native_decide

theorem pentakisDodecahedronEdgeCol_proper : ∀ u v w : pentakisDodecahedron.V,
    pentakisDodecahedron.Adj u v = true → pentakisDodecahedron.Adj u w = true → v ≠ w →
      pentakisDodecahedronEdgeCol u v ≠ pentakisDodecahedronEdgeCol u w := by native_decide

/-- **The pentakis dodecahedron is class one**: `χ' = Δ = 6`. -/
@[simp] theorem edgeChromNum_pentakisDodecahedron : pentakisDodecahedron.edgeChromNum = 6 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := pentakisDodecahedron)
      pentakisDodecahedronEdgeCol pentakisDodecahedronEdgeCol_symm
      pentakisDodecahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum pentakisDodecahedron
    rwa [maxDeg_pentakisDodecahedron] at h

/-! ## The rhombic triacontahedron

The Catalan solid dual to the icosidodecahedron: bipartite, twelve vertices of degree five and
twenty of degree three, and the twenty are the maximum independent set. -/

@[simp] theorem maxDeg_rhombicTriacontahedron : rhombicTriacontahedron.maxDeg = 5 := by
  native_decide

/-- **The independence number of the rhombic triacontahedron is twenty.** -/
@[simp] theorem indepNum_rhombicTriacontahedron : rhombicTriacontahedron.indepNum = 20 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := rhombicTriacontahedron)
    (l := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] : List (Fin 32)))
    (by decide) (by native_decide)

/-- **The rhombic triacontahedron has no triangle**, having girth four, so its cliques are its
edges. -/
@[simp] theorem cliqueNum_rhombicTriacontahedron : rhombicTriacontahedron.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_rhombicTriacontahedron]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_rhombicTriacontahedron]; decide))

/-- **The rhombic triacontahedron is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_rhombicTriacontahedron : rhombicTriacontahedron.chromNum = 2 :=
  chromNum_eq_two_iff.2
    ⟨isBipartite_rhombicTriacontahedron, by rw [E_rhombicTriacontahedron]; decide⟩

/-- A proper five-edge-colouring of the rhombic triacontahedron, as a symmetric table; the
entries off the edge set are `0`. -/
def rhombicTriacontahedronEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 4, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 3, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 4],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 3],
   [0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 3, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 1, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `rhombicTriacontahedronEdgeColTable` read as an edge colouring, clamped into `Fin
5`. -/
def rhombicTriacontahedronEdgeCol (x y : rhombicTriacontahedron.V) : Fin 5 :=
  ⟨min ((rhombicTriacontahedronEdgeColTable.getD x.1 []).getD y.1 0) 4, by omega⟩

theorem rhombicTriacontahedronEdgeCol_symm : ∀ x y : rhombicTriacontahedron.V,
    rhombicTriacontahedronEdgeCol x y = rhombicTriacontahedronEdgeCol y x := by native_decide

theorem rhombicTriacontahedronEdgeCol_proper : ∀ u v w : rhombicTriacontahedron.V,
    rhombicTriacontahedron.Adj u v = true → rhombicTriacontahedron.Adj u w = true → v ≠ w →
      rhombicTriacontahedronEdgeCol u v ≠ rhombicTriacontahedronEdgeCol u w := by native_decide

/-- **The rhombic triacontahedron is class one**: `χ' = Δ = 5`. -/
@[simp] theorem edgeChromNum_rhombicTriacontahedron : rhombicTriacontahedron.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := rhombicTriacontahedron)
      rhombicTriacontahedronEdgeCol rhombicTriacontahedronEdgeCol_symm
      rhombicTriacontahedronEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum rhombicTriacontahedron
    rwa [maxDeg_rhombicTriacontahedron] at h

end NamedGraphs
