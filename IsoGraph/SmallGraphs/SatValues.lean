import IsoGraph.SmallGraphs.Operators

/-!
# The gallery's co-NP invariants, by SAT

Three graphs of the gallery whose independence, clique, chromatic and edge chromatic numbers were
all out of reach before `graph_sat`: the Chvátal graph, Tietze's graph and the Robertson graph.
Each of the four values needs a bound in both directions, and the two directions are proved by
opposite means:

* the refutation — `α ≤ n`, `ω ≤ n`, `k < χ`, `k < χ'` — goes to `graph_sat native`, which hands
  the formula to a SAT solver;
* the witness — an independent set, a clique, a colouring, an edge colouring — is a table found by
  machine and checked here, through `le_indepNum_of_nodup`, `le_cliqueNum_of_nodup`,
  `chromNum_le_of_colouring` and `edgeChromNum_mk_le_of_colouring`.

Two of the three are class two, which is what makes them worth the trouble: Tietze's graph is the
Petersen graph with a vertex blown up into a triangle, and the Robertson graph is the `(4, 5)`-cage
with `χ' = 5 = Δ + 1`.  The third snark of the library, `edgeChromNum_flowerSnark`, is proved the
same way in `SmallGraphs.EdgeColourings`, next to the colouring tables it belongs with.
-/

namespace NamedGraphs

open CGraph

/-! ## The Chvátal graph

The smallest triangle-free four-regular graph of chromatic number four, so `α`, `ω` and `χ` are all
part of what it is named for; and it is class one, `χ' = Δ = 4`. -/

/-- A proper `4`-colouring of the Chvátal graph, one colour per vertex. -/
def chvatalColTable : List ℕ := [0, 1, 0, 1, 2, 0, 1, 0, 1, 2, 3, 3]

/-- The table `chvatalColTable` read as a colouring, clamped into `Fin 4`. -/
def chvatalCol (v : chvatal.V) : Fin 4 := ⟨min (chvatalColTable.getD v.1 0) 3, by omega⟩

theorem chvatalCol_proper : ∀ u v : chvatal.V, chvatal.Adj u v = true →
    chvatalCol u ≠ chvatalCol v := by native_decide

/-- **The Chvátal graph needs four colours**, by a SAT refutation of the three-colour system. -/
theorem four_le_chromNum_chvatal : 4 ≤ chvatal.chromNum := by
  show 3 < chvatal.chromNum
  graph_sat native

/-- **The chromatic number of the Chvátal graph is four**, the property it was built for: it is
triangle-free and four-regular, and Brooks' bound `χ ≤ Δ` is met. -/
@[simp] theorem chromNum_chvatal : chvatal.chromNum = 4 :=
  le_antisymm (chromNum_le_of_colouring chvatalCol chvatalCol_proper) four_le_chromNum_chvatal

/-- **The independence number of the Chvátal graph is four.** -/
@[simp] theorem indepNum_chvatal : chvatal.indepNum = 4 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := chvatal) (l := ([0, 2, 5, 7] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **The Chvátal graph is triangle-free**: its cliques are its edges. -/
@[simp] theorem cliqueNum_chvatal : chvatal.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := chvatal) (l := ([0, 1] : List (Fin 12)))
    (by decide) (by native_decide)

/-- A proper `4`-edge-colouring of the Chvátal graph, as a symmetric table; the entries off the
edge set are `0`. -/
def chvatalEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0, 0],
   [0, 0, 1, 0, 0, 2, 0, 3, 0, 0, 0, 0],
   [0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0],
   [0, 0, 2, 0, 3, 0, 0, 0, 0, 1, 0, 0],
   [1, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1],
   [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2],
   [0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0],
   [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 1, 3, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 3, 1, 2, 0, 0, 0, 0]]

/-- The table `chvatalEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def chvatalEdgeCol (x y : chvatal.V) : Fin 4 :=
  ⟨min ((chvatalEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem chvatalEdgeCol_symm : ∀ x y : chvatal.V, chvatalEdgeCol x y = chvatalEdgeCol y x := by
  native_decide

theorem chvatalEdgeCol_proper : ∀ u v w : chvatal.V, chvatal.Adj u v = true →
    chvatal.Adj u w = true → v ≠ w → chvatalEdgeCol u v ≠ chvatalEdgeCol u w := by native_decide

theorem four_le_edgeChromNum_chvatal : 4 ≤ chvatal.edgeChromNum := by
  show 3 < chvatal.edgeChromNum
  graph_sat native

/-- **The Chvátal graph is class one**: `χ' = Δ = 4`. -/
@[simp] theorem edgeChromNum_chvatal : chvatal.edgeChromNum = 4 := by
  refine le_antisymm ?_ four_le_edgeChromNum_chvatal
  rw [← IsoGraph.edgeChromNum_mk]
  exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := chvatal)
    chvatalEdgeCol chvatalEdgeCol_symm chvatalEdgeCol_proper

/-! ## Tietze's graph

The Petersen graph with one vertex blown up into a triangle: cubic on twelve vertices, three
colours at the vertices and — like the Petersen graph it comes from — four at the edges. -/

/-- A proper `3`-colouring of Tietze's graph. -/
def tietzeColTable : List ℕ := [0, 1, 1, 1, 0, 0, 2, 2, 0, 2, 1, 1]

/-- The table `tietzeColTable` read as a colouring, clamped into `Fin 3`. -/
def tietzeCol (v : tietze.V) : Fin 3 := ⟨min (tietzeColTable.getD v.1 0) 2, by omega⟩

theorem tietzeCol_proper : ∀ u v : tietze.V, tietze.Adj u v = true →
    tietzeCol u ≠ tietzeCol v := by native_decide

theorem three_le_chromNum_tietze : 3 ≤ tietze.chromNum := by
  show 2 < tietze.chromNum
  graph_sat native

/-- **The chromatic number of Tietze's graph is three.** -/
@[simp] theorem chromNum_tietze : tietze.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring tietzeCol tietzeCol_proper) three_le_chromNum_tietze

/-- **The independence number of Tietze's graph is five**, as for the Petersen graph: blowing a
vertex up into a triangle costs nothing, since only one of the three can be used. -/
@[simp] theorem indepNum_tietze : tietze.indepNum = 5 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := tietze) (l := ([0, 4, 7, 8, 11] : List (Fin 12)))
    (by decide) (by native_decide)

/-- **Tietze's graph has a triangle**, the one the construction puts in, and nothing larger. -/
@[simp] theorem cliqueNum_tietze : tietze.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := tietze) (l := ([3, 8, 9] : List (Fin 12)))
    (by decide) (by native_decide)

/-- A proper `4`-edge-colouring of Tietze's graph, as a symmetric table. -/
def tietzeEdgeColTable : List (List ℕ) :=
  [[0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0]]

/-- The table `tietzeEdgeColTable` read as an edge colouring, clamped into `Fin 4`. -/
def tietzeEdgeCol (x y : tietze.V) : Fin 4 :=
  ⟨min ((tietzeEdgeColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem tietzeEdgeCol_symm : ∀ x y : tietze.V, tietzeEdgeCol x y = tietzeEdgeCol y x := by
  native_decide

theorem tietzeEdgeCol_proper : ∀ u v w : tietze.V, tietze.Adj u v = true →
    tietze.Adj u w = true → v ≠ w → tietzeEdgeCol u v ≠ tietzeEdgeCol u w := by native_decide

/-- **Tietze's graph is class two**: three colours do not suffice for its eighteen edges. -/
theorem four_le_edgeChromNum_tietze : 4 ≤ tietze.edgeChromNum := by
  show 3 < tietze.edgeChromNum
  graph_sat native

/-- **The chromatic index of Tietze's graph is four.** -/
@[simp] theorem edgeChromNum_tietze : tietze.edgeChromNum = 4 := by
  refine le_antisymm ?_ four_le_edgeChromNum_tietze
  rw [← IsoGraph.edgeChromNum_mk]
  exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tietze)
    tietzeEdgeCol tietzeEdgeCol_symm tietzeEdgeCol_proper

/-! ## The Robertson graph

The `(4, 5)`-cage: four-regular, girth five, nineteen vertices — an odd order, which already forces
`χ' > Δ`.  Here the value `5` comes out of the solver directly, on the thirty-eight vertices of the
line graph. -/

/-- A proper `3`-colouring of the Robertson graph. -/
def robertsonColTable : List ℕ := [0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2]

/-- The table `robertsonColTable` read as a colouring, clamped into `Fin 3`. -/
def robertsonCol (v : robertson.V) : Fin 3 := ⟨min (robertsonColTable.getD v.1 0) 2, by omega⟩

theorem robertsonCol_proper : ∀ u v : robertson.V, robertson.Adj u v = true →
    robertsonCol u ≠ robertsonCol v := by native_decide

theorem three_le_chromNum_robertson : 3 ≤ robertson.chromNum := by
  show 2 < robertson.chromNum
  graph_sat native

/-- **The chromatic number of the Robertson graph is three.** -/
@[simp] theorem chromNum_robertson : robertson.chromNum = 3 :=
  le_antisymm (chromNum_le_of_colouring robertsonCol robertsonCol_proper)
    three_le_chromNum_robertson

/-- **The independence number of the Robertson graph is seven.** -/
@[simp] theorem indepNum_robertson : robertson.indepNum = 7 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := robertson) (l := ([1, 3, 5, 7, 9, 15, 17] : List (Fin 19)))
    (by decide) (by native_decide)

/-- **The Robertson graph is triangle-free**, as any graph of girth five is. -/
@[simp] theorem cliqueNum_robertson : robertson.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_cliqueNum_of_nodup (G := robertson) (l := ([0, 1] : List (Fin 19)))
    (by decide) (by native_decide)

/-- A proper `5`-edge-colouring of the Robertson graph, as a symmetric table. -/
def robertsonEdgeColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3],
   [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0],
   [1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0],
   [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4],
   [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0],
   [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2],
   [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 4, 0],
   [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
   [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1],
   [3, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0]]

/-- The table `robertsonEdgeColTable` read as an edge colouring, clamped into `Fin 5`. -/
def robertsonEdgeCol (x y : robertson.V) : Fin 5 :=
  ⟨min ((robertsonEdgeColTable.getD x.1 []).getD y.1 0) 4, by omega⟩

theorem robertsonEdgeCol_symm : ∀ x y : robertson.V,
    robertsonEdgeCol x y = robertsonEdgeCol y x := by native_decide

theorem robertsonEdgeCol_proper : ∀ u v w : robertson.V, robertson.Adj u v = true →
    robertson.Adj u w = true → v ≠ w → robertsonEdgeCol u v ≠ robertsonEdgeCol u w := by
  native_decide

/-- **The Robertson graph is class two**: four colours do not suffice for its thirty-eight edges,
by a SAT refutation over the line graph. -/
theorem five_le_edgeChromNum_robertson : 5 ≤ robertson.edgeChromNum := by
  show 4 < robertson.edgeChromNum
  graph_sat native

/-- **The chromatic index of the Robertson graph is five.** -/
@[simp] theorem edgeChromNum_robertson : robertson.edgeChromNum = 5 := by
  refine le_antisymm ?_ five_le_edgeChromNum_robertson
  rw [← IsoGraph.edgeChromNum_mk]
  exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := robertson)
    robertsonEdgeCol robertsonEdgeCol_symm robertsonEdgeCol_proper

end NamedGraphs
