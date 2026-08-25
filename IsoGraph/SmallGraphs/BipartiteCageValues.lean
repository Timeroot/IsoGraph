import IsoGraph.SmallGraphs.Operators

/-!
# The large bipartite cages: the four co-NP invariants

The three `(3, 10)`-cages, the Foster graph, the Ljubljana graph and the Tutte 12-cage.  All six
are cubic and bipartite, which fixes three of the four values without a search: no triangle, so
`ω = 2`; two colour classes, so `χ = 2`; and a decomposition into three perfect matchings, so
`χ' = Δ = 3`.

What is not free is the independence number.  A cubic bipartite graph has a perfect matching, so
`α = |V| / 2`, but that is König's theorem and the library does not have it; instead each side of
the bipartition is written out as a witness and `graph_sat native` refutes one more.  The Tutte
12-cage's `α ≤ 63` on a hundred and twenty-six vertices is the largest refutation in the library.

The edge colourings are keyed by the sorted pair of endpoints rather than laid out as an `n × n`
table, which keeps them to one entry per edge and makes the symmetry a rewrite instead of a
check.
-/

namespace NamedGraphs

open CGraph

-- Building the CNF for a graph of this size recurses deeply.  The heartbeat budget, by contrast,
-- is needed by exactly one theorem in the file — see `indepNum_tutte12Cage` below — because the
-- refutations run as compiled code and cost almost nothing in heartbeats.
set_option maxRecDepth 100000

/-! ## The Harries graph

One of the three cubic graphs of girth ten on seventy vertices — the `(3, 10)`-cages — and the
one that is not vertex-transitive. -/

@[simp] theorem maxDeg_harries : harries.maxDeg = 3 :=
  haveI : Nonempty harries.V := ⟨(0 : Fin 70)⟩
  (isRegularWith_harries).maxDeg_eq

/-- One side of the bipartition of the Harries graph: thirty-five vertices, no two adjacent. -/
def harriesIndepSet : List (Fin 70) :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
   50, 52, 54, 56, 58, 60, 62, 64, 66, 68]

/-- **The independence number of the Harries graph is thirty-five.**  A cubic bipartite graph has
a perfect matching, so neither side of the bipartition can be beaten. -/
@[simp] theorem indepNum_harries : harries.indepNum = 35 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := harries) (l := harriesIndepSet)
    (by native_decide) (by native_decide)

/-- **The Harries graph has no triangle**, having girth ten, so its cliques are its edges. -/
@[simp] theorem cliqueNum_harries : harries.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_harries]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_harries]; decide))

/-- **The Harries graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_harries : harries.chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_harries, by rw [E_harries]; decide⟩

/-- A proper three-edge-colouring of the Harries graph, keyed by the ordered pair of endpoints:
three perfect matchings, one per colour. -/
def harriesEdgeColList : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 1), ((0, 41), 2), ((0, 69), 0), ((1, 2), 0), ((1, 52), 2), ((2, 3), 1), ((2, 59), 2),
   ((3, 4), 2), ((3, 16), 0), ((4, 5), 0), ((4, 25), 1), ((5, 6), 2), ((5, 48), 1), ((6, 7), 1),
   ((6, 33), 0), ((7, 8), 0), ((7, 40), 2), ((8, 9), 1), ((8, 65), 2), ((9, 10), 2), ((9, 22), 0),
   ((10, 11), 0), ((10, 29), 1), ((11, 12), 2), ((11, 60), 1), ((12, 13), 0), ((12, 49), 1),
   ((13, 14), 2), ((13, 42), 1), ((14, 15), 0), ((14, 55), 1), ((15, 16), 2), ((15, 66), 1),
   ((16, 17), 1), ((17, 18), 2), ((17, 30), 0), ((18, 19), 0), ((18, 39), 1), ((19, 20), 1),
   ((19, 62), 2), ((20, 21), 0), ((20, 47), 2), ((21, 22), 2), ((21, 54), 1), ((22, 23), 1),
   ((23, 24), 2), ((23, 36), 0), ((24, 25), 0), ((24, 43), 1), ((25, 26), 2), ((26, 27), 0),
   ((26, 63), 1), ((27, 28), 2), ((27, 56), 1), ((28, 29), 0), ((28, 69), 1), ((29, 30), 2),
   ((30, 31), 1), ((31, 32), 0), ((31, 44), 2), ((32, 33), 2), ((32, 53), 1), ((33, 34), 1),
   ((34, 35), 2), ((34, 61), 0), ((35, 36), 1), ((35, 68), 0), ((36, 37), 2), ((37, 38), 0),
   ((37, 50), 1), ((38, 39), 2), ((38, 57), 1), ((39, 40), 0), ((40, 41), 1), ((41, 42), 0),
   ((42, 43), 2), ((43, 44), 0), ((44, 45), 1), ((45, 46), 2), ((45, 58), 0), ((46, 47), 1),
   ((46, 67), 0), ((47, 48), 0), ((48, 49), 2), ((49, 50), 0), ((50, 51), 2), ((51, 52), 1),
   ((51, 64), 0), ((52, 53), 0), ((53, 54), 2), ((54, 55), 0), ((55, 56), 2), ((56, 57), 0),
   ((57, 58), 2), ((58, 59), 1), ((59, 60), 0), ((60, 61), 2), ((61, 62), 1), ((62, 63), 0),
   ((63, 64), 2), ((64, 65), 1), ((65, 66), 0), ((66, 67), 2), ((67, 68), 1), ((68, 69), 2)]

/-- The list `harriesEdgeColList` read as an edge colouring.  The key is sorted, so the colouring
is symmetric before anything is proved; edges off the list get colour `0`. -/
def harriesEdgeCol (x y : harries.V) : Fin 3 :=
  ⟨min ((harriesEdgeColList.lookup (min x.1 y.1, max x.1 y.1)).getD 0) 2, by omega⟩

theorem harriesEdgeCol_symm : ∀ x y : harries.V,
    harriesEdgeCol x y = harriesEdgeCol y x := by
  intro x y
  simp only [harriesEdgeCol, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]

theorem harriesEdgeCol_proper : ∀ u v w : harries.V,
    harries.Adj u v = true → harries.Adj u w = true → v ≠ w →
      harriesEdgeCol u v ≠ harriesEdgeCol u w := by native_decide

/-- **The Harries graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_harries : harries.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := harries)
      harriesEdgeCol harriesEdgeCol_symm harriesEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum harries
    rwa [maxDeg_harries] at h

/-! ## The Harries–Wong graph

The second `(3, 10)`-cage, distinguished from the Harries graph by its automorphism group. -/

@[simp] theorem maxDeg_harriesWong : harriesWong.maxDeg = 3 :=
  haveI : Nonempty harriesWong.V := ⟨(0 : Fin 70)⟩
  (isRegularWith_harriesWong).maxDeg_eq

/-- One side of the bipartition of the Harries–Wong graph: thirty-five vertices, no two adjacent. -/
def harriesWongIndepSet : List (Fin 70) :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
   50, 52, 54, 56, 58, 60, 62, 64, 66, 68]

/-- **The independence number of the Harries–Wong graph is thirty-five.**  A cubic bipartite
graph has a perfect matching, so neither side of the bipartition can be beaten. -/
@[simp] theorem indepNum_harriesWong : harriesWong.indepNum = 35 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := harriesWong) (l := harriesWongIndepSet)
    (by native_decide) (by native_decide)

/-- **The Harries–Wong graph has no triangle**, having girth ten, so its cliques are its edges. -/
@[simp] theorem cliqueNum_harriesWong : harriesWong.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_harriesWong]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_harriesWong]; decide))

/-- **The Harries–Wong graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_harriesWong : harriesWong.chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_harriesWong, by rw [E_harriesWong]; decide⟩

/-- A proper three-edge-colouring of the Harries–Wong graph, keyed by the ordered pair of
endpoints: three perfect matchings, one per colour. -/
def harriesWongEdgeColList : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 2), ((0, 9), 1), ((0, 69), 0), ((1, 2), 1), ((1, 26), 0), ((2, 3), 2), ((2, 33), 0),
   ((3, 4), 0), ((3, 56), 1), ((4, 5), 2), ((4, 21), 1), ((5, 6), 0), ((5, 38), 1), ((6, 7), 2),
   ((6, 15), 1), ((7, 8), 1), ((7, 48), 0), ((8, 9), 0), ((8, 63), 2), ((9, 10), 2), ((10, 11), 0),
   ((10, 19), 1), ((11, 12), 2), ((11, 36), 1), ((12, 13), 0), ((12, 57), 1), ((13, 14), 1),
   ((13, 42), 2), ((14, 15), 0), ((14, 31), 2), ((15, 16), 2), ((16, 17), 1), ((16, 25), 0),
   ((17, 18), 2), ((17, 60), 0), ((18, 19), 0), ((18, 53), 1), ((19, 20), 2), ((20, 21), 0),
   ((20, 29), 1), ((21, 22), 2), ((22, 23), 0), ((22, 43), 1), ((23, 24), 1), ((23, 50), 2),
   ((24, 25), 2), ((24, 65), 0), ((25, 26), 1), ((26, 27), 2), ((27, 28), 0), ((27, 40), 1),
   ((28, 29), 2), ((28, 47), 1), ((29, 30), 0), ((30, 31), 1), ((30, 67), 2), ((31, 32), 0),
   ((32, 33), 1), ((32, 51), 2), ((33, 34), 2), ((34, 35), 1), ((34, 61), 0), ((35, 36), 0),
   ((35, 46), 2), ((36, 37), 2), ((37, 38), 0), ((37, 66), 1), ((38, 39), 2), ((39, 40), 0),
   ((39, 52), 1), ((40, 41), 2), ((41, 42), 1), ((41, 62), 0), ((42, 43), 0), ((43, 44), 2),
   ((44, 45), 0), ((44, 69), 1), ((45, 46), 1), ((45, 54), 2), ((46, 47), 0), ((47, 48), 2),
   ((48, 49), 1), ((49, 50), 0), ((49, 58), 2), ((50, 51), 1), ((51, 52), 0), ((52, 53), 2),
   ((53, 54), 0), ((54, 55), 1), ((55, 56), 0), ((55, 64), 2), ((56, 57), 2), ((57, 58), 0),
   ((58, 59), 1), ((59, 60), 2), ((59, 68), 0), ((60, 61), 1), ((61, 62), 2), ((62, 63), 1),
   ((63, 64), 0), ((64, 65), 1), ((65, 66), 2), ((66, 67), 0), ((67, 68), 1), ((68, 69), 2)]

/-- The list `harriesWongEdgeColList` read as an edge colouring.  The key is sorted, so the
colouring is symmetric before anything is proved; edges off the list get colour `0`. -/
def harriesWongEdgeCol (x y : harriesWong.V) : Fin 3 :=
  ⟨min ((harriesWongEdgeColList.lookup (min x.1 y.1, max x.1 y.1)).getD 0) 2, by omega⟩

theorem harriesWongEdgeCol_symm : ∀ x y : harriesWong.V,
    harriesWongEdgeCol x y = harriesWongEdgeCol y x := by
  intro x y
  simp only [harriesWongEdgeCol, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]

theorem harriesWongEdgeCol_proper : ∀ u v w : harriesWong.V,
    harriesWong.Adj u v = true → harriesWong.Adj u w = true → v ≠ w →
      harriesWongEdgeCol u v ≠ harriesWongEdgeCol u w := by native_decide

/-- **The Harries–Wong graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_harriesWong : harriesWong.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := harriesWong)
      harriesWongEdgeCol harriesWongEdgeCol_symm harriesWongEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum harriesWong
    rwa [maxDeg_harriesWong] at h

/-! ## The Balaban 10-cage

The first `(3, 10)`-cage to be found, in 1972; the three cages of girth ten were shown to be
the only ones a year later. -/

@[simp] theorem maxDeg_balaban10Cage : balaban10Cage.maxDeg = 3 :=
  haveI : Nonempty balaban10Cage.V := ⟨(0 : Fin 70)⟩
  (isRegularWith_balaban10Cage).maxDeg_eq

/-- One side of the bipartition of the Balaban 10-cage: thirty-five vertices, no two adjacent. -/
def balaban10CageIndepSet : List (Fin 70) :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
   50, 52, 54, 56, 58, 60, 62, 64, 66, 68]

/-- **The independence number of the Balaban 10-cage is thirty-five.**  A cubic bipartite graph
has a perfect matching, so neither side of the bipartition can be beaten. -/
@[simp] theorem indepNum_balaban10Cage : balaban10Cage.indepNum = 35 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := balaban10Cage) (l := balaban10CageIndepSet)
    (by native_decide) (by native_decide)

/-- **The Balaban 10-cage has no triangle**, having girth ten, so its cliques are its edges. -/
@[simp] theorem cliqueNum_balaban10Cage : balaban10Cage.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_balaban10Cage]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_balaban10Cage]; decide))

/-- **The Balaban 10-cage is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_balaban10Cage : balaban10Cage.chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_balaban10Cage, by rw [E_balaban10Cage]; decide⟩

/-- A proper three-edge-colouring of the Balaban 10-cage, keyed by the ordered pair of endpoints:
three perfect matchings, one per colour. -/
def balaban10CageEdgeColList : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 2), ((0, 61), 1), ((0, 69), 0), ((1, 2), 0), ((1, 46), 1), ((2, 3), 2), ((2, 53), 1),
   ((3, 4), 0), ((3, 32), 1), ((4, 5), 1), ((4, 17), 2), ((5, 6), 2), ((5, 40), 0), ((6, 7), 1),
   ((6, 63), 0), ((7, 8), 0), ((7, 48), 2), ((8, 9), 2), ((8, 27), 1), ((9, 10), 0), ((9, 34), 1),
   ((10, 11), 2), ((10, 19), 1), ((11, 12), 0), ((11, 52), 1), ((12, 13), 2), ((12, 41), 1),
   ((13, 14), 1), ((13, 30), 0), ((14, 15), 2), ((14, 47), 0), ((15, 16), 0), ((15, 36), 1),
   ((16, 17), 1), ((16, 25), 2), ((17, 18), 0), ((18, 19), 2), ((18, 57), 1), ((19, 20), 0),
   ((20, 21), 2), ((20, 45), 1), ((21, 22), 0), ((21, 38), 1), ((22, 23), 2), ((22, 31), 1),
   ((23, 24), 0), ((23, 62), 1), ((24, 25), 1), ((24, 51), 2), ((25, 26), 0), ((26, 27), 2),
   ((26, 43), 1), ((27, 28), 0), ((28, 29), 2), ((28, 69), 1), ((29, 30), 1), ((29, 56), 0),
   ((30, 31), 2), ((31, 32), 0), ((32, 33), 2), ((33, 34), 0), ((33, 66), 1), ((34, 35), 2),
   ((35, 36), 0), ((35, 60), 1), ((36, 37), 2), ((37, 38), 0), ((37, 54), 1), ((38, 39), 2),
   ((39, 40), 1), ((39, 68), 0), ((40, 41), 2), ((41, 42), 0), ((42, 43), 2), ((42, 59), 1),
   ((43, 44), 0), ((44, 45), 2), ((44, 65), 1), ((45, 46), 0), ((46, 47), 2), ((47, 48), 1),
   ((48, 49), 0), ((49, 50), 2), ((49, 58), 1), ((50, 51), 1), ((50, 67), 0), ((51, 52), 0),
   ((52, 53), 2), ((53, 54), 0), ((54, 55), 2), ((55, 56), 1), ((55, 64), 0), ((56, 57), 2),
   ((57, 58), 0), ((58, 59), 2), ((59, 60), 0), ((60, 61), 2), ((61, 62), 0), ((62, 63), 2),
   ((63, 64), 1), ((64, 65), 2), ((65, 66), 0), ((66, 67), 2), ((67, 68), 1), ((68, 69), 2)]

/-- The list `balaban10CageEdgeColList` read as an edge colouring.  The key is sorted, so the
colouring is symmetric before anything is proved; edges off the list get colour `0`. -/
def balaban10CageEdgeCol (x y : balaban10Cage.V) : Fin 3 :=
  ⟨min ((balaban10CageEdgeColList.lookup (min x.1 y.1, max x.1 y.1)).getD 0) 2, by omega⟩

theorem balaban10CageEdgeCol_symm : ∀ x y : balaban10Cage.V,
    balaban10CageEdgeCol x y = balaban10CageEdgeCol y x := by
  intro x y
  simp only [balaban10CageEdgeCol, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]

theorem balaban10CageEdgeCol_proper : ∀ u v w : balaban10Cage.V,
    balaban10Cage.Adj u v = true → balaban10Cage.Adj u w = true → v ≠ w →
      balaban10CageEdgeCol u v ≠ balaban10CageEdgeCol u w := by native_decide

/-- **The Balaban 10-cage is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_balaban10Cage : balaban10Cage.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := balaban10Cage)
      balaban10CageEdgeCol balaban10CageEdgeCol_symm balaban10CageEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum balaban10Cage
    rwa [maxDeg_balaban10Cage] at h

/-! ## The Foster graph

The bipartite double cover of the Nauru graph's larger cousin: cubic, distance-transitive and
bipartite on ninety vertices, girth ten. -/

@[simp] theorem maxDeg_foster : foster.maxDeg = 3 :=
  haveI : Nonempty foster.V := ⟨(0 : Fin 90)⟩
  (isRegularWith_foster).maxDeg_eq

/-- One side of the bipartition of the Foster graph: forty-five vertices, no two adjacent. -/
def fosterIndepSet : List (Fin 90) :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
   50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88]

/-- **The independence number of the Foster graph is forty-five.**  A cubic bipartite graph has a
perfect matching, so neither side of the bipartition can be beaten. -/
@[simp] theorem indepNum_foster : foster.indepNum = 45 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := foster) (l := fosterIndepSet)
    (by native_decide) (by native_decide)

/-- **The Foster graph has no triangle**, having girth ten, so its cliques are its edges. -/
@[simp] theorem cliqueNum_foster : foster.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_foster]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_foster]; decide))

/-- **The Foster graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_foster : foster.chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_foster, by rw [E_foster]; decide⟩

/-- A proper three-edge-colouring of the Foster graph, keyed by the ordered pair of endpoints:
three perfect matchings, one per colour. -/
def fosterEdgeColList : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 2), ((0, 17), 1), ((0, 89), 0), ((1, 2), 0), ((1, 82), 1), ((2, 3), 2), ((2, 39), 1),
   ((3, 4), 0), ((3, 56), 1), ((4, 5), 1), ((4, 13), 2), ((5, 6), 0), ((5, 78), 2), ((6, 7), 2),
   ((6, 23), 1), ((7, 8), 1), ((7, 88), 0), ((8, 9), 0), ((8, 45), 2), ((9, 10), 2), ((9, 62), 1),
   ((10, 11), 0), ((10, 19), 1), ((11, 12), 2), ((11, 84), 1), ((12, 13), 0), ((12, 29), 1),
   ((13, 14), 1), ((14, 15), 0), ((14, 51), 2), ((15, 16), 2), ((15, 68), 1), ((16, 17), 0),
   ((16, 25), 1), ((17, 18), 2), ((18, 19), 0), ((18, 35), 1), ((19, 20), 2), ((20, 21), 0),
   ((20, 57), 1), ((21, 22), 2), ((21, 74), 1), ((22, 23), 0), ((22, 31), 1), ((23, 24), 2),
   ((24, 25), 0), ((24, 41), 1), ((25, 26), 2), ((26, 27), 0), ((26, 63), 1), ((27, 28), 2),
   ((27, 80), 1), ((28, 29), 0), ((28, 37), 1), ((29, 30), 2), ((30, 31), 0), ((30, 47), 1),
   ((31, 32), 2), ((32, 33), 0), ((32, 69), 1), ((33, 34), 2), ((33, 86), 1), ((34, 35), 0),
   ((34, 43), 1), ((35, 36), 2), ((36, 37), 0), ((36, 53), 1), ((37, 38), 2), ((38, 39), 0),
   ((38, 75), 1), ((39, 40), 2), ((40, 41), 0), ((40, 49), 1), ((41, 42), 2), ((42, 43), 0),
   ((42, 59), 1), ((43, 44), 2), ((44, 45), 0), ((44, 81), 1), ((45, 46), 1), ((46, 47), 0),
   ((46, 55), 2), ((47, 48), 2), ((48, 49), 0), ((48, 65), 1), ((49, 50), 2), ((50, 51), 1),
   ((50, 87), 0), ((51, 52), 0), ((52, 53), 2), ((52, 61), 1), ((53, 54), 0), ((54, 55), 1),
   ((54, 71), 2), ((55, 56), 0), ((56, 57), 2), ((57, 58), 0), ((58, 59), 2), ((58, 67), 1),
   ((59, 60), 0), ((60, 61), 2), ((60, 77), 1), ((61, 62), 0), ((62, 63), 2), ((63, 64), 0),
   ((64, 65), 2), ((64, 73), 1), ((65, 66), 0), ((66, 67), 2), ((66, 83), 1), ((67, 68), 0),
   ((68, 69), 2), ((69, 70), 0), ((70, 71), 1), ((70, 79), 2), ((71, 72), 0), ((72, 73), 2),
   ((72, 89), 1), ((73, 74), 0), ((74, 75), 2), ((75, 76), 0), ((76, 77), 2), ((76, 85), 1),
   ((77, 78), 0), ((78, 79), 1), ((79, 80), 0), ((80, 81), 2), ((81, 82), 0), ((82, 83), 2),
   ((83, 84), 0), ((84, 85), 2), ((85, 86), 0), ((86, 87), 2), ((87, 88), 1), ((88, 89), 2)]

/-- The list `fosterEdgeColList` read as an edge colouring.  The key is sorted, so the colouring
is symmetric before anything is proved; edges off the list get colour `0`. -/
def fosterEdgeCol (x y : foster.V) : Fin 3 :=
  ⟨min ((fosterEdgeColList.lookup (min x.1 y.1, max x.1 y.1)).getD 0) 2, by omega⟩

theorem fosterEdgeCol_symm : ∀ x y : foster.V,
    fosterEdgeCol x y = fosterEdgeCol y x := by
  intro x y
  simp only [fosterEdgeCol, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]

theorem fosterEdgeCol_proper : ∀ u v w : foster.V,
    foster.Adj u v = true → foster.Adj u w = true → v ≠ w →
      fosterEdgeCol u v ≠ fosterEdgeCol u w := by native_decide

/-- **The Foster graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_foster : foster.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := foster)
      fosterEdgeCol fosterEdgeCol_symm fosterEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum foster
    rwa [maxDeg_foster] at h

/-! ## The Ljubljana graph

The Levi graph of the Ljubljana configuration `(56₃)`: cubic, bipartite and edge-transitive on
a hundred and twelve vertices, girth ten. -/

@[simp] theorem maxDeg_ljubljana : ljubljana.maxDeg = 3 :=
  haveI : Nonempty ljubljana.V := ⟨(0 : Fin 112)⟩
  (isRegularWith_ljubljana).maxDeg_eq

/-- One side of the bipartition of the Ljubljana graph: fifty-six vertices, no two adjacent. -/
def ljubljanaIndepSet : List (Fin 112) :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
   50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96,
   98, 100, 102, 104, 106, 108, 110]

/-- **The independence number of the Ljubljana graph is fifty-six.**  A cubic bipartite graph has
a perfect matching, so neither side of the bipartition can be beaten. -/
@[simp] theorem indepNum_ljubljana : ljubljana.indepNum = 56 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := ljubljana) (l := ljubljanaIndepSet)
    (by native_decide) (by native_decide)

/-- **The Ljubljana graph has no triangle**, having girth ten, so its cliques are its edges. -/
@[simp] theorem cliqueNum_ljubljana : ljubljana.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_ljubljana]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_ljubljana]; decide))

/-- **The Ljubljana graph is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_ljubljana : ljubljana.chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_ljubljana, by rw [E_ljubljana]; decide⟩

/-- A proper three-edge-colouring of the Ljubljana graph, keyed by the ordered pair of endpoints:
three perfect matchings, one per colour. -/
def ljubljanaEdgeColList : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 1), ((0, 47), 2), ((0, 111), 0), ((1, 2), 2), ((1, 90), 0), ((2, 3), 1), ((2, 83), 0),
   ((3, 4), 2), ((3, 42), 0), ((4, 5), 0), ((4, 29), 1), ((5, 6), 1), ((5, 96), 2), ((6, 7), 2),
   ((6, 87), 0), ((7, 8), 0), ((7, 78), 1), ((8, 9), 2), ((8, 33), 1), ((9, 10), 1), ((9, 24), 0),
   ((10, 11), 0), ((10, 39), 2), ((11, 12), 1), ((11, 82), 2), ((12, 13), 0), ((12, 105), 2),
   ((13, 14), 2), ((13, 28), 1), ((14, 15), 0), ((14, 77), 1), ((15, 16), 1), ((15, 48), 2),
   ((16, 17), 0), ((16, 55), 2), ((17, 18), 1), ((17, 94), 2), ((18, 19), 2), ((18, 109), 0),
   ((19, 20), 1), ((19, 36), 0), ((20, 21), 2), ((20, 99), 0), ((21, 22), 1), ((21, 70), 0),
   ((22, 23), 2), ((22, 63), 0), ((23, 24), 1), ((23, 54), 0), ((24, 25), 2), ((25, 26), 0),
   ((25, 108), 1), ((26, 27), 2), ((26, 67), 1), ((27, 28), 0), ((27, 58), 1), ((28, 29), 2),
   ((29, 30), 0), ((30, 31), 2), ((30, 51), 1), ((31, 32), 0), ((31, 62), 1), ((32, 33), 2),
   ((32, 93), 1), ((33, 34), 0), ((34, 35), 1), ((34, 57), 2), ((35, 36), 2), ((35, 44), 0),
   ((36, 37), 1), ((37, 38), 2), ((37, 88), 0), ((38, 39), 0), ((38, 73), 1), ((39, 40), 1),
   ((40, 41), 0), ((40, 61), 2), ((41, 42), 1), ((41, 102), 2), ((42, 43), 2), ((43, 44), 1),
   ((43, 76), 0), ((44, 45), 2), ((45, 46), 0), ((45, 106), 1), ((46, 47), 1), ((46, 97), 2),
   ((47, 48), 0), ((48, 49), 1), ((49, 50), 2), ((49, 68), 0), ((50, 51), 0), ((50, 101), 1),
   ((51, 52), 2), ((52, 53), 0), ((52, 81), 1), ((53, 54), 2), ((53, 74), 1), ((54, 55), 1),
   ((55, 56), 0), ((56, 57), 1), ((56, 103), 2), ((57, 58), 0), ((58, 59), 2), ((59, 60), 0),
   ((59, 98), 1), ((60, 61), 1), ((60, 85), 2), ((61, 62), 0), ((62, 63), 2), ((63, 64), 1),
   ((64, 65), 2), ((64, 89), 0), ((65, 66), 1), ((65, 80), 0), ((66, 67), 0), ((66, 95), 2),
   ((67, 68), 2), ((68, 69), 1), ((69, 70), 2), ((69, 84), 0), ((70, 71), 1), ((71, 72), 0),
   ((71, 104), 2), ((72, 73), 2), ((72, 111), 1), ((73, 74), 0), ((74, 75), 2), ((75, 76), 1),
   ((75, 92), 0), ((76, 77), 2), ((77, 78), 0), ((78, 79), 2), ((79, 80), 1), ((79, 110), 0),
   ((80, 81), 2), ((81, 82), 0), ((82, 83), 1), ((83, 84), 2), ((84, 85), 1), ((85, 86), 0),
   ((86, 87), 2), ((86, 107), 1), ((87, 88), 1), ((88, 89), 2), ((89, 90), 1), ((90, 91), 2),
   ((91, 92), 1), ((91, 100), 0), ((92, 93), 2), ((93, 94), 0), ((94, 95), 1), ((95, 96), 0),
   ((96, 97), 1), ((97, 98), 0), ((98, 99), 2), ((99, 100), 1), ((100, 101), 2), ((101, 102), 0),
   ((102, 103), 1), ((103, 104), 0), ((104, 105), 1), ((105, 106), 0), ((106, 107), 2),
   ((107, 108), 0), ((108, 109), 2), ((109, 110), 1), ((110, 111), 2)]

/-- The list `ljubljanaEdgeColList` read as an edge colouring.  The key is sorted, so the
colouring is symmetric before anything is proved; edges off the list get colour `0`. -/
def ljubljanaEdgeCol (x y : ljubljana.V) : Fin 3 :=
  ⟨min ((ljubljanaEdgeColList.lookup (min x.1 y.1, max x.1 y.1)).getD 0) 2, by omega⟩

theorem ljubljanaEdgeCol_symm : ∀ x y : ljubljana.V,
    ljubljanaEdgeCol x y = ljubljanaEdgeCol y x := by
  intro x y
  simp only [ljubljanaEdgeCol, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]

theorem ljubljanaEdgeCol_proper : ∀ u v w : ljubljana.V,
    ljubljana.Adj u v = true → ljubljana.Adj u w = true → v ≠ w →
      ljubljanaEdgeCol u v ≠ ljubljanaEdgeCol u w := by native_decide

/-- **The Ljubljana graph is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_ljubljana : ljubljana.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := ljubljana)
      ljubljanaEdgeCol ljubljanaEdgeCol_symm ljubljanaEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum ljubljana
    rwa [maxDeg_ljubljana] at h

/-! ## The Tutte 12-cage

The Benson graph: the unique `(3, 12)`-cage, the incidence graph of the generalised hexagon
`GH(2, 2)`, on a hundred and twenty-six vertices. -/

@[simp] theorem maxDeg_tutte12Cage : tutte12Cage.maxDeg = 3 :=
  haveI : Nonempty tutte12Cage.V := ⟨(0 : Fin 126)⟩
  (isRegularWith_tutte12Cage).maxDeg_eq

/-- One side of the bipartition of the Tutte 12-cage: sixty-three vertices, no two adjacent. -/
def tutte12CageIndepSet : List (Fin 126) :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
   50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96,
   98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124]

-- Measured: 283 803 heartbeats, the only theorem in the file over the default.  The 126-vertex
-- independence CNF is the largest here, and the elaborator's `isDefEq` on it is what runs long.
set_option maxHeartbeats 800000 in
/-- **The independence number of the Tutte 12-cage is sixty-three.**  A cubic bipartite graph has
a perfect matching, so neither side of the bipartition can be beaten. -/
@[simp] theorem indepNum_tutte12Cage : tutte12Cage.indepNum = 63 := by
  refine le_antisymm (by graph_sat native) ?_
  exact le_indepNum_of_nodup (G := tutte12Cage) (l := tutte12CageIndepSet)
    (by native_decide) (by native_decide)

/-- **The Tutte 12-cage has no triangle**, having girth twelve, so its cliques are its edges. -/
@[simp] theorem cliqueNum_tutte12Cage : tutte12Cage.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_tutte12Cage]; decide))
    (two_le_cliqueNum_of_E_pos (by rw [E_tutte12Cage]; decide))

/-- **The Tutte 12-cage is bipartite**, so two colours do and one does not. -/
@[simp] theorem chromNum_tutte12Cage : tutte12Cage.chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_tutte12Cage, by rw [E_tutte12Cage]; decide⟩

/-- A proper three-edge-colouring of the Tutte 12-cage, keyed by the ordered pair of endpoints:
three perfect matchings, one per colour. -/
def tutte12CageEdgeColList : List ((ℕ × ℕ) × ℕ) :=
  [((0, 1), 1), ((0, 17), 2), ((0, 125), 0), ((1, 2), 0), ((1, 28), 2), ((2, 3), 2), ((2, 115), 1),
   ((3, 4), 1), ((3, 70), 0), ((4, 5), 2), ((4, 95), 0), ((5, 6), 0), ((5, 40), 1), ((6, 7), 1),
   ((6, 121), 2), ((7, 8), 2), ((7, 20), 0), ((8, 9), 0), ((8, 81), 1), ((9, 10), 2), ((9, 62), 1),
   ((10, 11), 0), ((10, 109), 1), ((11, 12), 2), ((11, 32), 1), ((12, 13), 1), ((12, 69), 0),
   ((13, 14), 2), ((13, 24), 0), ((14, 15), 0), ((14, 119), 1), ((15, 16), 1), ((15, 84), 2),
   ((16, 17), 0), ((16, 75), 2), ((17, 18), 1), ((18, 19), 0), ((18, 35), 2), ((19, 20), 1),
   ((19, 46), 2), ((20, 21), 2), ((21, 22), 0), ((21, 88), 1), ((22, 23), 2), ((22, 113), 1),
   ((23, 24), 1), ((23, 58), 0), ((24, 25), 2), ((25, 26), 0), ((25, 38), 1), ((26, 27), 2),
   ((26, 99), 1), ((27, 28), 0), ((27, 80), 1), ((28, 29), 1), ((29, 30), 0), ((29, 50), 2),
   ((30, 31), 1), ((30, 87), 2), ((31, 32), 0), ((31, 42), 2), ((32, 33), 2), ((33, 34), 0),
   ((33, 102), 1), ((34, 35), 1), ((34, 93), 2), ((35, 36), 0), ((36, 37), 1), ((36, 53), 2),
   ((37, 38), 0), ((37, 64), 2), ((38, 39), 2), ((39, 40), 0), ((39, 106), 1), ((40, 41), 2),
   ((41, 42), 0), ((41, 76), 1), ((42, 43), 1), ((43, 44), 0), ((43, 56), 2), ((44, 45), 2),
   ((44, 117), 1), ((45, 46), 0), ((45, 98), 1), ((46, 47), 1), ((47, 48), 0), ((47, 68), 2),
   ((48, 49), 1), ((48, 105), 2), ((49, 50), 0), ((49, 60), 2), ((50, 51), 1), ((51, 52), 0),
   ((51, 120), 2), ((52, 53), 1), ((52, 111), 2), ((53, 54), 0), ((54, 55), 1), ((54, 71), 2),
   ((55, 56), 0), ((55, 82), 2), ((56, 57), 1), ((57, 58), 2), ((57, 124), 0), ((58, 59), 1),
   ((59, 60), 0), ((59, 94), 2), ((60, 61), 1), ((61, 62), 0), ((61, 74), 2), ((62, 63), 2),
   ((63, 64), 0), ((63, 116), 1), ((64, 65), 1), ((65, 66), 2), ((65, 86), 0), ((66, 67), 1),
   ((66, 123), 0), ((67, 68), 0), ((67, 78), 2), ((68, 69), 1), ((69, 70), 2), ((70, 71), 1),
   ((71, 72), 0), ((72, 73), 2), ((72, 89), 1), ((73, 74), 0), ((73, 100), 1), ((74, 75), 1),
   ((75, 76), 0), ((76, 77), 2), ((77, 78), 0), ((77, 112), 1), ((78, 79), 1), ((79, 80), 0),
   ((79, 92), 2), ((80, 81), 2), ((81, 82), 0), ((82, 83), 1), ((83, 84), 0), ((83, 104), 2),
   ((84, 85), 1), ((85, 86), 2), ((85, 96), 0), ((86, 87), 1), ((87, 88), 0), ((88, 89), 2),
   ((89, 90), 0), ((90, 91), 2), ((90, 107), 1), ((91, 92), 0), ((91, 118), 1), ((92, 93), 1),
   ((93, 94), 0), ((94, 95), 1), ((95, 96), 2), ((96, 97), 1), ((97, 98), 0), ((97, 110), 2),
   ((98, 99), 2), ((99, 100), 0), ((100, 101), 2), ((101, 102), 0), ((101, 122), 1),
   ((102, 103), 2), ((103, 104), 0), ((103, 114), 1), ((104, 105), 1), ((105, 106), 0),
   ((106, 107), 2), ((107, 108), 0), ((108, 109), 2), ((108, 125), 1), ((109, 110), 0),
   ((110, 111), 1), ((111, 112), 0), ((112, 113), 2), ((113, 114), 0), ((114, 115), 2),
   ((115, 116), 0), ((116, 117), 2), ((117, 118), 0), ((118, 119), 2), ((119, 120), 0),
   ((120, 121), 1), ((121, 122), 0), ((122, 123), 2), ((123, 124), 1), ((124, 125), 2)]

/-- The list `tutte12CageEdgeColList` read as an edge colouring.  The key is sorted, so the
colouring is symmetric before anything is proved; edges off the list get colour `0`. -/
def tutte12CageEdgeCol (x y : tutte12Cage.V) : Fin 3 :=
  ⟨min ((tutte12CageEdgeColList.lookup (min x.1 y.1, max x.1 y.1)).getD 0) 2, by omega⟩

theorem tutte12CageEdgeCol_symm : ∀ x y : tutte12Cage.V,
    tutte12CageEdgeCol x y = tutte12CageEdgeCol y x := by
  intro x y
  simp only [tutte12CageEdgeCol, Nat.min_comm x.1 y.1, Nat.max_comm x.1 y.1]

theorem tutte12CageEdgeCol_proper : ∀ u v w : tutte12Cage.V,
    tutte12Cage.Adj u v = true → tutte12Cage.Adj u w = true → v ≠ w →
      tutte12CageEdgeCol u v ≠ tutte12CageEdgeCol u w := by native_decide

/-- **The Tutte 12-cage is class one**: `χ' = Δ = 3`. -/
@[simp] theorem edgeChromNum_tutte12Cage : tutte12Cage.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tutte12Cage)
      tutte12CageEdgeCol tutte12CageEdgeCol_symm tutte12CageEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum tutte12Cage
    rwa [maxDeg_tutte12Cage] at h

end NamedGraphs
