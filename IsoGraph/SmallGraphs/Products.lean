import IsoGraph.SmallGraphs.Complements

/-!
# Products of the named graphs

Products of the named graphs with each other and with the hypercubes, and the Mycielskians and line
graphs of the results.
-/

namespace IsoGraph

theorem chromNum_king (m n : ℕ) : (path (m + 2) ⊠g path (n + 2)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (G := path (m + 2)) (H := path (n + 2))
    (by rw [chromNum_path, cliqueNum_path]) (by rw [chromNum_path, cliqueNum_path])
  rw [cliqueNum_path, cliqueNum_path] at h
  omega

theorem chromNum_eq_cliqueNum_hypercube (n : ℕ) :
    (hypercube (n + 1)).chromNum = (hypercube (n + 1)).cliqueNum := by
  rw [chromNum_hypercube, cliqueNum_hypercube]

theorem chromNum_strongProduct_hypercube (m n : ℕ) :
    (hypercube (m + 1) ⊠g hypercube (n + 1)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_hypercube m) (chromNum_eq_cliqueNum_hypercube n)
  rw [cliqueNum_hypercube, cliqueNum_hypercube] at h
  omega

theorem chromNum_lexProduct_hypercube (m n : ℕ) :
    (hypercube (m + 1) ·g hypercube (n + 1)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_hypercube m) (chromNum_eq_cliqueNum_hypercube n)
  rw [cliqueNum_hypercube, cliqueNum_hypercube] at h
  omega

theorem chromNum_eq_cliqueNum_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).chromNum = (bipartite (m + 1) (n + 1)).cliqueNum := by
  rw [chromNum_bipartite, cliqueNum_bipartite]

theorem chromNum_strongProduct_bipartite (a b c d : ℕ) :
    (bipartite (a + 1) (b + 1) ⊠g bipartite (c + 1) (d + 1)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_bipartite a b) (chromNum_eq_cliqueNum_bipartite c d)
  rw [cliqueNum_bipartite, cliqueNum_bipartite] at h
  omega

theorem chromNum_lexProduct_bipartite (a b c d : ℕ) :
    (bipartite (a + 1) (b + 1) ·g bipartite (c + 1) (d + 1)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_bipartite a b) (chromNum_eq_cliqueNum_bipartite c d)
  rw [cliqueNum_bipartite, cliqueNum_bipartite] at h
  omega

/-- The **king graph** on an `(m+1) × (n+1)` board: a king crosses the board in `max m n` moves. -/
theorem diameter_king (m n : ℕ) : (path (m + 1) ⊠g path (n + 1)).diameter = max m n := by
  rw [diameter_strongProduct (isConnected_path m) (isConnected_path n), diameter_path,
    diameter_path]

theorem chromNum_tensorProduct_hypercube (m n : ℕ) :
    (hypercube (m + 1) ⊗g hypercube (n + 1)).chromNum = 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_hypercube m) (chromNum_eq_cliqueNum_hypercube n)
  rw [cliqueNum_hypercube, cliqueNum_hypercube] at h
  omega

theorem chromNum_tensorProduct_bipartite (a b c d : ℕ) :
    (bipartite (a + 1) (b + 1) ⊗g bipartite (c + 1) (d + 1)).chromNum = 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_bipartite a b) (chromNum_eq_cliqueNum_bipartite c d)
  rw [cliqueNum_bipartite, cliqueNum_bipartite] at h
  omega

/-! ### More vertex-transitive graphs -/

theorem isVertexTransitive_cartesianProduct_hypercube (m n : ℕ) :
    IsVertexTransitive (hypercube m □g hypercube n) :=
  (isVertexTransitive_hypercube m).cartesianProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_tensorProduct_hypercube (m n : ℕ) :
    IsVertexTransitive (hypercube m ⊗g hypercube n) :=
  (isVertexTransitive_hypercube m).tensorProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_strongProduct_hypercube (m n : ℕ) :
    IsVertexTransitive (hypercube m ⊠g hypercube n) :=
  (isVertexTransitive_hypercube m).strongProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_lexProduct_hypercube (m n : ℕ) :
    IsVertexTransitive (hypercube m ·g hypercube n) :=
  (isVertexTransitive_hypercube m).lexProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_cartesianProduct_cycle_hypercube (m n : ℕ) :
    IsVertexTransitive (cycle m □g hypercube n) :=
  (isVertexTransitive_cycle m).cartesianProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_tensorProduct_cycle_hypercube (m n : ℕ) :
    IsVertexTransitive (cycle m ⊗g hypercube n) :=
  (isVertexTransitive_cycle m).tensorProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_strongProduct_cycle_hypercube (m n : ℕ) :
    IsVertexTransitive (cycle m ⊠g hypercube n) :=
  (isVertexTransitive_cycle m).strongProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_lexProduct_cycle_hypercube (m n : ℕ) :
    IsVertexTransitive (cycle m ·g hypercube n) :=
  (isVertexTransitive_cycle m).lexProduct (isVertexTransitive_hypercube n)

theorem isVertexTransitive_cartesianProduct_kneser (m k n l : ℕ) :
    IsVertexTransitive (kneser m k □g kneser n l) :=
  (isVertexTransitive_kneser m k).cartesianProduct (isVertexTransitive_kneser n l)

theorem isVertexTransitive_tensorProduct_kneser (m k n l : ℕ) :
    IsVertexTransitive (kneser m k ⊗g kneser n l) :=
  (isVertexTransitive_kneser m k).tensorProduct (isVertexTransitive_kneser n l)

theorem isVertexTransitive_cartesianProduct_paley (p q : ℕ) [NeZero p] [Fact p.Prime] [NeZero q]
    [Fact q.Prime] : IsVertexTransitive (paley p □g paley q) :=
  (isVertexTransitive_paley p).cartesianProduct (isVertexTransitive_paley q)

theorem isVertexTransitive_strongProduct_paley (p q : ℕ) [NeZero p] [Fact p.Prime] [NeZero q]
    [Fact q.Prime] : IsVertexTransitive (paley p ⊠g paley q) :=
  (isVertexTransitive_paley p).strongProduct (isVertexTransitive_paley q)

theorem isVertexTransitive_cartesianProduct_crown (m n : ℕ) :
    IsVertexTransitive (crown m □g crown n) :=
  (isVertexTransitive_crown m).cartesianProduct (isVertexTransitive_crown n)

theorem isVertexTransitive_cartesianProduct_foldedCube (m n : ℕ) :
    IsVertexTransitive (foldedCube m □g foldedCube n) :=
  (isVertexTransitive_foldedCube m).cartesianProduct (isVertexTransitive_foldedCube n)

theorem isVertexTransitive_strongProduct_foldedCube (m n : ℕ) :
    IsVertexTransitive (foldedCube m ⊠g foldedCube n) :=
  (isVertexTransitive_foldedCube m).strongProduct (isVertexTransitive_foldedCube n)

/-! Line graphs of arc-transitive graphs. -/

theorem isVertexTransitive_lineGraph_hypercube (n : ℕ) :
    IsVertexTransitive (lineGraph (hypercube n)) := (isArcTransitive_hypercube n).lineGraph

theorem isVertexTransitive_lineGraph_kneser (n k : ℕ) :
    IsVertexTransitive (lineGraph (kneser n k)) := (isArcTransitive_kneser n k).lineGraph

theorem isVertexTransitive_lineGraph_petersen :
    IsVertexTransitive (lineGraph petersen) := isArcTransitive_petersen.lineGraph

/-! Complements of vertex-transitive graphs. -/

theorem isVertexTransitive_compl_petersen : IsVertexTransitive petersenᶜ :=
  (isVertexTransitive_compl _).2 isVertexTransitive_petersen

theorem isVertexTransitive_compl_bipartite_self (n : ℕ) :
    IsVertexTransitive ((bipartite n n)ᶜ) :=
  (isVertexTransitive_compl _).2 (isVertexTransitive_bipartite_self n)

theorem isVertexTransitive_compl_lineGraph_petersen :
    IsVertexTransitive ((lineGraph petersen)ᶜ) :=
  (isVertexTransitive_compl _).2 isVertexTransitive_lineGraph_petersen

/-! ### The cartesian product of a cycle with a hypercube -/

theorem cliqueNum_cartesianProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 4) □g hypercube (n + 1)).cliqueNum = 2 := by
  have h := cliqueNum_cartesianProduct (G := cycle (m + 4)) (H := hypercube (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [cliqueNum_cycle, cliqueNum_hypercube] at h
  omega

theorem chromNum_cartesianProduct_cycle_hypercube_even (t n : ℕ) :
    (cycle (2 * t + 2) □g hypercube (n + 1)).chromNum = 2 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * t + 2)) (H := hypercube (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [chromNum_cycle_even, chromNum_hypercube] at h
  omega

theorem chromNum_cartesianProduct_cycle_hypercube_odd (t n : ℕ) :
    (cycle (2 * t + 3) □g hypercube (n + 1)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * t + 3)) (H := hypercube (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [chromNum_cycle_odd, chromNum_hypercube] at h
  omega

theorem diameter_cartesianProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 1) □g hypercube n).diameter = (m + 1) / 2 + n := by
  rw [diameter_cartesianProduct (isConnected_cycle m) (isConnected_hypercube n), diameter_cycle,
    diameter_hypercube]

theorem radius_cartesianProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 1) □g hypercube n).radius = (m + 1) / 2 + n := by
  rw [radius_cartesianProduct (isConnected_cycle m) (isConnected_hypercube n), radius_cycle,
    radius_hypercube]

theorem maxDeg_cartesianProduct_cycle_hypercube (m n : ℕ) :
    maxDeg (cycle (m + 3) □g hypercube n) = 2 + n := by
  have h := maxDeg_cartesianProduct (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [maxDeg_cycle, maxDeg_hypercube] at h
  omega

theorem minDeg_cartesianProduct_cycle_hypercube (m n : ℕ) :
    minDeg (cycle (m + 3) □g hypercube n) = 2 + n := by
  have h := minDeg_cartesianProduct (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [minDeg_cycle, minDeg_hypercube] at h
  omega

theorem isRegularWith_cartesianProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 3) □g hypercube n).IsRegularWith (2 + n) :=
  (isRegularWith_cycle m).cartesianProduct (isRegularWith_hypercube n)

theorem girth_cartesianProduct_cycle_hypercube_even (t n : ℕ) :
    (cycle (2 * t + 4) □g hypercube (n + 1)).girth = 4 := by
  have hb : IsBipartite (cycle (2 * t + 4)) := by
    rw [show 2 * t + 4 = 2 * (t + 2) from by ring]
    exact isBipartite_cycle_even (t + 2)
  exact girth_cartesianProduct (by rw [E_cycle]; omega) (E_hypercube_pos n) hb
    (isBipartite_hypercube (n + 1))

/-- **A rook's graph with both sides even is class one.** -/
theorem edgeChromNum_rook_even (m n : ℕ) :
    (rook (2 * m + 2) (2 * n + 2)).edgeChromNum = 2 * m + 2 * n + 2 := by
  rw [show rook (2 * m + 2) (2 * n + 2) = complete (2 * m + 2) □g complete (2 * n + 2) from rfl]
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := complete (2 * m + 2))
      (H := complete (2 * n + 2)) (E_complete_pos (2 * m)) (E_complete_pos (2 * n))
    rwa [edgeChromNum_complete_even, edgeChromNum_complete_even,
      show 2 * m + 1 + (2 * n + 1) = 2 * m + 2 * n + 2 by ring] at h
  · have hd : maxDeg (complete (2 * m + 2) □g complete (2 * n + 2)) = 2 * m + 2 * n + 2 := by
      rw [show complete (2 * m + 2) □g complete (2 * n + 2) = rook (2 * m + 2) (2 * n + 2) from rfl,
        show 2 * m + 2 = (2 * m + 1) + 1 by omega, show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        maxDeg_rook]
      omega
    rw [← hd]
    exact maxDeg_le_edgeChromNum _

/-- **An even cycle crossed with a hypercube is class one.** -/
theorem edgeChromNum_cartesianProduct_cycle_even_hypercube (m n : ℕ) :
    (cycle (2 * m + 4) □g hypercube (n + 1)).edgeChromNum = n + 3 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := hypercube (n + 1))
      (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega) (E_hypercube_pos n)
    rwa [edgeChromNum_cycle_even, edgeChromNum_hypercube, show 2 + (n + 1) = n + 3 by ring] at h
  · have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g hypercube (n + 1))
    rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, maxDeg_cartesianProduct_cycle_hypercube,
      show 2 + (n + 1) = n + 3 by ring] at h

/-- **An oversized independent set in a factor blocks Hamiltonicity of the tensor product.**  A set
independent in `G`, crossed with all of `H`, is independent in `G ⊗g H`, so if it covered more than
half of `G` it covers more than half of the product too — and by
`not_isHamiltonian_of_V_lt_two_mul_indepNum` there is no spanning cycle. This is the only handle
on the tensor product here: it has no Hamiltonicity certificate of its own, since the product of
two spanning cycles falls apart into two components whenever both factors are bipartite. -/
theorem not_isHamiltonian_tensorProduct_of_indepNum {G H : IsoGraph} (h3 : 3 ≤ (G ⊗g H).V)
    (hH : 0 < H.V) (h : G.V < 2 * G.indepNum) : ¬ (G ⊗g H).IsHamiltonian := by
  refine not_isHamiltonian_of_V_lt_two_mul_indepNum h3 ?_
  have hge := indepNum_mul_V_le_indepNum_tensorProduct G H
  rw [V_tensorProduct]
  calc G.V * H.V < 2 * G.indepNum * H.V := (Nat.mul_lt_mul_right hH).2 h
    _ = 2 * (G.indepNum * H.V) := by ring
    _ ≤ 2 * (G ⊗g H).indepNum := by omega

/-! ### Connectivity of the tensor product

`isConnected_tensorProduct` asks for a connected non-bipartite left factor and a connected right
factor with at least one edge; the odd cycles, the complete graphs on at least three vertices and
the Petersen graph all serve on the left. -/

theorem isConnected_tensorProduct_cycle_odd_hypercube (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g hypercube (n + 1)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_hypercube (n + 1))
    (not_isBipartite_cycle_odd a) (E_hypercube_pos n)

theorem numComponents_tensorProduct_cycle_odd_hypercube (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g hypercube (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_hypercube a n)

theorem isConnected_tensorProduct_cycle_odd_petersen (a : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g petersen) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) isConnected_petersen
    (not_isBipartite_cycle_odd a) (by rw [E_petersen]; omega)

theorem numComponents_tensorProduct_cycle_odd_petersen (a : ℕ) :
    (cycle (2 * a + 3) ⊗g petersen).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_petersen a)

theorem isConnected_tensorProduct_cycle_odd_star (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g star (n + 1)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_star (n + 1))
    (not_isBipartite_cycle_odd a) (by rw [E_star]; omega)

theorem numComponents_tensorProduct_cycle_odd_star (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g star (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_star a n)

theorem isConnected_tensorProduct_complete_hypercube (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g hypercube (n + 1)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_hypercube (n + 1))
    (not_isBipartite_complete m) (E_hypercube_pos n)

theorem numComponents_tensorProduct_complete_hypercube (m n : ℕ) :
    (complete (m + 3) ⊗g hypercube (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_hypercube m n)

theorem isConnected_tensorProduct_complete_petersen (m : ℕ) :
    IsConnected (complete (m + 3) ⊗g petersen) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) isConnected_petersen
    (not_isBipartite_complete m) (by rw [E_petersen]; omega)

theorem numComponents_tensorProduct_complete_petersen (m : ℕ) :
    (complete (m + 3) ⊗g petersen).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_petersen m)

theorem isConnected_tensorProduct_complete_star (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g star (n + 1)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_star (n + 1))
    (not_isBipartite_complete m) (by rw [E_star]; omega)

theorem numComponents_tensorProduct_complete_star (m n : ℕ) :
    (complete (m + 3) ⊗g star (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_star m n)

theorem isConnected_tensorProduct_petersen_cycle (n : ℕ) :
    IsConnected (petersen ⊗g cycle (n + 3)) :=
  isConnected_tensorProduct isConnected_petersen (isConnected_cycle (n + 2))
    not_isBipartite_petersen (by rw [E_cycle]; omega)

theorem numComponents_tensorProduct_petersen_cycle (n : ℕ) :
    (petersen ⊗g cycle (n + 3)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_petersen_cycle n)

theorem isConnected_tensorProduct_petersen_path (n : ℕ) :
    IsConnected (petersen ⊗g path (n + 2)) :=
  isConnected_tensorProduct isConnected_petersen (isConnected_path (n + 1))
    not_isBipartite_petersen (by rw [E_path]; omega)

theorem numComponents_tensorProduct_petersen_path (n : ℕ) :
    (petersen ⊗g path (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_petersen_path n)

theorem isConnected_tensorProduct_petersen_complete (n : ℕ) :
    IsConnected (petersen ⊗g complete (n + 2)) :=
  isConnected_tensorProduct isConnected_petersen (isConnected_complete (n + 1))
    not_isBipartite_petersen (E_complete_pos n)

theorem numComponents_tensorProduct_petersen_complete (n : ℕ) :
    (petersen ⊗g complete (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_petersen_complete n)

theorem isConnected_tensorProduct_petersen_hypercube (n : ℕ) :
    IsConnected (petersen ⊗g hypercube (n + 1)) :=
  isConnected_tensorProduct isConnected_petersen (isConnected_hypercube (n + 1))
    not_isBipartite_petersen (E_hypercube_pos n)

theorem numComponents_tensorProduct_petersen_hypercube (n : ℕ) :
    (petersen ⊗g hypercube (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_petersen_hypercube n)

theorem isConnected_tensorProduct_petersen_star (n : ℕ) :
    IsConnected (petersen ⊗g star (n + 1)) :=
  isConnected_tensorProduct isConnected_petersen (isConnected_star (n + 1))
    not_isBipartite_petersen (by rw [E_star]; omega)

theorem numComponents_tensorProduct_petersen_star (n : ℕ) :
    (petersen ⊗g star (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_petersen_star n)

theorem isConnected_tensorProduct_petersen_petersen :
    IsConnected (petersen ⊗g petersen) :=
  isConnected_tensorProduct isConnected_petersen isConnected_petersen
    not_isBipartite_petersen (by rw [E_petersen]; omega)

theorem numComponents_tensorProduct_petersen_petersen :
    (petersen ⊗g petersen).numComponents = 1 :=
  numComponents_eq_one_of_isConnected isConnected_tensorProduct_petersen_petersen

/-! ### Triangles in the tensor product

A tensor product of two graphs with a triangle has a triangle, so its girth is three. -/

theorem girth_tensorProduct_complete_wheel (m n : ℕ) :
    (complete (m + 3) ⊗g wheel (n + 4)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_wheel])

theorem girth_tensorProduct_complete_fan (m n : ℕ) :
    (complete (m + 3) ⊗g fan (n + 2)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_fan])

theorem girth_tensorProduct_complete_book (m n : ℕ) :
    (complete (m + 3) ⊗g book (n + 1)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_book]; omega)

theorem girth_tensorProduct_complete_friendship (m n : ℕ) :
    (complete (m + 3) ⊗g friendship (n + 1)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_friendship])

theorem girth_tensorProduct_complete_cocktailParty (m n : ℕ) :
    (complete (m + 3) ⊗g cocktailParty (n + 3)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_cocktailParty]; omega)

theorem girth_tensorProduct_complete_triangular (m n : ℕ) :
    (complete (m + 3) ⊗g triangular (n + 4)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_triangular]; omega)

theorem girth_tensorProduct_wheel_wheel (m n : ℕ) :
    (wheel (m + 4) ⊗g wheel (n + 4)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_wheel]) (by rw [cliqueNum_wheel])

theorem girth_tensorProduct_friendship_friendship (m n : ℕ) :
    (friendship (m + 1) ⊗g friendship (n + 1)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_friendship]) (by rw [cliqueNum_friendship])

/-! ### The strong product of a cycle with a hypercube -/

theorem isConnected_strongProduct_cycle_hypercube (m n : ℕ) :
    IsConnected (cycle (m + 1) ⊠g hypercube n) :=
  isConnected_strongProduct (isConnected_cycle m) (isConnected_hypercube n)

theorem diameter_strongProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 1) ⊠g hypercube n).diameter = max ((m + 1) / 2) n := by
  rw [diameter_strongProduct (isConnected_cycle m) (isConnected_hypercube n), diameter_cycle,
    diameter_hypercube]

theorem radius_strongProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 1) ⊠g hypercube n).radius = max ((m + 1) / 2) n := by
  rw [radius_strongProduct (isConnected_cycle m) (isConnected_hypercube n), radius_cycle,
    radius_hypercube]

theorem maxDeg_strongProduct_cycle_hypercube (m n : ℕ) :
    maxDeg (cycle (m + 3) ⊠g hypercube n) = 3 * n + 2 := by
  have h := maxDeg_strongProduct (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [maxDeg_cycle, maxDeg_hypercube] at h
  omega

theorem minDeg_strongProduct_cycle_hypercube (m n : ℕ) :
    minDeg (cycle (m + 3) ⊠g hypercube n) = 3 * n + 2 := by
  have h := minDeg_strongProduct (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rw [minDeg_cycle, minDeg_hypercube] at h
  omega

theorem isRegularWith_strongProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 3) ⊠g hypercube n).IsRegularWith (3 * n + 2) := by
  have h := (isRegularWith_cycle m).strongProduct (isRegularWith_hypercube n)
  rwa [show (2 + 1) * (n + 1) - 1 = 3 * n + 2 from by omega] at h

theorem girth_strongProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 3) ⊠g hypercube (n + 1)).girth = 3 :=
  girth_strongProduct (by rw [E_cycle]; omega) (E_hypercube_pos n)

theorem chromNum_strongProduct_complete_hypercube (m n : ℕ) :
    (complete m ⊠g hypercube (n + 1)).chromNum = m * 2 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_hypercube n)
  rwa [cliqueNum_complete, cliqueNum_hypercube] at h

theorem chromNum_lexProduct_complete_hypercube (m n : ℕ) :
    (complete m ·g hypercube (n + 1)).chromNum = m * 2 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_hypercube n)
  rwa [cliqueNum_complete, cliqueNum_hypercube] at h

theorem chromNum_strongProduct_cycle_even_hypercube (m n : ℕ) :
    (cycle (2 * m + 4) ⊠g hypercube (n + 1)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_hypercube n)
  rw [cliqueNum_cycle, cliqueNum_hypercube] at h
  omega

theorem chromNum_lexProduct_cycle_even_hypercube (m n : ℕ) :
    (cycle (2 * m + 4) ·g hypercube (n + 1)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_hypercube n)
  rw [cliqueNum_cycle, cliqueNum_hypercube] at h
  omega

/-! ### The strong product of a path with a hypercube -/

theorem isConnected_strongProduct_path_hypercube (m n : ℕ) :
    IsConnected (path (m + 1) ⊠g hypercube n) :=
  isConnected_strongProduct (isConnected_path m) (isConnected_hypercube n)

theorem diameter_strongProduct_path_hypercube (m n : ℕ) :
    (path (m + 1) ⊠g hypercube n).diameter = max m n := by
  rw [diameter_strongProduct (isConnected_path m) (isConnected_hypercube n), diameter_path,
    diameter_hypercube]

theorem radius_strongProduct_path_hypercube (m n : ℕ) :
    (path (m + 1) ⊠g hypercube n).radius = max ((m + 1) / 2) n := by
  rw [radius_strongProduct (isConnected_path m) (isConnected_hypercube n), radius_path,
    radius_hypercube]

theorem maxDeg_strongProduct_path_hypercube (m n : ℕ) :
    maxDeg (path (m + 3) ⊠g hypercube n) = 3 * n + 2 := by
  have h := maxDeg_strongProduct (G := path (m + 3)) (H := hypercube n)
    (by rw [V_path]; omega) (by rw [V_hypercube]; positivity)
  rw [maxDeg_path, maxDeg_hypercube] at h
  omega

theorem minDeg_strongProduct_path_hypercube (m n : ℕ) :
    minDeg (path (m + 2) ⊠g hypercube n) = 2 * n + 1 := by
  have h := minDeg_strongProduct (G := path (m + 2)) (H := hypercube n)
    (by rw [V_path]; omega) (by rw [V_hypercube]; positivity)
  rw [minDeg_path, minDeg_hypercube] at h
  omega

theorem girth_strongProduct_path_hypercube (m n : ℕ) :
    (path (m + 2) ⊠g hypercube (n + 1)).girth = 3 :=
  girth_strongProduct (by rw [E_path]; omega) (E_hypercube_pos n)

theorem chromNum_strongProduct_path_hypercube (m n : ℕ) :
    (path (m + 2) ⊠g hypercube (n + 1)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_path m) (chromNum_eq_cliqueNum_hypercube n)
  rwa [cliqueNum_path, cliqueNum_hypercube] at h

theorem chromNum_lexProduct_path_hypercube (m n : ℕ) :
    (path (m + 2) ·g hypercube (n + 1)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_path m) (chromNum_eq_cliqueNum_hypercube n)
  rwa [cliqueNum_path, cliqueNum_hypercube] at h

/-! ### The lexicographic product of a cycle with a hypercube -/

theorem E_lexProduct_cycle_hypercube (m n : ℕ) :
    2 * (cycle (m + 3) ·g hypercube n).E
      = 2 * (2 ^ n * 2 ^ n * (m + 3)) + (m + 3) * (n * 2 ^ n) := by
  have h := E_hypercube n
  rw [E_lexProduct, V_hypercube, V_cycle, E_cycle,
    show 2 * (2 ^ n * 2 ^ n * (m + 3) + (m + 3) * (hypercube n).E)
      = 2 * (2 ^ n * 2 ^ n * (m + 3)) + (m + 3) * (2 * (hypercube n).E) from by ring, h]

theorem isConnected_lexProduct_cycle_hypercube (m n : ℕ) :
    IsConnected (cycle (m + 1) ·g hypercube n) :=
  isConnected_lexProduct (isConnected_cycle m) (isConnected_hypercube n)

theorem maxDeg_lexProduct_cycle_hypercube (m n : ℕ) :
    maxDeg (cycle (m + 3) ·g hypercube n) = 2 * 2 ^ n + n := by
  have h := maxDeg_lexProduct (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rwa [maxDeg_cycle, maxDeg_hypercube, V_hypercube] at h

theorem minDeg_lexProduct_cycle_hypercube (m n : ℕ) :
    minDeg (cycle (m + 3) ·g hypercube n) = 2 * 2 ^ n + n := by
  have h := minDeg_lexProduct (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rwa [minDeg_cycle, minDeg_hypercube, V_hypercube] at h

theorem isRegularWith_lexProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 3) ·g hypercube n).IsRegularWith (2 * 2 ^ n + n) := by
  have h := (isRegularWith_cycle m).lexProduct (isRegularWith_hypercube n)
  rwa [V_hypercube] at h

theorem girth_lexProduct_cycle_hypercube (m n : ℕ) :
    (cycle (m + 3) ·g hypercube (n + 1)).girth = 3 :=
  girth_lexProduct (by rw [E_cycle]; omega) (E_hypercube_pos n)

/-! ### Domination in a lexicographic product with a dominated right factor -/

theorem domNum_lexProduct_star (G : IsoGraph) (n : ℕ) :
    (G ·g star n).domNum = G.domNum :=
  domNum_lexProduct G (domNum_star n)

theorem domNum_lexProduct_wheel (G : IsoGraph) (n : ℕ) :
    (G ·g wheel n).domNum = G.domNum :=
  domNum_lexProduct G (domNum_wheel n)

theorem domNum_lexProduct_fan (G : IsoGraph) (n : ℕ) :
    (G ·g fan n).domNum = G.domNum :=
  domNum_lexProduct G (domNum_fan n)

theorem domNum_lexProduct_book (G : IsoGraph) (n : ℕ) :
    (G ·g book n).domNum = G.domNum :=
  domNum_lexProduct G (domNum_book n)

theorem domNum_lexProduct_friendship (G : IsoGraph) (n : ℕ) :
    (G ·g friendship n).domNum = G.domNum :=
  domNum_lexProduct G (domNum_friendship n)

/-! ### The join of two hypercubes -/

theorem E_join_hypercube (m n : ℕ) :
    2 * (hypercube m ∇g hypercube n).E = m * 2 ^ m + n * 2 ^ n + 2 * (2 ^ m * 2 ^ n) := by
  have h1 := E_hypercube m
  have h2 := E_hypercube n
  rw [E_join, V_hypercube, V_hypercube,
    show 2 * ((hypercube m).E + (hypercube n).E + 2 ^ m * 2 ^ n)
      = 2 * (hypercube m).E + 2 * (hypercube n).E + 2 * (2 ^ m * 2 ^ n) from by ring, h1, h2]

theorem maxDeg_join_hypercube (m n : ℕ) :
    maxDeg (hypercube m ∇g hypercube n) = max (m + 2 ^ n) (2 ^ m + n) := by
  have h := maxDeg_join (G := hypercube m) (H := hypercube n)
    (by rw [V_hypercube]; positivity) (by rw [V_hypercube]; positivity)
  rwa [maxDeg_hypercube, maxDeg_hypercube, V_hypercube, V_hypercube] at h

theorem minDeg_join_hypercube (m n : ℕ) :
    minDeg (hypercube m ∇g hypercube n) = min (m + 2 ^ n) (2 ^ m + n) := by
  have h := minDeg_join (G := hypercube m) (H := hypercube n)
    (by rw [V_hypercube]; positivity) (by rw [V_hypercube]; positivity)
  rwa [minDeg_hypercube, minDeg_hypercube, V_hypercube, V_hypercube] at h

@[simp] theorem girth_join_hypercube (m n : ℕ) :
    (hypercube (m + 1) ∇g hypercube (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_join, cliqueNum_hypercube, cliqueNum_hypercube]; omega)

/-! ### The disjoint union of two hypercubes -/

theorem E_disjUnion_hypercube (m n : ℕ) :
    2 * (hypercube m ⊕g hypercube n).E = m * 2 ^ m + n * 2 ^ n := by
  have h1 := E_hypercube m
  have h2 := E_hypercube n
  rw [E_disjUnion,
    show 2 * ((hypercube m).E + (hypercube n).E)
      = 2 * (hypercube m).E + 2 * (hypercube n).E from by ring, h1, h2]

theorem edgeChromNum_disjUnion_hypercube (m n : ℕ) :
    (hypercube (m + 1) ⊕g hypercube (n + 1)).edgeChromNum = max (m + 1) (n + 1) := by
  rw [edgeChromNum_disjUnion, edgeChromNum_hypercube, edgeChromNum_hypercube]

theorem minDeg_disjUnion_hypercube (m n : ℕ) :
    minDeg (hypercube m ⊕g hypercube n) = min m n := by
  rw [minDeg_disjUnion (by rw [V_hypercube]; positivity) (by rw [V_hypercube]; positivity),
    minDeg_hypercube, minDeg_hypercube]

theorem not_isConnected_disjUnion_hypercube (m n : ℕ) :
    ¬ IsConnected (hypercube m ⊕g hypercube n) :=
  not_isConnected_disjUnion (by rw [V_hypercube]; positivity)
    (by rw [V_hypercube]; positivity)

/-! ### The join of a complete graph with a hypercube -/

theorem E_join_complete_hypercube (m n : ℕ) :
    2 * (complete m ∇g hypercube n).E = 2 * m.choose 2 + n * 2 ^ n + 2 * (m * 2 ^ n) := by
  have h := E_hypercube n
  rw [E_join, E_complete, V_complete, V_hypercube,
    show 2 * (m.choose 2 + (hypercube n).E + m * 2 ^ n)
      = 2 * m.choose 2 + 2 * (hypercube n).E + 2 * (m * 2 ^ n) from by ring, h]

theorem maxDeg_join_complete_hypercube (m n : ℕ) :
    maxDeg (complete (m + 1) ∇g hypercube n) = max (m + 2 ^ n) (m + 1 + n) := by
  have h := maxDeg_join (G := complete (m + 1)) (H := hypercube n)
    (by rw [V_complete]; omega) (by rw [V_hypercube]; positivity)
  rw [maxDeg_complete, maxDeg_hypercube, V_complete, V_hypercube] at h
  simpa using h

theorem minDeg_join_complete_hypercube (m n : ℕ) :
    minDeg (complete (m + 1) ∇g hypercube n) = min (m + 2 ^ n) (m + 1 + n) := by
  have h := minDeg_join (G := complete (m + 1)) (H := hypercube n)
    (by rw [V_complete]; omega) (by rw [V_hypercube]; positivity)
  rw [minDeg_complete, minDeg_hypercube, V_complete, V_hypercube] at h
  simpa using h

@[simp] theorem girth_join_complete_hypercube (m n : ℕ) :
    (complete (m + 1) ∇g hypercube (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_join, cliqueNum_complete, cliqueNum_hypercube]; omega)

/-! ### The join of a cycle with a hypercube -/

theorem E_join_cycle_hypercube (m n : ℕ) :
    2 * (cycle (m + 3) ∇g hypercube n).E
      = 2 * (m + 3) + n * 2 ^ n + 2 * ((m + 3) * 2 ^ n) := by
  have h := E_hypercube n
  rw [E_join, E_cycle, V_cycle, V_hypercube,
    show 2 * ((m + 3) + (hypercube n).E + (m + 3) * 2 ^ n)
      = 2 * (m + 3) + 2 * (hypercube n).E + 2 * ((m + 3) * 2 ^ n) from by ring, h]

theorem maxDeg_join_cycle_hypercube (m n : ℕ) :
    maxDeg (cycle (m + 3) ∇g hypercube n) = max (2 + 2 ^ n) (m + 3 + n) := by
  have h := maxDeg_join (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rwa [maxDeg_cycle, maxDeg_hypercube, V_cycle, V_hypercube] at h

theorem minDeg_join_cycle_hypercube (m n : ℕ) :
    minDeg (cycle (m + 3) ∇g hypercube n) = min (2 + 2 ^ n) (m + 3 + n) := by
  have h := minDeg_join (G := cycle (m + 3)) (H := hypercube n)
    (by rw [V_cycle]; omega) (by rw [V_hypercube]; positivity)
  rwa [minDeg_cycle, minDeg_hypercube, V_cycle, V_hypercube] at h

@[simp] theorem girth_join_cycle_hypercube (m n : ℕ) :
    (cycle (m + 4) ∇g hypercube (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_hypercube]; omega)

theorem diameter_join_cycle_hypercube (m n : ℕ) :
    (cycle (m + 4) ∇g hypercube n).diameter = 2 := by
  have h : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
    rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 by omega]
  have h2 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 4) * (m + 3) = m * m + 7 * m + 12 := by ring
    omega
  refine diameter_join_left (by rw [V_hypercube]; positivity) ?_
  rw [E_cycle, V_cycle, h]
  omega

/-! ### The disjoint union of a hypercube with a complete graph -/

theorem E_disjUnion_hypercube_complete (m n : ℕ) :
    2 * (hypercube m ⊕g complete n).E = m * 2 ^ m + 2 * n.choose 2 := by
  have h := E_hypercube m
  rw [E_disjUnion, E_complete,
    show 2 * ((hypercube m).E + n.choose 2) = 2 * (hypercube m).E + 2 * n.choose 2 from by ring, h]

theorem minDeg_disjUnion_hypercube_complete (m n : ℕ) :
    minDeg (hypercube m ⊕g complete (n + 1)) = min m n := by
  have h := minDeg_disjUnion (G := hypercube m) (H := complete (n + 1))
    (by rw [V_hypercube]; positivity) (by rw [V_complete]; omega)
  rw [minDeg_hypercube, minDeg_complete] at h
  simpa using h

theorem not_isConnected_disjUnion_hypercube_complete (m n : ℕ) :
    ¬ IsConnected (hypercube m ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_hypercube]; positivity) (by rw [V_complete]; omega)

/-! ### The Mycielskian of a hypercube -/

theorem E_mycielskian_hypercube (n : ℕ) :
    2 * (mycielskian (hypercube n)).E = 3 * (n * 2 ^ n) + 2 * 2 ^ n := by
  have h := E_hypercube n
  rw [E_mycielskian, V_hypercube,
    show 2 * (3 * (hypercube n).E + 2 ^ n) = 3 * (2 * (hypercube n).E) + 2 * 2 ^ n from by ring, h]

theorem cliqueNum_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (hypercube (n + 1)) (by rw [V_hypercube]; positivity)
  rw [cliqueNum_hypercube] at h
  omega

theorem maxDeg_mycielskian_hypercube (n : ℕ) :
    maxDeg (mycielskian (hypercube n)) = max (2 * n) (2 ^ n) := by
  have h := maxDeg_mycielskian (hypercube n)
  rwa [maxDeg_hypercube, V_hypercube] at h

theorem minDeg_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).minDeg = min (n + 2) (2 ^ (n + 1)) := by
  have h := minDeg_mycielskian (hypercube (n + 1)) (by rw [V_hypercube]; positivity)
  rwa [minDeg_hypercube, V_hypercube,
    show min (2 * (n + 1)) (n + 1 + 1) = n + 2 from by omega] at h

theorem isConnected_mycielskian_hypercube (n : ℕ) :
    IsConnected (mycielskian (hypercube (n + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_hypercube]; omega)

theorem numComponents_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_hypercube]; omega)

theorem radius_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_hypercube]; omega)

theorem four_le_girth_mycielskian_hypercube (n : ℕ) :
    4 ≤ (mycielskian (hypercube (n + 1))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_hypercube]) (E_hypercube_pos n)

theorem matchNum_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).matchNum = 2 ^ (n + 1) := by
  have h := matchNum_mycielskian (G := hypercube (n + 1))
    (by rw [matchNum_hypercube, V_hypercube]; ring)
  rwa [V_hypercube] at h

theorem cliqueCoverNum_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).cliqueCoverNum = 2 ^ (n + 1) + 1 := by
  have h := cliqueCoverNum_mycielskian (hypercube (n + 1)) (by rw [V_hypercube]; positivity)
    (by rw [cliqueNum_hypercube]) (by rw [matchNum_hypercube, V_hypercube]; ring)
  rwa [V_hypercube] at h

/-! ### The Mycielskian of the Petersen graph -/

@[simp] theorem V_mycielskian_petersen : (mycielskian petersen).V = 21 := by
  rw [V_mycielskian, V_petersen]

@[simp] theorem E_mycielskian_petersen : (mycielskian petersen).E = 55 := by
  rw [E_mycielskian, E_petersen, V_petersen]

theorem cliqueNum_mycielskian_petersen : (mycielskian petersen).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian petersen (by rw [V_petersen]; omega)
  rw [cliqueNum_petersen] at h
  omega

theorem maxDeg_mycielskian_petersen : maxDeg (mycielskian petersen) = 10 := by
  have h := maxDeg_mycielskian petersen
  rw [maxDeg_petersen, V_petersen] at h
  omega

theorem minDeg_mycielskian_petersen : (mycielskian petersen).minDeg = 4 := by
  have h := minDeg_mycielskian petersen (by rw [V_petersen]; omega)
  rw [minDeg_petersen, V_petersen] at h
  omega

theorem domNum_mycielskian_petersen : (mycielskian petersen).domNum = 4 := by
  have h := domNum_mycielskian petersen (by rw [V_petersen]; omega)
  rw [domNum_petersen] at h
  omega

theorem isConnected_mycielskian_petersen : IsConnected (mycielskian petersen) :=
  isConnected_mycielskian _ (by rw [minDeg_petersen]; omega)

theorem numComponents_mycielskian_petersen : (mycielskian petersen).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_petersen]; omega)

theorem radius_mycielskian_petersen : (mycielskian petersen).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_petersen]; omega)

theorem four_le_girth_mycielskian_petersen : 4 ≤ (mycielskian petersen).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_petersen]) (by rw [E_petersen]; omega)

theorem matchNum_mycielskian_petersen : (mycielskian petersen).matchNum = 10 := by
  have h := matchNum_mycielskian (G := petersen) (by rw [matchNum_petersen, V_petersen])
  rwa [V_petersen] at h

theorem cliqueCoverNum_mycielskian_petersen : (mycielskian petersen).cliqueCoverNum = 11 := by
  have h := cliqueCoverNum_mycielskian petersen (by rw [V_petersen]; omega)
    (by rw [cliqueNum_petersen]) (by rw [matchNum_petersen, V_petersen])
  rw [V_petersen] at h
  omega

/-! ### The Mycielskian of a star -/

@[simp] theorem V_mycielskian_star (n : ℕ) : (mycielskian (star n)).V = 2 * n + 3 := by
  rw [V_mycielskian, V_star]
  omega

theorem E_mycielskian_star (n : ℕ) : (mycielskian (star n)).E = 4 * n + 1 := by
  rw [E_mycielskian, E_star, V_star]
  omega

theorem cliqueNum_mycielskian_star (n : ℕ) :
    (mycielskian (star (n + 1))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (star (n + 1)) (by rw [V_star]; omega)
  rw [cliqueNum_star] at h
  omega

theorem maxDeg_mycielskian_star (n : ℕ) :
    maxDeg (mycielskian (star (n + 1))) = 2 * n + 2 := by
  have h := maxDeg_mycielskian (star (n + 1))
  rw [maxDeg_star, V_star] at h
  omega

theorem minDeg_mycielskian_star (n : ℕ) :
    (mycielskian (star (n + 1))).minDeg = 2 := by
  have h := minDeg_mycielskian (star (n + 1)) (by rw [V_star]; omega)
  rw [minDeg_star, V_star] at h
  omega

theorem domNum_mycielskian_star (n : ℕ) :
    (mycielskian (star (n + 1))).domNum = 2 := by
  have h := domNum_mycielskian (star (n + 1)) (by rw [V_star]; omega)
  rw [domNum_star] at h
  omega

theorem isConnected_mycielskian_star (n : ℕ) :
    IsConnected (mycielskian (star (n + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_star]; omega)

theorem numComponents_mycielskian_star (n : ℕ) :
    (mycielskian (star (n + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_star]; omega)

theorem radius_mycielskian_star (n : ℕ) : (mycielskian (star (n + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_star]; omega)

theorem four_le_girth_mycielskian_star (n : ℕ) :
    4 ≤ (mycielskian (star (n + 1))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_star]) (by rw [E_star]; omega)

/-! ### The Mycielskian of a complete bipartite graph -/

theorem cliqueNum_mycielskian_bipartite (m n : ℕ) :
    (mycielskian (bipartite (m + 1) (n + 1))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (bipartite (m + 1) (n + 1)) (by rw [V_bipartite]; omega)
  rw [cliqueNum_bipartite] at h
  omega

theorem maxDeg_mycielskian_bipartite (m n : ℕ) :
    maxDeg (mycielskian (bipartite (m + 1) (n + 1)))
      = max (2 * max (m + 1) (n + 1)) (m + n + 2) := by
  have h := maxDeg_mycielskian (bipartite (m + 1) (n + 1))
  rwa [maxDeg_bipartite, V_bipartite, show m + 1 + (n + 1) = m + n + 2 from by omega] at h

theorem minDeg_mycielskian_bipartite (m n : ℕ) :
    (mycielskian (bipartite (m + 2) (n + 2))).minDeg = min (m + 2) (n + 2) + 1 := by
  have h := minDeg_mycielskian (bipartite (m + 2) (n + 2)) (by rw [V_bipartite]; omega)
  rw [minDeg_bipartite, V_bipartite] at h
  omega

theorem domNum_mycielskian_bipartite (m n : ℕ) :
    (mycielskian (bipartite (m + 2) (n + 2))).domNum = 3 := by
  have h := domNum_mycielskian (bipartite (m + 2) (n + 2)) (by rw [V_bipartite]; omega)
  rw [domNum_bipartite] at h
  omega

theorem isConnected_mycielskian_bipartite (m n : ℕ) :
    IsConnected (mycielskian (bipartite (m + 1) (n + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_bipartite]; omega)

theorem numComponents_mycielskian_bipartite (m n : ℕ) :
    (mycielskian (bipartite (m + 1) (n + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_bipartite]; omega)

theorem radius_mycielskian_bipartite (m n : ℕ) :
    (mycielskian (bipartite (m + 1) (n + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_bipartite]; omega)

theorem two_le_diameter_mycielskian_bipartite (m n : ℕ) :
    2 ≤ (mycielskian (bipartite (m + 1) (n + 1))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_bipartite]; omega)

theorem diameter_mycielskian_bipartite_le_four (m n : ℕ) :
    (mycielskian (bipartite (m + 1) (n + 1))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_bipartite]; omega)

theorem four_le_girth_mycielskian_bipartite (m n : ℕ) :
    4 ≤ (mycielskian (bipartite (m + 1) (n + 1))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_bipartite]) (by rw [E_bipartite]; positivity)

theorem matchNum_mycielskian_bipartite (n : ℕ) :
    (mycielskian (bipartite (n + 1) (n + 1))).matchNum = 2 * n + 2 := by
  have h := matchNum_mycielskian (G := bipartite (n + 1) (n + 1))
    (by rw [matchNum_bipartite, V_bipartite]; omega)
  rw [V_bipartite] at h
  omega

theorem cliqueCoverNum_mycielskian_bipartite (n : ℕ) :
    (mycielskian (bipartite (n + 1) (n + 1))).cliqueCoverNum = 2 * n + 3 := by
  have h := cliqueCoverNum_mycielskian (bipartite (n + 1) (n + 1)) (by rw [V_bipartite]; omega)
    (by rw [cliqueNum_bipartite]) (by rw [matchNum_bipartite, V_bipartite]; omega)
  rw [V_bipartite] at h
  omega

theorem indepNum_mycielskian_bipartite_le (m n : ℕ) :
    (mycielskian (bipartite (m + 1) (n + 1))).indepNum ≤ m + n + 2 + max (m + 1) (n + 1) := by
  have h := indepNum_mycielskian_le (bipartite (m + 1) (n + 1)) (by rw [V_bipartite]; omega)
  rw [V_bipartite, indepNum_bipartite] at h
  omega

theorem coverNum_mycielskian_bipartite_le (m n : ℕ) :
    (mycielskian (bipartite m n)).coverNum ≤ m + n + 1 := by
  have h := coverNum_mycielskian_le (bipartite m n)
  rwa [V_bipartite] at h

/-! ### The Mycielskian of a cocktail party graph -/

@[simp] theorem V_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty n)).V = 4 * n + 1 := by
  rw [V_mycielskian, V_cocktailParty]
  omega

theorem E_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 1))).E = 6 * n * n + 8 * n + 2 := by
  rw [E_mycielskian, E_cocktailParty, V_cocktailParty,
    show 2 * (n + 1) - 2 = 2 * n from by omega]
  ring

theorem cliqueNum_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).cliqueNum = n + 2 := by
  have h := cliqueNum_mycielskian (cocktailParty (n + 2)) (by rw [V_cocktailParty]; omega)
  rw [cliqueNum_cocktailParty] at h
  omega

theorem maxDeg_mycielskian_cocktailParty (n : ℕ) :
    maxDeg (mycielskian (cocktailParty (n + 1))) = max (4 * n) (2 * n + 2) := by
  have h := maxDeg_mycielskian (cocktailParty (n + 1))
  rw [maxDeg_cocktailParty, V_cocktailParty] at h
  omega

theorem minDeg_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).minDeg = 2 * n + 3 := by
  have h := minDeg_mycielskian (cocktailParty (n + 2)) (by rw [V_cocktailParty]; omega)
  rw [minDeg_cocktailParty, V_cocktailParty] at h
  omega

theorem domNum_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).domNum = 3 := by
  have h := domNum_mycielskian (cocktailParty (n + 2)) (by rw [V_cocktailParty]; omega)
  rw [domNum_cocktailParty] at h
  omega

theorem isConnected_mycielskian_cocktailParty (n : ℕ) :
    IsConnected (mycielskian (cocktailParty (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_cocktailParty]; omega)

theorem numComponents_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_cocktailParty]; omega)

theorem radius_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_cocktailParty]; omega)

theorem two_le_diameter_mycielskian_cocktailParty (n : ℕ) :
    2 ≤ (mycielskian (cocktailParty (n + 2))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_cocktailParty]; omega)

theorem diameter_mycielskian_cocktailParty_le_four (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_cocktailParty]; omega)

theorem girth_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 3))).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_mycielskian_cocktailParty]; omega)

theorem matchNum_mycielskian_cocktailParty (n : ℕ) :
    (mycielskian (cocktailParty (n + 2))).matchNum = 2 * n + 4 := by
  have h := matchNum_mycielskian (G := cocktailParty (n + 2))
    (by rw [matchNum_cocktailParty, V_cocktailParty])
  rw [V_cocktailParty] at h
  omega

theorem indepNum_mycielskian_cocktailParty_le (n : ℕ) :
    (mycielskian (cocktailParty (n + 1))).indepNum ≤ 2 * n + 4 := by
  have h := indepNum_mycielskian_le (cocktailParty (n + 1)) (by rw [V_cocktailParty]; omega)
  rw [V_cocktailParty, indepNum_cocktailParty] at h
  omega

theorem coverNum_mycielskian_cocktailParty_le (n : ℕ) :
    (mycielskian (cocktailParty n)).coverNum ≤ 2 * n + 1 := by
  have h := coverNum_mycielskian_le (cocktailParty n)
  rwa [V_cocktailParty] at h

/-! ### The Mycielskian of a wheel -/

@[simp] theorem V_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel n)).V = 2 * n + 3 := by
  rw [V_mycielskian, V_wheel]
  omega

theorem E_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 3))).E = 7 * n + 22 := by
  rw [E_mycielskian, E_wheel, V_wheel]
  omega

theorem cliqueNum_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 4))).cliqueNum = 3 := by
  have h := cliqueNum_mycielskian (wheel (n + 4)) (by rw [V_wheel]; omega)
  rw [cliqueNum_wheel] at h
  omega

theorem maxDeg_mycielskian_wheel (n : ℕ) :
    maxDeg (mycielskian (wheel (n + 3))) = 2 * n + 6 := by
  have h := maxDeg_mycielskian (wheel (n + 3))
  rw [maxDeg_wheel, V_wheel] at h
  omega

theorem minDeg_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 3))).minDeg = 4 := by
  have h := minDeg_mycielskian (wheel (n + 3)) (by rw [V_wheel]; omega)
  rw [minDeg_wheel, V_wheel] at h
  omega

theorem domNum_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 1))).domNum = 2 := by
  have h := domNum_mycielskian (wheel (n + 1)) (by rw [V_wheel]; omega)
  rw [domNum_wheel] at h
  omega

theorem isConnected_mycielskian_wheel (n : ℕ) :
    IsConnected (mycielskian (wheel (n + 3))) :=
  isConnected_mycielskian _ (by rw [minDeg_wheel]; omega)

theorem numComponents_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 3))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_wheel]; omega)

theorem radius_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 3))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_wheel]; omega)

theorem two_le_diameter_mycielskian_wheel (n : ℕ) :
    2 ≤ (mycielskian (wheel (n + 3))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_wheel]; omega)

theorem diameter_mycielskian_wheel_le_four (n : ℕ) :
    (mycielskian (wheel (n + 3))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_wheel]; omega)

theorem girth_mycielskian_wheel (n : ℕ) :
    (mycielskian (wheel (n + 4))).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_mycielskian_wheel])

theorem matchNum_mycielskian_wheel (m : ℕ) :
    (mycielskian (wheel (2 * m + 3))).matchNum = 2 * m + 4 := by
  have h := matchNum_mycielskian (G := wheel (2 * m + 3))
    (by rw [matchNum_wheel, V_wheel]; omega)
  rw [V_wheel] at h
  omega

theorem indepNum_mycielskian_wheel_le (n : ℕ) :
    (mycielskian (wheel (n + 3))).indepNum ≤ n + 4 + (n + 3) / 2 := by
  have h := indepNum_mycielskian_le (wheel (n + 3)) (by rw [V_wheel]; omega)
  rw [V_wheel, indepNum_wheel] at h
  omega

theorem coverNum_mycielskian_wheel_le (n : ℕ) :
    (mycielskian (wheel n)).coverNum ≤ n + 2 := by
  have h := coverNum_mycielskian_le (wheel n)
  rwa [V_wheel, show 1 + n + 1 = n + 2 from by omega] at h

/-! ### The Mycielskian of a fan -/

@[simp] theorem V_mycielskian_fan (n : ℕ) : (mycielskian (fan n)).V = 2 * n + 3 := by
  rw [V_mycielskian, V_fan]
  omega

theorem E_mycielskian_fan (n : ℕ) : (mycielskian (fan (n + 1))).E = 7 * n + 5 := by
  rw [E_mycielskian, E_fan, V_fan]
  omega

theorem cliqueNum_mycielskian_fan (n : ℕ) :
    (mycielskian (fan (n + 2))).cliqueNum = 3 := by
  have h := cliqueNum_mycielskian (fan (n + 2)) (by rw [V_fan]; omega)
  rw [cliqueNum_fan] at h
  omega

theorem maxDeg_mycielskian_fan (n : ℕ) :
    maxDeg (mycielskian (fan (n + 3))) = 2 * n + 6 := by
  have h := maxDeg_mycielskian (fan (n + 3))
  rw [maxDeg_fan, V_fan] at h
  omega

theorem minDeg_mycielskian_fan (n : ℕ) :
    (mycielskian (fan (n + 2))).minDeg = 3 := by
  have h := minDeg_mycielskian (fan (n + 2)) (by rw [V_fan]; omega)
  rw [minDeg_fan, V_fan] at h
  omega

theorem domNum_mycielskian_fan (n : ℕ) :
    (mycielskian (fan n)).domNum = 2 := by
  have h := domNum_mycielskian (fan n) (by rw [V_fan]; omega)
  rw [domNum_fan] at h
  omega

theorem isConnected_mycielskian_fan (n : ℕ) :
    IsConnected (mycielskian (fan (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_fan]; omega)

theorem numComponents_mycielskian_fan (n : ℕ) :
    (mycielskian (fan (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_fan]; omega)

theorem radius_mycielskian_fan (n : ℕ) :
    (mycielskian (fan (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_fan]; omega)

theorem two_le_diameter_mycielskian_fan (n : ℕ) :
    2 ≤ (mycielskian (fan (n + 2))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_fan]; omega)

theorem diameter_mycielskian_fan_le_four (n : ℕ) :
    (mycielskian (fan (n + 2))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_fan]; omega)

theorem girth_mycielskian_fan (n : ℕ) :
    (mycielskian (fan (n + 2))).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_mycielskian_fan])

theorem matchNum_mycielskian_fan (m : ℕ) :
    (mycielskian (fan (2 * m + 1))).matchNum = 2 * m + 2 := by
  have h := matchNum_mycielskian (G := fan (2 * m + 1)) (by rw [matchNum_fan, V_fan]; omega)
  rw [V_fan] at h
  omega

theorem indepNum_mycielskian_fan_le (n : ℕ) :
    (mycielskian (fan (n + 1))).indepNum ≤ n + 2 + (n + 2) / 2 := by
  have h := indepNum_mycielskian_le (fan (n + 1)) (by rw [V_fan]; omega)
  rw [V_fan, indepNum_fan] at h
  omega

theorem coverNum_mycielskian_fan_le (n : ℕ) :
    (mycielskian (fan n)).coverNum ≤ n + 2 := by
  have h := coverNum_mycielskian_le (fan n)
  rwa [V_fan, show 1 + n + 1 = n + 2 from by omega] at h

/-! ### The Mycielskian of a book -/

@[simp] theorem V_mycielskian_book (n : ℕ) : (mycielskian (book n)).V = 2 * n + 5 := by
  rw [V_mycielskian, V_book]
  omega

theorem E_mycielskian_book (n : ℕ) : (mycielskian (book n)).E = 7 * n + 5 := by
  rw [E_mycielskian, E_book, V_book]
  omega

theorem cliqueNum_mycielskian_book (n : ℕ) :
    (mycielskian (book (n + 1))).cliqueNum = 3 := by
  have h := cliqueNum_mycielskian (book (n + 1)) (by rw [V_book]; omega)
  rw [cliqueNum_book] at h
  omega

theorem maxDeg_mycielskian_book (n : ℕ) :
    maxDeg (mycielskian (book (n + 1))) = 2 * n + 4 := by
  have h := maxDeg_mycielskian (book (n + 1))
  rw [maxDeg_book, V_book] at h
  omega

theorem minDeg_mycielskian_book (n : ℕ) :
    (mycielskian (book (n + 1))).minDeg = 3 := by
  have h := minDeg_mycielskian (book (n + 1)) (by rw [V_book]; omega)
  rw [minDeg_book, V_book] at h
  omega

theorem domNum_mycielskian_book (n : ℕ) :
    (mycielskian (book n)).domNum = 2 := by
  have h := domNum_mycielskian (book n) (by rw [V_book]; omega)
  rw [domNum_book] at h
  omega

theorem isConnected_mycielskian_book (n : ℕ) :
    IsConnected (mycielskian (book (n + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_book]; omega)

theorem numComponents_mycielskian_book (n : ℕ) :
    (mycielskian (book (n + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_book]; omega)

theorem radius_mycielskian_book (n : ℕ) :
    (mycielskian (book (n + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_book]; omega)

theorem two_le_diameter_mycielskian_book (n : ℕ) :
    2 ≤ (mycielskian (book (n + 1))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_book]; omega)

theorem diameter_mycielskian_book_le_four (n : ℕ) :
    (mycielskian (book (n + 1))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_book]; omega)

theorem girth_mycielskian_book (n : ℕ) :
    (mycielskian (book (n + 1))).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_mycielskian_book])

theorem indepNum_mycielskian_book_le (n : ℕ) :
    (mycielskian (book n)).indepNum ≤ 2 + n + max 1 n := by
  have h := indepNum_mycielskian_le (book n) (by rw [V_book]; omega)
  rw [V_book, indepNum_book] at h
  omega

theorem coverNum_mycielskian_book_le (n : ℕ) :
    (mycielskian (book n)).coverNum ≤ n + 3 := by
  have h := coverNum_mycielskian_le (book n)
  rwa [V_book, show 2 + n + 1 = n + 3 from by omega] at h

/-! ### The Mycielskian of a friendship graph -/

@[simp] theorem V_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship n)).V = 4 * n + 3 := by
  rw [V_mycielskian, V_friendship]
  omega

theorem E_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship n)).E = 11 * n + 1 := by
  rw [E_mycielskian, E_friendship, V_friendship]
  omega

theorem chromNum_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship (n + 1))).chromNum = 4 := by
  rw [chromNum_mycielskian, chromNum_friendship]

theorem cliqueNum_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship (n + 1))).cliqueNum = 3 := by
  have h := cliqueNum_mycielskian (friendship (n + 1)) (by rw [V_friendship]; omega)
  rw [cliqueNum_friendship] at h
  omega

theorem maxDeg_mycielskian_friendship (n : ℕ) :
    maxDeg (mycielskian (friendship (n + 1))) = 4 * n + 4 := by
  have h := maxDeg_mycielskian (friendship (n + 1))
  rw [maxDeg_friendship, V_friendship] at h
  omega

theorem minDeg_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship (n + 1))).minDeg = 3 := by
  have h := minDeg_mycielskian (friendship (n + 1)) (by rw [V_friendship]; omega)
  rw [minDeg_friendship, V_friendship] at h
  omega

theorem domNum_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship n)).domNum = 2 := by
  have h := domNum_mycielskian (friendship n) (by rw [V_friendship]; omega)
  rw [domNum_friendship] at h
  omega

theorem isConnected_mycielskian_friendship (n : ℕ) :
    IsConnected (mycielskian (friendship (n + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_friendship]; omega)

theorem numComponents_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship (n + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_friendship]; omega)

theorem radius_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship (n + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_friendship]; omega)

theorem two_le_diameter_mycielskian_friendship (n : ℕ) :
    2 ≤ (mycielskian (friendship (n + 1))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_friendship]; omega)

theorem diameter_mycielskian_friendship_le_four (n : ℕ) :
    (mycielskian (friendship (n + 1))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_friendship]; omega)

theorem girth_mycielskian_friendship (n : ℕ) :
    (mycielskian (friendship (n + 1))).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_mycielskian_friendship])

theorem indepNum_mycielskian_friendship_le (n : ℕ) :
    (mycielskian (friendship n)).indepNum ≤ 2 * n + 1 + max n 1 := by
  have h := indepNum_mycielskian_le (friendship n) (by rw [V_friendship]; omega)
  rw [V_friendship, indepNum_friendship] at h
  omega

theorem coverNum_mycielskian_friendship_le (n : ℕ) :
    (mycielskian (friendship n)).coverNum ≤ 2 * n + 2 := by
  have h := coverNum_mycielskian_le (friendship n)
  rwa [V_friendship, show 2 * n + 1 + 1 = 2 * n + 2 from by omega] at h

/-! ### The Mycielskian of a ladder -/

@[simp] theorem V_mycielskian_ladder (n : ℕ) : (mycielskian (ladder n)).V = 4 * n + 1 := by
  rw [V_mycielskian, V_ladder]
  omega

theorem E_mycielskian_ladder (n : ℕ) : (mycielskian (ladder (n + 1))).E = 11 * n + 5 := by
  rw [E_mycielskian, E_ladder, V_ladder]
  omega

theorem cliqueNum_mycielskian_ladder (n : ℕ) :
    (mycielskian (ladder (n + 2))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (ladder (n + 2)) (by rw [V_ladder]; omega)
  rw [cliqueNum_ladder] at h
  omega

theorem maxDeg_mycielskian_ladder (n : ℕ) :
    maxDeg (mycielskian (ladder (n + 3))) = 2 * n + 6 := by
  have h := maxDeg_mycielskian (ladder (n + 3))
  rw [maxDeg_ladder, V_ladder] at h
  omega

theorem minDeg_mycielskian_ladder (n : ℕ) :
    (mycielskian (ladder (n + 2))).minDeg = 3 := by
  have h := minDeg_mycielskian (ladder (n + 2)) (by rw [V_ladder]; omega)
  rw [minDeg_ladder, V_ladder] at h
  omega

theorem isConnected_mycielskian_ladder (n : ℕ) :
    IsConnected (mycielskian (ladder (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_ladder]; omega)

theorem numComponents_mycielskian_ladder (n : ℕ) :
    (mycielskian (ladder (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_ladder]; omega)

theorem radius_mycielskian_ladder (n : ℕ) :
    (mycielskian (ladder (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_ladder]; omega)

theorem two_le_diameter_mycielskian_ladder (n : ℕ) :
    2 ≤ (mycielskian (ladder (n + 2))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_ladder]; omega)

theorem diameter_mycielskian_ladder_le_four (n : ℕ) :
    (mycielskian (ladder (n + 2))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_ladder]; omega)

theorem four_le_girth_mycielskian_ladder (n : ℕ) :
    4 ≤ (mycielskian (ladder (n + 2))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_ladder]) (by rw [E_ladder]; omega)

theorem matchNum_mycielskian_ladder (n : ℕ) :
    (mycielskian (ladder n)).matchNum = 2 * n := by
  have h := matchNum_mycielskian (G := ladder n) (by rw [matchNum_ladder, V_ladder]; omega)
  rw [V_ladder] at h
  omega

theorem cliqueCoverNum_mycielskian_ladder (n : ℕ) :
    (mycielskian (ladder (n + 2))).cliqueCoverNum = 2 * n + 5 := by
  have h := cliqueCoverNum_mycielskian (ladder (n + 2)) (by rw [V_ladder]; omega)
    (by rw [cliqueNum_ladder]) (by rw [matchNum_ladder, V_ladder]; omega)
  rw [V_ladder] at h
  omega

theorem indepNum_mycielskian_ladder_le (n : ℕ) :
    (mycielskian (ladder (n + 1))).indepNum ≤ 3 * n + 3 := by
  have h := indepNum_mycielskian_le (ladder (n + 1)) (by rw [V_ladder]; omega)
  rw [V_ladder, indepNum_ladder] at h
  omega

theorem coverNum_mycielskian_ladder_le (n : ℕ) :
    (mycielskian (ladder n)).coverNum ≤ 2 * n + 1 := by
  have h := coverNum_mycielskian_le (ladder n)
  rw [V_ladder] at h
  omega

/-! ### The Mycielskian of a prism -/

@[simp] theorem V_mycielskian_prism (n : ℕ) : (mycielskian (prism n)).V = 4 * n + 1 := by
  rw [V_mycielskian, V_prism]
  omega

theorem E_mycielskian_prism (n : ℕ) : (mycielskian (prism (n + 3))).E = 11 * n + 33 := by
  rw [E_mycielskian, E_prism, V_prism]
  omega

theorem cliqueNum_mycielskian_prism (n : ℕ) :
    (mycielskian (prism (n + 4))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (prism (n + 4)) (by rw [V_prism]; omega)
  rw [cliqueNum_prism] at h
  omega

theorem maxDeg_mycielskian_prism (n : ℕ) :
    maxDeg (mycielskian (prism (n + 3))) = 2 * n + 6 := by
  have h := maxDeg_mycielskian (prism (n + 3))
  rw [maxDeg_prism, V_prism] at h
  omega

theorem minDeg_mycielskian_prism (n : ℕ) :
    (mycielskian (prism (n + 3))).minDeg = 4 := by
  have h := minDeg_mycielskian (prism (n + 3)) (by rw [V_prism]; omega)
  rw [minDeg_prism, V_prism] at h
  omega

theorem isConnected_mycielskian_prism (n : ℕ) :
    IsConnected (mycielskian (prism (n + 3))) :=
  isConnected_mycielskian _ (by rw [minDeg_prism]; omega)

theorem numComponents_mycielskian_prism (n : ℕ) :
    (mycielskian (prism (n + 3))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_prism]; omega)

theorem radius_mycielskian_prism (n : ℕ) :
    (mycielskian (prism (n + 3))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_prism]; omega)

theorem two_le_diameter_mycielskian_prism (n : ℕ) :
    2 ≤ (mycielskian (prism (n + 3))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_prism]; omega)

theorem diameter_mycielskian_prism_le_four (n : ℕ) :
    (mycielskian (prism (n + 3))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_prism]; omega)

theorem four_le_girth_mycielskian_prism (n : ℕ) :
    4 ≤ (mycielskian (prism (n + 4))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_prism]) (by rw [E_prism]; omega)

theorem matchNum_mycielskian_prism (n : ℕ) :
    (mycielskian (prism n)).matchNum = 2 * n := by
  have h := matchNum_mycielskian (G := prism n) (by rw [matchNum_prism, V_prism]; omega)
  rw [V_prism] at h
  omega

theorem cliqueCoverNum_mycielskian_prism (n : ℕ) :
    (mycielskian (prism (n + 4))).cliqueCoverNum = 2 * n + 9 := by
  have h := cliqueCoverNum_mycielskian (prism (n + 4)) (by rw [V_prism]; omega)
    (by rw [cliqueNum_prism]) (by rw [matchNum_prism, V_prism]; omega)
  rw [V_prism] at h
  omega

theorem coverNum_mycielskian_prism_le (n : ℕ) :
    (mycielskian (prism n)).coverNum ≤ 2 * n + 1 := by
  have h := coverNum_mycielskian_le (prism n)
  rw [V_prism] at h
  omega

/-! ### The Mycielskian of a crown graph -/

@[simp] theorem V_mycielskian_crown (n : ℕ) : (mycielskian (crown n)).V = 4 * n + 1 := by
  rw [V_mycielskian, V_crown]
  omega

theorem E_mycielskian_crown (n : ℕ) :
    (mycielskian (crown n)).E = 6 * n.choose 2 + 2 * n := by
  rw [E_mycielskian, E_crown, V_crown]
  omega

theorem cliqueNum_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (crown (n + 2)) (by rw [V_crown]; omega)
  rw [cliqueNum_crown] at h
  omega

theorem maxDeg_mycielskian_crown (n : ℕ) :
    maxDeg (mycielskian (crown (n + 2))) = 2 * n + 4 := by
  have h := maxDeg_mycielskian (crown (n + 2))
  rw [maxDeg_crown, V_crown] at h
  omega

theorem minDeg_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).minDeg = n + 2 := by
  have h := minDeg_mycielskian (crown (n + 2)) (by rw [V_crown]; omega)
  rw [minDeg_crown, V_crown] at h
  omega

theorem domNum_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).domNum = 3 := by
  have h := domNum_mycielskian (crown (n + 2)) (by rw [V_crown]; omega)
  rw [domNum_crown] at h
  omega

theorem isConnected_mycielskian_crown (n : ℕ) :
    IsConnected (mycielskian (crown (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_crown]; omega)

theorem numComponents_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_crown]; omega)

theorem radius_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_crown]; omega)

theorem two_le_diameter_mycielskian_crown (n : ℕ) :
    2 ≤ (mycielskian (crown (n + 2))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_crown]; omega)

theorem diameter_mycielskian_crown_le_four (n : ℕ) :
    (mycielskian (crown (n + 2))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_crown]; omega)

theorem four_le_girth_mycielskian_crown (n : ℕ) :
    4 ≤ (mycielskian (crown (n + 2))).girth := by
  refine four_le_girth_mycielskian _ (by rw [cliqueNum_crown]) ?_
  have h := Nat.choose_pos (show 2 ≤ n + 2 by omega)
  rw [E_crown]
  omega

theorem matchNum_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).matchNum = 2 * n + 4 := by
  have h := matchNum_mycielskian (G := crown (n + 2)) (by rw [matchNum_crown, V_crown])
  rw [V_crown] at h
  omega

theorem cliqueCoverNum_mycielskian_crown (n : ℕ) :
    (mycielskian (crown (n + 2))).cliqueCoverNum = 2 * n + 5 := by
  have h := cliqueCoverNum_mycielskian (crown (n + 2)) (by rw [V_crown]; omega)
    (by rw [cliqueNum_crown]) (by rw [matchNum_crown, V_crown])
  rw [V_crown] at h
  omega

theorem indepNum_mycielskian_crown_le (n : ℕ) :
    (mycielskian (crown (n + 2))).indepNum ≤ 3 * n + 6 := by
  have h := indepNum_mycielskian_le (crown (n + 2)) (by rw [V_crown]; omega)
  rw [V_crown, indepNum_crown] at h
  omega

theorem coverNum_mycielskian_crown_le (n : ℕ) :
    (mycielskian (crown n)).coverNum ≤ 2 * n + 1 := by
  have h := coverNum_mycielskian_le (crown n)
  rw [V_crown] at h
  omega

end IsoGraph
