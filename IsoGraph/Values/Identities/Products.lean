import IsoGraph.Values.Identities.Complements

/-!
# The products of two named families

The four products applied to pairs of families — a complete graph with a cycle, a cycle with a
hypercube, a path with a hypercube — and the colourings, metrics and transitivity that come with
them.  Connectivity and triangles in the tensor product are the delicate entries, since the tensor
product of two connected graphs need not be connected.  The Mycielskians of the small families
begin at the end of the module.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ### Colourings and metrics of the strong and lexicographic products -/

/-- If both factors have chromatic number equal to their clique number, the strong product does
too: the clique bound below meets the product colouring above. -/
theorem chromNum_strongProduct_of_chromNum_eq_cliqueNum {G H : IsoGraph}
    (hG : G.chromNum = G.cliqueNum) (hH : H.chromNum = H.cliqueNum) :
    (G ⊠g H).chromNum = G.cliqueNum * H.cliqueNum := by
  have h1 := chromNum_strongProduct_le G H
  have h2 := cliqueNum_le_chromNum (G ⊠g H)
  rw [cliqueNum_strongProduct] at h2
  rw [hG, hH] at h1
  omega

/-- The same for the lexicographic product. -/
theorem chromNum_lexProduct_of_chromNum_eq_cliqueNum {G H : IsoGraph}
    (hG : G.chromNum = G.cliqueNum) (hH : H.chromNum = H.cliqueNum) :
    (G ·g H).chromNum = G.cliqueNum * H.cliqueNum := by
  have h1 := chromNum_lexProduct_le G H
  have h2 := cliqueNum_le_chromNum (G ·g H)
  rw [cliqueNum_lexProduct] at h2
  rw [hG, hH] at h1
  omega

theorem chromNum_king (m n : ℕ) : (path (m + 2) ⊠g path (n + 2)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (G := path (m + 2)) (H := path (n + 2))
    (by rw [chromNum_path, cliqueNum_path]) (by rw [chromNum_path, cliqueNum_path])
  rw [cliqueNum_path, cliqueNum_path] at h
  omega

theorem chromNum_eq_cliqueNum_cycle_even (m : ℕ) :
    (cycle (2 * m + 4)).chromNum = (cycle (2 * m + 4)).cliqueNum := by
  rw [cliqueNum_cycle, show 2 * m + 4 = 2 * (m + 1) + 2 from by ring, chromNum_cycle_even]

theorem chromNum_strongProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ⊠g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

theorem chromNum_lexProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ·g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
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

theorem diameter_strongProduct_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 2)).diameter = 1 := by
  rw [diameter_strongProduct (isConnected_complete (m + 1)) (isConnected_complete (n + 1)),
    diameter_complete, diameter_complete, max_self]

theorem radius_strongProduct_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 2)).radius = 1 := by
  rw [radius_strongProduct (isConnected_complete (m + 1)) (isConnected_complete (n + 1)),
    radius_complete, radius_complete, max_self]

theorem numComponents_strongProduct_complete (m n : ℕ) :
    (complete (m + 1) ⊠g complete (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_strongProduct_complete m n)

theorem numComponents_lexProduct_complete (m n : ℕ) :
    (complete (m + 1) ·g complete (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_lexProduct_complete m n)

/-- A dominating vertex of the second factor makes the lexicographic product dominated exactly as
its first factor is. -/
theorem domNum_lexProduct_complete (G : IsoGraph) (n : ℕ) :
    (G ·g complete (n + 1)).domNum = G.domNum :=
  domNum_lexProduct G (domNum_complete n)

theorem domNum_strongProduct_complete (m n : ℕ) :
    (complete (m + 1) ⊠g complete (n + 1)).domNum = 1 :=
  domNum_strongProduct_eq_one (domNum_complete m) (domNum_complete n)

theorem radius_strongProduct_of_domNum_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 1)).radius = 1 := by
  refine radius_strongProduct_eq_one ?_ (domNum_complete (m + 1)) (domNum_complete n)
  rw [V_strongProduct, V_complete, V_complete]
  have h : 2 * 1 ≤ (m + 2) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem radius_lexProduct_complete (m n : ℕ) :
    (complete (m + 2) ·g complete (n + 1)).radius = 1 := by
  refine radius_lexProduct_eq_one ?_ (domNum_complete (m + 1)) (domNum_complete n)
  rw [V_lexProduct, V_complete, V_complete]
  have h : 2 * 1 ≤ (m + 2) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ### Perfect factors in the tensor and lexicographic products -/

/-- The tensor product projects onto either factor, so `χ(G ⊗ H) ≤ min χ(G) χ(H)`, while its
clique number is `min ω(G) ω(H)`; when both factors have `χ = ω` the two bounds meet. -/
theorem chromNum_tensorProduct_of_chromNum_eq_cliqueNum {G H : IsoGraph}
    (hG : G.chromNum = G.cliqueNum) (hH : H.chromNum = H.cliqueNum) :
    (G ⊗g H).chromNum = min G.cliqueNum H.cliqueNum := by
  have h1 := chromNum_tensorProduct_le G H
  have h2 := cliqueNum_le_chromNum (G ⊗g H)
  rw [cliqueNum_tensorProduct] at h2
  rw [hG, hH] at h1
  omega

theorem chromNum_eq_cliqueNum_path (n : ℕ) :
    (path (n + 2)).chromNum = (path (n + 2)).cliqueNum := by
  rw [chromNum_path, cliqueNum_path]

theorem chromNum_eq_cliqueNum_complete (n : ℕ) :
    (complete n).chromNum = (complete n).cliqueNum := by
  rw [chromNum_complete, cliqueNum_complete]

theorem chromNum_tensorProduct_complete (m n : ℕ) :
    (complete m ⊗g complete n).chromNum = min m n := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_complete n)
  rwa [cliqueNum_complete, cliqueNum_complete] at h

theorem chromNum_tensorProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ⊗g cycle (2 * n + 4)).chromNum = 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

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

theorem chromNum_tensorProduct_complete_path (m n : ℕ) :
    (complete m ⊗g path (n + 2)).chromNum = min m 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_path n)
  rwa [cliqueNum_complete, cliqueNum_path] at h

theorem chromNum_tensorProduct_complete_cycle_even (m n : ℕ) :
    (complete m ⊗g cycle (2 * n + 4)).chromNum = min m 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_cycle_even n)
  rwa [cliqueNum_complete, cliqueNum_cycle] at h

theorem chromNum_strongProduct_complete_path (m n : ℕ) :
    (complete m ⊠g path (n + 2)).chromNum = m * 2 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_path n)
  rwa [cliqueNum_complete, cliqueNum_path] at h

theorem chromNum_lexProduct_complete_path (m n : ℕ) :
    (complete m ·g path (n + 2)).chromNum = m * 2 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_path n)
  rwa [cliqueNum_complete, cliqueNum_path] at h

theorem chromNum_strongProduct_complete_cycle_even (m n : ℕ) :
    (complete m ⊠g cycle (2 * n + 4)).chromNum = m * 2 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_cycle_even n)
  rwa [cliqueNum_complete, cliqueNum_cycle] at h

theorem chromNum_strongProduct_path_cycle_even (m n : ℕ) :
    (path (m + 2) ⊠g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_path m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_path, cliqueNum_cycle] at h
  omega

theorem chromNum_lexProduct_path_cycle_even (m n : ℕ) :
    (path (m + 2) ·g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_path m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_path, cliqueNum_cycle] at h
  omega

/-- The clique cover dual: independent sets multiply in a lexicographic product and clique covers
multiply at worst, so factors with `κ = α` force equality. -/
theorem cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum {G H : IsoGraph}
    (hG : G.cliqueCoverNum = G.indepNum) (hH : H.cliqueCoverNum = H.indepNum) :
    (G ·g H).cliqueCoverNum = G.indepNum * H.indepNum := by
  have h1 := cliqueCoverNum_lexProduct_le G H
  have h2 := indepNum_le_cliqueCoverNum (G ·g H)
  rw [indepNum_lexProduct] at h2
  rw [hG, hH] at h1
  omega

theorem cliqueCoverNum_eq_indepNum_path (n : ℕ) :
    (path n).cliqueCoverNum = (path n).indepNum := by
  rw [cliqueCoverNum_path, indepNum_path]

theorem cliqueCoverNum_eq_indepNum_complete (n : ℕ) :
    (complete (n + 1)).cliqueCoverNum = (complete (n + 1)).indepNum := by
  rw [cliqueCoverNum_complete, indepNum_complete]
  omega

theorem cliqueCoverNum_eq_indepNum_cycle_even (m : ℕ) :
    (cycle (2 * m + 4)).cliqueCoverNum = (cycle (2 * m + 4)).indepNum := by
  rw [cliqueCoverNum_cycle, indepNum_cycle]
  omega

theorem cliqueCoverNum_lexProduct_path (m n : ℕ) :
    (path m ·g path n).cliqueCoverNum = (m + 1) / 2 * ((n + 1) / 2) := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_path m) (cliqueCoverNum_eq_indepNum_path n)
  rwa [indepNum_path, indepNum_path] at h

theorem cliqueCoverNum_lexProduct_complete (m n : ℕ) :
    (complete (m + 1) ·g complete (n + 1)).cliqueCoverNum = 1 := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_complete m) (cliqueCoverNum_eq_indepNum_complete n)
  rw [indepNum_complete, indepNum_complete, Nat.min_eq_right (by omega : 1 ≤ m + 1),
    Nat.min_eq_right (by omega : 1 ≤ n + 1)] at h
  simpa using h

theorem cliqueCoverNum_lexProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ·g cycle (2 * n + 4)).cliqueCoverNum = (m + 2) * (n + 2) := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_cycle_even m) (cliqueCoverNum_eq_indepNum_cycle_even n)
  rw [indepNum_cycle, indepNum_cycle, show (2 * m + 4) / 2 = m + 2 from by omega,
    show (2 * n + 4) / 2 = n + 2 from by omega] at h
  exact h

theorem cliqueCoverNum_lexProduct_path_complete (m n : ℕ) :
    (path m ·g complete (n + 1)).cliqueCoverNum = (m + 1) / 2 := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_path m) (cliqueCoverNum_eq_indepNum_complete n)
  rw [indepNum_path, indepNum_complete, Nat.min_eq_right (by omega : 1 ≤ n + 1)] at h
  simpa using h

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

theorem isVertexTransitive_cartesianProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m □g cycle n) :=
  (isVertexTransitive_complete m).cartesianProduct (isVertexTransitive_cycle n)

theorem isVertexTransitive_tensorProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m ⊗g cycle n) :=
  (isVertexTransitive_complete m).tensorProduct (isVertexTransitive_cycle n)

theorem isVertexTransitive_strongProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m ⊠g cycle n) :=
  (isVertexTransitive_complete m).strongProduct (isVertexTransitive_cycle n)

theorem isVertexTransitive_lexProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m ·g cycle n) :=
  (isVertexTransitive_complete m).lexProduct (isVertexTransitive_cycle n)

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

theorem isVertexTransitive_compl_petersen : IsVertexTransitive (petersenᶜ) :=
  (isVertexTransitive_compl _).2 isVertexTransitive_petersen

theorem isVertexTransitive_compl_bipartite_self (n : ℕ) :
    IsVertexTransitive ((bipartite n n)ᶜ) :=
  (isVertexTransitive_compl _).2 (isVertexTransitive_bipartite_self n)

theorem isVertexTransitive_compl_lineGraph_petersen :
    IsVertexTransitive ((lineGraph petersen)ᶜ) :=
  (isVertexTransitive_compl _).2 isVertexTransitive_lineGraph_petersen

/-! ### The cartesian product of a complete graph with a cycle -/

theorem cliqueNum_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) □g cycle (n + 4)).cliqueNum = m + 2 := by
  have h := cliqueNum_cartesianProduct (G := complete (m + 2)) (H := cycle (n + 4))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [cliqueNum_complete, cliqueNum_cycle] at h
  omega

theorem chromNum_cartesianProduct_complete_cycle_even (m t : ℕ) :
    (complete (m + 2) □g cycle (2 * t + 2)).chromNum = m + 2 := by
  have h := chromNum_cartesianProduct (G := complete (m + 2)) (H := cycle (2 * t + 2))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_complete, chromNum_cycle_even] at h
  omega

theorem chromNum_cartesianProduct_complete_cycle_odd (m t : ℕ) :
    (complete (m + 3) □g cycle (2 * t + 3)).chromNum = m + 3 := by
  have h := chromNum_cartesianProduct (G := complete (m + 3)) (H := cycle (2 * t + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_complete, chromNum_cycle_odd] at h
  omega

theorem diameter_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) □g cycle (n + 1)).diameter = 1 + (n + 1) / 2 := by
  rw [diameter_cartesianProduct (isConnected_complete (m + 1)) (isConnected_cycle n),
    diameter_complete, diameter_cycle]

theorem radius_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) □g cycle (n + 1)).radius = 1 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_complete (m + 1)) (isConnected_cycle n),
    radius_complete, radius_cycle]

theorem maxDeg_cartesianProduct_complete_cycle (m n : ℕ) :
    maxDeg (complete (m + 1) □g cycle (n + 3)) = m + 2 := by
  have h := maxDeg_cartesianProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_complete, maxDeg_cycle] at h
  omega

theorem minDeg_cartesianProduct_complete_cycle (m n : ℕ) :
    minDeg (complete (m + 1) □g cycle (n + 3)) = m + 2 := by
  have h := minDeg_cartesianProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_complete, minDeg_cycle] at h
  omega

theorem isRegularWith_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 1) □g cycle (n + 3)).IsRegularWith (m + 2) := by
  have h := (isRegularWith_complete (m + 1)).cartesianProduct (isRegularWith_cycle n)
  rwa [show m + 1 - 1 + 2 = m + 2 from by omega] at h

theorem girth_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 3) □g cycle (n + 3)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_cartesianProduct (G := complete (m + 3)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [cliqueNum_complete] at h
  omega

/-! ### The cartesian product of a complete graph with a path -/

theorem cliqueNum_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 2)).cliqueNum = m + 2 := by
  have h := cliqueNum_cartesianProduct (G := complete (m + 2)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_complete, cliqueNum_path] at h
  omega

theorem chromNum_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 2)).chromNum = m + 2 := by
  have h := chromNum_cartesianProduct (G := complete (m + 2)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [chromNum_complete, chromNum_path] at h
  omega

theorem diameter_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 1)).diameter = 1 + n := by
  rw [diameter_cartesianProduct (isConnected_complete (m + 1)) (isConnected_path n),
    diameter_complete, diameter_path]

theorem radius_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 1)).radius = 1 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_complete (m + 1)) (isConnected_path n),
    radius_complete, radius_path]

theorem maxDeg_cartesianProduct_complete_path (m n : ℕ) :
    maxDeg (complete (m + 1) □g path (n + 3)) = m + 2 := by
  have h := maxDeg_cartesianProduct (G := complete (m + 1)) (H := path (n + 3))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [maxDeg_complete, maxDeg_path] at h
  omega

theorem minDeg_cartesianProduct_complete_path (m n : ℕ) :
    minDeg (complete (m + 1) □g path (n + 2)) = m + 1 := by
  have h := minDeg_cartesianProduct (G := complete (m + 1)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [minDeg_complete, minDeg_path] at h
  omega

theorem girth_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 3) □g path (n + 2)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_cartesianProduct (G := complete (m + 3)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_complete] at h
  omega

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

/-! ### Class-one cartesian products

`χ'(G □ H) ≤ χ'(G) + χ'(H)` meets the maximum degree exactly when both factors do, so a product of
two class-one graphs is class one.  Every case below has an even complete graph or an even cycle
on each side, since those are the class-one members of their families. -/

/-- **`K_{2m+2} □ Pₙ` is class one.** -/
theorem edgeChromNum_cartesianProduct_complete_even_path (m n : ℕ) :
    (complete (2 * m + 2) □g path (n + 3)).edgeChromNum = 2 * m + 3 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := complete (2 * m + 2)) (H := path (n + 3))
      (E_complete_pos (2 * m))
      (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
    rwa [edgeChromNum_complete_even, edgeChromNum_path, show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h
  · have h := maxDeg_le_edgeChromNum (complete (2 * m + 2) □g path (n + 3))
    rwa [show 2 * m + 2 = (2 * m + 1) + 1 by omega, maxDeg_cartesianProduct_complete_path,
      show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h

/-- **`K_{2m+2} □ C_{2n+4}` is class one.** -/
theorem edgeChromNum_cartesianProduct_complete_even_cycle_even (m n : ℕ) :
    (complete (2 * m + 2) □g cycle (2 * n + 4)).edgeChromNum = 2 * m + 3 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := complete (2 * m + 2))
      (H := cycle (2 * n + 4)) (E_complete_pos (2 * m))
      (by rw [show 2 * n + 4 = (2 * n + 1) + 3 by omega, E_cycle]; omega)
    rwa [edgeChromNum_complete_even, edgeChromNum_cycle_even,
      show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h
  · have h := maxDeg_le_edgeChromNum (complete (2 * m + 2) □g cycle (2 * n + 4))
    rwa [show 2 * m + 2 = (2 * m + 1) + 1 by omega, show 2 * n + 4 = (2 * n + 1) + 3 by omega,
      maxDeg_cartesianProduct_complete_cycle, show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h

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

/-! ### Colouring the torus and the cylinder -/

theorem chromNum_cartesianProduct_cycle_even_even (a b : ℕ) :
    (cycle (2 * a + 2) □g cycle (2 * b + 2)).chromNum = 2 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 2)) (H := cycle (2 * b + 2))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_cycle_even, chromNum_cycle_even] at h
  omega

theorem chromNum_cartesianProduct_cycle_odd_even (a b : ℕ) :
    (cycle (2 * a + 3) □g cycle (2 * b + 2)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 3)) (H := cycle (2 * b + 2))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_cycle_odd, chromNum_cycle_even] at h
  omega

theorem chromNum_cartesianProduct_cycle_odd_odd (a b : ℕ) :
    (cycle (2 * a + 3) □g cycle (2 * b + 3)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 3)) (H := cycle (2 * b + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_cycle_odd, chromNum_cycle_odd] at h
  omega

theorem chromNum_cartesianProduct_cycle_even_path (a n : ℕ) :
    (cycle (2 * a + 2) □g path (n + 2)).chromNum = 2 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 2)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [chromNum_cycle_even, chromNum_path] at h
  omega

theorem chromNum_cartesianProduct_cycle_odd_path (a n : ℕ) :
    (cycle (2 * a + 3) □g path (n + 2)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 3)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [chromNum_cycle_odd, chromNum_path] at h
  omega

/-! ### Connectivity of the tensor product

`isConnected_tensorProduct` asks for a connected non-bipartite left factor and a connected right
factor with at least one edge; the odd cycles, the complete graphs on at least three vertices and
the Petersen graph all serve on the left. -/

theorem E_pos_hypercube (n : ℕ) : 0 < (hypercube (n + 1)).E := by
  have h := E_hypercube (n + 1)
  have hp : 0 < (n + 1) * 2 ^ (n + 1) := by positivity
  omega

theorem isConnected_tensorProduct_cycle_odd_cycle (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g cycle (n + 3)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_cycle (n + 2))
    (not_isBipartite_cycle_odd a) (by rw [E_cycle]; omega)

theorem numComponents_tensorProduct_cycle_odd_cycle (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g cycle (n + 3)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_cycle a n)

theorem isConnected_tensorProduct_cycle_odd_path (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g path (n + 2)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_path (n + 1))
    (not_isBipartite_cycle_odd a) (by rw [E_path]; omega)

theorem numComponents_tensorProduct_cycle_odd_path (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g path (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_path a n)

theorem isConnected_tensorProduct_cycle_odd_complete (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g complete (n + 2)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_complete (n + 1))
    (not_isBipartite_cycle_odd a) (E_complete_pos n)

theorem numComponents_tensorProduct_cycle_odd_complete (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g complete (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_complete a n)

theorem isConnected_tensorProduct_cycle_odd_hypercube (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g hypercube (n + 1)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_hypercube (n + 1))
    (not_isBipartite_cycle_odd a) (E_pos_hypercube n)

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

theorem isConnected_tensorProduct_complete_cycle (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g cycle (n + 3)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_cycle (n + 2))
    (not_isBipartite_complete m) (by rw [E_cycle]; omega)

theorem numComponents_tensorProduct_complete_cycle (m n : ℕ) :
    (complete (m + 3) ⊗g cycle (n + 3)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_cycle m n)

theorem isConnected_tensorProduct_complete_path (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g path (n + 2)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_path (n + 1))
    (not_isBipartite_complete m) (by rw [E_path]; omega)

theorem numComponents_tensorProduct_complete_path (m n : ℕ) :
    (complete (m + 3) ⊗g path (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_path m n)

theorem isConnected_tensorProduct_complete_hypercube (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g hypercube (n + 1)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_hypercube (n + 1))
    (not_isBipartite_complete m) (E_pos_hypercube n)

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
    not_isBipartite_petersen (E_pos_hypercube n)

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

/-! ### The strong product of a complete graph with a cycle -/

theorem isConnected_strongProduct_complete_cycle (m n : ℕ) :
    IsConnected (complete (m + 1) ⊠g cycle (n + 1)) :=
  isConnected_strongProduct (isConnected_complete m) (isConnected_cycle n)

theorem diameter_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ⊠g cycle (n + 1)).diameter = max 1 ((n + 1) / 2) := by
  rw [diameter_strongProduct (isConnected_complete (m + 1)) (isConnected_cycle n),
    diameter_complete, diameter_cycle]

theorem radius_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ⊠g cycle (n + 1)).radius = max 1 ((n + 1) / 2) := by
  rw [radius_strongProduct (isConnected_complete (m + 1)) (isConnected_cycle n), radius_complete,
    radius_cycle]

theorem maxDeg_strongProduct_complete_cycle (m n : ℕ) :
    maxDeg (complete (m + 1) ⊠g cycle (n + 3)) = 3 * m + 2 := by
  have h := maxDeg_strongProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_complete, maxDeg_cycle] at h
  omega

theorem minDeg_strongProduct_complete_cycle (m n : ℕ) :
    minDeg (complete (m + 1) ⊠g cycle (n + 3)) = 3 * m + 2 := by
  have h := minDeg_strongProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_complete, minDeg_cycle] at h
  omega

theorem isRegularWith_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 1) ⊠g cycle (n + 3)).IsRegularWith (3 * m + 2) := by
  have h := (isRegularWith_complete (m + 1)).strongProduct (isRegularWith_cycle n)
  rwa [show (m + 1 - 1 + 1) * (2 + 1) - 1 = 3 * m + 2 from by omega] at h

theorem girth_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ⊠g cycle (n + 3)).girth = 3 :=
  girth_strongProduct (E_complete_pos m) (by rw [E_cycle]; omega)

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
  girth_strongProduct (by rw [E_cycle]; omega) (E_pos_hypercube n)

/-! ### The lexicographic product of a complete graph with a cycle -/

theorem isConnected_lexProduct_complete_cycle (m n : ℕ) :
    IsConnected (complete (m + 1) ·g cycle (n + 1)) :=
  isConnected_lexProduct (isConnected_complete m) (isConnected_cycle n)

theorem maxDeg_lexProduct_complete_cycle (m n : ℕ) :
    maxDeg (complete (m + 1) ·g cycle (n + 3)) = m * (n + 3) + 2 := by
  have h := maxDeg_lexProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_complete, maxDeg_cycle, V_cycle] at h
  simpa using h

theorem minDeg_lexProduct_complete_cycle (m n : ℕ) :
    minDeg (complete (m + 1) ·g cycle (n + 3)) = m * (n + 3) + 2 := by
  have h := minDeg_lexProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_complete, minDeg_cycle, V_cycle] at h
  simpa using h

theorem isRegularWith_lexProduct_complete_cycle (m n : ℕ) :
    (complete (m + 1) ·g cycle (n + 3)).IsRegularWith (m * (n + 3) + 2) := by
  have h := (isRegularWith_complete (m + 1)).lexProduct (isRegularWith_cycle n)
  rw [V_cycle, show m + 1 - 1 = m from by omega] at h
  exact h

theorem girth_lexProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ·g cycle (n + 3)).girth = 3 :=
  girth_lexProduct (E_complete_pos m) (by rw [E_cycle]; omega)

/-! ### More colourings of the strong and lexicographic products -/

theorem chromNum_lexProduct_complete_cycle_even (m n : ℕ) :
    (complete m ·g cycle (2 * n + 4)).chromNum = m * 2 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_cycle_even n)
  rwa [cliqueNum_complete, cliqueNum_cycle] at h

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

theorem cliqueCoverNum_lexProduct_complete_cycle_even (m n : ℕ) :
    (complete (m + 1) ·g cycle (2 * n + 4)).cliqueCoverNum = n + 2 := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_complete m) (cliqueCoverNum_eq_indepNum_cycle_even n)
  rw [indepNum_complete, indepNum_cycle, Nat.min_eq_right (by omega : 1 ≤ m + 1),
    Nat.one_mul] at h
  omega

/-! ### The strong product of a complete graph with a path -/

theorem isConnected_strongProduct_complete_path (m n : ℕ) :
    IsConnected (complete (m + 1) ⊠g path (n + 1)) :=
  isConnected_strongProduct (isConnected_complete m) (isConnected_path n)

theorem diameter_strongProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ⊠g path (n + 1)).diameter = max 1 n := by
  rw [diameter_strongProduct (isConnected_complete (m + 1)) (isConnected_path n),
    diameter_complete, diameter_path]

theorem radius_strongProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ⊠g path (n + 1)).radius = max 1 ((n + 1) / 2) := by
  rw [radius_strongProduct (isConnected_complete (m + 1)) (isConnected_path n), radius_complete,
    radius_path]

theorem maxDeg_strongProduct_complete_path (m n : ℕ) :
    maxDeg (complete (m + 1) ⊠g path (n + 3)) = 3 * m + 2 := by
  have h := maxDeg_strongProduct (G := complete (m + 1)) (H := path (n + 3))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [maxDeg_complete, maxDeg_path] at h
  omega

theorem minDeg_strongProduct_complete_path (m n : ℕ) :
    minDeg (complete (m + 1) ⊠g path (n + 2)) = 2 * m + 1 := by
  have h := minDeg_strongProduct (G := complete (m + 1)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [minDeg_complete, minDeg_path] at h
  omega

theorem girth_strongProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ⊠g path (n + 2)).girth = 3 :=
  girth_strongProduct (E_complete_pos m) (by rw [E_path]; omega)

/-! ### The lexicographic product of a complete graph with a path -/

theorem isConnected_lexProduct_complete_path (m n : ℕ) :
    IsConnected (complete (m + 1) ·g path (n + 1)) :=
  isConnected_lexProduct (isConnected_complete m) (isConnected_path n)

theorem maxDeg_lexProduct_complete_path (m n : ℕ) :
    maxDeg (complete (m + 1) ·g path (n + 3)) = m * (n + 3) + 2 := by
  have h := maxDeg_lexProduct (G := complete (m + 1)) (H := path (n + 3))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [maxDeg_complete, maxDeg_path, V_path] at h
  simpa using h

theorem minDeg_lexProduct_complete_path (m n : ℕ) :
    minDeg (complete (m + 1) ·g path (n + 2)) = m * (n + 2) + 1 := by
  have h := minDeg_lexProduct (G := complete (m + 1)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [minDeg_complete, minDeg_path, V_path] at h
  simpa using h

theorem girth_lexProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ·g path (n + 2)).girth = 3 :=
  girth_lexProduct (E_complete_pos m) (by rw [E_path]; omega)

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
  girth_strongProduct (by rw [E_path]; omega) (E_pos_hypercube n)

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
  girth_lexProduct (by rw [E_cycle]; omega) (E_pos_hypercube n)

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

/-! ### The join of a path with a cycle -/

theorem maxDeg_join_path_cycle (m n : ℕ) :
    maxDeg (path (m + 3) ∇g cycle (n + 3)) = max (n + 5) (m + 5) := by
  have h := maxDeg_join (G := path (m + 3)) (H := cycle (n + 3))
    (by rw [V_path]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_path, maxDeg_cycle, V_path, V_cycle] at h
  rw [h]
  omega

theorem minDeg_join_path_cycle (m n : ℕ) :
    minDeg (path (m + 2) ∇g cycle (n + 3)) = min (n + 4) (m + 4) := by
  have h := minDeg_join (G := path (m + 2)) (H := cycle (n + 3))
    (by rw [V_path]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_path, minDeg_cycle, V_path, V_cycle] at h
  rw [h]
  omega

@[simp] theorem girth_join_path_cycle (m n : ℕ) :
    (path (m + 2) ∇g cycle (n + 4)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_path, cliqueNum_cycle]; omega)

theorem diameter_join_path_cycle (m n : ℕ) :
    (path (m + 3) ∇g cycle (n + 1)).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_cycle]; omega) ?_
  rw [E_path, V_path, h]
  omega

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

/-! ### The Mycielskian of a cycle -/

theorem E_mycielskian_cycle (m : ℕ) : (mycielskian (cycle (m + 3))).E = 4 * (m + 3) := by
  rw [E_mycielskian, E_cycle, V_cycle]
  omega

theorem cliqueNum_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 4))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (cycle (m + 4)) (by rw [V_cycle]; omega)
  rw [cliqueNum_cycle] at h
  omega

theorem maxDeg_mycielskian_cycle (m : ℕ) :
    maxDeg (mycielskian (cycle (m + 3))) = max 4 (m + 3) := by
  have h := maxDeg_mycielskian (cycle (m + 3))
  rw [maxDeg_cycle, V_cycle] at h
  omega

theorem minDeg_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 3))).minDeg = min 3 (m + 3) := by
  have h := minDeg_mycielskian (cycle (m + 3)) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, V_cycle] at h
  omega

theorem domNum_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 3))).domNum = (m + 5) / 3 + 1 := by
  have h := domNum_mycielskian (cycle (m + 3)) (by rw [V_cycle]; omega)
  rw [domNum_cycle] at h
  omega

theorem isConnected_mycielskian_cycle (m : ℕ) :
    IsConnected (mycielskian (cycle (m + 3))) :=
  isConnected_mycielskian _ (by rw [minDeg_cycle]; omega)

theorem numComponents_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 3))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_cycle]; omega)

theorem radius_mycielskian_cycle (m : ℕ) : (mycielskian (cycle (m + 3))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_cycle]; omega)

theorem four_le_girth_mycielskian_cycle (m : ℕ) :
    4 ≤ (mycielskian (cycle (m + 4))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_cycle]) (by rw [E_cycle]; omega)

theorem matchNum_mycielskian_cycle_even (m : ℕ) :
    (mycielskian (cycle (2 * m + 4))).matchNum = 2 * m + 4 := by
  have h := matchNum_mycielskian (cycle (2 * m + 4)) (by rw [matchNum_cycle, V_cycle]; omega)
  rwa [V_cycle] at h

theorem cliqueCoverNum_mycielskian_cycle_even (m : ℕ) :
    (mycielskian (cycle (2 * m + 4))).cliqueCoverNum = 2 * m + 5 := by
  have h := cliqueCoverNum_mycielskian (cycle (2 * m + 4)) (by rw [V_cycle]; omega)
    (by rw [cliqueNum_cycle]) (by rw [matchNum_cycle, V_cycle]; omega)
  rw [V_cycle] at h
  omega

/-! ### The Mycielskian of a path -/

theorem E_mycielskian_path (m : ℕ) : (mycielskian (path (m + 1))).E = 4 * m + 1 := by
  rw [E_mycielskian, E_path, V_path]
  omega

theorem cliqueNum_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 2))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (path (m + 2)) (by rw [V_path]; omega)
  rw [cliqueNum_path] at h
  omega

theorem maxDeg_mycielskian_path (m : ℕ) :
    maxDeg (mycielskian (path (m + 3))) = max 4 (m + 3) := by
  have h := maxDeg_mycielskian (path (m + 3))
  rw [maxDeg_path, V_path] at h
  omega

theorem minDeg_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 2))).minDeg = min 2 (m + 2) := by
  have h := minDeg_mycielskian (path (m + 2)) (by rw [V_path]; omega)
  rw [minDeg_path, V_path] at h
  omega

theorem domNum_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 1))).domNum = (m + 3) / 3 + 1 := by
  have h := domNum_mycielskian (path (m + 1)) (by rw [V_path]; omega)
  rw [domNum_path] at h
  omega

theorem isConnected_mycielskian_path (m : ℕ) :
    IsConnected (mycielskian (path (m + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_path]; omega)

theorem numComponents_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_path]; omega)

theorem radius_mycielskian_path (m : ℕ) : (mycielskian (path (m + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_path]; omega)

theorem four_le_girth_mycielskian_path (m : ℕ) :
    4 ≤ (mycielskian (path (m + 2))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_path]) (by rw [E_path]; omega)

theorem matchNum_mycielskian_path_even (m : ℕ) :
    (mycielskian (path (2 * m + 2))).matchNum = 2 * m + 2 := by
  have h := matchNum_mycielskian (path (2 * m + 2)) (by rw [matchNum_path, V_path]; omega)
  rwa [V_path] at h

theorem cliqueCoverNum_mycielskian_path_even (m : ℕ) :
    (mycielskian (path (2 * m + 2))).cliqueCoverNum = 2 * m + 3 := by
  have h := cliqueCoverNum_mycielskian (path (2 * m + 2)) (by rw [V_path]; omega)
    (by rw [cliqueNum_path]) (by rw [matchNum_path, V_path]; omega)
  rw [V_path] at h
  omega

/-! ### The Mycielskian of a complete graph -/

theorem cliqueNum_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 1))).cliqueNum = max (m + 1) 2 := by
  have h := cliqueNum_mycielskian (complete (m + 1)) (by rw [V_complete]; omega)
  rw [cliqueNum_complete] at h
  omega

theorem maxDeg_mycielskian_complete (m : ℕ) :
    maxDeg (mycielskian (complete m)) = max (2 * (m - 1)) m := by
  have h := maxDeg_mycielskian (complete m)
  rw [maxDeg_complete, V_complete] at h
  omega

theorem minDeg_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 1))).minDeg = min (2 * m) (m + 1) := by
  have h := minDeg_mycielskian (complete (m + 1)) (by rw [V_complete]; omega)
  rw [minDeg_complete, V_complete] at h
  omega

theorem domNum_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 1))).domNum = 2 := by
  have h := domNum_mycielskian (complete (m + 1)) (by rw [V_complete]; omega)
  rw [domNum_complete] at h
  omega

theorem isConnected_mycielskian_complete (m : ℕ) :
    IsConnected (mycielskian (complete (m + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_complete]; omega)

theorem numComponents_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_complete]; omega)

theorem radius_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_complete]; omega)

theorem girth_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 3))).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_mycielskian (complete (m + 3)) (by rw [V_complete]; omega)
  rw [cliqueNum_complete] at h
  omega

theorem matchNum_mycielskian_complete_even (m : ℕ) :
    (mycielskian (complete (2 * m))).matchNum = 2 * m := by
  have h := matchNum_mycielskian (complete (2 * m)) (by rw [matchNum_complete, V_complete]; omega)
  rwa [V_complete] at h

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
  four_le_girth_mycielskian _ (by rw [cliqueNum_hypercube]) (E_pos_hypercube n)

theorem matchNum_mycielskian_hypercube (n : ℕ) :
    (mycielskian (hypercube (n + 1))).matchNum = 2 ^ (n + 1) := by
  have h := matchNum_mycielskian (hypercube (n + 1))
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
  have h := matchNum_mycielskian petersen (by rw [matchNum_petersen, V_petersen])
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
  have h := matchNum_mycielskian (bipartite (n + 1) (n + 1))
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
  have h := matchNum_mycielskian (cocktailParty (n + 2))
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
  have h := matchNum_mycielskian (wheel (2 * m + 3))
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
  have h := matchNum_mycielskian (fan (2 * m + 1)) (by rw [matchNum_fan, V_fan]; omega)
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
  have h := matchNum_mycielskian (ladder n) (by rw [matchNum_ladder, V_ladder]; omega)
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
  have h := matchNum_mycielskian (prism n) (by rw [matchNum_prism, V_prism]; omega)
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
  have h := matchNum_mycielskian (crown (n + 2)) (by rw [matchNum_crown, V_crown])
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
