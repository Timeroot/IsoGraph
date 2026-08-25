import IsoGraph.SmallGraphs.Tables

/-!
# Values pinned down by a bound from each side

Values pinned down by a bound from each side, and the demonstrations that the bound library and the
`simp` set really do close these goals unaided.
-/

namespace IsoGraph

/-! ## The simp set at work

These are not new facts — they are a regression test that the `@[simp]` lemmas above compose the
way they are meant to, and that none of them loops. -/

example : (cycle 5)ᶜᶜ = cycle 5 := by simp

example (n : ℕ) : empty 0 □g cycle n = empty 0 := by simp

example (G : IsoGraph) : empty 1 ·g (G ·g empty 1) = G := by simp

example : circulant 7 [0, 3, 3] = circulant 7 [3] := by simp

example (n : ℕ) : IsBipartite (hypercube n) := by simp

example (ks : List ℕ) : IsBipartite (spider ks) := by simp

example (m n : ℕ) : IsBipartite (doubleStar m n) := by simp

example (k : ℕ) : IsBipartite (tadpole 6 k) := isBipartite_tadpole_even 3 k

example : IsBipartite (cyclePendant 4 [1, 1]) := isBipartite_cyclePendant_even 2 [1, 1] (by decide)

example : IsBipartite (thetaGraph [0, 2, 4]) := isBipartite_thetaGraph_even (by decide)

example : IsBipartite (thetaGraph [1, 3, 5]) := isBipartite_thetaGraph_odd (by decide)

example : ¬ IsBipartite (thetaGraph [0, 1]) := not_isBipartite_thetaGraph_pair (by decide)

example (k : ℕ) : ¬ IsBipartite (tadpole 5 k) := not_isBipartite_tadpole_odd 1 k

example : ¬ IsBipartite (cyclePendant 3 [1, 0, 2]) := not_isBipartite_cyclePendant_odd 0 [1, 0, 2]

example : ¬ IsBipartite (lollipop 4 2) := not_isBipartite_lollipop 1 2

example : ¬ IsBipartite (wheel 5) := not_isBipartite_wheel 2

example : ¬ IsBipartite (mycielskian (cycle 5)) := by simp

example : IsBipartite (mycielskian (empty 3)) := by simp

example : IsBipartite (foldedCube 5) := isBipartite_foldedCube_odd (by decide)

example : ¬ IsBipartite (foldedCube 4) := not_isBipartite_foldedCube_even 1

example : IsBipartite (circulant 8 [1, 3]) := isBipartite_circulant (by decide) (by decide)

example : ¬ IsBipartite (circulant 7 [2]) :=
  not_isBipartite_circulant_of_odd (by decide) 2 (by decide) (by omega) (by omega)

example : ¬ IsBipartite (kneser 6 2) := by simp

example : ¬ IsBipartite (johnson 5 2) := by simp

example : ¬ IsBipartite (triangular 5) := not_isBipartite_triangular (by omega)

example : ¬ IsBipartite petersen := by simp

example : ¬ IsBipartite (rook 3 3) := not_isBipartite_rook 0 2

example : ¬ IsBipartite (book 3) := by simp

example : ¬ IsBipartite (cocktailParty 4) := by simp

example : ¬ IsBipartite (fan 5) := by simp

example (G : IsoGraph) : ¬ IsBipartite (cycle 3 ∇g G) :=
  not_isBipartite_join_left not_isBipartite_cycle_three

example : ¬ IsBipartite (completeMultipartite [2, 3, 4]) :=
  not_isBipartite_completeMultipartite 1 2 3 []

example : ¬ IsBipartite (prism 5) := not_isBipartite_prism_odd 1

example (G H : IsoGraph) (h : IsBipartite (G ⊕g H)) : IsBipartite G := by simp_all

example (n : ℕ) : IsBipartite (thetaGraph (List.replicate n 1)) := by simp

example (m n : ℕ) : IsBipartite (ladder m ⊕g bipartite m n) := by simp

example (m n : ℕ) : IsBipartite (cycle (2 * m) □g path n) := by simp

example (n : ℕ) :
    complete 2 ⊗g hypercube n = hypercube n ⊕g hypercube n :=
  tensorProduct_complete_two_of_isBipartite _ (by simp)

example : circulant 9 [0, 1] = cycle 9 := by simp

example : (paley 13)ᶜ = paley 13 := by simp

example : petersen.V = 10 := by simp [Nat.choose]

example (G H : IsoGraph) : (Gᶜᶜ ⊕g H).V = G.V + H.V := by simp

example (m n : ℕ) : (rook m n).V = m * n := by simp

example (n : ℕ) : lineGraph (empty n) = empty 0 := by simp

example (n : ℕ) : empty n ⊗g complete 3 = empty (n * 3) := by simp

example : tadpole 3 0 = complete 3 := by rw [tadpole_zero, cycle_three]

example (k : ℕ) : spider [k] = lollipop 1 k := by simp

example : lollipop 3 0 = complete 3 := by simp

example : spider [1] = complete 2 := by simp

example (m : ℕ) : IsBipartite (tadpole (2 * m) 0) := by simp

example : cyclePendant 5 [] = cycle 5 := by simp

example : (cyclePendant 5 [])ᶜ = cycle 5 := by simp

example : spider [2, 2] = path 5 := by simp

example : thetaGraph [3] = path 5 := by simp

example (j : ℕ) : thetaGraph (List.replicate (j + 1) 0) = complete 2 := by simp

example (n : ℕ) : spider (List.replicate n 1) = star n := by simp

example : doubleStar 0 3 = star 4 := by simp

example : doubleStar 3 0 = star 4 := by simp

example : doubleStar 0 1 = path 3 := by rw [doubleStar_left_zero, star_two]

example : thetaGraph [1, 1] = cycle 4 := by simp

example : thetaGraph [0, 2] = cycle 4 := by simp

example : thetaGraph [1, 2] = cycle 5 := by simp

example : thetaGraph [0, 0] = complete 2 := by simp

example : thetaGraph [0, 1] = complete 3 := by rw [thetaGraph_pair, show 2 + 0 + 1 = 3 from rfl,
  cycle_three]

example (m : ℕ) : cyclePendant m [1] = tadpole m 1 := by simp

example : doubleStar 2 3 = doubleStar 3 2 := by rw [doubleStar_comm]

example : spider [0, 2, 0, 3] = spider [2, 0, 3] := by simp

example : tadpole 2 4 = path 6 := by simp

example : lollipop 2 4 = path 6 := by simp

example (k : ℕ) : lollipop 3 k = tadpole 3 k := by rw [lollipop_three_eq_tadpole]

example (ks : List ℕ) : thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks) := by simp

example : tadpole 1 5 = path 6 := by simp

example : spider [2, 0, 3] = spider [2, 3] := by simpa using spider_append_zero_cons [2] [3]

example : cyclePendant 3 [1, 0] = cyclePendant 3 [1] := by
  simpa using cyclePendant_append_zero 3 [1]

example : cyclePendant 1 [3] = star 3 := by simp

example : cyclePendant 1 [2] = path 3 := by rw [cyclePendant_one, star_two]

example : spider [1, 3, 2] = spider [2, 1, 3] := spider_perm (by decide)

example (ks : List ℕ) : spider (ks ++ [0]) = spider (0 :: ks) :=
  spider_perm (List.perm_append_singleton 0 ks)

example (a b : ℕ) : spider [a, b] = spider [b, a] := spider_perm (List.Perm.swap b a [])

example : thetaGraph [1, 2, 3] = thetaGraph [3, 1, 2] := thetaGraph_perm (by decide)

example (xs : List ℕ) : thetaGraph (xs ++ [0]) = thetaGraph (0 :: xs) :=
  thetaGraph_perm (List.perm_append_singleton 0 xs)

example : thetaGraph [1, 1, 1, 1] = bipartite 2 4 := by
  rw [show ([1, 1, 1, 1] : List ℕ) = List.replicate 4 1 from rfl, thetaGraph_replicate_one]

example : thetaGraph [1, 1] = cycle 4 := by simp

example (n : ℕ) : thetaGraph (List.replicate n 1) = bipartite 2 n := by simp

example : IsConnected (prism 6) := by simp

example : IsConnected (hypercube 4) := by simp

example : ¬ IsConnected (cycle 3 ⊕g cycle 4) :=
  not_isConnected_disjUnion (by simp) (by simp)

example (G : IsoGraph) (h : IsConnected G) : IsConnected (G □g path 3) := by
  simp [h]

example : ¬ IsAcyclic (wheel 5) := by simp

example : IsTree (star 7) := by simp

example : ¬ IsConnected (empty 3) := by simp

example : IsConnected (book 4) := by simp

example (G : IsoGraph) (h : IsTree G) (hv : G.V = 10) : G.E = 9 := by
  have := h.E_add_one
  omega

example : (cocktailParty 4).cliqueNum = 4 := by simp

example : (book 5).indepNum = 5 := by simp

example : (wheel 7).indepNum = 3 := by simp

example : (complete 5)ᶜ.indepNum = 5 := by simp

example : (star 6).cliqueNum = 2 := by simp

example : (empty 3 ·g empty 4).indepNum = 12 := by simp

example : IsConnected (path 3 ⊠g cycle 4) :=
  isConnected_strongProduct (by simp) (by simp)

example : ¬ IsBipartite (complete 2 ·g complete 2) :=
  not_isBipartite_lexProduct (by simp) (by simp)

example : ¬ IsBipartite (path 2 ⊠g path 2) :=
  not_isBipartite_strongProduct (by simp) (by simp)

example : IsVertexTransitive petersenᶜ := by simp

example : IsVertexTransitive (hypercube 3 □g cycle 5) :=
  (isVertexTransitive_hypercube 3).cartesianProduct (isVertexTransitive_cycle 5)

example : IsVertexTransitive (triangular 5) := by simp

example : IsSRGWith (rook 3 3) 9 4 1 2 := isSRGWith_rook 3

example : IsSRGWith (triangular 5) 10 6 3 4 := isSRGWith_triangular 5 (by norm_num)

example : IsSRGWith (cocktailParty 4) 8 6 4 6 := isSRGWith_cocktailParty 4

example : IsSRGWith (bipartite 3 3) 6 3 0 3 := isSRGWith_bipartite 3

example : IsSRGWith petersenᶜ 10 6 3 4 := isSRGWith_petersen.compl

example : (degSequence (complete 5)).sum = 20 := by
  rw [sum_degSequence, E_complete]
  rfl

example : (degSequence petersen).length = 10 := by rw [degSequence_petersen]; rfl

example : petersen.E = 15 := by have := isSRGWith_petersen.two_mul_E; omega

example : (rook 3 3).E = 18 := by have := (isSRGWith_rook 3).two_mul_E; omega

example : degSequence (cocktailParty 3) = [4, 4, 4, 4, 4, 4] := by
  rw [degSequence_cocktailParty]
  rfl

example : petersenᶜ.E = 30 := by
  rw [E_compl_eq, V_petersen]
  have h : (10 : ℕ).choose 2 = 45 := rfl
  have := isSRGWith_petersen.two_mul_E
  omega

example : (lineGraph petersen).E = 30 := by
  rw [isSRGWith_petersen.E_lineGraph]
  rfl

example : (lineGraph (complete 5)).E = 30 := by simp [Nat.choose]

example : (triangular 5).E = 30 := by simp [Nat.choose]

example (G : IsoGraph) (h : G.V = 5) (h2 : G.E = 4) : Gᶜ.E = 6 := by
  rw [E_compl_eq, h, h2]
  rfl

example : degSequence (rook 3 3) = List.replicate 9 4 := by simp

example : 2 * (kneser 5 2).E = 30 := by
  rw [two_mul_E_kneser 5 (k := 2) (by norm_num)]
  rfl

example : (fan 4).V = 5 := by simp

example : (cocktailParty 4).V = 8 := by simp

example : (triangular 5).V = 10 := by simp [Nat.choose]

example : degSequence (hypercube 3) = List.replicate 8 3 := by simp

example : degSequence (complete 3 ⊗g complete 4) = List.replicate 12 6 := by
  rw [degSequence_tensorProduct (degSequence_complete 3) (degSequence_complete 4)]

example : degSequence (complete 2 ⊠g complete 2) = List.replicate 4 3 := by
  rw [degSequence_strongProduct (degSequence_complete 2) (degSequence_complete 2)]

example : 2 * (hypercube 4).E = 64 := by rw [two_mul_E_hypercube]; rfl

example : degSequence (cycle 5) = List.replicate 5 2 := by simp

example : degSequence (prism 3) = List.replicate 6 3 := by simp

example : (lineGraph (cycle 6)).E = 6 := by simp

example (G : IsoGraph) (h : IsVertexTransitive G) (hV : G.V = 7) (hE : G.E = 14) :
    degSequence G = List.replicate 7 4 := by
  have := degSequence_of_isVertexTransitive (k := 4) h (by omega) (by omega)
  rwa [hV] at this

example : (wheel 6).E = 12 := by simp

example : (prism 6).E = 18 := by simp

example : (rook 3 3).E = 18 := by simp [Nat.choose]

example : (hypercube 4).E = 32 := by
  have := E_hypercube 4
  omega

example : (completeMultipartite [1, 1, 3]).E = 7 := by
  have := E_completeMultipartite [1, 1, 3]
  simp [Nat.choose] at this
  omega

example : complete 3 ≠ complete 4 := by simp

example : cycle 4 ≠ complete 4 :=
  ne_of_E_ne (by rw [show (4 : ℕ) = 1 + 3 from rfl, E_cycle, E_complete]; decide)

example : complete 5 ≠ cycle 5 :=
  ne_of_degSequence_ne (by
    rw [degSequence_complete, show (5 : ℕ) = 2 + 3 from rfl, degSequence_cycle]
    decide)

/-- The six-cycle and two triangles share their order, size and degree sequence; connectivity
tells them apart. -/
example : cycle 6 ≠ cycle 3 ⊕g cycle 3 :=
  ne_of_isConnected (isConnected_cycle 5) (not_isConnected_disjUnion (by simp) (by simp))

example : cycle 6 ≠ complete 3 ⊕g complete 3 :=
  ne_of_indepNum_ne (by
    rw [show (6 : ℕ) = 3 + 3 from rfl, indepNum_cycle, indepNum_disjUnion, indepNum_complete]
    decide)

/-- The triangular prism and `K₃,₃` are both cubic on six vertices; bipartiteness separates
them. -/
example : prism 3 ≠ bipartite 3 3 :=
  (ne_of_isBipartite (isBipartite_bipartite 3 3) (not_isBipartite_prism_odd 0)).symm

example : path 5 ≠ cycle 5 := path_ne_cycle 4 2

example : petersen ≠ cycle 10 :=
  ne_of_degSequence_ne (by
    rw [degSequence_petersen, show (10 : ℕ) = 7 + 3 from rfl, degSequence_cycle]
    decide)

example : complete 3 ⊕g empty 1 ≠ star 3 :=
  ne_of_cliqueNum_ne (by
    rw [cliqueNum_disjUnion, cliqueNum_complete, cliqueNum_empty,
      show (3 : ℕ) = 2 + 1 from rfl, cliqueNum_star]
    decide)

/-- The cube and two disjoint copies of `K₄` are both cubic on eight vertices with twelve
edges. -/
example : hypercube 3 ≠ complete 4 ⊕g complete 4 :=
  ne_of_isConnected (isConnected_hypercube 3) (not_isConnected_disjUnion (by simp) (by simp))

example : complete 4 ≠ path 4 :=
  ne_of_diameter_ne (by
    rw [show (4 : ℕ) = 2 + 2 from rfl, diameter_complete, show (2 + 2 : ℕ) = 3 + 1 from rfl,
      diameter_path]
    decide)

example (G : IsoGraph) (h : G.V = 5) : G ≠ petersen := ne_of_V_ne (by rw [h, V_petersen]; decide)

example : petersen.diameter = 2 := by simp

example : (rook 3 3).diameter = 2 := diameter_rook 1 1

example : (cocktailParty 5).diameter = 2 := diameter_cocktailParty 3

example : (triangular 5).diameter = 2 := diameter_triangular (by norm_num)

/-- The Petersen graph is not the 10-cycle: their diameters (and degree sequences) differ. -/
example : petersen ≠ cycle 10 :=
  ne_of_diameter_ne (by
    rw [diameter_petersen, show (10 : ℕ) = 9 + 1 from rfl, diameter_cycle]
    decide)

example : (star 5).diameter = 2 := by simp

example : (wheel 6).diameter = 2 := by simp

example : (fan 5).diameter = 2 := diameter_fan 1

example : (book 4).diameter = 2 := by simp

/-- The star and the path on four vertices have the same order, size and edge count, and both are
trees; the diameter is what tells them apart. -/
example : star 3 ≠ path 4 :=
  ne_of_diameter_ne (by
    rw [show (3 : ℕ) = 1 + 2 from rfl, diameter_star, show (4 : ℕ) = 3 + 1 from rfl, diameter_path]
    decide)

example : IsConnected (complete 3 ⊕g complete 3)ᶜ := by simp

example : (complete 3 ⊕g complete 3)ᶜ.diameter = 2 :=
  diameter_compl_disjUnion (by simp) (by simp) (by simp [Nat.choose])

example : IsConnected (empty 5)ᶜ := by
  rw [compl_empty]
  exact isConnected_complete 4

/- A disconnected graph and a connected one of the same order and size: the six-cycle against
two triangles, once more. -/

example : ¬ IsConnected (cycle 3 ⊕g cycle 3) :=
  not_isConnected_disjUnion (by simp) (by simp)

example : degMultiset (star 4) = {4, 1, 1, 1, 1} := by
  rw [degMultiset_star]
  rfl

example : degMultiset (wheel 4) = {4, 3, 3, 3, 3} := by
  rw [show (4 : ℕ) = 1 + 3 from rfl, degMultiset_wheel]
  rfl

/- The complement of the five-cycle is a five-cycle, degree by degree. -/

example : degMultiset (cycle 5)ᶜ = Multiset.replicate 5 2 := by
  rw [compl_cycle_five, show (5 : ℕ) = 2 + 3 from rfl, degMultiset_cycle]

example : star 4 ≠ cycle 4 :=
  ne_of_degMultiset_ne (by
    rw [degMultiset_star, show (4 : ℕ) = 1 + 3 from rfl, degMultiset_cycle]
    decide)

/- The degree multiset does not separate everything: a triangle plus a square has the same
degrees as the seven-cycle, and only connectivity tells them apart. -/

example : degMultiset (cycle 3 ⊕g cycle 4) = degMultiset (cycle 7) := by
  rw [show (3 : ℕ) = 0 + 3 from rfl, show (4 : ℕ) = 1 + 3 from rfl, degMultiset_disjUnion,
    degMultiset_cycle, degMultiset_cycle, show (7 : ℕ) = 4 + 3 from rfl, degMultiset_cycle]
  rfl

example : cycle 3 ⊕g cycle 4 ≠ cycle 7 :=
  Ne.symm (ne_of_isConnected (isConnected_cycle 6)
    (not_isConnected_disjUnion (G := cycle 3) (H := cycle 4) (by simp) (by simp)))

example : degSequence (path 5) = [1, 1, 2, 2, 2] := degSequence_path 3

example : degMultiset (path 2) = {1, 1} := degMultiset_path 0

/- The star and the path on four vertices: same order, same size, both trees, and now separated
by the degree multiset as well as by the diameter. -/

example : star 3 ≠ path 4 :=
  ne_of_degMultiset_ne (by
    have h1 : degMultiset (star 3) = 3 ::ₘ Multiset.replicate 3 1 := degMultiset_star 3
    have h2 : degMultiset (path 4) = 1 ::ₘ 1 ::ₘ Multiset.replicate 2 2 := degMultiset_path 2
    rw [h1, h2]
    decide)

example : degSequence (star 4) = [1, 1, 1, 1, 4] := degSequence_star 4

example : degSequence (wheel 5) = [3, 3, 3, 3, 3, 5] := degSequence_wheel 2

example : degSequence (book 3) = [2, 2, 2, 4, 4] := degSequence_book 3

/- The three-rung ladder: the four corners have degree two and the two middle vertices degree
three. -/

example : degMultiset (ladder 3) = {2, 2, 3, 3, 2, 2} := by
  have h1 : degMultiset (path 3) = 1 ::ₘ 1 ::ₘ Multiset.replicate 1 2 := degMultiset_path 1
  have h2 : degMultiset (complete 2) = Multiset.replicate 2 1 := degMultiset_complete 2
  rw [show ladder 3 = path 3 □g complete 2 from rfl,
    degMultiset_cartesianProduct, h1, h2]
  decide

/- A star times an edge, in the lexicographic product: the hub sees everything. -/

example : degMultiset (complete 2 ·g empty 3) = Multiset.replicate 6 3 := by
  have h1 : degMultiset (complete 2) = Multiset.replicate 2 1 := degMultiset_complete 2
  have h2 : degMultiset (empty 3) = Multiset.replicate 3 0 := degMultiset_empty 3
  rw [degMultiset_lexProduct, h1, h2, V_empty]
  decide

/- The tensor product multiplies degrees, so each row of `K₃ × P₃` repeats the path's degrees
scaled by two. -/

example : degMultiset (complete 3 ⊗g path 3) = {2, 4, 2, 2, 4, 2, 2, 4, 2} := by
  have h1 : degMultiset (complete 3) = Multiset.replicate 3 2 := degMultiset_complete 3
  have h2 : degMultiset (path 3) = 1 ::ₘ 1 ::ₘ Multiset.replicate 1 2 := degMultiset_path 1
  rw [degMultiset_tensorProduct, h1, h2]
  decide

/- `K₂ ⊠ K₂` is `K₄`, and the degrees agree: `(1 + 1) * (1 + 1) - 1 = 3`. -/

example : degMultiset (complete 2 ⊠g complete 2) = Multiset.replicate 4 3 := by
  have h1 : degMultiset (complete 2) = Multiset.replicate 2 1 := degMultiset_complete 2
  rw [degMultiset_strongProduct, h1]
  decide

example : path 6 ≠ cycle 6 :=
  ne_of_degMultiset_ne (by
    have h1 : degMultiset (path 6) = 1 ::ₘ 1 ::ₘ Multiset.replicate 4 2 := degMultiset_path 4
    have h2 : degMultiset (cycle 6) = Multiset.replicate 6 2 := degMultiset_cycle 3
    rw [h1, h2]
    decide)

example : (bipartite 2 3 □g complete 4).cliqueNum = 4 := by
  rw [cliqueNum_cartesianProduct (by simp) (by simp), cliqueNum_complete,
    show bipartite 2 3 = bipartite (1 + 1) (2 + 1) from rfl, cliqueNum_bipartite]
  decide

example : (rook 3 3).cliqueNum = 3 := by simp

example : (complete 3 ⊗g complete 5).cliqueNum = 3 := by simp

example : (complete 3 ·g complete 5).cliqueNum = 15 := by simp

example : (empty 4 ·g complete 5).cliqueNum = 5 := by simp

example : rook 3 3 ≠ complete 3 ·g complete 3 :=
  ne_of_cliqueNum_ne (by simp)

example : complete 4 ⊗g complete 4 ≠ rook 3 3 :=
  ne_of_cliqueNum_ne (by simp)

example : (hypercube 4).diameter = 4 := diameter_hypercube 4

example : (ladder 5).diameter = 5 := diameter_ladder 4

example : (prism 6).diameter = 4 := diameter_prism 5

example : (rook 4 4).diameter = 2 := diameter_rook 2 2

/- `Q₄` and the `4 × 4` rook graph both have sixteen vertices and are both `4`-regular, but the
hypercube is far bigger across. -/

example : hypercube 4 ≠ rook 4 4 :=
  ne_of_diameter_ne (by rw [diameter_hypercube, diameter_rook]; decide)

example : (complete 3 ⊕g complete 3).diameter = 0 :=
  diameter_disjUnion (by simp) (by simp)

example : (complete 5).chromNum = 5 := by simp

example : (cycle 8).chromNum = 2 := chromNum_cycle_even 3

example : (cycle 7).chromNum = 3 := chromNum_cycle_odd 2

example : (path 9).chromNum = 2 := by simp

example : (hypercube 4).chromNum = 2 := by simp

example : (bipartite 3 4).chromNum = 2 := by simp

example : (path 3 □g path 4).chromNum = 2 := by simp

example : (empty 7).chromNum = 1 := by simp

example : (complete 4 ⊕g cycle 5).chromNum = 4 := by
  rw [chromNum_disjUnion, chromNum_complete, show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]
  decide

example : (cycle 3 ⊗g complete 5).chromNum ≤ 3 := by
  refine le_trans (chromNum_tensorProduct_le _ _) ?_
  rw [show (cycle 3).chromNum = 3 from chromNum_cycle_odd 0]
  exact min_le_left _ _

/- The Petersen graph contains a 5-cycle, so two colours are not enough. -/

example : 3 ≤ petersen.chromNum := three_le_chromNum (by simp)

/- A `3 × 3` rook graph contains a triangle. -/

example : 3 ≤ (rook 3 3).chromNum := le_trans (by simp) (cliqueNum_le_chromNum _)

/- `C₃ ⊔ C₃` and `C₆` are both 2-regular on six vertices with six edges; the chromatic number
tells them apart. -/

example : cycle 3 ⊕g cycle 3 ≠ cycle 6 :=
  ne_of_chromNum_ne (by
    rw [chromNum_disjUnion, show (cycle 3).chromNum = 3 from chromNum_cycle_odd 0,
      show (cycle 6).chromNum = 2 from chromNum_cycle_even 2]
    decide)

example : (complete 3 ∇g cycle 5).chromNum = 6 := by
  rw [chromNum_join, chromNum_complete, show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]

example : (cycle 4 ∇g cycle 4).chromNum = 4 := by
  rw [chromNum_join, show (cycle 4).chromNum = 2 from chromNum_cycle_even 1]

example : (complete 4 □g cycle 5).chromNum = 4 := by
  rw [chromNum_cartesianProduct (by simp) (by simp), chromNum_complete,
    show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]
  decide

example : (cycle 5 ·g complete 2).chromNum ≤ 6 := by
  have h := chromNum_lexProduct_le (cycle 5) (complete 2)
  rw [show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1, chromNum_complete] at h
  omega

/- The independence number bounds the chromatic number from below. -/

example (n : ℕ) : n + 1 ≤ (cocktailParty (n + 1)).chromNum := by
  have h := V_le_chromNum_mul_indepNum (cocktailParty (n + 1))
  rw [V_cocktailParty, indepNum_cocktailParty] at h
  omega

example : (wheel 7).chromNum = 4 := chromNum_wheel_odd 2

example : (cocktailParty 4).chromNum = 4 := by simp

/-! ### Turán at work -/

/-- Mantel's bound is attained by the balanced complete bipartite graph. -/
example (m : ℕ) : 4 * (bipartite m m).E = (bipartite m m).V ^ 2 := by
  rw [E_bipartite, V_bipartite]
  ring

/-- Turán's bound is attained by the complete graph `K_r`, whose clique number is exactly `r`. -/
example (n : ℕ) :
    2 * (n + 1) * (complete (n + 1)).E = ((n + 1) - 1) * (complete (n + 1)).V ^ 2 := by
  have key : 2 * (n + 1).choose 2 = (n + 1) * n := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self n
    have hc : (n + 1) * n = n * (n + 1) := Nat.mul_comm _ _
    omega
  rw [E_complete, V_complete, Nat.add_sub_cancel]
  calc 2 * (n + 1) * (n + 1).choose 2 = (n + 1) * (2 * (n + 1).choose 2) := by ring
    _ = (n + 1) * ((n + 1) * n) := by rw [key]
    _ = n * (n + 1) ^ 2 := by ring

/-- The Petersen graph is well under the Mantel threshold, as it must be: it has no triangle. -/
example : 4 * petersen.E ≤ petersen.V ^ 2 :=
  petersen.four_mul_E_le_V_sq_of_girth_ne_three (by rw [girth_petersen]; omega)

/-- Edge counting alone certifies a triangle in `K₃`. -/
example : (complete 3).girth = 3 := girth_eq_three_of_V_sq_lt _ (by simp)

/-- ... and in the triangular graph `T(5)`, which has `10` vertices and `30` edges. -/
example : (triangular 5).girth = 3 := girth_eq_three_of_V_sq_lt _ (by simp [Nat.choose])

/-- The complement bound at work on `C₅`, whose independence number is two: `40 ≤ 25 + 20`. -/
example : 4 * (cycle 5).V.choose 2 ≤ (cycle 5).V ^ 2 + 4 * (cycle 5).E :=
  four_mul_choose_le _ (by rw [show (5 : ℕ) = 2 + 3 from rfl, indepNum_cycle])

/-- Turán with `r = 2` detects that `K₄` has a clique on more than two vertices. -/
example : 2 < (complete 4).cliqueNum := lt_cliqueNum_of_lt _ (by omega) (by simp; decide)

example : (cycle 5).V = 5 ∧ (cycle 5).cliqueNum < 3 ∧ (cycle 5).indepNum < 3 := by
  refine ⟨by simp, by rw [cliqueNum_cycle_five]; omega, ?_⟩
  rw [show (5 : ℕ) = 2 + 3 from rfl, indepNum_cycle]
  omega

/-- The Petersen graph, being triangle-free on ten vertices, must contain three pairwise
non-adjacent vertices. -/
example : 3 ≤ petersen.indepNum :=
  petersen.three_le_indepNum_of_girth_ne_three (by rw [V_petersen]; omega)
    (by rw [girth_petersen]; omega)

/-- So must the cube graph, which is bipartite on eight vertices. -/
example : 3 ≤ (hypercube 3).indepNum :=
  (hypercube 3).three_le_indepNum_of_isBipartite (by simp) (isBipartite_hypercube 3)

/-- A graph on `70` vertices has four mutually adjacent or four mutually non-adjacent vertices. -/
example (G : IsoGraph) (h : 70 ≤ G.V) : 4 ≤ G.cliqueNum ∨ 4 ≤ G.indepNum :=
  G.le_cliqueNum_or_le_indepNum (by rw [show (4 : ℕ) + 4 = 8 from rfl,
    show Nat.choose 8 4 = 70 from rfl]; exact h)

/-! ### The vertex cover number -/

attribute [simp] IsoGraph.coverNum_add_indepNum

@[simp] theorem coverNum_bipartite (m n : ℕ) : (bipartite m n).coverNum = min m n := by
  rw [coverNum_eq, V_bipartite, indepNum_bipartite]
  omega

@[simp] theorem coverNum_star (n : ℕ) : (star n).coverNum = min 1 n := by
  rw [star_eq_bipartite, coverNum_bipartite]

@[simp] theorem coverNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).coverNum = ds.sum - (ds.max?).getD 0 := by
  rw [coverNum_eq, V_completeMultipartite, indepNum_completeMultipartite]

attribute [simp] IsoGraph.coverNum_le_E

/-! ### The cover number at work -/

example : (cycle 6).coverNum = 3 := by rw [show (6 : ℕ) = 3 + 3 from rfl, coverNum_cycle]

example : (complete 5).coverNum = 4 := by simp

example : (bipartite 3 4).coverNum = 3 := by simp

/-- `|E| ≤ τ·Δ` is an equality on stars, where a single vertex covers everything. -/
example (n : ℕ) :
    (star (n + 1)).E = (star (n + 1)).coverNum * (star (n + 1)).maxDeg := by
  rw [E_star, maxDeg_star, coverNum_star, Nat.min_eq_left (by omega), one_mul]

/-! ### Consequences for the named families -/

/-- The independence number of a rook's graph is at most `min m n`: a set of squares no two of
which share a row or a column is a partial permutation matrix.  This is the hard direction of
`α(K_m □ K_n) = min m n`, and it comes out of the clique–coclique bound because the rook's graph
is vertex-transitive with `ω = max m n`. -/
theorem indepNum_rook_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (rook m n).indepNum ≤ min m n := by
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_rook m n)
  rw [cliqueNum_rook hm hn, V_rook] at h
  have hmax : 0 < max m n := lt_of_lt_of_le hm (le_max_left m n)
  refine Nat.le_of_mul_le_mul_right ?_ hmax
  calc (rook m n).indepNum * max m n ≤ m * n := h
    _ = min m n * max m n := (min_mul_max m n).symm

/-- Hypercubes: an independent set in `Q_n` has at most `2^(n-1)` vertices (and the even-weight
vertices show this is sharp). -/
theorem two_mul_indepNum_hypercube_le (n : ℕ) :
    2 * (hypercube (n + 1)).indepNum ≤ 2 ^ (n + 1) := by
  have hE : 0 < (hypercube (n + 1)).E := by
    have h := E_hypercube (n + 1)
    have hpos : 0 < (n + 1) * 2 ^ (n + 1) :=
      Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
    omega
  have := two_mul_indepNum_le_V (isVertexTransitive_hypercube (n + 1)) hE
  rwa [V_hypercube] at this

/-- Kneser graphs: `α(K(n, k)) · ω(K(n, k)) ≤ C(n, k)`. -/
theorem indepNum_mul_cliqueNum_kneser_le (n k : ℕ) :
    (kneser n k).indepNum * (kneser n k).cliqueNum ≤ n.choose k := by
  have := indepNum_mul_cliqueNum_le_V (isVertexTransitive_kneser n k)
  rwa [V_kneser] at this

/-- The Petersen graph is triangle-free, so its independence number is at most `5`.
(The true value is `4`; the clique–coclique bound is off by one here.) -/
theorem indepNum_petersen_le : petersen.indepNum ≤ 5 := by
  have hE : 0 < petersen.E := by
    have h : 2 * petersen.E = 30 := by
      rw [two_mul_E_kneser 5 (k := 2) (by norm_num)]; rfl
    omega
  have := two_mul_indepNum_le_V isVertexTransitive_petersen hE
  rw [V_petersen] at this
  omega

/-! Tightness: the complete graph, the cocktail-party graph and the rook's graph all meet the
bound with equality. -/

example (n : ℕ) : (complete (n + 1)).indepNum * (complete (n + 1)).cliqueNum = (complete (n + 1)).V := by
  simp

example (n : ℕ) :
    (cocktailParty (n + 1)).indepNum * (cocktailParty (n + 1)).cliqueNum
      = (cocktailParty (n + 1)).V := by
  rw [indepNum_cocktailParty, cliqueNum_cocktailParty, V_cocktailParty]

/-- The star `K_{1,3}` has `α · ω = 3 · 2 > 4 = |V|`, so it is not vertex-transitive. -/
example : ¬ IsVertexTransitive (star 3) := by
  refine not_isVertexTransitive_of_V_lt ?_
  rw [indepNum_star, cliqueNum_star, V_star]
  norm_num

/-- Unbalanced complete bipartite graphs are not vertex-transitive. -/
example (m n : ℕ) (h : m + 2 ≤ n) : ¬ IsVertexTransitive (bipartite (m + 1) (n + 1)) := by
  refine not_isVertexTransitive_of_V_lt ?_
  rw [indepNum_bipartite, cliqueNum_bipartite, V_bipartite]
  have hmax : max (m + 1) (n + 1) = n + 1 := Nat.max_eq_right (by omega)
  rw [hmax]
  omega

/-- Paley graphs are Cayley graphs of the additive group of the field, so they are
vertex-transitive. -/
@[simp] theorem isVertexTransitive_paley (q : ℕ) [NeZero q] [Fact q.Prime] :
    IsVertexTransitive (paley q) :=
  CGraph.isVertexTransitive_paley q

/-- `ω(Paley 13) ≤ 3` (the true value is `3`), from `ω² ≤ 13`.  Since `Paley 13` is
self-complementary this bounds its independence number too. -/
theorem cliqueNum_paley_thirteen_le : (paley 13).cliqueNum ≤ 3 := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h := cliqueNum_sq_le_V_of_compl_eq (isVertexTransitive_paley 13) compl_paley_thirteen
  rw [V_paley] at h
  by_contra hcon
  push_neg at hcon
  have : 4 * 4 ≤ (paley 13).cliqueNum ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul hcon hcon
  omega

theorem indepNum_paley_thirteen_le : (paley 13).indepNum ≤ 3 := by
  rw [indepNum_eq_cliqueNum_of_compl_eq compl_paley_thirteen]
  exact cliqueNum_paley_thirteen_le

/-- `ω(Paley 17) ≤ 4`, from `ω² ≤ 17`. -/
theorem cliqueNum_paley_seventeen_le : (paley 17).cliqueNum ≤ 4 := by
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have h := cliqueNum_sq_le_V_of_compl_eq (isVertexTransitive_paley 17) compl_paley_seventeen
  rw [V_paley] at h
  by_contra hcon
  push_neg at hcon
  have : 5 * 5 ≤ (paley 17).cliqueNum ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul hcon hcon
  omega

/-- No graph on `6` vertices is self-complementary. -/
example (G : IsoGraph) (h : G.V = 6) : Gᶜ ≠ G := fun hc ↦ by
  have := V_mod_four_of_compl_eq hc
  rw [h] at this
  omega

/-! ### The table -/

attribute [simp] IsoGraph.domNum_empty IsoGraph.domNum_complete IsoGraph.domNum_star

/-- `γ(Petersen) ≥ 3` (the true value is `3`). -/
theorem three_le_domNum_petersen : 3 ≤ petersen.domNum := by
  have h := le_domNum_of_regular (G := petersen) (k := 3) maxDeg_petersen
  rw [V_petersen] at h
  omega

example : (star 5).domNum = 1 := by simp

example : (empty 4).domNum = 4 := by simp

example : (complete 7).domNum = 1 := by simp

/-! ### The radius table -/

attribute [simp] IsoGraph.domNum_wheel

@[simp] theorem radius_hypercube (n : ℕ) : (hypercube n).radius = n := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_hypercube n),
    diameter_hypercube]

@[simp] theorem radius_petersen : petersen.radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive isVertexTransitive_petersen, diameter_petersen]

@[simp] theorem radius_rook (m n : ℕ) : (rook (m + 2) (n + 2)).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_rook _ _), diameter_rook]

@[simp] theorem radius_cocktailParty (n : ℕ) : (cocktailParty (n + 2)).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (by simp), diameter_cocktailParty]

theorem radius_triangular {n : ℕ} (hn : 4 ≤ n) : (triangular n).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_triangular n),
    diameter_triangular hn]

theorem radius_bipartite_self (n : ℕ) : (bipartite (n + 2) (n + 2)).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_bipartite_self _),
    diameter_bipartite_self]

@[simp] theorem radius_star (n : ℕ) : (star (n + 1)).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one (by rw [V_star]; omega)]
  exact domNum_star (n + 1)

/-- The hub of a wheel dominates it, so the wheel has radius one. -/
@[simp] theorem radius_wheel (n : ℕ) : (wheel (n + 1)).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one (by rw [V_wheel]; omega)]
  exact domNum_wheel (n + 1)

@[simp] theorem radius_prism (n : ℕ) : (prism (n + 1)).radius = (n + 1) / 2 + 1 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_prism _), diameter_prism]

theorem radius_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_paley q),
    diameter_paley q hq hq5]

/-! ### Consequences -/

/-- A graph of radius `r` needs at least `2r` steps to be crossed in the worst case, so a graph
with a large diameter has a large radius. -/
example (G : IsoGraph) (h : 5 ≤ G.diameter) : 3 ≤ G.radius := by
  have := G.diameter_le_two_mul_radius
  omega

example : (complete 5).radius = 1 := by simp

example : (star 4).radius = 1 := by simp

example (n : ℕ) : (cycle (2 * n + 1)).radius = n := by
  rw [show 2 * n + 1 = n + n + 1 from by omega, radius_cycle]
  omega

@[simp] theorem cliqueCount_prism_even (m : ℕ) : (prism (2 * m)).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_prism_even m)

@[simp] theorem cliqueCount_star (n : ℕ) : (star n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_star n)

@[simp] theorem cliqueCount_petersen : petersen.cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_petersen]
  omega

@[simp] theorem cliqueCount_bipartite (m n : ℕ) : (bipartite m n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_bipartite m n)

@[simp] theorem cliqueCount_hypercube (n : ℕ) : (hypercube n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_hypercube n)

example : (complete 5).cliqueCount 3 = 10 := by rw [cliqueCount_complete]; decide

example : (cycle 6).cliqueCount 3 = 0 := cliqueCount_cycle_even 3

example : (empty 6).indepCount 3 = 20 := by rw [indepCount_empty]; decide

example : (complete 4).indepCount 2 = 0 := by
  show (complete 4).indepCount (0 + 2) = 0
  simp

@[simp] theorem indepCount_star (n k : ℕ) :
    (star n).indepCount (k + 2) = n.choose (k + 2) := by
  rw [star_def, CGraph.star, ← bipartite_def, indepCount_bipartite]
  simp [Nat.choose_eq_zero_of_lt]

example : (bipartite 4 6).indepCount 3 = 24 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, indepCount_bipartite]; decide

example : (complete 4 ⊕g complete 5).cliqueCount 3 = 14 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cliqueCount_disjUnion, cliqueCount_complete,
    cliqueCount_complete]
  decide

@[simp] theorem numComponents_star (n : ℕ) : (star n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_star n)

@[simp] theorem numComponents_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_bipartite m n)

@[simp] theorem numComponents_hypercube (n : ℕ) : (hypercube n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_hypercube n)

@[simp] theorem numComponents_wheel (n : ℕ) : (wheel (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_wheel n)

@[simp] theorem numComponents_prism (n : ℕ) : (prism (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_prism n)

@[simp] theorem numComponents_ladder (n : ℕ) : (ladder (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_ladder n)

@[simp] theorem numComponents_rook (m n : ℕ) : (rook (m + 1) (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_rook m n)

example : (cycle 5 ⊕g path 4).numComponents = 2 := by simp

example : (empty 7).numComponents = 7 := by simp

example : (cycle 5 ∇g empty 3).numComponents = 1 := by
  refine numComponents_join ?_ ?_ <;> simp

example : (cycle 5).numComponents < (cycle 5).V := numComponents_lt_V_of_E_pos (by simp)

example : (empty 3 □g empty 4).numComponents = 12 := by simp

example : IsConnected (hypercube 2) := by
  refine isConnected_of_V_le_two_mul_minDeg (G := hypercube 2) (by simp) ?_
  simp

example : (complete 4).autCount = 24 := by simp [Nat.factorial]

example : (empty 3).autCount = 6 := by simp [Nat.factorial]

/-! ### Automorphisms versus symmetry -/

example : 5 ≤ (cycle 5).autCount := by
  have := V_le_autCount_of_isVertexTransitive (G := cycle 5) (by simp) (by simp)
  simpa using this

example : 10 ≤ (cycle 5).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (G := cycle 5) (by simp)
  simpa using this

example : 24 ≤ (hypercube 3).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (G := hypercube 3) (by simp)
  simpa [show (hypercube 3).E = 12 from rfl] using this

example : 30 ≤ (kneser 5 2).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (G := kneser 5 2) (by simp)
  simpa [show (kneser 5 2).E = 15 from rfl] using this

/-- There is no cubic graph on seven vertices. -/
example (G : IsoGraph) (h : degSequence G = List.replicate 7 3) : False := by
  have hV : G.V = 7 := by rw [← length_degSequence, h, List.length_replicate]
  have := even_V_of_degSequence_replicate (by decide) h
  rw [hV] at this
  exact (by decide : ¬ Even 7) this

/-! ### Automorphisms of the constructions -/

example : 12 ≤ (complete 3 ⊕g complete 4).autCount := by
  have := autCount_mul_le_autCount_disjUnion (complete 3) (complete 4)
  simp [Nat.factorial] at this
  omega

example : (empty 5).V - (empty 5).E ≤ (empty 5).numComponents := by simp

example : ¬ (complete 1 ⊕g complete 1).IsConnected := by
  apply not_isConnected_of_E_add_one_lt_V
  simp

example : (mycielskian (cycle 5)).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian _ (by simp), cliqueNum_cycle_five, max_self]

example : (complete 3 ⊠g complete 3).E = 36 := by
  rw [E_strongProduct]
  simp

example : (complete 2 ·g empty 3).E = 9 := by
  rw [E_lexProduct]
  simp

example : (path 2 ⊠g path 2).E = 6 := by
  rw [E_strongProduct]
  simp

example : (paley 9).E = 27 := by
  rw [paley_nine_eq_lexProduct, E_lexProduct]
  simp

/-! ### Domination in disjoint unions, joins and cartesian products -/

attribute [simp] IsoGraph.domNum_disjUnion

theorem domNum_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).domNum = 2 := by
  rw [bipartite_eq_join]
  exact domNum_join_eq_two (by simp) (by simp) (by simp) (by simp)

example : (complete 3 ⊕g complete 4).domNum = 2 := by simp

example : (empty 5 ⊕g complete 3).domNum = 6 := by simp

example : (bipartite 3 3).domNum = 2 := domNum_bipartite 1 1

example : (complete 4 □g complete 4).domNum ≤ 4 := by
  have := domNum_cartesianProduct_le (complete 4) (complete 4)
  simpa using this

/-! ### The radius of a cartesian product -/

example : (cycle 5 □g cycle 5).radius = 4 := by
  rw [radius_cartesianProduct (by simp) (by simp)]
  simp

example : (rook 4 4).radius = 2 := by
  rw [rook, radius_cartesianProduct (by simp) (by simp)]
  simp

example : (cycle 5 ⊠g cycle 5).diameter ≤ 4 := by
  simp

example : (empty 3 ·g complete 2).domNum = 3 := by
  rw [domNum_lexProduct _ (by simp), domNum_empty]

example : (star 3 ⊠g star 4).domNum = 1 :=
  domNum_strongProduct_eq_one (by simp) (by simp)

example : (cycle 5 ·g complete 4).domNum = (cycle 5).domNum :=
  domNum_lexProduct _ (by simp)

example : 4 ≤ (cycle 5 ⊠g cycle 5).indepNum := by
  have h5 : (cycle 5).indepNum = 2 := by simp
  have h := indepNum_mul_indepNum_le_indepNum_strongProduct (cycle 5) (cycle 5)
  rw [h5] at h
  omega

example : 3 ≤ (complete 3 ⊗g complete 3).indepNum := by
  have h := V_mul_indepNum_le_indepNum_tensorProduct (complete 3) (complete 3)
  rw [V_complete, indepNum_complete] at h
  omega

/-! ### Colouring the strong product -/

/-- The strong product of complete graphs shows the upper bound is attained. -/
example : (complete 3 ⊠g complete 4).chromNum = 12 := by
  rw [strongProduct_complete, chromNum_complete]

example : 4 ≤ (cycle 5 ⊠g cycle 5).chromNum := by
  have h := cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (cycle 5) (cycle 5)
  have h5 : (cycle 5).cliqueNum = 2 := cliqueNum_cycle_five
  rw [h5] at h
  omega

example : (cycle 5 ⊠g cycle 5).chromNum ≤ 9 := by
  have h := chromNum_strongProduct_le (cycle 5) (cycle 5)
  have h5 : (cycle 5).chromNum = 3 := by
    have := chromNum_cycle_odd 1
    norm_num at this
    exact this
  rw [h5] at h
  omega

example : (cycle 4 ⊗g path 3).chromNum = 2 := by
  refine chromNum_tensorProduct_eq_two ?_ ?_ ?_
  · simpa using isBipartite_cycle_even 2
  · simp
  · simp

example : (cycle 5 ·g complete 3).coverNum = 13 := by
  rw [coverNum_lexProduct, V_cycle, V_complete, indepNum_complete]
  norm_num [show ((cycle 5).indepNum) = 2 from by simp]

example : (complete 3 □g complete 3).coverNum ≤ 8 := by
  have h := coverNum_cartesianProduct_le (complete 3) (complete 3)
  simpa using h

example : 6 ≤ (complete 3 □g complete 3).coverNum := by
  have h := V_mul_coverNum_le_coverNum_cartesianProduct (complete 3) (complete 3)
  simpa using h

/-- An edgeless graph attains the upper bound: `γ(E_n) = n` and `γ(K_n) = 1`. -/
example (n : ℕ) : (empty (n + 1)).domNum + (empty (n + 1))ᶜ.domNum = (n + 1) + 1 := by
  rw [compl_empty, domNum_empty, domNum_complete]

/-- The complement of `2 K₃` is `K₃,₃`, which two vertices dominate. -/
example : (complete 3 ⊕g complete 3)ᶜ.domNum ≤ 2 :=
  domNum_compl_disjUnion_le_two (by simp) (by simp)

/-- The complete graph attains the upper bound: `ω = n` and `α = 1`. -/
example (n : ℕ) :
    (complete (n + 1)).cliqueNum + (complete (n + 1)).indepNum = (complete (n + 1)).V + 1 := by
  rw [cliqueNum_complete, indepNum_complete, V_complete]
  omega

/-- So does the edgeless graph, with the roles swapped. -/
example (n : ℕ) :
    (empty (n + 1)).cliqueNum + (empty (n + 1)).indepNum = (empty (n + 1)).V + 1 := by
  rw [cliqueNum_empty, indepNum_empty, V_empty]
  omega

/-- The Petersen graph is far from either extreme: `ω = 2` and `α = 4`. -/
example : petersen.cliqueNum + petersen.indepNum ≤ 11 := by
  have h := petersen.cliqueNum_add_indepNum_le_V_add_one
  rwa [V_petersen] at h

/-- The five-cycle: `ω = α = 2`, comfortably between `3` and `6`. -/
example : (cycle 5).cliqueNum + (cycle 5).indepNum = 4 := by
  rw [cliqueNum_cycle_five]
  norm_num [show ((cycle 5).indepNum) = 2 from by simp]

/-- The five-cycle is self-complementary, and `τ(C₅) = 3`; the bound `2·5 - 3 = 7` is not tight
here, while the lower bound `5 - 1 = 4` is beaten too. -/
example : (cycle 5).coverNum + (cycle 5)ᶜ.coverNum = 6 := by
  rw [compl_cycle_five, coverNum_cycle]

/-- The complete graph attains the lower bound: `τ(Kₙ) = n - 1` and `τ(Kₙᶜ) = 0`. -/
example (n : ℕ) :
    (complete (n + 1)).coverNum + (complete (n + 1))ᶜ.coverNum = n := by
  rw [compl_complete, coverNum_complete, coverNum_empty]
  omega

/-- The five-cycle has `τ = 3`, so `χ(C₅) ≤ 4` — one more than the true value. -/
example : (cycle 5).chromNum ≤ 4 := by
  have h := (cycle 5).chromNum_le_coverNum_add_one
  rwa [coverNum_cycle] at h

@[simp] theorem isRegularWith_petersen : petersen.IsRegularWith 3 :=
  isRegularWith_of_degSequence degSequence_petersen

@[simp] theorem isRegularWith_hypercube (n : ℕ) : (hypercube n).IsRegularWith n :=
  isRegularWith_of_degSequence (degSequence_hypercube n)

@[simp] theorem isRegularWith_prism (n : ℕ) : (prism (n + 3)).IsRegularWith 3 :=
  isRegularWith_of_degSequence (degSequence_prism n)

@[simp] theorem isRegularWith_cocktailParty (n : ℕ) :
    (cocktailParty n).IsRegularWith (2 * n - 2) :=
  isRegularWith_of_degSequence (degSequence_cocktailParty n)

@[simp] theorem isRegularWith_bipartite_self (n : ℕ) : (bipartite n n).IsRegularWith n :=
  isRegularWith_of_degSequence (degSequence_bipartite_self n)

@[simp] theorem isRegularWith_rook (m n : ℕ) :
    (rook m n).IsRegularWith ((n - 1) + (m - 1)) :=
  isRegularWith_of_degSequence (degSequence_rook m n)

theorem isRegularWith_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (kneser n k).IsRegularWith ((n - k).choose k) :=
  isRegularWith_of_degSequence (degSequence_kneser (n := n) hk)

/-- The Petersen graph is `3`-regular on ten vertices, so it has fifteen edges. -/
example : petersen.E = 15 := by
  have h := isRegularWith_petersen.two_mul_E
  rw [V_petersen] at h
  omega

/-- `C₅ □ K₃` is `(2 + 2)`-regular. -/
example : (cycle 5 □g complete 3).IsRegularWith 4 := by
  have h := (isRegularWith_cycle 2).cartesianProduct (isRegularWith_complete 3)
  norm_num at h
  exact h

/-- The complement of a `k`-regular graph on `n` vertices is `(n - 1 - k)`-regular: for Petersen
that is the triangular graph `T(5)`, which is `6`-regular. -/
example : petersenᶜ.IsRegularWith 6 := by
  have h := isRegularWith_petersen.compl
  rwa [V_petersen] at h

/-- The cube `Q₃` is `3`-regular on eight vertices, so it has twelve edges. -/
example : (hypercube 3).E = 12 := by
  have h := (isRegularWith_hypercube 3).two_mul_E
  rw [V_hypercube] at h
  omega

/-- The triangular graph is the line graph of a complete graph, hence `(2n - 4)`-regular.
Unlike `isSRGWith_triangular` this needs no lower bound on `n`. -/
@[simp] theorem isRegularWith_triangular (n : ℕ) :
    (triangular n).IsRegularWith (2 * n - 4) := by
  have h := (isRegularWith_complete n).lineGraph
  rw [lineGraph_complete_eq_triangular] at h
  have hk : 2 * (n - 1) - 2 = 2 * n - 4 := by omega
  rwa [hk] at h

example : (lineGraph petersen).IsRegularWith 4 := (isRegularWith_petersen).lineGraph

example : (lineGraph petersen).V = 15 := by
  rw [V_lineGraph]
  have := isSRGWith_petersen.two_mul_E
  omega

/-- The Petersen graph is `3`-regular on ten vertices, so its line graph is `4`-regular on
fifteen vertices and has thirty edges. -/
example : (lineGraph petersen).E = 30 := by
  rw [isRegularWith_petersen.E_lineGraph, V_petersen]
  rfl

/-- The line graph of the cube `Q₃` is `4`-regular on twelve vertices, so it has 24 edges. -/
example : (lineGraph (hypercube 3)).E = 24 := by
  rw [(isRegularWith_hypercube 3).E_lineGraph, V_hypercube]
  rfl

example : (triangular 5).IsRegularWith 6 := isRegularWith_triangular 5

example : petersen.chromNum ≤ 4 := isRegularWith_petersen.chromNum_le

example : petersenᶜ.E = 30 := by
  have h := isRegularWith_petersen.two_mul_E_compl
  rw [V_petersen] at h
  omega

/-- No graph on five vertices is `3`-regular. -/
example (G : IsoGraph) (hV : G.V = 5) : ¬ G.IsRegularWith 3 := fun h ↦ by
  have := h.two_dvd_V (by omega)
  omega

example : (cycle 5).indepNum * 3 ≥ 5 := by
  have h := (isRegularWith_cycle 2).V_le_indepNum_mul (by simp)
  rw [V_cycle] at h
  omega

/-! ### Extremal degrees of the regular families

Every graph in the regularity table has `Δ = δ = k`, so `IsRegularWith.maxDeg_eq` and
`IsRegularWith.minDeg_eq` finish off the `maxDeg` and `minDeg` tables.  The vertex sets are
shifted where necessary so that they are nonempty. -/

theorem isRegularWith_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).IsRegularWith ((q - 1) / 2) :=
  (isSRGWith_paley q hq).isRegularWith

@[simp] theorem maxDeg_triangular (n : ℕ) : maxDeg (triangular (n + 2)) = 2 * n := by
  rw [(isRegularWith_triangular (n + 2)).maxDeg_eq
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))]
  omega

@[simp] theorem minDeg_triangular (n : ℕ) : minDeg (triangular (n + 2)) = 2 * n := by
  rw [(isRegularWith_triangular (n + 2)).minDeg_eq
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))]
  omega

@[simp] theorem maxDeg_rook (m n : ℕ) : maxDeg (rook (m + 1) (n + 1)) = n + m := by
  rw [(isRegularWith_rook (m + 1) (n + 1)).maxDeg_eq (by rw [V_rook]; positivity)]
  omega

@[simp] theorem minDeg_rook (m n : ℕ) : minDeg (rook (m + 1) (n + 1)) = n + m := by
  rw [(isRegularWith_rook (m + 1) (n + 1)).minDeg_eq (by rw [V_rook]; positivity)]
  omega

@[simp] theorem maxDeg_prism (n : ℕ) : maxDeg (prism (n + 3)) = 3 :=
  (isRegularWith_prism n).maxDeg_eq (by rw [V_prism]; omega)

@[simp] theorem minDeg_prism (n : ℕ) : minDeg (prism (n + 3)) = 3 :=
  (isRegularWith_prism n).minDeg_eq (by rw [V_prism]; omega)

@[simp] theorem maxDeg_cocktailParty (n : ℕ) : maxDeg (cocktailParty (n + 1)) = 2 * n := by
  rw [(isRegularWith_cocktailParty (n + 1)).maxDeg_eq (by rw [V_cocktailParty]; omega)]
  omega

@[simp] theorem minDeg_cocktailParty (n : ℕ) : minDeg (cocktailParty (n + 1)) = 2 * n := by
  rw [(isRegularWith_cocktailParty (n + 1)).minDeg_eq (by rw [V_cocktailParty]; omega)]
  omega

@[simp] theorem maxDeg_bipartite_self (n : ℕ) : maxDeg (bipartite (n + 1) (n + 1)) = n + 1 :=
  (isRegularWith_bipartite_self (n + 1)).maxDeg_eq (by rw [V_bipartite]; omega)

@[simp] theorem minDeg_bipartite_self (n : ℕ) : minDeg (bipartite (n + 1) (n + 1)) = n + 1 :=
  (isRegularWith_bipartite_self (n + 1)).minDeg_eq (by rw [V_bipartite]; omega)

theorem maxDeg_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    maxDeg (kneser n k) = (n - k).choose k :=
  (isRegularWith_kneser n hk).maxDeg_eq (by rw [V_kneser]; exact Nat.choose_pos hkn)

theorem minDeg_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    minDeg (kneser n k) = (n - k).choose k :=
  (isRegularWith_kneser n hk).minDeg_eq (by rw [V_kneser]; exact Nat.choose_pos hkn)

theorem maxDeg_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    maxDeg (paley q) = (q - 1) / 2 :=
  (isRegularWith_paley q hq).maxDeg_eq (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q))

theorem minDeg_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    minDeg (paley q) = (q - 1) / 2 :=
  (isRegularWith_paley q hq).minDeg_eq (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q))

example : maxDeg (triangular 5) = 6 := maxDeg_triangular 3

example : minDeg (rook 3 3) = 4 := minDeg_rook 2 2

/-- The Kneser graph `K(5, 2)` is the Petersen graph, and both are `3`-regular. -/
example : maxDeg (kneser 5 2) = 3 := by
  rw [maxDeg_kneser 5 2 (by omega) (by omega)]
  rfl

/-- Colouring the edges of a star is colouring the vertices of a complete graph. -/
@[simp] theorem edgeChromNum_star (n : ℕ) : (star n).edgeChromNum = n := by
  rw [edgeChromNum_eq, lineGraph_star, chromNum_complete]

/-- `χ'(Petersen) ≥ 3`; the true value is `4`, which needs the fact that the Petersen graph has
no perfect matching decomposition. -/
example : 3 ≤ petersen.edgeChromNum :=
  isRegularWith_petersen.le_edgeChromNum (by rw [V_petersen]; omega)

example : petersen.edgeChromNum ≤ 5 := by
  have h := petersen.edgeChromNum_le_two_mul_maxDeg_sub_one
  rw [maxDeg_petersen] at h
  omega

example : (star 4).edgeChromNum = 4 := edgeChromNum_star 4

/-- A star has a single edge available to any matching. -/
@[simp] theorem matchNum_star (n : ℕ) : (star n).matchNum = min n 1 := by
  rw [matchNum_eq, lineGraph_star, indepNum_complete]

/-- The Petersen graph has at most five independent edges, and `|E| ≤ χ' ν` then forces
`χ' ≥ 3`. -/
example : 2 * petersen.matchNum ≤ 10 := by
  have h := petersen.two_mul_matchNum_le_V
  rwa [V_petersen] at h

example : (star 4).matchNum = 1 := by rw [matchNum_star]; omega

example : (complete 2 ⊕g complete 2).matchNum = 2 := by
  rw [matchNum_disjUnion]
  have h : (complete 2).matchNum = 1 := by
    rw [← star_one, matchNum_star]
    omega
  omega

/-- `L(K_{m,n})` is the rook's graph, so a matching of the complete bipartite graph is a
partial permutation matrix and there are at most `min m n` of them. -/
theorem matchNum_bipartite_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (bipartite m n).matchNum ≤ min m n := by
  rw [matchNum_eq, lineGraph_bipartite]
  exact indepNum_rook_le m n hm hn

example : (cycle 5).matchNum = 2 := by rw [show (5 : ℕ) = 2 + 3 by ring, matchNum_cycle]

example : (cycle 6).edgeChromNum = 2 := by
  rw [show (6 : ℕ) = 2 * 1 + 4 by ring, edgeChromNum_cycle_even]

/-- `C₅` is not `2`-edge-colourable even though it is `2`-regular. -/
example : (cycle 5).edgeChromNum = 3 := by
  rw [show (5 : ℕ) = 2 * 1 + 3 by ring, edgeChromNum_cycle_odd]

example : petersen.matchNum + petersen.indepNum ≤ 10 := by
  have h := petersen.matchNum_add_indepNum_le_V
  rwa [V_petersen] at h

/-- `C₅` has `ν = α = 2`, one short of the bound. -/
example : (cycle 5).matchNum + (cycle 5).indepNum = 4 := by
  rw [show (5 : ℕ) = 2 + 3 by ring, matchNum_cycle, indepNum_cycle]

/-- A star is a case where `ν + α = n` is tight. -/
example : (star 4).matchNum + (star 4).indepNum = 5 := by
  rw [matchNum_star, indepNum_star]
  omega

/-- Two triangles of the triangular graph meet in a vertex, so `T(n)` has girth three. -/
@[simp] theorem girth_triangular (n : ℕ) : (triangular (n + 4)).girth = 3 :=
  (isSRGWith_triangular (n + 4) (by omega)).girth_eq_three
    (Nat.choose_pos (by omega)) (by omega) (by omega)

@[simp] theorem girth_johnson_two (n : ℕ) : (johnson (n + 4) 2).girth = 3 :=
  (isSRGWith_johnson_two (n + 4) (by omega)).girth_eq_three
    (Nat.choose_pos (by omega)) (by omega) (by omega)

/-- From `K(6,2)` onwards a Kneser graph has three pairwise disjoint pairs, hence a triangle;
`K(5,2)` is the Petersen graph, whose girth is five. -/
@[simp] theorem girth_kneser_two (n : ℕ) : (kneser (n + 6) 2).girth = 3 :=
  (isSRGWith_kneser_two (n + 6)).girth_eq_three (Nat.choose_pos (by omega))
    (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

/-- Paley graphs on at least nine vertices have `ℓ = (q - 5)/4 > 0`. -/
theorem girth_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    (paley q).girth = 3 :=
  (isSRGWith_paley q hq).girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem girth_lineGraph_petersen : (IsoGraph.lineGraph petersen).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_petersen])

@[simp] theorem girth_lineGraph_hypercube (n : ℕ) :
    (IsoGraph.lineGraph (hypercube (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_hypercube]; omega)

example : (triangular 5).girth = 3 := girth_triangular 1

example : (kneser 6 2).girth = 3 := girth_kneser_two 0

example : (paley 13).girth = 3 := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact girth_paley 13 rfl (by omega)

/-- A complete bipartite graph is covered by `max m n` edges and singletons. -/
@[simp] theorem cliqueCoverNum_bipartite (m n : ℕ) :
    (bipartite m n).cliqueCoverNum = max m n := by
  rw [cliqueCoverNum_eq, compl_bipartite, chromNum_disjUnion, chromNum_complete,
    chromNum_complete]

@[simp] theorem cliqueCoverNum_star (n : ℕ) : (star n).cliqueCoverNum = max 1 n :=
  cliqueCoverNum_bipartite 1 n

example : (empty 4).cliqueCoverNum = 4 := cliqueCoverNum_empty 4

example : (cycle 5).indepNum ≤ (cycle 5).cliqueCoverNum := indepNum_le_cliqueCoverNum _

/-- The clique cover bound is tight for a disjoint union of triangles. -/
example : (complete 3 ⊕g complete 3).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_disjUnion, show (3 : ℕ) = 2 + 1 by ring, cliqueCoverNum_complete]

/-- The complement of a complete multipartite graph is a disjoint union of cliques, so covering
it takes as many cliques as the largest part has vertices. -/
@[simp] theorem cliqueCoverNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).cliqueCoverNum = ds.foldr max 0 := by
  induction ds with
  | nil => rw [completeMultipartite_nil, cliqueCoverNum_empty, List.foldr_nil]
  | cons d ds ih =>
    rw [cliqueCoverNum_eq, compl_completeMultipartite_cons, chromNum_disjUnion,
      chromNum_complete, ← cliqueCoverNum_eq, ih, List.foldr_cons]

/-- The complement of a cocktail party graph is a perfect matching, which two cliques cover. -/
@[simp] theorem cliqueCoverNum_cocktailParty (n : ℕ) :
    (cocktailParty (n + 1)).cliqueCoverNum = 2 := by
  have h : ∀ m : ℕ, (List.replicate (m + 1) 2).foldr max 0 = 2 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [List.replicate_succ, List.foldr_cons, ih]; omega
  show (completeMultipartite (List.replicate (n + 1) 2)).cliqueCoverNum = 2
  rw [cliqueCoverNum_completeMultipartite, h]

example : (cocktailParty 3).cliqueCoverNum = 2 := cliqueCoverNum_cocktailParty 2

/-- For the cocktail party graph `n ≤ χ θ` reads `2n ≤ n · 2`, so it is tight. -/
example : (cocktailParty 3).V ≤ (cocktailParty 3).chromNum * (cocktailParty 3).cliqueCoverNum :=
  V_le_chromNum_mul_cliqueCoverNum _

example : petersen.numComponents ≤ petersen.cliqueCoverNum := numComponents_le_cliqueCoverNum _

/-! ### Graphs whose colouring numbers meet their clique numbers

`ω ≤ χ` and `α ≤ θ` always hold, and for several of the named families they are equalities.
Odd cycles show that this is not automatic: `C₅` has `ω = 2` but `χ = 3`. -/

/-- The rook's graph is a Cartesian product of cliques, and the chromatic number of a Cartesian
product is the larger of the two factors' chromatic numbers. -/
@[simp] theorem chromNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).chromNum = max (m + 1) (n + 1) := by
  show (complete (m + 1) □g complete (n + 1)).chromNum = _
  rw [chromNum_cartesianProduct (by rw [V_complete]; omega) (by rw [V_complete]; omega),
    chromNum_complete, chromNum_complete]

/-- Both numbers count the largest row or column. -/
theorem chromNum_eq_cliqueNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).chromNum = (rook (m + 1) (n + 1)).cliqueNum := by
  rw [chromNum_rook, cliqueNum_rook (by omega) (by omega)]

/-- Both numbers count the nonempty parts. -/
theorem chromNum_eq_cliqueNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).chromNum = (completeMultipartite ds).cliqueNum := by
  rw [chromNum_completeMultipartite, cliqueNum_completeMultipartite]

/-- Dually, both the independence number and the clique cover number of a complete multipartite
graph are the size of its largest part: the parts themselves are the optimal objects on both
sides. -/
theorem indepNum_eq_cliqueCoverNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (completeMultipartite ds).cliqueCoverNum := by
  induction ds with
  | nil => rw [completeMultipartite_nil, indepNum_empty, cliqueCoverNum_empty]
  | cons d ds ih =>
    rw [completeMultipartite_cons, indepNum_join, cliqueCoverNum_join, indepNum_empty,
      cliqueCoverNum_empty, ih]

example : (rook 3 3).chromNum = 3 := by
  rw [show (3 : ℕ) = 2 + 1 by ring, chromNum_rook]
  omega

example (n : ℕ) : (hypercube (n + 1)).chromNum = (hypercube (n + 1)).cliqueNum := by
  refine chromNum_eq_cliqueNum_of_isBipartite (isBipartite_hypercube (n + 1)) ?_
  have h := E_hypercube (n + 1)
  have hpos : 0 < (n + 1) * 2 ^ (n + 1) :=
    Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
  omega

example (m n : ℕ) : (bipartite (m + 1) (n + 1)).indepNum
    = (bipartite (m + 1) (n + 1)).cliqueCoverNum := by
  rw [indepNum_bipartite, cliqueCoverNum_bipartite]

/-! ### The named families that contain a cycle -/

@[simp] theorem not_isAcyclic_petersen : ¬ IsAcyclic petersen :=
  not_isAcyclic_of_girth_pos (by rw [girth_petersen]; omega)

@[simp] theorem not_isAcyclic_bipartite (m n : ℕ) : ¬ IsAcyclic (bipartite (m + 2) (n + 2)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_bipartite]; omega)

@[simp] theorem not_isAcyclic_hypercube (n : ℕ) : ¬ IsAcyclic (hypercube (n + 2)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_hypercube]; omega)

@[simp] theorem not_isAcyclic_cocktailParty (n : ℕ) : ¬ IsAcyclic (cocktailParty (n + 3)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_cocktailParty]; omega)

@[simp] theorem not_isAcyclic_book (n : ℕ) : ¬ IsAcyclic (book (n + 1)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_book]; omega)

@[simp] theorem not_isAcyclic_triangular (n : ℕ) : ¬ IsAcyclic (triangular (n + 4)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_triangular]; omega)

@[simp] theorem not_isAcyclic_johnson_two (n : ℕ) : ¬ IsAcyclic (johnson (n + 4) 2) :=
  not_isAcyclic_of_girth_pos (by rw [girth_johnson_two]; omega)

@[simp] theorem not_isAcyclic_kneser_two (n : ℕ) : ¬ IsAcyclic (kneser (n + 6) 2) :=
  not_isAcyclic_of_girth_pos (by rw [girth_kneser_two]; omega)

theorem not_isAcyclic_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : 3 ≤ max m n) :
    ¬ IsAcyclic (rook m n) :=
  not_isAcyclic_of_girth_pos (by rw [girth_rook hm hn h]; omega)

theorem not_isAcyclic_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    ¬ IsAcyclic (paley q) :=
  not_isAcyclic_of_girth_pos (by rw [girth_paley q hq hq9]; omega)

@[simp] theorem not_isTree_petersen : ¬ IsTree petersen :=
  not_isTree_of_girth_pos (by rw [girth_petersen]; omega)

@[simp] theorem not_isTree_bipartite (m n : ℕ) : ¬ IsTree (bipartite (m + 2) (n + 2)) :=
  not_isTree_of_girth_pos (by rw [girth_bipartite]; omega)

@[simp] theorem not_isTree_hypercube (n : ℕ) : ¬ IsTree (hypercube (n + 2)) :=
  not_isTree_of_girth_pos (by rw [girth_hypercube]; omega)

example : ¬ IsAcyclic (hypercube 4) := by simp

example : (star 5).cliqueNum = 2 := cliqueNum_of_isTree (isTree_star 5) (by rw [V_star]; omega)

example (G : IsoGraph) (h : IsTree G) : G.cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isAcyclic ((isTree_iff_isConnected_and_isAcyclic G).1 h).2

/-! ### The chromatic index of the complete bipartite graphs and the stars

Both are cases where the line graph is one of the named families in its own right: the line graph
of `K_{m,n}` is the rook's graph `K_m □ K_n` and the line graph of a star is complete, so the
chromatic index can be read straight off the chromatic-number table. -/

/-- **König's edge-colouring theorem for complete bipartite graphs**: `χ'(K_{m,n}) = max m n`,
which is exactly the maximum degree.  Here it is a consequence of `χ(K_m □ K_n) = max m n`. -/
@[simp] theorem edgeChromNum_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).edgeChromNum = max (m + 1) (n + 1) := by
  rw [edgeChromNum_eq, lineGraph_bipartite, chromNum_rook]

/-- Stars attain the trivial lower bound `Δ ≤ χ'`. -/
theorem edgeChromNum_star_eq_maxDeg (n : ℕ) :
    (star (n + 1)).edgeChromNum = maxDeg (star (n + 1)) := by
  rw [edgeChromNum_star, maxDeg_star]

theorem le_edgeChromNum_hypercube (n : ℕ) : n ≤ (hypercube n).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (hypercube n)
  rwa [maxDeg_hypercube] at h

theorem three_le_edgeChromNum_petersen : 3 ≤ petersen.edgeChromNum := by
  have h := maxDeg_le_edgeChromNum petersen
  rwa [maxDeg_petersen] at h

/-! ### The triangular graphs as line graphs of complete graphs

`J(n, 2)` is the line graph of `Kₙ`, so the general line-graph bounds turn into statements about
cliques, colourings and independent sets in the triangular graphs. -/

/-- The `n - 1` edges at a vertex of `Kₙ` form a clique of `J(n, 2)`. -/
theorem sub_one_le_cliqueNum_johnson_two (n : ℕ) : n - 1 ≤ (johnson n 2).cliqueNum := by
  have h := maxDeg_le_cliqueNum_lineGraph (complete n)
  rwa [maxDeg_complete, lineGraph_complete] at h

theorem sub_one_le_chromNum_johnson_two (n : ℕ) : n - 1 ≤ (johnson n 2).chromNum :=
  le_trans (sub_one_le_cliqueNum_johnson_two n) (cliqueNum_le_chromNum _)

theorem chromNum_johnson_two_le (n : ℕ) : (johnson n 2).chromNum ≤ 2 * (n - 1) - 1 := by
  have h := edgeChromNum_complete_le n
  rwa [edgeChromNum_eq, lineGraph_complete] at h

/-- An independent set of `J(n, 2)` is a matching of `Kₙ`, so it has at most `n / 2` members. -/
theorem two_mul_indepNum_johnson_two_le (n : ℕ) : 2 * (johnson n 2).indepNum ≤ n := by
  have h := two_mul_matchNum_le_V (complete n)
  rwa [matchNum_eq, lineGraph_complete, V_complete] at h

theorem sub_one_le_chromNum_triangular (n : ℕ) : n - 1 ≤ (triangular n).chromNum :=
  sub_one_le_chromNum_johnson_two n

example : (bipartite 3 5).edgeChromNum = 5 := by
  rw [show (3 : ℕ) = 2 + 1 by ring, show (5 : ℕ) = 4 + 1 by ring, edgeChromNum_bipartite]
  omega

example : (star 6).edgeChromNum = 6 := by simp

example : 4 ≤ (johnson 5 2).cliqueNum := sub_one_le_cliqueNum_johnson_two 5

/-! ### The Kneser graphs on pairs

`K(n, 2)` is strongly regular with `μ = C(n - 3, 2) > 0` once `n ≥ 5`, which settles its metric
structure, and it is the complement of the triangular graph `T(n)`, which converts the line-graph
bounds of the previous section into bounds on its cliques and independent sets. -/

theorem diameter_kneser_two (m : ℕ) : (kneser (m + 5) 2).diameter = 2 := by
  refine (isSRGWith_kneser_two (m + 5)).diameter_eq_two ?_ ?_
  · rw [show m + 5 - 3 = m + 2 from by omega]
    exact Nat.choose_pos (by omega)
  · have h1 : (m + 5).choose 2 = (m + 4) + (m + 4).choose 2 := by
      rw [Nat.choose_succ_succ (m + 4) 1, Nat.choose_one_right]
    have h2 : (m + 4).choose 2 = (m + 3) + (m + 3).choose 2 := by
      rw [Nat.choose_succ_succ (m + 3) 1, Nat.choose_one_right]
    rw [show m + 5 - 2 = m + 3 from by omega]
    omega

@[simp] theorem isConnected_kneser_two (m : ℕ) : IsConnected (kneser (m + 5) 2) :=
  isConnected_of_diameter_ne_zero (by rw [diameter_kneser_two]; omega)

@[simp] theorem numComponents_kneser_two (m : ℕ) : (kneser (m + 5) 2).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_kneser_two m)

@[simp] theorem radius_kneser_two (m : ℕ) : (kneser (m + 5) 2).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_kneser _ _),
    diameter_kneser_two]

/-- A clique of `K(n, 2)` is a set of pairwise disjoint pairs, that is, a matching of `Kₙ`. -/
theorem two_mul_cliqueNum_kneser_two_le (n : ℕ) : 2 * (kneser n 2).cliqueNum ≤ n := by
  have h := two_mul_indepNum_johnson_two_le n
  rwa [show johnson n 2 = (kneser n 2)ᶜ from triangular_eq_compl_kneser n,
    indepNum_compl] at h

/-- **Erdős–Ko–Rado, lower bound.**  The `n - 1` pairs through a fixed point are pairwise
intersecting, so they form an independent set of `K(n, 2)`. -/
theorem sub_one_le_indepNum_kneser_two (n : ℕ) : n - 1 ≤ (kneser n 2).indepNum := by
  have h := sub_one_le_cliqueNum_johnson_two n
  rwa [show johnson n 2 = (kneser n 2)ᶜ from triangular_eq_compl_kneser n,
    cliqueNum_compl] at h

theorem sub_one_le_cliqueCoverNum_kneser_two (n : ℕ) :
    n - 1 ≤ (kneser n 2).cliqueCoverNum :=
  le_trans (sub_one_le_indepNum_kneser_two n) (indepNum_le_cliqueCoverNum _)

@[simp] theorem not_isBipartite_kneser_two (n : ℕ) : ¬ IsBipartite (kneser (n + 6) 2) := by
  intro hb
  have h := four_le_girth_of_isBipartite hb (not_isAcyclic_kneser_two n)
  rw [girth_kneser_two] at h
  omega

theorem three_le_chromNum_kneser_two (n : ℕ) : 3 ≤ (kneser (n + 6) 2).chromNum := by
  by_contra hc
  exact not_isBipartite_kneser_two n (isBipartite_iff_chromNum_le_two.2 (by omega))

example : petersen.diameter = 2 := diameter_kneser_two 0

example : 5 ≤ (kneser 6 2).indepNum := sub_one_le_indepNum_kneser_two 6

/-! ### König's matching theorem for complete bipartite graphs

Every edge colouring of `G` splits its edges into `χ'(G)` matchings, so `|E| ≤ χ'(G) · ν(G)`.
For `K_{m,n}` the chromatic index is `max m n`, and `min m n · max m n = m · n`, so the bound
already forces `ν ≥ min m n` — which together with the clique–coclique bound on the rook's graph
pins down the matching number, the independence number of `K_m □ K_n`, and `ν = τ`. -/

theorem min_le_matchNum_bipartite (m n : ℕ) :
    min (m + 1) (n + 1) ≤ (bipartite (m + 1) (n + 1)).matchNum := by
  have h := E_le_edgeChromNum_mul_matchNum (bipartite (m + 1) (n + 1))
  rw [E_bipartite, edgeChromNum_bipartite] at h
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < max (m + 1) (n + 1) by omega)
  calc max (m + 1) (n + 1) * min (m + 1) (n + 1)
      = (m + 1) * (n + 1) := by rw [Nat.mul_comm]; exact min_mul_max _ _
    _ ≤ max (m + 1) (n + 1) * (bipartite (m + 1) (n + 1)).matchNum := h

@[simp] theorem matchNum_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).matchNum = min (m + 1) (n + 1) :=
  le_antisymm (matchNum_bipartite_le _ _ (by omega) (by omega)) (min_le_matchNum_bipartite m n)

/-- **König's theorem** for the complete bipartite graphs: the maximum size of a matching equals
the minimum size of a vertex cover. -/
theorem matchNum_eq_coverNum_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).matchNum = (bipartite (m + 1) (n + 1)).coverNum := by
  rw [matchNum_bipartite, coverNum_bipartite]

/-- `K_{n,n}` has a perfect matching. -/
theorem two_mul_matchNum_bipartite_self (n : ℕ) :
    2 * (bipartite (n + 1) (n + 1)).matchNum = (bipartite (n + 1) (n + 1)).V := by
  rw [matchNum_bipartite, V_bipartite]
  omega

/-- A maximum independent set of the rook's graph is a maximum matching of `K_{m,n}`, so the
bound `α(K_m □ K_n) ≤ min m n` from the clique–coclique inequality is attained. -/
@[simp] theorem indepNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).indepNum = min (m + 1) (n + 1) := by
  have h := matchNum_bipartite m n
  rwa [matchNum_eq, lineGraph_bipartite] at h

@[simp] theorem coverNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).coverNum = (m + 1) * (n + 1) - min (m + 1) (n + 1) := by
  have h := coverNum_add_indepNum (rook (m + 1) (n + 1))
  rw [indepNum_rook, V_rook] at h
  omega

theorem indepNum_mul_cliqueNum_eq_V_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).indepNum * (rook (m + 1) (n + 1)).cliqueNum
      = (rook (m + 1) (n + 1)).V := by
  rw [indepNum_rook, cliqueNum_rook (by omega) (by omega), V_rook, min_mul_max]

example : (bipartite 3 5).matchNum = 3 := by
  rw [show (3 : ℕ) = 2 + 1 by ring, show (5 : ℕ) = 4 + 1 by ring, matchNum_bipartite]
  omega

example : (rook 4 6).indepNum = 4 := by
  rw [show (4 : ℕ) = 3 + 1 by ring, show (6 : ℕ) = 5 + 1 by ring, indepNum_rook]
  omega

example (n : ℕ) : (bipartite (n + 1) (n + 1)).matchNum = n + 1 := by simp

example : (cycle 5).coverNum ≤ 4 := by
  have h := (cycle 5).coverNum_le_two_mul_matchNum
  rw [show (5 : ℕ) = 2 + 3 by ring, matchNum_cycle] at h
  omega

example (G : IsoGraph) (h : G.matchNum = 0) : G.coverNum = 0 := by
  have := G.coverNum_le_two_mul_matchNum
  omega

@[simp] theorem isSelfComplementary_paley_thirteen : IsSelfComplementary (paley 13) :=
  compl_paley_thirteen

@[simp] theorem isSelfComplementary_paley_seventeen : IsSelfComplementary (paley 17) :=
  compl_paley_seventeen

@[simp] theorem not_isSelfComplementary_petersen : ¬ IsSelfComplementary petersen := by
  intro h
  have h2 := h.V_mod_four
  rw [V_petersen] at h2
  omega

@[simp] theorem not_isSelfComplementary_hypercube (n : ℕ) :
    ¬ IsSelfComplementary (hypercube (n + 3)) := by
  intro h
  refine h.not_isBipartite ?_ (isBipartite_hypercube _)
  rw [V_hypercube]
  have h2 : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  norm_num at h2
  omega

theorem not_isSelfComplementary_bipartite {m n : ℕ} (h : 5 ≤ m + n) :
    ¬ IsSelfComplementary (bipartite m n) := by
  intro hs
  exact hs.not_isBipartite (by rw [V_bipartite]; omega) (isBipartite_bipartite m n)

/-! ### The self-complementary Paley graphs -/

@[simp] theorem E_paley_thirteen : (paley 13).E = 39 := by
  have h := isSelfComplementary_paley_thirteen.two_mul_E
  rw [V_paley, show (13 : ℕ).choose 2 = 78 from by decide] at h
  omega

@[simp] theorem E_paley_seventeen : (paley 17).E = 68 := by
  have h := isSelfComplementary_paley_seventeen.two_mul_E
  rw [V_paley, show (17 : ℕ).choose 2 = 136 from by decide] at h
  omega

theorem indepNum_paley_seventeen_le : (paley 17).indepNum ≤ 4 := by
  have h := isSelfComplementary_paley_seventeen.cliqueNum_eq_indepNum
  have h2 := cliqueNum_paley_seventeen_le
  omega

theorem five_le_chromNum_paley_thirteen : 5 ≤ (paley 13).chromNum := by
  have h := V_le_chromNum_mul_indepNum (paley 13)
  rw [V_paley] at h
  by_contra hc
  have h2 : (paley 13).chromNum * (paley 13).indepNum ≤ 4 * 3 :=
    Nat.mul_le_mul (by omega) indepNum_paley_thirteen_le
  omega

theorem five_le_chromNum_paley_seventeen : 5 ≤ (paley 17).chromNum := by
  have h := V_le_chromNum_mul_indepNum (paley 17)
  rw [V_paley] at h
  by_contra hc
  have h2 : (paley 17).chromNum * (paley 17).indepNum ≤ 4 * 4 :=
    Nat.mul_le_mul (by omega) indepNum_paley_seventeen_le
  omega

theorem chromNum_paley_thirteen_le : (paley 13).chromNum ≤ 7 := by
  have h := isSelfComplementary_paley_thirteen.two_mul_chromNum_le
  rw [V_paley] at h
  omega

theorem chromNum_paley_seventeen_le : (paley 17).chromNum ≤ 9 := by
  have h := isSelfComplementary_paley_seventeen.two_mul_chromNum_le
  rw [V_paley] at h
  omega

theorem five_le_cliqueCoverNum_paley_thirteen : 5 ≤ (paley 13).cliqueCoverNum := by
  have h := isSelfComplementary_paley_thirteen.chromNum_eq_cliqueCoverNum
  have h2 := five_le_chromNum_paley_thirteen
  omega

theorem five_le_cliqueCoverNum_paley_seventeen : 5 ≤ (paley 17).cliqueCoverNum := by
  have h := isSelfComplementary_paley_seventeen.chromNum_eq_cliqueCoverNum
  have h2 := five_le_chromNum_paley_seventeen
  omega

example : (cycle 5).E = 5 := by
  have h := isSelfComplementary_cycle_five.two_mul_E
  rw [V_cycle, show (5 : ℕ).choose 2 = 10 from by decide] at h
  omega

example : ¬ IsSelfComplementary (cycle 6) := by
  intro h
  have h2 := h.V_mod_four
  rw [V_cycle] at h2
  omega

example : ¬ IsSelfComplementary (bipartite 3 3) :=
  not_isSelfComplementary_bipartite (by omega)

example : 3 ≤ (paley 13).chromNum :=
  isSelfComplementary_paley_thirteen.three_le_chromNum (by rw [V_paley]; omega)

end IsoGraph
