import IsoGraph.Values.Identities.Tables
import IsoGraph.ForMathlib.Nat

/-!
# The simp set at work: the bounds, on the quotient

From here to the end of the library the pattern is the same: a statement about the isomorphism
class, proved by `simp` from the tables already established and from the `CGraph`-level theorems
transferred by `@[toIsoGraph]`.  Nothing below descends to a representative.

This module carries the general bounds across — Turán, Ramsey, Gallai, the clique–coclique bound,
König's theorem for the complete bipartite graphs, the two-approximation for vertex covers — and
fills in the columns they govern: the vertex cover number, the domination number, the radius, the
clique, component and automorphism counts, the edge chromatic number, the matching number and the
clique cover number.
-/

set_option autoImplicit false

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

/-! ### Turán's theorem -/

/-- **Mantel's theorem**: `4·|E| ≤ |V|²` for a triangle-free graph. -/
theorem four_mul_E_le_V_sq (G : IsoGraph) (h : G.cliqueNum ≤ 2) : 4 * G.E ≤ G.V ^ 2 := by
  have := G.two_mul_mul_E_le (r := 2) (by omega) h
  omega

/-- A graph with more than `|V|²/4` edges contains a triangle, so its girth is `3`. -/
theorem three_le_cliqueNum_of_V_sq_lt (G : IsoGraph) (h : G.V ^ 2 < 4 * G.E) :
    3 ≤ G.cliqueNum := by
  by_contra hcon
  exact absurd (G.four_mul_E_le_V_sq (by omega)) (by omega)

theorem girth_eq_three_of_V_sq_lt (G : IsoGraph) (h : G.V ^ 2 < 4 * G.E) : G.girth = 3 :=
  girth_eq_three_iff.2 (G.three_le_cliqueNum_of_V_sq_lt h)

/-- The general contrapositive of Turán: beating the Turán density forces a bigger clique. -/
theorem lt_cliqueNum_of_lt (G : IsoGraph) {r : ℕ} (hr : 0 < r)
    (h : (r - 1) * G.V ^ 2 < 2 * r * G.E) : r < G.cliqueNum := by
  by_contra hcon
  exact absurd (G.two_mul_mul_E_le hr (Nat.not_lt.1 hcon)) (by omega)

/-- Mantel's bound applies to every graph of girth at least four, and to every bipartite graph. -/
theorem four_mul_E_le_V_sq_of_girth_ne_three (G : IsoGraph) (h : G.girth ≠ 3) :
    4 * G.E ≤ G.V ^ 2 := by
  refine G.four_mul_E_le_V_sq ?_
  by_contra hcon
  exact h (girth_eq_three_iff.2 (by omega))

theorem four_mul_E_le_V_sq_of_isBipartite (G : IsoGraph) (h : IsBipartite G) :
    4 * G.E ≤ G.V ^ 2 :=
  G.four_mul_E_le_V_sq (cliqueNum_le_two_of_isBipartite h)

/-! ### Turán in the complement: few independent vertices means many edges -/

/-- Turán applied to `Gᶜ`: a graph with independence number at most `r` has few *non*-edges. -/
theorem two_mul_mul_E_compl_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.indepNum ≤ r) :
    2 * r * Gᶜ.E ≤ (r - 1) * G.V ^ 2 := by
  have hV : Gᶜ.V = G.V := V_compl G
  have := Gᶜ.two_mul_mul_E_le hr (by rwa [cliqueNum_compl])
  rwa [hV] at this

/-- Consequently a graph with independence number at most `r` has *many* edges: the `Gᶜ` bound
turns into a lower bound on `G.E` through `|E(G)| + |EGᶜ| = C(|V|, 2)`. -/
theorem two_mul_mul_choose_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.indepNum ≤ r) :
    2 * r * G.V.choose 2 ≤ (r - 1) * G.V ^ 2 + 2 * r * G.E := by
  have hsum := G.E_compl_add
  have hb := G.two_mul_mul_E_compl_le hr h
  calc 2 * r * G.V.choose 2 = 2 * r * Gᶜ.E + 2 * r * G.E := by
        rw [← Nat.mul_add, hsum]
    _ ≤ (r - 1) * G.V ^ 2 + 2 * r * G.E := Nat.add_le_add_right hb _

/-- **Mantel in the complement**: a graph with no three pairwise non-adjacent vertices has at
least `C(n, 2) - n²/4` edges. -/
theorem four_mul_choose_le (G : IsoGraph) (h : G.indepNum ≤ 2) :
    4 * G.V.choose 2 ≤ G.V ^ 2 + 4 * G.E := by
  have := G.two_mul_mul_choose_le (r := 2) (by omega) h
  omega

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

/-! ### The Ramsey number `R(3, 3)` -/

/-- The same for a graph of girth other than three, in particular any bipartite graph. -/
theorem three_le_indepNum_of_girth_ne_three (G : IsoGraph) (h : 6 ≤ G.V) (hg : G.girth ≠ 3) :
    3 ≤ G.indepNum := by
  refine G.three_le_indepNum_of_cliqueNum_le_two h ?_
  by_contra hcon
  exact hg (girth_eq_three_iff.2 (by omega))

theorem three_le_indepNum_of_isBipartite (G : IsoGraph) (h : 6 ≤ G.V) (hb : IsBipartite G) :
    3 ≤ G.indepNum :=
  G.three_le_indepNum_of_cliqueNum_le_two h (cliqueNum_le_two_of_isBipartite hb)

/-- Either way round: on six vertices a graph or its complement has girth three. -/
theorem girth_eq_three_or_girth_compl_eq_three (G : IsoGraph) (h : 6 ≤ G.V) :
    G.girth = 3 ∨ Gᶜ.girth = 3 := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · exact Or.inl (girth_eq_three_iff.2 h')
  · exact Or.inr (girth_eq_three_iff.2 (by rwa [cliqueNum_compl]))

/-! ### `R(3, 3) = 6`: five vertices are not enough -/

/-- The five-cycle has neither a triangle nor three pairwise non-adjacent vertices, so the bound
`R(3, 3) ≤ 6` cannot be improved. -/
theorem cliqueNum_cycle_five : (cycle 5).cliqueNum = 2 := by
  have hle : (cycle 5).cliqueNum ≤ 2 := by
    by_contra hcon
    have := girth_eq_three_iff.2 (show 3 ≤ (cycle 5).cliqueNum by omega)
    rw [girth_cycle_five] at this
    omega
  have hge : 2 ≤ (cycle 5).cliqueNum := two_le_cliqueNum_of_E_pos (by simp)
  omega

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

/-! ### Ramsey numbers in general -/

/-- The diagonal case, in the crude but memorable form `4^s` — since `C(2s, s) ≤ 2^(2s)`. -/
theorem le_cliqueNum_or_le_indepNum_of_pow (G : IsoGraph) {s : ℕ} (h : 4 ^ s ≤ G.V) :
    s ≤ G.cliqueNum ∨ s ≤ G.indepNum := by
  refine G.le_cliqueNum_or_le_indepNum (le_trans ?_ h)
  calc (s + s).choose s ≤ 2 ^ (s + s) := Nat.choose_le_two_pow _ _
    _ = 4 ^ s := by rw [← two_mul, pow_mul]; norm_num

/-- A graph on `70` vertices has four mutually adjacent or four mutually non-adjacent vertices. -/
example (G : IsoGraph) (h : 70 ≤ G.V) : 4 ≤ G.cliqueNum ∨ 4 ≤ G.indepNum :=
  G.le_cliqueNum_or_le_indepNum (by rw [show (4 : ℕ) + 4 = 8 from rfl]; simpa using h)

/-! ### The vertex cover number -/

attribute [simp] IsoGraph.coverNum_add_indepNum

theorem coverNum_eq (G : IsoGraph) : G.coverNum = G.V - G.indepNum := by
  have := G.coverNum_add_indepNum
  omega

theorem indepNum_eq_V_sub_coverNum (G : IsoGraph) : G.indepNum = G.V - G.coverNum := by
  have := G.coverNum_add_indepNum
  omega

theorem coverNum_le_V (G : IsoGraph) : G.coverNum ≤ G.V := by
  have := G.coverNum_add_indepNum
  omega

/-- In the complement, Gallai reads `τGᶜ + ω(G) = |V|`. -/
theorem coverNum_compl_add_cliqueNum (G : IsoGraph) :
    Gᶜ.coverNum + G.cliqueNum = G.V := by
  have := Gᶜ.coverNum_add_indepNum
  rwa [indepNum_compl, V_compl] at this

/-! ### The vertex cover table -/

@[simp] theorem coverNum_empty (n : ℕ) : (empty n).coverNum = 0 := by
  rw [coverNum_eq, V_empty, indepNum_empty]
  omega

@[simp] theorem coverNum_complete (n : ℕ) : (complete n).coverNum = n - 1 := by
  rw [coverNum_eq, V_complete, indepNum_complete]
  omega

@[simp] theorem coverNum_cycle (n : ℕ) : (cycle (n + 3)).coverNum = (n + 3) - (n + 3) / 2 := by
  rw [coverNum_eq, V_cycle, indepNum_cycle]

@[simp] theorem coverNum_bipartite (m n : ℕ) : (bipartite m n).coverNum = min m n := by
  rw [coverNum_eq, V_bipartite, indepNum_bipartite]
  omega

@[simp] theorem coverNum_star (n : ℕ) : (star n).coverNum = min 1 n := by
  rw [star_eq_bipartite, coverNum_bipartite]

@[simp] theorem coverNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).coverNum = G.coverNum + H.coverNum := by
  rw [coverNum_eq, coverNum_eq, coverNum_eq, V_disjUnion, indepNum_disjUnion]
  have := G.coverNum_add_indepNum
  have := H.coverNum_add_indepNum
  omega

@[simp] theorem coverNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).coverNum = ds.sum - (ds.max?).getD 0 := by
  rw [coverNum_eq, V_completeMultipartite, indepNum_completeMultipartite]

/-! ### Where the cover number sits among the other invariants -/

/-- Turned around, this is a lower bound on the cover number, and via Gallai an upper bound on
the independence number. -/
theorem indepNum_mul_maxDeg_le (G : IsoGraph) :
    G.E + G.indepNum * G.maxDeg ≤ G.V * G.maxDeg := by
  have h1 := G.E_le_coverNum_mul_maxDeg
  have h2 := G.coverNum_add_indepNum
  calc G.E + G.indepNum * G.maxDeg ≤ G.coverNum * G.maxDeg + G.indepNum * G.maxDeg :=
        Nat.add_le_add_right h1 _
    _ = (G.coverNum + G.indepNum) * G.maxDeg := by ring
    _ = G.V * G.maxDeg := by rw [h2]

attribute [simp] IsoGraph.coverNum_le_E

/-- A graph with an edge has an independent set smaller than its whole vertex set. -/
theorem indepNum_lt_V_of_E_pos (G : IsoGraph) (h : 0 < G.E) : G.indepNum < G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, E_mk] at h
  rw [← mk_canonicalize g, indepNum_mk, V_mk]
  exact CGraph.indepNum_lt_card_of_E_pos _ h

/-- A vertex cover meets every edge, so a graph with an edge needs one, and conversely a graph
with no edges needs none. -/
theorem coverNum_pos (G : IsoGraph) (h : 0 < G.E) : 0 < G.coverNum := by
  have h1 := G.coverNum_add_indepNum
  have h2 := G.indepNum_lt_V_of_E_pos h
  omega

@[simp] theorem coverNum_eq_zero_iff (G : IsoGraph) : G.coverNum = 0 ↔ G.E = 0 := by
  constructor
  · intro h
    by_contra hcon
    exact absurd (G.coverNum_pos (by omega)) (by omega)
  · intro h
    have := G.coverNum_le_E
    omega

/-! ### The cover number at work -/

example : (cycle 6).coverNum = 3 := by rw [show (6 : ℕ) = 3 + 3 from rfl, coverNum_cycle]

example : (complete 5).coverNum = 4 := by simp

example : (bipartite 3 4).coverNum = 3 := by simp

/-- `|E| ≤ τ·Δ` is an equality on stars, where a single vertex covers everything. -/
example (n : ℕ) :
    (star (n + 1)).E = (star (n + 1)).coverNum * (star (n + 1)).maxDeg := by
  rw [E_star, maxDeg_star, coverNum_star, Nat.min_eq_left (by omega), one_mul]

/-! ### The clique–coclique bound -/

/-- **The clique–coclique bound**: `α · ω ≤ |V|` for a vertex-transitive graph.  Both factors are
maximised by the same graph only in very rigid cases; see the examples below. -/
theorem indepNum_mul_cliqueNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) :
    G.indepNum * G.cliqueNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, indepNum_mk, cliqueNum_mk]
  rw [← mk_canonicalize g, isVertexTransitive_mk] at h
  exact CGraph.indepNum_mul_cliqueNum_le_card _ h

/-- Contrapositive: `α · ω > |V|` is a certificate of *non*-vertex-transitivity, and one that is
independent of the usual degree-sequence obstruction. -/
theorem not_isVertexTransitive_of_V_lt {G : IsoGraph} (h : G.V < G.indepNum * G.cliqueNum) :
    ¬ IsVertexTransitive G := fun hvt ↦ absurd (indepNum_mul_cliqueNum_le_V hvt) (by omega)

/-- A vertex-transitive graph with an edge has an independent set of at most half its vertices. -/
theorem two_mul_indepNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) (hE : 0 < G.E) :
    2 * G.indepNum ≤ G.V := by
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hE
  calc 2 * G.indepNum = G.indepNum * 2 := by ring
    _ ≤ G.indepNum * G.cliqueNum := Nat.mul_le_mul_left _ h1
    _ ≤ G.V := indepNum_mul_cliqueNum_le_V h

/-- Dually, a vertex-transitive graph that is not complete has a clique of at most half its
vertices (`2 ≤ α` says exactly that some pair of vertices is non-adjacent). -/
theorem two_mul_cliqueNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) (hα : 2 ≤ G.indepNum) :
    2 * G.cliqueNum ≤ G.V :=
  le_trans (Nat.mul_le_mul_right _ hα) (indepNum_mul_cliqueNum_le_V h)

/-- The clique–coclique bound and the greedy bound `|V| ≤ χ · α` sandwich `|V|` between two
products with the same first factor, so a vertex-transitive graph has `ω ≤ χ` with room to spare
whenever the bound is not tight. -/
theorem indepNum_mul_cliqueNum_le_chromNum_mul_indepNum {G : IsoGraph} (h : IsVertexTransitive G) :
    G.indepNum * G.cliqueNum ≤ G.chromNum * G.indepNum :=
  le_trans (indepNum_mul_cliqueNum_le_V h) (V_le_chromNum_mul_indepNum G)

/-- In a vertex-transitive graph the independence number and the vertex cover number are related
by `ω · (|V| - τ) ≤ |V|`. -/
theorem cliqueNum_mul_V_sub_coverNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) :
    G.cliqueNum * (G.V - G.coverNum) ≤ G.V := by
  rw [← indepNum_eq_V_sub_coverNum, Nat.mul_comm]
  exact indepNum_mul_cliqueNum_le_V h

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

/-- Cycles: the clique–coclique bound recovers `α(C_n) ≤ ⌊n/2⌋`. -/
theorem two_mul_indepNum_cycle_le (n : ℕ) : 2 * (cycle (n + 3)).indepNum ≤ n + 3 := by
  have hE : 0 < (cycle (n + 3)).E := by simp
  have := two_mul_indepNum_le_V (isVertexTransitive_cycle (n + 3)) hE
  rwa [V_cycle] at this

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

/-! ### Self-complementary graphs -/

/-- A self-complementary graph has as many vertices in its largest independent set as in its
largest clique. -/
theorem indepNum_eq_cliqueNum_of_compl_eq {G : IsoGraph} (h : Gᶜ = G) :
    G.indepNum = G.cliqueNum := by
  conv_lhs => rw [← h]
  rw [indepNum_compl]

/-- A self-complementary graph owns exactly half of the possible edges. -/
theorem two_mul_E_of_compl_eq {G : IsoGraph} (h : Gᶜ = G) : 2 * G.E = G.V.choose 2 := by
  have h1 := G.E_compl
  rw [h] at h1
  omega

private theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Nat.choose_two_right, Nat.succ_sub_one]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    have h : (m + 1) * m = 2 * k := by rw [Nat.mul_comm]; omega
    rw [h]
    omega

/-- **A self-complementary graph has `|V| ≡ 0` or `1 (mod 4)`**: it owns half of the `C(|V|, 2)`
possible edges, so `4` divides `|V| · (|V| - 1)`. -/
theorem V_mod_four_of_compl_eq {G : IsoGraph} (h : Gᶜ = G) :
    G.V % 4 = 0 ∨ G.V % 4 = 1 := by
  have h1 := two_mul_E_of_compl_eq h
  have h2 := two_mul_choose_two G.V
  have h3 : 4 * G.E = G.V * (G.V - 1) := by omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk⟩ : ∃ k, G.V = 4 * k + G.V % 4 := ⟨G.V / 4, by omega⟩
  have hr : G.V % 4 = 2 ∨ G.V % 4 = 3 := by omega
  rcases hr with hr | hr <;> rw [hr] at hk
  · have hexp : G.V * (G.V - 1) = 16 * (k * k) + 12 * k + 2 := by
      rw [hk, show 4 * k + 2 - 1 = 4 * k + 1 from by omega]; ring
    omega
  · have hexp : G.V * (G.V - 1) = 16 * (k * k) + 20 * k + 6 := by
      rw [hk, show 4 * k + 3 - 1 = 4 * k + 2 from by omega]; ring
    omega

/-- A self-complementary *vertex-transitive* graph has `ω² ≤ |V|`, since `α = ω` there. -/
theorem cliqueNum_sq_le_V_of_compl_eq {G : IsoGraph} (h : IsVertexTransitive G)
    (hc : Gᶜ = G) : G.cliqueNum ^ 2 ≤ G.V := by
  have hα := indepNum_eq_cliqueNum_of_compl_eq hc
  have hle := indepNum_mul_cliqueNum_le_V h
  rw [hα, ← pow_two] at hle
  exact hle

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

/-! ### The domination number -/

theorem domNum_le_V (G : IsoGraph) : G.domNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk]
  exact CGraph.domNum_le_card _

theorem domNum_pos {G : IsoGraph} (h : 0 < G.V) : 0 < G.domNum := by
  have := (G.domNum_eq_zero_iff).not.2 (by omega : ¬ G.V = 0)
  omega

/-- **The degree bound** `|V| ≤ γ·(Δ + 1)`. -/
theorem V_le_domNum_mul_maxDeg_add_one (G : IsoGraph) : G.V ≤ G.domNum * (G.maxDeg + 1) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk, maxDeg_mk]
  exact CGraph.card_le_domNum_mul_maxDeg_add_one _

/-- **`γ + Δ ≤ |V|`**. -/
theorem domNum_add_maxDeg_le_V (G : IsoGraph) : G.domNum + G.maxDeg ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk, maxDeg_mk]
  exact CGraph.domNum_add_maxDeg_le_card _

/-- **`γ ≤ τ`** for a graph with no isolated vertex. -/
theorem domNum_le_coverNum {G : IsoGraph} (h : 1 ≤ G.minDeg) : G.domNum ≤ G.coverNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, domNum_mk, coverNum_mk]
  rw [← mk_canonicalize g, minDeg_mk] at h
  exact CGraph.domNum_le_coverNum _ h

/-- With Gallai's identity, the degree bound reads `τ ≥ |V|·Δ/(Δ+1) - ...`; more usefully it
bounds the independence number from below, since `γ ≤ α`. -/
theorem V_le_indepNum_mul_maxDeg_add_one (G : IsoGraph) : G.V ≤ G.indepNum * (G.maxDeg + 1) :=
  le_trans G.V_le_domNum_mul_maxDeg_add_one
    (Nat.mul_le_mul_right _ G.domNum_le_indepNum)

/-! ### The table -/

attribute [simp] IsoGraph.domNum_empty IsoGraph.domNum_complete IsoGraph.domNum_star

/-- A `k`-regular graph needs at least `|V|/(k + 1)` vertices to dominate it. -/
theorem le_domNum_of_regular {G : IsoGraph} {k : ℕ} (h : G.maxDeg = k) :
    G.V ≤ G.domNum * (k + 1) := by
  rw [← h]; exact G.V_le_domNum_mul_maxDeg_add_one

/-- `γ(Petersen) ≥ 3` (the true value is `3`). -/
theorem three_le_domNum_petersen : 3 ≤ petersen.domNum := by
  have h := le_domNum_of_regular (G := petersen) (k := 3) maxDeg_petersen
  rw [V_petersen] at h
  omega

/-- `γ(Cₙ) ≥ n/3`. -/
theorem le_domNum_cycle (n : ℕ) : n + 3 ≤ (cycle (n + 3)).domNum * 3 := by
  have h := le_domNum_of_regular (G := cycle (n + 3)) (k := 2) (maxDeg_cycle n)
  rwa [V_cycle] at h

example : (star 5).domNum = 1 := by simp

example : (empty 4).domNum = 4 := by simp

example : (complete 7).domNum = 1 := by simp

/-! ### The radius -/

theorem radius_pos {G : IsoGraph} (hc : IsConnected G) (hV : 1 < G.V) : 0 < G.radius := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk]
  rw [← mk_canonicalize g, isConnected_mk] at hc
  rw [← mk_canonicalize g, V_mk] at hV
  exact CGraph.radius_pos _ hc hV

/-- **`r = 1 ↔ γ = 1`** on a graph with at least two vertices. -/
theorem radius_eq_one_iff_domNum_eq_one {G : IsoGraph} (hV : 1 < G.V) :
    G.radius = 1 ↔ G.domNum = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk, domNum_mk]
  rw [← mk_canonicalize g, V_mk] at hV
  exact CGraph.radius_eq_one_iff_domNum_eq_one _ hV

/-- **A vertex-transitive graph has `r = d`.** -/
theorem radius_eq_diameter_of_isVertexTransitive {G : IsoGraph} (h : IsVertexTransitive G) :
    G.radius = G.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk, diameter_mk]
  rw [← mk_canonicalize g, isVertexTransitive_mk] at h
  exact CGraph.radius_eq_diameter_of_isVertexTransitive _ h

/-! ### The radius table -/

attribute [simp] IsoGraph.domNum_wheel


@[simp] theorem radius_empty (n : ℕ) : (empty n).radius = 0 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_empty n), diameter_empty]

@[simp] theorem radius_complete (n : ℕ) : (complete (n + 2)).radius = 1 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_complete _),
    diameter_complete]

@[simp] theorem radius_cycle (n : ℕ) : (cycle (n + 1)).radius = (n + 1) / 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_cycle _), diameter_cycle]

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

/-! ### Counting cliques -/

@[simp] theorem cliqueCount_two (G : IsoGraph) : G.cliqueCount 2 = G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, E_mk]
  classical
  exact CGraph.cliqueCount_two _

/-! ### The clique-count table -/

@[simp] theorem cliqueCount_cycle_even (m : ℕ) : (cycle (2 * m)).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_cycle_even m)

@[simp] theorem cliqueCount_cycle_four : (cycle 4).cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_cycle_four]
  omega

@[simp] theorem cliqueCount_cycle_five : (cycle 5).cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_cycle_five]
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

/-! ### Counting independent sets -/

@[simp] theorem cliqueCount_compl (G : IsoGraph) (n : ℕ) :
    Gᶜ.cliqueCount n = G.indepCount n := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, cliqueCount_mk, indepCount_mk]
  exact CGraph.cliqueCount_compl _ n

@[simp] theorem indepCount_compl (G : IsoGraph) (n : ℕ) :
    Gᶜ.indepCount n = G.cliqueCount n := by
  rw [← cliqueCount_compl Gᶜ, compl_compl]

theorem indepCount_two_add_E (G : IsoGraph) : G.indepCount 2 + G.E = G.V.choose 2 := by
  rw [← cliqueCount_compl, cliqueCount_two]
  exact E_compl_add G

example : (empty 6).indepCount 3 = 20 := by rw [indepCount_empty]; decide

example : (complete 4).indepCount 2 = 0 := by
  show (complete 4).indepCount (0 + 2) = 0
  simp

/-! ### Counting cliques in a disjoint union -/

@[simp] theorem indepCount_join (G H : IsoGraph) (n : ℕ) :
    (G ∇g H).indepCount (n + 1) = G.indepCount (n + 1) + H.indepCount (n + 1) := by
  rw [join, indepCount_compl, cliqueCount_disjUnion, cliqueCount_compl, cliqueCount_compl]

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

/-! ### Counting connected components -/

theorem numComponents_eq_one_of_isConnected {G : IsoGraph} (h : G.IsConnected) :
    G.numComponents = 1 :=
  (numComponents_eq_one_iff G).2 h

theorem numComponents_le_V (G : IsoGraph) : G.numComponents ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.numComponents_le_card g

/-- **At most one of a graph and its complement is disconnected.** -/
theorem numComponents_compl_eq_one {G : IsoGraph} (h : 2 ≤ G.numComponents) :
    Gᶜ.numComponents = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, numComponents_mk]
  rw [← mk_canonicalize g, numComponents_mk] at h
  exact CGraph.numComponents_compl_eq_one _ h

/-! ### The component-count table -/

@[simp] theorem numComponents_path (n : ℕ) : (path (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_path n)

@[simp] theorem numComponents_cycle (n : ℕ) : (cycle (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_cycle n)

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

/-! ### Components versus the other invariants -/

@[simp] theorem numComponents_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_join hG hH)

/-- A graph has as many components as vertices exactly when it has no edges. -/
theorem numComponents_eq_V_iff (G : IsoGraph) : G.numComponents = G.V ↔ G.E = 0 := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk, E_mk, numComponents_mk]
  exact CGraph.numComponents_eq_card_iff _

theorem numComponents_lt_V_of_E_pos {G : IsoGraph} (h : 0 < G.E) : G.numComponents < G.V := by
  have hle := G.numComponents_le_V
  have := (G.numComponents_eq_V_iff).not.2 (by omega : ¬ G.E = 0)
  omega

example : (cycle 5 ∇g empty 3).numComponents = 1 := by
  refine numComponents_join ?_ ?_ <;> simp

example : (cycle 5).numComponents < (cycle 5).V := numComponents_lt_V_of_E_pos (by simp)

/-! ### Components of a Cartesian product -/

/-- **The components of a Cartesian product are the pairs of components.** -/
@[simp] theorem numComponents_cartesianProduct (G H : IsoGraph) :
    (G □g H).numComponents = G.numComponents * H.numComponents := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, numComponents_mk,
    numComponents_mk, numComponents_mk]
  exact CGraph.numComponents_cartesianProduct _ _

/-! ### A minimum-degree condition for connectedness -/

/-- **A graph with `2δ(G) + 1 ≥ |V|` is connected.** -/
theorem isConnected_of_V_le_two_mul_minDeg (G : IsoGraph) (hV : 0 < G.V)
    (h : G.V ≤ 2 * minDeg G + 1) : IsConnected G := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, V_mk, minDeg_mk] at h
  rw [← mk_canonicalize g, isConnected_mk]
  have : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  exact CGraph.isConnected_of_card_le_two_mul_minDeg _ h

theorem numComponents_eq_one_of_V_le_two_mul_minDeg (G : IsoGraph) (hV : 0 < G.V)
    (h : G.V ≤ 2 * minDeg G + 1) : G.numComponents = 1 :=
  numComponents_eq_one_of_isConnected (G.isConnected_of_V_le_two_mul_minDeg hV h)

example : (empty 3 □g empty 4).numComponents = 12 := by simp

example : IsConnected (hypercube 2) := by
  refine (hypercube 2).isConnected_of_V_le_two_mul_minDeg (by simp) ?_
  simp

/-! ### Counting automorphisms -/

/-- **A graph and its complement have the same automorphisms.** -/
@[simp] theorem autCount_compl (G : IsoGraph) : Gᶜ.autCount = G.autCount := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, compl_mk, autCount_mk, autCount_mk]
  exact CGraph.autCount_compl _

/-- Two graphs with different automorphism counts are different. -/
theorem ne_of_autCount_ne {G H : IsoGraph} (h : G.autCount ≠ H.autCount) : G ≠ H :=
  fun hGH ↦ h (hGH ▸ rfl)

example : (complete 4).autCount = 24 := by simp [Nat.factorial]

example : (empty 3).autCount = 6 := by simp [Nat.factorial]

/-! ### Automorphisms versus symmetry -/

theorem V_le_autCount_of_isVertexTransitive (G : IsoGraph) (hV : 0 < G.V)
    (h : G.IsVertexTransitive) : G.V ≤ G.autCount := by
  induction G using Quotient.inductionOn with | _ g =>
  haveI : Nonempty g.V := Fintype.card_pos_iff.1 hV
  exact CGraph.card_le_autCount_of_isVertexTransitive g h

theorem not_isVertexTransitive_of_autCount_lt (G : IsoGraph) (hV : 0 < G.V)
    (h : G.autCount < G.V) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.V_le_autCount_of_isVertexTransitive hV hvt) (by omega)

example : 5 ≤ (cycle 5).autCount := by
  have := V_le_autCount_of_isVertexTransitive (cycle 5) (by simp) (by simp)
  simpa using this

example : 10 ≤ (cycle 5).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (cycle 5) (by simp)
  simpa using this

example : 24 ≤ (hypercube 3).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (hypercube 3) (by simp)
  simpa using this

example : 30 ≤ (kneser 5 2).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (kneser 5 2) (by simp)
  simpa using this

/-! ### The handshaking lemma -/

/-- A graph all of whose degrees are odd has evenly many vertices. -/
theorem even_V_of_forall_odd_mem_degSequence (G : IsoGraph)
    (h : ∀ d ∈ degSequence G, Odd d) : Even G.V := by
  have hc := G.even_countP_odd_degSequence
  rwa [List.countP_eq_length.2 (fun d hd ↦ by simpa using h d hd), length_degSequence] at hc

/-- **An odd-regular graph has evenly many vertices.** -/
theorem even_V_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hk : Odd k)
    (h : degSequence G = List.replicate n k) : Even G.V :=
  G.even_V_of_forall_odd_mem_degSequence fun d hd ↦ by
    rw [h, List.mem_replicate] at hd
    exact hd.2 ▸ hk

/-- On an odd number of vertices, some degree is even. -/
theorem exists_even_mem_degSequence_of_odd_V (G : IsoGraph) (h : Odd G.V) :
    ∃ d ∈ degSequence G, Even d := by
  by_contra hc
  push_neg at hc
  exact Nat.not_even_iff_odd.2 h (G.even_V_of_forall_odd_mem_degSequence
    fun d hd ↦ Nat.not_even_iff_odd.1 (hc d hd))

/-- There is no cubic graph on seven vertices. -/
example (G : IsoGraph) (h : degSequence G = List.replicate 7 3) : False := by
  have hV : G.V = 7 := by rw [← length_degSequence, h, List.length_replicate]
  have := even_V_of_degSequence_replicate (by decide) h
  rw [hV] at this
  exact (by decide : ¬ Even 7) this

/-! ### Automorphisms of the constructions -/

theorem autCount_mul_le_autCount_join (G H : IsoGraph) :
    G.autCount * H.autCount ≤ (G ∇g H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, autCount_mk, autCount_mk, autCount_mk]
  exact CGraph.autCount_mul_le_autCount_join _ _

theorem autCount_mul_le_autCount_cartesianProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (G □g H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_cartesianProduct _ _

theorem autCount_mul_le_autCount_tensorProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (G ⊗g H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_tensorProduct _ _

theorem autCount_mul_le_autCount_strongProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (G ⊠g H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_strongProduct _ _

theorem autCount_mul_le_autCount_lexProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (G ·g H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_lexProduct _ _

theorem two_mul_autCount_mul_le_autCount_disjUnion_self (G : IsoGraph) (hV : 0 < G.V) :
    2 * (G.autCount * G.autCount) ≤ (G ⊕g G).autCount := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk] at hV
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, disjUnion_mk, autCount_mk, autCount_mk]
  exact CGraph.two_mul_autCount_mul_le_autCount_disjUnion_self _

example : 12 ≤ (complete 3 ⊕g complete 4).autCount := by
  have := autCount_mul_le_autCount_disjUnion (complete 3) (complete 4)
  simp [Nat.factorial] at this
  omega

/-! ### Vertices, edges and components -/

/-- `|V| ≤ |E| + c(G)`: a spanning forest has `|V| - c(G)` edges. -/
theorem V_le_E_add_numComponents (G : IsoGraph) : G.V ≤ G.E + G.numComponents := by
  induction G using Quotient.inductionOn with | _ g
  exact CGraph.card_le_E_add_numComponents g

theorem V_le_E_add_one_of_isConnected {G : IsoGraph} (h : G.IsConnected) : G.V ≤ G.E + 1 := by
  have := G.V_le_E_add_numComponents
  rw [numComponents_eq_one_of_isConnected h] at this
  exact this

theorem V_sub_E_le_numComponents (G : IsoGraph) : G.V - G.E ≤ G.numComponents := by
  have := G.V_le_E_add_numComponents
  omega

theorem E_pos_of_numComponents_lt_V {G : IsoGraph} (h : G.numComponents < G.V) : 0 < G.E := by
  have := G.V_le_E_add_numComponents
  omega

theorem not_isConnected_of_E_add_one_lt_V {G : IsoGraph} (h : G.E + 1 < G.V) :
    ¬ G.IsConnected := fun hc ↦ by
  have := V_le_E_add_one_of_isConnected hc
  omega

/-- `c(G) = |V|` forces `E = 0`, and this recovers it quantitatively: each edge kills at most one
component. -/
theorem V_sub_numComponents_le_E (G : IsoGraph) : G.V - G.numComponents ≤ G.E := by
  have := G.V_le_E_add_numComponents
  omega

example : (empty 5).V - (empty 5).E ≤ (empty 5).numComponents := by simp

example : ¬ (complete 1 ⊕g complete 1).IsConnected := by
  apply not_isConnected_of_E_add_one_lt_V
  simp

/-! ### The clique number of the Mycielskian -/

theorem cliqueNum_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    (mycielskian G).cliqueNum = max G.cliqueNum 2 := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk] at hV
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, mycielskian_mk, cliqueNum_mk, cliqueNum_mk]
  exact CGraph.cliqueNum_mycielskian _

theorem cliqueNum_mycielskian_eq_two {G : IsoGraph} (hV : 0 < G.V) (h : G.cliqueNum ≤ 2) :
    (mycielskian G).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian G hV]
  omega

/-- **Mycielski's theorem**: there are triangle-free graphs of arbitrarily large chromatic
number.  Iterating the Mycielskian from `K₁` keeps the clique number at most two while raising
the chromatic number by one each time. -/
theorem exists_cliqueNum_le_two_and_le_chromNum (k : ℕ) :
    ∃ G : IsoGraph, 0 < G.V ∧ G.cliqueNum ≤ 2 ∧ k ≤ G.chromNum := by
  induction k with
  | zero => exact ⟨complete 1, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨G, hV, hw, hc⟩ := ih
    refine ⟨mycielskian G, ?_, ?_, ?_⟩
    · rw [V_mycielskian]
      omega
    · rw [cliqueNum_mycielskian G hV]
      omega
    · rw [chromNum_mycielskian]
      omega

/-- The same statement with triangles counted rather than measured by the clique number. -/
theorem exists_cliqueCount_three_eq_zero_and_le_chromNum (k : ℕ) :
    ∃ G : IsoGraph, G.cliqueCount 3 = 0 ∧ k ≤ G.chromNum := by
  obtain ⟨G, -, hw, hc⟩ := exists_cliqueNum_le_two_and_le_chromNum k
  exact ⟨G, (cliqueCount_eq_zero_iff G 3).2 (by omega), hc⟩

example : (mycielskian (cycle 5)).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian _ (by simp), cliqueNum_cycle_five, max_self]

/-! ### Edge counts of the strong and lexicographic products -/

@[simp] theorem E_strongProduct (G H : IsoGraph) :
    (G ⊠g H).E = G.V * H.E + H.V * G.E + 2 * G.E * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_strongProduct _ _

@[simp] theorem E_lexProduct (G H : IsoGraph) :
    (G ·g H).E = H.V * H.V * G.E + G.V * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_lexProduct _ _

theorem E_strongProduct_eq_add (G H : IsoGraph) :
    (G ⊠g H).E = (G □g H).E + (G ⊗g H).E := by
  rw [E_strongProduct, E_cartesianProduct, E_tensorProduct]

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

theorem domNum_join_le_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).domNum ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, domNum_mk]
  exact CGraph.domNum_join_le_two _ _

@[simp] theorem domNum_join_eq_one_iff (G H : IsoGraph) :
    (G ∇g H).domNum = 1 ↔ G.domNum = 1 ∨ H.domNum = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, domNum_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_join_eq_one_iff _ _

theorem domNum_join_eq_two {G H : IsoGraph} (hGV : 0 < G.V) (hHV : 0 < H.V)
    (hG : G.domNum ≠ 1) (hH : H.domNum ≠ 1) : (G ∇g H).domNum = 2 := by
  have h1 := domNum_join_le_two hGV hHV
  have h2 : 0 < (G ∇g H).domNum := domNum_pos (by rw [V_join]; omega)
  have h3 : (G ∇g H).domNum ≠ 1 := fun h ↦ by
    rcases (domNum_join_eq_one_iff G H).1 h with h | h
    · exact hG h
    · exact hH h
  omega

theorem domNum_cartesianProduct_le (G H : IsoGraph) :
    (G □g H).domNum ≤ G.domNum * H.V := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, domNum_mk, domNum_mk, V_mk]
  exact CGraph.domNum_cartesianProduct_le _ _

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

theorem radius_cartesianProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G □g H).radius = G.radius + H.radius := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isConnected_mk] at hG
  rw [← mk_canonicalize h, isConnected_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, radius_mk, radius_mk,
    radius_mk]
  exact CGraph.radius_cartesianProduct _ _ hG hH

example : (cycle 5 □g cycle 5).radius = 4 := by
  rw [radius_cartesianProduct (by simp) (by simp)]
  simp

example : (rook 4 4).radius = 2 := by
  rw [rook, radius_cartesianProduct (by simp) (by simp)]
  simp

theorem diameter_strongProduct_le {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ⊠g H).diameter ≤ G.diameter + H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isConnected_mk] at hG
  rw [← mk_canonicalize h, isConnected_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, diameter_mk, diameter_mk,
    diameter_mk]
  exact CGraph.diameter_strongProduct_le _ _ hG hH

theorem diameter_lexProduct_le {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ·g H).diameter ≤ G.diameter + H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isConnected_mk] at hG
  rw [← mk_canonicalize h, isConnected_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, diameter_mk, diameter_mk,
    diameter_mk]
  exact CGraph.diameter_lexProduct_le _ _ hG hH

theorem radius_cartesianProduct_self {G : IsoGraph} (hG : IsConnected G) :
    (G □g G).radius = 2 * G.radius := by
  rw [radius_cartesianProduct hG hG, two_mul]

example : (cycle 5 ⊠g cycle 5).diameter ≤ 4 := by
  have := diameter_strongProduct_le (G := cycle 5) (H := cycle 5) (by simp) (by simp)
  simpa using this

/-! ### Domination in the graph products -/

theorem domNum_strongProduct_le (G H : IsoGraph) :
    (G ⊠g H).domNum ≤ G.domNum * H.domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, domNum_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_strongProduct_le _ _

theorem domNum_le_domNum_lexProduct (G : IsoGraph) {H : IsoGraph} (hH : 0 < H.V) :
    G.domNum ≤ (G ·g H).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_le_domNum_lexProduct _ _

theorem domNum_lexProduct (G : IsoGraph) {H : IsoGraph} (hH : H.domNum = 1) :
    (G ·g H).domNum = G.domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, domNum_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_lexProduct _ _ hH

/-- Two universal vertices give a universal vertex of the strong product. -/
theorem domNum_strongProduct_eq_one {G H : IsoGraph} (hG : G.domNum = 1) (hH : H.domNum = 1) :
    (G ⊠g H).domNum = 1 := by
  have hGV : 0 < G.V := by
    rcases Nat.eq_zero_or_pos G.V with h | h
    · rw [← domNum_eq_zero_iff] at h; omega
    · exact h
  have hHV : 0 < H.V := by
    rcases Nat.eq_zero_or_pos H.V with h | h
    · rw [← domNum_eq_zero_iff] at h; omega
    · exact h
  have h1 := domNum_strongProduct_le G H
  have h2 : 0 < (G ⊠g H).domNum :=
    domNum_pos (by rw [V_strongProduct]; exact Nat.mul_pos hGV hHV)
  rw [hG, hH] at h1
  omega

example : (empty 3 ·g complete 2).domNum = 3 := by
  rw [domNum_lexProduct _ (by simp), domNum_empty]

example : (star 3 ⊠g star 4).domNum = 1 :=
  domNum_strongProduct_eq_one (by simp) (by simp)

example : (cycle 5 ·g complete 4).domNum = (cycle 5).domNum :=
  domNum_lexProduct _ (by simp)

theorem domNum_le_domNum_cartesianProduct (G : IsoGraph) {H : IsoGraph} (hH : 0 < H.V) :
    G.domNum ≤ (G □g H).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_le_domNum_cartesianProduct _ _

theorem domNum_le_domNum_strongProduct (G : IsoGraph) {H : IsoGraph} (hH : 0 < H.V) :
    G.domNum ≤ (G ⊠g H).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_le_domNum_strongProduct _ _

/-- The domination number of a strong product sits between the larger factor value and the
product of the two. -/
theorem max_domNum_le_domNum_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.domNum H.domNum ≤ (G ⊠g H).domNum := by
  refine max_le (domNum_le_domNum_strongProduct G hH) ?_
  rw [strongProduct_comm]
  exact domNum_le_domNum_strongProduct H hG

/-! ### Independence numbers of the graph products -/

/-- `α(G) · α(H) ≤ α(G ⊠ H)`: the Shannon-capacity lower bound. -/
theorem indepNum_mul_indepNum_le_indepNum_strongProduct (G H : IsoGraph) :
    G.indepNum * H.indepNum ≤ (G ⊠g H).indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_mul_indepNum_le_indepNum_strongProduct _ _

/-- `α(G) · α(H) ≤ α(G □ H)`. -/
theorem indepNum_mul_indepNum_le_indepNum_cartesianProduct (G H : IsoGraph) :
    G.indepNum * H.indepNum ≤ (G □g H).indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_mul_indepNum_le_indepNum_cartesianProduct _ _

/-- `α(G) · |V(H)| ≤ α(G × H)`, since no tensor edge stays inside a slab. -/
theorem indepNum_mul_V_le_indepNum_tensorProduct (G H : IsoGraph) :
    G.indepNum * H.V ≤ (G ⊗g H).indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, indepNum_mk, indepNum_mk,
    V_mk]
  exact CGraph.indepNum_mul_card_le_indepNum_tensorProduct _ _

/-- `α(G × H)` is also at least `|V(G)| · α(H)`, by symmetry. -/
theorem V_mul_indepNum_le_indepNum_tensorProduct (G H : IsoGraph) :
    G.V * H.indepNum ≤ (G ⊗g H).indepNum := by
  rw [tensorProduct_comm, mul_comm]
  exact indepNum_mul_V_le_indepNum_tensorProduct H G

/-- `α(G □ H) ≤ |V(G)| · α(H)`, by counting fibrewise. -/
theorem indepNum_cartesianProduct_le (G H : IsoGraph) :
    (G □g H).indepNum ≤ G.V * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, indepNum_mk, indepNum_mk,
    V_mk]
  exact CGraph.indepNum_cartesianProduct_le _ _

/-- The mirror bound `α(G □ H) ≤ α(G) · |V(H)|`. -/
theorem indepNum_cartesianProduct_le' (G H : IsoGraph) :
    (G □g H).indepNum ≤ G.indepNum * H.V := by
  rw [cartesianProduct_comm, mul_comm]
  exact indepNum_cartesianProduct_le H G

/-- `α(G ⊠ H) ≤ |V(G)| · α(H)`. -/
theorem indepNum_strongProduct_le (G H : IsoGraph) :
    (G ⊠g H).indepNum ≤ G.V * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, indepNum_mk, indepNum_mk,
    V_mk]
  exact CGraph.indepNum_strongProduct_le _ _

/-- The mirror bound `α(G ⊠ H) ≤ α(G) · |V(H)|`. -/
theorem indepNum_strongProduct_le' (G H : IsoGraph) :
    (G ⊠g H).indepNum ≤ G.indepNum * H.V := by
  rw [strongProduct_comm, mul_comm]
  exact indepNum_strongProduct_le H G

/-- Squeezing the two bounds: a product with a complete graph has independence number exactly
`α(G)`, because `α(K_n) = 1` for `n ≠ 0`. -/
theorem indepNum_cartesianProduct_complete_le (G : IsoGraph) (n : ℕ) :
    (G □g complete n).indepNum ≤ G.indepNum * n := by
  have h := indepNum_cartesianProduct_le' G (complete n)
  rwa [V_complete] at h

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

/-- **`χ(G ⊠ H) ≤ χ(G)·χ(H)`.** -/
theorem chromNum_strongProduct_le (G H : IsoGraph) :
    (G ⊠g H).chromNum ≤ G.chromNum * H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.chromNum_strongProduct_le _ _

/-- `max χ(G) χ(H) ≤ χ(G ⊠ H)`, once both factors have a vertex. -/
theorem max_chromNum_le_chromNum_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.chromNum H.chromNum ≤ (G ⊠g H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.max_chromNum_le_chromNum_strongProduct _ _ a b

/-- `max χ(G) χ(H) ≤ χ(G[H])`, once both factors have a vertex. -/
theorem max_chromNum_le_chromNum_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.chromNum H.chromNum ≤ (G ·g H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.max_chromNum_le_chromNum_lexProduct _ _ a b

/-- `ω(G)·ω(H) ≤ χ(G ⊠ H)`. -/
theorem cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (G H : IsoGraph) :
    G.cliqueNum * H.cliqueNum ≤ (G ⊠g H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, chromNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_mul_cliqueNum_le_chromNum_strongProduct _ _

/-- Two edges make a tensor edge: `2 ≤ χ(G × H)`. -/
theorem two_le_chromNum_tensorProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    2 ≤ (G ⊗g H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, E_mk] at hG
  rw [← mk_canonicalize h, E_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, chromNum_mk]
  exact CGraph.two_le_chromNum_tensorProduct hG hH

/-- A bipartite factor and edges on both sides force `χ(G × H) = 2`. -/
theorem chromNum_tensorProduct_eq_two {G H : IsoGraph} (hG : IsBipartite G)
    (hGE : 0 < G.E) (hHE : 0 < H.E) : (G ⊗g H).chromNum = 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isBipartite_mk] at hG
  rw [← mk_canonicalize g, E_mk] at hGE
  rw [← mk_canonicalize h, E_mk] at hHE
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, chromNum_mk]
  exact CGraph.chromNum_tensorProduct_eq_two hG hGE hHE

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

/-! ### Vertex covers of the products -/

/-- Gallai turns the exact independence number of a lexicographic product into an exact cover
number: `τ(G[H]) = |V(G)|·|V(H)| - α(G)·α(H)`. -/
@[simp] theorem coverNum_lexProduct (G H : IsoGraph) :
    (G ·g H).coverNum = G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_lexProduct, indepNum_lexProduct]

/-- A cover of a join must contain one whole side. -/
@[simp] theorem coverNum_join (G H : IsoGraph) :
    (G ∇g H).coverNum = min (G.coverNum + H.V) (G.V + H.coverNum) := by
  rw [coverNum_eq, V_join, indepNum_join]
  have := G.coverNum_add_indepNum
  have := H.coverNum_add_indepNum
  omega

/-- The independent set bound `α(G)·α(H) ≤ α(G □ H)` becomes an upper bound on `τ`. -/
theorem coverNum_cartesianProduct_le (G H : IsoGraph) :
    (G □g H).coverNum ≤ G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_cartesianProduct]
  exact Nat.sub_le_sub_left (indepNum_mul_indepNum_le_indepNum_cartesianProduct G H) _

/-- The same bound for the strong product. -/
theorem coverNum_strongProduct_le (G H : IsoGraph) :
    (G ⊠g H).coverNum ≤ G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_strongProduct]
  exact Nat.sub_le_sub_left (indepNum_mul_indepNum_le_indepNum_strongProduct G H) _

/-- Fibrewise counting from below: `|V(G)|·τ(H) ≤ τ(G □ H)`. -/
theorem V_mul_coverNum_le_coverNum_cartesianProduct (G H : IsoGraph) :
    G.V * H.coverNum ≤ (G □g H).coverNum := by
  have h1 : G.V * H.coverNum = G.V * H.V - G.V * H.indepNum := by
    rw [coverNum_eq, Nat.mul_sub]
  have h2 := indepNum_cartesianProduct_le G H
  have h3 := (G □g H).coverNum_add_indepNum
  rw [V_cartesianProduct] at h3
  have h4 : G.V * H.indepNum ≤ G.V * H.V :=
    Nat.mul_le_mul_left _ (by have := H.coverNum_add_indepNum; omega)
  omega

/-- The mirror bound `τ(G) · |V(H)| ≤ τ(G □ H)`. -/
theorem coverNum_mul_V_le_coverNum_cartesianProduct (G H : IsoGraph) :
    G.coverNum * H.V ≤ (G □g H).coverNum := by
  rw [cartesianProduct_comm]
  have h := V_mul_coverNum_le_coverNum_cartesianProduct H G
  rwa [mul_comm] at h

/-- The strong product contains the cartesian one, and both have the same vertex set, so the
lower bound survives: `|V(G)|·τ(H) ≤ τ(G ⊠ H)`. -/
theorem V_mul_coverNum_le_coverNum_strongProduct (G H : IsoGraph) :
    G.V * H.coverNum ≤ (G ⊠g H).coverNum := by
  have h1 : G.V * H.coverNum = G.V * H.V - G.V * H.indepNum := by
    rw [coverNum_eq, Nat.mul_sub]
  have h2 := indepNum_strongProduct_le G H
  have h3 := (G ⊠g H).coverNum_add_indepNum
  rw [V_strongProduct] at h3
  have h4 : G.V * H.indepNum ≤ G.V * H.V :=
    Nat.mul_le_mul_left _ (by have := H.coverNum_add_indepNum; omega)
  omega

/-- The mirror bound for the strong product. -/
theorem coverNum_mul_V_le_coverNum_strongProduct (G H : IsoGraph) :
    G.coverNum * H.V ≤ (G ⊠g H).coverNum := by
  rw [strongProduct_comm]
  have h := V_mul_coverNum_le_coverNum_strongProduct H G
  rwa [mul_comm] at h

/-- A slab `S × V(H)` is independent in the tensor product, so covering it is cheap:
`τ(G × H) ≤ τ(G)·|V(H)|`. -/
theorem coverNum_tensorProduct_le (G H : IsoGraph) :
    (G ⊗g H).coverNum ≤ G.coverNum * H.V := by
  have h1 : G.coverNum * H.V = G.V * H.V - G.indepNum * H.V := by
    rw [coverNum_eq, Nat.sub_mul]
  have h2 := indepNum_mul_V_le_indepNum_tensorProduct G H
  have h3 := (G ⊗g H).coverNum_add_indepNum
  rw [V_tensorProduct] at h3
  omega

/-- The mirror bound `τ(G × H) ≤ |V(G)|·τ(H)`. -/
theorem coverNum_tensorProduct_le' (G H : IsoGraph) :
    (G ⊗g H).coverNum ≤ G.V * H.coverNum := by
  rw [tensorProduct_comm]
  have h := coverNum_tensorProduct_le H G
  rwa [mul_comm] at h

example : (cycle 5 ·g complete 3).coverNum = 13 := by
  rw [coverNum_lexProduct, V_cycle, V_complete, indepNum_complete]
  norm_num [show ((cycle 5).indepNum) = 2 from by simp]

example : (complete 3 □g complete 3).coverNum ≤ 8 := by
  have h := coverNum_cartesianProduct_le (complete 3) (complete 3)
  simpa using h

example : 6 ≤ (complete 3 □g complete 3).coverNum := by
  have h := V_mul_coverNum_le_coverNum_cartesianProduct (complete 3) (complete 3)
  simpa using h


/-! ### Nordhaus–Gaddum for the domination number -/

/-- **`γ(G) + γGᶜ ≤ |V| + 1`.** -/
theorem domNum_add_domNum_compl_le_V_add_one (G : IsoGraph) :
    G.domNum + Gᶜ.domNum ≤ G.V + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, domNum_mk, domNum_mk, V_mk]
  exact CGraph.domNum_add_domNum_compl_le_card_add_one _

/-- Two vertices dominate the complement of a disconnected graph. -/
theorem domNum_compl_le_two_of_not_isConnected {G : IsoGraph} (hV : 0 < G.V)
    (h : ¬ IsConnected G) : Gᶜ.domNum ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, isConnected_mk] at h
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, compl_mk, domNum_mk]
  exact CGraph.domNum_compl_le_two_of_not_isConnected _ h

/-- `3 ≤ γ(G) + γGᶜ` on at least two vertices. -/
theorem three_le_domNum_add_domNum_compl {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.domNum + Gᶜ.domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, compl_mk, domNum_mk, domNum_mk]
  exact CGraph.three_le_domNum_add_domNum_compl _ hV

/-- The two Nordhaus–Gaddum bounds together. -/
theorem domNum_add_domNum_compl_mem_Icc {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.domNum + Gᶜ.domNum ∧ G.domNum + Gᶜ.domNum ≤ G.V + 1 :=
  ⟨three_le_domNum_add_domNum_compl hV, G.domNum_add_domNum_compl_le_V_add_one⟩

/-- An edgeless graph attains the upper bound: `γ(E_n) = n` and `γ(K_n) = 1`. -/
example (n : ℕ) : (empty (n + 1)).domNum + (empty (n + 1))ᶜ.domNum = (n + 1) + 1 := by
  rw [compl_empty, domNum_empty, domNum_complete]

/-- The complement of a disconnected graph — in particular of any disjoint union of two
nonempty graphs — is dominated by two vertices. -/
theorem domNum_compl_disjUnion_le_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H)ᶜ.domNum ≤ 2 :=
  domNum_compl_le_two_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

/-- The complement of `2 K₃` is `K₃,₃`, which two vertices dominate. -/
example : (complete 3 ⊕g complete 3)ᶜ.domNum ≤ 2 :=
  domNum_compl_disjUnion_le_two (by simp) (by simp)


/-! ### Nordhaus–Gaddum for the clique and independence numbers -/

/-- A single vertex is a one-element independent set. -/
theorem one_le_indepNum {G : IsoGraph} (h : 0 < G.V) : 1 ≤ G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at h
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 h
  rw [← mk_canonicalize g, indepNum_mk]
  exact CGraph.one_le_indepNum_of_vertex a

/-- **Nordhaus–Gaddum for the clique number**: `ω(G) + α(G) ≤ |V| + 1`. -/
theorem cliqueNum_add_indepNum_le_V_add_one (G : IsoGraph) :
    G.cliqueNum + G.indepNum ≤ G.V + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueNum_mk, indepNum_mk, V_mk]
  exact CGraph.cliqueNum_add_indepNum_le_card_add_one _

/-- On two or more vertices, `3 ≤ ω(G) + α(G)`. -/
theorem three_le_cliqueNum_add_indepNum {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.cliqueNum + G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, cliqueNum_mk, indepNum_mk]
  exact CGraph.three_le_cliqueNum_add_indepNum _ hV

/-- The independence numbers of a graph and its complement: `α(G) + αGᶜ ≤ |V| + 1`. -/
theorem indepNum_add_indepNum_compl_le_V_add_one (G : IsoGraph) :
    G.indepNum + Gᶜ.indepNum ≤ G.V + 1 := by
  rw [indepNum_compl, Nat.add_comm]
  exact G.cliqueNum_add_indepNum_le_V_add_one

/-- The clique numbers of a graph and its complement: `ω(G) + ωGᶜ ≤ |V| + 1`. -/
theorem cliqueNum_add_cliqueNum_compl_le_V_add_one (G : IsoGraph) :
    G.cliqueNum + Gᶜ.cliqueNum ≤ G.V + 1 := by
  rw [cliqueNum_compl]
  exact G.cliqueNum_add_indepNum_le_V_add_one

/-- The matching lower bound for the complement pair. -/
theorem three_le_indepNum_add_indepNum_compl {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.indepNum + Gᶜ.indepNum := by
  rw [indepNum_compl, Nat.add_comm]
  exact three_le_cliqueNum_add_indepNum hV

theorem three_le_cliqueNum_add_cliqueNum_compl {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.cliqueNum + Gᶜ.cliqueNum := by
  rw [cliqueNum_compl]
  exact three_le_cliqueNum_add_indepNum hV

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


/-! ### Nordhaus–Gaddum for the vertex cover number -/

/-- Colour every vertex of a minimum vertex cover with its own colour and everything else with
one shared colour: `χ(G) ≤ τ(G) + 1`. -/
theorem chromNum_le_coverNum_add_one (G : IsoGraph) : G.chromNum ≤ G.coverNum + 1 := by
  have h := G.chromNum_le_V_sub_indepNum_add_one
  rwa [← coverNum_eq] at h

/-- Since `ω ≤ χ`, a graph with a small vertex cover has small cliques too. -/
theorem cliqueNum_le_coverNum_add_one (G : IsoGraph) : G.cliqueNum ≤ G.coverNum + 1 :=
  le_trans G.cliqueNum_le_chromNum G.chromNum_le_coverNum_add_one

/-- The exact Gallai bookkeeping for a graph and its complement: the four numbers
`τ(G)`, `τGᶜ`, `α(G)` and `ω(G)` add up to `2|V|`, because `τGᶜ = |V| - ω(G)`. -/
theorem coverNum_add_coverNum_compl_add_indepNum_add_cliqueNum (G : IsoGraph) :
    G.coverNum + Gᶜ.coverNum + (G.indepNum + G.cliqueNum) = 2 * G.V := by
  have h1 := G.coverNum_add_indepNum
  have h2 := G.coverNum_compl_add_cliqueNum
  omega

/-- **Nordhaus–Gaddum, lower bound**: `|V| - 1 ≤ τ(G) + τGᶜ`, dual to `α + ω ≤ |V| + 1`. -/
theorem V_sub_one_le_coverNum_add_coverNum_compl (G : IsoGraph) :
    G.V - 1 ≤ G.coverNum + Gᶜ.coverNum := by
  have h1 := G.coverNum_add_coverNum_compl_add_indepNum_add_cliqueNum
  have h2 := G.cliqueNum_add_indepNum_le_V_add_one
  omega

/-- **Nordhaus–Gaddum, upper bound**: `τ(G) + τGᶜ ≤ 2|V| - 3` once there are two vertices,
dual to `3 ≤ α + ω`. -/
theorem coverNum_add_coverNum_compl_le {G : IsoGraph} (hV : 2 ≤ G.V) :
    G.coverNum + Gᶜ.coverNum ≤ 2 * G.V - 3 := by
  have h1 := G.coverNum_add_coverNum_compl_add_indepNum_add_cliqueNum
  have h2 := three_le_cliqueNum_add_indepNum hV
  omega

/-- Consequently `γ(G) + α(G) ≤ |V|` for a graph with no isolated vertices. -/
theorem domNum_add_indepNum_le_V {G : IsoGraph} (h : 1 ≤ G.minDeg) :
    G.domNum + G.indepNum ≤ G.V := by
  have h1 := domNum_le_coverNum h
  have h2 := G.coverNum_add_indepNum
  omega

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


/-! ### Regular graphs -/

/-- A constant degree sequence is exactly regularity. -/
theorem isRegularWith_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : G.IsRegularWith k := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [degSequence_mk] at h
  exact CGraph.isRegularWith_of_degSequence h

/-- **The handshake lemma for regular graphs**: `2|E| = k|V|`. -/
theorem IsRegularWith.two_mul_E {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    2 * G.E = G.V * k := two_mul_E_of_degSequence_replicate h.degSequence

theorem IsRegularWith.maxDeg_eq {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) (hV : 0 < G.V) :
    G.maxDeg = k := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, isRegularWith_mk] at h
  rw [← mk_canonicalize g, V_mk] at hV
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, maxDeg_mk]
  exact CGraph.IsRegularWith.maxDeg_eq h v₀

theorem IsRegularWith.minDeg_eq {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) (hV : 0 < G.V) :
    G.minDeg = k := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, isRegularWith_mk] at h
  rw [← mk_canonicalize g, V_mk] at hV
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, minDeg_mk]
  exact CGraph.IsRegularWith.minDeg_eq h v₀

/-- **A vertex-transitive graph is regular**, of degree its common vertex degree. -/
theorem exists_isRegularWith_of_isVertexTransitive {G : IsoGraph} (h : IsVertexTransitive G) :
    ∃ k, G.IsRegularWith k := by
  obtain ⟨k, hk⟩ := exists_degSequence_replicate_of_isVertexTransitive h
  exact ⟨k, isRegularWith_of_degSequence hk⟩

/-! #### Regularity of the constructions -/

theorem IsRegularWith.compl {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    Gᶜ.IsRegularWith (G.V - 1 - k) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, isRegularWith_mk] at h
  rw [← mk_canonicalize g, V_mk, compl_mk, isRegularWith_mk]
  exact CGraph.IsRegularWith.compl h

theorem IsRegularWith.join {G H : IsoGraph} {k l m : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) (h1 : k + H.V = m) (h2 : G.V + l = m) :
    (G ∇g H).IsRegularWith m := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, isRegularWith_mk]
  rw [isRegularWith_mk] at hG hH
  rw [V_mk] at h1 h2
  exact CGraph.IsRegularWith.join hG hH h1 h2

/-- **The Cartesian product of a `k`-regular and an `l`-regular graph is `(k + l)`-regular.** -/
theorem IsRegularWith.cartesianProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G □g H).IsRegularWith (k + l) :=
  isRegularWith_of_degSequence (degSequence_cartesianProduct hG.degSequence hH.degSequence)

/-- **The tensor product multiplies the degrees.** -/
theorem IsRegularWith.tensorProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G ⊗g H).IsRegularWith (k * l) :=
  isRegularWith_of_degSequence (degSequence_tensorProduct hG.degSequence hH.degSequence)

/-- **The strong product**, being the union of the other two, has degree `(k+1)(l+1) - 1`. -/
theorem IsRegularWith.strongProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G ⊠g H).IsRegularWith ((k + 1) * (l + 1) - 1) :=
  isRegularWith_of_degSequence (degSequence_strongProduct hG.degSequence hH.degSequence)

/-- **The lexicographic product**: a vertex sees `k` whole copies of `H` plus its `l` neighbours
inside its own copy. -/
theorem IsRegularWith.lexProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G ·g H).IsRegularWith (k * H.V + l) :=
  isRegularWith_of_degSequence (degSequence_lexProduct hG.degSequence hH.degSequence)

/-! #### The regularity table -/

@[simp] theorem isRegularWith_empty (n : ℕ) : (empty n).IsRegularWith 0 :=
  isRegularWith_of_degSequence (degSequence_empty n)

@[simp] theorem isRegularWith_complete (n : ℕ) : (complete n).IsRegularWith (n - 1) :=
  isRegularWith_of_degSequence (degSequence_complete n)

@[simp] theorem isRegularWith_cycle (n : ℕ) : (cycle (n + 3)).IsRegularWith 2 :=
  isRegularWith_of_degSequence (degSequence_cycle n)

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

/-! ### Degrees in the line graph -/

/-- The line graph of a `k`-regular graph is `(2k - 2)`-regular: an edge `uv` meets the `k - 1`
other edges at `u` and the `k - 1` other edges at `v`. -/
theorem IsRegularWith.lineGraph {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    (IsoGraph.lineGraph G).IsRegularWith (2 * k - 2) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [isRegularWith_mk] at h
  rw [lineGraph_mk, isRegularWith_mk]
  exact CGraph.IsRegularWith.lineGraph h

/-- Two edge counts of a regular graph: `L(G)` is `(2k - 2)`-regular on `|E|` vertices. -/
theorem IsRegularWith.two_mul_E_lineGraph {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    2 * (IsoGraph.lineGraph G).E = G.E * (2 * k - 2) := by
  have h2 := h.lineGraph.two_mul_E
  rwa [V_lineGraph] at h2

/-- Counting the pairs of edges at each vertex: `|E(L(G))| = n * C(k, 2)` for a `k`-regular
graph on `n` vertices.  This drops the strong regularity hypothesis of `IsSRGWith.E_lineGraph`. -/
theorem IsRegularWith.E_lineGraph {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    (IsoGraph.lineGraph G).E = G.V * k.choose 2 := by
  rw [IsoGraph.E_lineGraph, h.degSequence, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem maxDeg_lineGraph_le (G : IsoGraph) : (lineGraph G).maxDeg ≤ 2 * G.maxDeg - 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, lineGraph_mk, maxDeg_mk, maxDeg_mk]
  exact CGraph.maxDeg_lineGraph_le _

theorem le_minDeg_lineGraph {G : IsoGraph} (h : 0 < G.E) :
    2 * G.minDeg - 2 ≤ (lineGraph G).minDeg := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [E_mk] at h
  rw [lineGraph_mk, minDeg_mk, minDeg_mk]
  refine CGraph.le_minDeg_lineGraph _ ?_
  have hcard : 0 < Fintype.card (CGraph.lineGraph g.canonicalize).V := by
    rwa [CGraph.card_lineGraph]
  exact (Fintype.card_pos_iff.1 hcard).some

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

/-! ### Consequences of regularity -/

/-- A `k`-regular graph on a nonempty vertex set has more than `k` vertices. -/
theorem IsRegularWith.lt_V {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) (hV : 0 < G.V) :
    k < G.V := by
  rw [← h.maxDeg_eq hV]
  exact maxDeg_lt_V hV

/-- The degree of a regular graph is determined by the graph. -/
theorem IsRegularWith.unique {G : IsoGraph} {k l : ℕ} (hk : G.IsRegularWith k)
    (hl : G.IsRegularWith l) (hV : 0 < G.V) : k = l := by
  rw [← hk.maxDeg_eq hV, ← hl.maxDeg_eq hV]

/-- The handshake parity constraint: an odd-degree regular graph has an even number of
vertices.  There is no `3`-regular graph on five vertices. -/
theorem IsRegularWith.two_dvd_V {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) (hk : ¬ 2 ∣ k) :
    2 ∣ G.V := by
  have h2 : 2 ∣ G.V * k := ⟨G.E, h.two_mul_E.symm⟩
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 hk

/-- Greedy colouring on a regular graph. -/
theorem IsRegularWith.chromNum_le {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.chromNum ≤ k + 1 := by
  rcases Nat.eq_zero_or_pos G.V with hV | hV
  · have := G.chromNum_le_V
    omega
  · rw [← h.maxDeg_eq hV]
    exact G.chromNum_le_maxDeg_add_one

/-- A dominating set of a `k`-regular graph covers at most `k + 1` vertices per element. -/
theorem IsRegularWith.V_le_domNum_mul {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.V ≤ G.domNum * (k + 1) :=
  le_domNum_of_regular (h.maxDeg_eq hV)

/-- The greedy bound `α ≥ n / (k + 1)` for a `k`-regular graph. -/
theorem IsRegularWith.V_le_indepNum_mul {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.V ≤ G.indepNum * (k + 1) := by
  rw [← h.maxDeg_eq hV]
  exact G.V_le_indepNum_mul_maxDeg_add_one

theorem IsRegularWith.domNum_add_le {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.domNum + k ≤ G.V := by
  rw [← h.maxDeg_eq hV]
  exact G.domNum_add_maxDeg_le_V

/-- Each vertex of a cover of a `k`-regular graph is on `k` edges. -/
theorem IsRegularWith.E_le_coverNum_mul {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.E ≤ G.coverNum * k := by
  rw [← h.maxDeg_eq hV]
  exact G.E_le_coverNum_mul_maxDeg

theorem IsRegularWith.E_add_indepNum_mul_le {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.E + G.indepNum * k ≤ G.V * k := by
  rw [← h.maxDeg_eq hV]
  exact G.indepNum_mul_maxDeg_le

/-- The complement of a `k`-regular graph is `(n - 1 - k)`-regular, so its edge count is
also forced. -/
theorem IsRegularWith.two_mul_E_compl {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    2 * Gᶜ.E = G.V * (G.V - 1 - k) := by
  have h2 := h.compl.two_mul_E
  rwa [V_compl] at h2

/-- A `0`-regular graph has no edges at all. -/
theorem IsRegularWith.eq_empty {G : IsoGraph} (h : G.IsRegularWith 0) : G = empty G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [isRegularWith_mk] at h
  rw [V_mk]
  exact mk_eq_empty (CGraph.adj_eq_false_of_isRegularWith_zero h)

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

/-! ### The edge chromatic number

An edge colouring of `G` is a vertex colouring of `L(G)`, so the chromatic index is the
chromatic number of the line graph and needs no separate well-definedness argument. -/

/-- The *edge chromatic number* (chromatic index) `χ'(G)`: the least number of colours needed
to colour the edges of `G` so that edges meeting at a vertex get different colours. -/
noncomputable def edgeChromNum (G : IsoGraph) : ℕ := chromNum (lineGraph G)

theorem edgeChromNum_eq (G : IsoGraph) : G.edgeChromNum = chromNum (lineGraph G) := rfl

theorem maxDeg_le_cliqueNum_lineGraph (G : IsoGraph) :
    G.maxDeg ≤ (lineGraph G).cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, lineGraph_mk, maxDeg_mk, cliqueNum_mk]
  exact CGraph.maxDeg_le_cliqueNum_lineGraph _

/-- Every edge colouring uses at least `Δ` colours, since the edges at a vertex of maximum
degree pairwise conflict. -/
theorem maxDeg_le_edgeChromNum (G : IsoGraph) : G.maxDeg ≤ G.edgeChromNum :=
  le_trans G.maxDeg_le_cliqueNum_lineGraph (cliqueNum_le_chromNum _)

/-- Greedy colouring of the line graph: `χ'(G) ≤ 2Δ - 1`.  Vizing's theorem improves this to
`Δ + 1`, but that is a much deeper fact. -/
theorem edgeChromNum_le_two_mul_maxDeg_sub_one (G : IsoGraph) :
    G.edgeChromNum ≤ 2 * G.maxDeg - 1 := by
  rcases Nat.eq_zero_or_pos G.maxDeg with h | h
  · have hE := G.two_mul_E_le_V_mul_maxDeg
    rw [h, Nat.mul_zero] at hE
    have h2 : chromNum (lineGraph G) ≤ (lineGraph G).V := chromNum_le_V _
    rw [V_lineGraph] at h2
    rw [edgeChromNum_eq, h]
    omega
  · have h1 := (lineGraph G).chromNum_le_maxDeg_add_one
    have h2 := G.maxDeg_lineGraph_le
    rw [edgeChromNum_eq]
    omega

/-- The chromatic index of a `k`-regular graph is at least `k`. -/
theorem IsRegularWith.le_edgeChromNum {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : k ≤ G.edgeChromNum := by
  rw [← h.maxDeg_eq hV]
  exact maxDeg_le_edgeChromNum G

@[simp] theorem edgeChromNum_empty (n : ℕ) : (empty n).edgeChromNum = 0 := by
  rw [edgeChromNum_eq, lineGraph_empty, chromNum_empty_zero]

/-- Colouring the edges of a star is colouring the vertices of a complete graph. -/
@[simp] theorem edgeChromNum_star (n : ℕ) : (star n).edgeChromNum = n := by
  rw [edgeChromNum_eq, lineGraph_star, chromNum_complete]

@[simp] theorem edgeChromNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).edgeChromNum = max G.edgeChromNum H.edgeChromNum := by
  rw [edgeChromNum_eq, lineGraph_disjUnion, chromNum_disjUnion, edgeChromNum_eq, edgeChromNum_eq]

/-- `χ'(Petersen) ≥ 3`; the true value is `4`, which needs the fact that the Petersen graph has
no perfect matching decomposition. -/
example : 3 ≤ petersen.edgeChromNum :=
  isRegularWith_petersen.le_edgeChromNum (by rw [V_petersen]; omega)

example : petersen.edgeChromNum ≤ 5 := by
  have h := petersen.edgeChromNum_le_two_mul_maxDeg_sub_one
  rw [maxDeg_petersen] at h
  omega

example : (star 4).edgeChromNum = 4 := edgeChromNum_star 4


/-! ### The matching number

A matching is a set of pairwise disjoint edges, that is, an independent set in the line
graph, so like the chromatic index the matching number needs no separate construction. -/

/-- The *matching number* `ν(G)`: the largest number of pairwise disjoint edges. -/
noncomputable def matchNum (G : IsoGraph) : ℕ := indepNum (lineGraph G)

theorem matchNum_eq (G : IsoGraph) : G.matchNum = indepNum (lineGraph G) := rfl

theorem matchNum_le_E (G : IsoGraph) : G.matchNum ≤ G.E := by
  have h := (lineGraph G).coverNum_add_indepNum
  rw [V_lineGraph] at h
  rw [matchNum_eq]
  omega

/-- Each of the `ν` edges of a maximum matching uses two private vertices. -/
theorem two_mul_matchNum_le_V (G : IsoGraph) : 2 * G.matchNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, matchNum_eq, lineGraph_mk, indepNum_mk, V_mk]
  exact CGraph.two_mul_indepNum_lineGraph_le_card _

/-- Gallai's identity in the line graph: an edge cover of `L(G)` complements a matching. -/
theorem coverNum_lineGraph_add_matchNum (G : IsoGraph) :
    coverNum (lineGraph G) + G.matchNum = G.E := by
  have h := (lineGraph G).coverNum_add_indepNum
  rwa [V_lineGraph] at h

/-- Every colour class of an edge colouring is a matching, so `|E| ≤ χ' ν`. -/
theorem E_le_edgeChromNum_mul_matchNum (G : IsoGraph) :
    G.E ≤ G.edgeChromNum * G.matchNum := by
  have h := V_le_chromNum_mul_indepNum (lineGraph G)
  rwa [V_lineGraph] at h

theorem matchNum_pos (G : IsoGraph) (h : 0 < G.E) : 0 < G.matchNum := by
  rw [matchNum_eq]
  exact one_le_indepNum (by rwa [V_lineGraph])

@[simp] theorem matchNum_eq_zero_iff (G : IsoGraph) : G.matchNum = 0 ↔ G.E = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hE
    have := G.matchNum_pos (Nat.pos_of_ne_zero hE)
    omega
  · have := G.matchNum_le_E
    omega

@[simp] theorem matchNum_empty (n : ℕ) : (empty n).matchNum = 0 := by
  rw [matchNum_eq, lineGraph_empty, indepNum_empty]

/-- A star has a single edge available to any matching. -/
@[simp] theorem matchNum_star (n : ℕ) : (star n).matchNum = min n 1 := by
  rw [matchNum_eq, lineGraph_star, indepNum_complete]

@[simp] theorem matchNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).matchNum = G.matchNum + H.matchNum := by
  rw [matchNum_eq, lineGraph_disjUnion, indepNum_disjUnion, matchNum_eq, matchNum_eq]

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


/-! ### Matchings and edge colourings of the named families

Whenever the line graph of a family is itself a named graph, the matching number and the
chromatic index of that family are read off from the independence and chromatic numbers of
the line graph, which are already known. -/

@[simp] theorem edgeChromNum_eq_zero_iff {G : IsoGraph} : G.edgeChromNum = 0 ↔ G.E = 0 := by
  rw [edgeChromNum_eq, chromNum_eq_zero_iff, V_lineGraph]

theorem edgeChromNum_pos {G : IsoGraph} (h : 0 < G.E) : 0 < G.edgeChromNum := by
  rcases Nat.eq_zero_or_pos G.edgeChromNum with h0 | h0
  · rw [edgeChromNum_eq_zero_iff] at h0; omega
  · exact h0

/-- Combining `|E| ≤ χ' ν` with `χ' ≤ 2Δ - 1`. -/
theorem E_le_two_mul_maxDeg_sub_one_mul_matchNum (G : IsoGraph) :
    G.E ≤ (2 * G.maxDeg - 1) * G.matchNum := by
  refine le_trans G.E_le_edgeChromNum_mul_matchNum ?_
  exact Nat.mul_le_mul_right _ G.edgeChromNum_le_two_mul_maxDeg_sub_one

/-- The line graph of a cycle is that same cycle, so a maximum matching of `C_n` is a maximum
independent set of `C_n`. -/
@[simp] theorem matchNum_cycle (n : ℕ) : (cycle (n + 3)).matchNum = (n + 3) / 2 := by
  rw [matchNum_eq, lineGraph_cycle, indepNum_cycle]

@[simp] theorem matchNum_complete_three : (complete 3).matchNum = 1 := by
  rw [matchNum_eq, lineGraph_complete_three, indepNum_complete]
  omega

/-- `L(K₄)` is the octahedron, whose independence number is `2`: `K₄` has a perfect matching. -/
@[simp] theorem matchNum_complete_four : (complete 4).matchNum = 2 := by
  rw [matchNum_eq, lineGraph_complete_four]
  exact indepNum_cocktailParty 2

/-- `L(K_{m,n})` is the rook's graph, so a matching of the complete bipartite graph is a
partial permutation matrix and there are at most `min m n` of them. -/
theorem matchNum_bipartite_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (bipartite m n).matchNum ≤ min m n := by
  rw [matchNum_eq, lineGraph_bipartite]
  exact indepNum_rook_le m n hm hn

/-- An even cycle is `2`-edge-colourable. -/
@[simp] theorem edgeChromNum_cycle_even (m : ℕ) : (cycle (2 * m + 4)).edgeChromNum = 2 := by
  rw [edgeChromNum_eq, show 2 * m + 4 = 2 * m + 1 + 3 by ring, lineGraph_cycle,
    show 2 * m + 1 + 3 = 2 * (m + 1) + 2 by ring, chromNum_cycle_even]

/-- An odd cycle needs three edge colours. -/
@[simp] theorem edgeChromNum_cycle_odd (m : ℕ) : (cycle (2 * m + 3)).edgeChromNum = 3 := by
  rw [edgeChromNum_eq, lineGraph_cycle, chromNum_cycle_odd]

/-- `L(P_n)` is `P_{n-1}`, so a path with at least two edges is `2`-edge-colourable. -/
@[simp] theorem edgeChromNum_path (n : ℕ) : (path (n + 3)).edgeChromNum = 2 := by
  rw [edgeChromNum_eq, lineGraph_path, chromNum_path]

@[simp] theorem edgeChromNum_complete_three : (complete 3).edgeChromNum = 3 := by
  rw [edgeChromNum_eq, lineGraph_complete_three, chromNum_complete]

/-- `χ'(K₄) = 3`: its line graph is the octahedron `K_{2,2,2}`, which is `3`-chromatic. -/
@[simp] theorem edgeChromNum_complete_four : (complete 4).edgeChromNum = 3 := by
  rw [edgeChromNum_eq, lineGraph_complete_four, chromNum_cocktailParty]

example : (cycle 5).matchNum = 2 := by rw [show (5 : ℕ) = 2 + 3 by ring, matchNum_cycle]

example : (cycle 6).edgeChromNum = 2 := by
  rw [show (6 : ℕ) = 2 * 1 + 4 by ring, edgeChromNum_cycle_even]

/-- `C₅` is not `2`-edge-colourable even though it is `2`-regular. -/
example : (cycle 5).edgeChromNum = 3 := by
  rw [show (5 : ℕ) = 2 * 1 + 3 by ring, edgeChromNum_cycle_odd]


/-! ### Matchings versus independent sets and covers -/

/-- Since an independent set meets each edge of a matching at most once, `ν + α ≤ n`. -/
theorem matchNum_add_indepNum_le_V (G : IsoGraph) : G.matchNum + G.indepNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, matchNum_eq, lineGraph_mk, indepNum_mk, indepNum_mk, V_mk]
  exact CGraph.indepNum_lineGraph_add_indepNum_le_card _

/-- `ν ≤ τ`: distinct edges of a matching need distinct vertices of a vertex cover.  Here it
falls out of `ν + α ≤ n` and Gallai's identity `τ + α = n`. -/
theorem matchNum_le_coverNum (G : IsoGraph) : G.matchNum ≤ G.coverNum := by
  have h1 := G.matchNum_add_indepNum_le_V
  have h2 := G.coverNum_add_indepNum
  omega

/-- A graph with a perfect matching has independence number at most `n / 2`. -/
theorem two_mul_indepNum_le_V_of_two_mul_matchNum_eq (G : IsoGraph)
    (h : 2 * G.matchNum = G.V) : 2 * G.indepNum ≤ G.V := by
  have h1 := G.matchNum_add_indepNum_le_V
  omega

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


/-! ### Girth three from strong regularity and from line graphs -/

/-- The edges at a vertex of degree three form a triangle in the line graph. -/
theorem girth_lineGraph_eq_three {G : IsoGraph} (h : 3 ≤ G.maxDeg) :
    (IsoGraph.lineGraph G).girth = 3 :=
  girth_eq_three_of_cliqueNum (le_trans h G.maxDeg_le_cliqueNum_lineGraph)

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


/-! ### The clique cover number

A partition of the vertices into cliques of `G` is a proper colouring of the complement, so
`θ(G) = χ(Ḡ)`.  As with the chromatic index this is a definition on `IsoGraph` built from
existing pieces, and every statement about it is a statement about `chromNum` in disguise. -/

/-- The *clique cover number* `θ(G)`: the least number of cliques needed to cover the
vertices. -/
noncomputable def cliqueCoverNum (G : IsoGraph) : ℕ := chromNum Gᶜ

theorem cliqueCoverNum_eq (G : IsoGraph) : G.cliqueCoverNum = chromNum Gᶜ := rfl

@[simp] theorem cliqueCoverNum_compl (G : IsoGraph) :
    Gᶜ.cliqueCoverNum = G.chromNum := by
  rw [cliqueCoverNum_eq, compl_compl]

@[simp] theorem chromNum_compl (G : IsoGraph) :
    Gᶜ.chromNum = G.cliqueCoverNum := rfl

/-- `α ≤ θ`, the complement of `ω ≤ χ`: a clique cover needs a separate clique for each vertex
of an independent set. -/
theorem indepNum_le_cliqueCoverNum (G : IsoGraph) : G.indepNum ≤ G.cliqueCoverNum := by
  rw [cliqueCoverNum_eq, ← cliqueNum_compl]
  exact cliqueNum_le_chromNum _

theorem cliqueCoverNum_le_V (G : IsoGraph) : G.cliqueCoverNum ≤ G.V := by
  have h := chromNum_le_V Gᶜ
  rwa [V_compl] at h

/-- `n ≤ θ ω`, the complement of `n ≤ χ α`: each of the `θ` cliques has at most `ω` vertices. -/
theorem V_le_cliqueCoverNum_mul_cliqueNum (G : IsoGraph) :
    G.V ≤ G.cliqueCoverNum * G.cliqueNum := by
  have h := V_le_chromNum_mul_indepNum Gᶜ
  rwa [V_compl, indepNum_compl] at h

theorem cliqueCoverNum_le_V_sub_cliqueNum_add_one (G : IsoGraph) :
    G.cliqueCoverNum ≤ G.V - G.cliqueNum + 1 := by
  have h := chromNum_le_V_sub_indepNum_add_one Gᶜ
  rwa [V_compl, indepNum_compl] at h

@[simp] theorem cliqueCoverNum_eq_zero_iff {G : IsoGraph} : G.cliqueCoverNum = 0 ↔ G.V = 0 := by
  rw [cliqueCoverNum_eq, chromNum_eq_zero_iff, V_compl]

/-- An edgeless graph needs one clique per vertex. -/
@[simp] theorem cliqueCoverNum_empty (n : ℕ) : (empty n).cliqueCoverNum = n := by
  rw [cliqueCoverNum_eq, compl_empty, chromNum_complete]

@[simp] theorem cliqueCoverNum_complete_zero : (complete 0).cliqueCoverNum = 0 := by
  rw [cliqueCoverNum_eq, compl_complete, chromNum_empty_zero]

@[simp] theorem cliqueCoverNum_complete (n : ℕ) : (complete (n + 1)).cliqueCoverNum = 1 := by
  rw [cliqueCoverNum_eq, compl_complete, chromNum_empty]

/-- Cliques never cross a disjoint union, so the clique covers add. -/
@[simp] theorem cliqueCoverNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).cliqueCoverNum = G.cliqueCoverNum + H.cliqueCoverNum := by
  rw [cliqueCoverNum_eq, compl_disjUnion, chromNum_join, cliqueCoverNum_eq, cliqueCoverNum_eq]

@[simp] theorem cliqueCoverNum_join (G H : IsoGraph) :
    (G ∇g H).cliqueCoverNum = max G.cliqueCoverNum H.cliqueCoverNum := by
  rw [cliqueCoverNum_eq, compl_join, chromNum_disjUnion, cliqueCoverNum_eq, cliqueCoverNum_eq]

/-- A complete bipartite graph is covered by `max m n` edges and singletons. -/
@[simp] theorem cliqueCoverNum_bipartite (m n : ℕ) :
    (bipartite m n).cliqueCoverNum = max m n := by
  rw [cliqueCoverNum_eq, compl_bipartite, chromNum_disjUnion, chromNum_complete,
    chromNum_complete]

@[simp] theorem cliqueCoverNum_star (n : ℕ) : (star n).cliqueCoverNum = max 1 n :=
  cliqueCoverNum_bipartite 1 n

/-- `C₅` is self-complementary, so `θ(C₅) = χ(C₅) = 3` even though `ω(C₅) = 2`. -/
@[simp] theorem cliqueCoverNum_cycle_five : (cycle 5).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_eq, compl_cycle_five, show (5 : ℕ) = 2 * 1 + 3 by ring, chromNum_cycle_odd]

example : (empty 4).cliqueCoverNum = 4 := cliqueCoverNum_empty 4

example : (cycle 5).indepNum ≤ (cycle 5).cliqueCoverNum := indepNum_le_cliqueCoverNum _

/-- The clique cover bound is tight for a disjoint union of triangles. -/
example : (complete 3 ⊕g complete 3).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_disjUnion, show (3 : ℕ) = 2 + 1 by ring, cliqueCoverNum_complete]


/-! ### Nordhaus–Gaddum for the clique cover number

Every bound relating a graph to its complement can be read as a bound relating the chromatic
number to the clique cover number. -/

/-- `n ≤ χ θ`: the `χ` colour classes are independent sets, so `θ` of them cover `G`. -/
theorem V_le_chromNum_mul_cliqueCoverNum (G : IsoGraph) :
    G.V ≤ G.chromNum * G.cliqueCoverNum :=
  G.V_le_chromNum_mul_chromNum_compl

/-- The Nordhaus–Gaddum upper bound, in clique cover form. -/
theorem chromNum_add_cliqueCoverNum_le_V_add_one (G : IsoGraph) :
    G.chromNum + G.cliqueCoverNum ≤ G.V + 1 :=
  G.chromNum_add_chromNum_compl_le_V_add_one

theorem four_mul_V_le_chromNum_add_cliqueCoverNum_sq (G : IsoGraph) :
    4 * G.V ≤ (G.chromNum + G.cliqueCoverNum) ^ 2 :=
  G.four_mul_V_le_chromNum_add_chromNum_compl_sq

/-- Each connected component needs a clique of its own. -/
theorem numComponents_le_cliqueCoverNum (G : IsoGraph) :
    G.numComponents ≤ G.cliqueCoverNum :=
  le_trans G.numComponents_le_indepNum G.indepNum_le_cliqueCoverNum

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

/-- A bipartite graph with an edge has `χ = ω = 2`. -/
theorem chromNum_eq_cliqueNum_of_isBipartite {G : IsoGraph} (hb : IsBipartite G) (hE : 0 < G.E) :
    G.chromNum = G.cliqueNum := by
  have h1 : G.chromNum = 2 := chromNum_eq_two_iff.2 ⟨hb, hE⟩
  have h2 := cliqueNum_le_two_of_isBipartite hb
  have h3 := two_le_cliqueNum_of_E_pos hE
  omega

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

/-! ### Acyclicity from girth

`girth_eq_zero_iff` says that a graph is acyclic exactly when its girth is `0`, so every entry
in the girth table for the named families immediately rules out acyclicity — and, since a tree is
in particular acyclic, rules out being a tree as well. -/

theorem not_isAcyclic_of_girth_pos {G : IsoGraph} (h : 0 < G.girth) : ¬ IsAcyclic G := by
  rw [← girth_eq_zero_iff]
  omega

theorem girth_pos_of_not_isAcyclic {G : IsoGraph} (h : ¬ IsAcyclic G) : 0 < G.girth :=
  Nat.pos_of_ne_zero fun h0 ↦ h (girth_eq_zero_iff.1 h0)

theorem not_isTree_of_girth_pos {G : IsoGraph} (h : 0 < G.girth) : ¬ IsTree G :=
  fun ht ↦ not_isAcyclic_of_girth_pos h ((isTree_iff_isConnected_and_isAcyclic G).1 ht).2

/-- An acyclic graph has no triangle, so no clique on three vertices. -/
theorem cliqueNum_le_two_of_isAcyclic {G : IsoGraph} (h : IsAcyclic G) : G.cliqueNum ≤ 2 := by
  by_contra hc
  exact not_isAcyclic_of_girth_pos
    (by rw [girth_eq_three_of_cliqueNum (by omega)]; omega) h

theorem cliqueCount_three_eq_zero_of_isAcyclic {G : IsoGraph} (h : IsAcyclic G) :
    G.cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_iff G |>.2 (by rw [girth_eq_zero_iff.2 h]; omega)

/-- A tree on at least two vertices has an edge, and no triangle. -/
theorem cliqueNum_of_isTree {G : IsoGraph} (h : IsTree G) (hV : 2 ≤ G.V) : G.cliqueNum = 2 := by
  have h1 := h.E_add_one
  have h2 := two_le_cliqueNum_of_E_pos (G := G) (by omega)
  have h3 := cliqueNum_le_two_of_isAcyclic ((isTree_iff_isConnected_and_isAcyclic G).1 h).2
  omega

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

/-- A graph with a vertex of degree at least three has a triangle in its line graph. -/
theorem not_isAcyclic_lineGraph {G : IsoGraph} (h : 3 ≤ G.maxDeg) :
    ¬ IsAcyclic (IsoGraph.lineGraph G) :=
  not_isAcyclic_of_girth_pos (by rw [girth_lineGraph_eq_three h]; omega)

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

/-! ### Bounds on the chromatic index of the regular families -/

theorem sub_one_le_edgeChromNum_complete (n : ℕ) : n - 1 ≤ (complete n).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (complete n)
  rwa [maxDeg_complete] at h

theorem edgeChromNum_complete_le (n : ℕ) : (complete n).edgeChromNum ≤ 2 * (n - 1) - 1 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (complete n)
  rwa [maxDeg_complete] at h

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

theorem matchNum_complete_le (n : ℕ) : (complete n).matchNum ≤ n / 2 := by
  have h := two_mul_matchNum_le_V (complete n)
  rw [V_complete] at h
  omega

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

/-! ### The two-approximation for vertex covers

A maximum matching leaves an independent set behind, so `|V| ≤ α + 2ν`; with Gallai's identity
`α + τ = |V|` this is the classical `τ ≤ 2ν`.  Together with `ν ≤ τ` it says that a maximum
matching always determines the vertex cover number to within a factor of two. -/

theorem V_le_indepNum_add_two_mul_matchNum (G : IsoGraph) :
    G.V ≤ G.indepNum + 2 * G.matchNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, indepNum_mk, matchNum_eq, lineGraph_mk, indepNum_mk]
  exact CGraph.card_le_indepNum_add_two_mul_indepNum_lineGraph _

/-- **The vertex cover number is at most twice the matching number.**  This is the guarantee
behind the greedy two-approximation algorithm for minimum vertex cover. -/
theorem coverNum_le_two_mul_matchNum (G : IsoGraph) : G.coverNum ≤ 2 * G.matchNum := by
  have h1 := G.V_le_indepNum_add_two_mul_matchNum
  have h2 := G.coverNum_add_indepNum
  omega

theorem matchNum_le_coverNum_le_two_mul_matchNum (G : IsoGraph) :
    G.matchNum ≤ G.coverNum ∧ G.coverNum ≤ 2 * G.matchNum :=
  ⟨G.matchNum_le_coverNum, G.coverNum_le_two_mul_matchNum⟩

theorem V_le_two_mul_coverNum_of_two_mul_matchNum_eq {G : IsoGraph} (h : 2 * G.matchNum = G.V) :
    G.V ≤ 2 * G.coverNum := by
  have h1 := G.matchNum_le_coverNum
  omega

example : (cycle 5).coverNum ≤ 4 := by
  have h := (cycle 5).coverNum_le_two_mul_matchNum
  rw [show (5 : ℕ) = 2 + 3 by ring, matchNum_cycle] at h
  omega

example (G : IsoGraph) (h : G.matchNum = 0) : G.coverNum = 0 := by
  have := G.coverNum_le_two_mul_matchNum
  omega


/-! ### Self-complementary graphs -/

/-- A graph is *self-complementary* when it is isomorphic to its own complement.  Because
`IsoGraph` is the quotient of graphs by isomorphism, this is literally the equation
`Gᶜ = G`. -/
def IsSelfComplementary (G : IsoGraph) : Prop := Gᶜ = G

theorem isSelfComplementary_iff {G : IsoGraph} :
    IsSelfComplementary G ↔ Gᶜ = G := Iff.rfl

theorem IsSelfComplementary.compl_eq {G : IsoGraph} (h : IsSelfComplementary G) :
    Gᶜ = G := h

theorem isSelfComplementary_compl {G : IsoGraph} (h : IsSelfComplementary G) :
    IsSelfComplementary Gᶜ := by
  show Gᶜᶜ = Gᶜ
  rw [compl_compl, h.compl_eq]

@[simp] theorem isSelfComplementary_empty_zero : IsSelfComplementary (empty 0) := by
  show (empty 0)ᶜ = empty 0
  rw [compl_empty, complete_zero]

@[simp] theorem isSelfComplementary_empty_one : IsSelfComplementary (empty 1) := by
  show (empty 1)ᶜ = empty 1
  rw [compl_empty, complete_one]

@[simp] theorem isSelfComplementary_path_four : IsSelfComplementary (path 4) :=
  compl_path_four

@[simp] theorem isSelfComplementary_cycle_five : IsSelfComplementary (cycle 5) :=
  compl_cycle_five

@[simp] theorem isSelfComplementary_paley_thirteen : IsSelfComplementary (paley 13) :=
  compl_paley_thirteen

@[simp] theorem isSelfComplementary_paley_seventeen : IsSelfComplementary (paley 17) :=
  compl_paley_seventeen

/-! ### Consequences of self-complementarity -/

/-- A self-complementary graph has exactly half of all possible edges. -/
theorem IsSelfComplementary.two_mul_E {G : IsoGraph} (h : IsSelfComplementary G) :
    2 * G.E = G.V.choose 2 := by
  have h2 := E_compl_add G
  rw [h.compl_eq] at h2
  omega

theorem IsSelfComplementary.cliqueNum_eq_indepNum {G : IsoGraph} (h : IsSelfComplementary G) :
    G.cliqueNum = G.indepNum := by
  have h2 := cliqueNum_compl G
  rwa [h.compl_eq] at h2

theorem IsSelfComplementary.chromNum_eq_cliqueCoverNum {G : IsoGraph}
    (h : IsSelfComplementary G) : G.chromNum = G.cliqueCoverNum := by
  have h2 := chromNum_compl G
  rwa [h.compl_eq] at h2

/-- Since `V ≤ χ(G) * χGᶜ`, a self-complementary graph needs at least `√V` colours. -/
theorem IsSelfComplementary.V_le_chromNum_sq {G : IsoGraph} (h : IsSelfComplementary G) :
    G.V ≤ G.chromNum * G.chromNum := by
  have h2 := V_le_chromNum_mul_chromNum_compl G
  rwa [h.compl_eq] at h2

/-- The Nordhaus–Gaddum upper bound, specialised to a self-complementary graph. -/
theorem IsSelfComplementary.two_mul_chromNum_le {G : IsoGraph} (h : IsSelfComplementary G) :
    2 * G.chromNum ≤ G.V + 1 := by
  have h2 := four_mul_chromNum_mul_chromNum_compl_le G
  rw [h.compl_eq, show (G.V + 1) ^ 2 = G.V * G.V + 2 * G.V + 1 from by ring] at h2
  by_contra hc
  have hle : (G.V + 2) * (G.V + 2) ≤ 2 * G.chromNum * (2 * G.chromNum) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [show (G.V + 2) * (G.V + 2) = G.V * G.V + 4 * G.V + 4 from by ring,
    show 2 * G.chromNum * (2 * G.chromNum) = 4 * (G.chromNum * G.chromNum) from by ring] at hle
  omega

theorem IsSelfComplementary.three_le_chromNum {G : IsoGraph} (h : IsSelfComplementary G)
    (hV : 5 ≤ G.V) : 3 ≤ G.chromNum := by
  have h2 := h.V_le_chromNum_sq
  by_contra hc
  have h3 : G.chromNum * G.chromNum ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem IsSelfComplementary.not_isBipartite {G : IsoGraph} (h : IsSelfComplementary G)
    (hV : 5 ≤ G.V) : ¬ IsBipartite G := by
  intro hb
  have h2 := isBipartite_iff_chromNum_le_two.1 hb
  have h3 := h.three_le_chromNum hV
  omega

theorem IsSelfComplementary.E_pos {G : IsoGraph} (h : IsSelfComplementary G) (hV : 2 ≤ G.V) :
    0 < G.E := by
  have h2 := h.two_mul_E
  have h3 := Nat.choose_pos hV
  omega

/-- A self-complementary graph is connected: otherwise its complement, which is the graph
itself, would have diameter two. -/
theorem IsSelfComplementary.isConnected {G : IsoGraph} (h : IsSelfComplementary G)
    (hV : 2 ≤ G.V) : IsConnected G := by
  by_contra hc
  have hd := diameter_compl hc (h.E_pos hV)
  rw [h.compl_eq] at hd
  exact hc (isConnected_of_diameter_ne_zero (by omega))

/-- A self-complementary graph has `0` or `1` vertices mod `4`, since it has half of all
`V.choose 2` possible edges. -/
theorem IsSelfComplementary.V_mod_four {G : IsoGraph} (h : IsSelfComplementary G) :
    G.V % 4 = 0 ∨ G.V % 4 = 1 := by
  have h2 := h.two_mul_E
  exact (choose_two_mod_two_eq_zero_iff G.V).1 (by omega)

/-! ### Graphs that are not self-complementary -/

theorem not_isSelfComplementary_empty (n : ℕ) : ¬ IsSelfComplementary (empty (n + 2)) := by
  intro h
  have h2 := h.two_mul_E
  rw [E_empty, V_empty] at h2
  have h3 := Nat.choose_pos (show 2 ≤ n + 2 by omega)
  omega

theorem not_isSelfComplementary_complete (n : ℕ) : ¬ IsSelfComplementary (complete (n + 2)) := by
  intro h
  have h2 := h.two_mul_E
  rw [E_complete, V_complete] at h2
  have h3 := Nat.choose_pos (show 2 ≤ n + 2 by omega)
  omega

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


/-! ### Line graphs of regular graphs -/

theorem pos_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) : 0 < n := by
  have h2 := two_mul_E_of_degSequence_replicate h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_mul] at h2
    omega
  · exact hn

theorem maxDeg_eq_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degSequence G = List.replicate n k) : maxDeg G = k :=
  maxDeg_of_degMultiset_replicate hn (degMultiset_of_degSequence h)

theorem minDeg_eq_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degSequence G = List.replicate n k) : minDeg G = k :=
  minDeg_of_degMultiset_replicate hn (degMultiset_of_degSequence h)

/-- A `k`-regular graph on `n` vertices has a line graph with `n * k.choose 2` edges: one for
each pair of edges meeting at a common vertex. -/
theorem E_lineGraph_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : (lineGraph G).E = n * k.choose 2 := by
  rw [E_lineGraph, h, List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- Counting the same edges through `|E| = n * k / 2`. -/
theorem two_mul_E_lineGraph_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) :
    2 * (lineGraph G).E = 2 * G.E * (k - 1) := by
  have h1 := E_lineGraph_of_degSequence_replicate h
  have h2 := two_mul_E_of_degSequence_replicate h
  calc 2 * (lineGraph G).E = n * (2 * k.choose 2) := by rw [h1]; ring
    _ = n * (k * (k - 1)) := by rw [two_mul_choose_two]
    _ = n * k * (k - 1) := by rw [Nat.mul_assoc]
    _ = 2 * G.E * (k - 1) := by rw [h2]

/-- **The line graph of a `k`-regular graph is `(2k - 2)`-regular.** -/
theorem isRegularWith_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    (lineGraph G).IsRegularWith (2 * k - 2) := by
  have hn := pos_of_degSequence_replicate hE h
  refine isRegularWith_of_maxDeg_le_of_le_minDeg ?_ ?_
  · have h3 := maxDeg_lineGraph_le G
    rwa [maxDeg_eq_of_degSequence_replicate hn h] at h3
  · have h3 := le_minDeg_lineGraph hE
    rwa [minDeg_eq_of_degSequence_replicate hn h] at h3

theorem maxDeg_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) : maxDeg (lineGraph G) = 2 * k - 2 := by
  have hn := pos_of_degSequence_replicate hE h
  have h1 := maxDeg_lineGraph_le G
  rw [maxDeg_eq_of_degSequence_replicate hn h] at h1
  have h2 := le_minDeg_lineGraph hE
  rw [minDeg_eq_of_degSequence_replicate hn h] at h2
  have h3 := minDeg_le_maxDeg (lineGraph G)
  omega

theorem minDeg_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) : minDeg (lineGraph G) = 2 * k - 2 := by
  have hn := pos_of_degSequence_replicate hE h
  have h1 := maxDeg_lineGraph_le G
  rw [maxDeg_eq_of_degSequence_replicate hn h] at h1
  have h2 := le_minDeg_lineGraph hE
  rw [minDeg_eq_of_degSequence_replicate hn h] at h2
  have h3 := minDeg_le_maxDeg (lineGraph G)
  omega

end IsoGraph
