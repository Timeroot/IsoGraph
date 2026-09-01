import IsoGraph.SmallGraphs.Operators

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The sporadic strongly regular graphs: the elementary invariants

The ten graphs of `SmallGraphs.Defs.SRG` that are not members of a family — the Shrikhande
graph, the lines on a cubic surface and the Schläfli graph, the three Chang graphs, and the
Hoffman–Singleton, Gewirtz, `M₂₂` and Higman–Sims graphs — arrive knowing only their
parameters, proved by a decision procedure over a hundred vertices at worst.  Almost everything
below is read off those parameters by the general theory in `Core.Symmetry`; the exceptions are
the five **clique numbers** of the graphs on 16 to 28 vertices, where the parameters give only a
bound and the exact value needs a maximum clique and a refutation of the next size up, and the ten
**matching numbers**, each an explicit list of disjoint edges.  Seven of the ten matchings are
perfect and the other three miss one vertex, because the graph has an odd number of them; for the
four triangle-free graphs that settles the **clique cover number** as well, since there a clique
is a vertex or an edge.  Those same three odd orders are what makes the **chromatic indices**
interesting: seven of the ten graphs are class one and three are class two, and the ten
`1`-factorizations are written out.  A last explicit table makes all ten **Hamiltonian**, one
spanning cycle each.  **Transitivity** is not read off the parameters either but decided
outright: seven of the ten are arc-transitive, and the three Chang graphs are not even
vertex-transitive.

Order, size, degrees and connectivity are immediate.  The three that take an argument are:

* the **diameter and radius** are two, because `μ > 0` puts a common neighbour between any two
  non-adjacent vertices and no vertex of a non-complete strongly regular graph sees everyone;
* the **girth** is three when `ℓ > 0`, four when `ℓ = 0` and `μ ≥ 2`, and five for the
  Hoffman–Singleton graph, the one Moore graph here;
* none is **bipartite**, since a bipartite strongly regular graph with `μ > 0` is complete
  bipartite and so has `n = 2k`.

The spectral invariants of the same ten graphs — spectrum, energy, algebraic connectivity, and the
independence, vertex cover and chromatic numbers that the ratio bound pins down — are in
`IsoGraph/Spectrum.lean`, which sits above this file.

A last section does the same for the Paley graph of a finite field, which has a parameter but is
read off `(n, k, ℓ, μ)` in exactly the same way.
-/

namespace IsoGraph

/-! ## The Shrikhande graph

The `(16, 6, 2, 2)` graph that is *not* the rook's graph `K₄ □ K₄`: same parameters, different
graph, and the first pair to show that the parameters do not determine a strongly regular graph. -/

@[simp] theorem V_shrikhande : shrikhande.V = 16 := shrikhande_srg.V_eq

@[simp] theorem E_shrikhande : shrikhande.E = 48 := by
  have := shrikhande_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_shrikhande : shrikhande.IsRegularWith 6 :=
  shrikhande_srg.isRegularWith

@[simp] theorem maxDeg_shrikhande : maxDeg shrikhande = 6 := shrikhande_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_shrikhande : minDeg shrikhande = 6 := shrikhande_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_shrikhande : degSequence shrikhande = List.replicate 16 6 :=
  shrikhande_srg.degSequence

@[simp] theorem degMultiset_shrikhande : degMultiset shrikhande = Multiset.replicate 16 6 :=
  shrikhande_srg.degMultiset

@[simp] theorem isConnected_shrikhande : IsConnected shrikhande :=
  shrikhande_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_shrikhande : shrikhande.numComponents = 1 :=
  shrikhande_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_shrikhande : shrikhande.diameter = 2 :=
  shrikhande_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_shrikhande : shrikhande.radius = 2 :=
  shrikhande_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_shrikhande : shrikhande.edgeConn = 6 :=
  shrikhande_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 2`, so the two ends of an edge have a common neighbour. -/
@[simp] theorem girth_shrikhande : shrikhande.girth = 3 :=
  shrikhande_srg.girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_shrikhande : ¬ IsAcyclic shrikhande :=
  not_isAcyclic_of_girth_pos (by rw [girth_shrikhande]; omega)

@[simp] theorem not_isTree_shrikhande : ¬ IsTree shrikhande :=
  not_isTree_of_girth_pos (by rw [girth_shrikhande]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `16 ≠ 2 · 6`. -/
@[simp] theorem not_isBipartite_shrikhande : ¬ IsBipartite shrikhande :=
  shrikhande_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `60` edges, not `48`. -/
@[simp] theorem not_isSelfComplementary_shrikhande : ¬ IsSelfComplementary shrikhande := by
  intro h
  have h2 := h.two_mul_E
  rw [E_shrikhande, V_shrikhande] at h2
  have h3 : (16 : ℕ).choose 2 = 120 := rfl
  omega

/-- **The clique number of the Shrikhande graph is three.**  `ℓ = 2` allows four, but the bound is
not attained: the Shrikhande graph is locally a hexagon, so a neighbourhood spans no triangle and
the triangles are all one gets.  This is the cheapest place to see the difference from the rook's
graph `K₄ □ K₄`, which has the same parameters and clique number four. -/
@[simp] theorem cliqueNum_shrikhande : shrikhande.cliqueNum = 3 :=
  le_antisymm (by graph_sat native)
    (shrikhande_srg.three_le_cliqueNum (by omega) (by omega) (by omega))

/-- `16 · 6 · 2 / 6`, from the parameters alone. -/
@[simp] theorem cliqueCount_shrikhande : shrikhande.cliqueCount 3 = 32 := by
  have h := shrikhande_srg.six_mul_cliqueCount_three
  omega

/-- And `16 · 9 · 4 / 6` independent triples, from the complementary parameters. -/
@[simp] theorem indepCount_shrikhande : shrikhande.indepCount 3 = 96 := by
  have h := shrikhande_srg.six_mul_indepCount_three
  omega

theorem six_le_cliqueCoverNum_shrikhande : 6 ≤ shrikhande.cliqueCoverNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum shrikhande
  rw [V_shrikhande, cliqueNum_shrikhande] at h
  omega

theorem three_le_domNum_shrikhande : 3 ≤ shrikhande.domNum := by
  have h := le_domNum_of_regular (G := shrikhande) (k := 6) maxDeg_shrikhande
  rw [V_shrikhande] at h
  omega

/-- A perfect matching of the Shrikhande graph, as pairs of `FinEnum` indices. -/
def shrikhandeMatching : List (Fin 16 × Fin 16) :=
  [(0, 15), (1, 13), (2, 14), (3, 7), (4, 9), (5, 10), (6, 11), (8, 12)]

/-- **The Shrikhande graph has a perfect matching**, so `ν = 8`.  The upper bound is `2ν ≤ n` and
needs nothing about the graph. -/
@[simp] theorem matchNum_shrikhande : shrikhande.matchNum = 8 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V shrikhande
    rw [V_shrikhande] at h
    omega
  · rw [shrikhande_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.shrikhande.V))
      shrikhandeMatching (by native_decide) (by decide)

/-! ## The lines on a cubic surface

The `(27, 10, 1, 5)` graph on the twenty-seven lines of a smooth cubic surface, two lines
adjacent when they meet.  Its complement is the Schläfli graph. -/

@[simp] theorem V_linesOnCubic : linesOnCubic.V = 27 := linesOnCubic_srg.V_eq

@[simp] theorem E_linesOnCubic : linesOnCubic.E = 135 := by
  have := linesOnCubic_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_linesOnCubic : linesOnCubic.IsRegularWith 10 :=
  linesOnCubic_srg.isRegularWith

@[simp] theorem maxDeg_linesOnCubic : maxDeg linesOnCubic = 10 :=
  linesOnCubic_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_linesOnCubic : minDeg linesOnCubic = 10 :=
  linesOnCubic_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_linesOnCubic : degSequence linesOnCubic = List.replicate 27 10 :=
  linesOnCubic_srg.degSequence

@[simp] theorem degMultiset_linesOnCubic : degMultiset linesOnCubic = Multiset.replicate 27 10 :=
  linesOnCubic_srg.degMultiset

@[simp] theorem isConnected_linesOnCubic : IsConnected linesOnCubic :=
  linesOnCubic_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_linesOnCubic : linesOnCubic.numComponents = 1 :=
  linesOnCubic_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_linesOnCubic : linesOnCubic.diameter = 2 :=
  linesOnCubic_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_linesOnCubic : linesOnCubic.radius = 2 :=
  linesOnCubic_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_linesOnCubic : linesOnCubic.edgeConn = 10 :=
  linesOnCubic_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 1`, so the two ends of an edge have a common neighbour. -/
@[simp] theorem girth_linesOnCubic : linesOnCubic.girth = 3 :=
  linesOnCubic_srg.girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_linesOnCubic : ¬ IsAcyclic linesOnCubic :=
  not_isAcyclic_of_girth_pos (by rw [girth_linesOnCubic]; omega)

@[simp] theorem not_isTree_linesOnCubic : ¬ IsTree linesOnCubic :=
  not_isTree_of_girth_pos (by rw [girth_linesOnCubic]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `27 ≠ 2 · 10`. -/
@[simp] theorem not_isBipartite_linesOnCubic : ¬ IsBipartite linesOnCubic :=
  linesOnCubic_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

@[simp] theorem not_isSelfComplementary_linesOnCubic : ¬ IsSelfComplementary linesOnCubic :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_linesOnCubic]; omega)

/-- `ℓ = 1`: every edge lies in exactly one triangle and in no larger clique, so `ω = 3`.  The
triangles are the tritangent planes, each meeting the surface in three of the lines. -/
@[simp] theorem cliqueNum_linesOnCubic : linesOnCubic.cliqueNum = 3 :=
  linesOnCubic_srg.cliqueNum_eq_three (by omega) (by omega)

/-- The forty-five tritangent planes of the cubic surface: `ℓ = 1`, so each of the `135` edges
lies in one triangle, and each triangle has three edges. -/
@[simp] theorem cliqueCount_linesOnCubic : linesOnCubic.cliqueCount 3 = 45 := by
  have h := linesOnCubic_srg.six_mul_cliqueCount_three
  omega

/-- The complement is the Schläfli graph, whose `720` triangles are these `720` triples of
pairwise skew lines. -/
@[simp] theorem indepCount_linesOnCubic : linesOnCubic.indepCount 3 = 720 := by
  have h := linesOnCubic_srg.six_mul_indepCount_three
  omega

/-- Twenty-seven lines in cliques of three. -/
theorem nine_le_cliqueCoverNum_linesOnCubic : 9 ≤ linesOnCubic.cliqueCoverNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum linesOnCubic
  rw [V_linesOnCubic, cliqueNum_linesOnCubic] at h
  omega

theorem three_le_domNum_linesOnCubic : 3 ≤ linesOnCubic.domNum := by
  have h := le_domNum_of_regular (G := linesOnCubic) (k := 10) maxDeg_linesOnCubic
  rw [V_linesOnCubic] at h
  omega

/-- A maximum matching of the lines on a cubic surface: thirteen disjoint pairs of
meeting lines, leaving the sixth line out. -/
def linesOnCubicMatching : List (Fin 27 × Fin 27) :=
  [(0, 9), (1, 21), (2, 25), (3, 24), (4, 23), (5, 22), (7, 20), (8, 17), (10, 19), (11, 18),
   (12, 26), (13, 16), (14, 15)]

/-- **Thirteen disjoint pairs of meeting lines**, one short of perfect because twenty-seven is
odd. -/
@[simp] theorem matchNum_linesOnCubic : linesOnCubic.matchNum = 13 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V linesOnCubic
    rw [V_linesOnCubic] at h
    omega
  · rw [linesOnCubic_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.linesOnCubic.V))
      linesOnCubicMatching (by native_decide) (by decide)

/-! ## The Schläfli graph

The `(27, 16, 10, 8)` complement of the graph of lines: two of the twenty-seven lines are
adjacent here when they are *skew*. -/

@[simp] theorem V_schlafli : schlafli.V = 27 := schlafli_srg.V_eq

@[simp] theorem E_schlafli : schlafli.E = 216 := by
  have := schlafli_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_schlafli : schlafli.IsRegularWith 16 := schlafli_srg.isRegularWith

@[simp] theorem maxDeg_schlafli : maxDeg schlafli = 16 := schlafli_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_schlafli : minDeg schlafli = 16 := schlafli_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_schlafli : degSequence schlafli = List.replicate 27 16 :=
  schlafli_srg.degSequence

@[simp] theorem degMultiset_schlafli : degMultiset schlafli = Multiset.replicate 27 16 :=
  schlafli_srg.degMultiset

@[simp] theorem isConnected_schlafli : IsConnected schlafli :=
  schlafli_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_schlafli : schlafli.numComponents = 1 :=
  schlafli_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_schlafli : schlafli.diameter = 2 :=
  schlafli_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_schlafli : schlafli.radius = 2 :=
  schlafli_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_schlafli : schlafli.edgeConn = 16 :=
  schlafli_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 10`, so the two ends of an edge have a common neighbour. -/
@[simp] theorem girth_schlafli : schlafli.girth = 3 :=
  schlafli_srg.girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_schlafli : ¬ IsAcyclic schlafli :=
  not_isAcyclic_of_girth_pos (by rw [girth_schlafli]; omega)

@[simp] theorem not_isTree_schlafli : ¬ IsTree schlafli :=
  not_isTree_of_girth_pos (by rw [girth_schlafli]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `27 ≠ 2 · 16`. -/
@[simp] theorem not_isBipartite_schlafli : ¬ IsBipartite schlafli :=
  schlafli_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

@[simp] theorem not_isSelfComplementary_schlafli : ¬ IsSelfComplementary schlafli :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_schlafli]; omega)

/-- The Schläfli graph is the complement of the lines on a cubic surface, so its independent sets
are that graph's cliques: `α = 3`, the three lines of a tritangent plane. -/
@[simp] theorem indepNum_schlafli : schlafli.indepNum = 3 := by
  rw [show schlafli = linesOnCubicᶜ from rfl, indepNum_compl, cliqueNum_linesOnCubic]

@[simp] theorem coverNum_schlafli : schlafli.coverNum = 24 := by
  have h := coverNum_add_indepNum schlafli
  rw [indepNum_schlafli, V_schlafli] at h
  omega

/-- **The clique number of the Schläfli graph is six.**  `ℓ = 10` only gives `ω ≤ 12`; the truth is
that the graph is locally the Clebsch graph, whose independence number is five, so a vertex and a
maximum coclique of its neighbourhood give six and no more.  The witness below is six pairwise
skew lines — half of a double six. -/
@[simp] theorem cliqueNum_schlafli : schlafli.cliqueNum = 6 := by
  rw [schlafli_def, cliqueNum_mk]
  refine le_antisymm (by graph_sat native) ?_
  exact CGraph.le_cliqueNum_of_nodup (G := _root_.SRG.schlafli)
    (l := ([5, 11, 23, 24, 25, 26] : List (Fin 27)).map
      (FinEnum.equiv (α := _root_.SRG.schlafli.V)).symm)
    (by decide) (by native_decide)

/-- `27 · 16 · 10 / 6`, from the parameters alone. -/
@[simp] theorem cliqueCount_schlafli : schlafli.cliqueCount 3 = 720 := by
  have h := schlafli_srg.six_mul_cliqueCount_three
  omega

/-- Dually, the `45` tritangent planes of the cubic surface. -/
@[simp] theorem indepCount_schlafli : schlafli.indepCount 3 = 45 := by
  have h := schlafli_srg.six_mul_indepCount_three
  omega

theorem five_le_cliqueCoverNum_schlafli : 5 ≤ schlafli.cliqueCoverNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum schlafli
  rw [V_schlafli, cliqueNum_schlafli] at h
  omega

theorem two_le_domNum_schlafli : 2 ≤ schlafli.domNum := by
  have h := le_domNum_of_regular (G := schlafli) (k := 16) maxDeg_schlafli
  rw [V_schlafli] at h
  omega

/-- A maximum matching of the Schläfli graph: thirteen disjoint pairs of skew lines. -/
def schlafliMatching : List (Fin 27 × Fin 27) :=
  [(0, 21), (1, 25), (2, 26), (3, 23), (4, 24), (5, 20), (6, 19), (7, 22), (8, 18), (9, 16),
   (10, 17), (11, 14), (12, 15)]

/-- **The Schläfli graph has a near-perfect matching**, again thirteen for want of an even vertex
count. -/
@[simp] theorem matchNum_schlafli : schlafli.matchNum = 13 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V schlafli
    rw [V_schlafli] at h
    omega
  · rw [schlafli_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.schlafli.V))
      schlafliMatching (by native_decide) (by decide)

/-! ## The first Chang graph

The first of the three `(28, 12, 6, 4)` graphs that are not the triangular graph `T(8)`,
obtained from it by switching on a perfect matching of `K₈`. -/

@[simp] theorem V_chang₁ : chang₁.V = 28 := chang₁_srg.V_eq

@[simp] theorem E_chang₁ : chang₁.E = 168 := by
  have := chang₁_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_chang₁ : chang₁.IsRegularWith 12 := chang₁_srg.isRegularWith

@[simp] theorem maxDeg_chang₁ : maxDeg chang₁ = 12 := chang₁_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_chang₁ : minDeg chang₁ = 12 := chang₁_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_chang₁ : degSequence chang₁ = List.replicate 28 12 :=
  chang₁_srg.degSequence

@[simp] theorem degMultiset_chang₁ : degMultiset chang₁ = Multiset.replicate 28 12 :=
  chang₁_srg.degMultiset

@[simp] theorem isConnected_chang₁ : IsConnected chang₁ :=
  chang₁_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_chang₁ : chang₁.numComponents = 1 :=
  chang₁_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_chang₁ : chang₁.diameter = 2 :=
  chang₁_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_chang₁ : chang₁.radius = 2 :=
  chang₁_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_chang₁ : chang₁.edgeConn = 12 :=
  chang₁_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 6`, so the two ends of an edge have a common neighbour. -/
@[simp] theorem girth_chang₁ : chang₁.girth = 3 :=
  chang₁_srg.girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_chang₁ : ¬ IsAcyclic chang₁ :=
  not_isAcyclic_of_girth_pos (by rw [girth_chang₁]; omega)

@[simp] theorem not_isTree_chang₁ : ¬ IsTree chang₁ :=
  not_isTree_of_girth_pos (by rw [girth_chang₁]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `28 ≠ 2 · 12`. -/
@[simp] theorem not_isBipartite_chang₁ : ¬ IsBipartite chang₁ :=
  chang₁_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `189` edges, not `168`. -/
@[simp] theorem not_isSelfComplementary_chang₁ : ¬ IsSelfComplementary chang₁ := by
  intro h
  have h2 := h.two_mul_E
  rw [E_chang₁, V_chang₁] at h2
  have h3 : (28 : ℕ).choose 2 = 378 := rfl
  omega

/-- **The clique number of the first Chang graph is six.**  `ℓ = 6` allows eight.  The triangular
graph `T(8)` with the same parameters has `ω = 7`, the seven pairs through a fixed point; Seidel
switching on a perfect matching breaks one vertex out of each of those stars. -/
@[simp] theorem cliqueNum_chang₁ : chang₁.cliqueNum = 6 := by
  rw [chang₁_def, cliqueNum_mk]
  refine le_antisymm (by graph_sat native) ?_
  exact CGraph.le_cliqueNum_of_nodup (G := _root_.SRG.chang₁)
    (l := ([21, 22, 23, 24, 25, 26] : List (Fin 28)).map
      (FinEnum.equiv (α := _root_.SRG.chang₁.V)).symm)
    (by decide) (by native_decide)

/-- `28 · 12 · 6 / 6`; the three Chang graphs and `T(8)` share the count, as they share the
parameters. -/
@[simp] theorem cliqueCount_chang₁ : chang₁.cliqueCount 3 = 336 := by
  have h := chang₁_srg.six_mul_cliqueCount_three
  omega

/-- `28 · 15 · 6 / 6`; again shared with the other two Chang graphs and with `T(8)`. -/
@[simp] theorem indepCount_chang₁ : chang₁.indepCount 3 = 420 := by
  have h := chang₁_srg.six_mul_indepCount_three
  omega

theorem five_le_cliqueCoverNum_chang₁ : 5 ≤ chang₁.cliqueCoverNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum chang₁
  rw [V_chang₁, cliqueNum_chang₁] at h
  omega

theorem three_le_domNum_chang₁ : 3 ≤ chang₁.domNum := by
  have h := le_domNum_of_regular (G := chang₁) (k := 12) maxDeg_chang₁
  rw [V_chang₁] at h
  omega

/-- A perfect matching of the first Chang graph. -/
def chang₁Matching : List (Fin 28 × Fin 28) :=
  [(0, 26), (1, 27), (2, 23), (3, 24), (4, 22), (5, 25), (6, 21), (7, 19), (8, 17), (9, 18),
   (10, 20), (11, 16), (12, 13), (14, 15)]

/-- **The first Chang graph has a perfect matching**, so `ν = 14`. -/
@[simp] theorem matchNum_chang₁ : chang₁.matchNum = 14 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V chang₁
    rw [V_chang₁] at h
    omega
  · rw [chang₁_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.chang₁.V))
      chang₁Matching (by native_decide) (by decide)

/-! ## The second Chang graph

Switching `T(8)` on a disjoint union `C₃ ∪ C₅` instead. -/

@[simp] theorem V_chang₂ : chang₂.V = 28 := chang₂_srg.V_eq

@[simp] theorem E_chang₂ : chang₂.E = 168 := by
  have := chang₂_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_chang₂ : chang₂.IsRegularWith 12 := chang₂_srg.isRegularWith

@[simp] theorem maxDeg_chang₂ : maxDeg chang₂ = 12 := chang₂_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_chang₂ : minDeg chang₂ = 12 := chang₂_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_chang₂ : degSequence chang₂ = List.replicate 28 12 :=
  chang₂_srg.degSequence

@[simp] theorem degMultiset_chang₂ : degMultiset chang₂ = Multiset.replicate 28 12 :=
  chang₂_srg.degMultiset

@[simp] theorem isConnected_chang₂ : IsConnected chang₂ :=
  chang₂_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_chang₂ : chang₂.numComponents = 1 :=
  chang₂_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_chang₂ : chang₂.diameter = 2 :=
  chang₂_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_chang₂ : chang₂.radius = 2 :=
  chang₂_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_chang₂ : chang₂.edgeConn = 12 :=
  chang₂_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 6`, so the two ends of an edge have a common neighbour. -/
@[simp] theorem girth_chang₂ : chang₂.girth = 3 :=
  chang₂_srg.girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_chang₂ : ¬ IsAcyclic chang₂ :=
  not_isAcyclic_of_girth_pos (by rw [girth_chang₂]; omega)

@[simp] theorem not_isTree_chang₂ : ¬ IsTree chang₂ :=
  not_isTree_of_girth_pos (by rw [girth_chang₂]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `28 ≠ 2 · 12`. -/
@[simp] theorem not_isBipartite_chang₂ : ¬ IsBipartite chang₂ :=
  chang₂_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `189` edges, not `168`. -/
@[simp] theorem not_isSelfComplementary_chang₂ : ¬ IsSelfComplementary chang₂ := by
  intro h
  have h2 := h.two_mul_E
  rw [E_chang₂, V_chang₂] at h2
  have h3 : (28 : ℕ).choose 2 = 378 := rfl
  omega

/-- **The clique number of the second Chang graph is five**, one less than the other two: switching
on a triangle-plus-matching cuts deeper than switching on a perfect matching.  With `α = 4` in
`IsoGraph/Spectrum.lean` this is an isomorphism invariant separating `chang₂` from `chang₁`,
`chang₃` and `T(8)` in one line. -/
@[simp] theorem cliqueNum_chang₂ : chang₂.cliqueNum = 5 := by
  rw [chang₂_def, cliqueNum_mk]
  refine le_antisymm (by graph_sat native) ?_
  exact CGraph.le_cliqueNum_of_nodup (G := _root_.SRG.chang₂)
    (l := ([22, 23, 24, 25, 26] : List (Fin 28)).map
      (FinEnum.equiv (α := _root_.SRG.chang₂.V)).symm)
    (by decide) (by native_decide)

@[inherit_doc cliqueCount_chang₁, simp]
theorem cliqueCount_chang₂ : chang₂.cliqueCount 3 = 336 := by
  have h := chang₂_srg.six_mul_cliqueCount_three
  omega

@[inherit_doc indepCount_chang₁, simp]
theorem indepCount_chang₂ : chang₂.indepCount 3 = 420 := by
  have h := chang₂_srg.six_mul_indepCount_three
  omega

theorem six_le_cliqueCoverNum_chang₂ : 6 ≤ chang₂.cliqueCoverNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum chang₂
  rw [V_chang₂, cliqueNum_chang₂] at h
  omega

theorem three_le_domNum_chang₂ : 3 ≤ chang₂.domNum := by
  have h := le_domNum_of_regular (G := chang₂) (k := 12) maxDeg_chang₂
  rw [V_chang₂] at h
  omega

/-- A perfect matching of the second Chang graph. -/
def chang₂Matching : List (Fin 28 × Fin 28) :=
  [(0, 26), (1, 12), (2, 25), (3, 27), (4, 22), (5, 19), (6, 20), (7, 21), (8, 23), (9, 17),
   (10, 15), (11, 16), (13, 18), (14, 24)]

/-- **The second Chang graph has a perfect matching.** -/
@[simp] theorem matchNum_chang₂ : chang₂.matchNum = 14 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V chang₂
    rw [V_chang₂] at h
    omega
  · rw [chang₂_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.chang₂.V))
      chang₂Matching (by native_decide) (by decide)

/-! ## The third Chang graph

Switching `T(8)` on an eight-cycle. -/

@[simp] theorem V_chang₃ : chang₃.V = 28 := chang₃_srg.V_eq

@[simp] theorem E_chang₃ : chang₃.E = 168 := by
  have := chang₃_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_chang₃ : chang₃.IsRegularWith 12 := chang₃_srg.isRegularWith

@[simp] theorem maxDeg_chang₃ : maxDeg chang₃ = 12 := chang₃_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_chang₃ : minDeg chang₃ = 12 := chang₃_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_chang₃ : degSequence chang₃ = List.replicate 28 12 :=
  chang₃_srg.degSequence

@[simp] theorem degMultiset_chang₃ : degMultiset chang₃ = Multiset.replicate 28 12 :=
  chang₃_srg.degMultiset

@[simp] theorem isConnected_chang₃ : IsConnected chang₃ :=
  chang₃_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_chang₃ : chang₃.numComponents = 1 :=
  chang₃_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_chang₃ : chang₃.diameter = 2 :=
  chang₃_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_chang₃ : chang₃.radius = 2 :=
  chang₃_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_chang₃ : chang₃.edgeConn = 12 :=
  chang₃_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 6`, so the two ends of an edge have a common neighbour. -/
@[simp] theorem girth_chang₃ : chang₃.girth = 3 :=
  chang₃_srg.girth_eq_three (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_chang₃ : ¬ IsAcyclic chang₃ :=
  not_isAcyclic_of_girth_pos (by rw [girth_chang₃]; omega)

@[simp] theorem not_isTree_chang₃ : ¬ IsTree chang₃ :=
  not_isTree_of_girth_pos (by rw [girth_chang₃]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `28 ≠ 2 · 12`. -/
@[simp] theorem not_isBipartite_chang₃ : ¬ IsBipartite chang₃ :=
  chang₃_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `189` edges, not `168`. -/
@[simp] theorem not_isSelfComplementary_chang₃ : ¬ IsSelfComplementary chang₃ := by
  intro h
  have h2 := h.two_mul_E
  rw [E_chang₃, V_chang₃] at h2
  have h3 : (28 : ℕ).choose 2 = 378 := rfl
  omega

/-- **The clique number of the third Chang graph is six**, as for `chang₁`; the two are told apart
by `Values.changs_pairwise_not_iso`, not by this. -/
@[simp] theorem cliqueNum_chang₃ : chang₃.cliqueNum = 6 := by
  rw [chang₃_def, cliqueNum_mk]
  refine le_antisymm (by graph_sat native) ?_
  exact CGraph.le_cliqueNum_of_nodup (G := _root_.SRG.chang₃)
    (l := ([20, 21, 22, 23, 24, 25] : List (Fin 28)).map
      (FinEnum.equiv (α := _root_.SRG.chang₃.V)).symm)
    (by decide) (by native_decide)

@[inherit_doc cliqueCount_chang₁, simp]
theorem cliqueCount_chang₃ : chang₃.cliqueCount 3 = 336 := by
  have h := chang₃_srg.six_mul_cliqueCount_three
  omega

@[inherit_doc indepCount_chang₁, simp]
theorem indepCount_chang₃ : chang₃.indepCount 3 = 420 := by
  have h := chang₃_srg.six_mul_indepCount_three
  omega

theorem five_le_cliqueCoverNum_chang₃ : 5 ≤ chang₃.cliqueCoverNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum chang₃
  rw [V_chang₃, cliqueNum_chang₃] at h
  omega

theorem three_le_domNum_chang₃ : 3 ≤ chang₃.domNum := by
  have h := le_domNum_of_regular (G := chang₃) (k := 12) maxDeg_chang₃
  rw [V_chang₃] at h
  omega

/-- A perfect matching of the third Chang graph. -/
def chang₃Matching : List (Fin 28 × Fin 28) :=
  [(0, 25), (1, 27), (2, 24), (3, 26), (4, 22), (5, 21), (6, 23), (7, 20), (8, 19), (9, 17),
   (10, 15), (11, 16), (12, 14), (13, 18)]

/-- **The third Chang graph has a perfect matching.** -/
@[simp] theorem matchNum_chang₃ : chang₃.matchNum = 14 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V chang₃
    rw [V_chang₃] at h
    omega
  · rw [chang₃_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.chang₃.V))
      chang₃Matching (by native_decide) (by decide)

/-! ## The Hoffman–Singleton graph

The `(50, 7, 0, 1)` Moore graph of degree seven: triangle-free, and any two non-adjacent
vertices have exactly one common neighbour, which is as dense as girth five can be. -/

@[simp] theorem V_hoffmanSingleton : hoffmanSingleton.V = 50 := hoffmanSingleton_srg.V_eq

@[simp] theorem E_hoffmanSingleton : hoffmanSingleton.E = 175 := by
  have := hoffmanSingleton_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_hoffmanSingleton : hoffmanSingleton.IsRegularWith 7 :=
  hoffmanSingleton_srg.isRegularWith

@[simp] theorem maxDeg_hoffmanSingleton : maxDeg hoffmanSingleton = 7 :=
  hoffmanSingleton_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_hoffmanSingleton : minDeg hoffmanSingleton = 7 :=
  hoffmanSingleton_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_hoffmanSingleton : degSequence hoffmanSingleton = List.replicate 50 7 :=
  hoffmanSingleton_srg.degSequence

@[simp] theorem degMultiset_hoffmanSingleton :
    degMultiset hoffmanSingleton = Multiset.replicate 50 7 :=
  hoffmanSingleton_srg.degMultiset

@[simp] theorem isConnected_hoffmanSingleton : IsConnected hoffmanSingleton :=
  hoffmanSingleton_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_hoffmanSingleton : hoffmanSingleton.numComponents = 1 :=
  hoffmanSingleton_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_hoffmanSingleton : hoffmanSingleton.diameter = 2 :=
  hoffmanSingleton_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_hoffmanSingleton : hoffmanSingleton.radius = 2 :=
  hoffmanSingleton_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_hoffmanSingleton : hoffmanSingleton.edgeConn = 7 :=
  hoffmanSingleton_srg.edgeConn_eq (by omega) (by omega)

/-- **A Moore graph**: `ℓ = 0` and `μ = 1` force the girth up to five, and no further. -/
@[simp] theorem girth_hoffmanSingleton : hoffmanSingleton.girth = 5 :=
  hoffmanSingleton_srg.girth_eq_five (by omega) (by omega)

@[simp] theorem not_isAcyclic_hoffmanSingleton : ¬ IsAcyclic hoffmanSingleton :=
  not_isAcyclic_of_girth_pos (by rw [girth_hoffmanSingleton]; omega)

@[simp] theorem not_isTree_hoffmanSingleton : ¬ IsTree hoffmanSingleton :=
  not_isTree_of_girth_pos (by rw [girth_hoffmanSingleton]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `50 ≠ 2 · 7`. -/
@[simp] theorem not_isBipartite_hoffmanSingleton : ¬ IsBipartite hoffmanSingleton :=
  hoffmanSingleton_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

@[simp] theorem not_isSelfComplementary_hoffmanSingleton : ¬ IsSelfComplementary hoffmanSingleton :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_hoffmanSingleton]; omega)

/-- Triangle-free, so the largest clique is an edge. -/
@[simp] theorem cliqueNum_hoffmanSingleton : hoffmanSingleton.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_hoffmanSingleton]; omega))
    (two_le_cliqueNum_of_E_pos (by rw [E_hoffmanSingleton]; omega))

/-- And therefore no triangles at all. -/
@[simp] theorem cliqueCount_hoffmanSingleton : hoffmanSingleton.cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_hoffmanSingleton]; omega)

/-- The independent triples, on the other hand, are `50 · 42 · 35 / 6`. -/
@[simp] theorem indepCount_hoffmanSingleton : hoffmanSingleton.indepCount 3 = 12250 := by
  have h := hoffmanSingleton_srg.six_mul_indepCount_three
  omega

theorem seven_le_domNum_hoffmanSingleton : 7 ≤ hoffmanSingleton.domNum := by
  have h := le_domNum_of_regular (G := hoffmanSingleton) (k := 7) maxDeg_hoffmanSingleton
  rw [V_hoffmanSingleton] at h
  omega

/-- A perfect matching of the Hoffman–Singleton graph. -/
def hoffmanSingletonMatching : List (Fin 50 × Fin 50) :=
  [(0, 45), (1, 46), (2, 47), (3, 48), (4, 49), (5, 43), (6, 44), (7, 40), (8, 41), (9, 42),
   (10, 39), (11, 35), (12, 36), (13, 37), (14, 38), (15, 33), (16, 34), (17, 30), (18, 31),
   (19, 32), (20, 25), (21, 26), (22, 27), (23, 28), (24, 29)]

/-- **The Hoffman–Singleton graph has a perfect matching**, so `ν = 25`. -/
@[simp] theorem matchNum_hoffmanSingleton : hoffmanSingleton.matchNum = 25 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V hoffmanSingleton
    rw [V_hoffmanSingleton] at h
    omega
  · rw [hoffmanSingleton_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.hoffmanSingleton.V))
      hoffmanSingletonMatching (by native_decide) (by native_decide)

/-- **The Hoffman–Singleton graph has clique cover number twenty-five.**  Triangle-free, so a
clique is a vertex or an edge, and the perfect matching gives a cover by edges alone. -/
@[simp] theorem cliqueCoverNum_hoffmanSingleton : hoffmanSingleton.cliqueCoverNum = 25 := by
  have hm : hoffmanSingleton.V ≤ 2 * hoffmanSingleton.matchNum + 1 := by
    rw [V_hoffmanSingleton, matchNum_hoffmanSingleton]; omega
  have h := cliqueCoverNum_of_cliqueNum_le_two cliqueNum_hoffmanSingleton.le hm
  rw [V_hoffmanSingleton] at h
  omega

/-! ## The Gewirtz graph

The `(56, 10, 0, 2)` graph on the fifty-six blocks of `S(3, 6, 22)` missing a fixed point,
two blocks adjacent when they are disjoint. -/

@[simp] theorem V_gewirtz : gewirtz.V = 56 := gewirtz_srg.V_eq

@[simp] theorem E_gewirtz : gewirtz.E = 280 := by
  have := gewirtz_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_gewirtz : gewirtz.IsRegularWith 10 := gewirtz_srg.isRegularWith

@[simp] theorem maxDeg_gewirtz : maxDeg gewirtz = 10 := gewirtz_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_gewirtz : minDeg gewirtz = 10 := gewirtz_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_gewirtz : degSequence gewirtz = List.replicate 56 10 :=
  gewirtz_srg.degSequence

@[simp] theorem degMultiset_gewirtz : degMultiset gewirtz = Multiset.replicate 56 10 :=
  gewirtz_srg.degMultiset

@[simp] theorem isConnected_gewirtz : IsConnected gewirtz :=
  gewirtz_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_gewirtz : gewirtz.numComponents = 1 :=
  gewirtz_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_gewirtz : gewirtz.diameter = 2 :=
  gewirtz_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_gewirtz : gewirtz.radius = 2 :=
  gewirtz_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_gewirtz : gewirtz.edgeConn = 10 :=
  gewirtz_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 0` rules out a triangle and `μ = 2 ≥ 2` supplies the fourth corner of a
square. -/
@[simp] theorem girth_gewirtz : gewirtz.girth = 4 :=
  gewirtz_srg.girth_eq_four (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_gewirtz : ¬ IsAcyclic gewirtz :=
  not_isAcyclic_of_girth_pos (by rw [girth_gewirtz]; omega)

@[simp] theorem not_isTree_gewirtz : ¬ IsTree gewirtz :=
  not_isTree_of_girth_pos (by rw [girth_gewirtz]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `56 ≠ 2 · 10`. -/
@[simp] theorem not_isBipartite_gewirtz : ¬ IsBipartite gewirtz :=
  gewirtz_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `770` edges, not `280`. -/
@[simp] theorem not_isSelfComplementary_gewirtz : ¬ IsSelfComplementary gewirtz := by
  intro h
  have h2 := h.two_mul_E
  rw [E_gewirtz, V_gewirtz] at h2
  have h3 : (56 : ℕ).choose 2 = 1540 := rfl
  omega

/-- Triangle-free, so the largest clique is an edge. -/
@[simp] theorem cliqueNum_gewirtz : gewirtz.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_gewirtz]; omega))
    (two_le_cliqueNum_of_E_pos (by rw [E_gewirtz]; omega))

/-- And therefore no triangles at all. -/
@[simp] theorem cliqueCount_gewirtz : gewirtz.cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_gewirtz]; omega)

/-- The independent triples, on the other hand, are `56 · 45 · 36 / 6`. -/
@[simp] theorem indepCount_gewirtz : gewirtz.indepCount 3 = 15120 := by
  have h := gewirtz_srg.six_mul_indepCount_three
  omega

theorem six_le_domNum_gewirtz : 6 ≤ gewirtz.domNum := by
  have h := le_domNum_of_regular (G := gewirtz) (k := 10) maxDeg_gewirtz
  rw [V_gewirtz] at h
  omega

/-- A perfect matching of the Gewirtz graph. -/
def gewirtzMatching : List (Fin 56 × Fin 56) :=
  [(0, 29), (1, 45), (2, 49), (3, 53), (4, 50), (5, 55), (6, 48), (7, 46), (8, 19), (9, 52),
   (10, 44), (11, 33), (12, 31), (13, 43), (14, 41), (15, 22), (16, 39), (17, 40), (18, 37),
   (20, 35), (21, 34), (23, 32), (24, 30), (25, 42), (26, 28), (27, 51), (36, 54), (38, 47)]

/-- **The Gewirtz graph has a perfect matching**, so `ν = 28`. -/
@[simp] theorem matchNum_gewirtz : gewirtz.matchNum = 28 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V gewirtz
    rw [V_gewirtz] at h
    omega
  · rw [gewirtz_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.gewirtz.V))
      gewirtzMatching (by native_decide) (by native_decide)

/-- **The Gewirtz graph has clique cover number twenty-eight**, by its perfect matching. -/
@[simp] theorem cliqueCoverNum_gewirtz : gewirtz.cliqueCoverNum = 28 := by
  have hm : gewirtz.V ≤ 2 * gewirtz.matchNum + 1 := by
    rw [V_gewirtz, matchNum_gewirtz]; omega
  have h := cliqueCoverNum_of_cliqueNum_le_two cliqueNum_gewirtz.le hm
  rw [V_gewirtz] at h
  omega

/-! ## The `M₂₂` graph

The `(77, 16, 0, 4)` graph on the seventy-seven blocks of `S(3, 6, 22)` containing a fixed
point, again with disjointness for adjacency. -/

@[simp] theorem V_m22 : m22.V = 77 := m22_srg.V_eq

@[simp] theorem E_m22 : m22.E = 616 := by
  have := m22_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_m22 : m22.IsRegularWith 16 := m22_srg.isRegularWith

@[simp] theorem maxDeg_m22 : maxDeg m22 = 16 := m22_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_m22 : minDeg m22 = 16 := m22_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_m22 : degSequence m22 = List.replicate 77 16 := m22_srg.degSequence

@[simp] theorem degMultiset_m22 : degMultiset m22 = Multiset.replicate 77 16 := m22_srg.degMultiset

@[simp] theorem isConnected_m22 : IsConnected m22 :=
  m22_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_m22 : m22.numComponents = 1 :=
  m22_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_m22 : m22.diameter = 2 :=
  m22_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_m22 : m22.radius = 2 :=
  m22_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_m22 : m22.edgeConn = 16 :=
  m22_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 0` rules out a triangle and `μ = 4 ≥ 2` supplies the fourth corner of a
square. -/
@[simp] theorem girth_m22 : m22.girth = 4 :=
  m22_srg.girth_eq_four (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_m22 : ¬ IsAcyclic m22 :=
  not_isAcyclic_of_girth_pos (by rw [girth_m22]; omega)

@[simp] theorem not_isTree_m22 : ¬ IsTree m22 :=
  not_isTree_of_girth_pos (by rw [girth_m22]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `77 ≠ 2 · 16`. -/
@[simp] theorem not_isBipartite_m22 : ¬ IsBipartite m22 :=
  m22_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `1463` edges, not `616`. -/
@[simp] theorem not_isSelfComplementary_m22 : ¬ IsSelfComplementary m22 := by
  intro h
  have h2 := h.two_mul_E
  rw [E_m22, V_m22] at h2
  have h3 : (77 : ℕ).choose 2 = 2926 := rfl
  omega

/-- Triangle-free, so the largest clique is an edge. -/
@[simp] theorem cliqueNum_m22 : m22.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_m22]; omega))
    (two_le_cliqueNum_of_E_pos (by rw [E_m22]; omega))

/-- And therefore no triangles at all. -/
@[simp] theorem cliqueCount_m22 : m22.cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_m22]; omega)

/-- The independent triples, on the other hand, are `77 · 60 · 47 / 6`. -/
@[simp] theorem indepCount_m22 : m22.indepCount 3 = 36190 := by
  have h := m22_srg.six_mul_indepCount_three
  omega

theorem five_le_domNum_m22 : 5 ≤ m22.domNum := by
  have h := le_domNum_of_regular (G := m22) (k := 16) maxDeg_m22
  rw [V_m22] at h
  omega

/-- A maximum matching of the `M₂₂` graph: thirty-eight disjoint edges, one vertex left over. -/
def m22Matching : List (Fin 77 × Fin 77) :=
  [(0, 34), (1, 75), (2, 74), (3, 73), (4, 72), (5, 71), (6, 76), (7, 69), (8, 33), (9, 67),
   (10, 66), (11, 65), (12, 64), (13, 63), (14, 70), (15, 61), (16, 60), (17, 59), (18, 58),
   (19, 57), (20, 54), (21, 55), (22, 50), (23, 51), (24, 53), (25, 52), (26, 47), (27, 46),
   (28, 49), (29, 43), (30, 45), (31, 44), (35, 48), (36, 68), (37, 41), (38, 42), (39, 62),
   (40, 56)]

/-- **A near-perfect matching of the `M₂₂` graph**; seventy-seven is odd, so one vertex is
necessarily missed. -/
@[simp] theorem matchNum_m22 : m22.matchNum = 38 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V m22
    rw [V_m22] at h
    omega
  · rw [m22_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.m22.V))
      m22Matching (by native_decide) (by native_decide)

/-- **The `M₂₂` graph has clique cover number thirty-nine**: thirty-eight edges of the matching
and the one vertex they miss. -/
@[simp] theorem cliqueCoverNum_m22 : m22.cliqueCoverNum = 39 := by
  have hm : m22.V ≤ 2 * m22.matchNum + 1 := by
    rw [V_m22, matchNum_m22]
  have h := cliqueCoverNum_of_cliqueNum_le_two cliqueNum_m22.le hm
  rw [V_m22] at h
  omega

/-! ## The Higman–Sims graph

The `(100, 22, 0, 6)` graph whose automorphism group contains the sporadic simple
Higman–Sims group with index two. -/

@[simp] theorem V_higmanSims : higmanSims.V = 100 := higmanSims_srg.V_eq

@[simp] theorem E_higmanSims : higmanSims.E = 1100 := by
  have := higmanSims_srg.two_mul_E
  omega

@[simp] theorem isRegularWith_higmanSims : higmanSims.IsRegularWith 22 :=
  higmanSims_srg.isRegularWith

@[simp] theorem maxDeg_higmanSims : maxDeg higmanSims = 22 := higmanSims_srg.maxDeg_eq (by omega)

@[simp] theorem minDeg_higmanSims : minDeg higmanSims = 22 := higmanSims_srg.minDeg_eq (by omega)

@[simp] theorem degSequence_higmanSims : degSequence higmanSims = List.replicate 100 22 :=
  higmanSims_srg.degSequence

@[simp] theorem degMultiset_higmanSims : degMultiset higmanSims = Multiset.replicate 100 22 :=
  higmanSims_srg.degMultiset

@[simp] theorem isConnected_higmanSims : IsConnected higmanSims :=
  higmanSims_srg.isConnected (by omega) (by omega)

@[simp] theorem numComponents_higmanSims : higmanSims.numComponents = 1 :=
  higmanSims_srg.numComponents_eq_one (by omega) (by omega)

@[simp] theorem diameter_higmanSims : higmanSims.diameter = 2 :=
  higmanSims_srg.diameter_eq_two (by omega) (by omega)

@[simp] theorem radius_higmanSims : higmanSims.radius = 2 :=
  higmanSims_srg.radius_eq_two (by omega) (by omega)

@[simp] theorem edgeConn_higmanSims : higmanSims.edgeConn = 22 :=
  higmanSims_srg.edgeConn_eq (by omega) (by omega)

/-- `ℓ = 0` rules out a triangle and `μ = 6 ≥ 2` supplies the fourth corner of a
square. -/
@[simp] theorem girth_higmanSims : higmanSims.girth = 4 :=
  higmanSims_srg.girth_eq_four (by omega) (by omega) (by omega)

@[simp] theorem not_isAcyclic_higmanSims : ¬ IsAcyclic higmanSims :=
  not_isAcyclic_of_girth_pos (by rw [girth_higmanSims]; omega)

@[simp] theorem not_isTree_higmanSims : ¬ IsTree higmanSims :=
  not_isTree_of_girth_pos (by rw [girth_higmanSims]; omega)

/-- Not bipartite: a bipartite strongly regular graph with `μ > 0` is complete bipartite,
and `100 ≠ 2 · 22`. -/
@[simp] theorem not_isBipartite_higmanSims : ¬ IsBipartite higmanSims :=
  higmanSims_srg.not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Not self-complementary: that would need `2475` edges, not `1100`. -/
@[simp] theorem not_isSelfComplementary_higmanSims : ¬ IsSelfComplementary higmanSims := by
  intro h
  have h2 := h.two_mul_E
  rw [E_higmanSims, V_higmanSims] at h2
  have h3 : (100 : ℕ).choose 2 = 4950 := rfl
  omega

/-- Triangle-free, so the largest clique is an edge. -/
@[simp] theorem cliqueNum_higmanSims : higmanSims.cliqueNum = 2 :=
  le_antisymm (cliqueNum_le_two_of_girth_ne_three (by rw [girth_higmanSims]; omega))
    (two_le_cliqueNum_of_E_pos (by rw [E_higmanSims]; omega))

/-- And therefore no triangles at all. -/
@[simp] theorem cliqueCount_higmanSims : higmanSims.cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_higmanSims]; omega)

/-- The independent triples, on the other hand, are `100 · 77 · 60 / 6`. -/
@[simp] theorem indepCount_higmanSims : higmanSims.indepCount 3 = 77000 := by
  have h := higmanSims_srg.six_mul_indepCount_three
  omega

theorem five_le_domNum_higmanSims : 5 ≤ higmanSims.domNum := by
  have h := le_domNum_of_regular (G := higmanSims) (k := 22) maxDeg_higmanSims
  rw [V_higmanSims] at h
  omega

/-- A perfect matching of the Higman–Sims graph. -/
def higmanSimsMatching : List (Fin 100 × Fin 100) :=
  [(0, 99), (1, 43), (2, 50), (3, 94), (4, 98), (5, 95), (6, 96), (7, 97), (8, 79), (9, 48),
   (10, 87), (11, 91), (12, 92), (13, 89), (14, 84), (15, 85), (16, 88), (17, 83), (18, 82),
   (19, 76), (20, 77), (21, 81), (22, 72), (23, 73), (24, 74), (25, 75), (26, 71), (27, 66),
   (28, 70), (29, 68), (30, 57), (31, 67), (32, 63), (33, 69), (34, 53), (35, 65), (36, 51),
   (37, 64), (38, 61), (39, 60), (40, 80), (41, 59), (42, 56), (44, 55), (45, 54), (46, 52),
   (47, 93), (49, 90), (58, 86), (62, 78)]

/-- **The Higman–Sims graph has a perfect matching**, so `ν = 50`. -/
@[simp] theorem matchNum_higmanSims : higmanSims.matchNum = 50 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V higmanSims
    rw [V_higmanSims] at h
    omega
  · rw [higmanSims_def, matchNum_mk]
    exact CGraph.length_le_matchNum (FinEnum.equiv (α := _root_.SRG.higmanSims.V))
      higmanSimsMatching (by native_decide) (by native_decide)

/-- **The Higman–Sims graph has clique cover number fifty**, by its perfect matching.  This is the
only one of its five hardest invariants that the matching settles outright. -/
@[simp] theorem cliqueCoverNum_higmanSims : higmanSims.cliqueCoverNum = 50 := by
  have hm : higmanSims.V ≤ 2 * higmanSims.matchNum + 1 := by
    rw [V_higmanSims, matchNum_higmanSims]; omega
  have h := cliqueCoverNum_of_cliqueNum_le_two cliqueNum_higmanSims.le hm
  rw [V_higmanSims] at h
  omega

/-! ## Transitivity

Whether the automorphism group is transitive on the vertices or on the arcs is decided rather
than witnessed: `Canon/Chain.lean` computes a generating set and proves it complete, so an orbit
that stops short is itself the proof that nothing reaches the rest.  Seven of the ten graphs are
arc-transitive, and vertex-transitivity follows for free, since none of them has an isolated
vertex.  The three Chang graphs are the exception, and there the implication runs the other way:
their automorphism groups have orders 384, 360 and 96, none of them divisible by 28, so no orbit
of vertices is the whole graph and no orbit of arcs is all of them.
-/

@[simp] theorem isArcTransitive_shrikhande : IsArcTransitive shrikhande := by
  rw [shrikhande_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_shrikhande : IsVertexTransitive shrikhande :=
  isArcTransitive_shrikhande.isVertexTransitive (by rw [minDeg_shrikhande]; omega)

@[simp] theorem isArcTransitive_linesOnCubic : IsArcTransitive linesOnCubic := by
  rw [linesOnCubic_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_linesOnCubic : IsVertexTransitive linesOnCubic :=
  isArcTransitive_linesOnCubic.isVertexTransitive (by rw [minDeg_linesOnCubic]; omega)

@[simp] theorem isArcTransitive_schlafli : IsArcTransitive schlafli := by
  rw [schlafli_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_schlafli : IsVertexTransitive schlafli :=
  isArcTransitive_schlafli.isVertexTransitive (by rw [minDeg_schlafli]; omega)

@[simp] theorem not_isVertexTransitive_chang₁ : ¬ IsVertexTransitive chang₁ := by
  rw [chang₁_def, isVertexTransitive_mk, ← CGraph.vertexTransitiveB_iff]
  native_decide

@[simp] theorem not_isArcTransitive_chang₁ : ¬ IsArcTransitive chang₁ := fun h =>
  not_isVertexTransitive_chang₁ (h.isVertexTransitive (by rw [minDeg_chang₁]; omega))

@[simp] theorem not_isVertexTransitive_chang₂ : ¬ IsVertexTransitive chang₂ := by
  rw [chang₂_def, isVertexTransitive_mk, ← CGraph.vertexTransitiveB_iff]
  native_decide

@[simp] theorem not_isArcTransitive_chang₂ : ¬ IsArcTransitive chang₂ := fun h =>
  not_isVertexTransitive_chang₂ (h.isVertexTransitive (by rw [minDeg_chang₂]; omega))

@[simp] theorem not_isVertexTransitive_chang₃ : ¬ IsVertexTransitive chang₃ := by
  rw [chang₃_def, isVertexTransitive_mk, ← CGraph.vertexTransitiveB_iff]
  native_decide

@[simp] theorem not_isArcTransitive_chang₃ : ¬ IsArcTransitive chang₃ := fun h =>
  not_isVertexTransitive_chang₃ (h.isVertexTransitive (by rw [minDeg_chang₃]; omega))

@[simp] theorem isArcTransitive_hoffmanSingleton : IsArcTransitive hoffmanSingleton := by
  rw [hoffmanSingleton_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_hoffmanSingleton : IsVertexTransitive hoffmanSingleton :=
  isArcTransitive_hoffmanSingleton.isVertexTransitive (by rw [minDeg_hoffmanSingleton]; omega)

@[simp] theorem isArcTransitive_gewirtz : IsArcTransitive gewirtz := by
  rw [gewirtz_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_gewirtz : IsVertexTransitive gewirtz :=
  isArcTransitive_gewirtz.isVertexTransitive (by rw [minDeg_gewirtz]; omega)

@[simp] theorem isArcTransitive_m22 : IsArcTransitive m22 := by
  rw [m22_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_m22 : IsVertexTransitive m22 :=
  isArcTransitive_m22.isVertexTransitive (by rw [minDeg_m22]; omega)

@[simp] theorem isArcTransitive_higmanSims : IsArcTransitive higmanSims := by
  rw [higmanSims_def, isArcTransitive_mk, ← CGraph.arcTransitiveB_iff]
  native_decide

@[simp] theorem isVertexTransitive_higmanSims : IsVertexTransitive higmanSims :=
  isArcTransitive_higmanSims.isVertexTransitive (by rw [minDeg_higmanSims]; omega)

/-! ## Chromatic indices

All ten graphs are regular, so `Δ` is the degree and `Δ ≤ χ'` for free; Vizing leaves two
possibilities, and here the split is seven to three.

Seven are class one, and a `Δ`-edge-colouring of a `Δ`-regular graph is exactly a
`1`-factorization: every colour class is a perfect matching.  That is how the tables below are
written — row `v` names the partner of `v` in each factor in turn — and it is why they need no
symmetry argument, the colour of `u v` being the position of `v` in `u`'s row and equally the
position of `u` in `v`'s.

The other three — the lines on a cubic surface, the Schläfli graph and `M₂₂` — have an odd number
of vertices, so no colour class is a perfect matching and each carries at most `(n - 1) / 2`
edges.  Then `Δ (n - 1) / 2 < n Δ / 2 = |E|`, so `Δ` colours run out; that is
`maxDeg_lt_edgeChromNum_of_isRegularWith_odd`, and since `Δ + 1` colours do suffice all three are
class two.  Their tables are near-`1`-factorizations into `Δ + 1` matchings, each missing a single
vertex, and a vertex records the factor that misses it by naming itself. -/

/-- A `1`-factorization of the Shrikhande graph into 6 perfect matchings: row `v` names the
partner of `v` in each. -/
def shrikhandeEdgeColTable : List (List ℕ) :=
  [[1, 3, 4, 5, 12, 15], [0, 2, 5, 6, 13, 12], [3, 1, 6, 7, 14, 13], [2, 0, 7, 4, 15, 14], [5, 7, 0,
  3, 8, 9], [4, 6, 1, 0, 9, 10], [7, 5, 2, 1, 10, 11], [6, 4, 3, 2, 11, 8], [9, 11, 12, 13, 4, 7],
  [8, 10, 13, 14, 5, 4], [11, 9, 14, 15, 6, 5], [10, 8, 15, 12, 7, 6], [13, 15, 8, 11, 0, 1], [12,
  14, 9, 8, 1, 2], [15, 13, 10, 9, 2, 3], [14, 12, 11, 10, 3, 0]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def shrikhandeEdgeCol (x y : _root_.SRG.shrikhande.V) : Fin 6 :=
  ⟨min ((shrikhandeEdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    5, by omega⟩

theorem shrikhandeEdgeCol_symm : ∀ x y : _root_.SRG.shrikhande.V,
    shrikhandeEdgeCol x y = shrikhandeEdgeCol y x := by native_decide

theorem shrikhandeEdgeCol_proper : ∀ u v w : _root_.SRG.shrikhande.V,
    _root_.SRG.shrikhande.Adj u v = true →
      _root_.SRG.shrikhande.Adj u w = true → v ≠ w →
        shrikhandeEdgeCol u v ≠ shrikhandeEdgeCol u w := by native_decide

/-- **The Shrikhande graph is class one**: `χ' = Δ = 6`. -/
@[simp] theorem edgeChromNum_shrikhande : shrikhande.edgeChromNum = 6 := by
  refine le_antisymm ?_ ?_
  · rw [shrikhande_def]
    exact edgeChromNum_mk_le_of_colouring shrikhandeEdgeCol shrikhandeEdgeCol_symm
      shrikhandeEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum shrikhande
    rwa [maxDeg_shrikhande] at h

/-- A near-`1`-factorization of the graph of lines on a cubic surface into 11 matchings: row `v`
names the partner of `v` in each matching, or `v` itself in the one matching that misses it. -/
def linesOnCubicEdgeColTable : List (List ℕ) :=
  [[7, 8, 9, 10, 11, 22, 23, 24, 25, 26, 0], [21, 18, 20, 26, 19, 10, 1, 11, 9, 8, 6], [25, 21, 16,
  11, 17, 6, 9, 7, 15, 2, 10], [14, 11, 17, 24, 10, 3, 6, 8, 20, 13, 7], [16, 19, 6, 4, 14, 23, 8,
  9, 12, 7, 11], [13, 15, 22, 5, 12, 9, 7, 10, 8, 6, 18], [26, 24, 4, 22, 25, 2, 3, 6, 23, 5, 1],
  [0, 20, 19, 21, 26, 18, 5, 2, 7, 4, 3], [17, 0, 25, 16, 15, 21, 4, 3, 5, 1, 8], [20, 13, 0, 17,
  24, 5, 2, 4, 1, 14, 9], [10, 23, 12, 0, 3, 1, 19, 5, 14, 16, 2], [22, 3, 11, 2, 0, 12, 18, 1, 13,
  15, 4], [24, 26, 10, 25, 5, 11, 21, 20, 4, 17, 12], [5, 9, 13, 23, 21, 26, 25, 19, 11, 3, 16], [3,
  22, 14, 18, 4, 25, 26, 21, 10, 9, 15], [23, 5, 15, 19, 8, 24, 20, 26, 2, 11, 14], [4, 16, 2, 8,
  18, 20, 24, 22, 26, 10, 13], [8, 17, 3, 9, 2, 19, 22, 23, 18, 12, 26], [18, 1, 23, 14, 16, 7, 11,
  25, 17, 24, 5], [19, 4, 7, 15, 1, 17, 10, 13, 24, 25, 22], [9, 7, 1, 20, 23, 16, 15, 12, 3, 22,
  25], [1, 2, 21, 7, 13, 8, 12, 14, 22, 23, 24], [11, 14, 5, 6, 22, 0, 17, 16, 21, 20, 19], [15, 10,
  18, 13, 20, 4, 0, 17, 6, 21, 23], [12, 6, 24, 3, 9, 15, 16, 0, 19, 18, 21], [2, 25, 8, 12, 6, 14,
  13, 18, 0, 19, 20], [6, 12, 26, 1, 7, 13, 14, 15, 16, 0, 17]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def linesOnCubicEdgeCol (x y : _root_.SRG.linesOnCubic.V) : Fin 11 :=
  ⟨min ((linesOnCubicEdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    10, by omega⟩

theorem linesOnCubicEdgeCol_symm : ∀ x y : _root_.SRG.linesOnCubic.V,
    linesOnCubicEdgeCol x y = linesOnCubicEdgeCol y x := by native_decide

theorem linesOnCubicEdgeCol_proper : ∀ u v w : _root_.SRG.linesOnCubic.V,
    _root_.SRG.linesOnCubic.Adj u v = true →
      _root_.SRG.linesOnCubic.Adj u w = true → v ≠ w →
        linesOnCubicEdgeCol u v ≠ linesOnCubicEdgeCol u w := by native_decide

/-- **The graph of lines on a cubic surface is class two**: `χ' = Δ + 1 = 11`. -/
@[simp] theorem edgeChromNum_linesOnCubic : linesOnCubic.edgeChromNum = 11 := by
  refine le_antisymm ?_ ?_
  · rw [linesOnCubic_def]
    exact edgeChromNum_mk_le_of_colouring linesOnCubicEdgeCol linesOnCubicEdgeCol_symm
      linesOnCubicEdgeCol_proper
  · have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd isRegularWith_linesOnCubic
      (by omega) (by rw [V_linesOnCubic])
    rw [maxDeg_linesOnCubic] at h
    omega

/-- A near-`1`-factorization of the Schläfli graph into 17 matchings: row `v` names the partner of
`v` in each matching, or `v` itself in the one matching that misses it. -/
def schlafliEdgeColTable : List (List ℕ) :=
  [[1, 2, 3, 4, 5, 6, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0], [0, 13, 16, 17, 25, 15, 14, 22,
  24, 3, 12, 7, 4, 5, 2, 1, 23], [19, 0, 23, 24, 14, 13, 2, 26, 12, 22, 8, 5, 3, 20, 1, 4, 18], [15,
  21, 0, 26, 16, 25, 19, 18, 3, 1, 23, 9, 2, 22, 4, 5, 12], [20, 25, 15, 0, 13, 17, 21, 24, 5, 18,
  22, 4, 1, 26, 3, 2, 10], [25, 20, 14, 16, 0, 23, 17, 19, 4, 26, 24, 2, 5, 1, 21, 3, 11], [11, 19,
  21, 13, 12, 0, 15, 20, 16, 6, 14, 8, 9, 18, 7, 10, 17], [13, 12, 25, 23, 7, 14, 16, 17, 22, 10, 9,
  1, 11, 24, 6, 8, 15], [9, 18, 19, 14, 26, 22, 24, 23, 13, 20, 2, 6, 10, 12, 11, 7, 8], [8, 15, 12,
  21, 19, 18, 26, 25, 23, 16, 7, 3, 6, 9, 10, 11, 22], [26, 17, 22, 18, 20, 24, 25, 10, 21, 7, 13,
  11, 8, 15, 9, 6, 4], [6, 16, 17, 19, 24, 20, 23, 21, 26, 25, 11, 10, 7, 14, 8, 9, 5], [18, 7, 9,
  22, 6, 12, 0, 15, 2, 23, 1, 19, 13, 8, 16, 14, 3], [7, 1, 13, 6, 4, 2, 20, 0, 8, 24, 10, 15, 12,
  17, 22, 18, 14], [24, 14, 5, 8, 2, 7, 1, 16, 0, 19, 6, 23, 20, 11, 17, 12, 13], [3, 9, 4, 15, 17,
  1, 6, 12, 25, 0, 21, 13, 16, 10, 18, 22, 7], [21, 11, 1, 5, 3, 16, 7, 14, 6, 9, 0, 25, 15, 23, 12,
  17, 19], [17, 10, 11, 1, 15, 4, 5, 7, 20, 21, 25, 0, 24, 13, 14, 16, 6], [12, 8, 26, 10, 18, 9,
  22, 3, 19, 4, 20, 21, 0, 6, 15, 13, 2], [2, 6, 8, 11, 9, 21, 3, 5, 18, 14, 26, 12, 23, 0, 19, 20,
  16], [4, 5, 24, 20, 10, 11, 13, 6, 17, 8, 18, 26, 14, 2, 0, 19, 21], [16, 3, 6, 9, 21, 19, 4, 11,
  10, 17, 15, 18, 26, 25, 5, 0, 20], [23, 26, 10, 12, 22, 8, 18, 1, 7, 2, 4, 24, 25, 3, 13, 15, 9],
  [22, 24, 2, 7, 23, 5, 11, 8, 9, 12, 3, 14, 19, 16, 26, 25, 1], [14, 23, 20, 2, 11, 10, 8, 4, 1,
  13, 5, 22, 17, 7, 25, 26, 24], [5, 4, 7, 25, 1, 3, 10, 9, 15, 11, 17, 16, 22, 21, 24, 23, 26],
  [10, 22, 18, 3, 8, 26, 9, 2, 11, 5, 19, 20, 21, 4, 23, 24, 25]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def schlafliEdgeCol (x y : _root_.SRG.schlafli.V) : Fin 17 :=
  ⟨min ((schlafliEdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    16, by omega⟩

theorem schlafliEdgeCol_symm : ∀ x y : _root_.SRG.schlafli.V,
    schlafliEdgeCol x y = schlafliEdgeCol y x := by native_decide

theorem schlafliEdgeCol_proper : ∀ u v w : _root_.SRG.schlafli.V,
    _root_.SRG.schlafli.Adj u v = true →
      _root_.SRG.schlafli.Adj u w = true → v ≠ w →
        schlafliEdgeCol u v ≠ schlafliEdgeCol u w := by native_decide

/-- **The Schläfli graph is class two**: `χ' = Δ + 1 = 17`. -/
@[simp] theorem edgeChromNum_schlafli : schlafli.edgeChromNum = 17 := by
  refine le_antisymm ?_ ?_
  · rw [schlafli_def]
    exact edgeChromNum_mk_le_of_colouring schlafliEdgeCol schlafliEdgeCol_symm
      schlafliEdgeCol_proper
  · have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd isRegularWith_schlafli
      (by omega) (by rw [V_schlafli])
    rw [maxDeg_schlafli] at h
    omega

/-- A `1`-factorization of the first Chang graph into 12 perfect matchings: row `v` names the
partner of `v` in each. -/
def chang₁EdgeColTable : List (List ℕ) :=
  [[8, 9, 12, 13, 17, 18, 19, 20, 23, 24, 25, 26], [17, 15, 23, 6, 8, 10, 2, 27, 12, 21, 3, 14],
  [23, 17, 16, 27, 22, 12, 1, 11, 7, 14, 8, 4], [14, 18, 15, 24, 4, 13, 21, 9, 6, 27, 1, 10], [27,
  24, 18, 11, 3, 16, 13, 7, 14, 22, 9, 2], [20, 19, 25, 7, 21, 11, 26, 22, 15, 6, 10, 16], [15, 10,
  19, 1, 27, 21, 9, 25, 3, 5, 7, 8], [19, 25, 22, 5, 16, 27, 11, 4, 2, 8, 6, 9], [0, 23, 17, 19, 1,
  9, 27, 12, 25, 7, 2, 6], [24, 0, 27, 18, 19, 8, 6, 3, 13, 25, 4, 7], [21, 6, 26, 20, 11, 1, 12,
  13, 27, 15, 5, 3], [16, 27, 20, 4, 10, 5, 7, 2, 22, 26, 13, 12], [26, 20, 0, 17, 23, 2, 10, 8, 1,
  13, 27, 11], [18, 26, 24, 0, 20, 3, 4, 10, 9, 12, 11, 27], [3, 16, 21, 23, 24, 22, 18, 17, 4, 2,
  15, 1], [6, 1, 3, 16, 18, 17, 20, 19, 5, 10, 14, 21], [11, 14, 2, 15, 7, 4, 17, 18, 19, 20, 22,
  5], [1, 2, 8, 12, 0, 15, 16, 14, 20, 23, 19, 18], [13, 3, 4, 9, 15, 0, 14, 16, 24, 19, 20, 17],
  [7, 5, 6, 8, 9, 25, 0, 15, 16, 18, 17, 20], [5, 12, 11, 10, 13, 26, 15, 0, 17, 16, 18, 19], [10,
  22, 14, 25, 5, 6, 3, 24, 26, 1, 23, 15], [25, 21, 7, 26, 2, 14, 24, 5, 11, 4, 16, 23], [2, 8, 1,
  14, 12, 24, 25, 26, 0, 17, 21, 22], [9, 4, 13, 3, 14, 23, 22, 21, 18, 0, 26, 25], [22, 7, 5, 21,
  26, 19, 23, 6, 8, 9, 0, 24], [12, 13, 10, 22, 25, 20, 5, 23, 21, 11, 24, 0], [4, 11, 9, 2, 6, 7,
  8, 1, 10, 3, 12, 13]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def chang₁EdgeCol (x y : _root_.SRG.chang₁.V) : Fin 12 :=
  ⟨min ((chang₁EdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    11, by omega⟩

theorem chang₁EdgeCol_symm : ∀ x y : _root_.SRG.chang₁.V,
    chang₁EdgeCol x y = chang₁EdgeCol y x := by native_decide

theorem chang₁EdgeCol_proper : ∀ u v w : _root_.SRG.chang₁.V,
    _root_.SRG.chang₁.Adj u v = true →
      _root_.SRG.chang₁.Adj u w = true → v ≠ w →
        chang₁EdgeCol u v ≠ chang₁EdgeCol u w := by native_decide

/-- **The first Chang graph is class one**: `χ' = Δ = 12`. -/
@[simp] theorem edgeChromNum_chang₁ : chang₁.edgeChromNum = 12 := by
  refine le_antisymm ?_ ?_
  · rw [chang₁_def]
    exact edgeChromNum_mk_le_of_colouring chang₁EdgeCol chang₁EdgeCol_symm
      chang₁EdgeCol_proper
  · have h := maxDeg_le_edgeChromNum chang₁
    rwa [maxDeg_chang₁] at h

/-- A `1`-factorization of the second Chang graph into 12 perfect matchings: row `v` names the
partner of `v` in each. -/
def chang₂EdgeColTable : List (List ℕ) :=
  [[2, 8, 12, 13, 17, 18, 19, 21, 23, 24, 25, 26], [15, 6, 10, 17, 12, 27, 23, 9, 14, 3, 8, 20], [0,
  19, 5, 15, 26, 10, 18, 25, 3, 13, 6, 24], [18, 14, 24, 10, 20, 4, 13, 6, 2, 1, 15, 27], [16, 24,
  7, 27, 22, 3, 21, 20, 13, 18, 14, 11], [22, 16, 2, 25, 9, 19, 26, 10, 11, 6, 7, 15], [7, 1, 20,
  19, 25, 8, 15, 3, 27, 5, 2, 10], [6, 11, 4, 21, 8, 25, 20, 27, 16, 19, 5, 22], [19, 0, 23, 20, 7,
  6, 25, 12, 17, 27, 1, 21], [12, 26, 15, 14, 5, 22, 17, 1, 10, 11, 23, 16], [26, 15, 1, 3, 27, 2,
  11, 5, 9, 12, 13, 6], [27, 7, 26, 16, 21, 12, 10, 13, 5, 9, 22, 4], [9, 21, 0, 23, 1, 11, 27, 8,
  26, 10, 17, 13], [21, 27, 18, 0, 24, 26, 3, 11, 4, 2, 10, 12], [17, 3, 22, 9, 23, 15, 24, 16, 1,
  20, 4, 18], [1, 10, 9, 2, 19, 14, 6, 17, 18, 16, 3, 5], [4, 5, 17, 11, 18, 21, 22, 14, 7, 15, 19,
  9], [14, 18, 16, 1, 0, 23, 9, 15, 8, 21, 12, 19], [3, 17, 13, 24, 16, 0, 2, 19, 15, 4, 21, 14],
  [8, 2, 25, 6, 15, 5, 0, 18, 21, 7, 16, 17], [25, 23, 6, 8, 3, 24, 7, 4, 22, 14, 27, 1], [13, 12,
  27, 7, 11, 16, 4, 0, 19, 17, 18, 8], [5, 25, 14, 26, 4, 9, 16, 24, 20, 23, 11, 7], [24, 20, 8, 12,
  14, 17, 1, 26, 0, 22, 9, 25], [23, 4, 3, 18, 13, 20, 14, 22, 25, 0, 26, 2], [20, 22, 19, 5, 6, 7,
  8, 2, 24, 26, 0, 23], [10, 9, 11, 22, 2, 13, 5, 23, 12, 25, 24, 0], [11, 13, 21, 4, 10, 1, 12, 7,
  6, 8, 20, 3]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def chang₂EdgeCol (x y : _root_.SRG.chang₂.V) : Fin 12 :=
  ⟨min ((chang₂EdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    11, by omega⟩

theorem chang₂EdgeCol_symm : ∀ x y : _root_.SRG.chang₂.V,
    chang₂EdgeCol x y = chang₂EdgeCol y x := by native_decide

theorem chang₂EdgeCol_proper : ∀ u v w : _root_.SRG.chang₂.V,
    _root_.SRG.chang₂.Adj u v = true →
      _root_.SRG.chang₂.Adj u w = true → v ≠ w →
        chang₂EdgeCol u v ≠ chang₂EdgeCol u w := by native_decide

/-- **The second Chang graph is class one**: `χ' = Δ = 12`. -/
@[simp] theorem edgeChromNum_chang₂ : chang₂.edgeChromNum = 12 := by
  refine le_antisymm ?_ ?_
  · rw [chang₂_def]
    exact edgeChromNum_mk_le_of_colouring chang₂EdgeCol chang₂EdgeCol_symm
      chang₂EdgeCol_proper
  · have h := maxDeg_le_edgeChromNum chang₂
    rwa [maxDeg_chang₂] at h

/-- A `1`-factorization of the third Chang graph into 12 perfect matchings: row `v` names the
partner of `v` in each. -/
def chang₃EdgeColTable : List (List ℕ) :=
  [[2, 6, 8, 12, 13, 14, 17, 18, 19, 23, 24, 25], [20, 12, 27, 17, 21, 26, 23, 10, 15, 9, 8, 3], [0,
  24, 25, 18, 19, 5, 21, 13, 14, 3, 10, 15], [21, 20, 26, 24, 27, 18, 4, 15, 10, 2, 13, 1], [26, 18,
  20, 27, 11, 16, 3, 24, 13, 6, 22, 7], [14, 21, 19, 16, 9, 2, 10, 22, 25, 15, 7, 11], [18, 0, 16,
  23, 24, 22, 13, 9, 17, 4, 11, 12], [19, 25, 14, 26, 16, 11, 22, 20, 27, 8, 5, 4], [17, 19, 0, 25,
  26, 27, 14, 23, 12, 7, 1, 20], [23, 17, 21, 22, 5, 15, 12, 6, 11, 1, 16, 10], [27, 14, 11, 15, 12,
  13, 5, 1, 3, 21, 2, 9], [12, 16, 10, 13, 4, 7, 27, 14, 9, 22, 6, 5], [11, 1, 23, 0, 10, 17, 9, 27,
  8, 13, 14, 6], [24, 27, 18, 11, 0, 10, 6, 2, 4, 12, 3, 14], [5, 10, 7, 19, 25, 0, 8, 11, 2, 27,
  12, 13], [16, 26, 17, 10, 18, 9, 19, 3, 1, 5, 21, 2], [15, 11, 6, 5, 7, 4, 26, 19, 22, 18, 9, 17],
  [8, 9, 15, 1, 23, 12, 0, 26, 6, 19, 18, 16], [6, 4, 13, 2, 15, 3, 24, 0, 26, 16, 17, 19], [7, 8,
  5, 14, 2, 25, 15, 16, 0, 17, 26, 18], [1, 3, 4, 21, 22, 24, 25, 7, 23, 26, 27, 8], [3, 5, 9, 20,
  1, 23, 2, 25, 24, 10, 15, 22], [25, 23, 24, 9, 20, 6, 7, 5, 16, 11, 4, 21], [9, 22, 12, 6, 17, 21,
  1, 8, 20, 0, 25, 24], [13, 2, 22, 3, 6, 20, 18, 4, 21, 25, 0, 23], [22, 7, 2, 8, 14, 19, 20, 21,
  5, 24, 23, 0], [4, 15, 3, 7, 8, 1, 16, 17, 18, 20, 19, 27], [10, 13, 1, 4, 3, 8, 11, 12, 7, 14,
  20, 26]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def chang₃EdgeCol (x y : _root_.SRG.chang₃.V) : Fin 12 :=
  ⟨min ((chang₃EdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    11, by omega⟩

theorem chang₃EdgeCol_symm : ∀ x y : _root_.SRG.chang₃.V,
    chang₃EdgeCol x y = chang₃EdgeCol y x := by native_decide

theorem chang₃EdgeCol_proper : ∀ u v w : _root_.SRG.chang₃.V,
    _root_.SRG.chang₃.Adj u v = true →
      _root_.SRG.chang₃.Adj u w = true → v ≠ w →
        chang₃EdgeCol u v ≠ chang₃EdgeCol u w := by native_decide

/-- **The third Chang graph is class one**: `χ' = Δ = 12`. -/
@[simp] theorem edgeChromNum_chang₃ : chang₃.edgeChromNum = 12 := by
  refine le_antisymm ?_ ?_
  · rw [chang₃_def]
    exact edgeChromNum_mk_le_of_colouring chang₃EdgeCol chang₃EdgeCol_symm
      chang₃EdgeCol_proper
  · have h := maxDeg_le_edgeChromNum chang₃
    rwa [maxDeg_chang₃] at h

/-- A `1`-factorization of the Hoffman–Singleton graph into 7 perfect matchings: row `v` names the
partner of `v` in each. -/
def hoffmanSingletonEdgeColTable : List (List ℕ) :=
  [[1, 4, 25, 30, 35, 40, 45], [0, 26, 2, 31, 36, 41, 46], [3, 32, 1, 27, 37, 42, 47], [2, 28, 33,
  38, 4, 43, 48], [29, 0, 34, 39, 3, 44, 49], [6, 9, 31, 25, 49, 37, 43], [5, 7, 32, 26, 38, 45,
  44], [8, 6, 39, 33, 27, 46, 40], [7, 34, 9, 28, 47, 35, 41], [30, 5, 8, 36, 42, 48, 29], [11, 14,
  41, 48, 25, 39, 32], [10, 49, 12, 42, 33, 26, 35], [13, 27, 11, 45, 43, 36, 34], [12, 46, 44, 14,
  28, 30, 37], [31, 10, 29, 13, 40, 47, 38], [33, 19, 16, 47, 44, 25, 36], [37, 17, 15, 40, 48, 34,
  26], [27, 16, 49, 18, 41, 38, 30], [45, 31, 42, 17, 39, 28, 19], [43, 15, 35, 29, 46, 32, 18],
  [46, 25, 38, 34, 21, 24, 42], [26, 47, 30, 43, 20, 22, 39], [48, 35, 27, 44, 23, 21, 31], [24, 40,
  36, 32, 22, 49, 28], [23, 29, 37, 41, 45, 20, 33], [28, 20, 0, 5, 10, 15, 27], [21, 1, 28, 6, 29,
  11, 16], [17, 12, 22, 2, 7, 29, 25], [25, 3, 26, 8, 13, 18, 23], [4, 24, 14, 19, 26, 27, 9], [9,
  33, 21, 0, 32, 13, 17], [14, 18, 5, 1, 34, 33, 22], [34, 2, 6, 23, 30, 19, 10], [15, 30, 3, 7, 11,
  31, 24], [32, 8, 4, 20, 31, 16, 12], [38, 22, 19, 37, 0, 8, 11], [39, 38, 23, 9, 1, 12, 15], [16,
  39, 24, 35, 2, 5, 13], [35, 36, 20, 3, 6, 17, 14], [36, 37, 7, 4, 18, 10, 21], [42, 23, 43, 16,
  14, 0, 7], [44, 43, 10, 24, 17, 1, 8], [40, 44, 18, 11, 9, 2, 20], [19, 41, 40, 21, 12, 3, 5],
  [41, 42, 13, 22, 15, 4, 6], [18, 48, 47, 12, 24, 6, 0], [20, 13, 48, 49, 19, 7, 1], [49, 21, 45,
  15, 8, 14, 2], [22, 45, 46, 10, 16, 9, 3], [47, 11, 17, 46, 5, 23, 4]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def hoffmanSingletonEdgeCol (x y : _root_.SRG.hoffmanSingleton.V) : Fin 7 :=
  ⟨min ((hoffmanSingletonEdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    6, by omega⟩

theorem hoffmanSingletonEdgeCol_symm : ∀ x y : _root_.SRG.hoffmanSingleton.V,
    hoffmanSingletonEdgeCol x y = hoffmanSingletonEdgeCol y x := by native_decide

theorem hoffmanSingletonEdgeCol_proper : ∀ u v w : _root_.SRG.hoffmanSingleton.V,
    _root_.SRG.hoffmanSingleton.Adj u v = true →
      _root_.SRG.hoffmanSingleton.Adj u w = true → v ≠ w →
        hoffmanSingletonEdgeCol u v ≠ hoffmanSingletonEdgeCol u w := by native_decide

/-- **The Hoffman–Singleton graph is class one**: `χ' = Δ = 7`. -/
@[simp] theorem edgeChromNum_hoffmanSingleton : hoffmanSingleton.edgeChromNum = 7 := by
  refine le_antisymm ?_ ?_
  · rw [hoffmanSingleton_def]
    exact edgeChromNum_mk_le_of_colouring hoffmanSingletonEdgeCol hoffmanSingletonEdgeCol_symm
      hoffmanSingletonEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum hoffmanSingleton
    rwa [maxDeg_hoffmanSingleton] at h

/-- A `1`-factorization of the Gewirtz graph into 10 perfect matchings: row `v` names the partner
of `v` in each. -/
def gewirtzEdgeColTable : List (List ℕ) :=
  [[29, 30, 33, 34, 37, 38, 46, 48, 50, 55], [28, 31, 32, 35, 38, 43, 45, 37, 51, 54], [30, 40, 35,
  32, 49, 39, 29, 44, 36, 52], [31, 28, 34, 33, 39, 36, 41, 42, 47, 53], [21, 23, 25, 27, 47, 49,
  37, 39, 54, 50], [20, 22, 37, 26, 42, 44, 39, 24, 55, 51], [22, 20, 27, 40, 25, 45, 36, 38, 53,
  48], [23, 21, 26, 46, 41, 24, 38, 43, 52, 36], [17, 19, 53, 51, 46, 26, 33, 35, 49, 25], [19, 17,
  52, 50, 45, 27, 32, 34, 24, 42], [16, 18, 41, 54, 26, 25, 34, 32, 48, 44], [24, 16, 40, 47, 33,
  18, 27, 55, 43, 35], [47, 52, 17, 18, 21, 22, 48, 51, 31, 29], [44, 50, 18, 43, 28, 53, 30, 17,
  23, 20], [55, 49, 45, 20, 31, 29, 23, 16, 41, 19], [54, 42, 22, 19, 16, 46, 40, 28, 30, 21], [10,
  11, 50, 53, 15, 52, 51, 14, 39, 38], [8, 9, 12, 39, 55, 40, 54, 13, 38, 41], [46, 10, 13, 12, 36,
  11, 42, 49, 45, 37], [9, 8, 47, 15, 48, 37, 43, 36, 44, 14], [5, 6, 54, 14, 52, 34, 47, 46, 35,
  13], [4, 7, 44, 45, 12, 55, 35, 53, 34, 15], [6, 5, 15, 41, 43, 12, 49, 50, 33, 32], [7, 4, 42,
  48, 32, 51, 14, 40, 13, 33], [11, 48, 30, 31, 54, 7, 53, 5, 9, 49], [52, 43, 4, 30, 6, 10, 55, 31,
  42, 8], [40, 45, 7, 5, 10, 8, 50, 47, 29, 28], [51, 29, 6, 4, 44, 9, 11, 41, 28, 46], [1, 3, 55,
  49, 13, 48, 52, 15, 27, 26], [0, 27, 43, 42, 53, 14, 2, 54, 26, 12], [2, 0, 24, 25, 51, 41, 13,
  45, 15, 47], [3, 1, 46, 24, 14, 50, 44, 25, 12, 40], [53, 55, 1, 2, 23, 47, 9, 10, 46, 22], [45,
  44, 0, 3, 11, 54, 8, 52, 22, 23], [49, 51, 3, 0, 40, 20, 10, 9, 21, 43], [48, 41, 2, 1, 50, 42,
  21, 8, 20, 11], [50, 54, 51, 55, 18, 3, 6, 19, 2, 7], [41, 53, 5, 52, 0, 19, 4, 1, 40, 18], [42,
  47, 49, 44, 1, 0, 7, 6, 17, 16], [43, 46, 48, 17, 3, 2, 5, 4, 16, 45], [26, 2, 11, 6, 34, 17, 15,
  23, 37, 31], [37, 35, 10, 22, 7, 30, 3, 27, 14, 17], [38, 15, 23, 29, 5, 35, 18, 3, 25, 9], [39,
  25, 29, 13, 22, 1, 19, 7, 11, 34], [13, 33, 21, 38, 27, 5, 31, 2, 19, 10], [33, 26, 14, 21, 9, 6,
  1, 30, 18, 39], [18, 39, 31, 7, 8, 15, 0, 20, 32, 27], [12, 38, 19, 11, 4, 32, 20, 26, 3, 30],
  [35, 24, 39, 23, 19, 28, 12, 0, 10, 6], [34, 14, 38, 28, 2, 4, 22, 18, 8, 24], [36, 13, 16, 9, 35,
  31, 26, 22, 0, 4], [27, 34, 36, 8, 30, 23, 16, 12, 1, 5], [25, 12, 9, 37, 20, 16, 28, 33, 7, 2],
  [32, 37, 8, 16, 29, 13, 24, 21, 6, 3], [15, 36, 20, 10, 24, 33, 17, 29, 4, 1], [14, 32, 28, 36,
  17, 21, 25, 11, 5, 0]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def gewirtzEdgeCol (x y : _root_.SRG.gewirtz.V) : Fin 10 :=
  ⟨min ((gewirtzEdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    9, by omega⟩

theorem gewirtzEdgeCol_symm : ∀ x y : _root_.SRG.gewirtz.V,
    gewirtzEdgeCol x y = gewirtzEdgeCol y x := by native_decide

theorem gewirtzEdgeCol_proper : ∀ u v w : _root_.SRG.gewirtz.V,
    _root_.SRG.gewirtz.Adj u v = true →
      _root_.SRG.gewirtz.Adj u w = true → v ≠ w →
        gewirtzEdgeCol u v ≠ gewirtzEdgeCol u w := by native_decide

/-- **The Gewirtz graph is class one**: `χ' = Δ = 10`. -/
@[simp] theorem edgeChromNum_gewirtz : gewirtz.edgeChromNum = 10 := by
  refine le_antisymm ?_ ?_
  · rw [gewirtz_def]
    exact edgeChromNum_mk_le_of_colouring gewirtzEdgeCol gewirtzEdgeCol_symm
      gewirtzEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum gewirtz
    rwa [maxDeg_gewirtz] at h

/-- A near-`1`-factorization of the `M₂₂` graph into 17 matchings: row `v` names the partner of
`v` in each matching, or `v` itself in the one matching that misses it. -/
def m22EdgeColTable : List (List ℕ) :=
  [[29, 30, 33, 34, 37, 38, 46, 48, 50, 55, 67, 68, 70, 71, 74, 76, 0], [72, 73, 68, 37, 69, 28, 31,
  67, 45, 51, 54, 1, 43, 38, 35, 75, 32], [39, 74, 66, 30, 36, 32, 69, 49, 72, 29, 2, 76, 52, 44,
  40, 65, 35], [42, 34, 73, 33, 71, 39, 36, 75, 31, 41, 65, 53, 47, 3, 70, 66, 28], [49, 25, 70, 64,
  74, 27, 21, 50, 63, 54, 4, 47, 75, 23, 37, 39, 72], [5, 51, 39, 22, 73, 37, 64, 76, 71, 26, 44,
  20, 63, 42, 24, 55, 69], [73, 70, 61, 45, 20, 62, 76, 72, 40, 38, 53, 27, 48, 25, 22, 36, 6], [74,
  46, 69, 52, 41, 61, 26, 62, 24, 36, 43, 21, 23, 7, 38, 71, 75], [76, 66, 62, 68, 63, 75, 25, 35,
  51, 8, 19, 33, 26, 49, 17, 46, 53], [64, 65, 27, 61, 34, 67, 32, 42, 52, 75, 76, 17, 45, 24, 50,
  19, 9], [34, 48, 64, 74, 10, 73, 44, 26, 32, 68, 66, 54, 25, 61, 41, 18, 16], [43, 62, 67, 47, 18,
  63, 73, 33, 16, 65, 24, 40, 11, 55, 27, 35, 74], [22, 71, 29, 66, 64, 52, 51, 47, 48, 31, 21, 72,
  18, 62, 67, 12, 17], [17, 23, 53, 50, 68, 44, 65, 71, 13, 28, 18, 61, 20, 30, 63, 72, 43], [68,
  64, 23, 62, 14, 65, 45, 69, 49, 70, 29, 41, 55, 19, 31, 16, 20], [40, 67, 28, 42, 61, 66, 54, 30,
  21, 46, 15, 63, 22, 70, 16, 69, 19], [71, 52, 72, 39, 38, 59, 53, 60, 11, 16, 50, 51, 76, 75, 15,
  14, 10], [13, 60, 59, 70, 39, 55, 74, 73, 69, 40, 41, 9, 54, 17, 8, 38, 12], [75, 58, 49, 76, 11,
  69, 70, 46, 57, 42, 13, 45, 12, 37, 36, 10, 18], [36, 37, 48, 19, 58, 71, 72, 74, 73, 47, 8, 43,
  57, 14, 44, 9, 15], [35, 47, 52, 67, 6, 60, 66, 54, 74, 58, 46, 5, 13, 20, 75, 34, 14], [55, 35,
  45, 58, 65, 68, 4, 53, 15, 73, 12, 7, 44, 76, 60, 21, 34], [12, 41, 43, 5, 49, 50, 68, 59, 65, 74,
  75, 57, 15, 32, 6, 33, 22], [48, 13, 14, 40, 51, 23, 67, 57, 66, 76, 73, 42, 7, 4, 59, 32, 33],
  [66, 59, 24, 48, 70, 54, 58, 68, 7, 72, 11, 49, 53, 9, 5, 31, 30], [67, 4, 71, 55, 59, 58, 8, 65,
  42, 69, 25, 52, 10, 6, 30, 43, 31], [47, 45, 65, 57, 50, 40, 7, 10, 70, 5, 72, 67, 8, 60, 28, 29,
  26], [51, 44, 9, 41, 57, 4, 60, 66, 68, 71, 69, 6, 46, 27, 11, 28, 29], [28, 55, 15, 49, 76, 1,
  62, 64, 58, 13, 48, 74, 59, 52, 26, 27, 3], [0, 63, 12, 43, 75, 42, 61, 58, 59, 2, 14, 29, 73, 54,
  53, 26, 27], [30, 0, 75, 2, 45, 51, 57, 15, 64, 62, 47, 73, 60, 13, 25, 41, 24], [31, 61, 76, 44,
  60, 57, 1, 63, 3, 12, 74, 46, 50, 40, 14, 24, 25], [63, 53, 55, 46, 47, 2, 9, 32, 10, 60, 71, 70,
  62, 22, 58, 23, 1], [60, 72, 0, 3, 44, 45, 52, 11, 54, 33, 61, 8, 69, 58, 64, 22, 23], [10, 3, 63,
  0, 9, 43, 40, 34, 62, 49, 51, 69, 72, 59, 57, 20, 21], [20, 21, 41, 59, 42, 48, 35, 8, 61, 50, 70,
  71, 64, 57, 1, 11, 2], [19, 54, 50, 60, 2, 36, 3, 51, 55, 7, 63, 64, 68, 67, 18, 6, 59], [37, 19,
  40, 1, 0, 5, 41, 52, 53, 61, 62, 66, 65, 18, 4, 59, 60], [38, 49, 58, 63, 16, 0, 42, 44, 47, 6,
  64, 65, 66, 1, 7, 17, 57], [2, 57, 5, 16, 17, 3, 43, 45, 46, 48, 58, 62, 67, 68, 39, 4, 61], [15,
  75, 37, 23, 40, 26, 34, 56, 6, 17, 68, 11, 71, 31, 2, 64, 58], [58, 22, 35, 27, 7, 76, 37, 41, 67,
  3, 17, 14, 56, 72, 10, 30, 63], [3, 56, 60, 15, 35, 29, 38, 9, 25, 18, 42, 23, 74, 5, 72, 68, 62],
  [11, 76, 22, 29, 66, 34, 39, 70, 60, 64, 7, 19, 1, 43, 56, 25, 13], [70, 27, 56, 31, 33, 13, 10,
  38, 75, 59, 5, 44, 21, 2, 19, 62, 67], [56, 26, 21, 6, 30, 33, 14, 39, 1, 45, 59, 18, 9, 74, 71,
  63, 66], [59, 7, 46, 32, 56, 72, 0, 18, 39, 15, 20, 31, 27, 73, 65, 8, 64], [26, 20, 47, 11, 32,
  56, 59, 12, 38, 19, 30, 4, 3, 69, 76, 61, 68], [23, 10, 19, 24, 48, 35, 63, 0, 12, 39, 28, 75, 6,
  56, 69, 60, 65], [4, 38, 18, 28, 22, 49, 56, 2, 14, 34, 60, 24, 61, 8, 73, 67, 71], [62, 69, 36,
  13, 26, 22, 50, 4, 0, 35, 16, 58, 31, 66, 9, 73, 56], [27, 5, 51, 56, 23, 30, 12, 36, 8, 1, 34,
  16, 58, 65, 61, 74, 70], [57, 16, 20, 7, 52, 12, 33, 37, 9, 63, 56, 25, 2, 28, 68, 70, 73], [69,
  32, 13, 53, 67, 74, 16, 21, 37, 56, 6, 3, 24, 64, 29, 57, 8], [65, 36, 57, 71, 62, 24, 15, 20, 33,
  4, 1, 10, 17, 29, 54, 56, 76], [21, 28, 32, 25, 72, 17, 75, 61, 36, 0, 57, 56, 14, 11, 66, 5, 55],
  [45, 42, 44, 51, 46, 47, 49, 40, 56, 53, 52, 55, 41, 48, 43, 54, 50], [52, 39, 54, 26, 27, 31, 30,
  23, 18, 57, 55, 22, 19, 35, 34, 53, 38], [41, 18, 38, 21, 19, 25, 24, 29, 28, 20, 39, 50, 51, 33,
  32, 58, 40], [46, 24, 17, 35, 25, 16, 47, 22, 29, 44, 45, 59, 28, 34, 23, 37, 36], [33, 17, 42,
  36, 31, 20, 27, 16, 43, 32, 49, 60, 30, 26, 21, 48, 37], [61, 31, 6, 9, 15, 7, 29, 55, 35, 37, 33,
  13, 49, 10, 51, 47, 39], [50, 11, 8, 14, 54, 6, 28, 7, 34, 30, 37, 39, 32, 12, 62, 44, 42], [32,
  29, 34, 38, 8, 11, 48, 31, 4, 52, 36, 15, 5, 63, 13, 45, 41], [9, 14, 10, 4, 12, 64, 5, 28, 30,
  43, 38, 36, 35, 53, 33, 40, 46], [54, 9, 26, 65, 21, 14, 13, 25, 22, 11, 3, 38, 37, 51, 46, 2,
  48], [24, 8, 2, 12, 43, 15, 20, 27, 23, 66, 10, 37, 38, 50, 55, 3, 45], [25, 15, 11, 20, 53, 9,
  23, 1, 41, 67, 0, 26, 39, 36, 12, 49, 44], [14, 68, 1, 8, 13, 21, 22, 24, 27, 10, 40, 0, 36, 39,
  52, 42, 47], [53, 50, 7, 69, 1, 18, 2, 14, 17, 25, 27, 34, 33, 47, 48, 15, 5], [44, 6, 4, 17, 24,
  70, 18, 43, 26, 14, 35, 32, 0, 15, 3, 52, 51], [16, 12, 25, 54, 3, 19, 71, 13, 5, 27, 32, 35, 40,
  0, 45, 7, 49], [1, 33, 16, 72, 55, 46, 19, 6, 2, 24, 26, 12, 34, 41, 42, 13, 4], [6, 1, 3, 73, 5,
  10, 11, 17, 19, 21, 23, 30, 29, 46, 49, 50, 52], [7, 2, 74, 10, 4, 53, 17, 19, 20, 22, 31, 28, 42,
  45, 0, 51, 11], [18, 40, 30, 75, 29, 8, 55, 3, 44, 9, 22, 48, 4, 16, 20, 1, 7], [8, 43, 31, 18,
  28, 41, 6, 5, 76, 23, 9, 2, 16, 21, 47, 0, 54]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def m22EdgeCol (x y : _root_.SRG.m22.V) : Fin 17 :=
  ⟨min ((m22EdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    16, by omega⟩

theorem m22EdgeCol_symm : ∀ x y : _root_.SRG.m22.V,
    m22EdgeCol x y = m22EdgeCol y x := by native_decide

theorem m22EdgeCol_proper : ∀ u v w : _root_.SRG.m22.V,
    _root_.SRG.m22.Adj u v = true →
      _root_.SRG.m22.Adj u w = true → v ≠ w →
        m22EdgeCol u v ≠ m22EdgeCol u w := by native_decide

/-- **The `M₂₂` graph is class two**: `χ' = Δ + 1 = 17`. -/
@[simp] theorem edgeChromNum_m22 : m22.edgeChromNum = 17 := by
  refine le_antisymm ?_ ?_
  · rw [m22_def]
    exact edgeChromNum_mk_le_of_colouring m22EdgeCol m22EdgeCol_symm
      m22EdgeCol_proper
  · have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd isRegularWith_m22
      (by omega) (by rw [V_m22])
    rw [maxDeg_m22] at h
    omega

/-- A `1`-factorization of the Higman–Sims graph into 22 perfect matchings: row `v` names the
partner of `v` in each. -/
def higmanSimsEdgeColTable : List (List ℕ) :=
  [[33, 24, 25, 27, 29, 22, 30, 28, 32, 31, 82, 37, 36, 99, 23, 79, 80, 78, 34, 81, 26, 35], [46,
  38, 43, 44, 86, 48, 83, 41, 22, 47, 78, 49, 84, 40, 39, 85, 24, 99, 23, 25, 45, 42], [87, 52, 26,
  40, 57, 54, 55, 38, 78, 27, 56, 90, 53, 51, 28, 41, 29, 39, 89, 88, 99, 50], [53, 93, 50, 78, 60,
  43, 44, 99, 31, 42, 94, 61, 45, 92, 32, 91, 51, 58, 52, 59, 33, 30], [98, 58, 97, 61, 47, 55, 48,
  95, 96, 78, 49, 57, 34, 35, 46, 56, 54, 36, 59, 60, 37, 99], [79, 50, 22, 58, 30, 63, 62, 34, 65,
  83, 99, 42, 26, 54, 66, 67, 46, 64, 91, 38, 87, 95], [23, 35, 99, 55, 51, 31, 69, 68, 79, 96, 92,
  84, 70, 71, 88, 63, 43, 62, 27, 58, 47, 38], [50, 28, 24, 39, 64, 85, 46, 93, 99, 36, 69, 43, 32,
  59, 68, 97, 79, 65, 72, 89, 73, 55], [25, 67, 47, 73, 72, 94, 86, 39, 29, 54, 33, 71, 66, 79, 99,
  90, 59, 98, 51, 42, 70, 37], [75, 80, 39, 23, 26, 56, 33, 98, 93, 74, 58, 44, 88, 52, 83, 68, 64,
  66, 99, 48, 36, 70], [49, 84, 71, 67, 97, 69, 53, 22, 57, 80, 32, 87, 99, 58, 65, 37, 75, 45, 74,
  27, 94, 39], [99, 85, 48, 59, 68, 96, 38, 31, 77, 76, 71, 66, 91, 65, 45, 52, 90, 80, 25, 28, 57,
  34], [67, 76, 49, 95, 53, 44, 64, 89, 92, 59, 80, 24, 29, 69, 56, 30, 99, 35, 38, 70, 77, 86],
  [76, 99, 72, 52, 36, 60, 27, 30, 25, 62, 70, 94, 49, 83, 74, 81, 40, 43, 65, 54, 89, 96], [70, 42,
  73, 53, 95, 90, 99, 60, 26, 65, 63, 75, 40, 84, 48, 77, 55, 81, 37, 31, 93, 24], [34, 23, 61, 75,
  42, 99, 32, 71, 62, 85, 29, 64, 98, 55, 81, 72, 87, 92, 77, 49, 52, 41], [48, 81, 91, 41, 99, 64,
  88, 63, 74, 71, 28, 33, 97, 22, 73, 43, 53, 54, 35, 61, 86, 76], [60, 92, 76, 68, 27, 33, 56, 97,
  24, 75, 50, 63, 41, 90, 47, 99, 82, 72, 83, 67, 34, 45], [74, 77, 62, 99, 67, 25, 57, 44, 51, 26,
  98, 89, 35, 32, 91, 73, 60, 41, 82, 68, 46, 84], [40, 82, 29, 31, 61, 76, 75, 62, 94, 44, 36, 69,
  95, 73, 57, 50, 88, 85, 47, 99, 66, 22], [61, 96, 45, 37, 28, 72, 40, 23, 86, 82, 74, 99, 93, 46,
  77, 87, 66, 69, 30, 51, 63, 56], [89, 86, 80, 83, 91, 79, 98, 78, 95, 99, 81, 88, 87, 85, 82, 96,
  93, 90, 84, 97, 92, 94], [51, 68, 5, 96, 70, 0, 93, 10, 1, 98, 52, 59, 77, 16, 89, 60, 72, 55, 56,
  92, 90, 19], [6, 15, 67, 9, 89, 91, 97, 20, 50, 53, 73, 95, 59, 60, 0, 65, 94, 57, 1, 76, 54, 90],
  [66, 0, 7, 94, 98, 57, 96, 87, 17, 51, 91, 12, 54, 62, 52, 71, 1, 88, 61, 74, 58, 14], [8, 56, 0,
  93, 92, 18, 87, 53, 13, 69, 95, 58, 75, 63, 55, 88, 50, 97, 11, 1, 61, 64], [45, 59, 2, 76, 9, 86,
  92, 47, 14, 18, 97, 96, 5, 61, 43, 94, 71, 49, 85, 72, 0, 69], [91, 66, 64, 0, 17, 61, 13, 77, 42,
  2, 48, 85, 46, 86, 59, 44, 95, 93, 6, 10, 98, 73], [62, 7, 42, 98, 20, 70, 94, 0, 58, 60, 16, 67,
  47, 44, 2, 83, 49, 95, 75, 11, 84, 92], [68, 65, 19, 84, 0, 58, 43, 83, 8, 63, 15, 46, 12, 97, 93,
  45, 2, 60, 48, 96, 91, 74], [97, 55, 90, 85, 5, 73, 0, 13, 98, 48, 68, 41, 71, 57, 84, 12, 47, 75,
  20, 39, 88, 3], [86, 97, 41, 19, 39, 6, 67, 11, 3, 0, 89, 72, 56, 64, 87, 49, 74, 46, 98, 14, 83,
  54], [90, 70, 95, 54, 83, 47, 15, 66, 0, 56, 10, 38, 7, 18, 3, 48, 86, 96, 63, 40, 76, 88], [0,
  46, 77, 62, 65, 17, 9, 55, 49, 38, 8, 16, 96, 87, 69, 95, 57, 84, 40, 85, 3, 89], [15, 53, 70, 89,
  43, 93, 74, 5, 88, 86, 39, 40, 4, 94, 44, 69, 73, 51, 0, 84, 17, 11], [39, 6, 83, 66, 52, 40, 90,
  94, 75, 50, 72, 65, 18, 4, 42, 93, 45, 12, 16, 87, 85, 0], [42, 90, 53, 87, 13, 71, 63, 51, 45, 7,
  19, 77, 0, 41, 67, 84, 38, 4, 92, 86, 9, 91], [83, 43, 92, 20, 76, 41, 52, 88, 85, 89, 38, 0, 50,
  68, 62, 10, 91, 44, 14, 64, 4, 8], [73, 1, 93, 72, 82, 81, 11, 2, 97, 33, 37, 32, 61, 74, 75, 98,
  36, 94, 12, 5, 60, 6], [35, 63, 9, 7, 31, 82, 95, 8, 91, 81, 34, 92, 60, 77, 1, 61, 76, 2, 62, 30,
  96, 10], [19, 98, 68, 2, 79, 35, 20, 59, 80, 91, 67, 34, 14, 1, 92, 58, 13, 71, 33, 32, 64, 97],
  [93, 69, 31, 16, 96, 37, 59, 1, 70, 95, 65, 30, 17, 36, 79, 2, 58, 18, 94, 66, 80, 15], [36, 14,
  28, 97, 15, 74, 76, 96, 27, 3, 88, 5, 89, 56, 35, 57, 68, 82, 80, 8, 69, 1], [80, 37, 1, 82, 34,
  3, 29, 90, 56, 87, 66, 7, 67, 98, 26, 16, 6, 13, 95, 57, 75, 77], [96, 54, 63, 1, 71, 12, 3, 18,
  87, 19, 55, 9, 72, 28, 34, 27, 81, 37, 79, 90, 97, 65], [26, 88, 20, 70, 55, 89, 73, 81, 36, 64,
  79, 62, 3, 95, 11, 29, 35, 10, 54, 98, 1, 17], [1, 33, 94, 92, 88, 53, 7, 52, 71, 90, 76, 29, 27,
  20, 4, 70, 5, 31, 81, 75, 18, 80], [64, 89, 8, 81, 4, 32, 91, 26, 52, 1, 87, 74, 28, 53, 17, 80,
  30, 77, 19, 65, 6, 93], [16, 94, 11, 50, 69, 1, 4, 67, 72, 30, 27, 51, 62, 82, 14, 32, 92, 89, 29,
  9, 79, 87], [10, 51, 12, 63, 93, 88, 66, 79, 33, 73, 4, 1, 13, 91, 90, 31, 28, 26, 50, 15, 82,
  68], [7, 5, 3, 48, 81, 84, 80, 70, 23, 35, 17, 86, 37, 96, 98, 19, 25, 74, 49, 77, 71, 2], [22,
  49, 81, 80, 6, 95, 85, 36, 18, 24, 83, 48, 76, 2, 97, 64, 3, 34, 8, 20, 65, 75], [84, 2, 82, 13,
  35, 67, 37, 46, 47, 79, 22, 97, 86, 9, 24, 11, 69, 73, 3, 95, 15, 63], [3, 34, 36, 14, 12, 46, 10,
  25, 66, 23, 96, 82, 2, 47, 85, 62, 16, 83, 68, 79, 72, 98], [85, 44, 84, 32, 75, 2, 68, 69, 82, 8,
  77, 93, 24, 5, 80, 92, 4, 16, 45, 13, 23, 31], [94, 30, 86, 6, 45, 4, 2, 33, 76, 66, 44, 83, 80,
  15, 25, 82, 14, 22, 67, 91, 74, 7], [81, 25, 65, 71, 73, 9, 17, 85, 43, 32, 2, 79, 31, 42, 12, 4,
  84, 91, 22, 94, 62, 20], [63, 64, 79, 86, 2, 24, 18, 72, 10, 92, 93, 4, 83, 30, 19, 42, 33, 23,
  70, 43, 11, 81], [77, 4, 89, 5, 85, 29, 81, 73, 28, 72, 9, 25, 90, 10, 76, 40, 41, 3, 86, 6, 24,
  82], [82, 26, 88, 11, 87, 83, 41, 40, 84, 12, 75, 22, 23, 7, 27, 74, 8, 63, 4, 3, 81, 62], [17,
  71, 87, 64, 3, 13, 79, 14, 69, 28, 85, 80, 39, 23, 86, 22, 18, 29, 88, 4, 38, 66], [20, 83, 15, 4,
  19, 27, 65, 80, 68, 84, 90, 3, 38, 26, 70, 39, 89, 67, 24, 16, 25, 79], [28, 78, 18, 33, 90, 80,
  5, 19, 15, 13, 86, 45, 48, 24, 37, 53, 97, 6, 39, 93, 56, 59], [57, 39, 44, 49, 80, 5, 36, 16, 89,
  29, 14, 17, 85, 25, 94, 6, 98, 59, 32, 78, 20, 52], [47, 57, 27, 60, 7, 16, 12, 82, 90, 45, 84,
  15, 94, 31, 96, 51, 9, 5, 78, 37, 40, 25], [92, 29, 56, 88, 33, 98, 61, 86, 5, 14, 41, 35, 82, 11,
  10, 23, 78, 7, 13, 47, 51, 44], [24, 27, 78, 35, 84, 92, 49, 32, 53, 55, 43, 11, 8, 81, 5, 89, 20,
  9, 97, 41, 19, 60], [12, 8, 23, 10, 18, 52, 31, 48, 81, 93, 40, 28, 43, 88, 36, 5, 96, 61, 55, 17,
  78, 85], [29, 22, 40, 17, 11, 87, 54, 6, 61, 94, 30, 81, 78, 37, 7, 9, 42, 86, 53, 18, 95, 49],
  [78, 41, 98, 91, 48, 10, 6, 54, 60, 25, 7, 19, 81, 12, 33, 34, 52, 20, 90, 83, 42, 26], [14, 32,
  34, 45, 22, 28, 82, 50, 41, 97, 13, 91, 6, 78, 61, 46, 85, 87, 57, 12, 8, 9], [95, 60, 10, 56, 44,
  36, 89, 15, 46, 16, 11, 8, 30, 6, 78, 24, 26, 40, 93, 82, 50, 83], [88, 91, 13, 38, 8, 20, 84, 57,
  48, 58, 35, 31, 44, 80, 95, 15, 22, 17, 7, 26, 53, 78], [38, 87, 14, 8, 56, 30, 45, 58, 83, 49,
  23, 78, 92, 19, 16, 18, 34, 52, 96, 80, 7, 27], [18, 95, 85, 90, 78, 42, 34, 92, 16, 9, 20, 47,
  79, 38, 13, 59, 31, 50, 10, 24, 55, 29], [9, 79, 96, 15, 54, 78, 19, 91, 35, 17, 59, 14, 25, 89,
  38, 86, 10, 30, 28, 46, 43, 51], [13, 12, 17, 26, 37, 19, 42, 84, 55, 11, 46, 98, 51, 93, 58, 78,
  39, 79, 87, 23, 32, 16], [58, 18, 33, 79, 94, 97, 78, 27, 11, 88, 54, 36, 22, 39, 20, 14, 83, 47,
  15, 50, 12, 43], [69, 62, 66, 3, 74, 75, 77, 21, 2, 4, 1, 73, 68, 70, 71, 76, 65, 0, 64, 63, 67,
  72], [5, 75, 57, 77, 40, 21, 60, 49, 6, 52, 45, 56, 74, 8, 41, 0, 7, 76, 44, 53, 48, 61], [43, 9,
  21, 51, 63, 62, 50, 61, 40, 10, 12, 60, 55, 72, 54, 47, 0, 11, 42, 73, 41, 46], [56, 16, 51, 47,
  50, 38, 58, 45, 67, 39, 21, 68, 69, 66, 15, 13, 44, 14, 46, 0, 59, 57], [59, 19, 52, 43, 38, 39,
  70, 64, 54, 20, 0, 53, 65, 48, 21, 55, 17, 42, 18, 71, 49, 58], [37, 61, 35, 21, 32, 59, 1, 29,
  73, 5, 51, 55, 57, 13, 9, 28, 77, 53, 17, 69, 31, 71], [52, 10, 54, 29, 66, 50, 72, 76, 59, 61,
  64, 6, 1, 14, 30, 36, 56, 33, 21, 34, 28, 18], [54, 11, 74, 30, 58, 7, 51, 56, 37, 15, 60, 27, 63,
  21, 53, 1, 70, 19, 26, 33, 35, 67], [31, 21, 55, 57, 1, 26, 8, 65, 20, 34, 62, 50, 52, 27, 60, 75,
  32, 68, 58, 36, 16, 12], [2, 73, 60, 36, 59, 68, 25, 24, 44, 43, 47, 10, 21, 33, 31, 20, 15, 70,
  76, 35, 5, 48], [72, 45, 59, 65, 46, 49, 16, 37, 34, 77, 42, 21, 9, 67, 6, 25, 19, 24, 60, 2, 30,
  32], [21, 47, 58, 34, 23, 45, 71, 12, 63, 37, 31, 18, 42, 75, 22, 66, 61, 48, 2, 7, 13, 33], [32,
  36, 30, 74, 62, 14, 35, 43, 64, 46, 61, 2, 58, 17, 49, 8, 11, 21, 69, 44, 22, 23], [27, 72, 16,
  69, 21, 23, 47, 75, 39, 40, 24, 70, 11, 49, 18, 3, 37, 56, 5, 55, 29, 36], [65, 17, 37, 46, 25,
  66, 26, 74, 12, 57, 6, 39, 73, 3, 40, 54, 48, 15, 36, 22, 21, 28], [41, 3, 38, 25, 49, 34, 22, 7,
  9, 67, 57, 54, 20, 76, 29, 35, 21, 27, 71, 62, 14, 47], [55, 48, 46, 24, 77, 8, 28, 35, 19, 68, 3,
  13, 64, 34, 63, 26, 23, 38, 41, 56, 10, 21], [71, 74, 32, 12, 14, 51, 39, 4, 21, 41, 25, 23, 19,
  45, 72, 33, 27, 28, 43, 52, 68, 5], [44, 20, 75, 22, 41, 11, 24, 42, 4, 6, 53, 26, 33, 50, 64, 21,
  67, 32, 73, 29, 39, 13], [30, 31, 4, 42, 10, 77, 23, 17, 38, 70, 26, 52, 16, 29, 51, 7, 62, 25,
  66, 21, 44, 40], [4, 40, 69, 28, 24, 65, 21, 9, 30, 22, 18, 76, 15, 43, 50, 38, 63, 8, 31, 45, 27,
  53], [11, 13, 6, 18, 16, 15, 14, 3, 7, 21, 5, 20, 10, 0, 8, 17, 12, 1, 9, 19, 2, 4]]

/-- The table read as an edge colouring: the colour of `x y` is the matching that `y` lies in as
seen from `x`. -/
def higmanSimsEdgeCol (x y : _root_.SRG.higmanSims.V) : Fin 22 :=
  ⟨min ((higmanSimsEdgeColTable.getD (FinEnum.equiv x).1 []).idxOf (FinEnum.equiv y).1)
    21, by omega⟩

theorem higmanSimsEdgeCol_symm : ∀ x y : _root_.SRG.higmanSims.V,
    higmanSimsEdgeCol x y = higmanSimsEdgeCol y x := by native_decide

theorem higmanSimsEdgeCol_proper : ∀ u v w : _root_.SRG.higmanSims.V,
    _root_.SRG.higmanSims.Adj u v = true →
      _root_.SRG.higmanSims.Adj u w = true → v ≠ w →
        higmanSimsEdgeCol u v ≠ higmanSimsEdgeCol u w := by native_decide

/-- **The Higman–Sims graph is class one**: `χ' = Δ = 22`. -/
@[simp] theorem edgeChromNum_higmanSims : higmanSims.edgeChromNum = 22 := by
  refine le_antisymm ?_ ?_
  · rw [higmanSims_def]
    exact edgeChromNum_mk_le_of_colouring higmanSimsEdgeCol higmanSimsEdgeCol_symm
      higmanSimsEdgeCol_proper
  · have h := maxDeg_le_edgeChromNum higmanSims
    rwa [maxDeg_higmanSims] at h

/-! ## Hamiltonian cycles

All ten are Hamiltonian, and each cycle below is written out as a `cyclicNumbering`: the vertices
in the order the cycle meets them, named by their `FinEnum` index.  Nothing is searched for at
elaboration time — the certificate is `n` adjacency queries and one injectivity check, so the ten
together cost less than one of the matchings above. -/

/-- A Hamiltonian cycle of the Shrikhande graph, as `FinEnum` indices. -/
def shrikhandeCycle : ℕ → _root_.SRG.shrikhande.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.shrikhande.V)).symm
    (([0, 3, 15, 12, 1, 2, 7, 6, 11, 8, 9, 13, 14, 10, 5, 4] : List (Fin 16)).getD i 0)

/-- **The Shrikhande graph is Hamiltonian.** -/
theorem isHamiltonian_shrikhande : shrikhande.IsHamiltonian := by
  rw [shrikhande_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 16) shrikhandeCycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the graph of lines on a cubic surface, as `FinEnum` indices. -/
def linesOnCubicCycle : ℕ → _root_.SRG.linesOnCubic.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.linesOnCubic.V)).symm
    (([0, 11, 22, 16, 2, 10, 3, 14, 18, 24, 21, 7, 4, 19, 17, 23, 13, 9, 5, 8, 15, 26, 12, 20, 1, 6,
      25] : List (Fin 27)).getD i 0)

/-- **The graph of lines on a cubic surface is Hamiltonian.** -/
theorem isHamiltonian_linesOnCubic : linesOnCubic.IsHamiltonian := by
  rw [linesOnCubic_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 27) linesOnCubicCycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the Schläfli graph, as `FinEnum` indices. -/
def schlafliCycle : ℕ → _root_.SRG.schlafli.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.schlafli.V)).symm
    (([0, 6, 21, 26, 25, 24, 10, 22, 23, 7, 8, 11, 20, 13, 4, 2, 5, 17, 14, 1, 3, 12, 16, 19, 9, 18,
      15] : List (Fin 27)).getD i 0)

/-- **The Schläfli graph is Hamiltonian.** -/
theorem isHamiltonian_schlafli : schlafli.IsHamiltonian := by
  rw [schlafli_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 27) schlafliCycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the first Chang graph, as `FinEnum` indices. -/
def chang₁Cycle : ℕ → _root_.SRG.chang₁.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.chang₁.V)).symm
    (([0, 17, 12, 23, 8, 1, 2, 14, 18, 24, 4, 16, 22, 26, 21, 25, 7, 11, 13, 9, 27, 3, 6, 10, 15, 5,
      19, 20] : List (Fin 28)).getD i 0)

/-- **The first Chang graph is Hamiltonian.** -/
theorem isHamiltonian_chang₁ : chang₁.IsHamiltonian := by
  rw [chang₁_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 28) chang₁Cycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the second Chang graph, as `FinEnum` indices. -/
def chang₂Cycle : ℕ → _root_.SRG.chang₂.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.chang₂.V)).symm
    (([0, 21, 12, 8, 17, 23, 1, 27, 20, 25, 6, 19, 7, 22, 14, 9, 16, 15, 5, 11, 26, 10, 2, 18, 13,
      4, 3, 24] : List (Fin 28)).getD i 0)

/-- **The second Chang graph is Hamiltonian.** -/
theorem isHamiltonian_chang₂ : chang₂.IsHamiltonian := by
  rw [chang₂_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 28) chang₂Cycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the third Chang graph, as `FinEnum` indices. -/
def chang₃Cycle : ℕ → _root_.SRG.chang₃.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.chang₃.V)).symm
    (([0, 17, 23, 8, 7, 4, 26, 27, 20, 3, 18, 24, 13, 2, 25, 14, 19, 16, 22, 11, 5, 15, 10, 21, 1,
      9, 6, 12] : List (Fin 28)).getD i 0)

/-- **The third Chang graph is Hamiltonian.** -/
theorem isHamiltonian_chang₃ : chang₃.IsHamiltonian := by
  rw [chang₃_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 28) chang₃Cycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the Hoffman–Singleton graph, as `FinEnum` indices. -/
def hoffmanSingletonCycle : ℕ → _root_.SRG.hoffmanSingleton.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.hoffmanSingleton.V)).symm
    (([0, 1, 46, 7, 39, 10, 48, 16, 26, 28, 25, 27, 29, 4, 3, 2, 32, 23, 24, 37, 13, 30, 17, 41, 44,
      15, 33, 11, 49, 5, 9, 8, 47, 21, 22, 35, 19, 43, 40, 14, 31, 18, 42, 20, 34, 12, 36, 38, 6,
      45] : List (Fin 50)).getD i 0)

/-- **The Hoffman–Singleton graph is Hamiltonian.** -/
theorem isHamiltonian_hoffmanSingleton : hoffmanSingleton.IsHamiltonian := by
  rw [hoffmanSingleton_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 50) hoffmanSingletonCycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the Gewirtz graph, as `FinEnum` indices. -/
def gewirtzCycle : ℕ → _root_.SRG.gewirtz.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.gewirtz.V)).symm
    (([0, 33, 23, 48, 28, 52, 7, 38, 16, 10, 44, 13, 50, 26, 8, 25, 55, 17, 39, 4, 54, 36, 51, 5,
      37, 19, 43, 1, 45, 9, 32, 2, 30, 24, 53, 6, 22, 49, 14, 41, 27, 29, 12, 21, 34, 20, 35, 11,
      47, 3, 31, 40, 15, 42, 18, 46] : List (Fin 56)).getD i 0)

/-- **The Gewirtz graph is Hamiltonian.** -/
theorem isHamiltonian_gewirtz : gewirtz.IsHamiltonian := by
  rw [gewirtz_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 56) gewirtzCycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the `M₂₂` graph, as `FinEnum` indices. -/
def m22Cycle : ℕ → _root_.SRG.m22.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.m22.V)).symm
    (([0, 74, 31, 50, 22, 33, 61, 55, 57, 35, 11, 27, 46, 39, 4, 64, 28, 58, 20, 5, 51, 12, 62, 7,
      24, 49, 14, 68, 8, 19, 43, 76, 9, 42, 23, 32, 2, 52, 73, 10, 66, 15, 70, 44, 21, 60, 16, 38,
      17, 54, 65, 13, 30, 25, 71, 45, 59, 36, 63, 34, 3, 47, 56, 48, 69, 53, 6, 40, 26, 29, 75, 18,
      37, 41, 72, 1, 67] : List (Fin 77)).getD i 0)

/-- **The `M₂₂` graph is Hamiltonian.** -/
theorem isHamiltonian_m22 : m22.IsHamiltonian := by
  rw [m22_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 77) m22Cycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-- A Hamiltonian cycle of the Higman–Sims graph, as `FinEnum` indices. -/
def higmanSimsCycle : ℕ → _root_.SRG.higmanSims.V := fun i ↦
  (FinEnum.equiv (α := _root_.SRG.higmanSims.V)).symm
    (([0, 23, 57, 30, 90, 32, 70, 22, 10, 97, 25, 61, 39, 1, 84, 34, 89, 18, 44, 63, 20, 74, 38, 72,
      31, 98, 15, 87, 24, 52, 46, 53, 2, 88, 9, 56, 12, 99, 4, 49, 79, 75, 35, 6, 47, 17, 60, 66,
      92, 28, 7, 50, 5, 65, 86, 55, 33, 62, 80, 51, 48, 14, 95, 21, 83, 77, 43, 82, 54, 93, 29, 68,
      37, 8, 94, 19, 85, 67, 36, 41, 58, 3, 42, 69, 78, 76, 13, 40, 71, 26, 59, 11, 96, 64, 27, 91,
      16, 73, 45, 81] : List (Fin 100)).getD i 0)

/-- **The Higman–Sims graph is Hamiltonian.** -/
theorem isHamiltonian_higmanSims : higmanSims.IsHamiltonian := by
  rw [higmanSims_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_of_cyclicNumbering (n := 100) higmanSimsCycle (by norm_num)
    (by native_decide) (by native_decide) (by native_decide)

/-! ## The Paley graph of a finite field

The same reading, for a graph with a parameter.  `paleyField F` is strongly regular with
parameters `(q, (q-1)/2, (q-5)/4, (q-1)/4)` whenever `q = Fintype.card F` is `1 mod 4`, so every
theorem above applies verbatim, with side conditions on `q` in place of arithmetic on literals:
`μ = (q-1)/4` is positive from `q ≥ 5` and `ℓ = (q-5)/4` from `q ≥ 9`.  The one member the girth
misses is `q = 5`, where `ℓ = 0` and `μ = 1` and the graph is the pentagon.

`paley q` — the same graph for `q` prime, built from a bitmask of quadratic residues rather than
from a field — carries its own copies of these; see `SmallGraphs.Tables` and `SmallGraphs.Bounds`.
-/

section
open Fintype
variable {F : Type} [Field F] [FinEnum F]

@[simp] theorem V_paleyField : (paleyField F).V = Fintype.card F := CGraph.card_paleyField

theorem four_mul_E_paleyField (hq : Fintype.card F % 4 = 1) :
    4 * (paleyField F).E = Fintype.card F * (Fintype.card F - 1) := by
  have h := (isSRGWith_paleyField (F := F) hq).two_mul_E
  have h2 : 2 * ((Fintype.card F - 1) / 2) = Fintype.card F - 1 := by omega
  calc 4 * (paleyField F).E = 2 * (2 * (paleyField F).E) := by ring
    _ = 2 * (Fintype.card F * ((Fintype.card F - 1) / 2)) := by rw [h]
    _ = Fintype.card F * (2 * ((Fintype.card F - 1) / 2)) := by ring
    _ = Fintype.card F * (Fintype.card F - 1) := by rw [h2]

theorem E_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).E = Fintype.card F * (Fintype.card F - 1) / 4 := by
  have h := four_mul_E_paleyField (F := F) hq
  set m := Fintype.card F * (Fintype.card F - 1) with hm
  omega

theorem isRegularWith_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).IsRegularWith ((Fintype.card F - 1) / 2) :=
  (isSRGWith_paleyField (F := F) hq).isRegularWith

theorem maxDeg_paleyField (hq : Fintype.card F % 4 = 1) :
    maxDeg (paleyField F) = (Fintype.card F - 1) / 2 :=
  (isSRGWith_paleyField (F := F) hq).maxDeg_eq (by omega)

theorem minDeg_paleyField (hq : Fintype.card F % 4 = 1) :
    minDeg (paleyField F) = (Fintype.card F - 1) / 2 :=
  (isSRGWith_paleyField (F := F) hq).minDeg_eq (by omega)

theorem degSequence_paleyField (hq : Fintype.card F % 4 = 1) :
    degSequence (paleyField F) = List.replicate (Fintype.card F) ((Fintype.card F - 1) / 2) :=
  (isSRGWith_paleyField (F := F) hq).degSequence

theorem degMultiset_paleyField (hq : Fintype.card F % 4 = 1) :
    degMultiset (paleyField F) = Multiset.replicate (Fintype.card F) ((Fintype.card F - 1) / 2) :=
  (isSRGWith_paleyField (F := F) hq).degMultiset

theorem isConnected_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    IsConnected (paleyField F) :=
  (isSRGWith_paleyField (F := F) hq).isConnected (by omega) (by omega)

theorem numComponents_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    (paleyField F).numComponents = 1 :=
  (isSRGWith_paleyField (F := F) hq).numComponents_eq_one (by omega) (by omega)

theorem diameter_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    (paleyField F).diameter = 2 :=
  (isSRGWith_paleyField (F := F) hq).diameter_eq_two (by omega) (by omega)

theorem radius_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    (paleyField F).radius = 2 :=
  (isSRGWith_paleyField (F := F) hq).radius_eq_two (by omega) (by omega)

theorem edgeConn_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    (paleyField F).edgeConn = (Fintype.card F - 1) / 2 :=
  (isSRGWith_paleyField (F := F) hq).edgeConn_eq (by omega) (by omega)

/-- `ℓ = (q-5)/4` is positive once `q ≥ 9`, so the two ends of an edge have a common neighbour.
For `q = 5` the graph is `C₅` and the girth is five. -/
theorem girth_paleyField (hq : Fintype.card F % 4 = 1) (hq9 : 9 ≤ Fintype.card F) :
    (paleyField F).girth = 3 :=
  (isSRGWith_paleyField (F := F) hq).girth_eq_three (by omega) (by omega) (by omega)

theorem not_isAcyclic_paleyField (hq : Fintype.card F % 4 = 1) (hq9 : 9 ≤ Fintype.card F) :
    ¬ IsAcyclic (paleyField F) :=
  not_isAcyclic_of_girth_pos (by rw [girth_paleyField hq hq9]; omega)

theorem not_isTree_paleyField (hq : Fintype.card F % 4 = 1) (hq9 : 9 ≤ Fintype.card F) :
    ¬ IsTree (paleyField F) :=
  not_isTree_of_girth_pos (by rw [girth_paleyField hq hq9]; omega)

/-- Not bipartite: that would force `q = 2 · (q-1)/2 = q - 1`. -/
theorem not_isBipartite_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    ¬ IsBipartite (paleyField F) :=
  (isSRGWith_paleyField (F := F) hq).not_isBipartite (by omega) (by omega) (by omega) (by omega)

/-- Translation alone gives `q` automorphisms; the full group has order `q(q-1)/2` for `q` prime,
and `q` is all the vertex-transitivity argument sees. -/
theorem le_autCount_paleyField : Fintype.card F ≤ (paleyField F).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := paleyField F)
    (by rw [V_paleyField]; exact Fintype.card_pos_iff.2 ⟨0⟩) (isVertexTransitive_paleyField F)
  rwa [V_paleyField] at h

/-- One vertex dominates only `(q+1)/2` of the `q`, so two are needed. -/
theorem two_le_domNum_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    2 ≤ (paleyField F).domNum := by
  have h := le_domNum_of_regular (G := paleyField F) (maxDeg_paleyField hq)
  rw [V_paleyField] at h
  by_contra hc
  have h2 : (paleyField F).domNum * ((Fintype.card F - 1) / 2 + 1)
      ≤ 1 * ((Fintype.card F - 1) / 2 + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

end

/-! **Paley graphs of fields are self-complementary**: multiplication by a fixed non-square
carries the graph onto its complement.  This is `CGraph.Iso.complPaleyField` at `IsoGraph`
level. -/

attribute [toIsoGraph simp compl_paleyField] CGraph.Iso.complPaleyField

section
open Fintype
variable {F : Type} [Field F] [FinEnum F]

/-- A field of odd order has a non-square, so `paleyField F` really does equal its complement. -/
theorem isSelfComplementary_paleyField (hq : Fintype.card F % 4 = 1) :
    IsSelfComplementary (paleyField F) := by
  have hchar : ringChar F ≠ 2 := fun h ↦ by
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hchar
  exact compl_paleyField hq hg

/-- **The Paley bound on clique numbers**, `ω ≤ √q`: the graph is vertex-transitive and equal to
its complement, so `ω · α = ω²` cannot exceed the number of vertices. -/
theorem cliqueNum_sq_le_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).cliqueNum ^ 2 ≤ Fintype.card F := by
  have h := cliqueNum_sq_le_V_of_compl_eq (isVertexTransitive_paleyField F)
    (isSelfComplementary_paleyField hq).compl_eq
  rwa [V_paleyField] at h

theorem indepNum_eq_cliqueNum_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).indepNum = (paleyField F).cliqueNum :=
  (isSelfComplementary_paleyField hq).cliqueNum_eq_indepNum.symm

theorem chromNum_eq_cliqueCoverNum_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).chromNum = (paleyField F).cliqueCoverNum :=
  (isSelfComplementary_paleyField hq).chromNum_eq_cliqueCoverNum

/-- Nordhaus–Gaddum, halved: `2χ ≤ q + 1`. -/
theorem two_mul_chromNum_paleyField_le (hq : Fintype.card F % 4 = 1) :
    2 * (paleyField F).chromNum ≤ Fintype.card F + 1 := by
  have h := (isSelfComplementary_paleyField hq).two_mul_chromNum_le
  rwa [V_paleyField] at h

theorem three_le_chromNum_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    3 ≤ (paleyField F).chromNum :=
  (isSelfComplementary_paleyField hq).three_le_chromNum (by rw [V_paleyField]; omega)

theorem three_le_cliqueCoverNum_paleyField (hq : Fintype.card F % 4 = 1)
    (hq5 : 5 ≤ Fintype.card F) : 3 ≤ (paleyField F).cliqueCoverNum := by
  have h := chromNum_eq_cliqueCoverNum_paleyField hq
  have h2 := three_le_chromNum_paleyField hq hq5
  omega

end

end IsoGraph
