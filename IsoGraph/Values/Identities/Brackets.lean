import IsoGraph.Values.Identities.TreesAndCycles

/-!
# Brackets, negative entries, and degenerate parameters

What is left of the tables after the exact values: the entries that are only known between two
bounds, and the entries that are negative.

The brackets are the domination numbers and edge chromatic numbers of the families where neither
bound is tight, and the automorphism counts that are only bounded below.  The negative entries are
the graphs that are *not* vertex- or arc-transitive, not self-complementary, or not class one, each
refuted by an invariant that would have to agree and does not.  The module ends with the degenerate
parameters of the tree-and-cycle families, where the definitions collapse to something simpler.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ### Lower bounds on automorphism counts

An arc-transitive graph has an automorphism carrying any arc to any other, so its automorphism
group is at least as large as its arc count `2E`.  These are the first entries in the
`autCount` row for anything other than `complete` and `empty`.
-/

/-- The Petersen graph is arc-transitive with `15` edges. -/
theorem thirty_le_autCount_petersen : 30 ≤ petersen.autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive isArcTransitive_petersen
  rw [E_petersen] at h
  omega

/-- The cycle is arc-transitive with `n` edges; its automorphism group is in fact exactly the
dihedral group of that order. -/
theorem two_mul_le_autCount_cycle (n : ℕ) : 2 * (n + 3) ≤ (cycle (n + 3)).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_cycle (n + 3))
  rw [E_cycle] at h
  omega

/-- The hypercube is arc-transitive with `n · 2ⁿ⁻¹` edges. -/
theorem mul_two_pow_le_autCount_hypercube (n : ℕ) : n * 2 ^ n ≤ (hypercube n).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_hypercube n)
  rw [E_hypercube] at h
  exact h

/-- Kneser graphs are arc-transitive, so `|Aut|` is at least the number of arcs. -/
theorem le_autCount_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    n.choose k * (n - k).choose k ≤ (kneser n k).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_kneser n k)
  rw [two_mul_E_kneser n hk] at h
  exact h

/-- `K_{n,n}` is arc-transitive with `n²` edges. -/
theorem le_autCount_bipartite_self (n : ℕ) : 2 * (n * n) ≤ (bipartite n n).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_bipartite_self n)
  rw [E_bipartite] at h
  exact h

/-! ### The negative entries of the vertex-transitivity column -/

/-- The friendship windmill has hub degree `2n` and rim degree `2`, so from two blades on it is
not vertex-transitive. -/
@[simp] theorem not_isVertexTransitive_friendship (n : ℕ) :
    ¬ IsVertexTransitive (friendship (n + 2)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 2 = (n + 1) + 1 from rfl, minDeg_friendship, maxDeg_friendship]
  omega

/-- The tadpole has a degree-one tail end and a degree-three junction. -/
@[simp] theorem not_isVertexTransitive_tadpole (m k : ℕ) :
    ¬ IsVertexTransitive (tadpole (m + 3) (k + 1)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [minDeg_tadpole, maxDeg_tadpole]
  omega

/-- The lollipop has a degree-one stick end and a clique of degree `m + 2`. -/
@[simp] theorem not_isVertexTransitive_lollipop (m k : ℕ) :
    ¬ IsVertexTransitive (lollipop (m + 2) (k + 1)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [minDeg_lollipop, maxDeg_lollipop]
  omega

/-- A double star with at least one leaf has leaves of degree one and a centre of degree at
least two.  (With no leaves at all it is `K₂`, which *is* vertex-transitive.) -/
@[simp] theorem not_isVertexTransitive_doubleStar (m n : ℕ) :
    ¬ IsVertexTransitive (doubleStar (m + 1) n) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [minDeg_doubleStar, maxDeg_doubleStar]
  omega

/-- **The Mycielskian of a `k`-regular graph is never vertex-transitive for `k ≥ 2`.**  The
shadow of a vertex keeps degree `k`, but the apex is joined to all `|V|` shadows and the
original vertices double their degree to `2k`; since `k + 1 ≤ |V|` and `k + 2 ≤ 2k`, the
minimum degree `k + 1` falls short of the maximum. -/
theorem not_isVertexTransitive_mycielskian {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hk : 2 ≤ k) (hV : 0 < G.V) : ¬ IsVertexTransitive (mycielskian G) := by
  have hlt : maxDeg G < G.V := maxDeg_lt_V hV
  have hmax : maxDeg G = k := h.maxDeg_eq hV
  have hmin : minDeg G = k := h.minDeg_eq hV
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [minDeg_mycielskian G hV, maxDeg_mycielskian G, hmax, hmin]
  omega

/-- In particular the Grötzsch graph's parent `C₅` is `2`-regular; the same argument covers every
Mycielskian tower step. -/
theorem not_isVertexTransitive_mycielskian_cycle (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (cycle (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_cycle n) (by omega) (by simp)

/-! ### The negative entries of the arc-transitivity column

Arc-transitivity implies vertex-transitivity as soon as there are no isolated vertices, so every
negative vertex-transitivity entry is also a negative arc-transitivity entry.  The lift of
`CGraph.isVertexTransitive_of_isArcTransitive` to the quotient states "no isolated vertices" as
`0 < δ`.
-/

/-- **Arc-transitive graphs with no isolated vertex are vertex-transitive.**  Given `u` and `v`,
pick any neighbours `u'` and `v'` and carry the arc `u → u'` to the arc `v → v'`. -/
theorem IsArcTransitive.isVertexTransitive {G : IsoGraph} (h : IsArcTransitive G)
    (hδ : 0 < G.minDeg) : IsVertexTransitive G := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [isVertexTransitive_mk]
  rw [isArcTransitive_mk] at h
  rw [minDeg_mk] at hδ
  refine CGraph.isVertexTransitive_of_isArcTransitive _ (fun u ↦ ?_) h
  have hd : 0 < g.canonicalize.toSimple.degree u :=
    lt_of_lt_of_le hδ (CGraph.minDeg_le_degree g.canonicalize u)
  obtain ⟨v, hv⟩ := (SimpleGraph.degree_pos_iff_exists_adj g.canonicalize.toSimple u).1 hd
  exact ⟨v, hv⟩

/-- The contrapositive, which is how the whole column below is filled. -/
theorem not_isArcTransitive_of_not_isVertexTransitive {G : IsoGraph} (hδ : 0 < G.minDeg)
    (h : ¬ IsVertexTransitive G) : ¬ IsArcTransitive G :=
  fun ha ↦ h (ha.isVertexTransitive hδ)

@[simp] theorem not_isArcTransitive_path (n : ℕ) : ¬ IsArcTransitive (path (n + 3)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 3 = n + 1 + 2 from rfl, minDeg_path]; omega) (not_isVertexTransitive_path n)

@[simp] theorem not_isArcTransitive_star (n : ℕ) : ¬ IsArcTransitive (star (n + 2)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 2 = n + 1 + 1 from rfl, minDeg_star]; omega) (not_isVertexTransitive_star n)

@[simp] theorem not_isArcTransitive_wheel (n : ℕ) : ¬ IsArcTransitive (wheel (n + 4)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 4 = n + 1 + 3 from rfl, minDeg_wheel]; omega) (not_isVertexTransitive_wheel n)

@[simp] theorem not_isArcTransitive_fan (n : ℕ) : ¬ IsArcTransitive (fan (n + 3)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 3 = n + 1 + 2 from rfl, minDeg_fan]; omega) (not_isVertexTransitive_fan n)

@[simp] theorem not_isArcTransitive_book (n : ℕ) : ¬ IsArcTransitive (book (n + 2)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 2 = n + 1 + 1 from rfl, minDeg_book]; omega) (not_isVertexTransitive_book n)

@[simp] theorem not_isArcTransitive_ladder (n : ℕ) : ¬ IsArcTransitive (ladder (n + 3)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 3 = n + 1 + 2 from rfl, minDeg_ladder]; omega)
    (not_isVertexTransitive_ladder n)

@[simp] theorem not_isArcTransitive_friendship (n : ℕ) : ¬ IsArcTransitive (friendship (n + 2)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 2 = n + 1 + 1 from rfl, minDeg_friendship]; omega)
    (not_isVertexTransitive_friendship n)

@[simp] theorem not_isArcTransitive_tadpole (m k : ℕ) :
    ¬ IsArcTransitive (tadpole (m + 3) (k + 1)) :=
  not_isArcTransitive_of_not_isVertexTransitive (by rw [minDeg_tadpole]; omega)
    (not_isVertexTransitive_tadpole m k)

@[simp] theorem not_isArcTransitive_lollipop (m k : ℕ) :
    ¬ IsArcTransitive (lollipop (m + 2) (k + 1)) :=
  not_isArcTransitive_of_not_isVertexTransitive (by rw [minDeg_lollipop]; omega)
    (not_isVertexTransitive_lollipop m k)

@[simp] theorem not_isArcTransitive_doubleStar (m n : ℕ) :
    ¬ IsArcTransitive (doubleStar (m + 1) n) :=
  not_isArcTransitive_of_not_isVertexTransitive (by rw [minDeg_doubleStar]; omega)
    (not_isVertexTransitive_doubleStar m n)

theorem not_isArcTransitive_grotzsch : ¬ IsArcTransitive grotzsch :=
  not_isArcTransitive_of_not_isVertexTransitive (by rw [minDeg_grotzsch]; omega)
    not_isVertexTransitive_grotzsch

/-! ### Automorphism counts of the vertex-transitive families -/

/-- A vertex-transitive graph has at least `|V|` automorphisms. -/
theorem le_autCount_foldedCube (n : ℕ) : 2 ^ n ≤ (foldedCube n).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := foldedCube n)
    (by rw [V_foldedCube]; positivity) (isVertexTransitive_foldedCube n)
  rwa [V_foldedCube] at h

theorem le_autCount_triangular (n : ℕ) : (n + 2).choose 2 ≤ (triangular (n + 2)).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := triangular (n + 2))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega)) (isVertexTransitive_triangular (n + 2))
  rwa [V_triangular] at h

theorem le_autCount_johnson {n k : ℕ} (hk : k ≤ n) : n.choose k ≤ (johnson n k).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := johnson n k)
    (by rw [V_johnson]; exact Nat.choose_pos hk) (isVertexTransitive_johnson n k)
  rwa [V_johnson] at h

theorem le_autCount_rook (m n : ℕ) :
    (m + 1) * (n + 1) ≤ (rook (m + 1) (n + 1)).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := rook (m + 1) (n + 1))
    (by rw [V_rook]; positivity) (isVertexTransitive_rook (m + 1) (n + 1))
  rwa [V_rook] at h

theorem le_autCount_prism (n : ℕ) : (n + 1) * 2 ≤ (prism (n + 1)).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := prism (n + 1))
    (by rw [V_prism]; positivity) (isVertexTransitive_prism (n + 1))
  rwa [V_prism] at h

theorem le_autCount_cocktailParty (n : ℕ) : 2 * (n + 1) ≤ (cocktailParty (n + 1)).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := cocktailParty (n + 1))
    (by rw [V_cocktailParty]; positivity) (isVertexTransitive_cocktailParty (n + 1))
  rwa [V_cocktailParty] at h

theorem le_autCount_crown (n : ℕ) : 2 * (n + 1) ≤ (crown (n + 1)).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := crown (n + 1))
    (by rw [V_crown]; positivity) (isVertexTransitive_crown (n + 1))
  rwa [V_crown] at h

theorem le_autCount_paley (q : ℕ) [NeZero q] [Fact q.Prime] : q ≤ (paley q).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := paley q)
    (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q)) (isVertexTransitive_paley q)
  rwa [V_paley] at h

theorem le_autCount_circulant (n : ℕ) (S : List ℕ) :
    n + 1 ≤ (circulant (n + 1) S).autCount := by
  have h := V_le_autCount_of_isVertexTransitive (G := circulant (n + 1) S)
    (by rw [V_circulant]; omega) (isVertexTransitive_circulant (n + 1) S)
  rwa [V_circulant] at h

theorem le_autCount_completeMultipartite_replicate (m d : ℕ) :
    (m + 1) * (d + 1) ≤ (completeMultipartite (List.replicate (m + 1) (d + 1))).autCount := by
  have h := V_le_autCount_of_isVertexTransitive
    (G := completeMultipartite (List.replicate (m + 1) (d + 1)))
    (by rw [V_completeMultipartite_replicate]; positivity)
    (isVertexTransitive_completeMultipartite_replicate (m + 1) (d + 1))
  rwa [V_completeMultipartite_replicate] at h

/-- The line graph of `Kₙ` has one vertex per edge, and it inherits vertex-transitivity from the
arc-transitivity of `Kₙ`. -/
theorem le_autCount_lineGraph_complete (n : ℕ) :
    (n + 2).choose 2 ≤ (lineGraph (complete (n + 2))).autCount := by
  have hE : (complete (n + 2)).E = (n + 2).choose 2 := E_complete (n + 2)
  have h := V_le_autCount_of_isVertexTransitive (G := lineGraph (complete (n + 2)))
    (by rw [V_lineGraph, hE]; exact Nat.choose_pos (by omega))
    ((isArcTransitive_complete (n + 2)).lineGraph)
  rwa [V_lineGraph, hE] at h

theorem le_autCount_lineGraph_cycle (n : ℕ) :
    n + 3 ≤ (lineGraph (cycle (n + 3))).autCount := by
  have hE : (cycle (n + 3)).E = n + 3 := E_cycle n
  have h := V_le_autCount_of_isVertexTransitive (G := lineGraph (cycle (n + 3)))
    (by rw [V_lineGraph, hE]; omega) (isVertexTransitive_lineGraph_cycle (n + 3))
  rwa [V_lineGraph, hE] at h

/-! ### Domination brackets from the degree bounds

`|V| ≤ γ · (Δ + 1)` (each chosen vertex dominates at most `Δ + 1` vertices) and `γ + Δ ≤ |V|`
(a maximum-degree vertex together with the complement of its closed neighbourhood dominates)
bracket the domination number of any regular graph as soon as the degree is known.
-/

/-- The circular ladder is cubic on `2n` vertices, so at least a quarter of them must be chosen. -/
theorem le_domNum_prism (n : ℕ) : n + 3 ≤ 2 * (prism (n + 3)).domNum := by
  have h := V_le_domNum_mul_maxDeg_add_one (prism (n + 3))
  rw [V_prism, maxDeg_prism] at h
  omega

/-- The matching upper bound. -/
theorem domNum_prism_le (n : ℕ) : (prism (n + 3)).domNum ≤ 2 * n + 3 := by
  have h := domNum_add_maxDeg_le_V (prism (n + 3))
  rw [V_prism, maxDeg_prism] at h
  omega

/-! ### Vertex-transitive graphs of odd order are class two -/

/-- **A vertex-transitive graph of odd order with an edge is class two.**  Vertex-transitivity
gives regularity, and a regular graph of odd order needs more than `Δ` edge colours because each
colour class is a matching and so misses a vertex. -/
theorem maxDeg_lt_edgeChromNum_of_isVertexTransitive_odd {G : IsoGraph}
    (h : IsVertexTransitive G) (hodd : G.V % 2 = 1) (hE : 0 < G.E) :
    maxDeg G < G.edgeChromNum := by
  have hV : 0 < G.V := by omega
  refine maxDeg_lt_edgeChromNum_of_isRegularWith_odd
    (isRegularWith_minDeg_of_isVertexTransitive hV h) ?_ hodd
  by_contra hk
  have hk0 : G.minDeg = 0 := by omega
  have h2 := two_mul_E_of_isVertexTransitive hV h
  rw [hk0, Nat.mul_zero] at h2
  omega

/-- Every circulant graph on an odd number of vertices is class two. -/
theorem maxDeg_lt_edgeChromNum_circulant {n : ℕ} {S : List ℕ} (hodd : n % 2 = 1)
    (hE : 0 < (circulant n S).E) :
    maxDeg (circulant n S) < (circulant n S).edgeChromNum :=
  maxDeg_lt_edgeChromNum_of_isVertexTransitive_odd (isVertexTransitive_circulant n S)
    (by rw [V_circulant]; exact hodd) hE

/-- Kneser graphs with an odd number of vertices are class two: `χ'(K(n, k)) > C(n − k, k)`. -/
theorem edgeChromNum_kneser_ge {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hodd : n.choose k % 2 = 1) : (n - k).choose k < (kneser n k).edgeChromNum := by
  have hkn : k ≤ n := by omega
  have hE : 0 < (kneser n k).E := by
    have h := two_mul_E_kneser n hk
    have hp : 0 < n.choose k * (n - k).choose k :=
      Nat.mul_pos (Nat.choose_pos hkn) (Nat.choose_pos (by omega))
    omega
  have h := maxDeg_lt_edgeChromNum_of_isVertexTransitive_odd (isVertexTransitive_kneser n k)
    (by rw [V_kneser]; exact hodd) hE
  rwa [maxDeg_kneser n k hk hkn] at h

/-- `K(7, 3)` is `4`-regular on `35` vertices, so it needs at least five edge colours. -/
theorem edgeChromNum_kneser_seven_three_ge : 5 ≤ (kneser 7 3).edgeChromNum := by
  have h := edgeChromNum_kneser_ge (n := 7) (k := 3) (by norm_num) (by norm_num) (by decide)
  norm_num at h
  omega

/-- Johnson graphs with an odd number of vertices are class two: `χ'(J(n, k)) > k(n − k)`. -/
theorem edgeChromNum_johnson_ge {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (hodd : n.choose k % 2 = 1) : k * (n - k) < (johnson n k).edgeChromNum := by
  have hV : 0 < (johnson n k).V := by rw [V_johnson]; exact Nat.choose_pos hkn.le
  have hd : maxDeg (johnson n k) = k * (n - k) := maxDeg_johnson hkn.le
  have hmin : minDeg (johnson n k) = k * (n - k) := by
    rw [minDeg_eq_maxDeg_of_isVertexTransitive hV (isVertexTransitive_johnson n k), hd]
  have hE : 0 < (johnson n k).E := by
    have h := two_mul_E_of_isVertexTransitive hV (isVertexTransitive_johnson n k)
    rw [hmin, V_johnson] at h
    have hp : 0 < n.choose k * (k * (n - k)) :=
      Nat.mul_pos (Nat.choose_pos hkn.le) (Nat.mul_pos (by omega) (by omega))
    omega
  have h := maxDeg_lt_edgeChromNum_of_isVertexTransitive_odd (isVertexTransitive_johnson n k)
    (by rw [V_johnson]; exact hodd) hE
  rwa [hd] at h

/-- `J(7, 3)` is `12`-regular on `35` vertices. -/
theorem edgeChromNum_johnson_seven_three_ge : 13 ≤ (johnson 7 3).edgeChromNum := by
  have h := edgeChromNum_johnson_ge (n := 7) (k := 3) (by norm_num) (by norm_num) (by decide)
  norm_num at h
  omega

/-! ### Independence and cover bounds for the tree-and-cycle families

`|V| ≤ χ · α` — some colour class has at least `|V| / χ` vertices, and colour classes are
independent — turns every known chromatic number into an independence lower bound, and
`τ + α = |V|` turns that into a cover upper bound.  These are the first entries in the
`indepNum` and `coverNum` rows for the spider, the tadpole, the lollipop and the theta graph.
-/

theorem le_indepNum_spider (legs : List ℕ) (h : 0 < legs.sum) :
    1 + legs.sum ≤ 2 * (spider legs).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (spider legs)
  rw [chromNum_spider legs h, V_spider] at h1
  omega

theorem coverNum_spider_le (legs : List ℕ) (h : 0 < legs.sum) :
    2 * (spider legs).coverNum ≤ 1 + legs.sum := by
  have h1 := coverNum_add_indepNum (spider legs)
  have h2 := le_indepNum_spider legs h
  rw [V_spider] at h1
  omega

theorem le_indepNum_tadpole_even (m k : ℕ) :
    2 * m + k + 4 ≤ 2 * (tadpole (2 * m + 4) k).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (tadpole (2 * m + 4) k)
  rw [chromNum_tadpole_even, V_tadpole] at h1
  omega

theorem coverNum_tadpole_even_le (m k : ℕ) :
    2 * (tadpole (2 * m + 4) k).coverNum ≤ 2 * m + k + 4 := by
  have h1 := coverNum_add_indepNum (tadpole (2 * m + 4) k)
  have h2 := le_indepNum_tadpole_even m k
  rw [V_tadpole] at h1
  omega

theorem le_indepNum_tadpole_odd (m k : ℕ) :
    2 * m + k + 3 ≤ 3 * (tadpole (2 * m + 3) k).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (tadpole (2 * m + 3) k)
  rw [chromNum_tadpole_odd, V_tadpole] at h1
  omega

theorem coverNum_tadpole_odd_le (m k : ℕ) :
    3 * (tadpole (2 * m + 3) k).coverNum ≤ 2 * (2 * m + k + 3) := by
  have h1 := coverNum_add_indepNum (tadpole (2 * m + 3) k)
  have h2 := le_indepNum_tadpole_odd m k
  rw [V_tadpole] at h1
  omega

/-- The lollipop needs `m + 2` colours for its clique, so the bound is weak, but it is the first
entry in the cell. -/
theorem le_indepNum_lollipop (m k : ℕ) :
    m + k + 2 ≤ (m + 2) * (lollipop (m + 2) k).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (lollipop (m + 2) k)
  rw [chromNum_lollipop, V_lollipop] at h1
  omega

theorem le_indepNum_thetaGraph_even {xs : List ℕ} (hne : xs ≠ []) (h0 : ∀ k ∈ xs, 0 < k)
    (h : ∀ k ∈ xs, k % 2 = 0) : 2 + xs.sum ≤ 2 * (thetaGraph xs).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (thetaGraph xs)
  rw [chromNum_thetaGraph_even hne h0 h, V_thetaGraph] at h1
  omega

theorem coverNum_thetaGraph_even_le {xs : List ℕ} (hne : xs ≠ []) (h0 : ∀ k ∈ xs, 0 < k)
    (h : ∀ k ∈ xs, k % 2 = 0) : 2 * (thetaGraph xs).coverNum ≤ 2 + xs.sum := by
  have h1 := coverNum_add_indepNum (thetaGraph xs)
  have h2 := le_indepNum_thetaGraph_even hne h0 h
  rw [V_thetaGraph] at h1
  omega

theorem le_indepNum_thetaGraph_odd {xs : List ℕ} (hne : xs ≠ []) (h : ∀ k ∈ xs, k % 2 = 1) :
    2 + xs.sum ≤ 2 * (thetaGraph xs).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (thetaGraph xs)
  rw [chromNum_thetaGraph_odd hne h, V_thetaGraph] at h1
  omega

theorem le_indepNum_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t + 2) :
    2 * t + 2 + ks.sum ≤ 2 * (cyclePendant (2 * t + 2) ks).indepNum := by
  have h1 := V_le_chromNum_mul_indepNum (cyclePendant (2 * t + 2) ks)
  rw [chromNum_cyclePendant_even t ks h, V_cyclePendant] at h1
  omega

theorem coverNum_cyclePendant_even_le (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t + 2) :
    2 * (cyclePendant (2 * t + 2) ks).coverNum ≤ 2 * t + 2 + ks.sum := by
  have h1 := coverNum_add_indepNum (cyclePendant (2 * t + 2) ks)
  have h2 := le_indepNum_cyclePendant_even t ks h
  rw [V_cyclePendant] at h1
  omega

/-! ### Edge chromatic lower bounds from the maximum degree

`Δ ≤ χ'` because the edges at a vertex pairwise conflict.  Until Vizing's theorem is available
this is the only entry many of these cells can have, but it is a sharp one: for every class-one
graph it is the answer.
-/

/-- The Mycielskian's apex sees every shadow, and the original vertices double their degree. -/
theorem le_edgeChromNum_mycielskian (G : IsoGraph) :
    max (2 * maxDeg G) G.V ≤ (mycielskian G).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (mycielskian G)
  rwa [maxDeg_mycielskian] at h

theorem le_edgeChromNum_grotzsch : 5 ≤ grotzsch.edgeChromNum := by
  have h := maxDeg_le_edgeChromNum grotzsch
  rwa [maxDeg_grotzsch] at h

theorem edgeChromNum_grotzsch_le : grotzsch.edgeChromNum ≤ 9 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one grotzsch
  rwa [maxDeg_grotzsch] at h

theorem le_edgeChromNum_ladder (n : ℕ) : 3 ≤ (ladder (n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (ladder (n + 3))
  rwa [maxDeg_ladder] at h

theorem edgeChromNum_ladder_le (n : ℕ) : (ladder (n + 3)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (ladder (n + 3))
  rwa [maxDeg_ladder] at h

theorem le_edgeChromNum_prism (n : ℕ) : 3 ≤ (prism (n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (prism (n + 3))
  rwa [maxDeg_prism] at h

theorem edgeChromNum_prism_le (n : ℕ) : (prism (n + 3)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (prism (n + 3))
  rwa [maxDeg_prism] at h

theorem le_edgeChromNum_crown (n : ℕ) : n + 1 ≤ (crown (n + 2)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (crown (n + 2))
  rwa [maxDeg_crown] at h

/-- Transporting `CGraph.chromNum_lineGraph_le_of_edgeColouring` to the quotient: an explicit
symmetric colouring of the ordered pairs, proper on the edges, bounds the chromatic index. -/
theorem edgeChromNum_mk_le_of_colouring {G : CGraph} {k : ℕ}
    (c : G.V → G.V → Fin k) (hsymm : ∀ x y, c x y = c y x)
    (hproper : ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w) :
    edgeChromNum ⟦G⟧ ≤ k := by
  rw [edgeChromNum_eq, lineGraph_mk, chromNum_mk]
  exact CGraph.chromNum_lineGraph_le_of_edgeColouring c hsymm hproper

/-- **The chromatic index of a ladder is three.**  The lower bound is the maximum degree and the
upper bound is `CGraph.ladderCol`, so Vizing's alternative never has to be ruled out. -/
theorem edgeChromNum_ladder (n : ℕ) : (ladder (n + 3)).edgeChromNum = 3 := by
  refine le_antisymm ?_ (le_edgeChromNum_ladder n)
  rw [show (ladder (n + 3)) = path (n + 3) □g complete 2 from rfl, path_def, complete_def 2,
    cartesianProduct_mk]
  exact edgeChromNum_mk_le_of_colouring
    (G := CGraph.cartesianProduct (CGraph.path (n + 3)) (CGraph.complete 2))
    (CGraph.ladderCol (n + 3)) (CGraph.ladderCol_symm (n + 3)) (CGraph.ladderCol_proper (n + 3))

/-- **The chromatic index of a crown is its degree.**  `S_{n+2}^0` is `(n+1)`-regular and class
one, by the difference colouring `CGraph.crownCol`. -/
theorem edgeChromNum_crown (n : ℕ) : (crown (n + 2)).edgeChromNum = n + 1 := by
  refine le_antisymm ?_ (le_edgeChromNum_crown n)
  rw [show (crown (n + 2)) = complete (n + 2) ⊗g complete 2 from rfl, complete_def (n + 2),
    complete_def 2, tensorProduct_mk]
  exact edgeChromNum_mk_le_of_colouring
    (G := CGraph.tensorProduct (CGraph.complete (n + 2)) (CGraph.complete 2))
    (CGraph.crownCol n) (CGraph.crownCol_symm n) (CGraph.crownCol_proper n)

/-- **The chromatic index of a prism is three.**  `Cₙ □ K₂` is cubic, and `CGraph.prismCol`
three-colours its edges for every `n ≥ 3` and either parity, so the prism is class one. -/
theorem edgeChromNum_prism (n : ℕ) : (prism (n + 3)).edgeChromNum = 3 := by
  refine le_antisymm ?_ (le_edgeChromNum_prism n)
  rw [show (prism (n + 3)) = cycle (n + 3) □g complete 2 from rfl, cycle_def, complete_def 2,
    cartesianProduct_mk]
  exact edgeChromNum_mk_le_of_colouring
    (G := CGraph.cartesianProduct (CGraph.cycle (n + 3)) (CGraph.complete 2))
    (CGraph.prismCol (n + 3)) (CGraph.prismCol_symm (n + 3)) (CGraph.prismCol_proper n)

/-- **The chromatic index of the Grötzsch graph is five.**  Its maximum degree is five, and
`CGraph.grotzschColTable` exhibits a five-colouring, so the Grötzsch graph is class one. -/
theorem edgeChromNum_grotzsch : grotzsch.edgeChromNum = 5 := by
  refine le_antisymm ?_ le_edgeChromNum_grotzsch
  rw [show grotzsch = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.mycielskian (CGraph.cycle 5))
    CGraph.grotzschCol CGraph.grotzschCol_symm CGraph.grotzschCol_proper

theorem le_edgeChromNum_cocktailParty (n : ℕ) :
    2 * n ≤ (cocktailParty (n + 1)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (cocktailParty (n + 1))
  rwa [maxDeg_cocktailParty] at h

/-- The round-robin colouring `CGraph.cpCol` uses `2n+2` colours on `K_{(n+2)×2}`. -/
theorem edgeChromNum_cocktailParty_le (n : ℕ) :
    (cocktailParty (n + 2)).edgeChromNum ≤ 2 * n + 2 := by
  rw [show (cocktailParty (n + 2) : IsoGraph)
      = completeMultipartite (List.replicate (n + 2) 2) from rfl, completeMultipartite_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.cocktailParty (n + 2))
    (CGraph.cpCol n) (CGraph.cpCol_symm n) (CGraph.cpCol_proper n)

/-- **The chromatic index of a cocktail party graph is its degree.**  `K_{(n+1)×2}` is
`K_{2n+2}` minus a perfect matching; deleting one factor of the round-robin `1`-factorisation of
`K_{2n+2}` leaves exactly that graph, `2n`-coloured, so the cocktail party graph is class one. -/
theorem edgeChromNum_cocktailParty (n : ℕ) : (cocktailParty (n + 1)).edgeChromNum = 2 * n := by
  rcases n with _ | k
  · rw [show (0 : ℕ) + 1 = 1 from rfl, cocktailParty_one, edgeChromNum_empty]
  · have hle := edgeChromNum_cocktailParty_le k
    have hge : 2 * (k + 1) ≤ (cocktailParty (k + 2)).edgeChromNum :=
      le_edgeChromNum_cocktailParty (k + 1)
    show (cocktailParty (k + 2)).edgeChromNum = 2 * (k + 1)
    omega

theorem le_edgeChromNum_book (n : ℕ) : n + 2 ≤ (book (n + 1)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (book (n + 1))
  rwa [maxDeg_book] at h

theorem le_edgeChromNum_fan (n : ℕ) : n + 3 ≤ (fan (n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (fan (n + 3))
  rwa [maxDeg_fan] at h

theorem le_edgeChromNum_doubleStar (m n : ℕ) :
    max m n + 1 ≤ (doubleStar m n).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (doubleStar m n)
  rwa [maxDeg_doubleStar] at h

/-- **The chromatic index of a double star is its maximum degree.**  A tree is always class one;
here the colouring is explicit, numbering the pendants at each hub from `1` and giving the central
edge colour `0`. -/
theorem edgeChromNum_doubleStar (m n : ℕ) : (doubleStar m n).edgeChromNum = max m n + 1 := by
  refine le_antisymm ?_ (le_edgeChromNum_doubleStar m n)
  rw [doubleStar_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.doubleStar m n)
    (CGraph.doubleStarCol m n) (CGraph.doubleStarCol_symm m n) (CGraph.doubleStarCol_proper m n)

theorem le_edgeChromNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    n - n / r ≤ (turan n r).edgeChromNum := by
  have h1 := maxDeg_le_edgeChromNum (turan n r)
  rwa [maxDeg_turan hr h] at h1

/-! ### Domination brackets for the tadpole and the lollipop -/

/-- The tadpole is cubic at its junction and has `m + k + 4` vertices. -/
theorem le_domNum_tadpole (m k : ℕ) :
    m + k + 4 ≤ 4 * (tadpole (m + 3) (k + 1)).domNum := by
  have h := V_le_domNum_mul_maxDeg_add_one (tadpole (m + 3) (k + 1))
  rw [V_tadpole, maxDeg_tadpole] at h
  omega

theorem domNum_tadpole_le (m k : ℕ) :
    (tadpole (m + 3) (k + 1)).domNum + 3 ≤ m + k + 4 := by
  have h := domNum_add_maxDeg_le_V (tadpole (m + 3) (k + 1))
  rw [V_tadpole, maxDeg_tadpole] at h
  omega

/-- The lollipop's clique vertex dominates the whole head at once. -/
theorem le_domNum_lollipop (m k : ℕ) :
    m + k + 3 ≤ (lollipop (m + 2) (k + 1)).domNum * (m + 3) := by
  have h := V_le_domNum_mul_maxDeg_add_one (lollipop (m + 2) (k + 1))
  rw [V_lollipop, maxDeg_lollipop] at h
  have h2 : (lollipop (m + 2) (k + 1)).domNum * (m + 2 + 1)
      = (lollipop (m + 2) (k + 1)).domNum * (m + 3) := by ring
  omega

theorem domNum_lollipop_le (m k : ℕ) :
    (lollipop (m + 2) (k + 1)).domNum + m + 2 ≤ m + k + 3 := by
  have h := domNum_add_maxDeg_le_V (lollipop (m + 2) (k + 1))
  rw [V_lollipop, maxDeg_lollipop] at h
  omega

/-! ### Counting edges detects the cycles

A graph with at least as many edges as vertices cannot be a tree, and if it is also connected it
cannot be acyclic.  This is the cheapest cycle detector in the library: it needs no witness
cycle, only the two counts.
-/

theorem not_isTree_of_V_le_E {G : IsoGraph} (h : G.V ≤ G.E) : ¬ IsTree G :=
  fun ht ↦ by have := ht.E_add_one; omega

theorem not_isTree_of_not_isAcyclic {G : IsoGraph} (h : ¬ IsAcyclic G) : ¬ IsTree G :=
  fun ht ↦ h ((isTree_iff_isConnected_and_isAcyclic G).1 ht).2

theorem not_isAcyclic_of_V_le_E {G : IsoGraph} (hc : IsConnected G) (h : G.V ≤ G.E) :
    ¬ IsAcyclic G :=
  not_isAcyclic_of_isConnected hc (not_isTree_of_V_le_E h)

/-- The tadpole has exactly as many edges as vertices. -/
@[simp] theorem not_isTree_tadpole (m k : ℕ) : ¬ IsTree (tadpole (m + 3) k) :=
  not_isTree_of_V_le_E (by rw [V_tadpole, E_tadpole])

/-- Attaching pendant paths to a cycle keeps the edge and vertex counts equal. -/
theorem not_isTree_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    ¬ IsTree (cyclePendant (m + 3) ks) :=
  not_isTree_of_V_le_E (by rw [V_cyclePendant, E_cyclePendant m ks h])

@[simp] theorem not_isTree_lollipop (m k : ℕ) : ¬ IsTree (lollipop (m + 3) k) :=
  not_isTree_of_not_isAcyclic (not_isAcyclic_lollipop m k)

/-- The tadpole is triangle-free once its cycle has four or more vertices, so its shortest cycle
has length at least four. -/
theorem four_le_girth_tadpole (m k : ℕ) : 4 ≤ (tadpole (m + 4) k).girth :=
  four_le_girth_of_cliqueNum (cliqueNum_tadpole m k).le (not_isAcyclic_tadpole (m + 1) k)

/-! ### Clique covers of the tree-and-cycle families

`|V| ≤ κ · ω`, since every clique in a cover has at most `ω` vertices.  For a triangle-free
graph this is `κ ≥ ⌈|V| / 2⌉`, which is the first entry in the clique-cover cell for the spider
and the tadpole; the lollipop's clique makes its bound weaker but still non-trivial.
-/

theorem le_cliqueCoverNum_spider (legs : List ℕ) (h : 0 < legs.sum) :
    (2 + legs.sum) / 2 ≤ (spider legs).cliqueCoverNum := by
  have h1 := le_cliqueCoverNum_of_cliqueNum_le_two (cliqueNum_spider legs h).le
  rw [V_spider] at h1
  omega

theorem le_cliqueCoverNum_tadpole (m k : ℕ) :
    (m + k + 5) / 2 ≤ (tadpole (m + 4) k).cliqueCoverNum := by
  have h1 := le_cliqueCoverNum_of_cliqueNum_le_two (cliqueNum_tadpole m k).le
  rw [V_tadpole] at h1
  omega

theorem le_cliqueCoverNum_lollipop (m k : ℕ) :
    m + k + 2 ≤ (lollipop (m + 2) k).cliqueCoverNum * (m + 2) := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum (lollipop (m + 2) k)
  rw [cliqueNum_lollipop, V_lollipop] at h
  omega

/-! ### Automorphisms of the graphs built by joining

`|Aut G| · |Aut H| ≤ |Aut (G ∇g H)|`, because an automorphism of each side extends to the join
by acting on the two sides independently.  Every cone-shaped family in the library is a join
with `complete 1` or `complete 2`, so this single bound opens the automorphism cell for the
star, the wheel, the book, the fan and the friendship windmill — the graphs that are *not*
vertex-transitive and so are out of reach of `V_le_autCount_of_isVertexTransitive`.
-/

theorem factorial_mul_factorial_le_autCount_bipartite (m n : ℕ) :
    m.factorial * n.factorial ≤ (bipartite m n).autCount := by
  have h := autCount_mul_le_autCount_join (empty m) (empty n)
  rwa [← bipartite_eq_join, autCount_empty, autCount_empty] at h

/-- The star's rays may be permuted arbitrarily. -/
theorem factorial_le_autCount_star (n : ℕ) : n.factorial ≤ (star n).autCount := by
  have h := factorial_mul_factorial_le_autCount_bipartite 1 n
  rw [← star_eq_bipartite] at h
  simpa using h

/-- The wheel inherits the dihedral symmetry of its rim. -/
theorem le_autCount_wheel (n : ℕ) : 2 * (n + 3) ≤ (wheel (n + 3)).autCount := by
  have h := autCount_mul_le_autCount_join (complete 1) (cycle (n + 3))
  rw [← wheel_eq_join, autCount_complete, Nat.factorial_one, Nat.one_mul] at h
  have h2 := two_mul_le_autCount_cycle n
  omega

/-- **The wheel `Wₙ` has exactly `2n` automorphisms** once the rim has length at least four: the
hub is the only vertex adjacent to all the others, so it is fixed, and the wheel inherits the
dihedral symmetry of its rim and nothing more.  `wheel 3 = K₄` is the exception, with `24`. -/
theorem autCount_wheel (n : ℕ) : (wheel (n + 4)).autCount = 2 * (n + 4) := by
  have hle : (wheel (n + 4)).autCount ≤ 2 * (n + 4) := by
    rw [wheel_def, autCount_mk]
    exact CGraph.autCount_wheel_le (by omega)
  have hge : 2 * (n + 4) ≤ (wheel (n + 4)).autCount := le_autCount_wheel (n + 1)
  omega

/-- The book's pages may be permuted arbitrarily, and its spine may be flipped. -/
theorem two_mul_factorial_le_autCount_book (n : ℕ) :
    2 * n.factorial ≤ (book n).autCount := by
  have h := autCount_mul_le_autCount_join (complete 2) (empty n)
  rwa [← book_eq_join, autCount_complete, autCount_empty,
    show Nat.factorial 2 = 2 from rfl] at h

/-- The fan is a cone over a path, so it is at least as symmetric as the path. -/
theorem autCount_path_le_autCount_fan (n : ℕ) : (path n).autCount ≤ (fan n).autCount := by
  have h := autCount_mul_le_autCount_join (complete 1) (path n)
  rwa [← fan_eq_join, autCount_complete, Nat.factorial_one, Nat.one_mul] at h

/-- The windmill is a cone over a perfect matching, whose automorphism group is the one of the
cocktail-party graph it complements. -/
theorem le_autCount_friendship (n : ℕ) : 2 * (n + 1) ≤ (friendship (n + 1)).autCount := by
  have h := autCount_mul_le_autCount_join (complete 1) ((cocktailParty (n + 1))ᶜ)
  rw [← friendship_eq_join_compl_cocktailParty, autCount_complete, Nat.factorial_one,
    Nat.one_mul, autCount_compl] at h
  have h2 := le_autCount_cocktailParty n
  omega

/-! ### The Grötzsch graph's independence number, bracketed

The eleven vertices of the Grötzsch graph split into the five shadows, the five rim vertices and
the apex.  The shadows are pairwise non-adjacent, so `α ≥ 5`; and a clique cover of a
triangle-free graph is an independent set's worth of cliques, so `α ≤ θ = 6`.  The complementary
bracket for the vertex cover follows from `τ + α = |V|`.
-/

theorem five_le_indepNum_grotzsch : 5 ≤ grotzsch.indepNum := by
  have h := V_le_indepNum_mycielskian (cycle 5)
  rwa [V_cycle] at h

theorem indepNum_grotzsch_le : grotzsch.indepNum ≤ 6 := by
  have h := indepNum_le_cliqueCoverNum grotzsch
  rwa [cliqueCoverNum_grotzsch] at h

theorem five_le_coverNum_grotzsch : 5 ≤ grotzsch.coverNum := by
  have h := coverNum_add_indepNum grotzsch
  have h2 := indepNum_grotzsch_le
  rw [V_grotzsch] at h
  omega

theorem coverNum_grotzsch_le : grotzsch.coverNum ≤ 6 := by
  have h := coverNum_add_indepNum grotzsch
  have h2 := five_le_indepNum_grotzsch
  rw [V_grotzsch] at h
  omega

/-- **The independence number of the Grötzsch graph is five.**  The shadows realise it, and that
no six vertices are independent is a finite check over the `2¹¹` subsets. -/
theorem indepNum_grotzsch : grotzsch.indepNum = 5 := by
  rw [show grotzsch = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk, indepNum_mk]
  exact CGraph.indepNum_mycielskian_cycle_five

/-- **The vertex cover number of the Grötzsch graph is six**, by Gallai's identity. -/
theorem coverNum_grotzsch : grotzsch.coverNum = 6 := by
  have h := coverNum_add_indepNum grotzsch
  rw [V_grotzsch, indepNum_grotzsch] at h
  omega

/-! ### The line graph's matching, covering and dominating numbers

An independent set of `L(G)` is a matching of `G`, so the three general inequalities relating
independence, clique covers and domination transfer verbatim to the line graph.
-/

theorem matchNum_le_cliqueCoverNum_lineGraph (G : IsoGraph) :
    G.matchNum ≤ (lineGraph G).cliqueCoverNum := by
  have h := indepNum_le_cliqueCoverNum (lineGraph G)
  rwa [indepNum_lineGraph] at h

theorem two_mul_matchNum_lineGraph_le_E (G : IsoGraph) :
    2 * (lineGraph G).matchNum ≤ G.E := by
  have h := two_mul_matchNum_le_V (lineGraph G)
  rwa [V_lineGraph] at h

/-- Each vertex of `L(G)` dominates at most `2Δ - 1` vertices including itself. -/
theorem E_le_domNum_lineGraph_mul (G : IsoGraph) (hd : 1 ≤ G.maxDeg) :
    G.E ≤ (lineGraph G).domNum * (2 * G.maxDeg) := by
  have h := V_le_domNum_mul_maxDeg_add_one (lineGraph G)
  have h2 := maxDeg_lineGraph_le G
  rw [V_lineGraph] at h
  exact h.trans (Nat.mul_le_mul_left _ (by omega))

/-! ### Circulants: domination, colouring and clique covers

A circulant is regular, so once its degree is pinned down by an edge count the general
`|V| ≤ γ(Δ + 1)`, `γ + Δ ≤ |V|` and `χ ≤ Δ + 1` bounds specialise to it.
-/

theorem le_domNum_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : n ≤ (circulant n S).domNum * (k + 1) := by
  have h := V_le_domNum_mul_maxDeg_add_one (circulant n S)
  rwa [V_circulant, maxDeg_circulant hn hk] at h

theorem domNum_circulant_le {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : (circulant n S).domNum + k ≤ n := by
  have h := domNum_add_maxDeg_le_V (circulant n S)
  rwa [V_circulant, maxDeg_circulant hn hk] at h

theorem chromNum_circulant_le {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : (circulant n S).chromNum ≤ k + 1 := by
  have h := chromNum_le_maxDeg_add_one (circulant n S)
  rwa [maxDeg_circulant hn hk] at h

theorem le_cliqueCoverNum_mul_cliqueNum_circulant (n : ℕ) (S : List ℕ) :
    n ≤ (circulant n S).cliqueCoverNum * (circulant n S).cliqueNum := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum (circulant n S)
  rwa [V_circulant] at h

theorem two_mul_matchNum_le_circulant (n : ℕ) (S : List ℕ) :
    2 * (circulant n S).matchNum ≤ n := by
  have h := two_mul_matchNum_le_V (circulant n S)
  rwa [V_circulant] at h

/-! ### Eccentricity from domination

`r = 1` exactly when a single vertex dominates the graph, so the domination lower bounds proved
for the tadpole and the lollipop immediately force a radius — and hence a diameter — of at least
two.  These are the first entries in the distance cells of those two families.
-/

theorem two_le_radius_tadpole (m k : ℕ) : 2 ≤ (tadpole (m + 4) (k + 1)).radius := by
  have hV : 1 < (tadpole (m + 4) (k + 1)).V := by rw [V_tadpole]; omega
  have hc : IsConnected (tadpole (m + 4) (k + 1)) := isConnected_tadpole (m + 1) (k + 1)
  have hpos := radius_pos hc hV
  have h : m + 1 + k + 4 ≤ 4 * (tadpole (m + 4) (k + 1)).domNum := le_domNum_tadpole (m + 1) k
  have hne : (tadpole (m + 4) (k + 1)).domNum ≠ 1 := by intro he; rw [he] at h; omega
  have h1 : (tadpole (m + 4) (k + 1)).radius ≠ 1 := fun he ↦
    hne ((radius_eq_one_iff_domNum_eq_one hV).1 he)
  omega

theorem two_le_diameter_tadpole (m k : ℕ) : 2 ≤ (tadpole (m + 4) (k + 1)).diameter :=
  le_trans (two_le_radius_tadpole m k) (radius_le_diameter _)

theorem two_le_radius_lollipop (m k : ℕ) : 2 ≤ (lollipop (m + 2) (k + 2)).radius := by
  have hV : 1 < (lollipop (m + 2) (k + 2)).V := by rw [V_lollipop]; omega
  have hc : IsConnected (lollipop (m + 2) (k + 2)) := isConnected_lollipop (m + 1) (k + 2)
  have hpos := radius_pos hc hV
  have h : m + (k + 1) + 3 ≤ (lollipop (m + 2) (k + 2)).domNum * (m + 3) :=
    le_domNum_lollipop m (k + 1)
  have hne : (lollipop (m + 2) (k + 2)).domNum ≠ 1 := by
    intro he; rw [he, Nat.one_mul] at h; omega
  have h1 : (lollipop (m + 2) (k + 2)).radius ≠ 1 := fun he ↦
    hne ((radius_eq_one_iff_domNum_eq_one hV).1 he)
  omega

theorem two_le_diameter_lollipop (m k : ℕ) : 2 ≤ (lollipop (m + 2) (k + 2)).diameter :=
  le_trans (two_le_radius_lollipop m k) (radius_le_diameter _)

/-- A theta graph with two or more internally disjoint paths has more edges than vertices. -/
theorem not_isTree_thetaGraph (xs : List ℕ) (h : ∀ k ∈ xs, 0 < k) (hl : 2 ≤ xs.length) :
    ¬ IsTree (thetaGraph xs) :=
  not_isTree_of_V_le_E (by rw [V_thetaGraph, E_thetaGraph xs h]; omega)

/-! ### Automorphisms of a complete multipartite graph, part by part

`completeMultipartite_cons` peels one part off the front as a join, so the join bound on
automorphism counts turns into a recursion: each part of size `d` contributes a factor of `d!`.
Applied to a balanced Turán graph it recovers the vertex count, which is the bound the transitive
route already gives, but the recursion itself is what the unbalanced parts will need.
-/

theorem factorial_mul_autCount_le_autCount_completeMultipartite_cons (d : ℕ) (ds : List ℕ) :
    d.factorial * (completeMultipartite ds).autCount
      ≤ (completeMultipartite (d :: ds)).autCount := by
  rw [completeMultipartite_cons]
  have h := autCount_mul_le_autCount_join (empty d) (completeMultipartite ds)
  rwa [autCount_empty] at h

theorem le_autCount_turan (m d : ℕ) :
    (m + 1) * (d + 1) ≤ (turan ((m + 1) * (d + 1)) (m + 1)).autCount := by
  have hdvd : (m + 1) ∣ (m + 1) * (d + 1) := Dvd.intro _ rfl
  rw [turan_of_dvd hdvd, Nat.mul_div_cancel_left _ (Nat.succ_pos m)]
  exact le_autCount_completeMultipartite_replicate m d

/-! ### More edge chromatic brackets

`Δ ≤ χ' ≤ 2Δ - 1` again, now for the families whose maximum degree was known but whose edge
colouring cell was still empty.
-/

theorem le_edgeChromNum_tadpole (m k : ℕ) : 3 ≤ (tadpole (m + 3) (k + 1)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (tadpole (m + 3) (k + 1))
  rwa [maxDeg_tadpole] at h

theorem edgeChromNum_tadpole_le (m k : ℕ) : (tadpole (m + 3) (k + 1)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (tadpole (m + 3) (k + 1))
  rwa [maxDeg_tadpole] at h

theorem le_edgeChromNum_lollipop (m k : ℕ) :
    m + 2 ≤ (lollipop (m + 2) (k + 1)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (lollipop (m + 2) (k + 1))
  rwa [maxDeg_lollipop] at h

theorem edgeChromNum_lollipop_le (m k : ℕ) :
    (lollipop (m + 2) (k + 1)).edgeChromNum ≤ 2 * m + 3 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (lollipop (m + 2) (k + 1))
  rw [maxDeg_lollipop] at h
  omega

theorem edgeChromNum_doubleStar_le (m n : ℕ) :
    (doubleStar m n).edgeChromNum ≤ 2 * max m n + 1 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (doubleStar m n)
  rw [maxDeg_doubleStar] at h
  omega

theorem le_edgeChromNum_triangular (n : ℕ) : 2 * n ≤ (triangular (n + 2)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (triangular (n + 2))
  rwa [maxDeg_triangular] at h

theorem le_edgeChromNum_johnson {n k : ℕ} (hk : k ≤ n) :
    k * (n - k) ≤ (johnson n k).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (johnson n k)
  rwa [maxDeg_johnson hk] at h

theorem le_edgeChromNum_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (q - 1) / 2 ≤ (paley q).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (paley q)
  rwa [maxDeg_paley q hq] at h

/-! ### Clique covers from the clique number

`|V| ≤ θ ω` once more, for the three families whose clique number is exactly known but whose
clique-cover cell was empty.
-/

theorem le_cliqueCoverNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    n ≤ (turan n r).cliqueCoverNum * r := by
  have h1 := V_le_cliqueCoverNum_mul_cliqueNum (turan n r)
  rwa [V_turan, cliqueNum_turan hr h] at h1

theorem le_cliqueCoverNum_crown (n : ℕ) : n + 2 ≤ (crown (n + 2)).cliqueCoverNum := by
  have h := le_cliqueCoverNum_of_cliqueNum_le_two (cliqueNum_crown n).le
  rw [V_crown] at h
  omega

theorem le_cliqueCoverNum_johnson_two (n : ℕ) :
    (n + 4).choose 2 ≤ (johnson (n + 4) 2).cliqueCoverNum * (n + 3) := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum (johnson (n + 4) 2)
  rwa [V_johnson, cliqueNum_johnson_two] at h

theorem le_cliqueCoverNum_triangular_of_choose (n : ℕ) :
    (n + 4).choose 2 ≤ (triangular (n + 4)).cliqueCoverNum * (n + 3) := by
  have h := V_le_cliqueCoverNum_mul_cliqueNum (triangular (n + 4))
  rwa [V_triangular, cliqueNum_triangular] at h

/-! ### Domination in the Paley graph

The Paley graph is `(q - 1)/2`-regular, so a dominating set covers at most `(q + 1)/2` vertices
per element.
-/

theorem le_domNum_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    q ≤ (paley q).domNum * ((q - 1) / 2 + 1) := by
  have h := V_le_domNum_mul_maxDeg_add_one (paley q)
  rwa [V_paley, maxDeg_paley q hq] at h

theorem domNum_paley_le (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).domNum + (q - 1) / 2 ≤ q := by
  have h := domNum_add_maxDeg_le_V (paley q)
  rwa [V_paley, maxDeg_paley q hq] at h

/-- A cycle with pendant paths attached contains a cycle, so its girth is at least three. -/
theorem three_le_girth_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    3 ≤ (cyclePendant (m + 3) ks).girth :=
  three_le_girth (not_isAcyclic_cyclePendant m ks h)

/-! ### Matchings from independence, and matchings from edge colourings

Two routes into the matching-number cells that were still empty.  Where the independence number
is known exactly, `ν ≤ τ = |V| - α ≤ 2ν` brackets the matching number between a half and a whole
of the vertex cover.  Where it is not, `|E| ≤ χ' ν` converts an edge-colouring upper bound into a
matching lower bound: a proper edge colouring splits the edges into `χ'` matchings, so one of
them has at least `|E| / χ'` edges.
-/

theorem matchNum_triangular_le (n : ℕ) : (triangular n).matchNum ≤ n.choose 2 - n / 2 := by
  have h1 := matchNum_le_coverNum (triangular n)
  have h2 := coverNum_add_indepNum (triangular n)
  rw [V_triangular, indepNum_triangular] at h2
  omega

theorem le_matchNum_triangular (n : ℕ) :
    n.choose 2 - n / 2 ≤ 2 * (triangular n).matchNum := by
  have h1 := coverNum_le_two_mul_matchNum (triangular n)
  have h2 := coverNum_add_indepNum (triangular n)
  rw [V_triangular, indepNum_triangular] at h2
  omega

theorem matchNum_johnson_two_le (n : ℕ) : (johnson n 2).matchNum ≤ n.choose 2 - n / 2 := by
  have h1 := matchNum_le_coverNum (johnson n 2)
  have h2 := coverNum_add_indepNum (johnson n 2)
  rw [V_johnson, indepNum_johnson_two] at h2
  omega

theorem le_matchNum_johnson_two (n : ℕ) :
    n.choose 2 - n / 2 ≤ 2 * (johnson n 2).matchNum := by
  have h1 := coverNum_le_two_mul_matchNum (johnson n 2)
  have h2 := coverNum_add_indepNum (johnson n 2)
  rw [V_johnson, indepNum_johnson_two] at h2
  omega

theorem matchNum_kneser_two_le (n : ℕ) :
    (kneser (n + 4) 2).matchNum ≤ (n + 4).choose 2 - (n + 3) := by
  have h1 := matchNum_le_coverNum (kneser (n + 4) 2)
  have h2 := coverNum_add_indepNum (kneser (n + 4) 2)
  rw [V_kneser, indepNum_kneser_two] at h2
  omega

theorem le_matchNum_kneser_two (n : ℕ) :
    (n + 4).choose 2 - (n + 3) ≤ 2 * (kneser (n + 4) 2).matchNum := by
  have h1 := coverNum_le_two_mul_matchNum (kneser (n + 4) 2)
  have h2 := coverNum_add_indepNum (kneser (n + 4) 2)
  rw [V_kneser, indepNum_kneser_two] at h2
  omega

/-- The tadpole has `Δ = 3`, so `χ' ≤ 5` and one of the five colour classes is large. -/
theorem le_matchNum_tadpole (m k : ℕ) :
    m + k + 4 ≤ 5 * (tadpole (m + 3) (k + 1)).matchNum := by
  have h1 := E_le_edgeChromNum_mul_matchNum (tadpole (m + 3) (k + 1))
  have h2 := edgeChromNum_tadpole_le m k
  rw [E_tadpole] at h1
  calc m + k + 4 = m + 3 + (k + 1) := by ring
    _ ≤ (tadpole (m + 3) (k + 1)).edgeChromNum * (tadpole (m + 3) (k + 1)).matchNum := h1
    _ ≤ 5 * (tadpole (m + 3) (k + 1)).matchNum := Nat.mul_le_mul_right _ h2

theorem le_matchNum_lollipop (m k : ℕ) :
    (m + 2).choose 2 + (k + 1) ≤ (2 * m + 3) * (lollipop (m + 2) (k + 1)).matchNum := by
  have h1 := E_le_edgeChromNum_mul_matchNum (lollipop (m + 2) (k + 1))
  have h2 := edgeChromNum_lollipop_le m k
  rw [E_lollipop] at h1
  exact h1.trans (Nat.mul_le_mul_right _ h2)

/-- The lollipop's vertex cover, from the chromatic bound on its independence number. -/
theorem coverNum_lollipop_le (m k : ℕ) :
    (m + 2) * (lollipop (m + 2) k).coverNum ≤ (m + 1) * (m + k + 2) := by
  have h1 := coverNum_add_indepNum (lollipop (m + 2) k)
  have h2 := le_indepNum_lollipop m k
  rw [V_lollipop] at h1
  have h5 : (m + 2) * (lollipop (m + 2) k).coverNum + (m + 2) * (lollipop (m + 2) k).indepNum
      = (m + 1) * (m + k + 2) + (m + k + 2) := by
    rw [← Nat.mul_add, h1]; ring
  omega

/-! ### The last of the domination brackets

`|V| ≤ γ(Δ + 1)` and `γ + Δ ≤ |V|` for the remaining families whose maximum degree is known.  The
hypercube bound is the classical sphere-covering bound for binary codes of radius one.
-/

theorem le_domNum_hypercube (n : ℕ) : 2 ^ n ≤ (hypercube n).domNum * (n + 1) := by
  have h := V_le_domNum_mul_maxDeg_add_one (hypercube n)
  rwa [V_hypercube, maxDeg_hypercube] at h

theorem domNum_hypercube_le (n : ℕ) : (hypercube n).domNum + n ≤ 2 ^ n := by
  have h := domNum_add_maxDeg_le_V (hypercube n)
  rwa [V_hypercube, maxDeg_hypercube] at h

theorem le_domNum_kneser {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n.choose k ≤ (kneser n k).domNum * ((n - k).choose k + 1) := by
  have h := V_le_domNum_mul_maxDeg_add_one (kneser n k)
  rwa [V_kneser, maxDeg_kneser n k hk hkn] at h

theorem domNum_kneser_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (kneser n k).domNum + (n - k).choose k ≤ n.choose k := by
  have h := domNum_add_maxDeg_le_V (kneser n k)
  rwa [V_kneser, maxDeg_kneser n k hk hkn] at h

theorem le_domNum_johnson {n k : ℕ} (hk : k ≤ n) :
    n.choose k ≤ (johnson n k).domNum * (k * (n - k) + 1) := by
  have h := V_le_domNum_mul_maxDeg_add_one (johnson n k)
  rwa [V_johnson, maxDeg_johnson hk] at h

theorem domNum_johnson_le {n k : ℕ} (hk : k ≤ n) :
    (johnson n k).domNum + k * (n - k) ≤ n.choose k := by
  have h := domNum_add_maxDeg_le_V (johnson n k)
  rwa [V_johnson, maxDeg_johnson hk] at h

theorem le_domNum_ladder (n : ℕ) : n + 3 ≤ 2 * (ladder (n + 3)).domNum := by
  have h := V_le_domNum_mul_maxDeg_add_one (ladder (n + 3))
  rw [V_ladder, maxDeg_ladder] at h
  omega

theorem domNum_ladder_le (n : ℕ) : (ladder (n + 3)).domNum + 3 ≤ 2 * (n + 3) := by
  have h := domNum_add_maxDeg_le_V (ladder (n + 3))
  rw [V_ladder, maxDeg_ladder] at h
  omega

/-- The ladder is `Pₙ □ K₂`, so it is at least twice as symmetric as the path. -/
theorem two_mul_autCount_path_le_autCount_ladder (n : ℕ) :
    2 * (path (n + 1)).autCount ≤ (ladder (n + 1)).autCount := by
  have h := autCount_mul_le_autCount_cartesianProduct (path (n + 1)) (complete 2)
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [show ladder (n + 1) = path (n + 1) □g complete 2 from rfl]
  rw [autCount_complete, show Nat.factorial 2 = 2 from rfl] at h
  omega

/-- The line graph of a `k`-regular graph is `(2k - 2)`-regular, so its edge chromatic number is
bracketed by the usual sandwich. -/
theorem le_edgeChromNum_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    2 * k - 2 ≤ (lineGraph G).edgeChromNum := by
  have h1 := maxDeg_le_edgeChromNum (lineGraph G)
  rwa [maxDeg_lineGraph hE h] at h1

theorem edgeChromNum_lineGraph_le {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    (lineGraph G).edgeChromNum ≤ 2 * (2 * k - 2) - 1 := by
  have h1 := edgeChromNum_le_two_mul_maxDeg_sub_one (lineGraph G)
  rwa [maxDeg_lineGraph hE h] at h1

/-! ### Counting triangles in the triangle-free families

`cliqueCount G 3` is the number of triangles.  It vanishes exactly when the girth is not three,
and in particular whenever the graph is bipartite or its clique number is at most two — two
conditions the library already knows for most of its families.
-/

@[simp] theorem cliqueCount_path (n : ℕ) : (path n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_path n)

@[simp] theorem cliqueCount_ladder (n : ℕ) : (ladder n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_ladder n)

@[simp] theorem cliqueCount_spider (legs : List ℕ) : (spider legs).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_spider legs)

@[simp] theorem cliqueCount_doubleStar (m n : ℕ) : (doubleStar m n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_doubleStar m n)

@[simp] theorem cliqueCount_crown (n : ℕ) : (crown n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_crown n)

@[simp] theorem cliqueCount_turan_two (n : ℕ) : (turan n 2).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_turan_two n)

theorem cliqueCount_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t) :
    (cyclePendant (2 * t) ks).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_cyclePendant_even t ks h)

theorem cliqueCount_thetaGraph_even {xs : List ℕ} (h : ∀ k ∈ xs, k % 2 = 0) :
    (thetaGraph xs).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_thetaGraph_even h)

theorem cliqueCount_thetaGraph_odd {xs : List ℕ} (h : ∀ k ∈ xs, k % 2 = 1) :
    (thetaGraph xs).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_thetaGraph_odd h)

theorem cliqueCount_circulant {n : ℕ} {S : List ℕ} (hn : n % 2 = 0) (hS : ∀ d ∈ S, d % 2 = 1) :
    (circulant n S).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_circulant hn hS)

@[simp] theorem cliqueCount_tadpole (m k : ℕ) : (tadpole (m + 4) k).cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_tadpole]; omega)

@[simp] theorem cliqueCount_grotzsch : grotzsch.cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_grotzsch]; omega)

/-- The Mycielskian of a triangle-free graph is triangle-free: that is the whole point of the
construction. -/
theorem cliqueCount_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : G.cliqueNum ≤ 2) :
    (mycielskian G).cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_mycielskian_eq_two hV h]; omega)

/-! ### Graphs that are not self-complementary, by bipartiteness

A self-complementary graph on five or more vertices needs at least three colours, so it is never
bipartite.  That refutes self-complementarity for every bipartite family in the library once it
is large enough — the exceptions `path 4` and `empty 1` below the threshold are exactly the two
small self-complementary bipartite graphs.
-/

theorem not_isSelfComplementary_of_isBipartite {G : IsoGraph} (hb : IsBipartite G)
    (hV : 5 ≤ G.V) : ¬ IsSelfComplementary G :=
  fun h ↦ h.not_isBipartite hV hb

@[simp] theorem not_isSelfComplementary_path (n : ℕ) :
    ¬ IsSelfComplementary (path (n + 5)) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_path _) (by rw [V_path]; omega)

@[simp] theorem not_isSelfComplementary_star (n : ℕ) :
    ¬ IsSelfComplementary (star (n + 5)) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_star _)
    (by rw [star_eq_bipartite, V_bipartite]; omega)

@[simp] theorem not_isSelfComplementary_ladder (n : ℕ) :
    ¬ IsSelfComplementary (ladder (n + 3)) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_ladder _) (by rw [V_ladder]; omega)

@[simp] theorem not_isSelfComplementary_crown (n : ℕ) :
    ¬ IsSelfComplementary (crown (n + 3)) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_crown _) (by rw [V_crown]; omega)

@[simp] theorem not_isSelfComplementary_doubleStar (m n : ℕ) :
    ¬ IsSelfComplementary (doubleStar (m + 3) n) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_doubleStar _ _)
    (by rw [V_doubleStar]; omega)

theorem not_isSelfComplementary_spider (legs : List ℕ) (h : 4 ≤ legs.sum) :
    ¬ IsSelfComplementary (spider legs) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_spider legs) (by rw [V_spider]; omega)

theorem not_isSelfComplementary_cycle_even (m : ℕ) :
    ¬ IsSelfComplementary (cycle (2 * (m + 3))) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_cycle_even _) (by rw [V_cycle]; omega)

theorem not_isSelfComplementary_tadpole_even (m k : ℕ) :
    ¬ IsSelfComplementary (tadpole (2 * (m + 3)) k) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_tadpole_even _ _)
    (by rw [V_tadpole]; omega)

/-! ### More graphs that are not self-complementary

Beyond bipartiteness there are three cheap obstructions: the vertex count must be `0` or `1`
mod `4`, the clique and independence numbers must agree, and the graph must be connected.  Each
one is a one-line consequence of a lemma already in the file, and between them they refute
self-complementarity for almost every remaining family.
-/

theorem not_isSelfComplementary_of_V_mod_four {G : IsoGraph} (h : G.V % 4 = 2 ∨ G.V % 4 = 3) :
    ¬ IsSelfComplementary G := by
  intro hs
  rcases hs.V_mod_four with h' | h' <;> omega

theorem not_isSelfComplementary_of_cliqueNum_ne_indepNum {G : IsoGraph}
    (h : G.cliqueNum ≠ G.indepNum) : ¬ IsSelfComplementary G :=
  fun hs ↦ h hs.cliqueNum_eq_indepNum

theorem not_isSelfComplementary_of_not_isConnected {G : IsoGraph} (hV : 2 ≤ G.V)
    (h : ¬ IsConnected G) : ¬ IsSelfComplementary G :=
  fun hs ↦ h (hs.isConnected hV)

theorem not_isSelfComplementary_of_two_mul_E_ne {G : IsoGraph} (h : 2 * G.E ≠ G.V.choose 2) :
    ¬ IsSelfComplementary G :=
  fun hs ↦ h hs.two_mul_E

theorem not_isSelfComplementary_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ IsSelfComplementary (G ⊕g H) :=
  not_isSelfComplementary_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

@[simp] theorem not_isSelfComplementary_grotzsch : ¬ IsSelfComplementary grotzsch :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_grotzsch]; omega)

theorem not_isSelfComplementary_cycle_three_mod_four (m : ℕ) :
    ¬ IsSelfComplementary (cycle (4 * m + 3)) :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_cycle]; omega)

theorem not_isSelfComplementary_prism_odd (m : ℕ) :
    ¬ IsSelfComplementary (prism (2 * m + 1)) :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_prism]; omega)

theorem not_isSelfComplementary_prism_even (m : ℕ) :
    ¬ IsSelfComplementary (prism (2 * (m + 2))) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_prism_even _) (by rw [V_prism]; omega)

theorem not_isSelfComplementary_friendship_odd (m : ℕ) :
    ¬ IsSelfComplementary (friendship (2 * m + 1)) :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_friendship]; omega)

theorem not_isSelfComplementary_friendship (n : ℕ) :
    ¬ IsSelfComplementary (friendship (n + 4)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_friendship, indepNum_friendship]; omega)

theorem not_isSelfComplementary_cocktailParty (n : ℕ) :
    ¬ IsSelfComplementary (cocktailParty (n + 3)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_cocktailParty, indepNum_cocktailParty]; omega)

theorem not_isSelfComplementary_book (n : ℕ) : ¬ IsSelfComplementary (book (n + 4)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_book, indepNum_book]; omega)

theorem not_isSelfComplementary_wheel (n : ℕ) : ¬ IsSelfComplementary (wheel (n + 8)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_wheel, indepNum_wheel]; omega)

theorem not_isSelfComplementary_fan (n : ℕ) : ¬ IsSelfComplementary (fan (n + 8)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_fan, indepNum_fan]; omega)

theorem not_isSelfComplementary_triangular (n : ℕ) :
    ¬ IsSelfComplementary (triangular (n + 4)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_triangular, indepNum_triangular]; omega)

theorem not_isSelfComplementary_johnson_two (n : ℕ) :
    ¬ IsSelfComplementary (johnson (n + 4) 2) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_johnson_two, indepNum_johnson_two]; omega)

theorem not_isSelfComplementary_kneser_two (n : ℕ) :
    ¬ IsSelfComplementary (kneser (n + 4) 2) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_kneser_two, indepNum_kneser_two]; omega)

theorem not_isSelfComplementary_rook (m n : ℕ) (h : m ≠ n) :
    ¬ IsSelfComplementary (rook (m + 1) (n + 1)) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    rw [cliqueNum_rook (by omega) (by omega), indepNum_rook]; omega)

/-- The Mycielskian of a triangle-free graph on at least three vertices has clique number two
but independence number at least three. -/
theorem not_isSelfComplementary_mycielskian {G : IsoGraph} (hV : 3 ≤ G.V)
    (h : G.cliqueNum ≤ 2) : ¬ IsSelfComplementary (mycielskian G) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    have h1 := V_le_indepNum_mycielskian G
    rw [cliqueNum_mycielskian_eq_two (by omega) h]
    omega)

/-! ### The two-path theta graph and the two-legged spider

`thetaGraph [a, b]` is a cycle and `spider [a, b]` is a path, so every invariant of those two
families transfers verbatim: the matching, domination, covering and eccentricity entries for
both families in this degenerate case.
-/

@[simp] theorem maxDeg_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    maxDeg (thetaGraph [a, b]) = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hc, maxDeg_cycle]

@[simp] theorem minDeg_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    minDeg (thetaGraph [a, b]) = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hc, minDeg_cycle]

@[simp] theorem domNum_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    (thetaGraph [a, b]).domNum = (a + b + 4) / 3 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hc, domNum_cycle]
  omega

@[simp] theorem matchNum_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    (thetaGraph [a, b]).matchNum = (a + b + 2) / 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hc, matchNum_cycle]
  omega

@[simp] theorem coverNum_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    (thetaGraph [a, b]).coverNum = (a + b + 3) / 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hc, coverNum_cycle]
  omega

@[simp] theorem radius_thetaGraph_pair (a b : ℕ) :
    (thetaGraph [a, b]).radius = (a + b + 2) / 2 := by
  rw [thetaGraph_pair, show 2 + a + b = 1 + a + b + 1 from by ring, radius_cycle]
  omega

@[simp] theorem diameter_thetaGraph_pair (a b : ℕ) :
    (thetaGraph [a, b]).diameter = (a + b + 2) / 2 := by
  rw [thetaGraph_pair, show 2 + a + b = 1 + a + b + 1 from by ring, diameter_cycle]
  omega

@[simp] theorem isConnected_thetaGraph_pair (a b : ℕ) : IsConnected (thetaGraph [a, b]) := by
  rw [thetaGraph_pair, show 2 + a + b = 1 + a + b + 1 from by ring]
  exact isConnected_cycle _

@[simp] theorem numComponents_thetaGraph_pair (a b : ℕ) : (thetaGraph [a, b]).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_thetaGraph_pair a b)

@[simp] theorem matchNum_spider_pair (a b : ℕ) : (spider [a, b]).matchNum = (a + b + 1) / 2 := by
  rw [spider_pair, matchNum_path]
  omega

@[simp] theorem coverNum_spider_pair (a b : ℕ) : (spider [a, b]).coverNum = (a + b + 1) / 2 := by
  rw [spider_pair, coverNum_path]
  omega

@[simp] theorem cliqueCoverNum_spider_pair (a b : ℕ) :
    (spider [a, b]).cliqueCoverNum = (a + b + 2) / 2 := by
  rw [spider_pair, cliqueCoverNum_path]
  omega

@[simp] theorem domNum_spider_pair (a b : ℕ) : (spider [a, b]).domNum = (a + b + 3) / 3 := by
  rw [spider_pair, show 1 + a + b = a + b + 1 from by ring, domNum_path]

@[simp] theorem radius_spider_pair (a b : ℕ) : (spider [a, b]).radius = (a + b + 1) / 2 := by
  rw [spider_pair, show 1 + a + b = a + b + 1 from by ring, radius_path]

@[simp] theorem diameter_spider_pair (a b : ℕ) : (spider [a, b]).diameter = a + b := by
  rw [spider_pair, show 1 + a + b = a + b + 1 from by ring, diameter_path]

@[simp] theorem maxDeg_spider_pair (a b : ℕ) (h : 2 ≤ a + b) : maxDeg (spider [a, b]) = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 1 + a + b = c + 3 := ⟨a + b - 2, by omega⟩
  rw [spider_pair, hc, maxDeg_path]

@[simp] theorem minDeg_spider_pair (a b : ℕ) (h : 1 ≤ a + b) : minDeg (spider [a, b]) = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, 1 + a + b = c + 2 := ⟨a + b - 1, by omega⟩
  rw [spider_pair, hc, minDeg_path]

@[simp] theorem edgeChromNum_spider_pair (a b : ℕ) (h : 2 ≤ a + b) :
    (spider [a, b]).edgeChromNum = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 1 + a + b = c + 3 := ⟨a + b - 2, by omega⟩
  rw [spider_pair, hc, edgeChromNum_path]

/-! ### A cycle with one pendant vertex

`cyclePendant m [1]` is the tadpole `T(m, 1)`, which fills the first cells of the
`cyclePendant` row for the degree invariants. -/

@[simp] theorem maxDeg_cyclePendant_singleton_one (m : ℕ) :
    maxDeg (cyclePendant (m + 3) [1]) = 3 := by
  rw [cyclePendant_singleton_one, maxDeg_tadpole]

@[simp] theorem minDeg_cyclePendant_singleton_one (m : ℕ) :
    minDeg (cyclePendant (m + 3) [1]) = 1 := by
  rw [cyclePendant_singleton_one, minDeg_tadpole]

/-! ### Colouring and symmetry for the two-parameter theta graph and spider

The rest of the cycle's and the path's rows, transferred along `thetaGraph_pair` and
`spider_pair`, together with the transitivity that comes with them: a two-path theta graph is a
cycle, hence arc-transitive, while a two-legged spider is a path, hence not even vertex-transitive.
-/

@[simp] theorem cliqueNum_thetaGraph_pair (a b : ℕ) (h : 2 ≤ a + b) :
    (thetaGraph [a, b]).cliqueNum = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 4 := ⟨a + b - 2, by omega⟩
  rw [thetaGraph_pair, hc, cliqueNum_cycle]

@[simp] theorem indepNum_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    (thetaGraph [a, b]).indepNum = (a + b + 2) / 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hc, indepNum_cycle]
  omega

@[simp] theorem chromNum_thetaGraph_pair_even (a b : ℕ) (h : (a + b) % 2 = 0) :
    (thetaGraph [a, b]).chromNum = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = 2 * m + 2 := ⟨(a + b) / 2, by omega⟩
  rw [thetaGraph_pair, hm, chromNum_cycle_even]

@[simp] theorem chromNum_thetaGraph_pair_odd (a b : ℕ) (h : (a + b) % 2 = 1) :
    (thetaGraph [a, b]).chromNum = 3 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = 2 * m + 3 := ⟨(a + b - 1) / 2, by omega⟩
  rw [thetaGraph_pair, hm, chromNum_cycle_odd]

@[simp] theorem edgeChromNum_thetaGraph_pair_even (a b : ℕ) (h : (a + b) % 2 = 0) (h2 : 2 ≤ a + b) :
    (thetaGraph [a, b]).edgeChromNum = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = 2 * m + 4 := ⟨(a + b - 2) / 2, by omega⟩
  rw [thetaGraph_pair, hm, edgeChromNum_cycle_even]

@[simp] theorem edgeChromNum_thetaGraph_pair_odd (a b : ℕ) (h : (a + b) % 2 = 1) :
    (thetaGraph [a, b]).edgeChromNum = 3 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = 2 * m + 3 := ⟨(a + b - 1) / 2, by omega⟩
  rw [thetaGraph_pair, hm, edgeChromNum_cycle_odd]

@[simp] theorem cliqueNum_spider_pair (a b : ℕ) (h : 1 ≤ a + b) :
    (spider [a, b]).cliqueNum = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 1 + a + b = c + 2 := ⟨a + b - 1, by omega⟩
  rw [spider_pair, hc, cliqueNum_path]

@[simp] theorem chromNum_spider_pair (a b : ℕ) (h : 1 ≤ a + b) : (spider [a, b]).chromNum = 2 := by
  obtain ⟨c, hc⟩ : ∃ c, 1 + a + b = c + 2 := ⟨a + b - 1, by omega⟩
  rw [spider_pair, hc, chromNum_path]

@[simp] theorem indepNum_spider_pair (a b : ℕ) : (spider [a, b]).indepNum = (a + b + 2) / 2 := by
  rw [spider_pair, indepNum_path]
  omega

theorem girth_spider_pair (a b : ℕ) : (spider [a, b]).girth = 0 := by
  rw [spider_pair, girth_path]

theorem isVertexTransitive_thetaGraph_pair (a b : ℕ) :
    IsVertexTransitive (thetaGraph [a, b]) := by
  rw [thetaGraph_pair]
  exact isVertexTransitive_cycle _

theorem isArcTransitive_thetaGraph_pair (a b : ℕ) : IsArcTransitive (thetaGraph [a, b]) := by
  rw [thetaGraph_pair]
  exact isArcTransitive_cycle _

theorem two_mul_le_autCount_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) :
    2 * (a + b + 2) ≤ (thetaGraph [a, b]).autCount := by
  obtain ⟨c, hc⟩ : ∃ c, 2 + a + b = c + 3 := ⟨a + b - 1, by omega⟩
  have h2 := two_mul_le_autCount_cycle c
  rw [thetaGraph_pair, hc]
  omega

@[simp] theorem not_isVertexTransitive_spider_pair (a b : ℕ) (h : 2 ≤ a + b) :
    ¬ IsVertexTransitive (spider [a, b]) := by
  obtain ⟨c, hc⟩ : ∃ c, 1 + a + b = c + 3 := ⟨a + b - 2, by omega⟩
  rw [spider_pair, hc]
  exact not_isVertexTransitive_path c

@[simp] theorem not_isArcTransitive_spider_pair (a b : ℕ) (h : 2 ≤ a + b) :
    ¬ IsArcTransitive (spider [a, b]) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [minDeg_spider_pair a b (by omega)]; omega)
    (not_isVertexTransitive_spider_pair a b h)

theorem not_isVertexTransitive_cyclePendant_singleton_one (m : ℕ) :
    ¬ IsVertexTransitive (cyclePendant (m + 3) [1]) := by
  rw [cyclePendant_singleton_one]
  exact not_isVertexTransitive_tadpole m 0

theorem not_isArcTransitive_cyclePendant_singleton_one (m : ℕ) :
    ¬ IsArcTransitive (cyclePendant (m + 3) [1]) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [minDeg_cyclePendant_singleton_one]; omega)
    (not_isVertexTransitive_cyclePendant_singleton_one m)

theorem not_isVertexTransitive_bipartite (m n : ℕ) (h : m ≠ n) :
    ¬ IsVertexTransitive (bipartite (m + 1) (n + 1)) :=
  not_isVertexTransitive_of_minDeg_ne_maxDeg (by rw [V_bipartite]; omega)
    (by rw [minDeg_bipartite, maxDeg_bipartite]; omega)

theorem not_isArcTransitive_bipartite (m n : ℕ) (h : m ≠ n) :
    ¬ IsArcTransitive (bipartite (m + 1) (n + 1)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [minDeg_bipartite]; omega)
    (not_isVertexTransitive_bipartite m n h)

/-! ### Automorphism counts from arc transitivity

An arc-transitive graph has at least `2|E|` automorphisms, which for the three arc-transitive
families whose edge count is known beats the vertex-transitive bound `|V| ≤ |Aut|` by a wide
margin. -/

theorem two_mul_E_le_autCount_hypercube (n : ℕ) : 2 ^ n * n ≤ (hypercube n).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_hypercube n)
  rwa [two_mul_E_hypercube] at h

theorem two_mul_E_le_autCount_kneser (n k : ℕ) (hk : 1 ≤ k) :
    n.choose k * (n - k).choose k ≤ (kneser n k).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_kneser n k)
  rwa [two_mul_E_kneser n hk] at h

theorem two_mul_E_le_autCount_bipartite_self (n : ℕ) :
    2 * (n * n) ≤ (bipartite n n).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_bipartite_self n)
  rwa [E_bipartite] at h

theorem le_autCount_thetaGraph_replicate_one (n : ℕ) :
    2 * n.factorial ≤ (thetaGraph (List.replicate n 1)).autCount := by
  have h := factorial_mul_factorial_le_autCount_bipartite 2 n
  rw [thetaGraph_replicate_one]
  rwa [show Nat.factorial 2 = 2 from rfl] at h

/-! ### Spiders and theta graphs whose legs all have length one

A spider all of whose legs have length one is a star, and a theta graph all of whose paths have
length one is `K₂,ₙ`.  Both identities are already in the file; what follows is the row of
invariants they carry across.
-/

theorem maxDeg_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) (hne : ks ≠ []) :
    maxDeg (spider ks) = ks.length := by
  obtain ⟨n, hn⟩ : ∃ n, ks.length = n + 1 := by
    cases ks with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [spider_of_all_one h, hn, maxDeg_star]

theorem minDeg_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) (hne : ks ≠ []) :
    minDeg (spider ks) = 1 := by
  obtain ⟨n, hn⟩ : ∃ n, ks.length = n + 1 := by
    cases ks with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [spider_of_all_one h, hn, minDeg_star]

theorem matchNum_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    (spider ks).matchNum = min ks.length 1 := by
  rw [spider_of_all_one h, matchNum_star]

theorem domNum_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    (spider ks).domNum = 1 := by
  rw [spider_of_all_one h, domNum_star]

theorem coverNum_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    (spider ks).coverNum = min 1 ks.length := by
  rw [spider_of_all_one h, coverNum_star]

theorem indepNum_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    (spider ks).indepNum = max 1 ks.length := by
  rw [spider_of_all_one h, indepNum_star]

theorem cliqueCoverNum_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    (spider ks).cliqueCoverNum = max 1 ks.length := by
  rw [spider_of_all_one h, cliqueCoverNum_star]

theorem edgeChromNum_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    (spider ks).edgeChromNum = ks.length := by
  rw [spider_of_all_one h, edgeChromNum_star]

theorem radius_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) (hne : ks ≠ []) :
    (spider ks).radius = 1 := by
  obtain ⟨n, hn⟩ : ∃ n, ks.length = n + 1 := by
    cases ks with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [spider_of_all_one h, hn, radius_star]

theorem diameter_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) (hl : 2 ≤ ks.length) :
    (spider ks).diameter = 2 := by
  obtain ⟨n, hn⟩ : ∃ n, ks.length = n + 2 := ⟨ks.length - 2, by omega⟩
  rw [spider_of_all_one h, hn, diameter_star]

theorem factorial_le_autCount_spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) :
    ks.length.factorial ≤ (spider ks).autCount := by
  rw [spider_of_all_one h]
  exact factorial_le_autCount_star _

theorem maxDeg_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hne : xs ≠ []) :
    maxDeg (thetaGraph xs) = max 2 xs.length := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [thetaGraph_of_all_one h, hn, maxDeg_bipartite]

theorem minDeg_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hne : xs ≠ []) :
    minDeg (thetaGraph xs) = min 2 xs.length := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [thetaGraph_of_all_one h, hn, minDeg_bipartite]

theorem matchNum_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hne : xs ≠ []) :
    (thetaGraph xs).matchNum = min 2 xs.length := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [thetaGraph_of_all_one h, hn, matchNum_bipartite]

theorem indepNum_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) :
    (thetaGraph xs).indepNum = max 2 xs.length := by
  rw [thetaGraph_of_all_one h, indepNum_bipartite]

theorem coverNum_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) :
    (thetaGraph xs).coverNum = min 2 xs.length := by
  rw [thetaGraph_of_all_one h, coverNum_bipartite]

theorem cliqueCoverNum_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) :
    (thetaGraph xs).cliqueCoverNum = max 2 xs.length := by
  rw [thetaGraph_of_all_one h, cliqueCoverNum_bipartite]

theorem edgeChromNum_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hne : xs ≠ []) :
    (thetaGraph xs).edgeChromNum = max 2 xs.length := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [thetaGraph_of_all_one h, hn, edgeChromNum_bipartite]

theorem domNum_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hl : 2 ≤ xs.length) :
    (thetaGraph xs).domNum = 2 := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 2 := ⟨xs.length - 2, by omega⟩
  rw [thetaGraph_of_all_one h, hn, domNum_bipartite]

theorem diameter_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hl : 2 ≤ xs.length) :
    (thetaGraph xs).diameter = 2 := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 2 := ⟨xs.length - 2, by omega⟩
  rw [thetaGraph_of_all_one h, hn, diameter_bipartite]

theorem isConnected_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hne : xs ≠ []) :
    IsConnected (thetaGraph xs) := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n + 1 := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨t.length, rfl⟩
  rw [thetaGraph_of_all_one h, hn]
  exact isConnected_bipartite 1 n

theorem numComponents_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) (hne : xs ≠ []) :
    (thetaGraph xs).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_thetaGraph_of_all_one h hne)

/-! ### Degenerate cycles with pendant vertices

A cycle carrying no pendant vertices at all is a cycle, and a one-vertex cycle carrying `k` of
them is a star.  Both are already recorded; here is the row of invariants they transport into the
`cyclePendant` family, which is otherwise known only through inequalities.
-/

theorem maxDeg_cyclePendant_replicate_zero (m j : ℕ) :
    maxDeg (cyclePendant (m + 3) (List.replicate j 0)) = 2 := by
  rw [cyclePendant_replicate_zero, maxDeg_cycle]

theorem matchNum_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).matchNum = (m + 3) / 2 := by
  rw [cyclePendant_replicate_zero, matchNum_cycle]

theorem indepNum_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).indepNum = (m + 3) / 2 := by
  rw [cyclePendant_replicate_zero, indepNum_cycle]

theorem coverNum_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).coverNum = (m + 3) - (m + 3) / 2 := by
  rw [cyclePendant_replicate_zero, coverNum_cycle]

theorem cliqueNum_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 4) (List.replicate j 0)).cliqueNum = 2 := by
  rw [cyclePendant_replicate_zero, cliqueNum_cycle]

theorem cliqueCoverNum_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 4) (List.replicate j 0)).cliqueCoverNum = (m + 5) / 2 := by
  rw [cyclePendant_replicate_zero, cliqueCoverNum_cycle]

theorem domNum_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).domNum = (m + 5) / 3 := by
  rw [cyclePendant_replicate_zero, domNum_cycle]

theorem radius_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 1) (List.replicate j 0)).radius = (m + 1) / 2 := by
  rw [cyclePendant_replicate_zero, radius_cycle]

theorem diameter_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 1) (List.replicate j 0)).diameter = (m + 1) / 2 := by
  rw [cyclePendant_replicate_zero, diameter_cycle]

theorem isVertexTransitive_cyclePendant_replicate_zero (m j : ℕ) :
    IsVertexTransitive (cyclePendant m (List.replicate j 0)) := by
  rw [cyclePendant_replicate_zero]
  exact isVertexTransitive_cycle m

theorem isArcTransitive_cyclePendant_replicate_zero (m j : ℕ) :
    IsArcTransitive (cyclePendant m (List.replicate j 0)) := by
  rw [cyclePendant_replicate_zero]
  exact isArcTransitive_cycle m

theorem isRegularWith_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).IsRegularWith 2 := by
  rw [cyclePendant_replicate_zero]
  exact isRegularWith_cycle m

theorem degSequence_cyclePendant_replicate_zero (m j : ℕ) :
    degSequence (cyclePendant (m + 3) (List.replicate j 0)) = List.replicate (m + 3) 2 := by
  rw [cyclePendant_replicate_zero, degSequence_cycle]

theorem chromNum_cyclePendant_replicate_zero_odd (t j : ℕ) :
    (cyclePendant (2 * t + 3) (List.replicate j 0)).chromNum = 3 := by
  rw [cyclePendant_replicate_zero, chromNum_cycle_odd]

theorem edgeChromNum_cyclePendant_replicate_zero_even (t j : ℕ) :
    (cyclePendant (2 * t + 4) (List.replicate j 0)).edgeChromNum = 2 := by
  rw [cyclePendant_replicate_zero, edgeChromNum_cycle_even]

theorem edgeChromNum_cyclePendant_replicate_zero_odd (t j : ℕ) :
    (cyclePendant (2 * t + 3) (List.replicate j 0)).edgeChromNum = 3 := by
  rw [cyclePendant_replicate_zero, edgeChromNum_cycle_odd]

theorem two_mul_le_autCount_cyclePendant_replicate_zero (m j : ℕ) :
    2 * (m + 3) ≤ (cyclePendant (m + 3) (List.replicate j 0)).autCount := by
  rw [cyclePendant_replicate_zero]
  exact two_mul_le_autCount_cycle m

theorem maxDeg_cyclePendant_one (k : ℕ) : maxDeg (cyclePendant 1 [k + 1]) = k + 1 := by
  rw [cyclePendant_one, maxDeg_star]

theorem minDeg_cyclePendant_one (k : ℕ) : minDeg (cyclePendant 1 [k + 1]) = 1 := by
  rw [cyclePendant_one, minDeg_star]

theorem matchNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k]).matchNum = min k 1 := by
  rw [cyclePendant_one, matchNum_star]

theorem domNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k]).domNum = 1 := by
  rw [cyclePendant_one, domNum_star]

theorem indepNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k]).indepNum = max 1 k := by
  rw [cyclePendant_one, indepNum_star]

theorem coverNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k]).coverNum = min 1 k := by
  rw [cyclePendant_one, coverNum_star]

theorem cliqueCoverNum_cyclePendant_one (k : ℕ) :
    (cyclePendant 1 [k]).cliqueCoverNum = max 1 k := by
  rw [cyclePendant_one, cliqueCoverNum_star]

theorem edgeChromNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k]).edgeChromNum = k := by
  rw [cyclePendant_one, edgeChromNum_star]

theorem girth_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k]).girth = 0 := by
  rw [cyclePendant_one, girth_star]

theorem radius_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k + 1]).radius = 1 := by
  rw [cyclePendant_one, radius_star]

theorem diameter_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k + 2]).diameter = 2 := by
  rw [cyclePendant_one, diameter_star]

theorem chromNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k + 1]).chromNum = 2 := by
  rw [cyclePendant_one, chromNum_star]

theorem cliqueNum_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k + 1]).cliqueNum = 2 := by
  rw [cyclePendant_one, cliqueNum_star]

theorem isTree_cyclePendant_one (k : ℕ) : IsTree (cyclePendant 1 [k]) := by
  rw [cyclePendant_one]
  exact isTree_star k

theorem isBipartite_cyclePendant_one (k : ℕ) : IsBipartite (cyclePendant 1 [k]) := by
  rw [cyclePendant_one]
  exact isBipartite_star k

theorem compl_cyclePendant_one (k : ℕ) : (cyclePendant 1 [k])ᶜ = empty 1 ⊕g complete k := by
  rw [cyclePendant_one, compl_star]

theorem factorial_le_autCount_cyclePendant_one (k : ℕ) :
    k.factorial ≤ (cyclePendant 1 [k]).autCount := by
  rw [cyclePendant_one]
  exact factorial_le_autCount_star k

theorem not_isVertexTransitive_cyclePendant_one (k : ℕ) :
    ¬ IsVertexTransitive (cyclePendant 1 [k + 2]) := by
  rw [cyclePendant_one]
  exact not_isVertexTransitive_star k

theorem not_isArcTransitive_cyclePendant_one (k : ℕ) :
    ¬ IsArcTransitive (cyclePendant 1 [k + 2]) := by
  rw [cyclePendant_one]
  exact not_isArcTransitive_star k

/-! ### Tadpoles and lollipops with no tail

A tadpole with an empty tail is a cycle and a lollipop with an empty stick is a complete graph, so
the exact values known for those two families fill in the `k = 0` column of the tadpole and
lollipop rows, where until now only inequalities were available.
-/

theorem maxDeg_tadpole_zero (m : ℕ) : maxDeg (tadpole (m + 3) 0) = 2 := by
  rw [tadpole_zero, maxDeg_cycle]

theorem minDeg_tadpole_zero (m : ℕ) : minDeg (tadpole (m + 3) 0) = 2 := by
  rw [tadpole_zero, minDeg_cycle]

theorem matchNum_tadpole_zero (m : ℕ) : (tadpole (m + 3) 0).matchNum = (m + 3) / 2 := by
  rw [tadpole_zero, matchNum_cycle]

theorem indepNum_tadpole_zero (m : ℕ) : (tadpole (m + 3) 0).indepNum = (m + 3) / 2 := by
  rw [tadpole_zero, indepNum_cycle]

theorem coverNum_tadpole_zero (m : ℕ) :
    (tadpole (m + 3) 0).coverNum = (m + 3) - (m + 3) / 2 := by
  rw [tadpole_zero, coverNum_cycle]

theorem cliqueCoverNum_tadpole_zero (m : ℕ) :
    (tadpole (m + 4) 0).cliqueCoverNum = (m + 5) / 2 := by
  rw [tadpole_zero, cliqueCoverNum_cycle]

theorem domNum_tadpole_zero (m : ℕ) : (tadpole (m + 3) 0).domNum = (m + 5) / 3 := by
  rw [tadpole_zero, domNum_cycle]

theorem radius_tadpole_zero (m : ℕ) : (tadpole (m + 1) 0).radius = (m + 1) / 2 := by
  rw [tadpole_zero, radius_cycle]

theorem diameter_tadpole_zero (m : ℕ) : (tadpole (m + 1) 0).diameter = (m + 1) / 2 := by
  rw [tadpole_zero, diameter_cycle]

theorem edgeChromNum_tadpole_zero_even (t : ℕ) : (tadpole (2 * t + 4) 0).edgeChromNum = 2 := by
  rw [tadpole_zero, edgeChromNum_cycle_even]

theorem edgeChromNum_tadpole_zero_odd (t : ℕ) : (tadpole (2 * t + 3) 0).edgeChromNum = 3 := by
  rw [tadpole_zero, edgeChromNum_cycle_odd]

theorem degSequence_tadpole_zero (m : ℕ) :
    degSequence (tadpole (m + 3) 0) = List.replicate (m + 3) 2 := by
  rw [tadpole_zero, degSequence_cycle]

theorem isRegularWith_tadpole_zero (m : ℕ) : (tadpole (m + 3) 0).IsRegularWith 2 := by
  rw [tadpole_zero]
  exact isRegularWith_cycle m

theorem isVertexTransitive_tadpole_zero (m : ℕ) : IsVertexTransitive (tadpole m 0) := by
  rw [tadpole_zero]
  exact isVertexTransitive_cycle m

theorem isArcTransitive_tadpole_zero (m : ℕ) : IsArcTransitive (tadpole m 0) := by
  rw [tadpole_zero]
  exact isArcTransitive_cycle m

theorem two_mul_le_autCount_tadpole_zero (m : ℕ) :
    2 * (m + 3) ≤ (tadpole (m + 3) 0).autCount := by
  rw [tadpole_zero]
  exact two_mul_le_autCount_cycle m

theorem maxDeg_lollipop_zero (m : ℕ) : maxDeg (lollipop m 0) = m - 1 := by
  rw [lollipop_zero, maxDeg_complete]

theorem minDeg_lollipop_zero (m : ℕ) : minDeg (lollipop m 0) = m - 1 := by
  rw [lollipop_zero, minDeg_complete]

theorem matchNum_lollipop_zero (m : ℕ) : (lollipop m 0).matchNum = m / 2 := by
  rw [lollipop_zero, matchNum_complete]

theorem indepNum_lollipop_zero (m : ℕ) : (lollipop m 0).indepNum = min m 1 := by
  rw [lollipop_zero, indepNum_complete]

theorem coverNum_lollipop_zero (m : ℕ) : (lollipop m 0).coverNum = m - 1 := by
  rw [lollipop_zero, coverNum_complete]

theorem cliqueCoverNum_lollipop_zero (m : ℕ) : (lollipop (m + 1) 0).cliqueCoverNum = 1 := by
  rw [lollipop_zero, cliqueCoverNum_complete]

theorem domNum_lollipop_zero (m : ℕ) : (lollipop (m + 1) 0).domNum = 1 := by
  rw [lollipop_zero, domNum_complete]

theorem radius_lollipop_zero (m : ℕ) : (lollipop (m + 2) 0).radius = 1 := by
  rw [lollipop_zero, radius_complete]

theorem diameter_lollipop_zero (m : ℕ) : (lollipop (m + 2) 0).diameter = 1 := by
  rw [lollipop_zero, diameter_complete]

@[simp] theorem edgeChromNum_lollipop_zero (m : ℕ) :
    (lollipop (m + 2) 0).edgeChromNum = if m % 2 = 0 then m + 1 else m + 2 := by
  rw [lollipop_zero, edgeChromNum_complete]

theorem autCount_lollipop_zero (m : ℕ) : (lollipop m 0).autCount = Nat.factorial m := by
  rw [lollipop_zero, autCount_complete]

theorem degSequence_lollipop_zero (m : ℕ) :
    degSequence (lollipop m 0) = List.replicate m (m - 1) := by
  rw [lollipop_zero, degSequence_complete]

theorem isRegularWith_lollipop_zero (m : ℕ) : (lollipop m 0).IsRegularWith (m - 1) := by
  rw [lollipop_zero]
  exact isRegularWith_complete m

theorem isVertexTransitive_lollipop_zero (m : ℕ) : IsVertexTransitive (lollipop m 0) := by
  rw [lollipop_zero]
  exact isVertexTransitive_complete m

theorem isArcTransitive_lollipop_zero (m : ℕ) : IsArcTransitive (lollipop m 0) := by
  rw [lollipop_zero]
  exact isArcTransitive_complete m

/-! ### One-path theta graphs and one-legged spiders

A theta graph with a single path and a spider with a single leg are both paths, so the path row
transfers into the two families whose maximum degree is otherwise out of reach.
-/

theorem maxDeg_thetaGraph_singleton (k : ℕ) : maxDeg (thetaGraph [k + 1]) = 2 := by
  rw [thetaGraph_singleton, show k + 1 + 2 = k + 3 from by ring, maxDeg_path]

theorem minDeg_thetaGraph_singleton (k : ℕ) : minDeg (thetaGraph [k]) = 1 := by
  rw [thetaGraph_singleton, minDeg_path]

theorem matchNum_thetaGraph_singleton (k : ℕ) :
    (thetaGraph [k]).matchNum = (k + 2) / 2 := by
  rw [thetaGraph_singleton, matchNum_path]

theorem indepNum_thetaGraph_singleton (k : ℕ) :
    (thetaGraph [k]).indepNum = (k + 3) / 2 := by
  have h := indepNum_path (k + 2)
  rw [thetaGraph_singleton]
  omega

theorem coverNum_thetaGraph_singleton (k : ℕ) :
    (thetaGraph [k]).coverNum = (k + 2) / 2 := by
  rw [thetaGraph_singleton, coverNum_path]

theorem cliqueCoverNum_thetaGraph_singleton (k : ℕ) :
    (thetaGraph [k]).cliqueCoverNum = (k + 3) / 2 := by
  have h := cliqueCoverNum_path (k + 2)
  rw [thetaGraph_singleton]
  omega

theorem cliqueNum_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).cliqueNum = 2 := by
  rw [thetaGraph_singleton, cliqueNum_path]

theorem chromNum_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).chromNum = 2 := by
  rw [thetaGraph_singleton, chromNum_path]

@[simp] theorem domNum_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).domNum = (k + 4) / 3 := by
  have h := domNum_path (k + 1)
  rw [thetaGraph_singleton, show k + 2 = k + 1 + 1 from by ring]
  omega

@[simp] theorem radius_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).radius = (k + 2) / 2 := by
  have h := radius_path (k + 1)
  rw [thetaGraph_singleton, show k + 2 = k + 1 + 1 from by ring]
  omega

theorem diameter_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).diameter = k + 1 := by
  have h := diameter_path (k + 1)
  rw [thetaGraph_singleton, show k + 2 = k + 1 + 1 from by ring]
  omega

theorem edgeChromNum_thetaGraph_singleton (k : ℕ) : (thetaGraph [k + 1]).edgeChromNum = 2 := by
  rw [thetaGraph_singleton, show k + 1 + 2 = k + 3 from by ring, edgeChromNum_path]

theorem girth_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).girth = 0 := by
  rw [thetaGraph_singleton, girth_path]

theorem isAcyclic_thetaGraph_singleton (k : ℕ) : IsAcyclic (thetaGraph [k]) := by
  rw [thetaGraph_singleton]
  exact isAcyclic_path _

theorem isTree_thetaGraph_singleton (k : ℕ) : IsTree (thetaGraph [k]) := by
  rw [thetaGraph_singleton, show k + 2 = k + 1 + 1 from by ring]
  exact isTree_path (k + 1)

theorem isConnected_thetaGraph_singleton (k : ℕ) : IsConnected (thetaGraph [k]) := by
  rw [thetaGraph_singleton, show k + 2 = k + 1 + 1 from by ring]
  exact isConnected_path (k + 1)

theorem numComponents_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).numComponents = 1 := by
  rw [thetaGraph_singleton, show k + 2 = k + 1 + 1 from by ring, numComponents_path]

theorem not_isVertexTransitive_thetaGraph_singleton (k : ℕ) :
    ¬ IsVertexTransitive (thetaGraph [k + 1]) := by
  rw [thetaGraph_singleton, show k + 1 + 2 = k + 3 from by ring]
  exact not_isVertexTransitive_path k

theorem not_isArcTransitive_thetaGraph_singleton (k : ℕ) :
    ¬ IsArcTransitive (thetaGraph [k + 1]) := by
  rw [thetaGraph_singleton, show k + 1 + 2 = k + 3 from by ring]
  exact not_isArcTransitive_path k

theorem not_isSelfComplementary_thetaGraph_singleton (k : ℕ) :
    ¬ IsSelfComplementary (thetaGraph [k + 3]) := by
  rw [thetaGraph_singleton, show k + 3 + 2 = k + 5 from by ring]
  exact not_isSelfComplementary_path k

@[simp] theorem maxDeg_spider_singleton (k : ℕ) : maxDeg (spider [k + 2]) = 2 := by
  rw [spider_singleton, show 1 + (k + 2) = k + 3 from by ring, maxDeg_path]

@[simp] theorem matchNum_spider_singleton (k : ℕ) : (spider [k]).matchNum = (k + 1) / 2 := by
  rw [spider_singleton, show 1 + k = k + 1 from by ring, matchNum_path]

@[simp] theorem indepNum_spider_singleton (k : ℕ) : (spider [k]).indepNum = (k + 2) / 2 := by
  have h := indepNum_path (k + 1)
  rw [spider_singleton, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem coverNum_spider_singleton (k : ℕ) : (spider [k]).coverNum = (k + 1) / 2 := by
  rw [spider_singleton, show 1 + k = k + 1 from by ring, coverNum_path]

@[simp] theorem cliqueCoverNum_spider_singleton (k : ℕ) :
    (spider [k]).cliqueCoverNum = (k + 2) / 2 := by
  have h := cliqueCoverNum_path (k + 1)
  rw [spider_singleton, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem domNum_spider_singleton (k : ℕ) : (spider [k]).domNum = (k + 3) / 3 := by
  have h := domNum_path k
  rw [spider_singleton, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem radius_spider_singleton (k : ℕ) : (spider [k]).radius = (k + 1) / 2 := by
  have h := radius_path k
  rw [spider_singleton, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem diameter_spider_singleton (k : ℕ) : (spider [k]).diameter = k := by
  rw [spider_singleton, show 1 + k = k + 1 from by ring, diameter_path]

@[simp] theorem edgeChromNum_spider_singleton (k : ℕ) : (spider [k + 2]).edgeChromNum = 2 := by
  rw [spider_singleton, show 1 + (k + 2) = k + 3 from by ring, edgeChromNum_path]

@[simp] theorem lineGraph_spider_singleton (k : ℕ) : lineGraph (spider [k]) = path k := by
  rw [spider_singleton, show 1 + k = k + 1 from by ring, lineGraph_path]

@[simp] theorem not_isVertexTransitive_spider_singleton (k : ℕ) :
    ¬ IsVertexTransitive (spider [k + 2]) := by
  rw [spider_singleton, show 1 + (k + 2) = k + 3 from by ring]
  exact not_isVertexTransitive_path k

@[simp] theorem not_isArcTransitive_spider_singleton (k : ℕ) :
    ¬ IsArcTransitive (spider [k + 2]) := by
  rw [spider_singleton, show 1 + (k + 2) = k + 3 from by ring]
  exact not_isArcTransitive_path k

/-! ### Single-connection circulants and one-element Kneser graphs

`circulant n [1]` is the cycle and `kneser n 1` is the complete graph, so both families inherit
an exact row where otherwise only bounds are known.
-/

theorem matchNum_circulant_one (n : ℕ) : (circulant (n + 3) [1]).matchNum = (n + 3) / 2 := by
  rw [circulant_one, matchNum_cycle]

theorem indepNum_circulant_one (n : ℕ) : (circulant (n + 3) [1]).indepNum = (n + 3) / 2 := by
  rw [circulant_one, indepNum_cycle]

theorem coverNum_circulant_one (n : ℕ) :
    (circulant (n + 3) [1]).coverNum = (n + 3) - (n + 3) / 2 := by
  rw [circulant_one, coverNum_cycle]

theorem cliqueNum_circulant_one (n : ℕ) : (circulant (n + 4) [1]).cliqueNum = 2 := by
  rw [circulant_one, cliqueNum_cycle]

theorem cliqueCoverNum_circulant_one (n : ℕ) :
    (circulant (n + 4) [1]).cliqueCoverNum = (n + 5) / 2 := by
  rw [circulant_one, cliqueCoverNum_cycle]

theorem domNum_circulant_one (n : ℕ) : (circulant (n + 3) [1]).domNum = (n + 5) / 3 := by
  rw [circulant_one, domNum_cycle]

theorem diameter_circulant_one (n : ℕ) : (circulant (n + 1) [1]).diameter = (n + 1) / 2 := by
  rw [circulant_one, diameter_cycle]

theorem radius_circulant_one (n : ℕ) : (circulant (n + 1) [1]).radius = (n + 1) / 2 := by
  rw [circulant_one, radius_cycle]

theorem chromNum_circulant_one_even (m : ℕ) : (circulant (2 * m + 2) [1]).chromNum = 2 := by
  rw [circulant_one, chromNum_cycle_even]

theorem chromNum_circulant_one_odd (m : ℕ) : (circulant (2 * m + 3) [1]).chromNum = 3 := by
  rw [circulant_one, chromNum_cycle_odd]

theorem edgeChromNum_circulant_one_even (m : ℕ) :
    (circulant (2 * m + 4) [1]).edgeChromNum = 2 := by
  rw [circulant_one, edgeChromNum_cycle_even]

theorem edgeChromNum_circulant_one_odd (m : ℕ) :
    (circulant (2 * m + 3) [1]).edgeChromNum = 3 := by
  rw [circulant_one, edgeChromNum_cycle_odd]

theorem isRegularWith_circulant_one (n : ℕ) : (circulant (n + 3) [1]).IsRegularWith 2 := by
  rw [circulant_one]
  exact isRegularWith_cycle n

theorem isConnected_circulant_one (n : ℕ) : IsConnected (circulant (n + 1) [1]) := by
  rw [circulant_one]
  exact isConnected_cycle n

theorem numComponents_circulant_one (n : ℕ) : (circulant (n + 1) [1]).numComponents = 1 := by
  rw [circulant_one, numComponents_cycle]

theorem isArcTransitive_circulant_one (n : ℕ) : IsArcTransitive (circulant n [1]) := by
  rw [circulant_one]
  exact isArcTransitive_cycle n

theorem two_mul_le_autCount_circulant_one (n : ℕ) :
    2 * (n + 3) ≤ (circulant (n + 3) [1]).autCount := by
  rw [circulant_one]
  exact two_mul_le_autCount_cycle n

theorem not_isTree_circulant_one (n : ℕ) : ¬ IsTree (circulant (n + 3) [1]) := by
  rw [circulant_one]
  exact not_isTree_cycle n

theorem matchNum_kneser_one (n : ℕ) : (kneser n 1).matchNum = n / 2 := by
  rw [kneser_one, matchNum_complete]

theorem indepNum_kneser_one (n : ℕ) : (kneser n 1).indepNum = min n 1 := by
  rw [kneser_one, indepNum_complete]

theorem coverNum_kneser_one (n : ℕ) : (kneser n 1).coverNum = n - 1 := by
  rw [kneser_one, coverNum_complete]

theorem cliqueNum_kneser_one (n : ℕ) : (kneser n 1).cliqueNum = n := by
  rw [kneser_one, cliqueNum_complete]

theorem chromNum_kneser_one (n : ℕ) : (kneser n 1).chromNum = n := by
  rw [kneser_one, chromNum_complete]

theorem cliqueCoverNum_kneser_one (n : ℕ) : (kneser (n + 1) 1).cliqueCoverNum = 1 := by
  rw [kneser_one, cliqueCoverNum_complete]

theorem domNum_kneser_one (n : ℕ) : (kneser (n + 1) 1).domNum = 1 := by
  rw [kneser_one, domNum_complete]

theorem radius_kneser_one (n : ℕ) : (kneser (n + 2) 1).radius = 1 := by
  rw [kneser_one, radius_complete]

theorem diameter_kneser_one (n : ℕ) : (kneser (n + 2) 1).diameter = 1 := by
  rw [kneser_one, diameter_complete]

@[simp] theorem edgeChromNum_kneser_one (n : ℕ) :
    (kneser (n + 2) 1).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 := by
  rw [kneser_one, edgeChromNum_complete]

theorem autCount_kneser_one (n : ℕ) : (kneser n 1).autCount = Nat.factorial n := by
  rw [kneser_one, autCount_complete]

theorem girth_kneser_one (n : ℕ) : (kneser (n + 3) 1).girth = 3 := by
  rw [kneser_one, girth_complete]

@[simp] theorem not_isSelfComplementary_kneser_one (n : ℕ) :
    ¬ IsSelfComplementary (kneser (n + 2) 1) := by
  rw [kneser_one]
  exact not_isSelfComplementary_complete n

/-! ### One-element Johnson graphs and connectionless circulants

`johnson n 1` is the complete graph and `circulant n []` is the edgeless graph, which fills the
`k = 1` column of the Johnson row and the empty column of the circulant row.
-/

theorem matchNum_johnson_one (n : ℕ) : (johnson n 1).matchNum = n / 2 := by
  rw [johnson_one, matchNum_complete]

theorem indepNum_johnson_one (n : ℕ) : (johnson n 1).indepNum = min n 1 := by
  rw [johnson_one, indepNum_complete]

theorem cliqueNum_johnson_one (n : ℕ) : (johnson n 1).cliqueNum = n := by
  rw [johnson_one, cliqueNum_complete]

theorem chromNum_johnson_one (n : ℕ) : (johnson n 1).chromNum = n := by
  rw [johnson_one, chromNum_complete]

theorem cliqueCoverNum_johnson_one (n : ℕ) : (johnson (n + 1) 1).cliqueCoverNum = 1 := by
  rw [johnson_one, cliqueCoverNum_complete]

theorem domNum_johnson_one (n : ℕ) : (johnson (n + 1) 1).domNum = 1 := by
  rw [johnson_one, domNum_complete]

@[simp] theorem edgeChromNum_johnson_one (n : ℕ) :
    (johnson (n + 2) 1).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 := by
  rw [johnson_one, edgeChromNum_complete]

theorem autCount_johnson_one (n : ℕ) : (johnson n 1).autCount = Nat.factorial n := by
  rw [johnson_one, autCount_complete]

theorem isArcTransitive_johnson_one (n : ℕ) : IsArcTransitive (johnson n 1) := by
  rw [johnson_one]
  exact isArcTransitive_complete n

@[simp] theorem not_isSelfComplementary_johnson_one (n : ℕ) :
    ¬ IsSelfComplementary (johnson (n + 2) 1) := by
  rw [johnson_one]
  exact not_isSelfComplementary_complete n

theorem maxDeg_circulant_nil (n : ℕ) : maxDeg (circulant n []) = 0 := by
  rw [circulant_nil, maxDeg_empty]

theorem minDeg_circulant_nil (n : ℕ) : minDeg (circulant n []) = 0 := by
  rw [circulant_nil, minDeg_empty]

theorem matchNum_circulant_nil (n : ℕ) : (circulant n []).matchNum = 0 := by
  rw [circulant_nil, matchNum_empty]

theorem indepNum_circulant_nil (n : ℕ) : (circulant n []).indepNum = n := by
  rw [circulant_nil, indepNum_empty]

theorem coverNum_circulant_nil (n : ℕ) : (circulant n []).coverNum = 0 := by
  rw [circulant_nil, coverNum_empty]

theorem cliqueNum_circulant_nil (n : ℕ) : (circulant n []).cliqueNum = min n 1 := by
  rw [circulant_nil, cliqueNum_empty]

theorem cliqueCoverNum_circulant_nil (n : ℕ) : (circulant n []).cliqueCoverNum = n := by
  rw [circulant_nil, cliqueCoverNum_empty]

theorem chromNum_circulant_nil (n : ℕ) : (circulant (n + 1) []).chromNum = 1 := by
  rw [circulant_nil, chromNum_empty]

theorem edgeChromNum_circulant_nil (n : ℕ) : (circulant n []).edgeChromNum = 0 := by
  rw [circulant_nil, edgeChromNum_empty]

theorem domNum_circulant_nil (n : ℕ) : (circulant n []).domNum = n := by
  rw [circulant_nil, domNum_empty]

theorem radius_circulant_nil (n : ℕ) : (circulant n []).radius = 0 := by
  rw [circulant_nil, radius_empty]

theorem diameter_circulant_nil (n : ℕ) : (circulant n []).diameter = 0 := by
  rw [circulant_nil, diameter_empty]

theorem girth_circulant_nil (n : ℕ) : (circulant n []).girth = 0 := by
  rw [circulant_nil, girth_empty]

theorem numComponents_circulant_nil (n : ℕ) : (circulant n []).numComponents = n := by
  rw [circulant_nil, numComponents_empty]

theorem degSequence_circulant_nil (n : ℕ) :
    degSequence (circulant n []) = List.replicate n 0 := by
  rw [circulant_nil, degSequence_empty]

theorem autCount_circulant_nil (n : ℕ) : (circulant n []).autCount = Nat.factorial n := by
  rw [circulant_nil, autCount_empty]

theorem isRegularWith_circulant_nil (n : ℕ) : (circulant n []).IsRegularWith 0 := by
  rw [circulant_nil]
  exact isRegularWith_empty n

theorem isAcyclic_circulant_nil (n : ℕ) : IsAcyclic (circulant n []) := by
  rw [circulant_nil]
  exact isAcyclic_empty n

theorem isBipartite_circulant_nil (n : ℕ) : IsBipartite (circulant n []) := by
  rw [circulant_nil]
  exact isBipartite_empty n

theorem isArcTransitive_circulant_nil (n : ℕ) : IsArcTransitive (circulant n []) := by
  rw [circulant_nil]
  exact isArcTransitive_empty n

theorem not_isConnected_circulant_nil (n : ℕ) : ¬ IsConnected (circulant (n + 2) []) := by
  rw [circulant_nil]
  exact not_isConnected_empty n

@[simp] theorem not_isSelfComplementary_circulant_nil (n : ℕ) :
    ¬ IsSelfComplementary (circulant (n + 2) []) := by
  rw [circulant_nil]
  exact not_isSelfComplementary_empty n

/-! ### Tadpoles and lollipops on a one-vertex head

A tadpole whose cycle is a single vertex and a lollipop whose clique is a single vertex are both
paths, which fills the `m = 1` column of the two rows whose general entries all need `m ≥ 3`.
-/

@[simp] theorem maxDeg_tadpole_one (k : ℕ) : maxDeg (tadpole 1 (k + 2)) = 2 := by
  rw [tadpole_one, show 1 + (k + 2) = k + 3 from by ring, maxDeg_path]

@[simp] theorem minDeg_tadpole_one (k : ℕ) : minDeg (tadpole 1 (k + 1)) = 1 := by
  rw [tadpole_one, show 1 + (k + 1) = k + 2 from by ring, minDeg_path]

@[simp] theorem matchNum_tadpole_one (k : ℕ) : (tadpole 1 k).matchNum = (k + 1) / 2 := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring, matchNum_path]

@[simp] theorem indepNum_tadpole_one (k : ℕ) : (tadpole 1 k).indepNum = (k + 2) / 2 := by
  have h := indepNum_path (k + 1)
  rw [tadpole_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem coverNum_tadpole_one (k : ℕ) : (tadpole 1 k).coverNum = (k + 1) / 2 := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring, coverNum_path]

@[simp] theorem cliqueCoverNum_tadpole_one (k : ℕ) :
    (tadpole 1 k).cliqueCoverNum = (k + 2) / 2 := by
  have h := cliqueCoverNum_path (k + 1)
  rw [tadpole_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem cliqueNum_tadpole_one (k : ℕ) : (tadpole 1 (k + 1)).cliqueNum = 2 := by
  rw [tadpole_one, show 1 + (k + 1) = k + 2 from by ring, cliqueNum_path]

@[simp] theorem chromNum_tadpole_one (k : ℕ) : (tadpole 1 (k + 1)).chromNum = 2 := by
  rw [tadpole_one, show 1 + (k + 1) = k + 2 from by ring, chromNum_path]

@[simp] theorem domNum_tadpole_one (k : ℕ) : (tadpole 1 k).domNum = (k + 3) / 3 := by
  have h := domNum_path k
  rw [tadpole_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem radius_tadpole_one (k : ℕ) : (tadpole 1 k).radius = (k + 1) / 2 := by
  have h := radius_path k
  rw [tadpole_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem diameter_tadpole_one (k : ℕ) : (tadpole 1 k).diameter = k := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring, diameter_path]

@[simp] theorem edgeChromNum_tadpole_one (k : ℕ) : (tadpole 1 (k + 2)).edgeChromNum = 2 := by
  rw [tadpole_one, show 1 + (k + 2) = k + 3 from by ring, edgeChromNum_path]

theorem girth_tadpole_one (k : ℕ) : (tadpole 1 k).girth = 0 := by
  rw [tadpole_one, girth_path]

theorem isAcyclic_tadpole_one (k : ℕ) : IsAcyclic (tadpole 1 k) := by
  rw [tadpole_one]
  exact isAcyclic_path _

@[simp] theorem isTree_tadpole_one (k : ℕ) : IsTree (tadpole 1 k) := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring]
  exact isTree_path k

@[simp] theorem isConnected_tadpole_one (k : ℕ) : IsConnected (tadpole 1 k) := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring]
  exact isConnected_path k

@[simp] theorem numComponents_tadpole_one (k : ℕ) : (tadpole 1 k).numComponents = 1 := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring, numComponents_path]

@[simp] theorem lineGraph_tadpole_one (k : ℕ) : lineGraph (tadpole 1 k) = path k := by
  rw [tadpole_one, show 1 + k = k + 1 from by ring, lineGraph_path]

@[simp] theorem maxDeg_lollipop_one (k : ℕ) : maxDeg (lollipop 1 (k + 2)) = 2 := by
  rw [lollipop_one, show 1 + (k + 2) = k + 3 from by ring, maxDeg_path]

@[simp] theorem minDeg_lollipop_one (k : ℕ) : minDeg (lollipop 1 (k + 1)) = 1 := by
  rw [lollipop_one, show 1 + (k + 1) = k + 2 from by ring, minDeg_path]

@[simp] theorem matchNum_lollipop_one (k : ℕ) : (lollipop 1 k).matchNum = (k + 1) / 2 := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring, matchNum_path]

@[simp] theorem indepNum_lollipop_one (k : ℕ) : (lollipop 1 k).indepNum = (k + 2) / 2 := by
  have h := indepNum_path (k + 1)
  rw [lollipop_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem coverNum_lollipop_one (k : ℕ) : (lollipop 1 k).coverNum = (k + 1) / 2 := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring, coverNum_path]

@[simp] theorem cliqueCoverNum_lollipop_one (k : ℕ) :
    (lollipop 1 k).cliqueCoverNum = (k + 2) / 2 := by
  have h := cliqueCoverNum_path (k + 1)
  rw [lollipop_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem cliqueNum_lollipop_one (k : ℕ) : (lollipop 1 (k + 1)).cliqueNum = 2 := by
  rw [lollipop_one, show 1 + (k + 1) = k + 2 from by ring, cliqueNum_path]

@[simp] theorem chromNum_lollipop_one (k : ℕ) : (lollipop 1 (k + 1)).chromNum = 2 := by
  rw [lollipop_one, show 1 + (k + 1) = k + 2 from by ring, chromNum_path]

@[simp] theorem domNum_lollipop_one (k : ℕ) : (lollipop 1 k).domNum = (k + 3) / 3 := by
  have h := domNum_path k
  rw [lollipop_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem radius_lollipop_one (k : ℕ) : (lollipop 1 k).radius = (k + 1) / 2 := by
  have h := radius_path k
  rw [lollipop_one, show 1 + k = k + 1 from by ring]
  omega

@[simp] theorem diameter_lollipop_one (k : ℕ) : (lollipop 1 k).diameter = k := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring, diameter_path]

@[simp] theorem edgeChromNum_lollipop_one (k : ℕ) : (lollipop 1 (k + 2)).edgeChromNum = 2 := by
  rw [lollipop_one, show 1 + (k + 2) = k + 3 from by ring, edgeChromNum_path]

theorem girth_lollipop_one (k : ℕ) : (lollipop 1 k).girth = 0 := by
  rw [lollipop_one, girth_path]

theorem isAcyclic_lollipop_one (k : ℕ) : IsAcyclic (lollipop 1 k) := by
  rw [lollipop_one]
  exact isAcyclic_path _

@[simp] theorem isTree_lollipop_one (k : ℕ) : IsTree (lollipop 1 k) := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring]
  exact isTree_path k

@[simp] theorem isConnected_lollipop_one (k : ℕ) : IsConnected (lollipop 1 k) := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring]
  exact isConnected_path k

@[simp] theorem numComponents_lollipop_one (k : ℕ) : (lollipop 1 k).numComponents = 1 := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring, numComponents_path]

@[simp] theorem lineGraph_lollipop_one (k : ℕ) : lineGraph (lollipop 1 k) = path k := by
  rw [lollipop_one, show 1 + k = k + 1 from by ring, lineGraph_path]

/-! ### Kneser graphs below the packing threshold

Two `k`-subsets of an `n`-set cannot be disjoint once `n < 2 * k`, so `kneser n k` is edgeless
there.  The whole edgeless row therefore applies, in a range where the usual Kneser arguments —
which all assume `2 * k ≤ n` — say nothing at all.
-/

theorem maxDeg_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : maxDeg (kneser n k) = 0 := by
  rw [kneser_eq_empty n k h, maxDeg_empty]

theorem minDeg_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : minDeg (kneser n k) = 0 := by
  rw [kneser_eq_empty n k h, minDeg_empty]

@[simp] theorem matchNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : (kneser n k).matchNum = 0 := by
  rw [kneser_eq_empty n k h, matchNum_empty]

@[simp] theorem coverNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : (kneser n k).coverNum = 0 := by
  rw [kneser_eq_empty n k h, coverNum_empty]

theorem indepNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).indepNum = n.choose k := by
  rw [kneser_eq_empty n k h, indepNum_empty]

theorem cliqueNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).cliqueNum = min (n.choose k) 1 := by
  rw [kneser_eq_empty n k h, cliqueNum_empty]

theorem cliqueCoverNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).cliqueCoverNum = n.choose k := by
  rw [kneser_eq_empty n k h, cliqueCoverNum_empty]

theorem domNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : (kneser n k).domNum = n.choose k := by
  rw [kneser_eq_empty n k h, domNum_empty]

theorem numComponents_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).numComponents = n.choose k := by
  rw [kneser_eq_empty n k h, numComponents_empty]

theorem radius_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : (kneser n k).radius = 0 := by
  rw [kneser_eq_empty n k h, radius_empty]

theorem diameter_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : (kneser n k).diameter = 0 := by
  rw [kneser_eq_empty n k h, diameter_empty]

theorem girth_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : (kneser n k).girth = 0 := by
  rw [kneser_eq_empty n k h, girth_empty]

@[simp] theorem edgeChromNum_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).edgeChromNum = 0 := by
  rw [kneser_eq_empty n k h, edgeChromNum_empty]

theorem chromNum_kneser_of_lt (n k : ℕ) (hk : k ≤ n) (h : n < 2 * k) :
    (kneser n k).chromNum = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, n.choose k = m + 1 := ⟨n.choose k - 1, by
    have := Nat.choose_pos hk; omega⟩
  rw [kneser_eq_empty n k h, hm, chromNum_empty]

theorem degSequence_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    degSequence (kneser n k) = List.replicate (n.choose k) 0 := by
  rw [kneser_eq_empty n k h, degSequence_empty]

theorem autCount_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).autCount = Nat.factorial (n.choose k) := by
  rw [kneser_eq_empty n k h, autCount_empty]

theorem isRegularWith_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).IsRegularWith 0 := by
  rw [kneser_eq_empty n k h]
  exact isRegularWith_empty _

theorem isAcyclic_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : IsAcyclic (kneser n k) := by
  rw [kneser_eq_empty n k h]
  exact isAcyclic_empty _

theorem isBipartite_kneser_of_lt (n k : ℕ) (h : n < 2 * k) : IsBipartite (kneser n k) := by
  rw [kneser_eq_empty n k h]
  exact isBipartite_empty _

theorem isArcTransitive_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    IsArcTransitive (kneser n k) := by
  rw [kneser_eq_empty n k h]
  exact isArcTransitive_empty _

theorem compl_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k)ᶜ = complete (n.choose k) := by
  rw [kneser_eq_empty n k h, compl_empty]

theorem lineGraph_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    lineGraph (kneser n k) = empty 0 := by
  rw [kneser_eq_empty n k h, lineGraph_empty]

end IsoGraph
