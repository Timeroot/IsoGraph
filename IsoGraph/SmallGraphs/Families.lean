import IsoGraph.SmallGraphs.Bounds

/-!
# The parametrised families

The parametrised families in their own right: fans, books, prisms, ladders, cocktail party and
balanced complete multipartite graphs, and the line graphs of the regular families.
-/

namespace IsoGraph

/-! ### Edge counts of the regular families -/

@[simp] theorem E_petersen : petersen.E = 15 := by
  have h := two_mul_E_of_degSequence_replicate degSequence_petersen
  omega

@[simp] theorem E_cocktailParty (n : ℕ) : (cocktailParty n).E = n * (2 * n - 2) := by
  have h := two_mul_E_of_degSequence_replicate (degSequence_cocktailParty n)
  rw [Nat.mul_assoc] at h
  omega

theorem two_mul_E_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    2 * (paley q).E = q * ((q - 1) / 2) :=
  two_mul_E_of_degSequence_replicate (degSequence_paley q hq)

theorem E_pos_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) : 0 < (kneser n k).E := by
  have h := two_mul_E_kneser n hk
  have h1 : 0 < n.choose k := Nat.choose_pos (by omega)
  have h2 : 0 < (n - k).choose k := Nat.choose_pos (by omega)
  have h3 : 0 < n.choose k * (n - k).choose k := Nat.mul_pos h1 h2
  omega

/-! ### The line graphs of the named regular families -/

@[simp] theorem E_lineGraph_petersen : (lineGraph petersen).E = 30 := by
  have h := E_lineGraph_of_degSequence_replicate degSequence_petersen
  rw [show (3 : ℕ).choose 2 = 3 from by decide] at h
  omega

@[simp] theorem isRegularWith_lineGraph_petersen : (lineGraph petersen).IsRegularWith 4 := by
  have h := isRegularWith_lineGraph (by rw [E_petersen]; omega) degSequence_petersen
  norm_num at h
  exact h

@[simp] theorem E_lineGraph_prism (n : ℕ) : (lineGraph (prism (n + 3))).E = 6 * (n + 3) := by
  have h := E_lineGraph_of_degSequence_replicate (degSequence_prism n)
  rw [show (3 : ℕ).choose 2 = 3 from by decide] at h
  omega

@[simp] theorem isRegularWith_lineGraph_prism (n : ℕ) :
    (lineGraph (prism (n + 3))).IsRegularWith 4 := by
  have h := isRegularWith_lineGraph (by rw [E_prism]; omega) (degSequence_prism n)
  norm_num at h
  exact h

@[simp] theorem E_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube n)).E = 2 ^ n * n.choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_hypercube n)

theorem isRegularWith_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 1))).IsRegularWith (2 * (n + 1) - 2) := by
  refine isRegularWith_lineGraph ?_ (degSequence_hypercube (n + 1))
  have h := E_hypercube (n + 1)
  have h2 : 0 < (n + 1) * 2 ^ (n + 1) := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  omega

@[simp] theorem E_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty n)).E = 2 * n * (2 * n - 2).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_cocktailParty n)

theorem isRegularWith_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty (n + 2))).IsRegularWith (2 * (2 * (n + 2) - 2) - 2) := by
  refine isRegularWith_lineGraph ?_ (degSequence_cocktailParty (n + 2))
  rw [E_cocktailParty]
  exact Nat.mul_pos (by omega) (by omega)

@[simp] theorem E_lineGraph_bipartite_self (n : ℕ) :
    (lineGraph (bipartite n n)).E = 2 * n * n.choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_bipartite_self n)

theorem isRegularWith_lineGraph_bipartite_self (n : ℕ) :
    (lineGraph (bipartite (n + 1) (n + 1))).IsRegularWith (2 * (n + 1) - 2) := by
  refine isRegularWith_lineGraph ?_ (degSequence_bipartite_self (n + 1))
  rw [E_bipartite]
  exact Nat.mul_pos (by omega) (by omega)

theorem E_lineGraph_triangular (n : ℕ) (hn : 4 ≤ n) :
    (lineGraph (triangular n)).E = n.choose 2 * (2 * (n - 2)).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_triangular n hn)

theorem isRegularWith_lineGraph_triangular (n : ℕ) (hn : 4 ≤ n) :
    (lineGraph (triangular n)).IsRegularWith (2 * (2 * (n - 2)) - 2) := by
  refine isRegularWith_lineGraph ?_ (degSequence_triangular n hn)
  rw [E_triangular]
  exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

theorem E_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) :
    (lineGraph (kneser n k)).E = n.choose k * ((n - k).choose k).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_kneser (n := n) hk)

theorem isRegularWith_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (lineGraph (kneser n k)).IsRegularWith (2 * (n - k).choose k - 2) :=
  isRegularWith_lineGraph (E_pos_kneser n k hk hkn) (degSequence_kneser (n := n) hk)

theorem E_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (lineGraph (paley q)).E = q * ((q - 1) / 2).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_paley q hq)

theorem isRegularWith_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : (lineGraph (paley q)).IsRegularWith (2 * ((q - 1) / 2) - 2) := by
  refine isRegularWith_lineGraph ?_ (degSequence_paley q hq)
  have h := two_mul_E_paley q hq
  have h2 : 0 < q * ((q - 1) / 2) := Nat.mul_pos (by omega) (by omega)
  omega

/-! ### Consistency of the line graph counts -/

example (n : ℕ) : (lineGraph (cycle (n + 3))).E = n + 3 := by
  have h := E_lineGraph_of_degSequence_replicate (degSequence_cycle n)
  rw [show (2 : ℕ).choose 2 = 1 from by decide] at h
  omega

example (n : ℕ) : (lineGraph (complete n)).E = n * (n - 1).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_complete n)

example : (lineGraph petersen).V = 15 := by rw [V_lineGraph, E_petersen]

example (n : ℕ) : 2 * (lineGraph (hypercube (n + 1))).E = 2 * (hypercube (n + 1)).E * n := by
  have h := two_mul_E_lineGraph_of_degSequence_replicate (degSequence_hypercube (n + 1))
  rwa [Nat.add_sub_cancel] at h

example : (path 7).indepNum = 4 := by rw [indepNum_path]

example : (path 6).matchNum = 3 := by rw [matchNum_path]

/-! ### The fan graph

`fan n = K₁ ∨ Pₙ` is a path with an extra apex vertex joined to all of it.  Every invariant of a
join is determined by the two factors, so the whole table for the fan follows from the table for
the path together with the trivial values for `K₁`. -/

theorem fan_eq_join (n : ℕ) : fan n = complete 1 ∇g path n := rfl

@[simp] theorem fan_zero : fan 0 = complete 1 := by
  show complete 1 ∇g path 0 = _
  rw [path_zero, ← complete_zero, join_complete]

@[simp] theorem fan_one : fan 1 = complete 2 := by
  show complete 1 ∇g path 1 = _
  rw [path_one, ← complete_one, join_complete]

@[simp] theorem fan_two : fan 2 = complete 3 := by
  show complete 1 ∇g path 2 = _
  rw [path_two, join_complete]

@[simp] theorem E_fan (n : ℕ) : (fan (n + 1)).E = 2 * n + 1 := by
  show (complete 1 ∇g path (n + 1)).E = _
  rw [E_join, E_complete, E_path, V_complete, V_path, show (1 : ℕ).choose 2 = 0 from rfl]
  omega

@[simp] theorem chromNum_fan (n : ℕ) : (fan (n + 2)).chromNum = 3 := by
  show (complete 1 ∇g path (n + 2)).chromNum = _
  rw [chromNum_join, chromNum_complete, chromNum_path]

@[simp] theorem cliqueNum_fan (n : ℕ) : (fan (n + 2)).cliqueNum = 3 := by
  show (complete 1 ∇g path (n + 2)).cliqueNum = _
  rw [cliqueNum_join, cliqueNum_complete, cliqueNum_path]

/-- The apex is never worth taking: a maximum independent set of the fan is one of the path. -/
@[simp] theorem indepNum_fan (n : ℕ) : (fan (n + 1)).indepNum = (n + 2) / 2 := by
  show (complete 1 ∇g path (n + 1)).indepNum = _
  rw [indepNum_join, indepNum_complete, indepNum_path]
  omega

@[simp] theorem coverNum_fan (n : ℕ) : (fan (n + 1)).coverNum = (n + 3) / 2 := by
  have h := (fan (n + 1)).coverNum_add_indepNum
  rw [V_fan, indepNum_fan] at h
  omega

/-- The apex has the largest degree once the path is long enough to be a path. -/
@[simp] theorem maxDeg_fan (n : ℕ) : maxDeg (fan (n + 3)) = n + 3 := by
  show maxDeg (complete 1 ∇g path (n + 3)) = _
  rw [maxDeg_join (by simp) (by simp), maxDeg_complete, maxDeg_path, V_complete, V_path]
  omega

/-- An end of the path keeps the smallest degree, `2`. -/
@[simp] theorem minDeg_fan (n : ℕ) : minDeg (fan (n + 2)) = 2 := by
  show minDeg (complete 1 ∇g path (n + 2)) = _
  rw [minDeg_join (by simp) (by simp), minDeg_complete, minDeg_path, V_complete, V_path]
  omega

@[simp] theorem numComponents_fan (n : ℕ) : (fan (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_fan n)

/-- The apex dominates the whole fan. -/
@[simp] theorem domNum_fan (n : ℕ) : (fan n).domNum = 1 := by
  show (complete 1 ∇g path n).domNum = _
  exact (domNum_join_eq_one_iff _ _).2 (Or.inl (domNum_complete 0))

@[simp] theorem radius_fan (n : ℕ) : (fan (n + 1)).radius = 1 :=
  (radius_eq_one_iff_domNum_eq_one (by rw [V_fan]; omega)).2 (domNum_fan (n + 1))

/-- The apex closes a triangle with the first edge of the path. -/
@[simp] theorem girth_fan (n : ℕ) : (fan (n + 2)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_fan])

@[simp] theorem not_isAcyclic_fan (n : ℕ) : ¬ IsAcyclic (fan (n + 2)) := by
  rw [← girth_eq_zero_iff, girth_fan]
  omega

@[simp] theorem not_isTree_fan (n : ℕ) : ¬ IsTree (fan (n + 2)) :=
  not_isTree_of_girth_pos (by rw [girth_fan]; omega)

@[simp] theorem cliqueCoverNum_fan (n : ℕ) :
    (fan n).cliqueCoverNum = max 1 ((path n).cliqueCoverNum) := by
  show (complete 1 ∇g path n).cliqueCoverNum = _
  rw [cliqueCoverNum_join, cliqueCoverNum_complete]

example : (fan 4).E = 7 := by rw [show (4 : ℕ) = 3 + 1 from rfl, E_fan]

example : (fan 5).chromNum = 3 := chromNum_fan 3

example : (fan 6).indepNum = 3 := by rw [show (6 : ℕ) = 5 + 1 from rfl, indepNum_fan]

example : maxDeg (fan 5) = 5 := maxDeg_fan 2

/-- The hub together with an edge of the rim is the largest clique in a wheel. -/
@[simp] theorem cliqueNum_wheel (n : ℕ) : (wheel (n + 4)).cliqueNum = 3 := by
  rw [wheel_eq_join, cliqueNum_join, cliqueNum_complete, cliqueNum_cycle]

@[simp] theorem coverNum_wheel (n : ℕ) : (wheel (n + 3)).coverNum = n + 4 - (n + 3) / 2 := by
  have h := (wheel (n + 3)).coverNum_add_indepNum
  rw [V_wheel, indepNum_wheel] at h
  omega

example : (cycle 7).cliqueNum = 2 := cliqueNum_cycle 3

example : (wheel 5).cliqueNum = 3 := cliqueNum_wheel 1

/-! ### The book graph

`Bₙ = K₂ ∨ Eₙ` is `n` triangles glued along a common edge.  Writing it as a join reduces every
invariant to the two factors. -/

@[simp] theorem E_book (n : ℕ) : (book n).E = 2 * n + 1 := by
  rw [book_eq_join, E_join, E_complete, E_empty, V_complete, V_empty,
    show (2 : ℕ).choose 2 = 1 from rfl]
  omega

/-- The two spine vertices dominate the book. -/
@[simp] theorem maxDeg_book (n : ℕ) : maxDeg (book (n + 1)) = n + 2 := by
  rw [book_eq_join, maxDeg_join (by simp) (by simp), maxDeg_complete, maxDeg_empty, V_complete,
    V_empty]
  omega

/-- Each page vertex sees only the two spine vertices. -/
@[simp] theorem minDeg_book (n : ℕ) : minDeg (book (n + 1)) = 2 := by
  rw [book_eq_join, minDeg_join (by simp) (by simp), minDeg_complete, minDeg_empty, V_complete,
    V_empty]
  omega

@[simp] theorem coverNum_book (n : ℕ) : (book n).coverNum = min (1 + n) 2 := by
  rw [book_eq_join, coverNum_join, coverNum_complete, coverNum_empty, V_complete, V_empty]

@[simp] theorem cliqueCoverNum_book (n : ℕ) : (book n).cliqueCoverNum = max 1 n := by
  rw [book_eq_join, cliqueCoverNum_join, cliqueCoverNum_complete, cliqueCoverNum_empty]

@[simp] theorem domNum_book (n : ℕ) : (book n).domNum = 1 := by
  rw [book_eq_join]
  exact (domNum_join_eq_one_iff _ _).2 (Or.inl (domNum_complete 1))

@[simp] theorem radius_book (n : ℕ) : (book n).radius = 1 :=
  (radius_eq_one_iff_domNum_eq_one (by rw [V_book]; omega)).2 (domNum_book n)

@[simp] theorem numComponents_book (n : ℕ) : (book n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_book n)

example : (book 4).E = 9 := E_book 4

example : maxDeg (book 3) = 4 := maxDeg_book 2

/-! ### The cocktail party graph -/

@[simp] theorem coverNum_cocktailParty (n : ℕ) : (cocktailParty (n + 1)).coverNum = 2 * n := by
  have h := (cocktailParty (n + 1)).coverNum_add_indepNum
  rw [V_cocktailParty, indepNum_cocktailParty] at h
  omega

/-- No single vertex dominates the cocktail party graph — each one misses its own partner — but
any two non-partners do. -/
@[simp] theorem domNum_cocktailParty (n : ℕ) : (cocktailParty (n + 2)).domNum = 2 := by
  have h1 : (cocktailParty (n + 2)).domNum ≤ 2 := by
    have h := domNum_le_indepNum (cocktailParty (n + 2))
    rwa [indepNum_cocktailParty] at h
  have h2 : (cocktailParty (n + 2)).domNum ≠ 1 := by
    intro h
    have h3 := (radius_eq_one_iff_domNum_eq_one
      (G := cocktailParty (n + 2)) (by rw [V_cocktailParty]; omega)).2 h
    rw [radius_cocktailParty] at h3
    omega
  have h3 := domNum_pos (G := cocktailParty (n + 2)) (by rw [V_cocktailParty]; omega)
  omega

example : (cocktailParty 3).coverNum = 4 := coverNum_cocktailParty 2

/-! ### Two binomial coefficients -/

/-! ### Independent sets and cliques in triangular and Kneser graphs -/

/-- **The independence number of a triangular graph**: an independent set in `T(n) = L(Kₙ)` is
a matching of `Kₙ`, so `α(T(n)) = ν(Kₙ) = ⌊n/2⌋`. -/
@[simp] theorem indepNum_johnson_two (n : ℕ) : (johnson n 2).indepNum = n / 2 := by
  rw [← lineGraph_complete, ← matchNum_eq, matchNum_complete]

theorem indepNum_triangular (n : ℕ) : (triangular n).indepNum = n / 2 :=
  indepNum_johnson_two n

@[simp] theorem coverNum_johnson_two (n : ℕ) :
    (johnson n 2).coverNum = n.choose 2 - n / 2 := by
  have h := (johnson n 2).coverNum_add_indepNum
  rw [V_johnson, indepNum_johnson_two] at h
  omega

/-- Complementing turns the triangular graph into the Kneser graph `K(n, 2)`. -/
@[simp] theorem cliqueNum_kneser_two (n : ℕ) : (kneser n 2).cliqueNum = n / 2 := by
  have h := indepNum_johnson_two n
  rw [show johnson n 2 = (kneser n 2)ᶜ from triangular_eq_compl_kneser n,
    indepNum_compl] at h
  exact h

/-- **The clique number of a triangular graph on an even ground set**: the `n - 1` edges at a
fixed vertex of `Kₙ` are pairwise adjacent in `T(n)`, and vertex transitivity caps a clique at
`|V| / α = n - 1`. -/
theorem cliqueNum_johnson_two_even (m : ℕ) :
    (johnson (2 * m + 2) 2).cliqueNum = 2 * m + 1 := by
  have hlow := sub_one_le_cliqueNum_johnson_two (2 * m + 2)
  have hch : (2 * m + 2).choose 2 = (m + 1) * (2 * m + 1) := by
    rw [show 2 * m + 2 = 2 * (m + 1) from by ring, choose_two_two_mul,
      show 2 * (m + 1) - 1 = 2 * m + 1 from by omega]
  have hvt : IsVertexTransitive (johnson (2 * m + 2) 2) :=
    isVertexTransitive_triangular (2 * m + 2)
  have h := indepNum_mul_cliqueNum_le_V hvt
  rw [V_johnson, indepNum_johnson_two, show (2 * m + 2) / 2 = m + 1 from by omega, hch] at h
  have hup := Nat.le_of_mul_le_mul_left h m.succ_pos
  omega

theorem cliqueNum_triangular_even (m : ℕ) :
    (triangular (2 * m + 2)).cliqueNum = 2 * m + 1 :=
  cliqueNum_johnson_two_even m

/-- The independence number of the Kneser graph `K(2m+2, 2)`, by complementation. -/
theorem indepNum_kneser_two_even (m : ℕ) :
    (kneser (2 * m + 2) 2).indepNum = 2 * m + 1 := by
  have h := cliqueNum_johnson_two_even m
  rw [show johnson (2 * m + 2) 2 = (kneser (2 * m + 2) 2)ᶜ from
    triangular_eq_compl_kneser (2 * m + 2), cliqueNum_compl] at h
  exact h

theorem chromNum_johnson_two_even_lower (m : ℕ) :
    2 * m + 1 ≤ (johnson (2 * m + 2) 2).chromNum := by
  have h := cliqueNum_le_chromNum (johnson (2 * m + 2) 2)
  rw [cliqueNum_johnson_two_even] at h
  exact h

/-! ### Independent sets in the hypercube -/

/-- **The independence number of a hypercube**: `α(Qₙ) = 2ⁿ⁻¹`.  One half comes from
`|V| ≤ χ · α` with `χ = 2`, the other from `2α ≤ |V|`, which holds in any vertex-transitive
graph with an edge. -/
@[simp] theorem indepNum_hypercube (n : ℕ) : (hypercube (n + 1)).indepNum = 2 ^ n := by
  have h1 := two_mul_indepNum_hypercube_le n
  have h2 := V_le_chromNum_mul_indepNum (hypercube (n + 1))
  rw [V_hypercube, chromNum_hypercube] at h2
  have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  omega

@[simp] theorem coverNum_hypercube (n : ℕ) : (hypercube (n + 1)).coverNum = 2 ^ n := by
  have h := (hypercube (n + 1)).coverNum_add_indepNum
  rw [V_hypercube, indepNum_hypercube] at h
  have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  omega

/-- The hypercube is bipartite with both sides of the bipartition as large as possible. -/
theorem two_mul_indepNum_hypercube (n : ℕ) :
    2 * (hypercube (n + 1)).indepNum = (hypercube (n + 1)).V := by
  rw [indepNum_hypercube, V_hypercube]
  ring

theorem indepNum_eq_coverNum_hypercube (n : ℕ) :
    (hypercube (n + 1)).indepNum = (hypercube (n + 1)).coverNum := by
  rw [indepNum_hypercube, coverNum_hypercube]

example : (hypercube 4).indepNum = 8 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, indepNum_hypercube]; norm_num

example : (complete 7).matchNum = 3 := by rw [matchNum_complete]

example : (complete 8).matchNum = 4 := by rw [matchNum_complete]

example : (triangular 6).indepNum = 3 := by rw [indepNum_triangular]

example : (triangular 6).cliqueNum = 5 := by
  rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, cliqueNum_triangular_even]

example : (kneser 6 2).cliqueNum = 3 := by rw [cliqueNum_kneser_two]

example : 5 ≤ (complete 5).edgeChromNum := by
  have h := le_edgeChromNum_complete_odd 1
  norm_num at h
  exact h

/-! ### Cliques in the hypercube and the Petersen graph -/

/-- A bipartite graph with an edge has clique number exactly two. -/
@[simp] theorem cliqueNum_hypercube (n : ℕ) : (hypercube (n + 1)).cliqueNum = 2 := by
  have h1 := cliqueNum_le_chromNum (hypercube (n + 1))
  rw [chromNum_hypercube] at h1
  have h2 : 2 ≤ (hypercube (n + 1)).cliqueNum := by
    refine two_le_cliqueNum_of_E_pos ?_
    have h := E_hypercube (n + 1)
    have hp : 0 < (n + 1) * 2 ^ (n + 1) := Nat.mul_pos n.succ_pos (Nat.two_pow_pos _)
    omega
  omega

/-- Three colours suffice for the Petersen graph, so a colour class has at least four
of its ten vertices. -/
theorem four_le_indepNum_petersen : 4 ≤ petersen.indepNum := by
  have h := V_le_chromNum_mul_indepNum petersen
  rw [V_petersen, chromNum_petersen] at h
  omega

/-- **The Petersen graph is triangle-free**: it is vertex-transitive with `α ≥ 4`, and
`α · ω ≤ 10` leaves no room for a triangle. -/
@[simp] theorem cliqueNum_petersen : petersen.cliqueNum = 2 := by
  have h := indepNum_mul_cliqueNum_le_V isVertexTransitive_petersen
  rw [V_petersen] at h
  have h2 : 2 ≤ petersen.cliqueNum :=
    two_le_cliqueNum_of_E_pos (by rw [E_petersen]; omega)
  have h5 : 4 * petersen.cliqueNum ≤ petersen.indepNum * petersen.cliqueNum :=
    Nat.mul_le_mul_right _ four_le_indepNum_petersen
  omega

theorem four_le_girth_petersen : 4 ≤ petersen.girth :=
  four_le_girth_of_cliqueNum (by rw [cliqueNum_petersen])
    (not_isAcyclic_of_isConnected isConnected_petersen (by
      intro h
      have := h.E_add_one
      rw [E_petersen, V_petersen] at this
      omega))

@[simp] theorem numComponents_petersen : petersen.numComponents = 1 :=
  numComponents_eq_one_of_isConnected isConnected_petersen

/-! ### Connectivity of the strongly regular families -/

@[simp] theorem numComponents_triangular {n : ℕ} (hn : 4 ≤ n) :
    (triangular n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_triangular hn)

@[simp] theorem numComponents_cocktailParty (n : ℕ) :
    (cocktailParty (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_cocktailParty n)

theorem numComponents_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_paley q hq hq5)

/-! ### Prisms and ladders -/

@[simp] theorem cliqueNum_ladder (n : ℕ) : (ladder (n + 2)).cliqueNum = 2 := by
  rw [show ladder (n + 2) = path (n + 2) □g complete 2 from rfl,
    cliqueNum_cartesianProduct (by rw [V_path]; omega) (by rw [V_complete]; omega),
    cliqueNum_path, cliqueNum_complete]
  norm_num

/-- A prism over a cycle of length at least four is triangle-free. -/
@[simp] theorem cliqueNum_prism (n : ℕ) : (prism (n + 4)).cliqueNum = 2 := by
  rw [show prism (n + 4) = cycle (n + 4) □g complete 2 from rfl,
    cliqueNum_cartesianProduct (by rw [V_cycle]; omega) (by rw [V_complete]; omega),
    cliqueNum_cycle, cliqueNum_complete]
  norm_num

/-- The triangular prism `K₃ □ K₂` does contain a triangle. -/
@[simp] theorem cliqueNum_prism_three : (prism 3).cliqueNum = 3 := by
  rw [show prism 3 = cycle 3 □g complete 2 from rfl,
    cliqueNum_cartesianProduct (by rw [V_cycle]; omega) (by rw [V_complete]; omega),
    cliqueNum_cycle_three, cliqueNum_complete]
  norm_num

/-- An odd prism needs three colours: the rim already does. -/
@[simp] theorem chromNum_prism_odd (m : ℕ) : (prism (2 * m + 3)).chromNum = 3 := by
  rw [show prism (2 * m + 3) = cycle (2 * m + 3) □g complete 2 from rfl,
    chromNum_cartesianProduct (by rw [V_cycle]; omega) (by rw [V_complete]; omega),
    chromNum_cycle_odd, chromNum_complete]
  norm_num

/-- **The independence number of a ladder**: `α(Pₙ □ K₂) = n`.  A ladder is bipartite, which
gives `2α ≥ |V|`, and an independent set meets each rung at most once, which gives `α ≤ n`. -/
@[simp] theorem indepNum_ladder (n : ℕ) : (ladder n).indepNum = n := by
  have hc : (complete 2).indepNum = 1 := by rw [indepNum_complete]; norm_num
  have hup : (ladder n).indepNum ≤ (path n).V * (complete 2).indepNum :=
    indepNum_cartesianProduct_le _ _
  rw [V_path, hc, Nat.mul_one] at hup
  cases n with
  | zero => omega
  | succ m =>
    have h := V_le_chromNum_mul_indepNum (ladder (m + 1))
    rw [V_ladder, chromNum_ladder] at h
    omega

@[simp] theorem coverNum_ladder (n : ℕ) : (ladder n).coverNum = n := by
  have h := (ladder n).coverNum_add_indepNum
  rw [V_ladder, indepNum_ladder] at h
  omega

/-- **The independence number of an even prism**: same argument, with the even cycle supplying
the bipartition. -/
@[simp] theorem indepNum_prism_even (m : ℕ) : (prism (2 * m + 4)).indepNum = 2 * m + 4 := by
  have hc : (complete 2).indepNum = 1 := by rw [indepNum_complete]; norm_num
  have hup : (prism (2 * m + 4)).indepNum ≤ (cycle (2 * m + 4)).V * (complete 2).indepNum :=
    indepNum_cartesianProduct_le _ _
  rw [V_cycle, hc, Nat.mul_one] at hup
  have h := V_le_chromNum_mul_indepNum (prism (2 * m + 4))
  rw [V_prism, chromNum_prism_even] at h
  omega

@[simp] theorem coverNum_prism_even (m : ℕ) : (prism (2 * m + 4)).coverNum = 2 * m + 4 := by
  have h := (prism (2 * m + 4)).coverNum_add_indepNum
  rw [V_prism, indepNum_prism_even] at h
  omega

/-- An odd prism is vertex-transitive and triangle-free, so its independent sets are still
capped by one vertex per rung; one rung has to be missed entirely. -/
theorem indepNum_prism_odd_le (m : ℕ) : (prism (2 * m + 3)).indepNum ≤ 2 * m + 3 := by
  have hc : (complete 2).indepNum = 1 := by rw [indepNum_complete]; norm_num
  have hup : (prism (2 * m + 3)).indepNum ≤ (cycle (2 * m + 3)).V * (complete 2).indepNum :=
    indepNum_cartesianProduct_le _ _
  rw [V_cycle, hc, Nat.mul_one] at hup
  omega

example : (ladder 5).indepNum = 5 := by rw [indepNum_ladder]

example : (prism 6).indepNum = 6 := by
  rw [show (6 : ℕ) = 2 * 1 + 4 from rfl, indepNum_prism_even]

example : (prism 5).chromNum = 3 := by
  rw [show (5 : ℕ) = 2 * 1 + 3 from rfl, chromNum_prism_odd]

example : (hypercube 4).cliqueNum = 2 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, cliqueNum_hypercube]

example : (cycle 6).domNum = 2 := by rw [show (6 : ℕ) = 3 + 3 from rfl, domNum_cycle]

example : (cycle 7).domNum = 3 := by rw [show (7 : ℕ) = 4 + 3 from rfl, domNum_cycle]

/-! ### The balanced complete multipartite graph `K_{m×d}`

`completeMultipartite (List.replicate m d)` is the complete multipartite graph with `m` parts
of `d` vertices each — the cocktail party graph when `d = 2` and `Kₘ` when `d = 1`.  It is
`Kₘ[Eᵈ]`, the lexicographic product recorded by `completeMultipartite_replicate`, and that
identity carries every product formula across in one step. -/

/-- Peeling one part off a balanced complete multipartite graph. -/
theorem completeMultipartite_replicate_succ (m d : ℕ) :
    completeMultipartite (List.replicate (m + 1) d)
      = empty d ∇g completeMultipartite (List.replicate m d) := by
  rw [List.replicate_succ, completeMultipartite_cons]

@[simp] theorem V_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m d)).V = m * d := by
  rw [completeMultipartite_replicate, V_lexProduct, V_complete, V_empty]

@[simp] theorem E_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m d)).E = m.choose 2 * (d * d) := by
  rw [completeMultipartite_replicate, E_lexProduct, E_complete, E_empty, V_empty, V_complete,
    Nat.mul_zero, Nat.add_zero, Nat.mul_comm]

/-- `K_{m×d}` is regular of degree `(m - 1) d`. -/
@[simp] theorem degSequence_completeMultipartite_replicate (m d : ℕ) :
    degSequence (completeMultipartite (List.replicate m d))
      = List.replicate (m * d) ((m - 1) * d) := by
  rw [completeMultipartite_replicate,
    degSequence_lexProduct (degSequence_complete m) (degSequence_empty d), Nat.add_zero]

theorem maxDeg_completeMultipartite_replicate {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    maxDeg (completeMultipartite (List.replicate m d)) = (m - 1) * d := by
  rw [completeMultipartite_replicate,
    maxDeg_lexProduct (by rw [V_complete]; omega) (by rw [V_empty]; omega),
    maxDeg_complete, maxDeg_empty, V_empty, Nat.add_zero]

theorem minDeg_completeMultipartite_replicate {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    minDeg (completeMultipartite (List.replicate m d)) = (m - 1) * d := by
  rw [completeMultipartite_replicate,
    minDeg_lexProduct (by rw [V_complete]; omega) (by rw [V_empty]; omega),
    minDeg_complete, minDeg_empty, V_empty, Nat.add_zero]

@[simp] theorem numComponents_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 1))).numComponents = 1 := by
  rw [completeMultipartite_replicate_succ]
  exact numComponents_join (by rw [V_empty]; omega)
    (by rw [V_completeMultipartite_replicate]; positivity)

theorem isConnected_completeMultipartite_replicate (m d : ℕ) :
    IsConnected (completeMultipartite (List.replicate (m + 2) (d + 1))) := by
  rw [completeMultipartite_replicate_succ]
  exact isConnected_join (by rw [V_empty]; omega)
    (by rw [V_completeMultipartite_replicate]; positivity)

/-- With at least two parts of at least two vertices, two vertices of the same part are at
distance two, and nothing is further away. -/
@[simp] theorem diameter_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 2))).diameter = 2 := by
  rw [completeMultipartite_replicate_succ]
  refine diameter_join_left (by rw [V_completeMultipartite_replicate]; positivity) ?_
  rw [E_empty, V_empty]
  exact Nat.choose_pos (by omega)

private theorem domNum_completeMultipartite_replicate_ne_one (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 1) (d + 2))).domNum ≠ 1 := by
  induction m with
  | zero =>
    rw [show List.replicate 1 (d + 2) = [d + 2] from rfl, completeMultipartite_singleton,
      domNum_empty]
    omega
  | succ m ih =>
    rw [completeMultipartite_replicate_succ]
    intro h
    rcases (domNum_join_eq_one_iff _ _).1 h with h | h
    · rw [domNum_empty] at h; omega
    · exact ih h

/-- **The domination number of `K_{m×d}`**: one vertex dominates only its own part's
complement, so two are needed — and two suffice. -/
@[simp] theorem domNum_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 2))).domNum = 2 := by
  rw [completeMultipartite_replicate_succ]
  exact domNum_join_eq_two (by rw [V_empty]; omega)
    (by rw [V_completeMultipartite_replicate]; positivity)
    (by rw [domNum_empty]; omega) (domNum_completeMultipartite_replicate_ne_one m d)

@[simp] theorem radius_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 2))).radius = 2 := by
  have hV : 1 < (completeMultipartite (List.replicate (m + 2) (d + 2))).V := by
    rw [V_completeMultipartite_replicate]; nlinarith
  have h1 : (completeMultipartite (List.replicate (m + 2) (d + 2))).radius ≠ 1 := by
    intro h
    rw [radius_eq_one_iff_domNum_eq_one hV, domNum_completeMultipartite_replicate] at h
    omega
  have h2 := radius_le_diameter (completeMultipartite (List.replicate (m + 2) (d + 2)))
  rw [diameter_completeMultipartite_replicate] at h2
  have hc : IsConnected (completeMultipartite (List.replicate (m + 2) (d + 2))) :=
    isConnected_completeMultipartite_replicate m (d + 1)
  have h3 := radius_pos hc hV
  omega

/-- Three parts give a triangle. -/
@[simp] theorem girth_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 3) (d + 1))).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [completeMultipartite_replicate, cliqueNum_lexProduct, cliqueNum_complete, cliqueNum_empty,
    show min (d + 1) 1 = 1 from by omega]
  omega

example : (cocktailParty 4).diameter = 2 := by
  show (completeMultipartite (List.replicate 4 2)).diameter = 2
  rw [show (4 : ℕ) = 2 + 2 from rfl, show (2 : ℕ) = 0 + 2 from rfl,
    diameter_completeMultipartite_replicate]

example : (completeMultipartite (List.replicate 3 3)).E = 27 := by
  rw [E_completeMultipartite_replicate]; norm_num

/-- The hypercube has a perfect matching (flip the last coordinate). -/
@[simp] theorem matchNum_hypercube (n : ℕ) : (hypercube (n + 1)).matchNum = 2 ^ n := by
  have hUB : (hypercube (n + 1)).matchNum ≤ 2 ^ n := by
    have := (hypercube (n + 1)).two_mul_matchNum_le_V
    rw [V_hypercube] at this
    omega
  -- Lower bound via exhibiting a matching of size 2^n
  -- The edges {(x ++ [false], x ++ [true]) | x : Fin n → Bool} form a perfect matching
  -- in hypercube (n+1), giving indepNum (lineGraph (hypercube (n+1))) ≥ 2^n
  have hLB : 2 ^ n ≤ (hypercube (n + 1)).matchNum := by
    rw [matchNum_eq]
    show 2 ^ n ≤ indepNum (lineGraph (hypercube (n + 1)))
    rw [show (hypercube (n + 1) : IsoGraph) = ⟦CGraph.hypercube (n + 1)⟧ from rfl, lineGraph_mk,
      indepNum_mk]
    
    let v0 : (Fin n → Bool) → (Fin (n + 1) → Bool) := fun x => Fin.cons false x
    let v1 : (Fin n → Bool) → (Fin (n + 1) → Bool) := fun x => Fin.cons true x
    -- Each (v0 x, v1 x) is an edge of hypercube (n+1)
    have huv_adj : ∀ x : Fin n → Bool, (CGraph.hypercube (n + 1)).Adj (v0 x) (v1 x) := by
      intro x
      rw [CGraph.hypercube_adj]
      dsimp [v0, v1]
      have : (Finset.univ.filter (fun i : Fin (n + 1) =>
          ¬(Fin.cons false x : Fin (n + 1) → Bool) i
            = (Fin.cons true x : Fin (n + 1) → Bool) i)) = {0} := by
        ext i
        simp [Fin.cons]
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      simp [this]
    -- Construct the matching edges as vertices of the line graph
    let edgeVertex : (Fin n → Bool) → (CGraph.lineGraph (CGraph.hypercube (n + 1))).V := fun x =>
      ⟨s(v0 x, v1 x), by
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
        exact huv_adj x⟩
    -- The Finset of these 2^n vertices
    let S : Finset (CGraph.lineGraph (CGraph.hypercube (n + 1))).V := Finset.univ.image edgeVertex
    -- Helper: v0 is injective
    have hv0_inj : Function.Injective v0 := by
      intro x y h
      simp [v0] at h
      exact h
    -- Disjointness: for x ≠ y, edges {v0 x, v1 x} and {v0 y, v1 y} share no vertex
    have hdisjoint : ∀ x y : (Fin n → Bool), x ≠ y →
        ¬∃ v : Fin (n + 1) → Bool, v ∈ (s(v0 x, v1 x) : Sym2 (Fin (n + 1) → Bool)) ∧
          v ∈ (s(v0 y, v1 y) : Sym2 (Fin (n + 1) → Bool)) := by
      intro x y hxy ⟨v, hv1, hv2⟩
      rw [Sym2.mem_iff] at hv1 hv2
      rcases hv1 with rfl | rfl
      · -- v = v0 x
        rcases hv2 with h1 | h1
        · exact hxy (hv0_inj h1)
        · have h2 : (false : Bool) = true := congr_fun h1 0
          exact absurd h2 (by decide)
      · -- v = v1 x
        rcases hv2 with h1 | h1
        · have h2 : (true : Bool) = false := congr_fun h1 0
          exact absurd h2 (by decide)
        · exact hxy (by simpa [v1] using h1)
    -- Show S is an independent set in lineGraph
    have hS_indep : (CGraph.lineGraph (CGraph.hypercube (n + 1))).toSimple.IsIndepSet S := by
      intro e he f hf haf
      simp only [S] at he hf
      rw [Finset.mem_coe, Finset.mem_image] at he hf
      obtain ⟨x, _, rfl⟩ := he
      obtain ⟨y, _, rfl⟩ := hf
      simp [CGraph.toSimple_adj, CGraph.lineGraph_adj]
      intro _
      have hne : x ≠ y := fun h => haf (h ▸ rfl)
      intro v hv hx1v
      exact hdisjoint x y hne ⟨v, hv, hx1v⟩
    -- edgeVertex is injective
    have hinj : Function.Injective edgeVertex := by
      intro x y hxy
      have hsym2 : s(v0 x, v1 x) = s(v0 y, v1 y) := Subtype.ext_iff.mp hxy
      rcases Sym2.eq_iff.1 hsym2 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hv0_inj h1
      · exfalso; have h2 : (false : Bool) = true := congr_fun h1 0
        exact absurd h2 (by decide)
    have hS_card : S.card = 2 ^ n := by
      show Finset.card (Finset.image edgeVertex Finset.univ) = 2 ^ n
      rw [Finset.card_image_of_injective _ hinj]
      simp [Finset.card_univ]
    exact hS_card ▸ hS_indep.card_le_indepNum
  omega

/-- **A balanced complete multipartite graph with at least two parts has a near-perfect
matching.** -/
theorem matchNum_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 1))).matchNum
      = (m + 2) * (d + 1) / 2 := by
  apply le_antisymm
  · have h1 := two_mul_matchNum_le_V (completeMultipartite (List.replicate (m + 2) (d + 1)))
    rw [V_completeMultipartite, List.sum_replicate] at h1
    simp at h1
    omega
  · -- Number the vertices round robin: `j` sits in part `j % k`, slot `j / k`.  Consecutive
    -- numbers land in different parts, so the pairs `{2t, 2t + 1}` are disjoint edges.
    set k := m + 2 with hk
    set s := d + 1 with hs
    set H : CGraph := CGraph.completeMultipartite (List.replicate k s) with hH
    rw [show (completeMultipartite (List.replicate k s) : IsoGraph) = ⟦H⟧ from rfl, matchNum_mk]
    have hlen : (List.replicate k s).length = k := List.length_replicate
    have hget : ∀ (i : Fin k), (List.replicate k s).get ⟨i, by rw [hlen]; exact i.2⟩ = s := by
      intro i; simp [List.getElem_replicate]
    let vertex : Fin k → Fin s → H.V := fun i a =>
      ⟨⟨i, by rw [hlen]; exact i.2⟩, Fin.cast (hget i).symm a⟩
    have hadj : ∀ (i j : Fin k) (a b : Fin s), H.Adj (vertex i a) (vertex j b) ↔ i ≠ j := by
      intro i j a b
      simp [vertex, H, CGraph.completeMultipartite_adj]
      simp [Fin.ext_iff]
    let f : Fin (k * s) → H.V := fun ⟨j, hj⟩ =>
      vertex ⟨j % k, Nat.mod_lt _ (by omega : 0 < k)⟩ ⟨j / k, Nat.div_lt_of_lt_mul hj⟩
    have hf_fst_val : ∀ j : Fin (k * s), (f j).1.val = j.val % k := by
      intro j; simp [f, vertex]
    have hf_snd_val : ∀ j : Fin (k * s), (f j).2.val = j.val / k := by
      intro j; simp [f, vertex]
    have hf_inj : Function.Injective f := by
      intro j1 j2 hfeq
      have hmod : j1.val % k = j2.val % k := by
        have h1 := congr_arg (fun v : H.V => v.1.val) hfeq
        simp only [hf_fst_val] at h1
        exact h1
      have hdiv : j1.val / k = j2.val / k := by
        have h2 := congr_arg (fun v : H.V => v.2.val) hfeq
        simp only [hf_snd_val] at h2
        exact h2
      refine Fin.ext ?_
      have h1' := Nat.div_add_mod j1.val k
      have h2' := Nat.div_add_mod j2.val k
      rw [hmod, hdiv] at h1'
      linarith [h2']
    have hbound : ∀ t : Fin (k * s / 2), 2 * (t : ℕ) + 1 < k * s := by
      intro t
      have ht : (t : ℕ) < k * s / 2 := t.2
      have := Nat.div_add_mod (k * s) 2
      omega
    have hbound' : ∀ t : Fin (k * s / 2), 2 * (t : ℕ) < k * s := fun t ↦ by
      have := hbound t; omega
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun t : Fin (k * s / 2) ↦ f ⟨2 * (t : ℕ), hbound' t⟩)
      (fun t : Fin (k * s / 2) ↦ f ⟨2 * (t : ℕ) + 1, hbound t⟩) ?_ ?_)
    · -- `2t` and `2t + 1` are different mod `k ≥ 2`, so they lie in different parts.
      have hpart : ∀ x y : Fin (k * s), x.val % k ≠ y.val % k → H.Adj (f x) (f y) := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hne
        simp only [f]
        rw [hadj]
        exact fun h ↦ hne (congrArg Fin.val h)
      intro t
      refine hpart ⟨2 * (t : ℕ), hbound' t⟩ ⟨2 * (t : ℕ) + 1, hbound t⟩ ?_
      dsimp only
      intro heq
      have := Nat.modEq_iff_dvd.mp (Nat.ModEq.symm heq)
      simp at this
      exact absurd (Int.le_of_dvd (by omega : (0 : ℤ) < 1) this) (by omega)
    · intro t t' htt'
      have hfval : ∀ x y : Fin (k * s), f x = f y → (x : ℕ) = (y : ℕ) :=
        fun x y he ↦ congrArg Fin.val (hf_inj he)
      have hne : ∀ (x y : ℕ) (hx : x < k * s) (hy : y < k * s), x ≠ y →
          f ⟨x, hx⟩ ≠ f ⟨y, hy⟩ :=
        fun x y hx hy hxy he ↦ hxy (hfval ⟨x, hx⟩ ⟨y, hy⟩ he)
      have ht : (t : ℕ) ≠ (t' : ℕ) := fun hval ↦ htt' (Fin.ext hval)
      exact ⟨hne _ _ (hbound' t) (hbound' t') (by omega),
        hne _ _ (hbound' t) (hbound t') (by omega),
        hne _ _ (hbound t) (hbound' t') (by omega),
        hne _ _ (hbound t) (hbound t') (by omega)⟩

/-- The cocktail party graph `K_{n×2}` has a perfect matching for `n ≥ 2`. -/
@[simp] theorem matchNum_cocktailParty (n : ℕ) : (cocktailParty (n + 2)).matchNum = n + 2 := by
  rw [show (cocktailParty (n + 2) : IsoGraph)
      = completeMultipartite (List.replicate (n + 2) 2) from rfl,
    matchNum_completeMultipartite_replicate n 1]
  omega


/-! ### Degrees and radius of the ladder -/

@[simp] theorem maxDeg_ladder (n : ℕ) : maxDeg (ladder (n + 3)) = 3 := by
  rw [show ladder (n + 3) = path (n + 3) □g complete 2 from rfl,
    maxDeg_cartesianProduct (by rw [V_path]; omega) (by rw [V_complete]; omega),
    maxDeg_path, maxDeg_complete]

@[simp] theorem minDeg_ladder (n : ℕ) : minDeg (ladder (n + 2)) = 2 := by
  rw [show ladder (n + 2) = path (n + 2) □g complete 2 from rfl,
    minDeg_cartesianProduct (by rw [V_path]; omega) (by rw [V_complete]; omega),
    minDeg_path, minDeg_complete]

/-- **The radius of a ladder**: the centre of the underlying path, on either rail. -/
@[simp] theorem radius_ladder (n : ℕ) : (ladder (n + 1)).radius = (n + 1) / 2 + 1 := by
  rw [show ladder (n + 1) = path (n + 1) □g complete 2 from rfl,
    radius_cartesianProduct (isConnected_path n) (isConnected_complete 1), radius_path,
    show complete 2 = complete (0 + 2) from rfl, radius_complete]

/-! ### Clique cover numbers from maximum matchings

`θ ≤ |V| - ν` pairs up as many vertices as a maximum matching allows and leaves the rest as
singletons; against `|V| ≤ θ · ω` it is tight for every triangle-free graph with a maximum
matching, and against `α ≤ θ` it is tight for the hypercube. -/

/-- **The clique cover number of a hypercube**: `θ(Qₙ) = 2ⁿ⁻¹`, the perfect matching. -/
@[simp] theorem cliqueCoverNum_hypercube (n : ℕ) :
    (hypercube (n + 1)).cliqueCoverNum = 2 ^ n := by
  have h1 := cliqueCoverNum_le_V_sub_matchNum (hypercube (n + 1))
  rw [V_hypercube, matchNum_hypercube] at h1
  have h2 := indepNum_le_cliqueCoverNum (hypercube (n + 1))
  rw [indepNum_hypercube] at h2
  have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  omega

/-- **The clique cover number of a wheel**: the hub joins one of the rim's cliques, so the
count is the rim's. -/
@[simp] theorem cliqueCoverNum_wheel (n : ℕ) :
    (wheel (n + 4)).cliqueCoverNum = (n + 5) / 2 := by
  rw [wheel_eq_join, show complete 1 = complete (0 + 1) from rfl, cliqueCoverNum_join,
    cliqueCoverNum_complete, cliqueCoverNum_cycle]
  omega

example : (hypercube 4).cliqueCoverNum = 8 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, cliqueCoverNum_hypercube]; norm_num

example : (cycle 7).cliqueCoverNum = 4 := by
  rw [show (7 : ℕ) = 3 + 4 from rfl, cliqueCoverNum_cycle]

example : (ladder 4).radius = 3 := by rw [show (4 : ℕ) = 3 + 1 from rfl, radius_ladder]

/-- The Petersen graph has independence number 4. -/
@[simp] theorem indepNum_petersen : petersen.indepNum = 4 := by
  unfold IsoGraph.petersen IsoGraph.indepNum IsoGraph.kneser
  rw [Quotient.lift_mk]
  rw [← CGraph.cliqueNum_compl]
  have heq : ((CGraph.kneser 5 2)ᶜ) ≃cg CGraph.johnson 5 2 :=
    CGraph.johnsonTwoIso 5 |>.symm
  have hclique_iso :
      ((CGraph.kneser 5 2)ᶜ).cliqueNum = (CGraph.johnson 5 2).cliqueNum := by
    unfold CGraph.cliqueNum
    exact SimpleGraph.Iso.cliqueNum_eq (CGraph.Iso.toSimpleIso heq)
  rw [hclique_iso]
  -- Now goal: CGraph.cliqueNum (johnson 5 2) = 4
  -- Use cliqueCount to get a decidable characterization
  have h4 : 0 < (CGraph.johnson 5 2).cliqueCount 4 ↔ 4 ≤ (CGraph.johnson 5 2).cliqueNum :=
    CGraph.cliqueCount_pos_iff (CGraph.johnson 5 2) 4
  have h5 : (CGraph.johnson 5 2).cliqueCount 5 = 0 ↔ (CGraph.johnson 5 2).cliqueNum < 5 :=
    CGraph.cliqueCount_eq_zero_iff (CGraph.johnson 5 2) 5
  have hc4 : 0 < (CGraph.johnson 5 2).cliqueCount 4 := by
    rw [CGraph.cliqueCount_eq_card_cliqueFinset]
    native_decide
  have hc5 : (CGraph.johnson 5 2).cliqueCount 5 = 0 := by
    rw [CGraph.cliqueCount_eq_card_cliqueFinset]
    native_decide
  have h4' : 4 ≤ (CGraph.johnson 5 2).cliqueNum := h4.mp hc4
  have h5' : (CGraph.johnson 5 2).cliqueNum < 5 := h5.mp hc5
  omega

/-- The Petersen graph has domination number 3. -/
@[simp] theorem domNum_petersen : petersen.domNum = 3 := by
  rw [petersen, kneser, IsoGraph.domNum_mk]
  let s : Finset (CGraph.kneser 5 2).V :=
    {⟨{0,2}, by decide⟩, ⟨{0,4}, by decide⟩, ⟨{2,4}, by decide⟩}
  have hcard : s.card = 3 := by decide
  have hdom : (CGraph.kneser 5 2).IsDominatingSet s := by
    unfold CGraph.IsDominatingSet
    decide
  have hle : (CGraph.kneser 5 2).domNum ≤ 3 :=
    le_trans (CGraph.domNum_le_card_of_isDominatingSet hdom) (by rw [hcard])
  have hcardV : FinEnum.card (CGraph.kneser 5 2).V = 10 := CGraph.card_petersen
  have hmaxDeg : (CGraph.kneser 5 2).maxDeg = 3 := IsoGraph.maxDeg_kneser 5 2 (by omega) (by omega)
  have hlow : 3 ≤ (CGraph.kneser 5 2).domNum := by
    have := CGraph.card_le_domNum_mul_maxDeg_add_one (CGraph.kneser 5 2)
    rw [hcardV, hmaxDeg] at this; omega
  omega

/-- The Petersen graph is triangle-free, so a clique cover is a cover by edges and vertices. -/
@[simp] theorem cliqueCoverNum_petersen : petersen.cliqueCoverNum = 5 := by
  --Lower bound: ≥ 5 from V = 10, cliqueNum = 2
  have hV : petersen.V = 10 := by
    rw [petersen, V_kneser]; decide
  have hclique : petersen.cliqueNum = 2 := cliqueNum_petersen
  have hlow : 5 ≤ petersen.cliqueCoverNum := by
    calc 5 = 10 / 2 := by decide
    _ ≤ petersen.cliqueCoverNum := by
      have := V_le_cliqueCoverNum_mul_cliqueNum petersen
      rw [hV, hclique] at this; omega
  --Upper bound: ≤ 5 from explicit 5-clique cover of petersen (5-colouring of petersenᶜ)
  have hupp : petersen.cliqueCoverNum ≤ 5 := by
    rw [cliqueCoverNum_eq]
    rw [petersen]
    rw [← triangular_eq_compl_kneser]
    show chromNum (triangular 5) ≤ 5
    show chromNum (johnson 5 2) ≤ 5
    simp [johnson, chromNum_mk]
    rw [CGraph.chromNum_le_iff_colorable]
    -- Coloring: color each 2-subset by (sum of its elements : Fin 5)
    let coloring : (CGraph.johnson 5 2).V → Fin 5 := fun ⟨s, hs⟩ => s.sum id
    exact ⟨coloring, by native_decide⟩
  omega

/-- The rungs of a ladder form a perfect matching. -/
@[simp] theorem matchNum_ladder (n : ℕ) : (ladder n).matchNum = n := by
  rw [matchNum_eq]
  have hup : (lineGraph (ladder n)).indepNum ≤ n := by
    have := (ladder n).two_mul_matchNum_le_V
    rw [matchNum_eq, V_ladder] at this
    omega
  -- Lower bound: construct independent set of size n in lineGraph(ladder n)
  -- The n rungs form a matching, so their edge-vertices form an independent set in the line graph.
  -- Work at IsoGraph level: ladder n = cartesianProduct (path n) (complete 2)
  -- lineGraph(ladder n) has vertices = edges of ladder n.
  -- The rungs (edges ((i,0),(i,1)) for i : Fin n) are n edges that are pairwise disjoint,
  -- so they form an independent set in the line graph.
  have hlower : n ≤ (lineGraph (ladder n)).indepNum := by
    show n ≤ indepNum (lineGraph (path n □g complete 2))
    rw [show path n = ⟦CGraph.path n⟧ from rfl, show complete 2 = ⟦CGraph.complete 2⟧ from rfl]
    rw [cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    -- The rungs are edges between (i,0) and (i,1) in the ladder
    -- In the line graph, these n vertices form an independent set
    let G' : CGraph := (CGraph.path n).cartesianProduct (CGraph.complete 2)
    -- Edge set membership for rungs
    have hrung_mem : ∀ i : Fin n,
        s((i, (0 : Fin 2)), (i, (1 : Fin 2))) ∈ G'.toSimple.edgeSet := by
      intro i
      simp [G', CGraph.cartesianProduct_adj, CGraph.complete_adj, SimpleGraph.mem_edgeSet]
    -- The vertices of lineGraph G' corresponding to rungs
    let rungVer : Fin n → (CGraph.lineGraph G').V := fun i =>
      ⟨s((i, (0 : Fin 2)), (i, (1 : Fin 2))), hrung_mem i⟩
    -- rungVer is injective
    have hrungVer_inj : Function.Injective rungVer := by
      intro i j hij
      have hval : s((i, (0 : Fin 2)), (i, (1 : Fin 2)))
          = s((j, (0 : Fin 2)), (j, (1 : Fin 2))) :=
        congr_arg Subtype.val hij
      rcases Sym2.eq_iff.1 hval with h | h
      · exact congr_arg Prod.fst h.1
      · exact congr_arg Prod.fst h.1
    -- The image of rungVer is an independent set in lineGraph G'
    let S : Finset (CGraph.lineGraph G').V := Finset.univ.image rungVer
    have hS_card : S.card = n := by
      rw [Finset.card_image_of_injective _ hrungVer_inj, Finset.card_fin]
    have hnotadj : ∀ i j : Fin n, i ≠ j →
        ¬(CGraph.lineGraph G').Adj (rungVer i) (rungVer j) := by
      intro i j hij
      show ¬_
      rw [CGraph.lineGraph_adj]
      simp [rungVer]
      intro h1 h2
      exact ⟨⟨by rintro h; exact hij (congr_arg Prod.fst h),
              by rintro h; exact hij (congr_arg Prod.fst h)⟩,
             by rintro h; exact hij (congr_arg Prod.fst h),
             by rintro h; exact hij (congr_arg Prod.fst h)⟩
    have hS_indep :
        (CGraph.lineGraph G').toSimple.IsIndepSet (S : Set (CGraph.lineGraph G').V) := by
      intro e he f hf hef
      simp [S] at he hf
      obtain ⟨i, hi, rfl⟩ := he
      obtain ⟨j, hj, rfl⟩ := hf
      have : i ≠ j := by intro heq; apply hef; exact heq ▸ rfl
      exact hnotadj i j this
    have := hS_indep.card_le_indepNum
    rw [hS_card] at this
    exact this
  omega

/-- The rungs of a prism form a perfect matching. -/
@[simp] theorem matchNum_prism (n : ℕ) : (prism n).matchNum = n := by
  set G := prism n with hG_def
  have hV : G.V = 2 * n := by
    simp [G, prism, V_cartesianProduct, V_cycle, V_complete]
    ring
  have hup : G.matchNum ≤ n := by
    have h := G.two_mul_matchNum_le_V
    rw [hV] at h; omega
  have hlow : n ≤ G.matchNum := by
    -- G = prism n = ⟦CGraph.prism n⟧
    have hG_iso : G = ⟦CGraph.prism n⟧ := by
      simp [hG_def, prism, cycle_def, complete_def, cartesianProduct_mk]
    rw [hG_iso, matchNum_eq, lineGraph_mk, indepNum_mk]
    set G' : CGraph := CGraph.prism n
    -- The rung edge between (i, 0) and (i, 1) is an edge of G' for each i : Fin n.
    -- These n edges are pairwise disjoint, giving an independent set of size n in lineGraph G'.
    have rung_adj : ∀ i : Fin n, G'.Adj ((i, (0 : Fin 2)) : G'.V) ((i, (1 : Fin 2)) : G'.V) := by
      intro i
      simp [G', CGraph.prism, CGraph.cartesianProduct_adj, CGraph.complete_adj]
    have rung_edge_mem : ∀ i : Fin n,
        s(((i, (0 : Fin 2)) : G'.V), ((i, (1 : Fin 2)) : G'.V)) ∈ G'.toSimple.edgeSet := by
      intro i
      rw [SimpleGraph.mem_edgeSet]
      exact rung_adj i
    -- Build the Finset of rung-edge vertices in lineGraph(G')
    let rungVer : Fin n → (CGraph.lineGraph G').V := fun i =>
      ⟨s((i, (0 : Fin 2)), (i, (1 : Fin 2))), rung_edge_mem i⟩
    let rungSet : Finset (CGraph.lineGraph G').V := Finset.univ.image rungVer
    have rung_pair_ne : ∀ i : Fin n,
        ((i, (0 : Fin 2)) : Fin n × Fin 2) ≠ ((i, (1 : Fin 2)) : Fin n × Fin 2) := by
      intro i; simp
    have hrung_inj : Function.Injective rungVer := by
      intro i j hij
      let e : Sym2 (Fin n × Fin 2) := s((j, (0 : Fin 2)), (j, (1 : Fin 2)))
      have hval : s((i, (0 : Fin 2)), (i, (1 : Fin 2))) = e := by
        exact congrArg Subtype.val hij
      have hmem_i0 : (i, (0 : Fin 2)) ∈ e := by
        rw [← hval]
        exact Sym2.mem_iff.mpr (Or.inl rfl)
      rcases Sym2.mem_iff.mp hmem_i0 with h | h <;> simp_all
    have hrung_card : rungSet.card = n := by
      rw [Finset.card_image_of_injective _ hrung_inj, Finset.card_univ, Fintype.card_fin]
    have hrung_not_adj :
        ∀ i j : Fin n, i ≠ j → ¬(CGraph.lineGraph G').Adj (rungVer i) (rungVer j) := by
      intro i j hij
      simp [CGraph.lineGraph_adj, hrung_inj.ne hij]
      intro x hx_i hx_j
      simp [rungVer, Sym2.mem_iff] at hx_i hx_j
      rcases hx_i with rfl | rfl
      · rcases hx_j with h | h <;> exact absurd (Prod.ext_iff.mp h).1 hij
      · rcases hx_j with h | h
        · exact absurd (Prod.ext_iff.mp h).1 hij
        · exact absurd (Prod.ext_iff.mp h).1 hij
    have hrung_indep :
        (CGraph.lineGraph G').toSimple.IsIndepSet
          (rungSet : Set (CGraph.lineGraph G').V) := by
      intro e he f hf hef
      rw [Finset.coe_image, Set.mem_image] at he hf
      obtain ⟨i, _, rfl⟩ := he
      obtain ⟨j, _, rfl⟩ := hf
      exact hrung_not_adj i j (by intro h; exact hef (h ▸ rfl))
    have hcaref : (CGraph.prism n).lineGraph.indepNum = (CGraph.lineGraph G').indepNum := by
      simp [G']
    rw [hcaref]
    have := hrung_indep.card_le_indepNum
    rw [hrung_card] at this
    exact this
  exact le_antisymm hup hlow

/-- The Petersen graph is cubic and bridgeless, so it has a perfect matching. -/
@[simp] theorem matchNum_petersen : petersen.matchNum = 5 := by
  have hub : petersen.matchNum ≤ 5 := by
    have h := petersen.two_mul_matchNum_le_V
    rw [V_petersen] at h; omega
  have hequindep : 5 ≤ petersen.lineGraph.indepNum := by
    simp only [petersen]
    -- Now goal is about lineGraph Compute.petersen
    simp only [kneser_def]
    -- The CGraph.kneser 5 2 is exactly the canonical form of petersen.
    -- We can relate indepNum at CGraph and IsoGraph levels.
    have hkneser_iso : petersen = ⟦CGraph.kneser 5 2⟧ := by rfl
    have h_le := IsoGraph.indepNum_petersen_le
    rw [hkneser_iso, IsoGraph.indepNum_mk] at h_le
    -- indepNum_petersen_le now gives (CGraph.kneser 5 2).indepNum ≤ 5
    -- Use CGraph-level gallai for line graph
    have hv : FinEnum.card (CGraph.kneser 5 2).V = 10 := by
      native_decide
    simp only [lineGraph_mk, IsoGraph.indepNum_mk]
    have h_exists : ∃ S : Finset (CGraph.lineGraph (CGraph.kneser 5 2)).V, S.card = 5 ∧
        (CGraph.lineGraph (CGraph.kneser 5 2)).toSimple.IsIndepSet
          (S : Set (CGraph.lineGraph (CGraph.kneser 5 2)).V) := by
      native_decide
    obtain ⟨S, hS_card, hS_indep⟩ := h_exists
    have := hS_indep.card_le_indepNum
    rw [hS_card] at this
    exact this
  have : petersen.matchNum = petersen.lineGraph.indepNum := matchNum_eq petersen
  omega

@[simp] theorem coverNum_petersen : petersen.coverNum = 6 := by
  have h := petersen.coverNum_add_indepNum
  rw [V_petersen, indepNum_petersen] at h
  omega

@[simp] theorem cliqueCoverNum_ladder (n : ℕ) : (ladder n).cliqueCoverNum = n := by
  have h1 := cliqueCoverNum_le_V_sub_matchNum (ladder n)
  rw [V_ladder, matchNum_ladder] at h1
  have h2 := indepNum_le_cliqueCoverNum (ladder n)
  rw [indepNum_ladder] at h2
  omega

@[simp] theorem cliqueCoverNum_prism (n : ℕ) : (prism (n + 4)).cliqueCoverNum = n + 4 := by
  have h1 := cliqueCoverNum_le_V_sub_matchNum (prism (n + 4))
  rw [V_prism, matchNum_prism] at h1
  have h2 := V_le_cliqueCoverNum_mul_cliqueNum (prism (n + 4))
  rw [V_prism, cliqueNum_prism] at h2
  omega

example : (path 6).cliqueCoverNum = 3 := by rw [cliqueCoverNum_path]

example : petersen.matchNum = 5 := matchNum_petersen

example : (ladder 5).cliqueCoverNum = 5 := by rw [cliqueCoverNum_ladder]

/-- **An odd prism misses a perfect independent set by one.**  Each of the `2m + 3` rungs holds at
most one vertex, and taking exactly one from every rung would two-colour the odd cycle
`C_{2m+3}`, which is not bipartite; so `α ≤ 2m + 2`, and `(2k, 0)` together with `(2k + 1, 1)`,
for `k ≤ m`, attains it. -/
@[simp] theorem indepNum_prism_odd (m : ℕ) : (prism (2 * m + 3)).indepNum = 2 * m + 2 := by
  have hG : prism (2 * m + 3) = ⟦CGraph.prism (2 * m + 3)⟧ := by
    simp [prism, cycle, complete, cartesianProduct_mk, CGraph.prism]
  rw [hG, indepNum_mk]
  refine le_antisymm ?_ ?_
  · -- an independent set meets every rung at most once, and meeting all `2m + 3` of them would
    -- two-colour the odd cycle
    have h := CGraph.indepNum_cartesianProduct_complete_two_lt (CGraph.cycle (2 * m + 3))
      (not_isBipartite_cycle_odd m)
    rw [CGraph.card_cycle] at h
    exact Nat.lt_succ_iff.mp h
  -- Lower bound: take `(2k, 0)` and `(2k + 1, 1)` for `k ≤ m`.  Two of these on the same layer
  -- have first coordinates of equal parity, so they are never consecutive on the cycle; two on
  -- different layers have first coordinates of different parity, so they differ.
  · have hcyc : ∀ u v : Fin (2 * m + 3), u.val ≤ 2 * m + 1 → v.val ≤ 2 * m + 1 →
        u.val % 2 = v.val % 2 → (CGraph.cycle (2 * m + 3)).Adj u v = false := by
      intro u v hu hv hpar
      rw [Bool.eq_false_iff, ne_eq, CGraph.cycle_adj_val]
      rintro ⟨-, hstep | hstep⟩ <;> rw [Nat.mod_eq_of_lt (by omega)] at hstep <;> omega
    let f : Fin (m + 1) × Fin 2 → (CGraph.prism (2 * m + 3)).V := fun p ↦
      (⟨2 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩, p.2)
    have hinj : Function.Injective f := by
      rintro ⟨k, b⟩ ⟨l, c⟩ h
      have h2 : b = c := congrArg Prod.snd h
      subst h2
      have h1 : 2 * k.val + b.val = 2 * l.val + b.val := congrArg (fun q ↦ (Prod.fst q).val) h
      have hkl : k = l := Fin.ext (by omega)
      rw [hkl]
    have hnadj : ∀ p q : Fin (m + 1) × Fin 2, p ≠ q →
        (CGraph.prism (2 * m + 3)).Adj (f p) (f q) = false := by
      rintro ⟨k, b⟩ ⟨l, c⟩ hpq
      have hk := k.isLt
      have hl := l.isLt
      have hb := b.isLt
      have hc := c.isLt
      rw [CGraph.cartesianProduct_adj, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
        Bool.and_eq_false_iff]
      by_cases hbc : b = c
      · subst hbc
        exact ⟨Or.inr (CGraph.adj_self _ _),
          Or.inl (hcyc _ _ (by simp only [f]; omega) (by simp only [f]; omega)
            (by simp only [f]; omega))⟩
      · have hbcv : b.val ≠ c.val := fun h ↦ hbc (Fin.ext h)
        refine ⟨Or.inl ?_, Or.inr (by simp only [f, decide_eq_false_iff_not]; exact hbc)⟩
        simp only [f, decide_eq_false_iff_not]
        intro h
        have := congrArg Fin.val h
        simp only at this
        omega
    calc 2 * m + 2 = Fintype.card (Fin (m + 1) × Fin 2) := by simp; omega
      _ ≤ _ := CGraph.card_le_indepNum f hinj hnadj

/-- The Johnson graph `J(n, k)` is regular of degree `k(n - k)`: a neighbour is obtained by
swapping one of the `k` chosen elements for one of the `n - k` unchosen ones, and that swap is a
bijection between the pairs `(a, b) ∈ s × sᶜ` and the neighbours of `s`. -/
@[simp] theorem degSequence_johnson {n k : ℕ} (hk : k ≤ n) :
    degSequence (johnson n k) = List.replicate (n.choose k) (k * (n - k)) := by
  simp only [johnson, degSequence_mk]
  have hnbrs : ∀ s : (CGraph.johnson n k).V,
      ((CGraph.johnson n k).nbrs s).card = k * (n - k) := by
    intro s
    by_cases hk0 : k = 0
    · -- with `k = 0` there is a single vertex and no edges at all
      subst hk0
      rw [Nat.zero_mul, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro t ht
      rw [CGraph.mem_nbrs, CGraph.johnson_adj, Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ht.1 (Subtype.ext (by rw [Finset.card_eq_zero.1 s.2, Finset.card_eq_zero.1 t.2]))
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    have hcard : ∀ {a b : Fin n}, a ∈ s.1 → b ∉ s.1 → (s.1.erase a ∪ {b}).card = k := by
      intro a b ha hb
      rw [Finset.card_union_of_disjoint (by simp [Finset.disjoint_singleton_right, hb]),
        Finset.card_erase_of_mem ha, Finset.card_singleton, s.2, Nat.sub_add_cancel hk1]
    have hbij : (s.1 ×ˢ s.1ᶜ).card = ((CGraph.johnson n k).nbrs s).card := by
      refine Finset.card_bij (fun p hp ↦ ⟨s.1.erase p.1 ∪ {p.2}, hcard (Finset.mem_product.1 hp).1
        (Finset.mem_compl.1 (Finset.mem_product.1 hp).2)⟩) ?_ ?_ ?_
      · -- swapping `a` out for `b` does produce a neighbour
        rintro ⟨a, b⟩ hp
        obtain ⟨ha, hb⟩ := Finset.mem_product.1 hp
        rw [Finset.mem_compl] at hb
        have hint : s.1 ∩ (s.1.erase a ∪ {b}) = s.1.erase a := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
          exact ⟨fun ⟨hx, h⟩ ↦ h.elim id fun hxb ↦ absurd (hxb ▸ hx) hb,
            fun h ↦ ⟨h.2, Or.inl h⟩⟩
        rw [CGraph.mem_nbrs, CGraph.johnson_adj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        refine ⟨fun h ↦ hb ?_, ?_⟩
        · rw [show s.1 = s.1.erase a ∪ {b} from congrArg Subtype.val h]
          exact Finset.mem_union_right _ (Finset.mem_singleton_self b)
        · rw [hint, Finset.card_erase_of_mem ha, s.2]
      · -- and distinct pairs produce distinct neighbours
        rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' heq
        obtain ⟨ha, hb⟩ := Finset.mem_product.1 hp
        obtain ⟨ha', hb'⟩ := Finset.mem_product.1 hp'
        rw [Finset.mem_compl] at hb hb'
        have h : s.1.erase a ∪ {b} = s.1.erase a' ∪ {b'} := congrArg Subtype.val heq
        have hbb : b = b' := by
          have hmem : b ∈ s.1.erase a' ∪ {b'} := by
            rw [← h]; exact Finset.mem_union_right _ (Finset.mem_singleton_self b)
          rcases Finset.mem_union.1 hmem with hx | hx
          · exact absurd (Finset.mem_of_mem_erase hx) hb
          · exact Finset.mem_singleton.1 hx
        subst hbb
        have hna : a ∉ s.1.erase a' ∪ {b} := by
          rw [← h, Finset.mem_union, Finset.mem_singleton]
          rintro (h1 | rfl)
          · exact Finset.ne_of_mem_erase h1 rfl
          · exact hb ha
        rw [Finset.mem_union, Finset.mem_singleton] at hna
        push_neg at hna
        by_contra hne
        exact hna.1 (Finset.mem_erase.2 ⟨fun hx ↦ hne (by rw [hx]), ha⟩)
      · -- every neighbour arises this way, from the unique points of `s \ t` and `t \ s`
        rintro t ht
        rw [CGraph.mem_nbrs, CGraph.johnson_adj, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at ht
        obtain ⟨hne, hint⟩ := ht
        obtain ⟨a, ha⟩ : ∃ a, s.1 \ t.1 = {a} := Finset.card_eq_one.1 (by
          have := Finset.card_sdiff_add_card_inter s.1 t.1
          rw [hint, s.2] at this
          omega)
        obtain ⟨b, hb⟩ : ∃ b, t.1 \ s.1 = {b} := Finset.card_eq_one.1 (by
          have := Finset.card_sdiff_add_card_inter t.1 s.1
          rw [Finset.inter_comm, hint, t.2] at this
          omega)
        have hain : a ∈ s.1 \ t.1 := by rw [ha]; exact Finset.mem_singleton_self a
        have hbin : b ∈ t.1 \ s.1 := by rw [hb]; exact Finset.mem_singleton_self b
        obtain ⟨has, hat⟩ := Finset.mem_sdiff.1 hain
        obtain ⟨hbt, hbs⟩ := Finset.mem_sdiff.1 hbin
        refine ⟨(a, b), Finset.mem_product.2 ⟨has, Finset.mem_compl.2 hbs⟩, Subtype.ext ?_⟩
        show s.1.erase a ∪ {b} = t.1
        ext x
        rw [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro (⟨hxa, hxs⟩ | rfl)
          · by_contra hxt
            exact hxa (Finset.mem_singleton.1 (by rw [← ha]; exact Finset.mem_sdiff.2 ⟨hxs, hxt⟩))
          · exact hbt
        · intro hx
          by_cases hxs : x ∈ s.1
          · exact Or.inl ⟨fun hxa ↦ hat (hxa ▸ hx), hxs⟩
          · exact Or.inr (Finset.mem_singleton.1 (by
              rw [← hb]; exact Finset.mem_sdiff.2 ⟨hx, hxs⟩))
    rw [← hbij, Finset.card_product, Finset.card_compl, Fintype.card_fin, s.2]
  rw [CGraph.degSequence_of_card_nbrs _ hnbrs, CGraph.card_johnson]

/-! ### Degrees and edge counts of the Johnson graphs

`J(n, k)` is regular of degree `k(n - k)`, so its edge count, maximum degree and minimum degree
all follow from the degree sequence. -/

theorem two_mul_E_johnson {n k : ℕ} (hk : k ≤ n) :
    2 * (johnson n k).E = n.choose k * (k * (n - k)) :=
  two_mul_E_of_degSequence_replicate (degSequence_johnson hk)

@[simp] theorem maxDeg_johnson {n k : ℕ} (hk : k ≤ n) : maxDeg (johnson n k) = k * (n - k) :=
  maxDeg_eq_of_degSequence_replicate (Nat.choose_pos hk) (degSequence_johnson hk)

@[simp] theorem minDeg_johnson {n k : ℕ} (hk : k ≤ n) : minDeg (johnson n k) = k * (n - k) :=
  minDeg_eq_of_degSequence_replicate (Nat.choose_pos hk) (degSequence_johnson hk)

theorem isRegularWith_johnson {n k : ℕ} (hk : k ≤ n) :
    (johnson n k).IsRegularWith (k * (n - k)) :=
  isRegularWith_of_degSequence (degSequence_johnson hk)

/-! ### The chromatic number of a triangular graph is an edge chromatic number

Since `T(n) = L(Kₙ)`, a proper colouring of `T(n)` is exactly a proper edge colouring of `Kₙ`,
so `χ(T(n)) = χ'(Kₙ)`.  Everything known about `χ'(Kₙ)` transports. -/

theorem chromNum_johnson_two (n : ℕ) : (johnson n 2).chromNum = (complete n).edgeChromNum := by
  rw [edgeChromNum_eq, lineGraph_complete]

theorem chromNum_triangular (n : ℕ) : (triangular n).chromNum = (complete n).edgeChromNum :=
  chromNum_johnson_two n

theorem chromNum_triangular_le (n : ℕ) : (triangular n).chromNum ≤ 2 * (n - 1) - 1 := by
  rw [chromNum_triangular]
  exact edgeChromNum_complete_le n

/-- An odd complete graph is class two, so `χ(T(2m+3)) ≥ 2m + 3`. -/
theorem le_chromNum_triangular_odd (m : ℕ) : 2 * m + 3 ≤ (triangular (2 * m + 3)).chromNum := by
  rw [chromNum_triangular]
  exact le_edgeChromNum_complete_odd m

@[simp] theorem chromNum_triangular_three : (triangular 3).chromNum = 3 := by
  rw [chromNum_triangular, edgeChromNum_complete_three]

@[simp] theorem chromNum_triangular_four : (triangular 4).chromNum = 3 := by
  rw [chromNum_triangular, edgeChromNum_complete_four]

/-! ### Vertex covers of the triangular and Kneser graphs, by Gallai -/

@[simp] theorem coverNum_triangular (n : ℕ) :
    (triangular n).coverNum = n.choose 2 - n / 2 :=
  coverNum_johnson_two n

@[simp] theorem coverNum_kneser_two_even (m : ℕ) :
    (kneser (2 * m + 2) 2).coverNum = (2 * m + 2).choose 2 - (2 * m + 1) := by
  have h := (kneser (2 * m + 2) 2).coverNum_add_indepNum
  rw [V_kneser, indepNum_kneser_two_even] at h
  omega

/-- A rook graph is dominated by one full row or one full column, whichever is shorter. -/
@[simp] theorem domNum_rook (m n : ℕ) : (rook (m + 1) (n + 1)).domNum = min (m + 1) (n + 1) := by
  simp (config := { decide := true }) only [IsoGraph.rook, IsoGraph.domNum_mk,
    IsoGraph.cartesianProduct_mk, IsoGraph.complete]
  apply le_antisymm
  · -- Upper bound: domNum ≤ min(m+1, n+1)
    have h1 : (CGraph.complete (m + 1) □g CGraph.complete (n + 1)).domNum ≤ n + 1 := by
      calc (CGraph.complete (m + 1) □g CGraph.complete (n + 1)).domNum
          ≤ (CGraph.complete (m + 1)).domNum * FinEnum.card (CGraph.complete (n + 1)).V :=
            CGraph.domNum_cartesianProduct_le _ _
        _ = 1 * (n + 1) := by rw [CGraph.domNum_complete, CGraph.card_complete]
        _ = n + 1 := one_mul _
    have h2 : (CGraph.complete (m + 1) □g CGraph.complete (n + 1)).domNum ≤ m + 1 := by
      have hiso : CGraph.complete (m + 1) □g CGraph.complete (n + 1) ≃cg
          CGraph.complete (n + 1) □g CGraph.complete (m + 1) :=
        CGraph.Iso.cartesianProductComm _ _
      rw [CGraph.domNum_eq_of_iso hiso]
      calc (CGraph.complete (n + 1) □g CGraph.complete (m + 1)).domNum
          ≤ (CGraph.complete (n + 1)).domNum * FinEnum.card (CGraph.complete (m + 1)).V :=
            CGraph.domNum_cartesianProduct_le _ _
        _ = 1 * (m + 1) := by rw [CGraph.domNum_complete, CGraph.card_complete]
        _ = m + 1 := one_mul _
    omega
  · -- Lower bound: min(m+1, n+1) ≤ domNum
    obtain ⟨S, hScard, hSdom⟩ := (CGraph.complete (m + 1) □g CGraph.complete
      (n + 1)).exists_isDominatingSet_domNum
    rw [← hScard]
    set V1 := (CGraph.complete (m + 1)).V
    set V2 := (CGraph.complete (n + 1)).V
    have hrow_hit_or_empty : (∀ i : V1, ∃ s ∈ S, s.1 = i) ∨ (∃ i₀ : V1, ∀ s ∈ S, s.1 ≠ i₀) := by
      by_contra h
      push_neg at h
      obtain ⟨hna, hnb⟩ := h
      obtain ⟨i₀, hi₀empty⟩ := hna
      have hA : ∀ i : V1, ∃ s ∈ S, s.1 = i := by
        intro i
        by_contra hi
        obtain ⟨s, hs, heq⟩ := hnb i₀
        exact hi₀empty s hs heq
      exact absurd (hA i₀) (by simpa using hi₀empty)
    rcases hrow_hit_or_empty with hrowfull | hrowempty
    · -- hrowfull: every row has a vertex of S → m+1 ≤ |S|
      have hinj : Function.Injective (fun i : V1 => ⟨Classical.choose (hrowfull i),
        (Classical.choose_spec (hrowfull i)).1⟩ : V1 → S) := by
        intro i i' heq
        have hci := Classical.choose_spec (hrowfull i)
        have hci' := Classical.choose_spec (hrowfull i')
        have heq' : Classical.choose (hrowfull i) = Classical.choose (hrowfull i') := by
          exact Subtype.ext_iff.mp heq
        rw [← hci.2, heq', hci'.2]
      have := Fintype.card_le_of_injective _ hinj
      have hV1 : Fintype.card V1 = m + 1 :=
        (FinEnum.card_eq_fintypeCard' (α := V1)).symm.trans (CGraph.card_complete (m + 1))
      have : m + 1 ≤ S.card := by
        have := this; rw [hV1] at this
        rw [Fintype.card_subtype] at this
        simp at this
        exact this
      exact min_le_of_left_le this
    · -- hrowempty: row i₀ empty → each column needs a vertex → n+1 ≤ |S|
      obtain ⟨i₀, hi₀empty⟩ := hrowempty
      have huniv2 : ∀ j : V2, ∃ s ∈ S, s.2 = j := by
        intro j
        have hnotin : (i₀, j) ∉ S := fun h => hi₀empty (i₀, j) h rfl
        rcases hSdom (i₀, j) with hout | ⟨u, hu, hadj⟩
        · exact absurd hout hnotin
        · rw [CGraph.cartesianProduct_adj] at hadj
          simp (config := { decide := true }) [CGraph.complete_adj] at hadj
          rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1 (hi₀empty u hu)
          · exact ⟨u, hu, h2⟩
      choose f hfmem hfproj using huniv2
      have hinj2 : Function.Injective (fun j : V2 => ⟨f j, hfmem j⟩ : V2 → S) := by
        intro j j' hfjj'
        have := congr_arg Subtype.val hfjj'
        have := congr_arg Prod.snd this
        rw [hfproj j, hfproj j'] at this
        exact this
      have hV2 : Fintype.card V2 = n + 1 :=
        (FinEnum.card_eq_fintypeCard' (α := V2)).symm.trans (CGraph.card_complete (n + 1))
      have hcard : n + 1 ≤ S.card := by
        have h := Fintype.card_le_of_injective _ hinj2
        rw [hV2] at h
        rw [Fintype.card_subtype] at h
        simp at h
        exact h
      exact min_le_of_right_le hcard

/-! ### Edge counts from the regular degree sequences -/

@[simp] theorem E_johnson {n k : ℕ} (hk : k ≤ n) :
    (johnson n k).E = n.choose k * (k * (n - k)) / 2 := by
  have h := two_mul_E_johnson hk
  omega

@[simp] theorem E_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (kneser n k).E = n.choose k * (n - k).choose k / 2 := by
  have h := two_mul_E_kneser n hk
  omega

theorem two_mul_E_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) :
    2 * (lineGraph (johnson n k)).E
      = n.choose k * (k * (n - k)) * (k * (n - k) - 1) := by
  rw [two_mul_E_lineGraph_of_degSequence_replicate (degSequence_johnson hk),
    two_mul_E_johnson hk]

/-- The three-cube has a perfect dominating set of size two: two antipodal vertices. -/
theorem domNum_hypercube_three : (hypercube 3).domNum = 2 := by
  simp only [IsoGraph.hypercube, IsoGraph.domNum_mk]
  -- No vertex is universal in hypercube 3
  have no_univ : ∀ v : (CGraph.hypercube 3).V, ∃ u : (CGraph.hypercube 3).V, u ≠ v ∧
    ¬(CGraph.hypercube 3).Adj v u := by
    native_decide
  -- domNum ≠ 1
  have domNum_ne_one : (CGraph.hypercube 3).domNum ≠ 1 := by
    intro h
    obtain ⟨s, hcard_s, hs⟩ := CGraph.exists_isDominatingSet_domNum (CGraph.hypercube 3)
    rw [h] at hcard_s
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard_s
    have hdom_v : ∀ u : (CGraph.hypercube 3).V, u = v ∨ (CGraph.hypercube 3).Adj v u = true := by
      intro u
      have h := hs u
      rcases h with h | ⟨u', hu', hadj⟩
      · simp at h; exact Or.inl h
      · rw [Finset.mem_singleton] at hu'
        subst hu'
        exact Or.inr hadj
    obtain ⟨u, huv, hnu⟩ := no_univ v
    cases hdom_v u with
    | inl hu => exact huv hu
    | inr hai => exact hnu hai
  -- domNum ≥ 1
  have domNum_pos' : 0 < (CGraph.hypercube 3).domNum :=
    CGraph.domNum_pos (CGraph.hypercube 3)
      (by native_decide : 0 < FinEnum.card (CGraph.hypercube 3).V)
  -- domNum ≥ 2
  have domNum_ge_two : 2 ≤ (CGraph.hypercube 3).domNum := by omega
  -- domNum ≤ 2: exhibit a dominating set of size 2
  have hle2 : (CGraph.hypercube 3).domNum ≤ 2 := by
    have hdom2 : (CGraph.hypercube 3).IsDominatingSet
        ({(fun _ => false), (fun _ => true)} : Finset ((CGraph.hypercube 3).V)) := by
      intro w
      simp only [CGraph.hypercube_adj, Finset.mem_insert, Finset.mem_singleton]
      revert w
      native_decide
    have hcard2 : ({(fun _ => false), (fun _ => true)} : Finset ((CGraph.hypercube 3).V)).card = 2
      := by
      native_decide
    rw [← hcard2]
    exact CGraph.domNum_le_card_of_isDominatingSet hdom2
  omega

example : (lineGraph petersen).indepNum = 5 := by rw [indepNum_lineGraph, matchNum_petersen]

example : (lineGraph (complete 4)).chromNum = 3 := by
  rw [chromNum_lineGraph, edgeChromNum_complete_four]

/-- A circulant graph is vertex transitive: translation by `1` is an automorphism. -/
theorem isVertexTransitive_circulant (n : ℕ) (S : List ℕ) :
    IsVertexTransitive (circulant n S) := by
  unfold IsoGraph.circulant
  rw [IsoGraph.isVertexTransitive_mk]
  unfold CGraph.IsVertexTransitive CGraph.circulant CGraph.ofRel
  by_cases hn : n = 0
  · subst hn; intro u v; fin_cases u
  · haveI : NeZero n := ⟨hn⟩
    intro u v
    -- Work in ZMod n for the group structure
    let equiv : ZMod n ≃ Fin n := {
      toFun := fun a => ⟨a.val, ZMod.val_lt a⟩
      invFun := fun i => (i.1 : ZMod n)
      left_inv := fun a => ZMod.natCast_rightInverse a
      right_inv := fun i => Fin.ext (ZMod.val_cast_of_lt i.2)
    }
    -- The translation permutation on Fin n
    let d : ZMod n := (equiv.symm v) - (equiv.symm u)
    let σ_fun : Fin n → Fin n := fun x => equiv (equiv.symm x + d)
    have hσ_bij : Function.Bijective σ_fun := by
      have h1 : Function.Bijective (fun z : ZMod n => z + d) := (Equiv.addRight d).bijective
      have h2 : Function.Bijective equiv := equiv.bijective
      have h3 : Function.Bijective equiv.symm := equiv.symm.bijective
      exact h2.comp (h1.comp h3)
    let σ_perm : Equiv.Perm (Fin n) := Equiv.ofBijective σ_fun hσ_bij
    refine ⟨CGraph.autoOfPerm σ_perm (fun x y => ?_), ?_⟩
    · -- Adjacency in circulant depends on (y - x : ZMod n).val, preserved by translation.
      simp only [σ_perm, Equiv.ofBijective_apply, σ_fun, equiv]
      -- Key: (σ y).val + n - (σ x).val ≡ y.val + n - x.val (mod n)
      -- because in ZMod: (equiv.symm y + d - (equiv.symm x + d)).val = (equiv.symm y - equiv.symm
      -- x).val
      have hdiff : ∀ x y : Fin n,
          ((↑(σ_perm y) + n - ↑(σ_perm x)) % n) = ((↑y + n - ↑x) % n) := by
        intro x y
        have hsval : ∀ x : Fin n, (σ_perm x : ℕ) = (equiv.symm x + d : ZMod n).val := by
          intro x; simp only [σ_perm, Equiv.ofBijective_apply, σ_fun, equiv]; rfl
        have h1 : ((↑(σ_perm y) + n - ↑(σ_perm x)) % n : ℕ) = ((equiv.symm y + d : ZMod n).val + n -
          (equiv.symm x + d : ZMod n).val) % n := by
          rw [hsval y, hsval x]
        have hsymm_val : ∀ x : Fin n, (equiv.symm x : ZMod n).val = (x : ℕ) := by
          intro x; simp [equiv, ZMod.val_cast_of_lt x.2]
        rw [h1]
        let x' : ZMod n := equiv.symm x + d
        let y' : ZMod n := equiv.symm y + d
        have key : (y'.val + n - x'.val) % n = (y' - x').val := zmod_val_sub x' y'
        have hcancel : (y' - x' : ZMod n) = equiv.symm y - equiv.symm x := by
          simp [x', y']
        rw [hcancel] at key
        rw [key, ← zmod_val_sub (equiv.symm x) (equiv.symm y), hsymm_val y, hsymm_val x]
      -- ≠ is preserved
      have hne' : σ_perm x ≠ σ_perm y ↔ x ≠ y := σ_perm.injective.ne_iff
      -- Now rewrite using hdiff and hne'
      show (decide (σ_perm x ≠ σ_perm y) &&
        (S.contains (((σ_perm y : Fin n) + n - (σ_perm x : Fin n)) % n) ||
         S.contains (((σ_perm x : Fin n) + n - (σ_perm y : Fin n)) % n))) =
        (decide (x ≠ y) &&
        (S.contains (((y : Fin n) + n - (x : Fin n)) % n) ||
         S.contains (((x : Fin n) + n - (y : Fin n)) % n)))
      simp [hne', hdiff]
    · show σ_perm u = v
      simp only [σ_perm, Equiv.ofBijective_apply, σ_fun, equiv]
      show equiv (equiv.symm u + d) = v
      simp [d, equiv, add_sub_cancel]
      exact Fin.ext (Nat.mod_eq_of_lt v.isLt)

/-- The rows of a rook graph are cliques, and the independence number matches. -/
@[simp] theorem cliqueCoverNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).cliqueCoverNum = min (m + 1) (n + 1) := by
  rw [cliqueCoverNum_eq, compl_rook]
  exact le_antisymm
    (le_trans (chromNum_tensorProduct_le _ _) (by simp [chromNum_complete]))
    (cliqueNum_le_chromNum _ |> le_trans
      (by rw [cliqueNum_tensorProduct, cliqueNum_complete, cliqueNum_complete]))

/-- **A complete graph of odd order is class two**: `K_{2m+3}` needs `2m + 3` edge colours,
one more than its maximum degree. -/
theorem edgeChromNum_complete_odd (m : ℕ) :
    (complete (2 * m + 3)).edgeChromNum = 2 * m + 3 := by
  rw [edgeChromNum_eq, lineGraph_complete]
  apply le_antisymm
  · have : johnson (2 * m + 3) 2 = ⟦CGraph.johnson (2 * m + 3) 2⟧ := rfl
    rw [this, chromNum_mk, CGraph.chromNum_le_iff_colorable]
    classical
    let n := 2 * m + 3
    let G : SimpleGraph {s : Finset (Fin n) // s.card = 2} := (CGraph.johnson n 2).toSimple
    have hcolor : ∀ (s t : {s : Finset (Fin n) // s.card = 2}), G.Adj s t →
        ((s.1.sum Fin.val) % n) ≠ ((t.1.sum Fin.val) % n) := by
      intro s t hadj
      simp only [G, CGraph.toSimple_adj, CGraph.johnson_adj] at hadj
      simp at hadj
      have hs_ne_ht' : (s : Finset (Fin n)) ≠ (t : Finset (Fin n)) := by
        intro h; exact hadj.1 (Subtype.ext h)
      have hinter : ((s : Finset (Fin n)) ∩ (t : Finset (Fin n))).card = 1 := hadj.2
      set s1 := (s : Finset (Fin n))
      set t1 := (t : Finset (Fin n))
      have hs1_card : s1.card = 2 := s.property
      have ht1_card : t1.card = 2 := t.property
      have hsdiff_s : (s1 \ t1).card = 1 := by
        have := Finset.card_sdiff_add_card_inter s1 t1
        rw [hs1_card, hinter] at this; omega
      have hsdiff_t : (t1 \ s1).card = 1 := by
        have h1 := Finset.card_sdiff_add_card_inter t1 s1
        rw [Finset.inter_comm, hinter, ht1_card] at h1; omega
      obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hsdiff_s
      obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hsdiff_t
      have ha_mem_s : a ∈ s1 := (ha_eq ▸ Finset.mem_singleton_self a) |> Finset.mem_sdiff.mp |>.1
      have ha_not_t : a ∉ t1 := (ha_eq ▸ Finset.mem_singleton_self a) |> Finset.mem_sdiff.mp |>.2
      have hb_mem_t : b ∈ t1 := (hb_eq ▸ Finset.mem_singleton_self b) |> Finset.mem_sdiff.mp |>.1
      have hb_not_s : b ∉ s1 := (hb_eq ▸ Finset.mem_singleton_self b) |> Finset.mem_sdiff.mp |>.2
      have hsum_s : ∑ x ∈ s1, (x : ℕ) = ∑ x ∈ s1 \ t1, (x : ℕ) + ∑ x ∈ s1 ∩ t1, (x : ℕ) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
      have hsum_inter : ∑ x ∈ s1 ∩ t1, (x : ℕ) = ∑ x ∈ t1 ∩ s1, (x : ℕ) := by
        rw [Finset.inter_comm]
      have hsum_t : ∑ x ∈ t1, (x : ℕ) = ∑ x ∈ t1 \ s1, (x : ℕ) + ∑ x ∈ t1 ∩ s1, (x : ℕ) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter ..), Finset.sdiff_union_inter]
      rw [hsum_s, hsum_t, ha_eq, hb_eq, Finset.sum_singleton, Finset.sum_singleton, hsum_inter]
      by_contra hneq
      have ha_lt : (a : ℕ) < n := a.2
      have hb_lt : (b : ℕ) < n := b.2
      have hab : (a : ℕ) = b := by
        have hmod : (a + ∑ x ∈ t1 ∩ s1, (x : ℕ)) % n = (b + ∑ x ∈ t1 ∩ s1, (x : ℕ)) % n := hneq
        have hv : a.val % n = b.val % n := by
          have h1 : (a.val : ZMod n) = (b.val : ZMod n) := by
            have h2 : (a.val + ∑ x ∈ t1 ∩ s1, x.val : ℕ) ≡ (b.val + ∑ x ∈ t1 ∩ s1, x.val : ℕ) [MOD
              n] := by
              exact hmod
            have h3 : (a.val : ZMod n) + (∑ x ∈ t1 ∩ s1, x.val : ZMod n) =
                       (b.val : ZMod n) + (∑ x ∈ t1 ∩ s1, x.val : ZMod n) := by
              norm_cast
              rw [ZMod.natCast_eq_natCast_iff]
              exact h2
            exact add_right_cancel h3
          exact congr_arg ZMod.val h1
        exact Nat.mod_eq_of_lt ha_lt ▸ hv ▸ Nat.mod_eq_of_lt hb_lt
      exact ha_not_t ((Fin.ext hab) ▸ hb_mem_t)
    refine ⟨SimpleGraph.Coloring.mk
      (fun s : {s : Finset (Fin n) // s.card = 2} ↦
        ⟨(s.1.sum Fin.val) % n, Nat.mod_lt _ (by omega)⟩)
      @fun v w h ↦ fun heq ↦ hcolor v w h (by have := congrArg Fin.val heq; exact this)⟩
  · have h := le_edgeChromNum_complete_odd m
    rw [← chromNum_johnson_two] at h
    exact h

/-- The edge chromatic number of a complete graph on at least two vertices: `Δ` when the order is
even and `Δ + 1` when it is odd. -/
theorem edgeChromNum_complete (n : ℕ) :
    (complete (n + 2)).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    rw [if_pos (by omega), edgeChromNum_complete_even]
  · subst hm
    rw [if_neg (by omega), show 2 * m + 1 + 2 = 2 * m + 3 by ring, edgeChromNum_complete_odd]

/-! ### The disjoint union of a path and a complete graph -/

theorem edgeChromNum_disjUnion_path_complete_odd (m n : ℕ) :
    (path (m + 3) ⊕g complete (2 * n + 3)).edgeChromNum = 2 * n + 3 := by
  have h := edgeChromNum_disjUnion (path (m + 3)) (complete (2 * n + 3))
  rw [edgeChromNum_path, edgeChromNum_complete_odd] at h
  omega

/-! ### The disjoint union of a cycle and a complete graph -/

theorem edgeChromNum_disjUnion_cycle_complete_odd (m n : ℕ) :
    (cycle (2 * m + 4) ⊕g complete (2 * n + 3)).edgeChromNum = 2 * n + 3 := by
  have h := edgeChromNum_disjUnion (cycle (2 * m + 4)) (complete (2 * n + 3))
  rw [edgeChromNum_cycle_even, edgeChromNum_complete_odd] at h
  omega

end IsoGraph
