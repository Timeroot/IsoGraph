import IsoGraph.Values.Identities.Products

/-!
# Mycielskians and line graphs of everything

The two unary operators, applied to every family in turn, and then to each other and to the
binary operators: the iterated line graph, the iterated Mycielskian, the line graph of a Cartesian
product, the Mycielskian of a join.  Interleaved with them are the joins and disjoint unions of
pairs of small families, which are the last of the two-family rows.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ### Joining two stars -/

@[simp] theorem V_join_star (m n : ℕ) : (star m ∇g star n).V = m + n + 2 := by
  rw [V_join, V_star, V_star]
  omega

theorem E_join_star (m n : ℕ) :
    (star m ∇g star n).E = m + n + (1 + m) * (1 + n) := by
  rw [E_join, E_star, E_star, V_star, V_star]

theorem cliqueNum_join_star (m n : ℕ) :
    (star (m + 1) ∇g star (n + 1)).cliqueNum = 4 := by
  rw [cliqueNum_join, cliqueNum_star, cliqueNum_star]

theorem chromNum_join_star (m n : ℕ) :
    (star (m + 1) ∇g star (n + 1)).chromNum = 4 := by
  rw [chromNum_join, chromNum_star, chromNum_star]

theorem indepNum_join_star (m n : ℕ) :
    (star m ∇g star n).indepNum = max (max 1 m) (max 1 n) := by
  rw [indepNum_join, indepNum_star, indepNum_star]

theorem coverNum_join_star (m n : ℕ) :
    (star m ∇g star n).coverNum = min (min 1 m + (1 + n)) (1 + m + min 1 n) := by
  rw [coverNum_join, coverNum_star, coverNum_star, V_star, V_star]

theorem cliqueCoverNum_join_star (m n : ℕ) :
    (star m ∇g star n).cliqueCoverNum = max (max 1 m) (max 1 n) := by
  rw [cliqueCoverNum_join, cliqueCoverNum_star, cliqueCoverNum_star]

theorem maxDeg_join_star (m n : ℕ) :
    maxDeg (star (m + 1) ∇g star (n + 1)) = m + n + 3 := by
  have h := maxDeg_join (G := star (m + 1)) (H := star (n + 1))
    (by rw [V_star]; omega) (by rw [V_star]; omega)
  rw [maxDeg_star, maxDeg_star, V_star, V_star] at h
  omega

theorem minDeg_join_star (m n : ℕ) :
    minDeg (star (m + 1) ∇g star (n + 1)) = min (n + 3) (m + 3) := by
  have h := minDeg_join (G := star (m + 1)) (H := star (n + 1))
    (by rw [V_star]; omega) (by rw [V_star]; omega)
  rw [minDeg_star, minDeg_star, V_star, V_star] at h
  omega

theorem isConnected_join_star (m n : ℕ) : IsConnected (star m ∇g star n) :=
  isConnected_join (by rw [V_star]; omega) (by rw [V_star]; omega)

theorem numComponents_join_star (m n : ℕ) : (star m ∇g star n).numComponents = 1 :=
  numComponents_join (by rw [V_star]; omega) (by rw [V_star]; omega)

theorem diameter_join_star (m n : ℕ) : (star (m + 2) ∇g star n).diameter = 2 := by
  have h : (1 + (m + 2)).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [show 1 + (m + 2) = m + 3 from by omega, Nat.choose_two_right,
      show m + 3 - 1 = m + 2 from by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_star]; omega) ?_
  rw [E_star, V_star, h]
  omega

theorem girth_join_star (m n : ℕ) : (star (m + 1) ∇g star (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join_star]; omega)

/-! ### Joining a complete graph and a star -/

@[simp] theorem V_join_complete_star (m n : ℕ) :
    (complete m ∇g star n).V = m + n + 1 := by
  rw [V_join, V_complete, V_star]
  omega

theorem E_join_complete_star (m n : ℕ) :
    (complete m ∇g star n).E = m.choose 2 + n + m * (1 + n) := by
  rw [E_join, E_complete, E_star, V_complete, V_star]

theorem cliqueNum_join_complete_star (m n : ℕ) :
    (complete m ∇g star (n + 1)).cliqueNum = m + 2 := by
  rw [cliqueNum_join, cliqueNum_complete, cliqueNum_star]

theorem chromNum_join_complete_star (m n : ℕ) :
    (complete m ∇g star (n + 1)).chromNum = m + 2 := by
  rw [chromNum_join, chromNum_complete, chromNum_star]

theorem indepNum_join_complete_star (m n : ℕ) :
    (complete m ∇g star n).indepNum = max (min m 1) (max 1 n) := by
  rw [indepNum_join, indepNum_complete, indepNum_star]

theorem coverNum_join_complete_star (m n : ℕ) :
    (complete m ∇g star n).coverNum = min (m - 1 + (1 + n)) (m + min 1 n) := by
  rw [coverNum_join, coverNum_complete, coverNum_star, V_complete, V_star]

theorem cliqueCoverNum_join_complete_star (m n : ℕ) :
    (complete (m + 1) ∇g star n).cliqueCoverNum = max 1 n := by
  rw [cliqueCoverNum_join, cliqueCoverNum_complete, cliqueCoverNum_star]
  omega

theorem maxDeg_join_complete_star (m n : ℕ) :
    maxDeg (complete (m + 1) ∇g star (n + 1)) = m + n + 2 := by
  have h := maxDeg_join (G := complete (m + 1)) (H := star (n + 1))
    (by rw [V_complete]; omega) (by rw [V_star]; omega)
  rw [maxDeg_complete, maxDeg_star, V_complete, V_star] at h
  omega

theorem minDeg_join_complete_star (m n : ℕ) :
    minDeg (complete (m + 1) ∇g star (n + 1)) = m + 2 := by
  have h := minDeg_join (G := complete (m + 1)) (H := star (n + 1))
    (by rw [V_complete]; omega) (by rw [V_star]; omega)
  rw [minDeg_complete, minDeg_star, V_complete, V_star] at h
  omega

theorem isConnected_join_complete_star (m n : ℕ) :
    IsConnected (complete (m + 1) ∇g star n) :=
  isConnected_join (by rw [V_complete]; omega) (by rw [V_star]; omega)

theorem numComponents_join_complete_star (m n : ℕ) :
    (complete (m + 1) ∇g star n).numComponents = 1 :=
  numComponents_join (by rw [V_complete]; omega) (by rw [V_star]; omega)

theorem diameter_join_complete_star (m n : ℕ) :
    (complete (m + 1) ∇g star (n + 2)).diameter = 2 := by
  have h : (1 + (n + 2)).choose 2 = (n + 3) * (n + 2) / 2 := by
    rw [show 1 + (n + 2) = n + 3 from by omega, Nat.choose_two_right,
      show n + 3 - 1 = n + 2 from by omega]
  have h2 : n + 3 ≤ (n + 3) * (n + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (n + 3) * (n + 2) = n * n + 5 * n + 6 := by ring
    omega
  refine diameter_join_right (by rw [V_complete]; omega) ?_
  rw [E_star, V_star, h]
  omega

theorem girth_join_complete_star (m n : ℕ) :
    (complete (m + 1) ∇g star (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join_complete_star]; omega)

/-! ### Joining a cycle and a star -/

@[simp] theorem V_join_cycle_star (m n : ℕ) :
    (cycle m ∇g star n).V = m + n + 1 := by
  rw [V_join, V_cycle, V_star]
  omega

theorem E_join_cycle_star (m n : ℕ) :
    (cycle (m + 3) ∇g star n).E = m + 3 + n + (m + 3) * (1 + n) := by
  rw [E_join, E_cycle, E_star, V_cycle, V_star]

theorem cliqueNum_join_cycle_star (m n : ℕ) :
    (cycle (m + 4) ∇g star (n + 1)).cliqueNum = 4 := by
  rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_star]

theorem chromNum_join_cycle_star_even (m n : ℕ) :
    (cycle (2 * m + 2) ∇g star (n + 1)).chromNum = 4 := by
  rw [chromNum_join, chromNum_cycle_even, chromNum_star]

theorem chromNum_join_cycle_star_odd (m n : ℕ) :
    (cycle (2 * m + 3) ∇g star (n + 1)).chromNum = 5 := by
  rw [chromNum_join, chromNum_cycle_odd, chromNum_star]

theorem indepNum_join_cycle_star (m n : ℕ) :
    (cycle (m + 3) ∇g star n).indepNum = max ((m + 3) / 2) (max 1 n) := by
  rw [indepNum_join, indepNum_cycle, indepNum_star]

theorem coverNum_join_cycle_star (m n : ℕ) :
    (cycle (m + 3) ∇g star n).coverNum
      = min (m + 3 - (m + 3) / 2 + (1 + n)) (m + 3 + min 1 n) := by
  rw [coverNum_join, coverNum_cycle, coverNum_star, V_cycle, V_star]

theorem cliqueCoverNum_join_cycle_star (m n : ℕ) :
    (cycle (m + 4) ∇g star n).cliqueCoverNum = max ((m + 5) / 2) (max 1 n) := by
  rw [cliqueCoverNum_join, cliqueCoverNum_cycle, cliqueCoverNum_star]

theorem maxDeg_join_cycle_star (m n : ℕ) :
    maxDeg (cycle (m + 3) ∇g star (n + 1)) = m + n + 4 := by
  have h := maxDeg_join (G := cycle (m + 3)) (H := star (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_star]; omega)
  rw [maxDeg_cycle, maxDeg_star, V_cycle, V_star] at h
  omega

theorem minDeg_join_cycle_star (m n : ℕ) :
    minDeg (cycle (m + 3) ∇g star (n + 1)) = min (n + 4) (m + 4) := by
  have h := minDeg_join (G := cycle (m + 3)) (H := star (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_star]; omega)
  rw [minDeg_cycle, minDeg_star, V_cycle, V_star] at h
  omega

theorem isConnected_join_cycle_star (m n : ℕ) :
    IsConnected (cycle (m + 3) ∇g star n) :=
  isConnected_join (by rw [V_cycle]; omega) (by rw [V_star]; omega)

theorem numComponents_join_cycle_star (m n : ℕ) :
    (cycle (m + 3) ∇g star n).numComponents = 1 :=
  numComponents_join (by rw [V_cycle]; omega) (by rw [V_star]; omega)

theorem diameter_join_cycle_star (m n : ℕ) :
    (cycle (m + 4) ∇g star n).diameter = 2 := by
  have h : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
    rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 from by omega]
  have h2 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 4) * (m + 3) = m * m + 7 * m + 12 := by ring
    omega
  refine diameter_join_left (by rw [V_star]; omega) ?_
  rw [E_cycle, V_cycle, h]
  omega

theorem girth_join_cycle_star (m n : ℕ) :
    (cycle (m + 4) ∇g star (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join_cycle_star]; omega)

/-! ### The disjoint union of two stars -/

@[simp] theorem V_disjUnion_star (m n : ℕ) : (star m ⊕g star n).V = m + n + 2 := by
  rw [V_disjUnion, V_star, V_star]
  omega

theorem cliqueNum_disjUnion_star (m n : ℕ) :
    (star (m + 1) ⊕g star (n + 1)).cliqueNum = 2 := by
  have h := cliqueNum_disjUnion (star (m + 1)) (star (n + 1))
  rw [cliqueNum_star, cliqueNum_star] at h
  omega

theorem chromNum_disjUnion_star (m n : ℕ) :
    (star (m + 1) ⊕g star (n + 1)).chromNum = 2 := by
  have h := chromNum_disjUnion (star (m + 1)) (star (n + 1))
  rw [chromNum_star, chromNum_star] at h
  omega

theorem indepNum_disjUnion_star (m n : ℕ) :
    (star m ⊕g star n).indepNum = max 1 m + max 1 n := by
  rw [indepNum_disjUnion, indepNum_star, indepNum_star]

theorem coverNum_disjUnion_star (m n : ℕ) :
    (star m ⊕g star n).coverNum = min 1 m + min 1 n := by
  rw [coverNum_disjUnion, coverNum_star, coverNum_star]

theorem cliqueCoverNum_disjUnion_star (m n : ℕ) :
    (star m ⊕g star n).cliqueCoverNum = max 1 m + max 1 n := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_star, cliqueCoverNum_star]

theorem matchNum_disjUnion_star (m n : ℕ) :
    (star m ⊕g star n).matchNum = min m 1 + min n 1 := by
  rw [matchNum_disjUnion, matchNum_star, matchNum_star]

theorem domNum_disjUnion_star (m n : ℕ) : (star m ⊕g star n).domNum = 2 := by
  have h := domNum_disjUnion (star m) (star n)
  rw [domNum_star, domNum_star] at h
  omega

theorem edgeChromNum_disjUnion_star (m n : ℕ) :
    (star m ⊕g star n).edgeChromNum = max m n := by
  rw [edgeChromNum_disjUnion, edgeChromNum_star, edgeChromNum_star]

theorem maxDeg_disjUnion_star (m n : ℕ) :
    maxDeg (star (m + 1) ⊕g star (n + 1)) = max (m + 1) (n + 1) := by
  rw [maxDeg_disjUnion, maxDeg_star, maxDeg_star]

theorem minDeg_disjUnion_star (m n : ℕ) :
    minDeg (star (m + 1) ⊕g star (n + 1)) = 1 := by
  have h := minDeg_disjUnion (G := star (m + 1)) (H := star (n + 1))
    (by rw [V_star]; omega) (by rw [V_star]; omega)
  rw [minDeg_star, minDeg_star] at h
  omega

theorem not_isConnected_disjUnion_star (m n : ℕ) : ¬ IsConnected (star m ⊕g star n) :=
  not_isConnected_disjUnion (by rw [V_star]; omega) (by rw [V_star]; omega)

theorem diameter_disjUnion_star (m n : ℕ) : (star m ⊕g star n).diameter = 0 :=
  diameter_disjUnion (by rw [V_star]; omega) (by rw [V_star]; omega)

theorem radius_disjUnion_star (m n : ℕ) : (star m ⊕g star n).radius = 0 :=
  radius_disjUnion (by rw [V_star]; omega) (by rw [V_star]; omega)

/-! ### The disjoint union of a complete graph and a star -/

@[simp] theorem V_disjUnion_complete_star (m n : ℕ) :
    (complete m ⊕g star n).V = m + n + 1 := by
  rw [V_disjUnion, V_complete, V_star]
  omega

theorem cliqueNum_disjUnion_complete_star (m n : ℕ) :
    (complete m ⊕g star (n + 1)).cliqueNum = max m 2 := by
  rw [cliqueNum_disjUnion, cliqueNum_complete, cliqueNum_star]

theorem chromNum_disjUnion_complete_star (m n : ℕ) :
    (complete m ⊕g star (n + 1)).chromNum = max m 2 := by
  rw [chromNum_disjUnion, chromNum_complete, chromNum_star]

theorem indepNum_disjUnion_complete_star (m n : ℕ) :
    (complete m ⊕g star n).indepNum = min m 1 + max 1 n := by
  rw [indepNum_disjUnion, indepNum_complete, indepNum_star]

theorem coverNum_disjUnion_complete_star (m n : ℕ) :
    (complete m ⊕g star n).coverNum = m - 1 + min 1 n := by
  rw [coverNum_disjUnion, coverNum_complete, coverNum_star]

theorem cliqueCoverNum_disjUnion_complete_star (m n : ℕ) :
    (complete (m + 1) ⊕g star n).cliqueCoverNum = 1 + max 1 n := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_complete, cliqueCoverNum_star]

theorem matchNum_disjUnion_complete_star (m n : ℕ) :
    (complete m ⊕g star n).matchNum = m / 2 + min n 1 := by
  rw [matchNum_disjUnion, matchNum_complete, matchNum_star]

theorem domNum_disjUnion_complete_star (m n : ℕ) :
    (complete (m + 1) ⊕g star n).domNum = 2 := by
  have h := domNum_disjUnion (complete (m + 1)) (star n)
  rw [domNum_complete, domNum_star] at h
  omega

theorem maxDeg_disjUnion_complete_star (m n : ℕ) :
    maxDeg (complete m ⊕g star (n + 1)) = max (m - 1) (n + 1) := by
  rw [maxDeg_disjUnion, maxDeg_complete, maxDeg_star]

theorem minDeg_disjUnion_complete_star (m n : ℕ) :
    minDeg (complete (m + 1) ⊕g star (n + 1)) = min m 1 := by
  have h := minDeg_disjUnion (G := complete (m + 1)) (H := star (n + 1))
    (by rw [V_complete]; omega) (by rw [V_star]; omega)
  rw [minDeg_complete, minDeg_star] at h
  omega

theorem not_isConnected_disjUnion_complete_star (m n : ℕ) :
    ¬ IsConnected (complete (m + 1) ⊕g star n) :=
  not_isConnected_disjUnion (by rw [V_complete]; omega) (by rw [V_star]; omega)

theorem diameter_disjUnion_complete_star (m n : ℕ) :
    (complete (m + 1) ⊕g star n).diameter = 0 :=
  diameter_disjUnion (by rw [V_complete]; omega) (by rw [V_star]; omega)

theorem radius_disjUnion_complete_star (m n : ℕ) :
    (complete (m + 1) ⊕g star n).radius = 0 :=
  radius_disjUnion (by rw [V_complete]; omega) (by rw [V_star]; omega)

/-! ### The disjoint union of a cycle and a star -/

@[simp] theorem V_disjUnion_cycle_star (m n : ℕ) :
    (cycle m ⊕g star n).V = m + n + 1 := by
  rw [V_disjUnion, V_cycle, V_star]
  omega

theorem cliqueNum_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 4) ⊕g star (n + 1)).cliqueNum = 2 := by
  have h := cliqueNum_disjUnion (cycle (m + 4)) (star (n + 1))
  rw [cliqueNum_cycle, cliqueNum_star] at h
  omega

theorem chromNum_disjUnion_cycle_star_even (m n : ℕ) :
    (cycle (2 * m + 2) ⊕g star (n + 1)).chromNum = 2 := by
  have h := chromNum_disjUnion (cycle (2 * m + 2)) (star (n + 1))
  rw [chromNum_cycle_even, chromNum_star] at h
  omega

theorem chromNum_disjUnion_cycle_star_odd (m n : ℕ) :
    (cycle (2 * m + 3) ⊕g star (n + 1)).chromNum = 3 := by
  have h := chromNum_disjUnion (cycle (2 * m + 3)) (star (n + 1))
  rw [chromNum_cycle_odd, chromNum_star] at h
  omega

theorem indepNum_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 3) ⊕g star n).indepNum = (m + 3) / 2 + max 1 n := by
  rw [indepNum_disjUnion, indepNum_cycle, indepNum_star]

theorem coverNum_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 3) ⊕g star n).coverNum = m + 3 - (m + 3) / 2 + min 1 n := by
  rw [coverNum_disjUnion, coverNum_cycle, coverNum_star]

theorem cliqueCoverNum_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 4) ⊕g star n).cliqueCoverNum = (m + 5) / 2 + max 1 n := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_cycle, cliqueCoverNum_star]

theorem matchNum_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 3) ⊕g star n).matchNum = (m + 3) / 2 + min n 1 := by
  rw [matchNum_disjUnion, matchNum_cycle, matchNum_star]

theorem domNum_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 3) ⊕g star n).domNum = (m + 5) / 3 + 1 := by
  rw [domNum_disjUnion, domNum_cycle, domNum_star]

theorem maxDeg_disjUnion_cycle_star (m n : ℕ) :
    maxDeg (cycle (m + 3) ⊕g star (n + 1)) = max 2 (n + 1) := by
  rw [maxDeg_disjUnion, maxDeg_cycle, maxDeg_star]

theorem minDeg_disjUnion_cycle_star (m n : ℕ) :
    minDeg (cycle (m + 3) ⊕g star (n + 1)) = 1 := by
  have h := minDeg_disjUnion (G := cycle (m + 3)) (H := star (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_star]; omega)
  rw [minDeg_cycle, minDeg_star] at h
  omega

theorem not_isConnected_disjUnion_cycle_star (m n : ℕ) :
    ¬ IsConnected (cycle (m + 1) ⊕g star n) :=
  not_isConnected_disjUnion (by rw [V_cycle]; omega) (by rw [V_star]; omega)

theorem diameter_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 1) ⊕g star n).diameter = 0 :=
  diameter_disjUnion (by rw [V_cycle]; omega) (by rw [V_star]; omega)

theorem radius_disjUnion_cycle_star (m n : ℕ) :
    (cycle (m + 1) ⊕g star n).radius = 0 :=
  radius_disjUnion (by rw [V_cycle]; omega) (by rw [V_star]; omega)

/-! ### The join of a path and a complete graph -/

theorem cliqueNum_join_path_complete (m n : ℕ) :
    (path (m + 2) ∇g complete n).cliqueNum = 2 + n := by
  rw [cliqueNum_join, cliqueNum_path, cliqueNum_complete]

theorem chromNum_join_path_complete (m n : ℕ) :
    (path (m + 2) ∇g complete n).chromNum = 2 + n := by
  rw [chromNum_join, chromNum_path, chromNum_complete]

theorem indepNum_join_path_complete (m n : ℕ) :
    (path m ∇g complete n).indepNum = max ((m + 1) / 2) (min n 1) := by
  rw [indepNum_join, indepNum_path, indepNum_complete]

theorem coverNum_join_path_complete (m n : ℕ) :
    (path m ∇g complete n).coverNum = min (m / 2 + n) (m + (n - 1)) := by
  rw [coverNum_join, coverNum_path, coverNum_complete, V_path, V_complete]

theorem cliqueCoverNum_join_path_complete (m n : ℕ) :
    (path (m + 1) ∇g complete (n + 1)).cliqueCoverNum = (m + 2) / 2 := by
  have h := cliqueCoverNum_join (path (m + 1)) (complete (n + 1))
  rw [cliqueCoverNum_path, cliqueCoverNum_complete] at h
  omega

theorem maxDeg_join_path_complete (m n : ℕ) :
    maxDeg (path (m + 3) ∇g complete (n + 1)) = max (n + 3) (m + 3 + n) := by
  have h := maxDeg_join (G := path (m + 3)) (H := complete (n + 1))
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [maxDeg_path, maxDeg_complete, V_path, V_complete] at h
  omega

theorem minDeg_join_path_complete (m n : ℕ) :
    minDeg (path (m + 2) ∇g complete (n + 1)) = min (n + 2) (m + 2 + n) := by
  have h := minDeg_join (G := path (m + 2)) (H := complete (n + 1))
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [minDeg_path, minDeg_complete, V_path, V_complete] at h
  omega

theorem isConnected_join_path_complete (m n : ℕ) :
    IsConnected (path (m + 1) ∇g complete (n + 1)) :=
  isConnected_join (by rw [V_path]; omega) (by rw [V_complete]; omega)

theorem numComponents_join_path_complete (m n : ℕ) :
    (path (m + 1) ∇g complete (n + 1)).numComponents = 1 :=
  numComponents_join (by rw [V_path]; omega) (by rw [V_complete]; omega)

theorem diameter_join_path_complete (m n : ℕ) :
    (path (m + 3) ∇g complete (n + 1)).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 from by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_complete]; omega) ?_
  rw [E_path, V_path, h]
  omega

/-! ### The join of a cycle and a complete graph -/

theorem cliqueNum_join_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ∇g complete n).cliqueNum = 2 + n := by
  rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_complete]

theorem chromNum_join_cycle_complete_even (m n : ℕ) :
    (cycle (2 * m + 2) ∇g complete n).chromNum = 2 + n := by
  rw [chromNum_join, chromNum_cycle_even, chromNum_complete]

theorem chromNum_join_cycle_complete_odd (m n : ℕ) :
    (cycle (2 * m + 3) ∇g complete n).chromNum = 3 + n := by
  rw [chromNum_join, chromNum_cycle_odd, chromNum_complete]

theorem indepNum_join_cycle_complete (m n : ℕ) :
    (cycle (m + 3) ∇g complete n).indepNum = max ((m + 3) / 2) (min n 1) := by
  rw [indepNum_join, indepNum_cycle, indepNum_complete]

theorem coverNum_join_cycle_complete (m n : ℕ) :
    (cycle (m + 3) ∇g complete n).coverNum =
      min (m + 3 - (m + 3) / 2 + n) (m + 3 + (n - 1)) := by
  rw [coverNum_join, coverNum_cycle, coverNum_complete, V_cycle, V_complete]

theorem cliqueCoverNum_join_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ∇g complete (n + 1)).cliqueCoverNum = (m + 5) / 2 := by
  have h := cliqueCoverNum_join (cycle (m + 4)) (complete (n + 1))
  rw [cliqueCoverNum_cycle, cliqueCoverNum_complete] at h
  omega

theorem maxDeg_join_cycle_complete (m n : ℕ) :
    maxDeg (cycle (m + 3) ∇g complete (n + 1)) = max (n + 3) (m + 3 + n) := by
  have h := maxDeg_join (G := cycle (m + 3)) (H := complete (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_complete]; omega)
  rw [maxDeg_cycle, maxDeg_complete, V_cycle, V_complete] at h
  omega

theorem minDeg_join_cycle_complete (m n : ℕ) :
    minDeg (cycle (m + 3) ∇g complete (n + 1)) = min (n + 3) (m + 3 + n) := by
  have h := minDeg_join (G := cycle (m + 3)) (H := complete (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_complete]; omega)
  rw [minDeg_cycle, minDeg_complete, V_cycle, V_complete] at h
  omega

theorem isConnected_join_cycle_complete (m n : ℕ) :
    IsConnected (cycle (m + 1) ∇g complete (n + 1)) :=
  isConnected_join (by rw [V_cycle]; omega) (by rw [V_complete]; omega)

theorem numComponents_join_cycle_complete (m n : ℕ) :
    (cycle (m + 1) ∇g complete (n + 1)).numComponents = 1 :=
  numComponents_join (by rw [V_cycle]; omega) (by rw [V_complete]; omega)

theorem diameter_join_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ∇g complete (n + 1)).diameter = 2 := by
  have h : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
    rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 from by omega]
  have h2 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 4) * (m + 3) = m * m + 7 * m + 12 := by ring
    omega
  refine diameter_join_left (by rw [V_complete]; omega) ?_
  rw [E_cycle, V_cycle, h]
  omega

/-! ### The join of a path and a star -/

@[simp] theorem V_join_path_star (m n : ℕ) : (path m ∇g star n).V = m + n + 1 := by
  rw [V_join, V_path, V_star]
  omega

@[simp] theorem E_join_path_star (m n : ℕ) :
    (path (m + 1) ∇g star n).E = m + n + (m + 1) * (n + 1) := by
  rw [E_join, E_path, E_star, V_path, V_star,
    show 1 + n = n + 1 from by omega]

theorem cliqueNum_join_path_star (m n : ℕ) :
    (path (m + 2) ∇g star (n + 1)).cliqueNum = 4 := by
  have h := cliqueNum_join (path (m + 2)) (star (n + 1))
  rw [cliqueNum_path, cliqueNum_star] at h
  omega

theorem chromNum_join_path_star (m n : ℕ) :
    (path (m + 2) ∇g star (n + 1)).chromNum = 4 := by
  have h := chromNum_join (path (m + 2)) (star (n + 1))
  rw [chromNum_path, chromNum_star] at h
  omega

theorem indepNum_join_path_star (m n : ℕ) :
    (path m ∇g star n).indepNum = max ((m + 1) / 2) (max 1 n) := by
  rw [indepNum_join, indepNum_path, indepNum_star]

theorem coverNum_join_path_star (m n : ℕ) :
    (path m ∇g star n).coverNum = min (m / 2 + (n + 1)) (m + min 1 n) := by
  rw [coverNum_join, coverNum_path, coverNum_star, V_path, V_star,
    show 1 + n = n + 1 from by omega]

theorem cliqueCoverNum_join_path_star (m n : ℕ) :
    (path m ∇g star n).cliqueCoverNum = max ((m + 1) / 2) (max 1 n) := by
  rw [cliqueCoverNum_join, cliqueCoverNum_path, cliqueCoverNum_star]

theorem maxDeg_join_path_star (m n : ℕ) :
    maxDeg (path (m + 3) ∇g star (n + 1)) = m + n + 4 := by
  have h := maxDeg_join (G := path (m + 3)) (H := star (n + 1))
    (by rw [V_path]; omega) (by rw [V_star]; omega)
  rw [maxDeg_path, maxDeg_star, V_path, V_star] at h
  omega

theorem minDeg_join_path_star (m n : ℕ) :
    minDeg (path (m + 2) ∇g star (n + 1)) = min (n + 3) (m + 3) := by
  have h := minDeg_join (G := path (m + 2)) (H := star (n + 1))
    (by rw [V_path]; omega) (by rw [V_star]; omega)
  rw [minDeg_path, minDeg_star, V_path, V_star] at h
  omega

theorem isConnected_join_path_star (m n : ℕ) : IsConnected (path (m + 1) ∇g star n) :=
  isConnected_join (by rw [V_path]; omega) (by rw [V_star]; omega)

theorem numComponents_join_path_star (m n : ℕ) :
    (path (m + 1) ∇g star n).numComponents = 1 :=
  numComponents_join (by rw [V_path]; omega) (by rw [V_star]; omega)

theorem diameter_join_path_star (m n : ℕ) : (path (m + 3) ∇g star n).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 from by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_star]; omega) ?_
  rw [E_path, V_path, h]
  omega

/-! ### The disjoint union of a path and a cycle -/

theorem cliqueNum_disjUnion_path_cycle (m n : ℕ) :
    (path (m + 2) ⊕g cycle (n + 4)).cliqueNum = 2 := by
  have h := cliqueNum_disjUnion (path (m + 2)) (cycle (n + 4))
  rw [cliqueNum_path, cliqueNum_cycle] at h
  omega

theorem chromNum_disjUnion_path_cycle_even (m n : ℕ) :
    (path (m + 2) ⊕g cycle (2 * n + 2)).chromNum = 2 := by
  have h := chromNum_disjUnion (path (m + 2)) (cycle (2 * n + 2))
  rw [chromNum_path, chromNum_cycle_even] at h
  omega

theorem chromNum_disjUnion_path_cycle_odd (m n : ℕ) :
    (path (m + 2) ⊕g cycle (2 * n + 3)).chromNum = 3 := by
  have h := chromNum_disjUnion (path (m + 2)) (cycle (2 * n + 3))
  rw [chromNum_path, chromNum_cycle_odd] at h
  omega

theorem indepNum_disjUnion_path_cycle (m n : ℕ) :
    (path m ⊕g cycle (n + 3)).indepNum = (m + 1) / 2 + (n + 3) / 2 := by
  rw [indepNum_disjUnion, indepNum_path, indepNum_cycle]

theorem coverNum_disjUnion_path_cycle (m n : ℕ) :
    (path m ⊕g cycle (n + 3)).coverNum = m / 2 + (n + 3 - (n + 3) / 2) := by
  rw [coverNum_disjUnion, coverNum_path, coverNum_cycle]

theorem cliqueCoverNum_disjUnion_path_cycle (m n : ℕ) :
    (path m ⊕g cycle (n + 4)).cliqueCoverNum = (m + 1) / 2 + (n + 5) / 2 := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_path, cliqueCoverNum_cycle]

theorem matchNum_disjUnion_path_cycle (m n : ℕ) :
    (path m ⊕g cycle (n + 3)).matchNum = m / 2 + (n + 3) / 2 := by
  rw [matchNum_disjUnion, matchNum_path, matchNum_cycle]

theorem domNum_disjUnion_path_cycle (m n : ℕ) :
    (path (m + 1) ⊕g cycle (n + 3)).domNum = (m + 3) / 3 + (n + 5) / 3 := by
  rw [domNum_disjUnion, domNum_path, domNum_cycle]

theorem edgeChromNum_disjUnion_path_cycle_even (m n : ℕ) :
    (path (m + 3) ⊕g cycle (2 * n + 4)).edgeChromNum = 2 := by
  have h := edgeChromNum_disjUnion (path (m + 3)) (cycle (2 * n + 4))
  rw [edgeChromNum_path, edgeChromNum_cycle_even] at h
  omega

theorem edgeChromNum_disjUnion_path_cycle_odd (m n : ℕ) :
    (path (m + 3) ⊕g cycle (2 * n + 3)).edgeChromNum = 3 := by
  have h := edgeChromNum_disjUnion (path (m + 3)) (cycle (2 * n + 3))
  rw [edgeChromNum_path, edgeChromNum_cycle_odd] at h
  omega

theorem maxDeg_disjUnion_path_cycle (m n : ℕ) :
    maxDeg (path (m + 3) ⊕g cycle (n + 3)) = 2 := by
  have h := maxDeg_disjUnion (path (m + 3)) (cycle (n + 3))
  rw [maxDeg_path, maxDeg_cycle] at h
  omega

theorem minDeg_disjUnion_path_cycle (m n : ℕ) :
    minDeg (path (m + 2) ⊕g cycle (n + 3)) = 1 := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := cycle (n + 3))
    (by rw [V_path]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_path, minDeg_cycle] at h
  omega

theorem not_isConnected_disjUnion_path_cycle (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g cycle (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_cycle]; omega)

theorem diameter_disjUnion_path_cycle (m n : ℕ) :
    (path (m + 1) ⊕g cycle (n + 1)).diameter = 0 :=
  diameter_disjUnion (by rw [V_path]; omega) (by rw [V_cycle]; omega)

theorem radius_disjUnion_path_cycle (m n : ℕ) :
    (path (m + 1) ⊕g cycle (n + 1)).radius = 0 :=
  radius_disjUnion (by rw [V_path]; omega) (by rw [V_cycle]; omega)

/-! ### The disjoint union of a path and a complete graph -/

theorem cliqueNum_disjUnion_path_complete (m n : ℕ) :
    (path (m + 2) ⊕g complete n).cliqueNum = max 2 n := by
  rw [cliqueNum_disjUnion, cliqueNum_path, cliqueNum_complete]

theorem chromNum_disjUnion_path_complete (m n : ℕ) :
    (path (m + 2) ⊕g complete n).chromNum = max 2 n := by
  rw [chromNum_disjUnion, chromNum_path, chromNum_complete]

theorem indepNum_disjUnion_path_complete (m n : ℕ) :
    (path m ⊕g complete n).indepNum = (m + 1) / 2 + min n 1 := by
  rw [indepNum_disjUnion, indepNum_path, indepNum_complete]

theorem coverNum_disjUnion_path_complete (m n : ℕ) :
    (path m ⊕g complete n).coverNum = m / 2 + (n - 1) := by
  rw [coverNum_disjUnion, coverNum_path, coverNum_complete]

theorem cliqueCoverNum_disjUnion_path_complete (m n : ℕ) :
    (path m ⊕g complete (n + 1)).cliqueCoverNum = (m + 1) / 2 + 1 := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_path, cliqueCoverNum_complete]

theorem matchNum_disjUnion_path_complete (m n : ℕ) :
    (path m ⊕g complete n).matchNum = m / 2 + n / 2 := by
  rw [matchNum_disjUnion, matchNum_path, matchNum_complete]

theorem domNum_disjUnion_path_complete (m n : ℕ) :
    (path (m + 1) ⊕g complete (n + 1)).domNum = (m + 3) / 3 + 1 := by
  rw [domNum_disjUnion, domNum_path, domNum_complete]

theorem edgeChromNum_disjUnion_path_complete_odd (m n : ℕ) :
    (path (m + 3) ⊕g complete (2 * n + 3)).edgeChromNum = 2 * n + 3 := by
  have h := edgeChromNum_disjUnion (path (m + 3)) (complete (2 * n + 3))
  rw [edgeChromNum_path, edgeChromNum_complete_odd] at h
  omega

theorem maxDeg_disjUnion_path_complete (m n : ℕ) :
    maxDeg (path (m + 3) ⊕g complete n) = max 2 (n - 1) := by
  rw [maxDeg_disjUnion, maxDeg_path, maxDeg_complete]

theorem minDeg_disjUnion_path_complete (m n : ℕ) :
    minDeg (path (m + 2) ⊕g complete (n + 1)) = min 1 n := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := complete (n + 1))
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [minDeg_path, minDeg_complete] at h
  omega

theorem not_isConnected_disjUnion_path_complete (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_complete]; omega)

theorem diameter_disjUnion_path_complete (m n : ℕ) :
    (path (m + 1) ⊕g complete (n + 1)).diameter = 0 :=
  diameter_disjUnion (by rw [V_path]; omega) (by rw [V_complete]; omega)

theorem radius_disjUnion_path_complete (m n : ℕ) :
    (path (m + 1) ⊕g complete (n + 1)).radius = 0 :=
  radius_disjUnion (by rw [V_path]; omega) (by rw [V_complete]; omega)

/-! ### The disjoint union of a path and a star -/

@[simp] theorem V_disjUnion_path_star (m n : ℕ) : (path m ⊕g star n).V = m + n + 1 := by
  rw [V_disjUnion, V_path, V_star]
  omega

theorem cliqueNum_disjUnion_path_star (m n : ℕ) :
    (path (m + 2) ⊕g star (n + 1)).cliqueNum = 2 := by
  have h := cliqueNum_disjUnion (path (m + 2)) (star (n + 1))
  rw [cliqueNum_path, cliqueNum_star] at h
  omega

theorem chromNum_disjUnion_path_star (m n : ℕ) :
    (path (m + 2) ⊕g star (n + 1)).chromNum = 2 := by
  have h := chromNum_disjUnion (path (m + 2)) (star (n + 1))
  rw [chromNum_path, chromNum_star] at h
  omega

theorem indepNum_disjUnion_path_star (m n : ℕ) :
    (path m ⊕g star n).indepNum = (m + 1) / 2 + max 1 n := by
  rw [indepNum_disjUnion, indepNum_path, indepNum_star]

theorem coverNum_disjUnion_path_star (m n : ℕ) :
    (path m ⊕g star n).coverNum = m / 2 + min 1 n := by
  rw [coverNum_disjUnion, coverNum_path, coverNum_star]

theorem cliqueCoverNum_disjUnion_path_star (m n : ℕ) :
    (path m ⊕g star n).cliqueCoverNum = (m + 1) / 2 + max 1 n := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_path, cliqueCoverNum_star]

theorem matchNum_disjUnion_path_star (m n : ℕ) :
    (path m ⊕g star n).matchNum = m / 2 + min n 1 := by
  rw [matchNum_disjUnion, matchNum_path, matchNum_star]

theorem domNum_disjUnion_path_star (m n : ℕ) :
    (path (m + 1) ⊕g star n).domNum = (m + 3) / 3 + 1 := by
  rw [domNum_disjUnion, domNum_path, domNum_star]

theorem edgeChromNum_disjUnion_path_star (m n : ℕ) :
    (path (m + 3) ⊕g star n).edgeChromNum = max 2 n := by
  rw [edgeChromNum_disjUnion, edgeChromNum_path, edgeChromNum_star]

theorem maxDeg_disjUnion_path_star (m n : ℕ) :
    maxDeg (path (m + 3) ⊕g star (n + 1)) = max 2 (n + 1) := by
  rw [maxDeg_disjUnion, maxDeg_path, maxDeg_star]

theorem minDeg_disjUnion_path_star (m n : ℕ) :
    minDeg (path (m + 2) ⊕g star (n + 1)) = 1 := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := star (n + 1))
    (by rw [V_path]; omega) (by rw [V_star]; omega)
  rw [minDeg_path, minDeg_star] at h
  omega

theorem not_isConnected_disjUnion_path_star (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g star n) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_star]; omega)

theorem diameter_disjUnion_path_star (m n : ℕ) :
    (path (m + 1) ⊕g star n).diameter = 0 :=
  diameter_disjUnion (by rw [V_path]; omega) (by rw [V_star]; omega)

theorem radius_disjUnion_path_star (m n : ℕ) :
    (path (m + 1) ⊕g star n).radius = 0 :=
  radius_disjUnion (by rw [V_path]; omega) (by rw [V_star]; omega)

/-! ### The Mycielskian of a double star -/

@[simp] theorem V_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar m n)).V = 2 * m + 2 * n + 5 := by
  rw [V_mycielskian, V_doubleStar]
  omega

@[simp] theorem E_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar m n)).E = 4 * m + 4 * n + 5 := by
  rw [E_mycielskian, E_doubleStar, V_doubleStar]
  omega

theorem chromNum_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar m n)).chromNum = 3 := by
  have h := chromNum_mycielskian (doubleStar m n)
  rw [chromNum_doubleStar] at h
  omega

theorem cliqueNum_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar m n)).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (doubleStar m n) (by rw [V_doubleStar]; omega)
  rw [cliqueNum_doubleStar] at h
  omega

theorem maxDeg_mycielskian_doubleStar (m n : ℕ) :
    maxDeg (mycielskian (doubleStar m n)) = max (2 * max m n + 2) (m + n + 2) := by
  have h := maxDeg_mycielskian (doubleStar m n)
  rw [maxDeg_doubleStar, V_doubleStar] at h
  omega

theorem minDeg_mycielskian_doubleStar (m n : ℕ) :
    minDeg (mycielskian (doubleStar m n)) = 2 := by
  have h := minDeg_mycielskian (doubleStar m n) (by rw [V_doubleStar]; omega)
  rw [minDeg_doubleStar, V_doubleStar] at h
  omega

theorem domNum_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar (m + 1) (n + 1))).domNum = 3 := by
  have h := domNum_mycielskian (doubleStar (m + 1) (n + 1)) (by rw [V_doubleStar]; omega)
  rw [domNum_doubleStar] at h
  omega

theorem isConnected_mycielskian_doubleStar (m n : ℕ) :
    IsConnected (mycielskian (doubleStar m n)) :=
  isConnected_mycielskian _ (by rw [minDeg_doubleStar]; omega)

theorem numComponents_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar m n)).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_doubleStar]; omega)

theorem radius_mycielskian_doubleStar (m n : ℕ) :
    (mycielskian (doubleStar m n)).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_doubleStar]; omega)

theorem two_le_diameter_mycielskian_doubleStar (m n : ℕ) :
    2 ≤ (mycielskian (doubleStar m n)).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_doubleStar]; omega)

theorem diameter_mycielskian_doubleStar_le_four (m n : ℕ) :
    (mycielskian (doubleStar m n)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_doubleStar]; omega)

theorem four_le_girth_mycielskian_doubleStar (m n : ℕ) :
    4 ≤ (mycielskian (doubleStar m n)).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_doubleStar]) (by rw [E_doubleStar]; omega)

theorem indepNum_mycielskian_doubleStar_le (m n : ℕ) :
    (mycielskian (doubleStar (m + 1) (n + 1))).indepNum ≤ 2 * m + 2 * n + 6 := by
  have h := indepNum_mycielskian_le (doubleStar (m + 1) (n + 1)) (by rw [V_doubleStar]; omega)
  rw [indepNum_doubleStar, V_doubleStar] at h
  omega

theorem coverNum_mycielskian_doubleStar_le (m n : ℕ) :
    (mycielskian (doubleStar m n)).coverNum ≤ m + n + 3 := by
  have h := coverNum_mycielskian_le (doubleStar m n)
  rw [V_doubleStar] at h
  omega

theorem V_le_indepNum_mycielskian_doubleStar (m n : ℕ) :
    m + n + 2 ≤ (mycielskian (doubleStar m n)).indepNum := by
  have h := V_le_indepNum_mycielskian (doubleStar m n)
  rw [V_doubleStar] at h
  omega

/-! ### The Mycielskian of a rook's graph -/

theorem chromNum_mycielskian_rook (m n : ℕ) :
    (mycielskian (rook (m + 1) (n + 1))).chromNum = max (m + 1) (n + 1) + 1 := by
  rw [chromNum_mycielskian, chromNum_rook]

theorem cliqueNum_mycielskian_rook (m n : ℕ) :
    (mycielskian (rook (m + 1) (n + 1))).cliqueNum = max (max (m + 1) (n + 1)) 2 := by
  have h := cliqueNum_mycielskian (rook (m + 1) (n + 1)) (by rw [V_rook]; positivity)
  rw [cliqueNum_rook (m := m + 1) (n := n + 1) (by omega) (by omega)] at h
  omega

theorem maxDeg_mycielskian_rook (m n : ℕ) :
    maxDeg (mycielskian (rook (m + 1) (n + 1))) =
      max (2 * (n + m)) ((m + 1) * (n + 1)) := by
  have h := maxDeg_mycielskian (rook (m + 1) (n + 1))
  rw [maxDeg_rook, V_rook] at h
  omega

theorem minDeg_mycielskian_rook (m n : ℕ) :
    minDeg (mycielskian (rook (m + 1) (n + 1))) =
      min (min (2 * (n + m)) (n + m + 1)) ((m + 1) * (n + 1)) := by
  have h := minDeg_mycielskian (rook (m + 1) (n + 1)) (by rw [V_rook]; positivity)
  rw [minDeg_rook, V_rook] at h
  omega

theorem domNum_mycielskian_rook (m n : ℕ) :
    (mycielskian (rook (m + 1) (n + 1))).domNum = min (m + 1) (n + 1) + 1 := by
  have h := domNum_mycielskian (rook (m + 1) (n + 1)) (by rw [V_rook]; positivity)
  rw [domNum_rook] at h
  omega

theorem isConnected_mycielskian_rook (m n : ℕ) :
    IsConnected (mycielskian (rook (m + 2) (n + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_rook]; omega)

theorem numComponents_mycielskian_rook (m n : ℕ) :
    (mycielskian (rook (m + 2) (n + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_rook]; omega)

theorem radius_mycielskian_rook (m n : ℕ) :
    (mycielskian (rook (m + 2) (n + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_rook]; omega)

theorem two_le_diameter_mycielskian_rook (m n : ℕ) :
    2 ≤ (mycielskian (rook (m + 2) (n + 1))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_rook]; omega)

theorem diameter_mycielskian_rook_le_four (m n : ℕ) :
    (mycielskian (rook (m + 2) (n + 1))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_rook]; omega)

theorem indepNum_mycielskian_rook_le (m n : ℕ) :
    (mycielskian (rook (m + 1) (n + 1))).indepNum ≤
      (m + 1) * (n + 1) + min (m + 1) (n + 1) := by
  have h := indepNum_mycielskian_le (rook (m + 1) (n + 1)) (by rw [V_rook]; positivity)
  rw [indepNum_rook, V_rook] at h
  omega

theorem coverNum_mycielskian_rook_le (m n : ℕ) :
    (mycielskian (rook m n)).coverNum ≤ m * n + 1 := by
  have h := coverNum_mycielskian_le (rook m n)
  rw [V_rook] at h
  omega

theorem girth_mycielskian_rook (m n : ℕ) :
    (mycielskian (rook (m + 3) (n + 1))).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_mycielskian (rook (m + 3) (n + 1)) (by rw [V_rook]; positivity)
  rw [cliqueNum_rook (m := m + 3) (n := n + 1) (by omega) (by omega)] at h
  omega

/-! ### The disjoint union of a cycle and a complete graph -/

theorem cliqueNum_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ⊕g complete n).cliqueNum = max 2 n := by
  rw [cliqueNum_disjUnion, cliqueNum_cycle, cliqueNum_complete]

theorem chromNum_disjUnion_cycle_complete_even (m n : ℕ) :
    (cycle (2 * m + 2) ⊕g complete n).chromNum = max 2 n := by
  rw [chromNum_disjUnion, chromNum_cycle_even, chromNum_complete]

theorem chromNum_disjUnion_cycle_complete_odd (m n : ℕ) :
    (cycle (2 * m + 3) ⊕g complete n).chromNum = max 3 n := by
  rw [chromNum_disjUnion, chromNum_cycle_odd, chromNum_complete]

theorem indepNum_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 3) ⊕g complete n).indepNum = (m + 3) / 2 + min n 1 := by
  rw [indepNum_disjUnion, indepNum_cycle, indepNum_complete]

theorem coverNum_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 3) ⊕g complete n).coverNum = m + 3 - (m + 3) / 2 + (n - 1) := by
  rw [coverNum_disjUnion, coverNum_cycle, coverNum_complete]

theorem cliqueCoverNum_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ⊕g complete (n + 1)).cliqueCoverNum = (m + 5) / 2 + 1 := by
  rw [cliqueCoverNum_disjUnion, cliqueCoverNum_cycle, cliqueCoverNum_complete]

theorem matchNum_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 3) ⊕g complete n).matchNum = (m + 3) / 2 + n / 2 := by
  rw [matchNum_disjUnion, matchNum_cycle, matchNum_complete]

theorem domNum_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 3) ⊕g complete (n + 1)).domNum = (m + 5) / 3 + 1 := by
  rw [domNum_disjUnion, domNum_cycle, domNum_complete]

theorem edgeChromNum_disjUnion_cycle_complete_odd (m n : ℕ) :
    (cycle (2 * m + 4) ⊕g complete (2 * n + 3)).edgeChromNum = 2 * n + 3 := by
  have h := edgeChromNum_disjUnion (cycle (2 * m + 4)) (complete (2 * n + 3))
  rw [edgeChromNum_cycle_even, edgeChromNum_complete_odd] at h
  omega

theorem maxDeg_disjUnion_cycle_complete (m n : ℕ) :
    maxDeg (cycle (m + 3) ⊕g complete n) = max 2 (n - 1) := by
  rw [maxDeg_disjUnion, maxDeg_cycle, maxDeg_complete]

theorem minDeg_disjUnion_cycle_complete (m n : ℕ) :
    minDeg (cycle (m + 3) ⊕g complete (n + 1)) = min 2 n := by
  have h := minDeg_disjUnion (G := cycle (m + 3)) (H := complete (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_complete]; omega)
  rw [minDeg_cycle, minDeg_complete] at h
  omega

theorem not_isConnected_disjUnion_cycle_complete (m n : ℕ) :
    ¬ IsConnected (cycle (m + 1) ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_cycle]; omega) (by rw [V_complete]; omega)

theorem diameter_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 1) ⊕g complete (n + 1)).diameter = 0 :=
  diameter_disjUnion (by rw [V_cycle]; omega) (by rw [V_complete]; omega)

theorem radius_disjUnion_cycle_complete (m n : ℕ) :
    (cycle (m + 1) ⊕g complete (n + 1)).radius = 0 :=
  radius_disjUnion (by rw [V_cycle]; omega) (by rw [V_complete]; omega)

/-! ### The Mycielskian of a triangular graph -/

theorem chromNum_mycielskian_triangular (n : ℕ) :
    (mycielskian (triangular n)).chromNum = (complete n).edgeChromNum + 1 := by
  rw [chromNum_mycielskian, chromNum_triangular]

theorem cliqueNum_mycielskian_triangular (n : ℕ) :
    (mycielskian (triangular (n + 4))).cliqueNum = n + 3 := by
  have h := cliqueNum_mycielskian (triangular (n + 4))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
  rw [cliqueNum_triangular] at h
  omega

theorem maxDeg_mycielskian_triangular (n : ℕ) :
    maxDeg (mycielskian (triangular (n + 2))) = max (4 * n) ((n + 2).choose 2) := by
  have h := maxDeg_mycielskian (triangular (n + 2))
  rw [maxDeg_triangular, V_triangular] at h
  omega

theorem minDeg_mycielskian_triangular (n : ℕ) :
    minDeg (mycielskian (triangular (n + 2)))
      = min (min (4 * n) (2 * n + 1)) ((n + 2).choose 2) := by
  have h := minDeg_mycielskian (triangular (n + 2))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
  rw [minDeg_triangular, V_triangular] at h
  omega

theorem domNum_mycielskian_triangular (n : ℕ) :
    (mycielskian (triangular (n + 2))).domNum = (n + 2) / 2 + 1 := by
  have h := domNum_mycielskian (triangular (n + 2))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
  rw [domNum_triangular] at h
  omega

theorem isConnected_mycielskian_triangular (n : ℕ) :
    IsConnected (mycielskian (triangular (n + 3))) :=
  isConnected_mycielskian _ (by rw [minDeg_triangular]; omega)

theorem numComponents_mycielskian_triangular (n : ℕ) :
    (mycielskian (triangular (n + 3))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_triangular]; omega)

theorem radius_mycielskian_triangular (n : ℕ) :
    (mycielskian (triangular (n + 3))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_triangular]; omega)

theorem two_le_diameter_mycielskian_triangular (n : ℕ) :
    2 ≤ (mycielskian (triangular (n + 3))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_triangular]; omega)

theorem diameter_mycielskian_triangular_le_four (n : ℕ) :
    (mycielskian (triangular (n + 3))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_triangular]; omega)

theorem indepNum_mycielskian_triangular_le (n : ℕ) :
    (mycielskian (triangular (n + 2))).indepNum ≤ (n + 2).choose 2 + (n + 2) / 2 := by
  have h := indepNum_mycielskian_le (triangular (n + 2))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
  rw [indepNum_triangular, V_triangular] at h
  omega

theorem coverNum_mycielskian_triangular_le (n : ℕ) :
    (mycielskian (triangular n)).coverNum ≤ n.choose 2 + 1 := by
  have h := coverNum_mycielskian_le (triangular n)
  rw [V_triangular] at h
  omega

theorem V_le_indepNum_mycielskian_triangular (n : ℕ) :
    n.choose 2 ≤ (mycielskian (triangular n)).indepNum := by
  have h := V_le_indepNum_mycielskian (triangular n)
  rw [V_triangular] at h
  omega

theorem girth_mycielskian_triangular (n : ℕ) :
    (mycielskian (triangular (n + 4))).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_mycielskian_triangular]
  omega

/-! ### The Mycielskian of a Kneser graph -/

@[simp] theorem E_mycielskian_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (mycielskian (kneser n k)).E
      = 3 * (n.choose k * (n - k).choose k / 2) + n.choose k := by
  rw [E_mycielskian, E_kneser n hk, V_kneser]

theorem maxDeg_mycielskian_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    maxDeg (mycielskian (kneser n k)) = max (2 * (n - k).choose k) (n.choose k) := by
  have h := maxDeg_mycielskian (kneser n k)
  rw [maxDeg_kneser n k hk hkn, V_kneser] at h
  omega

theorem minDeg_mycielskian_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    minDeg (mycielskian (kneser n k))
      = min (min (2 * (n - k).choose k) ((n - k).choose k + 1)) (n.choose k) := by
  have h := minDeg_mycielskian (kneser n k)
    (by rw [V_kneser]; exact Nat.choose_pos hkn)
  rw [minDeg_kneser n k hk hkn, V_kneser] at h
  omega

theorem isConnected_mycielskian_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    IsConnected (mycielskian (kneser n k)) :=
  isConnected_mycielskian _
    (by rw [minDeg_kneser n k hk (by omega)]; exact Nat.choose_pos (by omega))

theorem numComponents_mycielskian_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (mycielskian (kneser n k)).numComponents = 1 :=
  numComponents_mycielskian _
    (by rw [minDeg_kneser n k hk (by omega)]; exact Nat.choose_pos (by omega))

theorem radius_mycielskian_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (mycielskian (kneser n k)).radius = 2 :=
  radius_mycielskian _
    (by rw [minDeg_kneser n k hk (by omega)]; exact Nat.choose_pos (by omega))

theorem two_le_diameter_mycielskian_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    2 ≤ (mycielskian (kneser n k)).diameter :=
  two_le_diameter_mycielskian _
    (by rw [minDeg_kneser n k hk (by omega)]; exact Nat.choose_pos (by omega))

theorem diameter_mycielskian_kneser_le_four (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (mycielskian (kneser n k)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _
    (by rw [minDeg_kneser n k hk (by omega)]; exact Nat.choose_pos (by omega))

theorem coverNum_mycielskian_kneser_le (n k : ℕ) :
    (mycielskian (kneser n k)).coverNum ≤ n.choose k + 1 := by
  have h := coverNum_mycielskian_le (kneser n k)
  rw [V_kneser] at h
  omega

theorem V_le_indepNum_mycielskian_kneser (n k : ℕ) :
    n.choose k ≤ (mycielskian (kneser n k)).indepNum := by
  have h := V_le_indepNum_mycielskian (kneser n k)
  rw [V_kneser] at h
  omega

/-! ### The Mycielskian of a Johnson graph -/

@[simp] theorem E_mycielskian_johnson {n k : ℕ} (hk : k ≤ n) :
    (mycielskian (johnson n k)).E
      = 3 * (n.choose k * (k * (n - k)) / 2) + n.choose k := by
  rw [E_mycielskian, E_johnson hk, V_johnson]

theorem maxDeg_mycielskian_johnson {n k : ℕ} (hk : k ≤ n) :
    maxDeg (mycielskian (johnson n k)) = max (2 * (k * (n - k))) (n.choose k) := by
  have h := maxDeg_mycielskian (johnson n k)
  rw [maxDeg_johnson hk, V_johnson] at h
  omega

theorem minDeg_mycielskian_johnson {n k : ℕ} (hk : k ≤ n) :
    minDeg (mycielskian (johnson n k))
      = min (min (2 * (k * (n - k))) (k * (n - k) + 1)) (n.choose k) := by
  have h := minDeg_mycielskian (johnson n k)
    (by rw [V_johnson]; exact Nat.choose_pos hk)
  rw [minDeg_johnson hk, V_johnson] at h
  omega

theorem isConnected_mycielskian_johnson {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    IsConnected (mycielskian (johnson n k)) :=
  isConnected_mycielskian _
    (by rw [minDeg_johnson (by omega)]; exact Nat.mul_pos (by omega) (by omega))

theorem numComponents_mycielskian_johnson {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    (mycielskian (johnson n k)).numComponents = 1 :=
  numComponents_mycielskian _
    (by rw [minDeg_johnson (by omega)]; exact Nat.mul_pos (by omega) (by omega))

theorem radius_mycielskian_johnson {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    (mycielskian (johnson n k)).radius = 2 :=
  radius_mycielskian _
    (by rw [minDeg_johnson (by omega)]; exact Nat.mul_pos (by omega) (by omega))

theorem two_le_diameter_mycielskian_johnson {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    2 ≤ (mycielskian (johnson n k)).diameter :=
  two_le_diameter_mycielskian _
    (by rw [minDeg_johnson (by omega)]; exact Nat.mul_pos (by omega) (by omega))

theorem diameter_mycielskian_johnson_le_four {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    (mycielskian (johnson n k)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _
    (by rw [minDeg_johnson (by omega)]; exact Nat.mul_pos (by omega) (by omega))

theorem coverNum_mycielskian_johnson_le (n k : ℕ) :
    (mycielskian (johnson n k)).coverNum ≤ n.choose k + 1 := by
  have h := coverNum_mycielskian_le (johnson n k)
  rw [V_johnson] at h
  omega

theorem V_le_indepNum_mycielskian_johnson (n k : ℕ) :
    n.choose k ≤ (mycielskian (johnson n k)).indepNum := by
  have h := V_le_indepNum_mycielskian (johnson n k)
  rw [V_johnson] at h
  omega

/-! ### The Mycielskian of a Turán graph -/

theorem minDeg_turan_pos {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) : 0 < minDeg (turan n r) := by
  have hm : n * 2 ≤ n * r := Nat.mul_le_mul_left n hr
  have hlt : (n + r - 1) / r < n := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < r)]
    omega
  rw [minDeg_turan (by omega) hn]
  omega

@[simp] theorem V_mycielskian_turan (n r : ℕ) : (mycielskian (turan n r)).V = 2 * n + 1 := by
  rw [V_mycielskian, V_turan]

theorem E_mycielskian_turan (n r : ℕ) :
    (mycielskian (turan n r)).E
        + 3 * ((n % r) * ((n / r + 1).choose 2) + (r - n % r) * ((n / r).choose 2))
      = 3 * n.choose 2 + n := by
  have h := E_turan n r
  rw [E_mycielskian, V_turan]
  omega

theorem chromNum_mycielskian_turan {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) :
    (mycielskian (turan n r)).chromNum = r + 1 := by
  rw [chromNum_mycielskian, chromNum_turan hr hn]

theorem cliqueNum_mycielskian_turan {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) :
    (mycielskian (turan n r)).cliqueNum = max r 2 := by
  have h := cliqueNum_mycielskian (turan n r) (by rw [V_turan]; omega)
  rw [cliqueNum_turan hr hn] at h
  omega

theorem maxDeg_mycielskian_turan {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) :
    maxDeg (mycielskian (turan n r)) = max (2 * (n - n / r)) n := by
  have h := maxDeg_mycielskian (turan n r)
  rw [maxDeg_turan hr hn, V_turan] at h
  omega

theorem minDeg_mycielskian_turan {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) :
    minDeg (mycielskian (turan n r))
      = min (min (2 * (n - (n + r - 1) / r)) (n - (n + r - 1) / r + 1)) n := by
  have h := minDeg_mycielskian (turan n r) (by rw [V_turan]; omega)
  rw [minDeg_turan hr hn, V_turan] at h
  omega

theorem domNum_mycielskian_turan {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r ≤ n) :
    (mycielskian (turan n r)).domNum = 3 := by
  have h := domNum_mycielskian (turan n r) (by rw [V_turan]; omega)
  rw [domNum_turan hr hn] at h
  omega

theorem isConnected_mycielskian_turan {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    IsConnected (mycielskian (turan n r)) :=
  isConnected_mycielskian _ (minDeg_turan_pos hr hn)

theorem numComponents_mycielskian_turan {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    (mycielskian (turan n r)).numComponents = 1 :=
  numComponents_mycielskian _ (minDeg_turan_pos hr hn)

theorem radius_mycielskian_turan {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    (mycielskian (turan n r)).radius = 2 :=
  radius_mycielskian _ (minDeg_turan_pos hr hn)

theorem two_le_diameter_mycielskian_turan {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    2 ≤ (mycielskian (turan n r)).diameter :=
  two_le_diameter_mycielskian _ (minDeg_turan_pos hr hn)

theorem diameter_mycielskian_turan_le_four {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) :
    (mycielskian (turan n r)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (minDeg_turan_pos hr hn)

theorem matchNum_mycielskian_turan {m r : ℕ} (hr : 2 ≤ r) (hn : r ≤ 2 * m) :
    (mycielskian (turan (2 * m) r)).matchNum = 2 * m := by
  have h := matchNum_mycielskian (turan (2 * m) r)
    (by rw [matchNum_turan hr hn, V_turan]; omega)
  rw [V_turan] at h
  omega

theorem cliqueCoverNum_mycielskian_turan (m : ℕ) :
    (mycielskian (turan (2 * m + 2) 2)).cliqueCoverNum = 2 * m + 3 := by
  have h := cliqueCoverNum_mycielskian (turan (2 * m + 2) 2) (by rw [V_turan]; omega)
    (by rw [cliqueNum_turan (by omega) (by omega)])
    (by rw [matchNum_turan (by omega) (by omega), V_turan]; omega)
  rw [V_turan] at h
  omega

theorem indepNum_mycielskian_turan_le {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) :
    (mycielskian (turan n r)).indepNum ≤ n + (n + r - 1) / r := by
  have h := indepNum_mycielskian_le (turan n r) (by rw [V_turan]; omega)
  rw [indepNum_turan hr hn, V_turan] at h
  omega

theorem coverNum_mycielskian_turan_le (n r : ℕ) :
    (mycielskian (turan n r)).coverNum ≤ n + 1 := by
  have h := coverNum_mycielskian_le (turan n r)
  rw [V_turan] at h
  omega

theorem V_le_indepNum_mycielskian_turan (n r : ℕ) :
    n ≤ (mycielskian (turan n r)).indepNum := by
  have h := V_le_indepNum_mycielskian (turan n r)
  rw [V_turan] at h
  omega

theorem girth_mycielskian_turan {n r : ℕ} (hr : 3 ≤ r) (hn : r ≤ n) :
    (mycielskian (turan n r)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_mycielskian_turan (by omega) hn]
  omega

/-! ### The Mycielskian of a complete multipartite graph -/

theorem E_mycielskian_completeMultipartite (ds : List ℕ) :
    (mycielskian (completeMultipartite ds)).E + 3 * (ds.map (·.choose 2)).sum
      = 3 * ds.sum.choose 2 + ds.sum := by
  have h := E_completeMultipartite ds
  rw [E_mycielskian, V_completeMultipartite]
  omega

theorem chromNum_mycielskian_completeMultipartite (ds : List ℕ) :
    (mycielskian (completeMultipartite ds)).chromNum
      = (ds.map fun d ↦ min d 1).sum + 1 := by
  rw [chromNum_mycielskian, chromNum_completeMultipartite]

theorem cliqueNum_mycielskian_completeMultipartite (ds : List ℕ) (hs : 0 < ds.sum) :
    (mycielskian (completeMultipartite ds)).cliqueNum
      = max (ds.map (min · 1)).sum 2 := by
  have h := cliqueNum_mycielskian (completeMultipartite ds)
    (by rw [V_completeMultipartite]; omega)
  rw [cliqueNum_completeMultipartite] at h
  omega

theorem indepNum_mycielskian_completeMultipartite_le (ds : List ℕ) (hs : 0 < ds.sum) :
    (mycielskian (completeMultipartite ds)).indepNum ≤ ds.sum + (ds.max?).getD 0 := by
  have h := indepNum_mycielskian_le (completeMultipartite ds)
    (by rw [V_completeMultipartite]; omega)
  rw [indepNum_completeMultipartite, V_completeMultipartite] at h
  omega

theorem coverNum_mycielskian_completeMultipartite_le (ds : List ℕ) :
    (mycielskian (completeMultipartite ds)).coverNum ≤ ds.sum + 1 := by
  have h := coverNum_mycielskian_le (completeMultipartite ds)
  rw [V_completeMultipartite] at h
  omega

theorem V_le_indepNum_mycielskian_completeMultipartite (ds : List ℕ) :
    ds.sum ≤ (mycielskian (completeMultipartite ds)).indepNum := by
  have h := V_le_indepNum_mycielskian (completeMultipartite ds)
  rw [V_completeMultipartite] at h
  omega

/-! ### The Mycielskian of the Grötzsch graph -/

theorem chromNum_mycielskian_grotzsch : (mycielskian grotzsch).chromNum = 5 := by
  have h := chromNum_mycielskian grotzsch
  rw [chromNum_grotzsch] at h
  omega

theorem cliqueNum_mycielskian_grotzsch : (mycielskian grotzsch).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian grotzsch (by rw [V_grotzsch]; omega)
  rw [cliqueNum_grotzsch] at h
  omega

theorem maxDeg_mycielskian_grotzsch : maxDeg (mycielskian grotzsch) = 11 := by
  have h := maxDeg_mycielskian grotzsch
  rw [maxDeg_grotzsch, V_grotzsch] at h
  omega

theorem minDeg_mycielskian_grotzsch : minDeg (mycielskian grotzsch) = 4 := by
  have h := minDeg_mycielskian grotzsch (by rw [V_grotzsch]; omega)
  rw [minDeg_grotzsch, V_grotzsch] at h
  omega

theorem domNum_mycielskian_grotzsch : (mycielskian grotzsch).domNum = 4 := by
  have h := domNum_mycielskian grotzsch (by rw [V_grotzsch]; omega)
  rw [domNum_grotzsch] at h
  omega

theorem isConnected_mycielskian_grotzsch : IsConnected (mycielskian grotzsch) :=
  isConnected_mycielskian _ (by rw [minDeg_grotzsch]; omega)

theorem numComponents_mycielskian_grotzsch : (mycielskian grotzsch).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_grotzsch]; omega)

theorem radius_mycielskian_grotzsch : (mycielskian grotzsch).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_grotzsch]; omega)

theorem two_le_diameter_mycielskian_grotzsch : 2 ≤ (mycielskian grotzsch).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_grotzsch]; omega)

theorem diameter_mycielskian_grotzsch_le_four : (mycielskian grotzsch).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_grotzsch]; omega)

theorem four_le_girth_mycielskian_grotzsch : 4 ≤ (mycielskian grotzsch).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_grotzsch]) (by rw [E_grotzsch]; omega)

theorem coverNum_mycielskian_grotzsch_le : (mycielskian grotzsch).coverNum ≤ 12 := by
  have h := coverNum_mycielskian_le grotzsch
  rw [V_grotzsch] at h
  omega

theorem V_le_indepNum_mycielskian_grotzsch : 11 ≤ (mycielskian grotzsch).indepNum := by
  have h := V_le_indepNum_mycielskian grotzsch
  rw [V_grotzsch] at h
  omega

/-! ### The Mycielskian of a grid graph -/

theorem chromNum_mycielskian_grid (m n : ℕ) :
    (mycielskian (path (m + 2) □g path (n + 2))).chromNum = 3 := by
  have h := chromNum_mycielskian (path (m + 2) □g path (n + 2))
  rw [chromNum_grid] at h
  omega

theorem cliqueNum_mycielskian_grid (m n : ℕ) :
    (mycielskian (path (m + 2) □g path (n + 2))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (path (m + 2) □g path (n + 2))
    (by rw [V_grid]; positivity)
  rw [cliqueNum_grid] at h
  omega

theorem maxDeg_mycielskian_grid (m n : ℕ) :
    maxDeg (mycielskian (path (m + 3) □g path (n + 3)))
      = max 8 ((m + 3) * (n + 3)) := by
  have h := maxDeg_mycielskian (path (m + 3) □g path (n + 3))
  rw [maxDeg_grid, V_grid] at h
  omega

theorem minDeg_mycielskian_grid (m n : ℕ) :
    minDeg (mycielskian (path (m + 2) □g path (n + 2)))
      = min 3 ((m + 2) * (n + 2)) := by
  have h := minDeg_mycielskian (path (m + 2) □g path (n + 2))
    (by rw [V_grid]; positivity)
  rw [minDeg_grid, V_grid] at h
  omega

theorem isConnected_mycielskian_grid (m n : ℕ) :
    IsConnected (mycielskian (path (m + 2) □g path (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_grid]; omega)

theorem numComponents_mycielskian_grid (m n : ℕ) :
    (mycielskian (path (m + 2) □g path (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_grid]; omega)

theorem radius_mycielskian_grid (m n : ℕ) :
    (mycielskian (path (m + 2) □g path (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_grid]; omega)

theorem four_le_girth_mycielskian_grid (m n : ℕ) :
    4 ≤ (mycielskian (path (m + 2) □g path (n + 2))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_grid]) (by rw [E_grid]; positivity)

theorem coverNum_mycielskian_grid_le (m n : ℕ) :
    (mycielskian (path m □g path n)).coverNum ≤ m * n + 1 := by
  have h := coverNum_mycielskian_le (path m □g path n)
  rw [V_grid] at h
  omega

/-! ### The Mycielskian of a king graph -/

theorem chromNum_mycielskian_king (m n : ℕ) :
    (mycielskian (path (m + 2) ⊠g path (n + 2))).chromNum = 5 := by
  have h := chromNum_mycielskian (path (m + 2) ⊠g path (n + 2))
  rw [chromNum_king] at h
  omega

theorem cliqueNum_mycielskian_king (m n : ℕ) :
    (mycielskian (path (m + 2) ⊠g path (n + 2))).cliqueNum = 4 := by
  have h := cliqueNum_mycielskian (path (m + 2) ⊠g path (n + 2))
    (by rw [V_king]; positivity)
  rw [cliqueNum_king] at h
  omega

theorem maxDeg_mycielskian_king (m n : ℕ) :
    maxDeg (mycielskian (path (m + 3) ⊠g path (n + 3)))
      = max 16 ((m + 3) * (n + 3)) := by
  have h := maxDeg_mycielskian (path (m + 3) ⊠g path (n + 3))
  rw [maxDeg_king, V_king] at h
  omega

theorem minDeg_mycielskian_king (m n : ℕ) :
    minDeg (mycielskian (path (m + 2) ⊠g path (n + 2)))
      = min 4 ((m + 2) * (n + 2)) := by
  have h := minDeg_mycielskian (path (m + 2) ⊠g path (n + 2))
    (by rw [V_king]; positivity)
  rw [minDeg_king, V_king] at h
  omega

theorem isConnected_mycielskian_king (m n : ℕ) :
    IsConnected (mycielskian (path (m + 2) ⊠g path (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_king]; omega)

theorem numComponents_mycielskian_king (m n : ℕ) :
    (mycielskian (path (m + 2) ⊠g path (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_king]; omega)

theorem radius_mycielskian_king (m n : ℕ) :
    (mycielskian (path (m + 2) ⊠g path (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_king]; omega)

theorem girth_mycielskian_king (m n : ℕ) :
    (mycielskian (path (m + 2) ⊠g path (n + 2))).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_mycielskian_king]
  omega

theorem coverNum_mycielskian_king_le (m n : ℕ) :
    (mycielskian (path m ⊠g path n)).coverNum ≤ m * n + 1 := by
  have h := coverNum_mycielskian_le (path m ⊠g path n)
  rw [V_king] at h
  omega

/-! ### The Mycielskian of a tadpole graph -/

theorem E_mycielskian_tadpole (m k : ℕ) :
    (mycielskian (tadpole (m + 3) k)).E = 4 * (m + k) + 12 := by
  have h := E_mycielskian (tadpole (m + 3) k)
  rw [E_tadpole, V_tadpole] at h
  omega

theorem cliqueNum_mycielskian_tadpole (m k : ℕ) :
    (mycielskian (tadpole (m + 4) k)).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (tadpole (m + 4) k) (by rw [V_tadpole]; omega)
  rw [cliqueNum_tadpole] at h
  omega

theorem maxDeg_mycielskian_tadpole (m k : ℕ) :
    maxDeg (mycielskian (tadpole (m + 3) (k + 1))) = max 6 (m + k + 4) := by
  have h := maxDeg_mycielskian (tadpole (m + 3) (k + 1))
  rw [maxDeg_tadpole, V_tadpole] at h
  omega

theorem minDeg_mycielskian_tadpole (m k : ℕ) :
    minDeg (mycielskian (tadpole (m + 3) (k + 1))) = 2 := by
  have h := minDeg_mycielskian (tadpole (m + 3) (k + 1)) (by rw [V_tadpole]; omega)
  rw [minDeg_tadpole, V_tadpole] at h
  omega

theorem isConnected_mycielskian_tadpole (m k : ℕ) :
    IsConnected (mycielskian (tadpole (m + 3) (k + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_tadpole]; omega)

theorem numComponents_mycielskian_tadpole (m k : ℕ) :
    (mycielskian (tadpole (m + 3) (k + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_tadpole]; omega)

theorem radius_mycielskian_tadpole (m k : ℕ) :
    (mycielskian (tadpole (m + 3) (k + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_tadpole]; omega)

theorem two_le_diameter_mycielskian_tadpole (m k : ℕ) :
    2 ≤ (mycielskian (tadpole (m + 3) (k + 1))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_tadpole]; omega)

theorem diameter_mycielskian_tadpole_le_four (m k : ℕ) :
    (mycielskian (tadpole (m + 3) (k + 1))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_tadpole]; omega)

theorem four_le_girth_mycielskian_tadpole (m k : ℕ) :
    4 ≤ (mycielskian (tadpole (m + 4) k)).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_tadpole]) (by rw [E_tadpole]; omega)

theorem coverNum_mycielskian_tadpole_le (m k : ℕ) :
    (mycielskian (tadpole m k)).coverNum ≤ m + k + 1 := by
  have h := coverNum_mycielskian_le (tadpole m k)
  rw [V_tadpole] at h
  omega

theorem V_le_indepNum_mycielskian_tadpole (m k : ℕ) :
    m + k ≤ (mycielskian (tadpole m k)).indepNum := by
  have h := V_le_indepNum_mycielskian (tadpole m k)
  rw [V_tadpole] at h
  omega

/-! ### The Mycielskian of a lollipop graph -/

@[simp] theorem E_mycielskian_lollipop (m k : ℕ) :
    (mycielskian (lollipop (m + 1) k)).E
      = 3 * ((m + 1).choose 2 + k) + (m + 1 + k) := by
  rw [E_mycielskian, E_lollipop, V_lollipop]

theorem chromNum_mycielskian_lollipop (m k : ℕ) :
    (mycielskian (lollipop (m + 2) k)).chromNum = m + 3 := by
  have h := chromNum_mycielskian (lollipop (m + 2) k)
  rw [chromNum_lollipop] at h
  omega

theorem cliqueNum_mycielskian_lollipop (m k : ℕ) :
    (mycielskian (lollipop (m + 2) k)).cliqueNum = m + 2 := by
  have h := cliqueNum_mycielskian (lollipop (m + 2) k) (by rw [V_lollipop]; omega)
  rw [cliqueNum_lollipop] at h
  omega

theorem maxDeg_mycielskian_lollipop (m k : ℕ) :
    maxDeg (mycielskian (lollipop (m + 2) (k + 1))) = max (2 * m + 4) (m + k + 3) := by
  have h := maxDeg_mycielskian (lollipop (m + 2) (k + 1))
  rw [maxDeg_lollipop, V_lollipop] at h
  omega

theorem minDeg_mycielskian_lollipop (m k : ℕ) :
    minDeg (mycielskian (lollipop (m + 2) (k + 1))) = 2 := by
  have h := minDeg_mycielskian (lollipop (m + 2) (k + 1)) (by rw [V_lollipop]; omega)
  rw [minDeg_lollipop, V_lollipop] at h
  omega

theorem isConnected_mycielskian_lollipop (m k : ℕ) :
    IsConnected (mycielskian (lollipop (m + 2) (k + 1))) :=
  isConnected_mycielskian _ (by rw [minDeg_lollipop]; omega)

theorem numComponents_mycielskian_lollipop (m k : ℕ) :
    (mycielskian (lollipop (m + 2) (k + 1))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_lollipop]; omega)

theorem radius_mycielskian_lollipop (m k : ℕ) :
    (mycielskian (lollipop (m + 2) (k + 1))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_lollipop]; omega)

theorem two_le_diameter_mycielskian_lollipop (m k : ℕ) :
    2 ≤ (mycielskian (lollipop (m + 2) (k + 1))).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_lollipop]; omega)

theorem diameter_mycielskian_lollipop_le_four (m k : ℕ) :
    (mycielskian (lollipop (m + 2) (k + 1))).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_lollipop]; omega)

theorem girth_mycielskian_lollipop (m k : ℕ) :
    (mycielskian (lollipop (m + 3) k)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_mycielskian_lollipop]
  omega

theorem coverNum_mycielskian_lollipop_le (m k : ℕ) :
    (mycielskian (lollipop m k)).coverNum ≤ m + k + 1 := by
  have h := coverNum_mycielskian_le (lollipop m k)
  rw [V_lollipop] at h
  omega

theorem V_le_indepNum_mycielskian_lollipop (m k : ℕ) :
    m + k ≤ (mycielskian (lollipop m k)).indepNum := by
  have h := V_le_indepNum_mycielskian (lollipop m k)
  rw [V_lollipop] at h
  omega

/-! ### The line graph of a wheel -/

theorem chromNum_lineGraph_wheel (n : ℕ) :
    (lineGraph (wheel (n + 4))).chromNum = n + 4 := by
  rw [chromNum_lineGraph, edgeChromNum_wheel]

theorem indepNum_lineGraph_wheel (n : ℕ) :
    (lineGraph (wheel (n + 3))).indepNum = (n + 4) / 2 := by
  rw [indepNum_lineGraph, matchNum_wheel]

theorem coverNum_lineGraph_wheel (n : ℕ) :
    (lineGraph (wheel (n + 3))).coverNum = 2 * (n + 3) - (n + 4) / 2 := by
  rw [coverNum_lineGraph, E_wheel, matchNum_wheel]

theorem cliqueNum_lineGraph_wheel (n : ℕ) :
    (lineGraph (wheel (n + 3))).cliqueNum = n + 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := wheel (n + 3))
    (by rw [maxDeg_wheel]; omega)
  rw [maxDeg_wheel] at h
  omega

theorem girth_lineGraph_wheel (n : ℕ) : (lineGraph (wheel (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_wheel]; omega)

theorem not_isBipartite_lineGraph_wheel (n : ℕ) :
    ¬ IsBipartite (lineGraph (wheel (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_wheel]; omega)

theorem not_isAcyclic_lineGraph_wheel (n : ℕ) :
    ¬ IsAcyclic (lineGraph (wheel (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_wheel]; omega)

theorem not_isTree_lineGraph_wheel (n : ℕ) : ¬ IsTree (lineGraph (wheel (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_wheel]; omega)

theorem isConnected_lineGraph_wheel (n : ℕ) : IsConnected (lineGraph (wheel (n + 3))) :=
  isConnected_lineGraph (isConnected_wheel _) (by rw [E_wheel]; omega)

theorem numComponents_lineGraph_wheel (n : ℕ) :
    (lineGraph (wheel (n + 3))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_wheel _) (by rw [E_wheel]; omega)

theorem radius_lineGraph_wheel_le (n : ℕ) : (lineGraph (wheel (n + 3))).radius ≤ 2 := by
  have h := radius_lineGraph_le (G := wheel (n + 3)) (isConnected_wheel _)
    (by rw [E_wheel]; omega)
  rw [radius_wheel] at h
  omega

theorem diameter_lineGraph_wheel_le (n : ℕ) : (lineGraph (wheel (n + 4))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := wheel (n + 4)) (isConnected_wheel _)
    (by rw [E_wheel]; omega)
  rw [diameter_wheel] at h
  omega

theorem maxDeg_lineGraph_wheel_le (n : ℕ) : maxDeg (lineGraph (wheel (n + 3))) ≤ 2 * n + 4 := by
  have h := maxDeg_lineGraph_le (wheel (n + 3))
  rw [maxDeg_wheel] at h
  omega

theorem le_minDeg_lineGraph_wheel (n : ℕ) : 4 ≤ minDeg (lineGraph (wheel (n + 3))) := by
  have h := le_minDeg_lineGraph (G := wheel (n + 3)) (by rw [E_wheel]; omega)
  rw [minDeg_wheel] at h
  omega

/-! ### The line graph of a fan -/

@[simp] theorem V_lineGraph_fan (n : ℕ) : (lineGraph (fan (n + 1))).V = 2 * n + 1 := by
  rw [V_lineGraph, E_fan]

theorem le_chromNum_lineGraph_fan (n : ℕ) :
    n + 3 ≤ (lineGraph (fan (n + 3))).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_fan n

theorem indepNum_lineGraph_fan (n : ℕ) :
    (lineGraph (fan (n + 1))).indepNum = (n + 2) / 2 := by
  rw [indepNum_lineGraph, matchNum_fan]

theorem coverNum_lineGraph_fan (n : ℕ) :
    (lineGraph (fan (n + 1))).coverNum = 2 * n + 1 - (n + 2) / 2 := by
  rw [coverNum_lineGraph, E_fan, matchNum_fan]

theorem cliqueNum_lineGraph_fan (n : ℕ) :
    (lineGraph (fan (n + 3))).cliqueNum = n + 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := fan (n + 3))
    (by rw [maxDeg_fan]; omega)
  rw [maxDeg_fan] at h
  omega

theorem girth_lineGraph_fan (n : ℕ) : (lineGraph (fan (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_fan]; omega)

theorem not_isBipartite_lineGraph_fan (n : ℕ) :
    ¬ IsBipartite (lineGraph (fan (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_fan]; omega)

theorem not_isAcyclic_lineGraph_fan (n : ℕ) :
    ¬ IsAcyclic (lineGraph (fan (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_fan]; omega)

theorem not_isTree_lineGraph_fan (n : ℕ) : ¬ IsTree (lineGraph (fan (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_fan]; omega)

theorem isConnected_lineGraph_fan (n : ℕ) : IsConnected (lineGraph (fan (n + 1))) :=
  isConnected_lineGraph (isConnected_fan _) (by rw [E_fan]; omega)

theorem numComponents_lineGraph_fan (n : ℕ) :
    (lineGraph (fan (n + 1))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_fan _) (by rw [E_fan]; omega)

theorem radius_lineGraph_fan_le (n : ℕ) : (lineGraph (fan (n + 1))).radius ≤ 2 := by
  have h := radius_lineGraph_le (G := fan (n + 1)) (isConnected_fan _) (by rw [E_fan]; omega)
  rw [radius_fan] at h
  omega

theorem diameter_lineGraph_fan_le (n : ℕ) : (lineGraph (fan (n + 4))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := fan (n + 4)) (isConnected_fan _) (by rw [E_fan]; omega)
  rw [diameter_fan] at h
  omega

theorem maxDeg_lineGraph_fan_le (n : ℕ) : maxDeg (lineGraph (fan (n + 3))) ≤ 2 * n + 4 := by
  have h := maxDeg_lineGraph_le (fan (n + 3))
  rw [maxDeg_fan] at h
  omega

theorem le_minDeg_lineGraph_fan (n : ℕ) : 2 ≤ minDeg (lineGraph (fan (n + 2))) := by
  have h := le_minDeg_lineGraph (G := fan (n + 2)) (by rw [E_fan]; omega)
  rw [minDeg_fan] at h
  omega

/-! ### The line graph of a friendship graph -/

@[simp] theorem V_lineGraph_friendship (n : ℕ) : (lineGraph (friendship n)).V = 3 * n := by
  rw [V_lineGraph, E_friendship]

theorem chromNum_lineGraph_friendship (n : ℕ) :
    (lineGraph (friendship (n + 2))).chromNum = 2 * n + 4 := by
  rw [chromNum_lineGraph, edgeChromNum_friendship]

theorem indepNum_lineGraph_friendship (n : ℕ) :
    (lineGraph (friendship n)).indepNum = n := by
  rw [indepNum_lineGraph, matchNum_friendship]

theorem coverNum_lineGraph_friendship (n : ℕ) :
    (lineGraph (friendship n)).coverNum = 2 * n := by
  rw [coverNum_lineGraph, E_friendship, matchNum_friendship]
  omega

theorem cliqueNum_lineGraph_friendship (n : ℕ) :
    (lineGraph (friendship (n + 2))).cliqueNum = 2 * n + 4 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := friendship (n + 2))
    (by rw [maxDeg_friendship]; omega)
  rw [maxDeg_friendship] at h
  omega

theorem girth_lineGraph_friendship (n : ℕ) : (lineGraph (friendship (n + 2))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_friendship]; omega)

theorem not_isBipartite_lineGraph_friendship (n : ℕ) :
    ¬ IsBipartite (lineGraph (friendship (n + 2))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_friendship]; omega)

theorem not_isAcyclic_lineGraph_friendship (n : ℕ) :
    ¬ IsAcyclic (lineGraph (friendship (n + 2))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_friendship]; omega)

theorem not_isTree_lineGraph_friendship (n : ℕ) :
    ¬ IsTree (lineGraph (friendship (n + 2))) :=
  not_isTree_lineGraph (by rw [maxDeg_friendship]; omega)

theorem isConnected_lineGraph_friendship (n : ℕ) :
    IsConnected (lineGraph (friendship (n + 1))) :=
  isConnected_lineGraph (isConnected_friendship n) (by rw [E_friendship]; omega)

theorem numComponents_lineGraph_friendship (n : ℕ) :
    (lineGraph (friendship (n + 1))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_friendship n) (by rw [E_friendship]; omega)

theorem radius_lineGraph_friendship_le (n : ℕ) :
    (lineGraph (friendship (n + 1))).radius ≤ 2 := by
  have h := radius_lineGraph_le (G := friendship (n + 1)) (isConnected_friendship n)
    (by rw [E_friendship]; omega)
  rw [radius_friendship] at h
  omega

theorem diameter_lineGraph_friendship_le (n : ℕ) :
    (lineGraph (friendship (n + 2))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := friendship (n + 2)) (isConnected_friendship _)
    (by rw [E_friendship]; omega)
  rw [diameter_friendship] at h
  omega

theorem maxDeg_lineGraph_friendship_le (n : ℕ) :
    maxDeg (lineGraph (friendship (n + 1))) ≤ 4 * n + 2 := by
  have h := maxDeg_lineGraph_le (friendship (n + 1))
  rw [maxDeg_friendship] at h
  omega

theorem le_minDeg_lineGraph_friendship (n : ℕ) :
    2 ≤ minDeg (lineGraph (friendship (n + 1))) := by
  have h := le_minDeg_lineGraph (G := friendship (n + 1)) (by rw [E_friendship]; omega)
  rw [minDeg_friendship] at h
  omega

/-! ### The line graph of a book -/

theorem indepNum_lineGraph_book (n : ℕ) : (lineGraph (book (n + 2))).indepNum = 2 := by
  rw [indepNum_lineGraph, matchNum_book]

theorem coverNum_lineGraph_book (n : ℕ) :
    (lineGraph (book (n + 2))).coverNum = 2 * n + 3 := by
  have h := coverNum_lineGraph (book (n + 2))
  rw [E_book, matchNum_book] at h
  omega

theorem cliqueNum_lineGraph_book (n : ℕ) :
    (lineGraph (book (n + 2))).cliqueNum = n + 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := book (n + 2))
    (by rw [maxDeg_book]; omega)
  rw [maxDeg_book] at h
  omega

theorem girth_lineGraph_book (n : ℕ) : (lineGraph (book (n + 2))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_book]; omega)

theorem not_isBipartite_lineGraph_book (n : ℕ) :
    ¬ IsBipartite (lineGraph (book (n + 2))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_book]; omega)

theorem not_isAcyclic_lineGraph_book (n : ℕ) : ¬ IsAcyclic (lineGraph (book (n + 2))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_book]; omega)

theorem not_isTree_lineGraph_book (n : ℕ) : ¬ IsTree (lineGraph (book (n + 2))) :=
  not_isTree_lineGraph (by rw [maxDeg_book]; omega)

theorem isConnected_lineGraph_book (n : ℕ) : IsConnected (lineGraph (book n)) :=
  isConnected_lineGraph (isConnected_book n) (by rw [E_book]; omega)

theorem numComponents_lineGraph_book (n : ℕ) : (lineGraph (book n)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_book n) (by rw [E_book]; omega)

theorem radius_lineGraph_book_le (n : ℕ) : (lineGraph (book n)).radius ≤ 2 := by
  have h := radius_lineGraph_le (G := book n) (isConnected_book n) (by rw [E_book]; omega)
  rw [radius_book] at h
  omega

theorem diameter_lineGraph_book_le (n : ℕ) : (lineGraph (book (n + 2))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := book (n + 2)) (isConnected_book _)
    (by rw [E_book]; omega)
  rw [diameter_book] at h
  omega

theorem maxDeg_lineGraph_book_le (n : ℕ) : maxDeg (lineGraph (book (n + 1))) ≤ 2 * n + 2 := by
  have h := maxDeg_lineGraph_le (book (n + 1))
  rw [maxDeg_book] at h
  omega

theorem le_minDeg_lineGraph_book (n : ℕ) : 2 ≤ minDeg (lineGraph (book (n + 1))) := by
  have h := le_minDeg_lineGraph (G := book (n + 1)) (by rw [E_book]; omega)
  rw [minDeg_book] at h
  omega

/-! ### The line graph of a crown graph -/

theorem indepNum_lineGraph_crown (n : ℕ) :
    (lineGraph (crown (n + 2))).indepNum = n + 2 := by
  rw [indepNum_lineGraph, matchNum_crown]

theorem coverNum_lineGraph_crown (n : ℕ) :
    (lineGraph (crown (n + 2))).coverNum = 2 * (n + 2).choose 2 - (n + 2) := by
  rw [coverNum_lineGraph, E_crown, matchNum_crown]

theorem cliqueNum_lineGraph_crown (n : ℕ) :
    (lineGraph (crown (n + 4))).cliqueNum = n + 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := crown (n + 4))
    (by rw [maxDeg_crown]; omega)
  rw [maxDeg_crown] at h
  omega

theorem girth_lineGraph_crown (n : ℕ) : (lineGraph (crown (n + 4))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_crown]; omega)

theorem not_isBipartite_lineGraph_crown (n : ℕ) :
    ¬ IsBipartite (lineGraph (crown (n + 4))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_crown]; omega)

theorem not_isAcyclic_lineGraph_crown (n : ℕ) : ¬ IsAcyclic (lineGraph (crown (n + 4))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_crown]; omega)

theorem not_isTree_lineGraph_crown (n : ℕ) : ¬ IsTree (lineGraph (crown (n + 4))) :=
  not_isTree_lineGraph (by rw [maxDeg_crown]; omega)

theorem E_pos_crown (n : ℕ) : 0 < (crown (n + 3)).E := by
  have h := Nat.choose_pos (n := n + 3) (k := 2) (by omega)
  rw [E_crown]
  omega

theorem isConnected_lineGraph_crown (n : ℕ) : IsConnected (lineGraph (crown (n + 3))) :=
  isConnected_lineGraph (isConnected_crown n) (E_pos_crown n)

theorem numComponents_lineGraph_crown (n : ℕ) :
    (lineGraph (crown (n + 3))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_crown n) (E_pos_crown n)

theorem radius_lineGraph_crown_le (n : ℕ) : (lineGraph (crown (n + 3))).radius ≤ 4 := by
  have h := radius_lineGraph_le (G := crown (n + 3)) (isConnected_crown n) (E_pos_crown n)
  rw [radius_crown] at h
  omega

theorem diameter_lineGraph_crown_le (n : ℕ) : (lineGraph (crown (n + 3))).diameter ≤ 4 := by
  have h := diameter_lineGraph_le (G := crown (n + 3)) (isConnected_crown n) (E_pos_crown n)
  rw [diameter_crown] at h
  omega

theorem maxDeg_lineGraph_crown (n : ℕ) :
    maxDeg (lineGraph (crown (n + 3))) = 2 * n + 2 := by
  have h1 := maxDeg_lineGraph_le (crown (n + 3))
  have h2 := le_minDeg_lineGraph (G := crown (n + 3)) (E_pos_crown n)
  have h3 := minDeg_le_maxDeg (lineGraph (crown (n + 3)))
  rw [maxDeg_crown] at h1
  rw [minDeg_crown] at h2
  omega

theorem minDeg_lineGraph_crown (n : ℕ) :
    minDeg (lineGraph (crown (n + 3))) = 2 * n + 2 := by
  have h1 := maxDeg_lineGraph_le (crown (n + 3))
  have h2 := le_minDeg_lineGraph (G := crown (n + 3)) (E_pos_crown n)
  have h3 := minDeg_le_maxDeg (lineGraph (crown (n + 3)))
  rw [maxDeg_crown] at h1
  rw [minDeg_crown] at h2
  omega

/-! ### The line graph of a ladder -/

@[simp] theorem V_lineGraph_ladder (n : ℕ) :
    (lineGraph (ladder (n + 1))).V = 3 * n + 1 := by
  rw [V_lineGraph, E_ladder]

theorem indepNum_lineGraph_ladder (n : ℕ) : (lineGraph (ladder n)).indepNum = n := by
  rw [indepNum_lineGraph, matchNum_ladder]

theorem coverNum_lineGraph_ladder (n : ℕ) :
    (lineGraph (ladder (n + 1))).coverNum = 2 * n := by
  have h := coverNum_lineGraph (ladder (n + 1))
  rw [E_ladder, matchNum_ladder] at h
  omega

theorem cliqueNum_lineGraph_ladder (n : ℕ) :
    (lineGraph (ladder (n + 3))).cliqueNum = 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := ladder (n + 3))
    (by rw [maxDeg_ladder])
  rw [maxDeg_ladder] at h
  omega

theorem girth_lineGraph_ladder (n : ℕ) : (lineGraph (ladder (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_ladder])

theorem not_isBipartite_lineGraph_ladder (n : ℕ) :
    ¬ IsBipartite (lineGraph (ladder (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_ladder])

theorem not_isAcyclic_lineGraph_ladder (n : ℕ) :
    ¬ IsAcyclic (lineGraph (ladder (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_ladder])

theorem not_isTree_lineGraph_ladder (n : ℕ) : ¬ IsTree (lineGraph (ladder (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_ladder])

theorem isConnected_lineGraph_ladder (n : ℕ) : IsConnected (lineGraph (ladder (n + 1))) :=
  isConnected_lineGraph (isConnected_ladder n) (by rw [E_ladder]; omega)

theorem numComponents_lineGraph_ladder (n : ℕ) :
    (lineGraph (ladder (n + 1))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_ladder n) (by rw [E_ladder]; omega)

theorem radius_lineGraph_ladder_le (n : ℕ) :
    (lineGraph (ladder (n + 1))).radius ≤ (n + 1) / 2 + 2 := by
  have h := radius_lineGraph_le (G := ladder (n + 1)) (isConnected_ladder n)
    (by rw [E_ladder]; omega)
  rw [radius_ladder] at h
  omega

theorem diameter_lineGraph_ladder_le (n : ℕ) :
    (lineGraph (ladder (n + 1))).diameter ≤ n + 2 := by
  have h := diameter_lineGraph_le (G := ladder (n + 1)) (isConnected_ladder n)
    (by rw [E_ladder]; omega)
  rw [diameter_ladder] at h
  omega

theorem maxDeg_lineGraph_ladder_le (n : ℕ) : maxDeg (lineGraph (ladder (n + 3))) ≤ 4 := by
  have h := maxDeg_lineGraph_le (ladder (n + 3))
  rw [maxDeg_ladder] at h
  omega

theorem le_minDeg_lineGraph_ladder (n : ℕ) : 2 ≤ minDeg (lineGraph (ladder (n + 2))) := by
  have h := le_minDeg_lineGraph (G := ladder (n + 2)) (by rw [E_ladder]; omega)
  rw [minDeg_ladder] at h
  omega

/-! ### The line graph of a double star -/

@[simp] theorem V_lineGraph_doubleStar (m n : ℕ) :
    (lineGraph (doubleStar m n)).V = m + n + 1 := by
  rw [V_lineGraph, E_doubleStar]

theorem indepNum_lineGraph_doubleStar (m n : ℕ) :
    (lineGraph (doubleStar (m + 1) (n + 1))).indepNum = 2 := by
  rw [indepNum_lineGraph, matchNum_doubleStar]

theorem coverNum_lineGraph_doubleStar (m n : ℕ) :
    (lineGraph (doubleStar (m + 1) (n + 1))).coverNum = m + n + 1 := by
  have h := coverNum_lineGraph (doubleStar (m + 1) (n + 1))
  rw [E_doubleStar, matchNum_doubleStar] at h
  omega

theorem cliqueNum_lineGraph_doubleStar (m n : ℕ) :
    (lineGraph (doubleStar (m + 2) n)).cliqueNum = max (m + 2) n + 1 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := doubleStar (m + 2) n)
    (by rw [maxDeg_doubleStar]; omega)
  rw [maxDeg_doubleStar] at h
  omega

theorem girth_lineGraph_doubleStar (m n : ℕ) :
    (lineGraph (doubleStar (m + 2) n)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_doubleStar]; omega)

theorem not_isBipartite_lineGraph_doubleStar (m n : ℕ) :
    ¬ IsBipartite (lineGraph (doubleStar (m + 2) n)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_doubleStar]; omega)

theorem not_isAcyclic_lineGraph_doubleStar (m n : ℕ) :
    ¬ IsAcyclic (lineGraph (doubleStar (m + 2) n)) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_doubleStar]; omega)

theorem not_isTree_lineGraph_doubleStar (m n : ℕ) :
    ¬ IsTree (lineGraph (doubleStar (m + 2) n)) :=
  not_isTree_lineGraph (by rw [maxDeg_doubleStar]; omega)

theorem isConnected_lineGraph_doubleStar (m n : ℕ) :
    IsConnected (lineGraph (doubleStar m n)) :=
  isConnected_lineGraph (isConnected_doubleStar m n) (by rw [E_doubleStar]; omega)

theorem numComponents_lineGraph_doubleStar (m n : ℕ) :
    (lineGraph (doubleStar m n)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_doubleStar m n) (by rw [E_doubleStar]; omega)

theorem radius_lineGraph_doubleStar_le (m n : ℕ) :
    (lineGraph (doubleStar (m + 1) (n + 1))).radius ≤ 3 := by
  have h := radius_lineGraph_le (G := doubleStar (m + 1) (n + 1))
    (isConnected_doubleStar _ _) (by rw [E_doubleStar]; omega)
  rw [radius_doubleStar] at h
  omega

theorem diameter_lineGraph_doubleStar_le (m n : ℕ) :
    (lineGraph (doubleStar (m + 1) (n + 1))).diameter ≤ 4 := by
  have h := diameter_lineGraph_le (G := doubleStar (m + 1) (n + 1))
    (isConnected_doubleStar _ _) (by rw [E_doubleStar]; omega)
  rw [diameter_doubleStar] at h
  omega

theorem maxDeg_lineGraph_doubleStar_le (m n : ℕ) :
    maxDeg (lineGraph (doubleStar m n)) ≤ 2 * max m n := by
  have h := maxDeg_lineGraph_le (doubleStar m n)
  rw [maxDeg_doubleStar] at h
  omega

/-! ### The line graph of a rook's graph -/

theorem E_pos_rook (m n : ℕ) : 0 < (rook (m + 2) (n + 2)).E := by
  have h : 0 < (m + 2) * ((n + 2).choose 2) :=
    Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  rw [E_rook]
  omega

theorem indepNum_lineGraph_rook (m n : ℕ) :
    (lineGraph (rook (m + 1) (n + 1))).indepNum = (m + 1) * (n + 1) / 2 := by
  rw [indepNum_lineGraph, matchNum_rook]

theorem coverNum_lineGraph_rook (m n : ℕ) :
    (lineGraph (rook (m + 1) (n + 1))).coverNum
      = (m + 1) * (n + 1).choose 2 + (n + 1) * (m + 1).choose 2 - (m + 1) * (n + 1) / 2 := by
  rw [coverNum_lineGraph, E_rook, matchNum_rook]

theorem cliqueNum_lineGraph_rook (m n : ℕ) :
    (lineGraph (rook (m + 2) (n + 3))).cliqueNum = m + n + 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := rook (m + 2) (n + 3))
    (by rw [maxDeg_rook]; omega)
  rw [maxDeg_rook] at h
  omega

theorem girth_lineGraph_rook (m n : ℕ) : (lineGraph (rook (m + 2) (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_rook]; omega)

theorem not_isBipartite_lineGraph_rook (m n : ℕ) :
    ¬ IsBipartite (lineGraph (rook (m + 2) (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_rook]; omega)

theorem not_isAcyclic_lineGraph_rook (m n : ℕ) :
    ¬ IsAcyclic (lineGraph (rook (m + 2) (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_rook]; omega)

theorem not_isTree_lineGraph_rook (m n : ℕ) :
    ¬ IsTree (lineGraph (rook (m + 2) (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_rook]; omega)

theorem isConnected_lineGraph_rook (m n : ℕ) :
    IsConnected (lineGraph (rook (m + 2) (n + 2))) :=
  isConnected_lineGraph (isConnected_rook _ _) (E_pos_rook m n)

theorem numComponents_lineGraph_rook (m n : ℕ) :
    (lineGraph (rook (m + 2) (n + 2))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_rook _ _) (E_pos_rook m n)

theorem radius_lineGraph_rook_le (m n : ℕ) :
    (lineGraph (rook (m + 2) (n + 2))).radius ≤ 3 := by
  have h := radius_lineGraph_le (G := rook (m + 2) (n + 2)) (isConnected_rook _ _)
    (E_pos_rook m n)
  rw [radius_rook] at h
  omega

theorem diameter_lineGraph_rook_le (m n : ℕ) :
    (lineGraph (rook (m + 2) (n + 2))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := rook (m + 2) (n + 2)) (isConnected_rook _ _)
    (E_pos_rook m n)
  rw [diameter_rook] at h
  omega

theorem maxDeg_lineGraph_rook (m n : ℕ) :
    maxDeg (lineGraph (rook (m + 2) (n + 2))) = 2 * m + 2 * n + 2 := by
  have h1 := maxDeg_lineGraph_le (rook (m + 2) (n + 2))
  have h2 := le_minDeg_lineGraph (G := rook (m + 2) (n + 2)) (E_pos_rook m n)
  have h3 := minDeg_le_maxDeg (lineGraph (rook (m + 2) (n + 2)))
  rw [maxDeg_rook] at h1
  rw [minDeg_rook] at h2
  omega

theorem minDeg_lineGraph_rook (m n : ℕ) :
    minDeg (lineGraph (rook (m + 2) (n + 2))) = 2 * m + 2 * n + 2 := by
  have h1 := maxDeg_lineGraph_le (rook (m + 2) (n + 2))
  have h2 := le_minDeg_lineGraph (G := rook (m + 2) (n + 2)) (E_pos_rook m n)
  have h3 := minDeg_le_maxDeg (lineGraph (rook (m + 2) (n + 2)))
  rw [maxDeg_rook] at h1
  rw [minDeg_rook] at h2
  omega

/-! ### The line graph of a hypercube -/

theorem E_hypercube_succ (n : ℕ) : (hypercube (n + 1)).E = (n + 1) * 2 ^ n := by
  have h := E_hypercube (n + 1)
  have h3 : (n + 1) * 2 ^ (n + 1) = 2 * ((n + 1) * 2 ^ n) := by ring
  omega

theorem two_mul_V_lineGraph_hypercube (n : ℕ) :
    2 * (lineGraph (hypercube n)).V = n * 2 ^ n := by
  rw [V_lineGraph, E_hypercube]

theorem V_lineGraph_hypercube_succ (n : ℕ) :
    (lineGraph (hypercube (n + 1))).V = (n + 1) * 2 ^ n := by
  rw [V_lineGraph, E_hypercube_succ]

theorem chromNum_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 1))).chromNum = n + 1 := by
  rw [chromNum_lineGraph, edgeChromNum_hypercube]

theorem indepNum_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 1))).indepNum = 2 ^ n := by
  rw [indepNum_lineGraph, matchNum_hypercube]

theorem coverNum_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 1))).coverNum = n * 2 ^ n := by
  have h := coverNum_lineGraph (hypercube (n + 1))
  rw [matchNum_hypercube, E_hypercube_succ] at h
  have h3 : (n + 1) * 2 ^ n = n * 2 ^ n + 2 ^ n := by ring
  omega

theorem isConnected_lineGraph_hypercube (n : ℕ) :
    IsConnected (lineGraph (hypercube (n + 1))) :=
  isConnected_lineGraph (isConnected_hypercube _) (by rw [E_hypercube_succ]; positivity)

theorem numComponents_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 1))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_hypercube _) (by rw [E_hypercube_succ]; positivity)

theorem radius_lineGraph_hypercube_le (n : ℕ) :
    (lineGraph (hypercube (n + 1))).radius ≤ n + 2 := by
  have h := radius_lineGraph_le (G := hypercube (n + 1)) (isConnected_hypercube _)
    (by rw [E_hypercube_succ]; positivity)
  rw [radius_hypercube] at h
  omega

theorem diameter_lineGraph_hypercube_le (n : ℕ) :
    (lineGraph (hypercube (n + 1))).diameter ≤ n + 2 := by
  have h := diameter_lineGraph_le (G := hypercube (n + 1)) (isConnected_hypercube _)
    (by rw [E_hypercube_succ]; positivity)
  rw [diameter_hypercube] at h
  omega

theorem maxDeg_lineGraph_hypercube (n : ℕ) :
    maxDeg (lineGraph (hypercube (n + 1))) = 2 * n := by
  have h := maxDeg_lineGraph (G := hypercube (n + 1))
    (by rw [E_hypercube_succ]; positivity) (degSequence_hypercube (n + 1))
  omega

theorem minDeg_lineGraph_hypercube (n : ℕ) :
    minDeg (lineGraph (hypercube (n + 1))) = 2 * n := by
  have h := minDeg_lineGraph (G := hypercube (n + 1))
    (by rw [E_hypercube_succ]; positivity) (degSequence_hypercube (n + 1))
  omega

/-! ### The line graph of the Petersen graph -/

@[simp] theorem V_lineGraph_petersen : (lineGraph petersen).V = 15 := by
  rw [V_lineGraph, E_petersen]

theorem le_chromNum_lineGraph_petersen : 3 ≤ (lineGraph petersen).chromNum := by
  rw [chromNum_lineGraph]
  exact three_le_edgeChromNum_petersen

theorem indepNum_lineGraph_petersen : (lineGraph petersen).indepNum = 5 := by
  rw [indepNum_lineGraph, matchNum_petersen]

theorem coverNum_lineGraph_petersen : (lineGraph petersen).coverNum = 10 := by
  have h := coverNum_lineGraph petersen
  rw [E_petersen, matchNum_petersen] at h
  omega

theorem not_isBipartite_lineGraph_petersen : ¬ IsBipartite (lineGraph petersen) :=
  not_isBipartite_lineGraph (by rw [maxDeg_petersen])

theorem not_isAcyclic_lineGraph_petersen : ¬ IsAcyclic (lineGraph petersen) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_petersen])

theorem not_isTree_lineGraph_petersen : ¬ IsTree (lineGraph petersen) :=
  not_isTree_lineGraph (by rw [maxDeg_petersen])

theorem isConnected_lineGraph_petersen : IsConnected (lineGraph petersen) :=
  isConnected_lineGraph isConnected_petersen (by rw [E_petersen]; omega)

theorem numComponents_lineGraph_petersen : (lineGraph petersen).numComponents = 1 :=
  numComponents_lineGraph isConnected_petersen (by rw [E_petersen]; omega)

theorem radius_lineGraph_petersen_le : (lineGraph petersen).radius ≤ 3 := by
  have h := radius_lineGraph_le (G := petersen) isConnected_petersen
    (by rw [E_petersen]; omega)
  rw [radius_petersen] at h
  omega

theorem diameter_lineGraph_petersen_le : (lineGraph petersen).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := petersen) isConnected_petersen
    (by rw [E_petersen]; omega)
  rw [diameter_petersen] at h
  omega

theorem maxDeg_lineGraph_petersen : maxDeg (lineGraph petersen) = 4 := by
  have h1 := maxDeg_lineGraph_le petersen
  have h2 := le_minDeg_lineGraph (G := petersen) (by rw [E_petersen]; omega)
  have h3 := minDeg_le_maxDeg (lineGraph petersen)
  rw [maxDeg_petersen] at h1
  rw [minDeg_petersen] at h2
  omega

theorem minDeg_lineGraph_petersen : minDeg (lineGraph petersen) = 4 := by
  have h1 := maxDeg_lineGraph_le petersen
  have h2 := le_minDeg_lineGraph (G := petersen) (by rw [E_petersen]; omega)
  have h3 := minDeg_le_maxDeg (lineGraph petersen)
  rw [maxDeg_petersen] at h1
  rw [minDeg_petersen] at h2
  omega

/-! ### The line graph of a prism -/

@[simp] theorem V_lineGraph_prism (n : ℕ) : (lineGraph (prism (n + 3))).V = 3 * (n + 3) := by
  rw [V_lineGraph, E_prism]

theorem le_chromNum_lineGraph_prism (n : ℕ) :
    3 ≤ (lineGraph (prism (n + 3))).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_prism n

theorem indepNum_lineGraph_prism (n : ℕ) : (lineGraph (prism n)).indepNum = n := by
  rw [indepNum_lineGraph, matchNum_prism]

theorem coverNum_lineGraph_prism (n : ℕ) :
    (lineGraph (prism (n + 3))).coverNum = 2 * n + 6 := by
  have h := coverNum_lineGraph (prism (n + 3))
  rw [E_prism, matchNum_prism] at h
  omega

theorem cliqueNum_lineGraph_prism (n : ℕ) :
    (lineGraph (prism (n + 3))).cliqueNum = 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := prism (n + 3))
    (by rw [maxDeg_prism])
  rw [maxDeg_prism] at h
  omega

theorem girth_lineGraph_prism (n : ℕ) : (lineGraph (prism (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_prism])

theorem not_isBipartite_lineGraph_prism (n : ℕ) :
    ¬ IsBipartite (lineGraph (prism (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_prism])

theorem not_isAcyclic_lineGraph_prism (n : ℕ) :
    ¬ IsAcyclic (lineGraph (prism (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_prism])

theorem not_isTree_lineGraph_prism (n : ℕ) : ¬ IsTree (lineGraph (prism (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_prism])

theorem isConnected_lineGraph_prism (n : ℕ) : IsConnected (lineGraph (prism (n + 3))) :=
  isConnected_lineGraph (isConnected_prism _) (by rw [E_prism]; omega)

theorem numComponents_lineGraph_prism (n : ℕ) :
    (lineGraph (prism (n + 3))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_prism _) (by rw [E_prism]; omega)

theorem radius_lineGraph_prism_le (n : ℕ) :
    (lineGraph (prism (n + 3))).radius ≤ (n + 3) / 2 + 2 := by
  have h := radius_lineGraph_le (G := prism (n + 3)) (isConnected_prism _)
    (by rw [E_prism]; omega)
  rw [radius_prism] at h
  omega

theorem diameter_lineGraph_prism_le (n : ℕ) :
    (lineGraph (prism (n + 3))).diameter ≤ (n + 3) / 2 + 2 := by
  have h := diameter_lineGraph_le (G := prism (n + 3)) (isConnected_prism _)
    (by rw [E_prism]; omega)
  rw [diameter_prism] at h
  omega

theorem maxDeg_lineGraph_prism (n : ℕ) : maxDeg (lineGraph (prism (n + 3))) = 4 := by
  have h1 := maxDeg_lineGraph_le (prism (n + 3))
  have h2 := le_minDeg_lineGraph (G := prism (n + 3)) (by rw [E_prism]; omega)
  have h3 := minDeg_le_maxDeg (lineGraph (prism (n + 3)))
  rw [maxDeg_prism] at h1
  rw [minDeg_prism] at h2
  omega

theorem minDeg_lineGraph_prism (n : ℕ) : minDeg (lineGraph (prism (n + 3))) = 4 := by
  have h1 := maxDeg_lineGraph_le (prism (n + 3))
  have h2 := le_minDeg_lineGraph (G := prism (n + 3)) (by rw [E_prism]; omega)
  have h3 := minDeg_le_maxDeg (lineGraph (prism (n + 3)))
  rw [maxDeg_prism] at h1
  rw [minDeg_prism] at h2
  omega

/-! ### The line graph of a cocktail party graph -/

@[simp] theorem V_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty n)).V = n * (2 * n - 2) := by
  rw [V_lineGraph, E_cocktailParty]

theorem E_pos_cocktailParty (n : ℕ) : 0 < (cocktailParty (n + 2)).E := by
  rw [E_cocktailParty, show 2 * (n + 2) - 2 = 2 * n + 2 from by omega]
  positivity

theorem le_chromNum_lineGraph_cocktailParty (n : ℕ) :
    2 * n ≤ (lineGraph (cocktailParty (n + 1))).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_cocktailParty n

theorem indepNum_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty (n + 2))).indepNum = n + 2 := by
  rw [indepNum_lineGraph, matchNum_cocktailParty]

theorem coverNum_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty (n + 2))).coverNum = (n + 2) * (2 * n + 1) := by
  have h := coverNum_lineGraph (cocktailParty (n + 2))
  rw [E_cocktailParty, matchNum_cocktailParty] at h
  have h2 : (n + 2) * (2 * (n + 2) - 2) = (n + 2) * (2 * n + 1) + (n + 2) := by
    rw [show 2 * (n + 2) - 2 = 2 * n + 2 from by omega]
    ring
  omega

theorem cliqueNum_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty (n + 3))).cliqueNum = 2 * n + 4 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := cocktailParty (n + 3))
    (by rw [maxDeg_cocktailParty]; omega)
  rw [maxDeg_cocktailParty] at h
  omega

theorem girth_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_cocktailParty]; omega)

theorem not_isBipartite_lineGraph_cocktailParty (n : ℕ) :
    ¬ IsBipartite (lineGraph (cocktailParty (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_cocktailParty]; omega)

theorem not_isAcyclic_lineGraph_cocktailParty (n : ℕ) :
    ¬ IsAcyclic (lineGraph (cocktailParty (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_cocktailParty]; omega)

theorem not_isTree_lineGraph_cocktailParty (n : ℕ) :
    ¬ IsTree (lineGraph (cocktailParty (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_cocktailParty]; omega)

theorem isConnected_lineGraph_cocktailParty (n : ℕ) :
    IsConnected (lineGraph (cocktailParty (n + 2))) :=
  isConnected_lineGraph (isConnected_cocktailParty n) (E_pos_cocktailParty n)

theorem numComponents_lineGraph_cocktailParty (n : ℕ) :
    (lineGraph (cocktailParty (n + 2))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_cocktailParty n) (E_pos_cocktailParty n)

theorem radius_lineGraph_cocktailParty_le (n : ℕ) :
    (lineGraph (cocktailParty (n + 2))).radius ≤ 3 := by
  have h := radius_lineGraph_le (G := cocktailParty (n + 2)) (isConnected_cocktailParty n)
    (E_pos_cocktailParty n)
  rw [radius_cocktailParty] at h
  omega

theorem diameter_lineGraph_cocktailParty_le (n : ℕ) :
    (lineGraph (cocktailParty (n + 2))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := cocktailParty (n + 2)) (isConnected_cocktailParty n)
    (E_pos_cocktailParty n)
  rw [diameter_cocktailParty] at h
  omega

theorem maxDeg_lineGraph_cocktailParty (n : ℕ) :
    maxDeg (lineGraph (cocktailParty (n + 2))) = 4 * n + 2 := by
  have h1 := maxDeg_lineGraph_le (cocktailParty (n + 2))
  have h2 := le_minDeg_lineGraph (G := cocktailParty (n + 2)) (E_pos_cocktailParty n)
  have h3 := minDeg_le_maxDeg (lineGraph (cocktailParty (n + 2)))
  rw [maxDeg_cocktailParty] at h1
  rw [minDeg_cocktailParty] at h2
  omega

theorem minDeg_lineGraph_cocktailParty (n : ℕ) :
    minDeg (lineGraph (cocktailParty (n + 2))) = 4 * n + 2 := by
  have h1 := maxDeg_lineGraph_le (cocktailParty (n + 2))
  have h2 := le_minDeg_lineGraph (G := cocktailParty (n + 2)) (E_pos_cocktailParty n)
  have h3 := minDeg_le_maxDeg (lineGraph (cocktailParty (n + 2)))
  rw [maxDeg_cocktailParty] at h1
  rw [minDeg_cocktailParty] at h2
  omega

theorem le_chromNum_lineGraph_book (n : ℕ) :
    n + 2 ≤ (lineGraph (book (n + 1))).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_book n

/-! ### The line graph of a triangular graph -/

theorem E_pos_triangular (n : ℕ) : 0 < (triangular (n + 4)).E := by
  have h : 0 < (n + 4) * ((n + 4 - 1).choose 2) :=
    Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  rw [E_triangular]
  omega

theorem cliqueNum_lineGraph_triangular (n : ℕ) :
    (lineGraph (triangular (n + 4))).cliqueNum = 2 * n + 4 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := triangular (n + 4))
    (by rw [maxDeg_triangular]; omega)
  rw [maxDeg_triangular] at h
  omega

theorem girth_lineGraph_triangular (n : ℕ) : (lineGraph (triangular (n + 4))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_triangular]; omega)

theorem not_isBipartite_lineGraph_triangular (n : ℕ) :
    ¬ IsBipartite (lineGraph (triangular (n + 4))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_triangular]; omega)

theorem not_isAcyclic_lineGraph_triangular (n : ℕ) :
    ¬ IsAcyclic (lineGraph (triangular (n + 4))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_triangular]; omega)

theorem not_isTree_lineGraph_triangular (n : ℕ) :
    ¬ IsTree (lineGraph (triangular (n + 4))) :=
  not_isTree_lineGraph (by rw [maxDeg_triangular]; omega)

theorem isConnected_lineGraph_triangular (n : ℕ) :
    IsConnected (lineGraph (triangular (n + 4))) :=
  isConnected_lineGraph (isConnected_triangular (by omega)) (E_pos_triangular n)

theorem numComponents_lineGraph_triangular (n : ℕ) :
    (lineGraph (triangular (n + 4))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_triangular (by omega)) (E_pos_triangular n)

theorem radius_lineGraph_triangular_le (n : ℕ) :
    (lineGraph (triangular (n + 4))).radius ≤ 3 := by
  have h := radius_lineGraph_le (G := triangular (n + 4)) (isConnected_triangular (by omega))
    (E_pos_triangular n)
  rw [radius_triangular (n := n + 4) (by omega)] at h
  omega

theorem diameter_lineGraph_triangular_le (n : ℕ) :
    (lineGraph (triangular (n + 4))).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := triangular (n + 4)) (isConnected_triangular (by omega))
    (E_pos_triangular n)
  rw [diameter_triangular (n := n + 4) (by omega)] at h
  omega

theorem maxDeg_lineGraph_triangular (n : ℕ) :
    maxDeg (lineGraph (triangular (n + 4))) = 4 * n + 6 := by
  have h1 := maxDeg_lineGraph_le (triangular (n + 4))
  have h2 := le_minDeg_lineGraph (G := triangular (n + 4)) (E_pos_triangular n)
  have h3 := minDeg_le_maxDeg (lineGraph (triangular (n + 4)))
  rw [maxDeg_triangular] at h1
  rw [minDeg_triangular] at h2
  omega

theorem minDeg_lineGraph_triangular (n : ℕ) :
    minDeg (lineGraph (triangular (n + 4))) = 4 * n + 6 := by
  have h1 := maxDeg_lineGraph_le (triangular (n + 4))
  have h2 := le_minDeg_lineGraph (G := triangular (n + 4)) (E_pos_triangular n)
  have h3 := minDeg_le_maxDeg (lineGraph (triangular (n + 4)))
  rw [maxDeg_triangular] at h1
  rw [minDeg_triangular] at h2
  omega

/-! ### The line graph of the Grötzsch graph -/

theorem le_chromNum_lineGraph_grotzsch : 5 ≤ (lineGraph grotzsch).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_grotzsch

theorem indepNum_lineGraph_grotzsch : (lineGraph grotzsch).indepNum = 5 := by
  rw [indepNum_lineGraph, matchNum_grotzsch]

theorem coverNum_lineGraph_grotzsch : (lineGraph grotzsch).coverNum = 15 := by
  have h := coverNum_lineGraph grotzsch
  rw [E_grotzsch, matchNum_grotzsch] at h
  omega

theorem cliqueNum_lineGraph_grotzsch : (lineGraph grotzsch).cliqueNum = 5 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := grotzsch)
    (by rw [maxDeg_grotzsch]; omega)
  rw [maxDeg_grotzsch] at h
  omega

theorem girth_lineGraph_grotzsch : (lineGraph grotzsch).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_grotzsch]; omega)

theorem not_isBipartite_lineGraph_grotzsch : ¬ IsBipartite (lineGraph grotzsch) :=
  not_isBipartite_lineGraph (by rw [maxDeg_grotzsch]; omega)

theorem not_isAcyclic_lineGraph_grotzsch : ¬ IsAcyclic (lineGraph grotzsch) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_grotzsch]; omega)

theorem not_isTree_lineGraph_grotzsch : ¬ IsTree (lineGraph grotzsch) :=
  not_isTree_lineGraph (by rw [maxDeg_grotzsch]; omega)

theorem isConnected_lineGraph_grotzsch : IsConnected (lineGraph grotzsch) :=
  isConnected_lineGraph isConnected_grotzsch (by rw [E_grotzsch]; omega)

theorem numComponents_lineGraph_grotzsch : (lineGraph grotzsch).numComponents = 1 :=
  numComponents_lineGraph isConnected_grotzsch (by rw [E_grotzsch]; omega)

theorem radius_lineGraph_grotzsch_le : (lineGraph grotzsch).radius ≤ 3 := by
  have h := radius_lineGraph_le (G := grotzsch) isConnected_grotzsch
    (by rw [E_grotzsch]; omega)
  rw [radius_grotzsch] at h
  omega

theorem diameter_lineGraph_grotzsch_le : (lineGraph grotzsch).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (G := grotzsch) isConnected_grotzsch
    (by rw [E_grotzsch]; omega)
  rw [diameter_grotzsch] at h
  omega

theorem maxDeg_lineGraph_grotzsch_le : maxDeg (lineGraph grotzsch) ≤ 8 := by
  have h := maxDeg_lineGraph_le grotzsch
  rw [maxDeg_grotzsch] at h
  omega

theorem le_minDeg_lineGraph_grotzsch : 4 ≤ minDeg (lineGraph grotzsch) := by
  have h := le_minDeg_lineGraph (G := grotzsch) (by rw [E_grotzsch]; omega)
  rw [minDeg_grotzsch] at h
  omega

/-! ### The line graph of a Turán graph -/

theorem V_lineGraph_turan (n r : ℕ) :
    (lineGraph (turan n r)).V
        + ((n % r) * ((n / r + 1).choose 2) + (r - n % r) * ((n / r).choose 2))
      = n.choose 2 := by
  rw [V_lineGraph]
  exact E_turan n r

theorem indepNum_lineGraph_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    (lineGraph (turan n r)).indepNum = n / 2 := by
  rw [indepNum_lineGraph, matchNum_turan hr h]

theorem coverNum_lineGraph_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    (lineGraph (turan n r)).coverNum = (turan n r).E - n / 2 := by
  rw [coverNum_lineGraph, matchNum_turan hr h]

theorem cliqueNum_lineGraph_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) (h3 : 3 ≤ n - n / r) :
    (lineGraph (turan n r)).cliqueNum = n - n / r := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := turan n r)
    (by rw [maxDeg_turan hr h]; exact h3)
  rw [maxDeg_turan hr h] at hm
  omega

theorem girth_lineGraph_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) (h3 : 3 ≤ n - n / r) :
    (lineGraph (turan n r)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_turan hr h]; exact h3)

theorem not_isBipartite_lineGraph_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n)
    (h3 : 3 ≤ n - n / r) : ¬ IsBipartite (lineGraph (turan n r)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_turan hr h]; exact h3)

theorem not_isAcyclic_lineGraph_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n)
    (h3 : 3 ≤ n - n / r) : ¬ IsAcyclic (lineGraph (turan n r)) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_turan hr h]; exact h3)

theorem not_isTree_lineGraph_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) (h3 : 3 ≤ n - n / r) :
    ¬ IsTree (lineGraph (turan n r)) :=
  not_isTree_lineGraph (by rw [maxDeg_turan hr h]; exact h3)

theorem maxDeg_lineGraph_turan_le {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    maxDeg (lineGraph (turan n r)) ≤ 2 * (n - n / r) - 2 := by
  have hm := maxDeg_lineGraph_le (turan n r)
  rw [maxDeg_turan hr h] at hm
  omega

/-! ### Edge positivity from connectivity -/

theorem E_pos_of_isConnected {G : IsoGraph} (h : IsConnected G) (hV : 2 ≤ G.V) : 0 < G.E :=
  E_pos_of_numComponents_lt_V (by rw [numComponents_eq_one_of_isConnected h]; omega)

/-! ### More of the line graph of a Turán graph -/

theorem E_pos_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) : 0 < (turan n r).E :=
  E_pos_of_isConnected (isConnected_turan hr h) (by rw [V_turan]; omega)

theorem isConnected_lineGraph_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    IsConnected (lineGraph (turan n r)) :=
  isConnected_lineGraph (isConnected_turan hr h) (E_pos_turan hr h)

theorem numComponents_lineGraph_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    (lineGraph (turan n r)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_turan hr h) (E_pos_turan hr h)

theorem radius_lineGraph_turan_le {n r : ℕ} (hr : 2 ≤ r) (h : 2 * r ≤ n) :
    (lineGraph (turan n r)).radius ≤ 3 := by
  have h2 : r ≤ n := by omega
  have hle := radius_lineGraph_le (G := turan n r) (isConnected_turan hr h2) (E_pos_turan hr h2)
  rw [radius_turan hr h] at hle
  omega

theorem diameter_lineGraph_turan_le {n r : ℕ} (hr : 2 ≤ r) (h : 2 * r ≤ n) :
    (lineGraph (turan n r)).diameter ≤ 3 := by
  have h2 : r ≤ n := by omega
  have hle := diameter_lineGraph_le (G := turan n r) (isConnected_turan hr h2) (E_pos_turan hr h2)
  rw [diameter_turan hr h] at hle
  omega

theorem le_minDeg_lineGraph_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    2 * (n - (n + r - 1) / r) - 2 ≤ minDeg (lineGraph (turan n r)) := by
  have hle := le_minDeg_lineGraph (G := turan n r) (E_pos_turan hr h)
  rwa [minDeg_turan (by omega) h] at hle

/-! ### The line graph of a tadpole graph -/

@[simp] theorem V_lineGraph_tadpole (m k : ℕ) :
    (lineGraph (tadpole (m + 3) k)).V = m + 3 + k := by
  rw [V_lineGraph, E_tadpole]

theorem E_pos_tadpole (m k : ℕ) : 0 < (tadpole (m + 3) k).E := by
  rw [E_tadpole]
  omega

theorem isConnected_lineGraph_tadpole (m k : ℕ) :
    IsConnected (lineGraph (tadpole (m + 3) k)) :=
  isConnected_lineGraph (isConnected_tadpole m k) (E_pos_tadpole m k)

theorem numComponents_lineGraph_tadpole (m k : ℕ) :
    (lineGraph (tadpole (m + 3) k)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_tadpole m k) (E_pos_tadpole m k)

theorem cliqueNum_lineGraph_tadpole (m k : ℕ) :
    (lineGraph (tadpole (m + 3) (k + 1))).cliqueNum = 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := tadpole (m + 3) (k + 1))
    (by rw [maxDeg_tadpole])
  rw [maxDeg_tadpole] at h
  omega

theorem girth_lineGraph_tadpole (m k : ℕ) : (lineGraph (tadpole (m + 3) (k + 1))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_tadpole])

theorem not_isBipartite_lineGraph_tadpole (m k : ℕ) :
    ¬ IsBipartite (lineGraph (tadpole (m + 3) (k + 1))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_tadpole])

theorem not_isAcyclic_lineGraph_tadpole (m k : ℕ) :
    ¬ IsAcyclic (lineGraph (tadpole (m + 3) (k + 1))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_tadpole])

theorem not_isTree_lineGraph_tadpole (m k : ℕ) :
    ¬ IsTree (lineGraph (tadpole (m + 3) (k + 1))) :=
  not_isTree_lineGraph (by rw [maxDeg_tadpole])

theorem maxDeg_lineGraph_tadpole_le (m k : ℕ) :
    maxDeg (lineGraph (tadpole (m + 3) (k + 1))) ≤ 4 := by
  have h := maxDeg_lineGraph_le (tadpole (m + 3) (k + 1))
  rw [maxDeg_tadpole] at h
  omega

theorem le_chromNum_lineGraph_tadpole (m k : ℕ) :
    3 ≤ (lineGraph (tadpole (m + 3) (k + 1))).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_tadpole m k

theorem chromNum_lineGraph_tadpole_le (m k : ℕ) :
    (lineGraph (tadpole (m + 3) (k + 1))).chromNum ≤ 5 := by
  rw [chromNum_lineGraph]
  exact edgeChromNum_tadpole_le m k

theorem le_indepNum_lineGraph_tadpole (m k : ℕ) :
    m + k + 4 ≤ 5 * (lineGraph (tadpole (m + 3) (k + 1))).indepNum := by
  rw [indepNum_lineGraph]
  exact le_matchNum_tadpole m k

theorem coverNum_lineGraph_tadpole (m k : ℕ) :
    (lineGraph (tadpole (m + 3) k)).coverNum = m + 3 + k - (tadpole (m + 3) k).matchNum := by
  rw [coverNum_lineGraph, E_tadpole]

theorem coverNum_lineGraph_tadpole_le (m k : ℕ) :
    5 * (lineGraph (tadpole (m + 3) (k + 1))).coverNum ≤ 4 * (m + k + 4) := by
  have h := coverNum_lineGraph (tadpole (m + 3) (k + 1))
  have h2 := le_matchNum_tadpole m k
  rw [E_tadpole] at h
  omega

/-! ### The line graph of a lollipop graph -/

@[simp] theorem V_lineGraph_lollipop (m k : ℕ) :
    (lineGraph (lollipop (m + 1) k)).V = (m + 1).choose 2 + k := by
  rw [V_lineGraph, E_lollipop]

theorem E_pos_lollipop (m k : ℕ) : 0 < (lollipop (m + 2) k).E := by
  have h := Nat.choose_pos (n := m + 1 + 1) (k := 2) (by omega)
  rw [E_lollipop]
  omega

theorem isConnected_lineGraph_lollipop (m k : ℕ) :
    IsConnected (lineGraph (lollipop (m + 2) k)) :=
  isConnected_lineGraph (isConnected_lollipop (m + 1) k) (E_pos_lollipop m k)

theorem numComponents_lineGraph_lollipop (m k : ℕ) :
    (lineGraph (lollipop (m + 2) k)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_lollipop (m + 1) k) (E_pos_lollipop m k)

theorem cliqueNum_lineGraph_lollipop (m k : ℕ) :
    (lineGraph (lollipop (m + 3) (k + 1))).cliqueNum = m + 3 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := lollipop (m + 3) (k + 1))
    (by rw [maxDeg_lollipop]; omega)
  rw [maxDeg_lollipop] at h
  omega

theorem girth_lineGraph_lollipop (m k : ℕ) :
    (lineGraph (lollipop (m + 3) (k + 1))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_lollipop]; omega)

theorem not_isBipartite_lineGraph_lollipop (m k : ℕ) :
    ¬ IsBipartite (lineGraph (lollipop (m + 3) (k + 1))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_lollipop]; omega)

theorem not_isAcyclic_lineGraph_lollipop (m k : ℕ) :
    ¬ IsAcyclic (lineGraph (lollipop (m + 3) (k + 1))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_lollipop]; omega)

theorem not_isTree_lineGraph_lollipop (m k : ℕ) :
    ¬ IsTree (lineGraph (lollipop (m + 3) (k + 1))) :=
  not_isTree_lineGraph (by rw [maxDeg_lollipop]; omega)

theorem maxDeg_lineGraph_lollipop_le (m k : ℕ) :
    maxDeg (lineGraph (lollipop (m + 2) (k + 1))) ≤ 2 * m + 2 := by
  have h := maxDeg_lineGraph_le (lollipop (m + 2) (k + 1))
  rw [maxDeg_lollipop] at h
  omega

theorem le_chromNum_lineGraph_lollipop (m k : ℕ) :
    m + 2 ≤ (lineGraph (lollipop (m + 2) (k + 1))).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_lollipop m k

theorem chromNum_lineGraph_lollipop_le (m k : ℕ) :
    (lineGraph (lollipop (m + 2) (k + 1))).chromNum ≤ 2 * m + 3 := by
  rw [chromNum_lineGraph]
  exact edgeChromNum_lollipop_le m k

theorem le_indepNum_lineGraph_lollipop (m k : ℕ) :
    (m + 2).choose 2 + (k + 1) ≤ (2 * m + 3) * (lineGraph (lollipop (m + 2) (k + 1))).indepNum := by
  rw [indepNum_lineGraph]
  exact le_matchNum_lollipop m k

theorem coverNum_lineGraph_lollipop (m k : ℕ) :
    (lineGraph (lollipop (m + 1) k)).coverNum
      = (m + 1).choose 2 + k - (lollipop (m + 1) k).matchNum := by
  rw [coverNum_lineGraph, E_lollipop]

/-! ### The line graph of a Kneser graph -/

theorem V_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) :
    (lineGraph (kneser n k)).V = n.choose k * (n - k).choose k / 2 := by
  rw [V_lineGraph, E_kneser n hk]

theorem maxDeg_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    maxDeg (lineGraph (kneser n k)) = 2 * (n - k).choose k - 2 :=
  maxDeg_lineGraph (E_pos_kneser n k hk hkn) (degSequence_kneser (n := n) hk)

theorem minDeg_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    minDeg (lineGraph (kneser n k)) = 2 * (n - k).choose k - 2 :=
  minDeg_lineGraph (E_pos_kneser n k hk hkn) (degSequence_kneser (n := n) hk)

theorem cliqueNum_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h3 : 3 ≤ (n - k).choose k) :
    (lineGraph (kneser n k)).cliqueNum = (n - k).choose k := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := kneser n k)
    (by rw [maxDeg_kneser n k hk hkn]; exact h3)
  rwa [maxDeg_kneser n k hk hkn] at h

theorem girth_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h3 : 3 ≤ (n - k).choose k) : (lineGraph (kneser n k)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_kneser n k hk hkn]; exact h3)

theorem not_isBipartite_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h3 : 3 ≤ (n - k).choose k) : ¬ IsBipartite (lineGraph (kneser n k)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_kneser n k hk hkn]; exact h3)

theorem not_isAcyclic_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h3 : 3 ≤ (n - k).choose k) : ¬ IsAcyclic (lineGraph (kneser n k)) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_kneser n k hk hkn]; exact h3)

theorem not_isTree_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (h3 : 3 ≤ (n - k).choose k) : ¬ IsTree (lineGraph (kneser n k)) :=
  not_isTree_lineGraph (by rw [maxDeg_kneser n k hk hkn]; exact h3)

theorem coverNum_lineGraph_kneser (n k : ℕ) (hk : 1 ≤ k) :
    (lineGraph (kneser n k)).coverNum
      = n.choose k * (n - k).choose k / 2 - (kneser n k).matchNum := by
  rw [coverNum_lineGraph, E_kneser n hk]

/-! ### The line graph of a Johnson graph -/

theorem E_pos_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) : 0 < (johnson n k).E := by
  have h1 := two_mul_E_johnson (le_of_lt h)
  have h2 : 0 < n.choose k := Nat.choose_pos (by omega)
  have h4 : 0 < n.choose k * (k * (n - k)) :=
    Nat.mul_pos h2 (Nat.mul_pos hk (by omega))
  omega

theorem V_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) :
    (lineGraph (johnson n k)).V = n.choose k * (k * (n - k)) / 2 := by
  rw [V_lineGraph, E_johnson hk]

theorem E_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) :
    (lineGraph (johnson n k)).E = n.choose k * (k * (n - k)).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_johnson hk)

theorem isRegularWith_lineGraph_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) :
    (lineGraph (johnson n k)).IsRegularWith (2 * (k * (n - k)) - 2) :=
  isRegularWith_lineGraph (E_pos_johnson hk h) (degSequence_johnson (le_of_lt h))

theorem maxDeg_lineGraph_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) :
    maxDeg (lineGraph (johnson n k)) = 2 * (k * (n - k)) - 2 :=
  maxDeg_lineGraph (E_pos_johnson hk h) (degSequence_johnson (le_of_lt h))

theorem minDeg_lineGraph_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) :
    minDeg (lineGraph (johnson n k)) = 2 * (k * (n - k)) - 2 :=
  minDeg_lineGraph (E_pos_johnson hk h) (degSequence_johnson (le_of_lt h))

theorem isConnected_lineGraph_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) :
    IsConnected (lineGraph (johnson n k)) :=
  isConnected_lineGraph (isConnected_johnson (le_of_lt h)) (E_pos_johnson hk h)

theorem numComponents_lineGraph_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) :
    (lineGraph (johnson n k)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_johnson (le_of_lt h)) (E_pos_johnson hk h)

theorem radius_lineGraph_johnson_le {n k : ℕ} (hk : 0 < k) (h : k < n) :
    (lineGraph (johnson n k)).radius ≤ min k (n - k) + 1 := by
  have hle := radius_lineGraph_le (G := johnson n k) (isConnected_johnson (le_of_lt h))
    (E_pos_johnson hk h)
  rwa [radius_johnson (le_of_lt h)] at hle

theorem diameter_lineGraph_johnson_le {n k : ℕ} (hk : 0 < k) (h : k < n) :
    (lineGraph (johnson n k)).diameter ≤ min k (n - k) + 1 := by
  have hle := diameter_lineGraph_le (G := johnson n k) (isConnected_johnson (le_of_lt h))
    (E_pos_johnson hk h)
  rwa [diameter_johnson (le_of_lt h)] at hle

theorem cliqueNum_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) (h3 : 3 ≤ k * (n - k)) :
    (lineGraph (johnson n k)).cliqueNum = k * (n - k) := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := johnson n k)
    (by rw [maxDeg_johnson hk]; exact h3)
  rwa [maxDeg_johnson hk] at h

theorem girth_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) (h3 : 3 ≤ k * (n - k)) :
    (lineGraph (johnson n k)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_johnson hk]; exact h3)

theorem not_isBipartite_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) (h3 : 3 ≤ k * (n - k)) :
    ¬ IsBipartite (lineGraph (johnson n k)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_johnson hk]; exact h3)

theorem not_isAcyclic_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) (h3 : 3 ≤ k * (n - k)) :
    ¬ IsAcyclic (lineGraph (johnson n k)) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_johnson hk]; exact h3)

theorem not_isTree_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) (h3 : 3 ≤ k * (n - k)) :
    ¬ IsTree (lineGraph (johnson n k)) :=
  not_isTree_lineGraph (by rw [maxDeg_johnson hk]; exact h3)

theorem le_chromNum_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) :
    k * (n - k) ≤ (lineGraph (johnson n k)).chromNum := by
  rw [chromNum_lineGraph]
  exact le_edgeChromNum_johnson hk

theorem coverNum_lineGraph_johnson {n k : ℕ} (hk : k ≤ n) :
    (lineGraph (johnson n k)).coverNum
      = n.choose k * (k * (n - k)) / 2 - (johnson n k).matchNum := by
  rw [coverNum_lineGraph, E_johnson hk]

theorem degSequence_lineGraph_johnson {n k : ℕ} (hk : 0 < k) (h : k < n) :
    degSequence (lineGraph (johnson n k))
      = List.replicate (n.choose k * (k * (n - k)) / 2) (2 * (k * (n - k)) - 2) := by
  have hd := (isRegularWith_lineGraph_johnson hk h).degSequence
  rwa [V_lineGraph, E_johnson (le_of_lt h)] at hd

/-! ### The line graph of a grid graph -/

theorem E_pos_grid (m n : ℕ) : 0 < (path (m + 2) □g path (n + 2)).E := by
  rw [E_grid]
  positivity

theorem isConnected_lineGraph_grid (m n : ℕ) :
    IsConnected (lineGraph (path (m + 2) □g path (n + 2))) :=
  isConnected_lineGraph (isConnected_grid (m + 1) (n + 1)) (E_pos_grid m n)

theorem numComponents_lineGraph_grid (m n : ℕ) :
    (lineGraph (path (m + 2) □g path (n + 2))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_grid (m + 1) (n + 1)) (E_pos_grid m n)

theorem le_minDeg_lineGraph_grid (m n : ℕ) :
    2 ≤ minDeg (lineGraph (path (m + 2) □g path (n + 2))) := by
  have h := le_minDeg_lineGraph (G := path (m + 2) □g path (n + 2)) (E_pos_grid m n)
  rw [minDeg_grid] at h
  omega

theorem radius_lineGraph_grid_le (m n : ℕ) :
    (lineGraph (path (m + 2) □g path (n + 2))).radius ≤ (m + 2) / 2 + (n + 2) / 2 + 1 := by
  have h := radius_lineGraph_le (G := path (m + 2) □g path (n + 2))
    (isConnected_grid (m + 1) (n + 1)) (E_pos_grid m n)
  rw [radius_grid] at h
  omega

theorem diameter_lineGraph_grid_le (m n : ℕ) :
    (lineGraph (path (m + 2) □g path (n + 2))).diameter ≤ m + n + 3 := by
  have h := diameter_lineGraph_le (G := path (m + 2) □g path (n + 2))
    (isConnected_grid (m + 1) (n + 1)) (E_pos_grid m n)
  rw [diameter_grid] at h
  omega

theorem cliqueNum_lineGraph_grid (m n : ℕ) :
    (lineGraph (path (m + 3) □g path (n + 3))).cliqueNum = 4 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := path (m + 3) □g path (n + 3))
    (by rw [maxDeg_grid]; omega)
  rw [maxDeg_grid] at h
  omega

theorem girth_lineGraph_grid (m n : ℕ) :
    (lineGraph (path (m + 3) □g path (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_grid]; omega)

theorem not_isBipartite_lineGraph_grid (m n : ℕ) :
    ¬ IsBipartite (lineGraph (path (m + 3) □g path (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_grid]; omega)

theorem not_isAcyclic_lineGraph_grid (m n : ℕ) :
    ¬ IsAcyclic (lineGraph (path (m + 3) □g path (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_grid]; omega)

theorem not_isTree_lineGraph_grid (m n : ℕ) :
    ¬ IsTree (lineGraph (path (m + 3) □g path (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_grid]; omega)

theorem maxDeg_lineGraph_grid_le (m n : ℕ) :
    maxDeg (lineGraph (path (m + 3) □g path (n + 3))) ≤ 6 := by
  have h := maxDeg_lineGraph_le (path (m + 3) □g path (n + 3))
  rw [maxDeg_grid] at h
  omega

/-! ### The line graph of a king graph -/

theorem E_pos_king (m n : ℕ) : 0 < (path (m + 2) ⊠g path (n + 2)).E := by
  rw [E_king]
  positivity

theorem isConnected_lineGraph_king (m n : ℕ) :
    IsConnected (lineGraph (path (m + 2) ⊠g path (n + 2))) :=
  isConnected_lineGraph (isConnected_king (m + 1) (n + 1)) (E_pos_king m n)

theorem numComponents_lineGraph_king (m n : ℕ) :
    (lineGraph (path (m + 2) ⊠g path (n + 2))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_king (m + 1) (n + 1)) (E_pos_king m n)

theorem le_minDeg_lineGraph_king (m n : ℕ) :
    4 ≤ minDeg (lineGraph (path (m + 2) ⊠g path (n + 2))) := by
  have h := le_minDeg_lineGraph (G := path (m + 2) ⊠g path (n + 2)) (E_pos_king m n)
  rw [minDeg_king] at h
  omega

theorem diameter_lineGraph_king_le (m n : ℕ) :
    (lineGraph (path (m + 2) ⊠g path (n + 2))).diameter ≤ max (m + 1) (n + 1) + 1 := by
  have h := diameter_lineGraph_le (G := path (m + 2) ⊠g path (n + 2))
    (isConnected_king (m + 1) (n + 1)) (E_pos_king m n)
  rw [diameter_king] at h
  omega

theorem cliqueNum_lineGraph_king (m n : ℕ) :
    (lineGraph (path (m + 3) ⊠g path (n + 3))).cliqueNum = 8 := by
  have h := cliqueNum_lineGraph_of_three_le_maxDeg (G := path (m + 3) ⊠g path (n + 3))
    (by rw [maxDeg_king]; omega)
  rw [maxDeg_king] at h
  omega

theorem girth_lineGraph_king (m n : ℕ) :
    (lineGraph (path (m + 3) ⊠g path (n + 3))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_king]; omega)

theorem not_isBipartite_lineGraph_king (m n : ℕ) :
    ¬ IsBipartite (lineGraph (path (m + 3) ⊠g path (n + 3))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_king]; omega)

theorem not_isAcyclic_lineGraph_king (m n : ℕ) :
    ¬ IsAcyclic (lineGraph (path (m + 3) ⊠g path (n + 3))) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_king]; omega)

theorem not_isTree_lineGraph_king (m n : ℕ) :
    ¬ IsTree (lineGraph (path (m + 3) ⊠g path (n + 3))) :=
  not_isTree_lineGraph (by rw [maxDeg_king]; omega)

theorem maxDeg_lineGraph_king_le (m n : ℕ) :
    maxDeg (lineGraph (path (m + 3) ⊠g path (n + 3))) ≤ 14 := by
  have h := maxDeg_lineGraph_le (path (m + 3) ⊠g path (n + 3))
  rw [maxDeg_king] at h
  omega

/-! ### The Mycielskian of a spider -/

@[simp] theorem V_mycielskian_spider (legs : List ℕ) :
    (mycielskian (spider legs)).V = 2 * legs.sum + 3 := by
  rw [V_mycielskian, V_spider]
  omega

@[simp] theorem E_mycielskian_spider (legs : List ℕ) :
    (mycielskian (spider legs)).E = 4 * legs.sum + 1 := by
  rw [E_mycielskian, E_spider, V_spider]
  omega

theorem chromNum_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    (mycielskian (spider legs)).chromNum = 3 := by
  have hm := chromNum_mycielskian (spider legs)
  rw [chromNum_spider legs h] at hm
  omega

theorem cliqueNum_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    (mycielskian (spider legs)).cliqueNum = 2 := by
  have hm := cliqueNum_mycielskian (spider legs) (by rw [V_spider]; omega)
  rw [cliqueNum_spider legs h] at hm
  omega

theorem minDeg_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    minDeg (mycielskian (spider legs)) = 2 := by
  have hm := minDeg_mycielskian (spider legs) (by rw [V_spider]; omega)
  rw [minDeg_spider legs h, V_spider] at hm
  omega

theorem isConnected_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    IsConnected (mycielskian (spider legs)) :=
  isConnected_mycielskian _ (by rw [minDeg_spider legs h]; omega)

theorem numComponents_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    (mycielskian (spider legs)).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_spider legs h]; omega)

theorem radius_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    (mycielskian (spider legs)).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_spider legs h]; omega)

theorem two_le_diameter_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    2 ≤ (mycielskian (spider legs)).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_spider legs h]; omega)

theorem diameter_mycielskian_spider_le_four (legs : List ℕ) (h : 0 < legs.sum) :
    (mycielskian (spider legs)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_spider legs h]; omega)

theorem four_le_girth_mycielskian_spider (legs : List ℕ) (h : 0 < legs.sum) :
    4 ≤ (mycielskian (spider legs)).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_spider legs h]) (by rw [E_spider]; omega)

theorem domNum_mycielskian_spider (legs : List ℕ) :
    (mycielskian (spider legs)).domNum = (spider legs).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_spider]; omega)

theorem coverNum_mycielskian_spider_le (legs : List ℕ) :
    (mycielskian (spider legs)).coverNum ≤ legs.sum + 2 := by
  have h := coverNum_mycielskian_le (spider legs)
  rw [V_spider] at h
  omega

theorem V_le_indepNum_mycielskian_spider (legs : List ℕ) :
    1 + legs.sum ≤ (mycielskian (spider legs)).indepNum := by
  have h := V_le_indepNum_mycielskian (spider legs)
  rwa [V_spider] at h

/-! ### The Mycielskian of a cycle with pendant paths -/

theorem E_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    (mycielskian (cyclePendant (m + 3) ks)).E = 4 * (m + 3 + ks.sum) := by
  rw [E_mycielskian, E_cyclePendant m ks h, V_cyclePendant]
  omega

theorem minDeg_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : minDeg (mycielskian (cyclePendant (m + 3) ks)) = 2 := by
  have hm := minDeg_mycielskian (cyclePendant (m + 3) ks) (by rw [V_cyclePendant]; omega)
  rw [minDeg_cyclePendant m ks h h2, V_cyclePendant] at hm
  omega

theorem isConnected_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : IsConnected (mycielskian (cyclePendant (m + 3) ks)) :=
  isConnected_mycielskian _ (by rw [minDeg_cyclePendant m ks h h2]; omega)

theorem numComponents_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : (mycielskian (cyclePendant (m + 3) ks)).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_cyclePendant m ks h h2]; omega)

theorem radius_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : (mycielskian (cyclePendant (m + 3) ks)).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_cyclePendant m ks h h2]; omega)

theorem two_le_diameter_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : 2 ≤ (mycielskian (cyclePendant (m + 3) ks)).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_cyclePendant m ks h h2]; omega)

theorem diameter_mycielskian_cyclePendant_le_four (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : (mycielskian (cyclePendant (m + 3) ks)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_cyclePendant m ks h h2]; omega)

theorem chromNum_mycielskian_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t + 2) :
    (mycielskian (cyclePendant (2 * t + 2) ks)).chromNum = 3 := by
  have hm := chromNum_mycielskian (cyclePendant (2 * t + 2) ks)
  rw [chromNum_cyclePendant_even t ks h] at hm
  omega

theorem domNum_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) :
    (mycielskian (cyclePendant (m + 1) ks)).domNum = (cyclePendant (m + 1) ks).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_cyclePendant]; omega)

theorem coverNum_mycielskian_cyclePendant_le (m : ℕ) (ks : List ℕ) :
    (mycielskian (cyclePendant m ks)).coverNum ≤ m + ks.sum + 1 := by
  have h := coverNum_mycielskian_le (cyclePendant m ks)
  rwa [V_cyclePendant] at h

theorem V_le_indepNum_mycielskian_cyclePendant (m : ℕ) (ks : List ℕ) :
    m + ks.sum ≤ (mycielskian (cyclePendant m ks)).indepNum := by
  have h := V_le_indepNum_mycielskian (cyclePendant m ks)
  rwa [V_cyclePendant] at h

/-! ### The line graph of a Mycielskian -/

theorem E_pos_mycielskian {G : IsoGraph} (h : 0 < G.V) : 0 < (mycielskian G).E := by
  rw [E_mycielskian]
  omega

theorem isConnected_lineGraph_mycielskian {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    IsConnected (lineGraph (mycielskian G)) :=
  isConnected_lineGraph (isConnected_mycielskian G h) (E_pos_mycielskian hV)

theorem numComponents_lineGraph_mycielskian {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    (lineGraph (mycielskian G)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_mycielskian G h) (E_pos_mycielskian hV)

theorem radius_lineGraph_mycielskian_le {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    (lineGraph (mycielskian G)).radius ≤ 3 := by
  have hr := radius_lineGraph_le (G := mycielskian G) (isConnected_mycielskian G h)
    (E_pos_mycielskian hV)
  rw [radius_mycielskian G h] at hr
  omega

theorem diameter_lineGraph_mycielskian_le {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    (lineGraph (mycielskian G)).diameter ≤ 5 := by
  have hd := diameter_lineGraph_le (G := mycielskian G) (isConnected_mycielskian G h)
    (E_pos_mycielskian hV)
  have h4 := diameter_mycielskian_le_four G h
  omega

theorem cliqueNum_lineGraph_mycielskian {G : IsoGraph} (h3 : 3 ≤ max (2 * maxDeg G) G.V) :
    (lineGraph (mycielskian G)).cliqueNum = max (2 * maxDeg G) G.V := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := mycielskian G)
    (by rw [maxDeg_mycielskian]; exact h3)
  rwa [maxDeg_mycielskian] at hm

theorem girth_lineGraph_mycielskian {G : IsoGraph} (h3 : 3 ≤ max (2 * maxDeg G) G.V) :
    (lineGraph (mycielskian G)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_mycielskian]; exact h3)

theorem not_isBipartite_lineGraph_mycielskian {G : IsoGraph}
    (h3 : 3 ≤ max (2 * maxDeg G) G.V) : ¬ IsBipartite (lineGraph (mycielskian G)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_mycielskian]; exact h3)

theorem not_isAcyclic_lineGraph_mycielskian {G : IsoGraph}
    (h3 : 3 ≤ max (2 * maxDeg G) G.V) : ¬ IsAcyclic (lineGraph (mycielskian G)) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_mycielskian]; exact h3)

theorem not_isTree_lineGraph_mycielskian {G : IsoGraph}
    (h3 : 3 ≤ max (2 * maxDeg G) G.V) : ¬ IsTree (lineGraph (mycielskian G)) :=
  not_isTree_lineGraph (by rw [maxDeg_mycielskian]; exact h3)

theorem maxDeg_lineGraph_mycielskian_le (G : IsoGraph) :
    maxDeg (lineGraph (mycielskian G)) ≤ 2 * max (2 * maxDeg G) G.V - 2 := by
  have hm := maxDeg_lineGraph_le (mycielskian G)
  rwa [maxDeg_mycielskian] at hm

theorem le_minDeg_lineGraph_mycielskian {G : IsoGraph} (hV : 0 < G.V) :
    2 * min (min (2 * G.minDeg) (G.minDeg + 1)) G.V - 2
      ≤ minDeg (lineGraph (mycielskian G)) := by
  have hm := le_minDeg_lineGraph (G := mycielskian G) (E_pos_mycielskian hV)
  rwa [minDeg_mycielskian G hV] at hm

theorem coverNum_lineGraph_mycielskian (G : IsoGraph) :
    (lineGraph (mycielskian G)).coverNum = 3 * G.E + G.V - (mycielskian G).matchNum := by
  rw [coverNum_lineGraph, E_mycielskian]

/-! ### The Mycielskian of a line graph -/

theorem E_mycielskian_lineGraph (G : IsoGraph) :
    (mycielskian (lineGraph G)).E = 3 * (lineGraph G).E + G.E := by
  rw [E_mycielskian, V_lineGraph]

theorem chromNum_mycielskian_lineGraph (G : IsoGraph) :
    (mycielskian (lineGraph G)).chromNum = G.edgeChromNum + 1 := by
  rw [chromNum_mycielskian, chromNum_lineGraph]

theorem cliqueNum_mycielskian_lineGraph {G : IsoGraph} (hE : 0 < G.E) (h : 3 ≤ G.maxDeg) :
    (mycielskian (lineGraph G)).cliqueNum = G.maxDeg := by
  have hm := cliqueNum_mycielskian (lineGraph G) (by rw [V_lineGraph]; exact hE)
  rw [cliqueNum_lineGraph_of_three_le_maxDeg h] at hm
  omega

theorem maxDeg_mycielskian_lineGraph (G : IsoGraph) :
    maxDeg (mycielskian (lineGraph G)) = max (2 * maxDeg (lineGraph G)) G.E := by
  rw [maxDeg_mycielskian, V_lineGraph]

theorem isConnected_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    IsConnected (mycielskian (lineGraph G)) :=
  isConnected_mycielskian _ h

theorem numComponents_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    (mycielskian (lineGraph G)).numComponents = 1 :=
  numComponents_mycielskian _ h

theorem radius_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    (mycielskian (lineGraph G)).radius = 2 :=
  radius_mycielskian _ h

theorem two_le_diameter_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    2 ≤ (mycielskian (lineGraph G)).diameter :=
  two_le_diameter_mycielskian _ h

theorem diameter_mycielskian_lineGraph_le_four {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    (mycielskian (lineGraph G)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ h

theorem coverNum_mycielskian_lineGraph_le (G : IsoGraph) :
    (mycielskian (lineGraph G)).coverNum ≤ G.E + 1 := by
  have h := coverNum_mycielskian_le (lineGraph G)
  rwa [V_lineGraph] at h

theorem E_le_indepNum_mycielskian_lineGraph (G : IsoGraph) :
    G.E ≤ (mycielskian (lineGraph G)).indepNum := by
  have h := V_le_indepNum_mycielskian (lineGraph G)
  rwa [V_lineGraph] at h

theorem domNum_mycielskian_lineGraph {G : IsoGraph} (hE : 0 < G.E) :
    (mycielskian (lineGraph G)).domNum = (lineGraph G).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_lineGraph]; exact hE)

theorem matchNum_mycielskian_lineGraph {G : IsoGraph} (h : 2 * (lineGraph G).matchNum = G.E) :
    (mycielskian (lineGraph G)).matchNum = G.E := by
  have hm := matchNum_mycielskian (lineGraph G) (by rw [V_lineGraph]; exact h)
  rwa [V_lineGraph] at hm

/-! ### The iterated line graph -/

theorem isRegularWith_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) (h : degSequence G = List.replicate n k) :
    (lineGraph (lineGraph G)).IsRegularWith (2 * (2 * k - 2) - 2) :=
  isRegularWith_lineGraph hE2 (isRegularWith_lineGraph hE h).degSequence

theorem maxDeg_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) (h : degSequence G = List.replicate n k) :
    maxDeg (lineGraph (lineGraph G)) = 2 * (2 * k - 2) - 2 :=
  maxDeg_lineGraph hE2 (isRegularWith_lineGraph hE h).degSequence

theorem minDeg_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) (h : degSequence G = List.replicate n k) :
    minDeg (lineGraph (lineGraph G)) = 2 * (2 * k - 2) - 2 :=
  minDeg_lineGraph hE2 (isRegularWith_lineGraph hE h).degSequence

theorem maxDeg_lineGraph_lineGraph_le (G : IsoGraph) :
    maxDeg (lineGraph (lineGraph G)) ≤ 2 * (2 * maxDeg G - 2) - 2 := by
  have h1 := maxDeg_lineGraph_le (lineGraph G)
  have h2 := maxDeg_lineGraph_le G
  omega

theorem isConnected_lineGraph_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : IsConnected (lineGraph (lineGraph G)) :=
  isConnected_lineGraph (isConnected_lineGraph hG hE) hE2

theorem numComponents_lineGraph_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : (lineGraph (lineGraph G)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_lineGraph hG hE) hE2

theorem radius_lineGraph_lineGraph_le {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : (lineGraph (lineGraph G)).radius ≤ G.radius + 2 := by
  have h1 := radius_lineGraph_le (G := lineGraph G) (isConnected_lineGraph hG hE) hE2
  have h2 := radius_lineGraph_le (G := G) hG hE
  omega

theorem diameter_lineGraph_lineGraph_le {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : (lineGraph (lineGraph G)).diameter ≤ G.diameter + 2 := by
  have h1 := diameter_lineGraph_le (G := lineGraph G) (isConnected_lineGraph hG hE) hE2
  have h2 := diameter_lineGraph_le (G := G) hG hE
  omega

theorem cliqueNum_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    (lineGraph (lineGraph G)).cliqueNum = 2 * k - 2 := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := lineGraph G)
    (by rw [maxDeg_lineGraph hE h]; exact h3)
  rwa [maxDeg_lineGraph hE h] at hm

theorem girth_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    (lineGraph (lineGraph G)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_lineGraph hE h]; exact h3)

theorem not_isBipartite_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    ¬ IsBipartite (lineGraph (lineGraph G)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_lineGraph hE h]; exact h3)

theorem not_isTree_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    ¬ IsTree (lineGraph (lineGraph G)) :=
  not_isTree_lineGraph (by rw [maxDeg_lineGraph hE h]; exact h3)

/-! ### The iterated Mycielskian -/

theorem minDeg_mycielskian_of_pos {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    (mycielskian G).minDeg = min (G.minDeg + 1) G.V := by
  have hm := minDeg_mycielskian G hV
  omega

@[simp] theorem V_mycielskian_mycielskian (G : IsoGraph) :
    (mycielskian (mycielskian G)).V = 4 * G.V + 3 := by
  rw [V_mycielskian, V_mycielskian]
  omega

@[simp] theorem E_mycielskian_mycielskian (G : IsoGraph) :
    (mycielskian (mycielskian G)).E = 9 * G.E + 5 * G.V + 1 := by
  rw [E_mycielskian, E_mycielskian, V_mycielskian]
  omega

theorem cliqueNum_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) :
    (mycielskian (mycielskian G)).cliqueNum = max G.cliqueNum 2 := by
  have h1 := cliqueNum_mycielskian (mycielskian G) (by rw [V_mycielskian]; omega)
  rw [cliqueNum_mycielskian G hV] at h1
  omega

theorem maxDeg_mycielskian_mycielskian (G : IsoGraph) :
    maxDeg (mycielskian (mycielskian G)) = max (2 * max (2 * maxDeg G) G.V) (2 * G.V + 1) := by
  rw [maxDeg_mycielskian, maxDeg_mycielskian, V_mycielskian]

theorem isConnected_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    IsConnected (mycielskian (mycielskian G)) :=
  isConnected_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem numComponents_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    (mycielskian (mycielskian G)).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem radius_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    (mycielskian (mycielskian G)).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem two_le_diameter_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V)
    (h : 0 < G.minDeg) : 2 ≤ (mycielskian (mycielskian G)).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem diameter_mycielskian_mycielskian_le_four {G : IsoGraph} (hV : 0 < G.V)
    (h : 0 < G.minDeg) : (mycielskian (mycielskian G)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem four_le_girth_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V)
    (hc : G.cliqueNum ≤ 2) : 4 ≤ (mycielskian (mycielskian G)).girth := by
  refine four_le_girth_mycielskian _ ?_ (by rw [E_mycielskian]; omega)
  rw [cliqueNum_mycielskian G hV]
  omega

theorem domNum_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) :
    (mycielskian (mycielskian G)).domNum = G.domNum + 2 := by
  have h1 := domNum_mycielskian (mycielskian G) (by rw [V_mycielskian]; omega)
  rw [domNum_mycielskian G hV] at h1
  omega

theorem coverNum_mycielskian_mycielskian_le (G : IsoGraph) :
    (mycielskian (mycielskian G)).coverNum ≤ 2 * G.V + 2 := by
  have h := coverNum_mycielskian_le (mycielskian G)
  rw [V_mycielskian] at h
  omega

theorem V_le_indepNum_mycielskian_mycielskian (G : IsoGraph) :
    2 * G.V + 1 ≤ (mycielskian (mycielskian G)).indepNum := by
  have h := V_le_indepNum_mycielskian (mycielskian G)
  rwa [V_mycielskian] at h

/-! ### Edge positivity for the binary operators -/

theorem E_pos_cartesianProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    0 < (G □g H).E := by
  have h := Nat.mul_pos hH hG
  rw [E_cartesianProduct]
  omega

theorem E_pos_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) : 0 < (G ∇g H).E := by
  have h := Nat.mul_pos hG hH
  rw [E_join]
  omega

theorem E_pos_disjUnion_left {G H : IsoGraph} (hG : 0 < G.E) : 0 < (G ⊕g H).E := by
  rw [E_disjUnion]
  omega

theorem E_pos_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    0 < (G ⊠g H).E := by
  have h := Nat.mul_pos hH hG
  rw [E_strongProduct]
  omega

/-! ### The line graph of a Cartesian product -/

theorem V_lineGraph_cartesianProduct (G H : IsoGraph) :
    (lineGraph (G □g H)).V = G.V * H.E + H.V * G.E := by
  rw [V_lineGraph, E_cartesianProduct]

theorem maxDeg_lineGraph_cartesianProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G □g H)) ≤ 2 * (maxDeg G + maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G □g H)
  rwa [maxDeg_cartesianProduct hG hH] at h

theorem le_minDeg_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G □g H).E) :
    2 * (minDeg G + minDeg H) - 2 ≤ minDeg (lineGraph (G □g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_cartesianProduct hG hH] at h

theorem isConnected_lineGraph_cartesianProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) : IsConnected (lineGraph (G □g H)) :=
  isConnected_lineGraph (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE

theorem numComponents_lineGraph_cartesianProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) : (lineGraph (G □g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE

theorem diameter_lineGraph_cartesianProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) :
    (lineGraph (G □g H)).diameter ≤ G.diameter + H.diameter + 1 := by
  have h := diameter_lineGraph_le (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE
  rw [diameter_cartesianProduct hG hH] at h
  omega

theorem radius_lineGraph_cartesianProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) :
    (lineGraph (G □g H)).radius ≤ G.radius + H.radius + 1 := by
  have h := radius_lineGraph_le (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE
  rw [radius_cartesianProduct hG hH] at h
  omega

theorem cliqueNum_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G + maxDeg H) :
    (lineGraph (G □g H)).cliqueNum = maxDeg G + maxDeg H := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G □g H)
    (by rw [maxDeg_cartesianProduct hG hH]; exact h3)
  rwa [maxDeg_cartesianProduct hG hH] at hm

theorem girth_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G + maxDeg H) : (lineGraph (G □g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_cartesianProduct hG hH]; exact h3)

theorem not_isBipartite_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V)
    (hH : 0 < H.V) (h3 : 3 ≤ maxDeg G + maxDeg H) : ¬ IsBipartite (lineGraph (G □g H)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_cartesianProduct hG hH]; exact h3)

/-! ### The line graph of a join -/

theorem V_lineGraph_join (G H : IsoGraph) :
    (lineGraph (G ∇g H)).V = G.E + H.E + G.V * H.V := by
  rw [V_lineGraph, E_join]

theorem maxDeg_lineGraph_join_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ∇g H)) ≤ 2 * max (maxDeg G + H.V) (G.V + maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ∇g H)
  rwa [maxDeg_join hG hH] at h

theorem le_minDeg_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    2 * min (minDeg G + H.V) (G.V + minDeg H) - 2 ≤ minDeg (lineGraph (G ∇g H)) := by
  have h := le_minDeg_lineGraph (E_pos_join hG hH)
  rwa [minDeg_join hG hH] at h

theorem isConnected_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (lineGraph (G ∇g H)) :=
  isConnected_lineGraph (isConnected_join hG hH) (E_pos_join hG hH)

theorem numComponents_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (lineGraph (G ∇g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_join hG hH) (E_pos_join hG hH)

theorem diameter_lineGraph_join_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (lineGraph (G ∇g H)).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (isConnected_join hG hH) (E_pos_join hG hH)
  have h2 := diameter_join_le_two hG hH
  omega

theorem cliqueNum_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ max (maxDeg G + H.V) (G.V + maxDeg H)) :
    (lineGraph (G ∇g H)).cliqueNum = max (maxDeg G + H.V) (G.V + maxDeg H) := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G ∇g H)
    (by rw [maxDeg_join hG hH]; exact h3)
  rwa [maxDeg_join hG hH] at hm

theorem girth_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ max (maxDeg G + H.V) (G.V + maxDeg H)) : (lineGraph (G ∇g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_join hG hH]; exact h3)

/-! ### The line graph of a disjoint union -/

theorem V_lineGraph_disjUnion (G H : IsoGraph) : (lineGraph (G ⊕g H)).V = G.E + H.E := by
  rw [V_lineGraph, E_disjUnion]

theorem maxDeg_lineGraph_disjUnion_le (G H : IsoGraph) :
    maxDeg (lineGraph (G ⊕g H)) ≤ 2 * max (maxDeg G) (maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ⊕g H)
  rwa [maxDeg_disjUnion] at h

theorem le_minDeg_lineGraph_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ⊕g H).E) :
    2 * min (minDeg G) (minDeg H) - 2 ≤ minDeg (lineGraph (G ⊕g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_disjUnion hG hH] at h

theorem numComponents_lineGraph_disjUnion {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    (lineGraph (G ⊕g H)).numComponents = 2 := by
  rw [lineGraph_disjUnion, numComponents_disjUnion, numComponents_lineGraph hG hE,
    numComponents_lineGraph hH hE2]

theorem not_isConnected_lineGraph_disjUnion {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    ¬ IsConnected (lineGraph (G ⊕g H)) := by
  intro h
  have h1 := numComponents_eq_one_of_isConnected h
  rw [numComponents_lineGraph_disjUnion hG hH hE hE2] at h1
  omega

/-! ### The line graph of a strong product -/

theorem V_lineGraph_strongProduct (G H : IsoGraph) :
    (lineGraph (G ⊠g H)).V = G.V * H.E + H.V * G.E + 2 * G.E * H.E := by
  rw [V_lineGraph, E_strongProduct]

theorem maxDeg_lineGraph_strongProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ⊠g H)) ≤ 2 * ((maxDeg G + 1) * (maxDeg H + 1) - 1) - 2 := by
  have h := maxDeg_lineGraph_le (G ⊠g H)
  rwa [maxDeg_strongProduct hG hH] at h

theorem le_minDeg_lineGraph_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ⊠g H).E) :
    2 * ((minDeg G + 1) * (minDeg H + 1) - 1) - 2 ≤ minDeg (lineGraph (G ⊠g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_strongProduct hG hH] at h

theorem isConnected_lineGraph_strongProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ⊠g H).E) : IsConnected (lineGraph (G ⊠g H)) :=
  isConnected_lineGraph (isConnected_strongProduct hG hH) hE

theorem diameter_lineGraph_strongProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ⊠g H).E) :
    (lineGraph (G ⊠g H)).diameter ≤ max G.diameter H.diameter + 1 := by
  have h := diameter_lineGraph_le (isConnected_strongProduct hG hH) hE
  rw [diameter_strongProduct hG hH] at h
  omega

theorem radius_lineGraph_strongProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ⊠g H).E) :
    (lineGraph (G ⊠g H)).radius ≤ max G.radius H.radius + 1 := by
  have h := radius_lineGraph_le (isConnected_strongProduct hG hH) hE
  rw [radius_strongProduct hG hH] at h
  omega

/-! ### The line graph of a complement -/

theorem V_lineGraph_compl (G : IsoGraph) : (lineGraph Gᶜ).V + G.E = G.V.choose 2 := by
  rw [V_lineGraph]
  exact E_compl G

theorem maxDeg_lineGraph_compl_le {G : IsoGraph} (hG : 0 < G.V) :
    maxDeg (lineGraph Gᶜ) ≤ 2 * (G.V - 1 - minDeg G) - 2 := by
  have h := maxDeg_lineGraph_le Gᶜ
  rwa [maxDeg_compl hG] at h

theorem le_minDeg_lineGraph_compl {G : IsoGraph} (hG : 0 < G.V) (hE : 0 < Gᶜ.E) :
    2 * (G.V - 1 - maxDeg G) - 2 ≤ minDeg (lineGraph Gᶜ) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_compl hG] at h

theorem cliqueNum_lineGraph_compl {G : IsoGraph} (hG : 0 < G.V) (h3 : 3 ≤ G.V - 1 - minDeg G) :
    (lineGraph Gᶜ).cliqueNum = G.V - 1 - minDeg G := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := Gᶜ)
    (by rw [maxDeg_compl hG]; exact h3)
  rwa [maxDeg_compl hG] at hm

/-! ### The Mycielskian of a join -/

@[simp] theorem V_mycielskian_join (G H : IsoGraph) :
    (mycielskian (G ∇g H)).V = 2 * G.V + 2 * H.V + 1 := by
  rw [V_mycielskian, V_join]
  omega

@[simp] theorem E_mycielskian_join (G H : IsoGraph) :
    (mycielskian (G ∇g H)).E = 3 * G.E + 3 * H.E + 3 * (G.V * H.V) + G.V + H.V := by
  rw [E_mycielskian, E_join, V_join]
  omega

theorem cliqueNum_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) :
    (mycielskian (G ∇g H)).cliqueNum = max (G.cliqueNum + H.cliqueNum) 2 := by
  have hm := cliqueNum_mycielskian (G ∇g H) (by rw [V_join]; omega)
  rwa [cliqueNum_join] at hm

theorem maxDeg_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G ∇g H))
      = max (2 * max (maxDeg G + H.V) (G.V + maxDeg H)) (G.V + H.V) := by
  rw [maxDeg_mycielskian, maxDeg_join hG hH, V_join]

theorem isConnected_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (mycielskian (G ∇g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_join hG hH]
  omega

theorem radius_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (mycielskian (G ∇g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_join hG hH]
  omega

/-! ### The Mycielskian of a Cartesian product -/

@[simp] theorem E_mycielskian_cartesianProduct (G H : IsoGraph) :
    (mycielskian (G □g H)).E = 3 * (G.V * H.E) + 3 * (H.V * G.E) + G.V * H.V := by
  rw [E_mycielskian, E_cartesianProduct, V_cartesianProduct]
  omega

theorem maxDeg_mycielskian_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G □g H)) = max (2 * (maxDeg G + maxDeg H)) (G.V * H.V) := by
  rw [maxDeg_mycielskian, maxDeg_cartesianProduct hG hH, V_cartesianProduct]

theorem isConnected_mycielskian_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) : IsConnected (mycielskian (G □g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_cartesianProduct hG hH]
  omega

theorem radius_mycielskian_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) : (mycielskian (G □g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_cartesianProduct hG hH]
  omega

/-! ### The Mycielskian of a disjoint union -/

@[simp] theorem V_mycielskian_disjUnion (G H : IsoGraph) :
    (mycielskian (G ⊕g H)).V = 2 * G.V + 2 * H.V + 1 := by
  rw [V_mycielskian, V_disjUnion]
  omega

@[simp] theorem E_mycielskian_disjUnion (G H : IsoGraph) :
    (mycielskian (G ⊕g H)).E = 3 * G.E + 3 * H.E + G.V + H.V := by
  rw [E_mycielskian, E_disjUnion, V_disjUnion]
  omega

theorem matchNum_mycielskian_disjUnion {G H : IsoGraph}
    (h : 2 * (G.matchNum + H.matchNum) = G.V + H.V) :
    (mycielskian (G ⊕g H)).matchNum = G.V + H.V := by
  have hm := matchNum_mycielskian (G ⊕g H) (by rw [matchNum_disjUnion, V_disjUnion]; exact h)
  rwa [V_disjUnion] at hm

theorem domNum_mycielskian_disjUnion {G H : IsoGraph} (hG : 0 < G.V) :
    (mycielskian (G ⊕g H)).domNum = G.domNum + H.domNum + 1 := by
  have hm := domNum_mycielskian (G ⊕g H) (by rw [V_disjUnion]; omega)
  rwa [domNum_disjUnion] at hm

/-! ### The Mycielskian of a complement -/

theorem E_mycielskian_compl (G : IsoGraph) :
    (mycielskian Gᶜ).E + 3 * G.E = 3 * (G.V.choose 2) + G.V := by
  have h := E_compl G
  rw [E_mycielskian, V_compl]
  omega

theorem maxDeg_mycielskian_compl {G : IsoGraph} (hG : 0 < G.V) :
    maxDeg (mycielskian Gᶜ) = max (2 * (G.V - 1 - minDeg G)) G.V := by
  rw [maxDeg_mycielskian, maxDeg_compl hG, V_compl]

theorem cliqueNum_mycielskian_compl {G : IsoGraph} (hG : 0 < G.V) :
    (mycielskian Gᶜ).cliqueNum = max G.indepNum 2 := by
  have hm := cliqueNum_mycielskian Gᶜ (by rw [V_compl]; exact hG)
  rwa [cliqueNum_compl] at hm

/-! ### The Mycielskian of a strong product -/

@[simp] theorem E_mycielskian_strongProduct (G H : IsoGraph) :
    (mycielskian (G ⊠g H)).E
      = 3 * (G.V * H.E) + 3 * (H.V * G.E) + 3 * (2 * G.E * H.E) + G.V * H.V := by
  rw [E_mycielskian, E_strongProduct, V_strongProduct]
  omega

/-! ### Edge positivity for the tensor and lexicographic products -/

theorem E_pos_tensorProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    0 < (G ⊗g H).E := by
  rw [E_tensorProduct]
  exact Nat.mul_pos (by omega) hH

theorem E_pos_lexProduct_left {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    0 < (G ·g H).E := by
  have h : 0 < H.V * H.V * G.E := Nat.mul_pos (Nat.mul_pos hH hH) hG
  rw [E_lexProduct]
  omega

theorem E_pos_lexProduct_right {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.E) :
    0 < (G ·g H).E := by
  have h : 0 < G.V * H.E := Nat.mul_pos hG hH
  rw [E_lexProduct]
  omega

/-! ### The line graph of a tensor product -/

theorem V_lineGraph_tensorProduct (G H : IsoGraph) :
    (lineGraph (G ⊗g H)).V = 2 * G.E * H.E := by
  rw [V_lineGraph, E_tensorProduct]

theorem maxDeg_lineGraph_tensorProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ⊗g H)) ≤ 2 * (maxDeg G * maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ⊗g H)
  rwa [maxDeg_tensorProduct hG hH] at h

theorem le_minDeg_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ⊗g H).E) :
    2 * (minDeg G * minDeg H) - 2 ≤ minDeg (lineGraph (G ⊗g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_tensorProduct hG hH] at h

theorem isConnected_lineGraph_tensorProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hb : ¬ IsBipartite G) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    IsConnected (lineGraph (G ⊗g H)) :=
  isConnected_lineGraph (isConnected_tensorProduct hG hH hb hE2) (E_pos_tensorProduct hE hE2)

theorem numComponents_lineGraph_tensorProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hb : ¬ IsBipartite G) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    (lineGraph (G ⊗g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_tensorProduct hG hH hb hE2) (E_pos_tensorProduct hE hE2)

theorem cliqueNum_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * maxDeg H) :
    (lineGraph (G ⊗g H)).cliqueNum = maxDeg G * maxDeg H := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G ⊗g H)
    (by rw [maxDeg_tensorProduct hG hH]; exact h3)
  rwa [maxDeg_tensorProduct hG hH] at hm

theorem girth_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * maxDeg H) : (lineGraph (G ⊗g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_tensorProduct hG hH]; exact h3)

theorem not_isBipartite_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * maxDeg H) : ¬ IsBipartite (lineGraph (G ⊗g H)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_tensorProduct hG hH]; exact h3)

/-! ### The line graph of a lexicographic product -/

theorem V_lineGraph_lexProduct (G H : IsoGraph) :
    (lineGraph (G ·g H)).V = H.V * H.V * G.E + G.V * H.E := by
  rw [V_lineGraph, E_lexProduct]

theorem maxDeg_lineGraph_lexProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ·g H)) ≤ 2 * (maxDeg G * H.V + maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ·g H)
  rwa [maxDeg_lexProduct hG hH] at h

theorem le_minDeg_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ·g H).E) :
    2 * (minDeg G * H.V + minDeg H) - 2 ≤ minDeg (lineGraph (G ·g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_lexProduct hG hH] at h

theorem isConnected_lineGraph_lexProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ·g H).E) : IsConnected (lineGraph (G ·g H)) :=
  isConnected_lineGraph (isConnected_lexProduct hG hH) hE

theorem numComponents_lineGraph_lexProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ·g H).E) : (lineGraph (G ·g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_lexProduct hG hH) hE

theorem diameter_lineGraph_lexProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ·g H).E) :
    (lineGraph (G ·g H)).diameter ≤ G.diameter + H.diameter + 1 := by
  have h := diameter_lineGraph_le (isConnected_lexProduct hG hH) hE
  have h2 := diameter_lexProduct_le hG hH
  omega

theorem cliqueNum_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * H.V + maxDeg H) :
    (lineGraph (G ·g H)).cliqueNum = maxDeg G * H.V + maxDeg H := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G ·g H)
    (by rw [maxDeg_lexProduct hG hH]; exact h3)
  rwa [maxDeg_lexProduct hG hH] at hm

theorem girth_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * H.V + maxDeg H) : (lineGraph (G ·g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_lexProduct hG hH]; exact h3)

theorem not_isBipartite_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * H.V + maxDeg H) : ¬ IsBipartite (lineGraph (G ·g H)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_lexProduct hG hH]; exact h3)

/-! ### The Mycielskian of a tensor product -/

theorem maxDeg_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G ⊗g H)) = max (2 * (maxDeg G * maxDeg H)) (G.V * H.V) := by
  rw [maxDeg_mycielskian, maxDeg_tensorProduct hG hH, V_tensorProduct]

theorem cliqueNum_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (mycielskian (G ⊗g H)).cliqueNum = max (min G.cliqueNum H.cliqueNum) 2 := by
  have hm := cliqueNum_mycielskian (G ⊗g H) (by rw [V_tensorProduct]; exact Nat.mul_pos hG hH)
  rwa [cliqueNum_tensorProduct] at hm

theorem isConnected_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) (h2 : 0 < minDeg H) : IsConnected (mycielskian (G ⊗g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_tensorProduct hG hH]
  exact Nat.mul_pos h h2

theorem radius_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) (h2 : 0 < minDeg H) : (mycielskian (G ⊗g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_tensorProduct hG hH]
  exact Nat.mul_pos h h2

/-! ### The Mycielskian of a lexicographic product -/

@[simp] theorem E_mycielskian_lexProduct (G H : IsoGraph) :
    (mycielskian (G ·g H)).E = 3 * (H.V * H.V * G.E) + 3 * (G.V * H.E) + G.V * H.V := by
  rw [E_mycielskian, E_lexProduct, V_lexProduct]
  omega

theorem maxDeg_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G ·g H)) = max (2 * (maxDeg G * H.V + maxDeg H)) (G.V * H.V) := by
  rw [maxDeg_mycielskian, maxDeg_lexProduct hG hH, V_lexProduct]

theorem cliqueNum_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (mycielskian (G ·g H)).cliqueNum = max (G.cliqueNum * H.cliqueNum) 2 := by
  have hm := cliqueNum_mycielskian (G ·g H) (by rw [V_lexProduct]; exact Nat.mul_pos hG hH)
  rwa [cliqueNum_lexProduct] at hm

theorem isConnected_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg H) : IsConnected (mycielskian (G ·g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_lexProduct hG hH]
  omega

theorem radius_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg H) : (mycielskian (G ·g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_lexProduct hG hH]
  omega

end IsoGraph
