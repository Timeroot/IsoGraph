import IsoGraph.SmallGraphs.Brackets

/-!
# Complements

Complements of the named graphs and of the parametrised families, and their invariants.
-/

namespace IsoGraph

theorem chromNum_compl_hypercube (n : ℕ) : ((hypercube (n + 1))ᶜ).chromNum = 2 ^ n := by
  rw [chromNum_compl, cliqueCoverNum_hypercube]

theorem maxDeg_compl_hypercube (n : ℕ) :
    maxDeg ((hypercube n)ᶜ) = 2 ^ n - 1 - n := by
  have h := maxDeg_compl (G := hypercube n) (by rw [V_hypercube]; positivity)
  rwa [V_hypercube, minDeg_hypercube] at h

theorem minDeg_compl_hypercube (n : ℕ) :
    minDeg ((hypercube n)ᶜ) = 2 ^ n - 1 - n := by
  have h := minDeg_compl (G := hypercube n) (by rw [V_hypercube]; positivity)
  rwa [V_hypercube, maxDeg_hypercube] at h

theorem two_mul_E_le_autCount_compl_hypercube (n : ℕ) :
    2 ^ n * n ≤ ((hypercube n)ᶜ).autCount := by
  rw [autCount_compl]
  exact two_mul_E_le_autCount_hypercube n

theorem maxDeg_compl_crown (n : ℕ) : maxDeg ((crown (n + 2))ᶜ) = n + 2 := by
  have h := maxDeg_compl (G := crown (n + 2)) (by rw [V_crown]; omega)
  rw [V_crown, minDeg_crown] at h
  omega

theorem minDeg_compl_crown (n : ℕ) : minDeg ((crown (n + 2))ᶜ) = n + 2 := by
  have h := minDeg_compl (G := crown (n + 2)) (by rw [V_crown]; omega)
  rw [V_crown, maxDeg_crown] at h
  omega

theorem E_compl_crown (n : ℕ) : ((crown n)ᶜ).E = (2 * n).choose 2 - 2 * n.choose 2 := by
  have h := E_compl (crown n)
  rw [E_crown, V_crown] at h
  omega

/-! ### Complements of the wheel, the ladder and the prism -/

theorem chromNum_compl_wheel (n : ℕ) : ((wheel (n + 4))ᶜ).chromNum = (n + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_wheel]

theorem maxDeg_compl_wheel (n : ℕ) : maxDeg ((wheel (n + 3))ᶜ) = n := by
  have h := maxDeg_compl (G := wheel (n + 3)) (by rw [V_wheel]; omega)
  rw [V_wheel, minDeg_wheel] at h
  omega

theorem minDeg_compl_wheel (n : ℕ) : minDeg ((wheel (n + 3))ᶜ) = 0 := by
  have h := minDeg_compl (G := wheel (n + 3)) (by rw [V_wheel]; omega)
  rw [V_wheel, maxDeg_wheel] at h
  omega

theorem E_compl_wheel (n : ℕ) : ((wheel (n + 3))ᶜ).E = (n + 4).choose 2 - 2 * (n + 3) := by
  have h := E_compl (wheel (n + 3))
  rw [E_wheel, V_wheel, show 1 + (n + 3) = n + 4 from by ring] at h
  omega

theorem chromNum_compl_ladder (n : ℕ) : ((ladder n)ᶜ).chromNum = n := by
  rw [chromNum_compl, cliqueCoverNum_ladder]

theorem maxDeg_compl_ladder (n : ℕ) : maxDeg ((ladder (n + 3))ᶜ) = 2 * n + 3 := by
  have h := maxDeg_compl (G := ladder (n + 3)) (by rw [V_ladder]; omega)
  have h2 : minDeg (ladder (n + 3)) = 2 := by
    rw [show n + 3 = n + 1 + 2 from by ring, minDeg_ladder]
  rw [V_ladder, h2] at h
  omega

theorem minDeg_compl_ladder (n : ℕ) : minDeg ((ladder (n + 3))ᶜ) = 2 * n + 2 := by
  have h := minDeg_compl (G := ladder (n + 3)) (by rw [V_ladder]; omega)
  rw [V_ladder, maxDeg_ladder] at h
  omega

theorem E_compl_ladder (n : ℕ) :
    ((ladder (n + 1))ᶜ).E = ((n + 1) * 2).choose 2 - (3 * n + 1) := by
  have h := E_compl (ladder (n + 1))
  rw [E_ladder, V_ladder] at h
  omega

theorem chromNum_compl_prism (n : ℕ) : ((prism (n + 4))ᶜ).chromNum = n + 4 := by
  rw [chromNum_compl, cliqueCoverNum_prism]

theorem maxDeg_compl_prism (n : ℕ) : maxDeg ((prism (n + 3))ᶜ) = 2 * n + 2 := by
  have h := maxDeg_compl (G := prism (n + 3)) (by rw [V_prism]; omega)
  rw [V_prism, minDeg_prism] at h
  omega

theorem minDeg_compl_prism (n : ℕ) : minDeg ((prism (n + 3))ᶜ) = 2 * n + 2 := by
  have h := minDeg_compl (G := prism (n + 3)) (by rw [V_prism]; omega)
  rw [V_prism, maxDeg_prism] at h
  omega

theorem E_compl_prism (n : ℕ) :
    ((prism (n + 3))ᶜ).E = ((n + 3) * 2).choose 2 - 3 * (n + 3) := by
  have h := E_compl (prism (n + 3))
  rw [E_prism, V_prism] at h
  omega

/-! ### Complements of the tadpole, lollipop, spider, theta and cycle-pendant families -/

theorem indepNum_compl_tadpole (m k : ℕ) : ((tadpole (m + 4) k)ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_tadpole]

theorem cliqueCoverNum_compl_tadpole_even (m k : ℕ) :
    ((tadpole (2 * m + 4) k)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_tadpole_even]

theorem cliqueCoverNum_compl_tadpole_odd (m k : ℕ) :
    ((tadpole (2 * m + 3) k)ᶜ).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_tadpole_odd]

theorem maxDeg_compl_tadpole (m k : ℕ) :
    maxDeg ((tadpole (m + 3) (k + 1))ᶜ) = m + k + 2 := by
  have h := maxDeg_compl (G := tadpole (m + 3) (k + 1)) (by rw [V_tadpole]; omega)
  rw [V_tadpole, minDeg_tadpole] at h
  omega

theorem minDeg_compl_tadpole (m k : ℕ) :
    minDeg ((tadpole (m + 3) (k + 1))ᶜ) = m + k := by
  have h := minDeg_compl (G := tadpole (m + 3) (k + 1)) (by rw [V_tadpole]; omega)
  rw [V_tadpole, maxDeg_tadpole] at h
  omega

theorem E_compl_tadpole (m k : ℕ) :
    ((tadpole (m + 3) k)ᶜ).E = (m + 3 + k).choose 2 - (m + 3 + k) := by
  have h := E_compl (tadpole (m + 3) k)
  rw [E_tadpole, V_tadpole] at h
  omega

theorem indepNum_compl_lollipop (m k : ℕ) : ((lollipop (m + 2) k)ᶜ).indepNum = m + 2 := by
  rw [indepNum_compl, cliqueNum_lollipop]

theorem cliqueCoverNum_compl_lollipop (m k : ℕ) :
    ((lollipop (m + 2) k)ᶜ).cliqueCoverNum = m + 2 := by
  rw [cliqueCoverNum_compl, chromNum_lollipop]

theorem maxDeg_compl_lollipop (m k : ℕ) :
    maxDeg ((lollipop (m + 2) (k + 1))ᶜ) = m + k + 1 := by
  have h := maxDeg_compl (G := lollipop (m + 2) (k + 1)) (by rw [V_lollipop]; omega)
  rw [V_lollipop, minDeg_lollipop] at h
  omega

theorem minDeg_compl_lollipop (m k : ℕ) : minDeg ((lollipop (m + 2) (k + 1))ᶜ) = k := by
  have h := minDeg_compl (G := lollipop (m + 2) (k + 1)) (by rw [V_lollipop]; omega)
  rw [V_lollipop, maxDeg_lollipop] at h
  omega

theorem E_compl_lollipop (m k : ℕ) :
    ((lollipop (m + 1) k)ᶜ).E = (m + 1 + k).choose 2 - ((m + 1).choose 2 + k) := by
  have h := E_compl (lollipop (m + 1) k)
  rw [E_lollipop, V_lollipop] at h
  omega

theorem indepNum_compl_spider (legs : List ℕ) (h : 0 < legs.sum) :
    ((spider legs)ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_spider legs h]

theorem cliqueCoverNum_compl_spider (legs : List ℕ) (h : 0 < legs.sum) :
    ((spider legs)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_spider legs h]

theorem maxDeg_compl_spider (legs : List ℕ) (hs : 0 < legs.sum) :
    maxDeg ((spider legs)ᶜ) = legs.sum - 1 := by
  have h := maxDeg_compl (G := spider legs) (by rw [V_spider]; omega)
  rw [V_spider, minDeg_spider legs hs] at h
  omega

theorem E_compl_spider (legs : List ℕ) :
    ((spider legs)ᶜ).E = (1 + legs.sum).choose 2 - legs.sum := by
  have h := E_compl (spider legs)
  rw [E_spider, V_spider] at h
  omega

theorem cliqueCoverNum_compl_thetaGraph_odd {xs : List ℕ} (hne : xs ≠ [])
    (h : ∀ k ∈ xs, k % 2 = 1) : ((thetaGraph xs)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_thetaGraph_odd hne h]

theorem cliqueCoverNum_compl_thetaGraph_even {xs : List ℕ} (hne : xs ≠ [])
    (h0 : ∀ k ∈ xs, 0 < k) (h : ∀ k ∈ xs, k % 2 = 0) :
    ((thetaGraph xs)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_thetaGraph_even hne h0 h]

theorem E_compl_thetaGraph (xs : List ℕ) (h0 : ∀ k ∈ xs, 0 < k) :
    ((thetaGraph xs)ᶜ).E = (2 + xs.sum).choose 2 - (xs.sum + xs.length) := by
  have h := E_compl (thetaGraph xs)
  rw [E_thetaGraph xs h0, V_thetaGraph] at h
  omega

theorem cliqueCoverNum_compl_cyclePendant_even (t : ℕ) (ks : List ℕ)
    (h : ks.length ≤ 2 * t + 2) : ((cyclePendant (2 * t + 2) ks)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_cyclePendant_even t ks h]

theorem maxDeg_compl_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3)
    (h2 : 0 < ks.sum) : maxDeg ((cyclePendant (m + 3) ks)ᶜ) = m + ks.sum + 1 := by
  have hd := maxDeg_compl (G := cyclePendant (m + 3) ks) (by rw [V_cyclePendant]; omega)
  rw [V_cyclePendant, minDeg_cyclePendant m ks h h2] at hd
  omega

theorem E_compl_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    ((cyclePendant (m + 3) ks)ᶜ).E = (m + 3 + ks.sum).choose 2 - (m + 3 + ks.sum) := by
  have hd := E_compl (cyclePendant (m + 3) ks)
  rw [E_cyclePendant m ks h, V_cyclePendant] at hd
  omega

/-! ### Complements of the double star, the Johnson and Kneser graphs -/

theorem cliqueNum_compl_doubleStar (m n : ℕ) :
    ((doubleStar (m + 1) (n + 1))ᶜ).cliqueNum = m + n + 2 := by
  rw [cliqueNum_compl, indepNum_doubleStar]

theorem indepNum_compl_doubleStar (m n : ℕ) : ((doubleStar m n)ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_doubleStar]

theorem chromNum_compl_doubleStar (m n : ℕ) :
    ((doubleStar (m + 1) (n + 1))ᶜ).chromNum = m + n + 2 := by
  rw [chromNum_compl, cliqueCoverNum_doubleStar]

theorem cliqueCoverNum_compl_doubleStar (m n : ℕ) :
    ((doubleStar m n)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_doubleStar]

theorem maxDeg_compl_doubleStar (m n : ℕ) : maxDeg ((doubleStar m n)ᶜ) = m + n := by
  have h := maxDeg_compl (G := doubleStar m n) (by rw [V_doubleStar]; omega)
  rw [V_doubleStar, minDeg_doubleStar] at h
  omega

theorem minDeg_compl_doubleStar (m n : ℕ) : minDeg ((doubleStar m n)ᶜ) = min m n := by
  have h := minDeg_compl (G := doubleStar m n) (by rw [V_doubleStar]; omega)
  rw [V_doubleStar, maxDeg_doubleStar] at h
  omega

theorem E_compl_doubleStar (m n : ℕ) :
    ((doubleStar m n)ᶜ).E = (2 + m + n).choose 2 - (m + n + 1) := by
  have h := E_compl (doubleStar m n)
  rw [E_doubleStar, V_doubleStar] at h
  omega

theorem maxDeg_compl_johnson {n k : ℕ} (hk : k ≤ n) :
    maxDeg ((johnson n k)ᶜ) = n.choose k - 1 - k * (n - k) := by
  have h := maxDeg_compl (G := johnson n k) (by rw [V_johnson]; exact Nat.choose_pos hk)
  rwa [V_johnson, minDeg_johnson hk] at h

theorem minDeg_compl_johnson {n k : ℕ} (hk : k ≤ n) :
    minDeg ((johnson n k)ᶜ) = n.choose k - 1 - k * (n - k) := by
  have h := minDeg_compl (G := johnson n k) (by rw [V_johnson]; exact Nat.choose_pos hk)
  rwa [V_johnson, maxDeg_johnson hk] at h

theorem E_compl_johnson {n k : ℕ} (hk : k ≤ n) :
    ((johnson n k)ᶜ).E = (n.choose k).choose 2 - n.choose k * (k * (n - k)) / 2 := by
  have h := E_compl (johnson n k)
  rw [E_johnson hk, V_johnson] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    maxDeg ((kneser n k)ᶜ) = n.choose k - 1 - (n - k).choose k := by
  have h := maxDeg_compl (G := kneser n k) (by rw [V_kneser]; exact Nat.choose_pos hkn)
  rwa [V_kneser, minDeg_kneser n k hk hkn] at h

theorem minDeg_compl_kneser (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    minDeg ((kneser n k)ᶜ) = n.choose k - 1 - (n - k).choose k := by
  have h := minDeg_compl (G := kneser n k) (by rw [V_kneser]; exact Nat.choose_pos hkn)
  rwa [V_kneser, maxDeg_kneser n k hk hkn] at h

theorem E_compl_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ((kneser n k)ᶜ).E = (n.choose k).choose 2 - n.choose k * (n - k).choose k / 2 := by
  have h := E_compl (kneser n k)
  rw [E_kneser n hk, V_kneser] at h
  rw [← h, Nat.add_sub_cancel]

theorem indepNum_compl_grotzsch : grotzschᶜ.indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_grotzsch]

theorem chromNum_compl_grotzsch : grotzschᶜ.chromNum = 6 := by
  rw [chromNum_compl, cliqueCoverNum_grotzsch]

@[simp] theorem cliqueCoverNum_compl_grotzsch : grotzschᶜ.cliqueCoverNum = 4 := by
  rw [cliqueCoverNum_compl, chromNum_grotzsch]

theorem cliqueNum_compl_grotzsch_le : grotzschᶜ.cliqueNum ≤ 6 := by
  rw [cliqueNum_compl]
  exact indepNum_grotzsch_le

theorem maxDeg_compl_grotzsch : maxDeg grotzschᶜ = 7 := by
  have h := maxDeg_compl (G := grotzsch) (by rw [V_grotzsch]; omega)
  rw [V_grotzsch, minDeg_grotzsch] at h
  omega

theorem minDeg_compl_grotzsch : minDeg grotzschᶜ = 5 := by
  have h := minDeg_compl (G := grotzsch) (by rw [V_grotzsch]; omega)
  rw [V_grotzsch, maxDeg_grotzsch] at h
  omega

theorem E_compl_grotzsch : grotzschᶜ.E = 35 := by
  have h := E_compl grotzsch
  rw [E_grotzsch, V_grotzsch, show (11 : ℕ).choose 2 = 55 from rfl] at h
  omega

theorem cliqueNum_compl_foldedCube_odd (m : ℕ) :
    ((foldedCube (2 * m + 1))ᶜ).cliqueNum = 2 ^ (2 * m) := by
  rw [cliqueNum_compl, indepNum_foldedCube_odd]

theorem cliqueCoverNum_compl_foldedCube_odd {n : ℕ} (hn : n % 2 = 1) :
    ((foldedCube n)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_foldedCube_odd hn]

/-! ### The grid and the torus -/

theorem cliqueNum_grid (m n : ℕ) : (path (m + 2) □g path (n + 2)).cliqueNum = 2 := by
  have h := cliqueNum_cartesianProduct (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_path, cliqueNum_path] at h
  omega

theorem maxDeg_grid (m n : ℕ) : maxDeg (path (m + 3) □g path (n + 3)) = 4 := by
  have h := maxDeg_cartesianProduct (G := path (m + 3)) (H := path (n + 3))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [maxDeg_path, maxDeg_path] at h
  omega

theorem minDeg_grid (m n : ℕ) : minDeg (path (m + 2) □g path (n + 2)) = 2 := by
  have h := minDeg_cartesianProduct (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path] at h
  omega

theorem diameter_grid (m n : ℕ) : (path (m + 1) □g path (n + 1)).diameter = m + n := by
  rw [diameter_cartesianProduct (isConnected_path m) (isConnected_path n), diameter_path,
    diameter_path]

theorem radius_grid (m n : ℕ) :
    (path (m + 1) □g path (n + 1)).radius = (m + 1) / 2 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_path m) (isConnected_path n), radius_path, radius_path]

/-- **The chromatic index of a grid is four**, two colours for each direction. -/
theorem edgeChromNum_grid (m n : ℕ) : (path (m + 3) □g path (n + 3)).edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := path (m + 3)) (H := path (n + 3))
      (by rw [show m + 3 = (m + 2) + 1 from rfl, E_path]; omega)
      (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
    rwa [edgeChromNum_path, edgeChromNum_path] at h
  · rw [← maxDeg_grid m n]
    exact maxDeg_le_edgeChromNum _

theorem maxDeg_king (m n : ℕ) : maxDeg (path (m + 3) ⊠g path (n + 3)) = 8 := by
  have h := maxDeg_strongProduct (G := path (m + 3)) (H := path (n + 3))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [maxDeg_path, maxDeg_path] at h
  omega

theorem minDeg_king (m n : ℕ) : minDeg (path (m + 2) ⊠g path (n + 2)) = 3 := by
  have h := minDeg_strongProduct (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path] at h
  omega

@[simp] theorem isConnected_king (m n : ℕ) : IsConnected (path (m + 1) ⊠g path (n + 1)) :=
  isConnected_strongProduct (isConnected_path m) (isConnected_path n)

@[simp] theorem girth_king (m n : ℕ) : (path (m + 2) ⊠g path (n + 2)).girth = 3 :=
  girth_strongProduct (by rw [E_path]; omega) (by rw [E_path]; omega)

/-! ### Complements of the grid, torus, cylinder and king graph -/

theorem E_compl_grid (m n : ℕ) :
    ((path (m + 1) □g path (n + 1))ᶜ).E
      = ((m + 1) * (n + 1)).choose 2 - ((m + 1) * n + (n + 1) * m) := by
  have h := E_compl (path (m + 1) □g path (n + 1))
  rw [E_cartesianProduct, E_path, E_path, V_path, V_path, V_cartesianProduct, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_grid (m n : ℕ) :
    maxDeg ((path (m + 3) □g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 3 := by
  have h := maxDeg_compl (G := path (m + 3) □g path (n + 3))
    (by rw [V_cartesianProduct, V_path, V_path]; positivity)
  rw [V_cartesianProduct, V_path, V_path, minDeg_grid] at h
  omega

theorem minDeg_compl_grid (m n : ℕ) :
    minDeg ((path (m + 3) □g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := path (m + 3) □g path (n + 3))
    (by rw [V_cartesianProduct, V_path, V_path]; positivity)
  rw [V_cartesianProduct, V_path, V_path, maxDeg_grid] at h
  omega

theorem indepNum_compl_grid (m n : ℕ) :
    ((path (m + 2) □g path (n + 2))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_grid]

theorem E_compl_king (m n : ℕ) :
    ((path (m + 1) ⊠g path (n + 1))ᶜ).E
      = ((m + 1) * (n + 1)).choose 2 - ((m + 1) * n + (n + 1) * m + 2 * m * n) := by
  have h := E_compl (path (m + 1) ⊠g path (n + 1))
  rw [E_strongProduct, E_path, E_path, V_path, V_path, V_strongProduct, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_king (m n : ℕ) :
    maxDeg ((path (m + 2) ⊠g path (n + 2))ᶜ) = (m + 2) * (n + 2) - 4 := by
  have h := maxDeg_compl (G := path (m + 2) ⊠g path (n + 2))
    (by rw [V_strongProduct, V_path, V_path]; positivity)
  rw [V_strongProduct, V_path, V_path, minDeg_king] at h
  omega

theorem minDeg_compl_king (m n : ℕ) :
    minDeg ((path (m + 3) ⊠g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 9 := by
  have h := minDeg_compl (G := path (m + 3) ⊠g path (n + 3))
    (by rw [V_strongProduct, V_path, V_path]; positivity)
  rw [V_strongProduct, V_path, V_path, maxDeg_king] at h
  omega

/-! ### Chromatic and clique cover numbers of complements -/

theorem chromNum_compl_cocktailParty (n : ℕ) : ((cocktailParty (n + 1))ᶜ).chromNum = 2 := by
  rw [chromNum_compl, cliqueCoverNum_cocktailParty]

theorem chromNum_compl_book (n : ℕ) : ((book n)ᶜ).chromNum = max 1 n := by
  rw [chromNum_compl, cliqueCoverNum_book]

theorem chromNum_compl_rook (m n : ℕ) :
    ((rook (m + 1) (n + 1))ᶜ).chromNum = min (m + 1) (n + 1) := by
  rw [chromNum_compl, cliqueCoverNum_rook]

theorem chromNum_compl_friendship (n : ℕ) : ((friendship (n + 1))ᶜ).chromNum = n + 1 := by
  rw [chromNum_compl, cliqueCoverNum_friendship]

@[simp] theorem chromNum_compl_petersen : petersenᶜ.chromNum = 5 := by
  rw [chromNum_compl, cliqueCoverNum_petersen]

theorem chromNum_compl_spider_pair (a b : ℕ) :
    ((spider [a, b])ᶜ).chromNum = (a + b + 2) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_spider_pair]

theorem chromNum_compl_spider_singleton (k : ℕ) :
    ((spider [k])ᶜ).chromNum = (k + 2) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_spider_singleton]

theorem chromNum_compl_thetaGraph_singleton (k : ℕ) :
    ((thetaGraph [k])ᶜ).chromNum = (k + 3) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_thetaGraph_singleton]

theorem chromNum_compl_circulant_one (n : ℕ) :
    ((circulant (n + 4) [1])ᶜ).chromNum = (n + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_circulant_one]

theorem chromNum_compl_tadpole_zero (m : ℕ) :
    ((tadpole (m + 4) 0)ᶜ).chromNum = (m + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_tadpole_zero]

theorem chromNum_compl_tadpole_one (k : ℕ) : ((tadpole 1 k)ᶜ).chromNum = (k + 2) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_tadpole_one]

theorem chromNum_compl_lollipop_one (k : ℕ) : ((lollipop 1 k)ᶜ).chromNum = (k + 2) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_lollipop_one]

theorem chromNum_compl_cyclePendant_replicate_zero (m j : ℕ) :
    ((cyclePendant (m + 4) (List.replicate j 0))ᶜ).chromNum = (m + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_cyclePendant_replicate_zero]

theorem cliqueCoverNum_compl_friendship (n : ℕ) :
    ((friendship (n + 1))ᶜ).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_friendship]

@[simp] theorem cliqueCoverNum_compl_petersen : petersenᶜ.cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_petersen]

theorem cliqueCoverNum_compl_triangular_even (m : ℕ) :
    ((triangular (2 * m + 4))ᶜ).cliqueCoverNum = 2 * m + 3 := by
  rw [cliqueCoverNum_compl, chromNum_triangular_even]

/-! ### Clique and independence numbers of complements -/

theorem indepNum_compl_book (n : ℕ) : ((book n)ᶜ).indepNum = 2 + min n 1 := by
  rw [indepNum_compl, cliqueNum_book]

theorem indepNum_compl_johnson_two_even (m : ℕ) :
    ((johnson (2 * m + 2) 2)ᶜ).indepNum = 2 * m + 1 := by
  rw [indepNum_compl, cliqueNum_johnson_two_even]

theorem indepNum_compl_friendship (n : ℕ) : ((friendship (n + 1))ᶜ).indepNum = 3 := by
  rw [indepNum_compl, cliqueNum_friendship]

theorem indepNum_compl_tadpole_one (k : ℕ) : ((tadpole 1 (k + 1))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_tadpole_one]

theorem indepNum_compl_lollipop_one (k : ℕ) : ((lollipop 1 (k + 1))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_lollipop_one]

theorem cliqueNum_compl_fan (n : ℕ) : ((fan (n + 1))ᶜ).cliqueNum = (n + 2) / 2 := by
  rw [cliqueNum_compl, indepNum_fan]

theorem cliqueNum_compl_friendship (n : ℕ) : ((friendship n)ᶜ).cliqueNum = max n 1 := by
  rw [cliqueNum_compl, indepNum_friendship]

theorem cliqueNum_compl_spider_pair (a b : ℕ) : ((spider [a, b])ᶜ).cliqueNum = (a + b + 2) / 2 := by
  rw [cliqueNum_compl, indepNum_spider_pair]

theorem cliqueNum_compl_spider_singleton (k : ℕ) : ((spider [k])ᶜ).cliqueNum = (k + 2) / 2 := by
  rw [cliqueNum_compl, indepNum_spider_singleton]

theorem cliqueNum_compl_tadpole_one (k : ℕ) : ((tadpole 1 k)ᶜ).cliqueNum = (k + 2) / 2 := by
  rw [cliqueNum_compl, indepNum_tadpole_one]

theorem cliqueNum_compl_lollipop_one (k : ℕ) : ((lollipop 1 k)ᶜ).cliqueNum = (k + 2) / 2 := by
  rw [cliqueNum_compl, indepNum_lollipop_one]

/-! ### Edge counts and degrees of more complements -/

theorem E_compl_bipartite (m n : ℕ) :
    ((bipartite m n)ᶜ).E = (m + n).choose 2 - m * n := by
  have h := E_compl (bipartite m n)
  rw [E_bipartite, V_bipartite] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_book (n : ℕ) : ((book n)ᶜ).E = (2 + n).choose 2 - (2 * n + 1) := by
  have h := E_compl (book n)
  rw [E_book, V_book] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_cocktailParty (n : ℕ) :
    ((cocktailParty n)ᶜ).E = (2 * n).choose 2 - n * (2 * n - 2) := by
  have h := E_compl (cocktailParty n)
  rw [E_cocktailParty, V_cocktailParty] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_completeMultipartite_replicate (m d : ℕ) :
    ((completeMultipartite (List.replicate m d))ᶜ).E
      = (m * d).choose 2 - m.choose 2 * (d * d) := by
  have h := E_compl (completeMultipartite (List.replicate m d))
  rw [E_completeMultipartite_replicate, V_completeMultipartite_replicate] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_fan (n : ℕ) : ((fan (n + 1))ᶜ).E = (1 + (n + 1)).choose 2 - (2 * n + 1) := by
  have h := E_compl (fan (n + 1))
  rw [E_fan, V_fan] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_friendship (n : ℕ) : ((friendship n)ᶜ).E = (2 * n + 1).choose 2 - 3 * n := by
  have h := E_compl (friendship n)
  rw [E_friendship, V_friendship] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_rook (m n : ℕ) :
    ((rook m n)ᶜ).E = (m * n).choose 2 - (m * n.choose 2 + n * m.choose 2) := by
  have h := E_compl (rook m n)
  rw [E_rook, V_rook] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_star (n : ℕ) : ((star n)ᶜ).E = (1 + n).choose 2 - n := by
  have h := E_compl (star n)
  rw [E_star, V_star] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_triangular (n : ℕ) :
    ((triangular n)ᶜ).E = (n.choose 2).choose 2 - n * (n - 1).choose 2 := by
  have h := E_compl (triangular n)
  rw [E_triangular, V_triangular] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_book (n : ℕ) : maxDeg ((book (n + 1))ᶜ) = n := by
  have h := maxDeg_compl (G := book (n + 1)) (by rw [V_book]; omega)
  rw [V_book, minDeg_book] at h
  omega

theorem minDeg_compl_book (n : ℕ) : minDeg ((book (n + 1))ᶜ) = 0 := by
  have h := minDeg_compl (G := book (n + 1)) (by rw [V_book]; omega)
  rw [V_book, maxDeg_book] at h
  omega

theorem maxDeg_compl_cocktailParty (n : ℕ) : maxDeg ((cocktailParty (n + 1))ᶜ) = 1 := by
  have h := maxDeg_compl (G := cocktailParty (n + 1)) (by rw [V_cocktailParty]; omega)
  rw [V_cocktailParty, minDeg_cocktailParty] at h
  omega

theorem minDeg_compl_cocktailParty (n : ℕ) : minDeg ((cocktailParty (n + 1))ᶜ) = 1 := by
  have h := minDeg_compl (G := cocktailParty (n + 1)) (by rw [V_cocktailParty]; omega)
  rw [V_cocktailParty, maxDeg_cocktailParty] at h
  omega

theorem maxDeg_compl_fan (n : ℕ) : maxDeg ((fan (n + 2))ᶜ) = n := by
  have h := maxDeg_compl (G := fan (n + 2)) (by rw [V_fan]; omega)
  rw [V_fan, minDeg_fan] at h
  omega

theorem minDeg_compl_fan (n : ℕ) : minDeg ((fan (n + 3))ᶜ) = 0 := by
  have h := minDeg_compl (G := fan (n + 3)) (by rw [V_fan]; omega)
  rw [V_fan, maxDeg_fan] at h
  omega

theorem maxDeg_compl_friendship (n : ℕ) : maxDeg ((friendship (n + 1))ᶜ) = 2 * n := by
  have h := maxDeg_compl (G := friendship (n + 1)) (by rw [V_friendship]; omega)
  rw [V_friendship, minDeg_friendship] at h
  omega

theorem minDeg_compl_friendship (n : ℕ) : minDeg ((friendship (n + 1))ᶜ) = 0 := by
  have h := minDeg_compl (G := friendship (n + 1)) (by rw [V_friendship]; omega)
  rw [V_friendship, maxDeg_friendship] at h
  omega

theorem maxDeg_compl_rook (m n : ℕ) : maxDeg ((rook (m + 1) (n + 1))ᶜ) = m * n := by
  have h := maxDeg_compl (G := rook (m + 1) (n + 1)) (by rw [V_rook]; positivity)
  rw [V_rook, minDeg_rook] at h
  have e : (m + 1) * (n + 1) = m * n + m + n + 1 := by ring
  omega

theorem minDeg_compl_rook (m n : ℕ) : minDeg ((rook (m + 1) (n + 1))ᶜ) = m * n := by
  have h := minDeg_compl (G := rook (m + 1) (n + 1)) (by rw [V_rook]; positivity)
  rw [V_rook, maxDeg_rook] at h
  have e : (m + 1) * (n + 1) = m * n + m + n + 1 := by ring
  omega

theorem maxDeg_compl_star (n : ℕ) : maxDeg ((star (n + 1))ᶜ) = n := by
  have h := maxDeg_compl (G := star (n + 1)) (by rw [V_star]; omega)
  rw [V_star, minDeg_star] at h
  omega

theorem minDeg_compl_star (n : ℕ) : minDeg ((star (n + 1))ᶜ) = 0 := by
  have h := minDeg_compl (G := star (n + 1)) (by rw [V_star]; omega)
  rw [V_star, maxDeg_star] at h
  omega

theorem maxDeg_compl_triangular (n : ℕ) :
    maxDeg ((triangular (n + 2))ᶜ) = (n + 2).choose 2 - 2 * n - 1 := by
  have h := maxDeg_compl (G := triangular (n + 2))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
  rw [V_triangular, minDeg_triangular] at h
  omega

theorem minDeg_compl_triangular (n : ℕ) :
    minDeg ((triangular (n + 2))ᶜ) = (n + 2).choose 2 - 2 * n - 1 := by
  have h := minDeg_compl (G := triangular (n + 2))
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
  rw [V_triangular, maxDeg_triangular] at h
  omega

theorem maxDeg_compl_petersen : maxDeg petersenᶜ = 6 := by
  have h := maxDeg_compl (G := petersen) (by rw [V_petersen]; omega)
  rw [V_petersen, minDeg_petersen] at h
  omega

theorem minDeg_compl_petersen : minDeg petersenᶜ = 6 := by
  have h := minDeg_compl (G := petersen) (by rw [V_petersen]; omega)
  rw [V_petersen, maxDeg_petersen] at h
  omega

theorem maxDeg_compl_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    maxDeg ((paley q)ᶜ) = (q - 1) / 2 := by
  have h := maxDeg_compl (G := paley q) (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q))
  rw [V_paley, minDeg_paley q hq] at h
  omega

theorem minDeg_compl_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    minDeg ((paley q)ᶜ) = (q - 1) / 2 := by
  have h := minDeg_compl (G := paley q) (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q))
  rw [V_paley, maxDeg_paley q hq] at h
  omega

theorem maxDeg_compl_completeMultipartite_replicate {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    maxDeg ((completeMultipartite (List.replicate m d))ᶜ) = d - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := maxDeg_compl (G := completeMultipartite (List.replicate (k + 1) d))
    (by rw [V_completeMultipartite_replicate]; positivity)
  rw [V_completeMultipartite_replicate, minDeg_completeMultipartite_replicate hm hd,
    Nat.add_sub_cancel] at h
  have e : (k + 1) * d = k * d + d := by ring
  omega

theorem minDeg_compl_completeMultipartite_replicate {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    minDeg ((completeMultipartite (List.replicate m d))ᶜ) = d - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := minDeg_compl (G := completeMultipartite (List.replicate (k + 1) d))
    (by rw [V_completeMultipartite_replicate]; positivity)
  rw [V_completeMultipartite_replicate, maxDeg_completeMultipartite_replicate hm hd,
    Nat.add_sub_cancel] at h
  have e : (k + 1) * d = k * d + d := by ring
  omega

theorem girth_compl_wheel (n : ℕ) : ((wheel (n + 6))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_wheel]; omega)

theorem girth_compl_crown (n : ℕ) : ((crown (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_crown]; omega)

theorem girth_compl_ladder (n : ℕ) : ((ladder (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_ladder]; omega)

theorem girth_compl_prism_even (m : ℕ) : ((prism (2 * m + 4))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_prism_even]; omega)

theorem girth_compl_prism_odd (m : ℕ) : ((prism (2 * m + 5))ᶜ).girth = 3 := by
  have h : ((prism (2 * m + 5))ᶜ).cliqueNum = 2 * m + 4 := by
    rw [cliqueNum_compl, show 2 * m + 5 = 2 * (m + 1) + 3 from by omega, indepNum_prism_odd]
    omega
  exact girth_eq_three_of_cliqueNum (by omega)

theorem girth_compl_doubleStar (m n : ℕ) : ((doubleStar (m + 2) (n + 1))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl_doubleStar]; omega)

theorem girth_compl_hypercube (n : ℕ) : ((hypercube (n + 3))ᶜ).girth = 3 := by
  have h2 : 2 ^ 2 ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_compl, indepNum_hypercube]
  norm_num at h2 ⊢
  omega

theorem girth_compl_rook (m n : ℕ) : ((rook (m + 3) (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_rook]; omega)

theorem girth_compl_fan (n : ℕ) : ((fan (n + 5))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl_fan]; omega)

theorem girth_compl_friendship (n : ℕ) : ((friendship (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl_friendship]; omega)

theorem girth_compl_book (n : ℕ) : ((book (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_book]; omega)

theorem girth_compl_circulant_one (n : ℕ) : ((circulant (n + 6) [1])ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_circulant_one]; omega)

theorem girth_compl_spider_singleton (k : ℕ) : ((spider [k + 4])ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl_spider_singleton]; omega)

theorem girth_compl_thetaGraph_singleton (k : ℕ) : ((thetaGraph [k + 3])ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_thetaGraph_singleton]; omega)

theorem girth_compl_tadpole_zero (m : ℕ) : ((tadpole (m + 6) 0)ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_tadpole_zero]; omega)

theorem girth_compl_cyclePendant_replicate_zero (m j : ℕ) :
    ((cyclePendant (m + 6) (List.replicate j 0))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_cyclePendant_replicate_zero]; omega)

theorem coverNum_compl_star (n : ℕ) : ((star (n + 1))ᶜ).coverNum = n := by
  have h := coverNum_compl_add_cliqueNum (star (n + 1))
  rw [cliqueNum_star, V_star] at h
  omega

theorem coverNum_compl_wheel (n : ℕ) : ((wheel (n + 4))ᶜ).coverNum = n + 2 := by
  have h := coverNum_compl_add_cliqueNum (wheel (n + 4))
  rw [cliqueNum_wheel, V_wheel] at h
  omega

theorem coverNum_compl_fan (n : ℕ) : ((fan (n + 2))ᶜ).coverNum = n := by
  have h := coverNum_compl_add_cliqueNum (fan (n + 2))
  rw [cliqueNum_fan, V_fan] at h
  omega

theorem coverNum_compl_book (n : ℕ) : ((book n)ᶜ).coverNum = n - min n 1 := by
  have h := coverNum_compl_add_cliqueNum (book n)
  rw [cliqueNum_book, V_book] at h
  omega

theorem coverNum_compl_crown (n : ℕ) : ((crown (n + 2))ᶜ).coverNum = 2 * n + 2 := by
  have h := coverNum_compl_add_cliqueNum (crown (n + 2))
  rw [cliqueNum_crown, V_crown] at h
  omega

theorem coverNum_compl_ladder (n : ℕ) : ((ladder (n + 2))ᶜ).coverNum = 2 * n + 2 := by
  have h := coverNum_compl_add_cliqueNum (ladder (n + 2))
  rw [cliqueNum_ladder, V_ladder] at h
  omega

theorem coverNum_compl_prism (n : ℕ) : ((prism (n + 4))ᶜ).coverNum = 2 * n + 6 := by
  have h := coverNum_compl_add_cliqueNum (prism (n + 4))
  rw [cliqueNum_prism, V_prism] at h
  omega

theorem coverNum_compl_prism_three : ((prism 3)ᶜ).coverNum = 3 := by
  have h := coverNum_compl_add_cliqueNum (prism 3)
  rw [cliqueNum_prism_three, V_prism] at h
  omega

theorem coverNum_compl_cocktailParty (n : ℕ) : ((cocktailParty n)ᶜ).coverNum = n := by
  have h := coverNum_compl_add_cliqueNum (cocktailParty n)
  rw [cliqueNum_cocktailParty, V_cocktailParty] at h
  omega

theorem coverNum_compl_doubleStar (m n : ℕ) : ((doubleStar m n)ᶜ).coverNum = m + n := by
  have h := coverNum_compl_add_cliqueNum (doubleStar m n)
  rw [cliqueNum_doubleStar, V_doubleStar] at h
  omega

theorem coverNum_compl_friendship (n : ℕ) : ((friendship (n + 1))ᶜ).coverNum = 2 * n := by
  have h := coverNum_compl_add_cliqueNum (friendship (n + 1))
  rw [cliqueNum_friendship, V_friendship] at h
  omega

theorem coverNum_compl_grotzsch : grotzschᶜ.coverNum = 9 := by
  have h := coverNum_compl_add_cliqueNum grotzsch
  rw [cliqueNum_grotzsch, V_grotzsch] at h
  omega

@[simp] theorem coverNum_compl_petersen : petersenᶜ.coverNum = 8 := by
  have h := coverNum_compl_add_cliqueNum petersen
  rw [cliqueNum_petersen, V_petersen] at h
  omega

theorem coverNum_compl_hypercube (n : ℕ) : ((hypercube (n + 1))ᶜ).coverNum = 2 ^ (n + 1) - 2 := by
  have h := coverNum_compl_add_cliqueNum (hypercube (n + 1))
  rw [cliqueNum_hypercube, V_hypercube] at h
  exact Nat.eq_sub_of_add_eq h

theorem coverNum_compl_lollipop (m k : ℕ) : ((lollipop (m + 2) k)ᶜ).coverNum = k := by
  have h := coverNum_compl_add_cliqueNum (lollipop (m + 2) k)
  rw [cliqueNum_lollipop, V_lollipop] at h
  omega

theorem coverNum_compl_lollipop_one (k : ℕ) : ((lollipop 1 (k + 1))ᶜ).coverNum = k := by
  have h := coverNum_compl_add_cliqueNum (lollipop 1 (k + 1))
  rw [cliqueNum_lollipop_one, V_lollipop] at h
  omega

theorem coverNum_compl_tadpole (m k : ℕ) : ((tadpole (m + 4) k)ᶜ).coverNum = m + k + 2 := by
  have h := coverNum_compl_add_cliqueNum (tadpole (m + 4) k)
  rw [cliqueNum_tadpole, V_tadpole] at h
  omega

theorem coverNum_compl_tadpole_one (k : ℕ) : ((tadpole 1 (k + 1))ᶜ).coverNum = k := by
  have h := coverNum_compl_add_cliqueNum (tadpole 1 (k + 1))
  rw [cliqueNum_tadpole_one, V_tadpole] at h
  omega

theorem coverNum_compl_spider (legs : List ℕ) (hs : 0 < legs.sum) :
    ((spider legs)ᶜ).coverNum = legs.sum - 1 := by
  have h := coverNum_compl_add_cliqueNum (spider legs)
  rw [cliqueNum_spider legs hs, V_spider] at h
  omega

theorem coverNum_compl_thetaGraph_singleton (k : ℕ) :
    ((thetaGraph [k])ᶜ).coverNum = k := by
  have h := coverNum_compl_add_cliqueNum (thetaGraph [k])
  rw [cliqueNum_thetaGraph_singleton, V_thetaGraph, List.sum_singleton] at h
  omega

theorem coverNum_compl_circulant_one (n : ℕ) : ((circulant (n + 4) [1])ᶜ).coverNum = n + 2 := by
  have h := coverNum_compl_add_cliqueNum (circulant (n + 4) [1])
  rw [cliqueNum_circulant_one, V_circulant] at h
  omega

theorem coverNum_compl_circulant_nil (n : ℕ) : ((circulant n [])ᶜ).coverNum = n - min n 1 := by
  have h := coverNum_compl_add_cliqueNum (circulant n [])
  rw [cliqueNum_circulant_nil, V_circulant] at h
  omega

theorem coverNum_compl_cyclePendant_replicate_zero (m j : ℕ) :
    ((cyclePendant (m + 4) (List.replicate j 0))ᶜ).coverNum = m + 2 := by
  rw [cyclePendant_replicate_zero, coverNum_compl_cycle]

theorem coverNum_compl_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ((rook m n)ᶜ).coverNum = m * n - max m n := by
  have h := coverNum_compl_add_cliqueNum (rook m n)
  rw [cliqueNum_rook hm hn, V_rook] at h
  omega

theorem coverNum_compl_turan {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    ((turan n r)ᶜ).coverNum = n - r := by
  have h := coverNum_compl_add_cliqueNum (turan n r)
  rw [cliqueNum_turan hr hrn, V_turan] at h
  omega

theorem coverNum_compl_grid (m n : ℕ) :
    ((path (m + 2) □g path (n + 2))ᶜ).coverNum = (m + 2) * (n + 2) - 2 := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) □g path (n + 2))
  rw [cliqueNum_grid, V_cartesianProduct, V_path, V_path] at h
  omega

theorem coverNum_compl_king (m n : ℕ) :
    ((path (m + 2) ⊠g path (n + 2))ᶜ).coverNum = (m + 2) * (n + 2) - 4 := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ⊠g path (n + 2))
  rw [cliqueNum_strongProduct, cliqueNum_path, cliqueNum_path, V_strongProduct, V_path, V_path] at h
  omega

theorem coverNum_compl_lineGraph_petersen : ((lineGraph petersen)ᶜ).coverNum = 12 := by
  have h := coverNum_compl_add_cliqueNum (lineGraph petersen)
  rw [cliqueNum_lineGraph_petersen, V_lineGraph, E_petersen] at h
  omega

theorem coverNum_compl_lineGraph_hypercube (n : ℕ) :
    ((lineGraph (hypercube (n + 3)))ᶜ).coverNum = (hypercube (n + 3)).E - (n + 3) := by
  have h := coverNum_compl_add_cliqueNum (lineGraph (hypercube (n + 3)))
  rw [cliqueNum_lineGraph_hypercube, V_lineGraph] at h
  omega

end IsoGraph
