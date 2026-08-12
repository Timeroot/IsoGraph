import IsoGraph.Values.Identities.Brackets

/-!
# Complements, and the graphs built from two named families

The complement of each named family, and then the graphs built by putting two of them together:
the grid, the torus, the cylinder and the king graph, the products, joins and disjoint unions of
two cycles, two paths or two complete graphs — and the complements of all of those in turn.

Complementation is where the columns interact: the chromatic number of a complement is the clique
cover number, its clique number is the independence number, its edge count is the deficit.  Those
four sections at the end are what make the rest of the complement rows follow by `simp`.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ### Complements of the named families

Cliques and independent sets swap under complementation, as do the chromatic number and the
clique cover number, and the automorphism group is unchanged.  Together with the degree and edge
identities that gives a complement column for every family whose four counting invariants are
known, even when the complement itself has no name.
-/

theorem chromNum_compl_cycle (n : ℕ) : ((cycle (n + 4))ᶜ).chromNum = (n + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_cycle]

theorem maxDeg_compl_cycle (n : ℕ) : maxDeg ((cycle (n + 3))ᶜ) = n := by
  have h := maxDeg_compl (G := cycle (n + 3)) (by rw [V_cycle]; omega)
  rw [V_cycle, minDeg_cycle] at h
  omega

theorem minDeg_compl_cycle (n : ℕ) : minDeg ((cycle (n + 3))ᶜ) = n := by
  have h := minDeg_compl (G := cycle (n + 3)) (by rw [V_cycle]; omega)
  rw [V_cycle, maxDeg_cycle] at h
  omega

theorem E_compl_cycle (n : ℕ) : ((cycle (n + 3))ᶜ).E = (n + 3).choose 2 - (n + 3) := by
  have h := E_compl (cycle (n + 3))
  rw [E_cycle, V_cycle] at h
  omega

theorem two_mul_le_autCount_compl_cycle (n : ℕ) :
    2 * (n + 3) ≤ ((cycle (n + 3))ᶜ).autCount := by
  rw [autCount_compl]
  exact two_mul_le_autCount_cycle n

theorem chromNum_compl_path (n : ℕ) : ((path n)ᶜ).chromNum = (n + 1) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_path]

theorem maxDeg_compl_path (n : ℕ) : maxDeg ((path (n + 3))ᶜ) = n + 1 := by
  have h := maxDeg_compl (G := path (n + 3)) (by rw [V_path]; omega)
  have h2 : minDeg (path (n + 3)) = 1 := by
    rw [show n + 3 = n + 1 + 2 from by ring, minDeg_path]
  rw [V_path, h2] at h
  omega

theorem minDeg_compl_path (n : ℕ) : minDeg ((path (n + 3))ᶜ) = n := by
  have h := minDeg_compl (G := path (n + 3)) (by rw [V_path]; omega)
  rw [V_path, maxDeg_path] at h
  omega

theorem E_compl_path (n : ℕ) : ((path (n + 1))ᶜ).E = (n + 1).choose 2 - n := by
  have h := E_compl (path (n + 1))
  rw [E_path, V_path] at h
  omega

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

/-! ### Complements of the Mycielskian, the Grötzsch graph and the odd folded cubes -/

theorem indepNum_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    ((mycielskian G)ᶜ).indepNum = max G.cliqueNum 2 := by
  rw [indepNum_compl, cliqueNum_mycielskian G hV]

theorem chromNum_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) (hc : G.cliqueNum ≤ 2)
    (hm : 2 * G.matchNum = G.V) : ((mycielskian G)ᶜ).chromNum = G.V + 1 := by
  rw [chromNum_compl, cliqueCoverNum_mycielskian G hV hc hm]

theorem cliqueNum_compl_mycielskian_le (G : IsoGraph) (hV : 0 < G.V) :
    ((mycielskian G)ᶜ).cliqueNum ≤ G.V + G.indepNum := by
  rw [cliqueNum_compl]
  exact indepNum_mycielskian_le G hV

theorem maxDeg_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    maxDeg ((mycielskian G)ᶜ) = 2 * G.V - min (min (2 * G.minDeg) (G.minDeg + 1)) G.V := by
  have h := maxDeg_compl (G := mycielskian G) (by rw [V_mycielskian]; omega)
  rw [V_mycielskian, minDeg_mycielskian G hV] at h
  omega

theorem minDeg_compl_mycielskian (G : IsoGraph) :
    minDeg ((mycielskian G)ᶜ) = 2 * G.V - max (2 * maxDeg G) G.V := by
  have h := minDeg_compl (G := mycielskian G) (by rw [V_mycielskian]; omega)
  rw [V_mycielskian, maxDeg_mycielskian G] at h
  omega

theorem E_compl_mycielskian (G : IsoGraph) :
    ((mycielskian G)ᶜ).E = (2 * G.V + 1).choose 2 - (3 * G.E + G.V) := by
  have h := E_compl (mycielskian G)
  rw [E_mycielskian, V_mycielskian] at h
  omega

theorem indepNum_compl_grotzsch : (grotzschᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_grotzsch]

theorem chromNum_compl_grotzsch : (grotzschᶜ).chromNum = 6 := by
  rw [chromNum_compl, cliqueCoverNum_grotzsch]

@[simp] theorem cliqueCoverNum_compl_grotzsch : (grotzschᶜ).cliqueCoverNum = 4 := by
  rw [cliqueCoverNum_compl, chromNum_grotzsch]

theorem cliqueNum_compl_grotzsch_le : (grotzschᶜ).cliqueNum ≤ 6 := by
  rw [cliqueNum_compl]
  exact indepNum_grotzsch_le

theorem maxDeg_compl_grotzsch : maxDeg (grotzschᶜ) = 7 := by
  have h := maxDeg_compl (G := grotzsch) (by rw [V_grotzsch]; omega)
  rw [V_grotzsch, minDeg_grotzsch] at h
  omega

theorem minDeg_compl_grotzsch : minDeg (grotzschᶜ) = 5 := by
  have h := minDeg_compl (G := grotzsch) (by rw [V_grotzsch]; omega)
  rw [V_grotzsch, maxDeg_grotzsch] at h
  omega

theorem E_compl_grotzsch : (grotzschᶜ).E = 35 := by
  have h := E_compl grotzsch
  rw [E_grotzsch, V_grotzsch, show (11 : ℕ).choose 2 = 55 from rfl] at h
  omega

theorem cliqueNum_compl_foldedCube_odd (m : ℕ) :
    ((foldedCube (2 * m + 1))ᶜ).cliqueNum = 2 ^ (2 * m) := by
  rw [cliqueNum_compl, indepNum_foldedCube_odd]

theorem cliqueCoverNum_compl_foldedCube_odd {n : ℕ} (hn : n % 2 = 1) :
    ((foldedCube n)ᶜ).cliqueCoverNum = 2 := by
  rw [cliqueCoverNum_compl, chromNum_foldedCube_odd hn]

/-! ### Complements of line graphs -/

theorem maxDeg_compl_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    maxDeg ((lineGraph G)ᶜ) = G.E - 1 - (2 * k - 2) := by
  have hd := maxDeg_compl (G := lineGraph G) (by rwa [V_lineGraph])
  rw [V_lineGraph, minDeg_lineGraph hE h] at hd
  omega

theorem minDeg_compl_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    minDeg ((lineGraph G)ᶜ) = G.E - 1 - (2 * k - 2) := by
  have hd := minDeg_compl (G := lineGraph G) (by rwa [V_lineGraph])
  rw [V_lineGraph, maxDeg_lineGraph hE h] at hd
  omega

theorem E_compl_lineGraph (G : IsoGraph) :
    ((lineGraph G)ᶜ).E = G.E.choose 2 - ((degSequence G).map fun d ↦ d.choose 2).sum := by
  have hd := E_compl (lineGraph G)
  rw [E_lineGraph, V_lineGraph] at hd
  omega

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

theorem E_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 3) □g cycle (n + 3)).E = 2 * ((m + 3) * (n + 3)) := by
  rw [E_cartesianProduct, E_cycle, E_cycle, V_cycle, V_cycle]
  ring

theorem cliqueNum_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 4) □g cycle (n + 4)).cliqueNum = 2 := by
  have h := cliqueNum_cartesianProduct (G := cycle (m + 4)) (H := cycle (n + 4))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

theorem maxDeg_cartesianProduct_cycle (m n : ℕ) :
    maxDeg (cycle (m + 3) □g cycle (n + 3)) = 4 := by
  have h := maxDeg_cartesianProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_cycle, maxDeg_cycle] at h
  omega

theorem minDeg_cartesianProduct_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) □g cycle (n + 3)) = 4 := by
  have h := minDeg_cartesianProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle] at h
  omega

@[simp] theorem isVertexTransitive_cartesianProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m □g cycle n) :=
  (isVertexTransitive_cycle m).cartesianProduct (isVertexTransitive_cycle n)

theorem radius_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 1) □g cycle (n + 1)).radius = (m + 1) / 2 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_cycle m) (isConnected_cycle n), radius_cycle,
    radius_cycle]

/-! ### The cylinder and the king graph -/

theorem cliqueNum_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 4) □g path (n + 2)).cliqueNum = 2 := by
  have h := cliqueNum_cartesianProduct (G := cycle (m + 4)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_cycle, cliqueNum_path] at h
  omega

theorem maxDeg_cartesianProduct_cycle_path (m n : ℕ) :
    maxDeg (cycle (m + 3) □g path (n + 3)) = 4 := by
  have h := maxDeg_cartesianProduct (G := cycle (m + 3)) (H := path (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [maxDeg_cycle, maxDeg_path] at h
  omega

theorem minDeg_cartesianProduct_cycle_path (m n : ℕ) :
    minDeg (cycle (m + 3) □g path (n + 2)) = 3 := by
  have h := minDeg_cartesianProduct (G := cycle (m + 3)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [minDeg_cycle, minDeg_path] at h
  omega

theorem diameter_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 1) □g path (n + 1)).diameter = (m + 1) / 2 + n := by
  rw [diameter_cartesianProduct (isConnected_cycle m) (isConnected_path n), diameter_cycle,
    diameter_path]

theorem radius_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 1) □g path (n + 1)).radius = (m + 1) / 2 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_cycle m) (isConnected_path n), radius_cycle,
    radius_path]

/-! ### The chromatic index of a grid, a cylinder and a torus -/

/-- **`χ'(G □ H) ≤ χ'(G) + χ'(H)`.**  An edge of a product moves exactly one coordinate, so the
two factors' edge colourings can be laid side by side.  Each factor needs an edge, since a
colouring with no colours has nowhere to send the values it is never asked for. -/
theorem edgeChromNum_cartesianProduct_le {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    (G □g H).edgeChromNum ≤ G.edgeChromNum + H.edgeChromNum := by
  have hG' : 0 < G.edgeChromNum := Nat.pos_of_ne_zero fun h ↦ by
    rw [edgeChromNum_eq_zero_iff] at h; omega
  have hH' : 0 < H.edgeChromNum := Nat.pos_of_ne_zero fun h ↦ by
    rw [edgeChromNum_eq_zero_iff] at h; omega
  simp only [edgeChromNum_eq] at hG' hH' ⊢
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, lineGraph_mk, lineGraph_mk, lineGraph_mk, chromNum_mk, chromNum_mk,
    chromNum_mk] at *
  exact CGraph.chromNum_lineGraph_cartesianProduct_le_add hG' hH'

/-- **The chromatic index of a grid is four**, two colours for each direction. -/
theorem edgeChromNum_grid (m n : ℕ) : (path (m + 3) □g path (n + 3)).edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := path (m + 3)) (H := path (n + 3))
      (by rw [show m + 3 = (m + 2) + 1 from rfl, E_path]; omega)
      (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
    rwa [edgeChromNum_path, edgeChromNum_path] at h
  · rw [← maxDeg_grid m n]
    exact maxDeg_le_edgeChromNum _

/-- **The chromatic index of a cylinder over an even cycle is four.** -/
theorem edgeChromNum_cartesianProduct_cycle_even_path (m n : ℕ) :
    (cycle (2 * m + 4) □g path (n + 3)).edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := path (n + 3))
      (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega)
      (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
    rwa [edgeChromNum_cycle_even, edgeChromNum_path] at h
  · have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g path (n + 3))
    rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, maxDeg_cartesianProduct_cycle_path] at h

/-- **The chromatic index of a torus with both sides even is four.** -/
theorem edgeChromNum_cartesianProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) □g cycle (2 * n + 4)).edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := cycle (2 * n + 4))
      (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega)
      (by rw [show 2 * n + 4 = (2 * n + 1) + 3 by omega, E_cycle]; omega)
    rwa [edgeChromNum_cycle_even, edgeChromNum_cycle_even] at h
  · have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g cycle (2 * n + 4))
    rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, show 2 * n + 4 = (2 * n + 1) + 3 by omega,
      maxDeg_cartesianProduct_cycle] at h

/-! An odd cycle costs a third colour, so the composition only brackets the remaining cases.  A
cylinder or a torus with an odd side is still `4`-regular where it is regular at all, and Vizing's
theorem — which is not in the library — would pin every case with an even side down to `4`. -/

/-- A cylinder over an odd cycle needs at least four colours and at most five. -/
theorem le_edgeChromNum_cartesianProduct_cycle_odd_path (m n : ℕ) :
    4 ≤ (cycle (2 * m + 3) □g path (n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (cycle (2 * m + 3) □g path (n + 3))
  rwa [maxDeg_cartesianProduct_cycle_path] at h

theorem edgeChromNum_cartesianProduct_cycle_odd_path_le (m n : ℕ) :
    (cycle (2 * m + 3) □g path (n + 3)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 3)) (H := path (n + 3))
    (by rw [E_cycle]; omega) (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
  rwa [edgeChromNum_cycle_odd, edgeChromNum_path] at h

/-- A torus with one even side and one odd side needs at least four colours and at most five. -/
theorem le_edgeChromNum_cartesianProduct_cycle_even_odd (m n : ℕ) :
    4 ≤ (cycle (2 * m + 4) □g cycle (2 * n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g cycle (2 * n + 3))
  rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, maxDeg_cartesianProduct_cycle] at h

theorem edgeChromNum_cartesianProduct_cycle_even_odd_le (m n : ℕ) :
    (cycle (2 * m + 4) □g cycle (2 * n + 3)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := cycle (2 * n + 3))
    (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega)
    (by rw [E_cycle]; omega)
  rwa [edgeChromNum_cycle_even, edgeChromNum_cycle_odd] at h

/-- **A torus with two odd sides needs a fifth colour**: it is `4`-regular on an odd number of
vertices, so no colour class can be a perfect matching. -/
theorem le_edgeChromNum_cartesianProduct_cycle_odd (m n : ℕ) :
    5 ≤ (cycle (2 * m + 3) □g cycle (2 * n + 3)).edgeChromNum := by
  have hreg : (cycle (2 * m + 3) □g cycle (2 * n + 3)).IsRegularWith 4 :=
    (isRegularWith_cycle (2 * m)).cartesianProduct (isRegularWith_cycle (2 * n))
  have hodd : (cycle (2 * m + 3) □g cycle (2 * n + 3)).V % 2 = 1 := by
    have h1 : (2 * m + 3) % 2 = 1 := by omega
    have h2 : (2 * n + 3) % 2 = 1 := by omega
    rw [V_cartesianProduct, V_cycle, V_cycle, Nat.mul_mod, h1, h2]
  have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd hreg (by omega) hodd
  rwa [maxDeg_cartesianProduct_cycle] at h

theorem edgeChromNum_cartesianProduct_cycle_odd_le (m n : ℕ) :
    (cycle (2 * m + 3) □g cycle (2 * n + 3)).edgeChromNum ≤ 6 := by
  have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 3)) (H := cycle (2 * n + 3))
    (by rw [E_cycle]; omega) (by rw [E_cycle]; omega)
  rwa [edgeChromNum_cycle_odd, edgeChromNum_cycle_odd] at h

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

/-! ### The tensor and strong products of two cycles -/

theorem maxDeg_tensorProduct_cycle (m n : ℕ) :
    maxDeg (cycle (m + 3) ⊗g cycle (n + 3)) = 4 := by
  have h := maxDeg_tensorProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_cycle, maxDeg_cycle] at h
  omega

theorem minDeg_tensorProduct_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) ⊗g cycle (n + 3)) = 4 := by
  have h := minDeg_tensorProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle] at h
  omega

@[simp] theorem isVertexTransitive_tensorProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m ⊗g cycle n) :=
  (isVertexTransitive_cycle m).tensorProduct (isVertexTransitive_cycle n)

theorem maxDeg_strongProduct_cycle (m n : ℕ) :
    maxDeg (cycle (m + 3) ⊠g cycle (n + 3)) = 8 := by
  have h := maxDeg_strongProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_cycle, maxDeg_cycle] at h
  omega

theorem minDeg_strongProduct_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) ⊠g cycle (n + 3)) = 8 := by
  have h := minDeg_strongProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle] at h
  omega

@[simp] theorem isConnected_strongProduct_cycle (m n : ℕ) :
    IsConnected (cycle (m + 1) ⊠g cycle (n + 1)) :=
  isConnected_strongProduct (isConnected_cycle m) (isConnected_cycle n)

@[simp] theorem girth_strongProduct_cycle (m n : ℕ) :
    (cycle (m + 3) ⊠g cycle (n + 3)).girth = 3 :=
  girth_strongProduct (by rw [E_cycle]; omega) (by rw [E_cycle]; omega)

@[simp] theorem isVertexTransitive_strongProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m ⊠g cycle n) :=
  (isVertexTransitive_cycle m).strongProduct (isVertexTransitive_cycle n)

/-! ### The lexicographic product of two cycles -/

theorem maxDeg_lexProduct_cycle (m n : ℕ) :
    maxDeg (cycle (m + 3) ·g cycle (n + 3)) = 2 * (n + 3) + 2 := by
  have h := maxDeg_lexProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_cycle, maxDeg_cycle, V_cycle] at h
  omega

theorem minDeg_lexProduct_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) ·g cycle (n + 3)) = 2 * (n + 3) + 2 := by
  have h := minDeg_lexProduct (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle, V_cycle] at h
  omega

@[simp] theorem isConnected_lexProduct_cycle (m n : ℕ) :
    IsConnected (cycle (m + 1) ·g cycle (n + 1)) :=
  isConnected_lexProduct (isConnected_cycle m) (isConnected_cycle n)

@[simp] theorem girth_lexProduct_cycle (m n : ℕ) :
    (cycle (m + 3) ·g cycle (n + 3)).girth = 3 :=
  girth_lexProduct (by rw [E_cycle]; omega) (by rw [E_cycle]; omega)

@[simp] theorem isVertexTransitive_lexProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m ·g cycle n) :=
  (isVertexTransitive_cycle m).lexProduct (isVertexTransitive_cycle n)

/-! ### The tensor and lexicographic products of two paths -/

theorem maxDeg_tensorProduct_path (m n : ℕ) :
    maxDeg (path (m + 3) ⊗g path (n + 3)) = 4 := by
  have h := maxDeg_tensorProduct (G := path (m + 3)) (H := path (n + 3))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [maxDeg_path, maxDeg_path] at h
  omega

theorem minDeg_tensorProduct_path (m n : ℕ) :
    minDeg (path (m + 2) ⊗g path (n + 2)) = 1 := by
  have h := minDeg_tensorProduct (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path] at h
  omega

@[simp] theorem isBipartite_tensorProduct_path (m n : ℕ) :
    IsBipartite (path m ⊗g path n) :=
  isBipartite_tensorProduct_left (isBipartite_path m)

@[simp] theorem chromNum_tensorProduct_path (m n : ℕ) :
    (path (m + 2) ⊗g path (n + 2)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_tensorProduct_path _ _,
    by rw [E_tensorProduct, E_path, E_path]; positivity⟩

theorem maxDeg_lexProduct_path (m n : ℕ) :
    maxDeg (path (m + 3) ·g path (n + 3)) = 2 * (n + 3) + 2 := by
  have h := maxDeg_lexProduct (G := path (m + 3)) (H := path (n + 3))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [maxDeg_path, maxDeg_path, V_path] at h
  omega

theorem minDeg_lexProduct_path (m n : ℕ) :
    minDeg (path (m + 2) ·g path (n + 2)) = n + 3 := by
  have h := minDeg_lexProduct (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path, V_path] at h
  omega

@[simp] theorem isConnected_lexProduct_path (m n : ℕ) :
    IsConnected (path (m + 1) ·g path (n + 1)) :=
  isConnected_lexProduct (isConnected_path m) (isConnected_path n)

@[simp] theorem girth_lexProduct_path (m n : ℕ) :
    (path (m + 2) ·g path (n + 2)).girth = 3 :=
  girth_lexProduct (by rw [E_path]; omega) (by rw [E_path]; omega)

theorem not_isBipartite_lexProduct_path (m n : ℕ) :
    ¬ IsBipartite (path (m + 2) ·g path (n + 2)) :=
  not_isBipartite_lexProduct (by rw [E_path]; omega) (by rw [E_path]; omega)

theorem chromNum_lexProduct_path (m n : ℕ) :
    (path (m + 2) ·g path (n + 2)).chromNum = 4 := by
  have h1 := chromNum_lexProduct_le (path (m + 2)) (path (n + 2))
  have h2 := cliqueNum_le_chromNum (path (m + 2) ·g path (n + 2))
  rw [chromNum_path, chromNum_path] at h1
  rw [cliqueNum_lexProduct, cliqueNum_path, cliqueNum_path] at h2
  omega

/-! ### The tensor, strong and lexicographic products of two complete graphs -/

theorem maxDeg_tensorProduct_complete (m n : ℕ) :
    maxDeg (complete (m + 1) ⊗g complete (n + 1)) = m * n := by
  have h := maxDeg_tensorProduct (G := complete (m + 1)) (H := complete (n + 1))
    (by rw [V_complete]; omega) (by rw [V_complete]; omega)
  rw [maxDeg_complete, maxDeg_complete] at h
  simpa using h

theorem minDeg_tensorProduct_complete (m n : ℕ) :
    minDeg (complete (m + 1) ⊗g complete (n + 1)) = m * n := by
  have h := minDeg_tensorProduct (G := complete (m + 1)) (H := complete (n + 1))
    (by rw [V_complete]; omega) (by rw [V_complete]; omega)
  rw [minDeg_complete, minDeg_complete] at h
  simpa using h

@[simp] theorem girth_tensorProduct_complete (m n : ℕ) :
    (complete (m + 3) ⊗g complete (n + 3)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_complete]; omega)

theorem isConnected_tensorProduct_complete (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g complete (n + 2)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_complete (n + 1))
    (not_isBipartite_complete m) (E_complete_pos n)

theorem numComponents_tensorProduct_complete (m n : ℕ) :
    (complete (m + 3) ⊗g complete (n + 2)).numComponents = 1 :=
  numComponents_tensorProduct (isConnected_complete (m + 2)) (isConnected_complete (n + 1))
    (not_isBipartite_complete m) (E_complete_pos n)

@[simp] theorem isVertexTransitive_tensorProduct_complete (m n : ℕ) :
    IsVertexTransitive (complete m ⊗g complete n) :=
  (isVertexTransitive_complete m).tensorProduct (isVertexTransitive_complete n)

theorem E_strongProduct_complete (m n : ℕ) :
    (complete m ⊠g complete n).E
      = m * n.choose 2 + n * m.choose 2 + 2 * m.choose 2 * n.choose 2 := by
  rw [E_strongProduct, E_complete, E_complete, V_complete, V_complete]

@[simp] theorem girth_strongProduct_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 2)).girth = 3 :=
  girth_strongProduct (E_complete_pos m) (E_complete_pos n)

theorem isConnected_strongProduct_complete (m n : ℕ) :
    IsConnected (complete (m + 1) ⊠g complete (n + 1)) :=
  isConnected_strongProduct (isConnected_complete m) (isConnected_complete n)

theorem E_lexProduct_complete (m n : ℕ) :
    (complete m ·g complete n).E = n * n * m.choose 2 + m * n.choose 2 := by
  rw [E_lexProduct, E_complete, E_complete, V_complete, V_complete]

theorem indepNum_lexProduct_complete (m n : ℕ) :
    (complete (m + 1) ·g complete (n + 1)).indepNum = 1 := by
  have h := indepNum_lexProduct (complete (m + 1)) (complete (n + 1))
  rw [indepNum_complete, indepNum_complete, Nat.min_eq_right (by omega : 1 ≤ m + 1),
    Nat.min_eq_right (by omega : 1 ≤ n + 1)] at h
  omega

@[simp] theorem girth_lexProduct_complete (m n : ℕ) :
    (complete (m + 2) ·g complete (n + 2)).girth = 3 :=
  girth_lexProduct (E_complete_pos m) (E_complete_pos n)

theorem isConnected_lexProduct_complete (m n : ℕ) :
    IsConnected (complete (m + 1) ·g complete (n + 1)) :=
  isConnected_lexProduct (isConnected_complete m) (isConnected_complete n)

/-! ### The join of two cycles -/

theorem maxDeg_join_cycle (m n : ℕ) :
    maxDeg (cycle (m + 3) ∇g cycle (n + 3)) = max (n + 5) (m + 5) := by
  have h := maxDeg_join (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_cycle, maxDeg_cycle, V_cycle, V_cycle] at h
  omega

theorem minDeg_join_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) ∇g cycle (n + 3)) = min (n + 5) (m + 5) := by
  have h := minDeg_join (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle, V_cycle, V_cycle] at h
  omega

@[simp] theorem girth_join_cycle (m n : ℕ) :
    (cycle (m + 4) ∇g cycle (n + 4)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_cycle]; omega)

theorem diameter_join_cycle (m n : ℕ) :
    (cycle (m + 4) ∇g cycle (n + 4)).diameter = 2 := by
  have h : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
    rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 by omega]
  have h2 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 4) * (m + 3) = m * m + 7 * m + 12 := by ring
    omega
  refine diameter_join_left (by rw [V_cycle]; omega) ?_
  rw [E_cycle, V_cycle, h]
  omega

/-! ### The join of two paths -/

theorem maxDeg_join_path (m n : ℕ) :
    maxDeg (path (m + 3) ∇g path (n + 3)) = max (n + 5) (m + 5) := by
  have h := maxDeg_join (G := path (m + 3)) (H := path (n + 3))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [maxDeg_path, maxDeg_path, V_path, V_path] at h
  omega

theorem minDeg_join_path (m n : ℕ) :
    minDeg (path (m + 2) ∇g path (n + 2)) = min (n + 3) (m + 3) := by
  have h := minDeg_join (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path, V_path, V_path] at h
  omega

@[simp] theorem girth_join_path (m n : ℕ) :
    (path (m + 2) ∇g path (n + 2)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_path, cliqueNum_path]; omega)

theorem diameter_join_path (m n : ℕ) :
    (path (m + 3) ∇g path (n + 3)).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_path]; omega) ?_
  rw [E_path, V_path, h]
  omega

/-! ### The disjoint union of two cycles -/

@[simp] theorem minDeg_disjUnion_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) ⊕g cycle (n + 3)) = 2 := by
  have h := minDeg_disjUnion (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle] at h
  omega

theorem not_isConnected_disjUnion_cycle (m n : ℕ) :
    ¬ IsConnected (cycle (m + 1) ⊕g cycle (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)

theorem chromNum_disjUnion_cycle_even_odd (m n : ℕ) :
    (cycle (2 * m + 2) ⊕g cycle (2 * n + 3)).chromNum = 3 := by
  have h := chromNum_disjUnion (cycle (2 * m + 2)) (cycle (2 * n + 3))
  rw [chromNum_cycle_even, chromNum_cycle_odd] at h
  omega

/-! ### The disjoint union of two paths -/

@[simp] theorem minDeg_disjUnion_path (m n : ℕ) :
    minDeg (path (m + 2) ⊕g path (n + 2)) = 1 := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path] at h
  omega

theorem not_isConnected_disjUnion_path (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g path (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_path]; omega)

/-! ### The disjoint union of two complete graphs -/

@[simp] theorem minDeg_disjUnion_complete (m n : ℕ) :
    minDeg (complete (m + 1) ⊕g complete (n + 1)) = min m n := by
  have h := minDeg_disjUnion (G := complete (m + 1)) (H := complete (n + 1))
    (by rw [V_complete]; omega) (by rw [V_complete]; omega)
  rw [minDeg_complete, minDeg_complete] at h
  omega

@[simp] theorem girth_disjUnion_complete (m n : ℕ) :
    (complete (m + 3) ⊕g complete (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_disjUnion, cliqueNum_complete, cliqueNum_complete]; omega)

theorem not_isConnected_disjUnion_complete (m n : ℕ) :
    ¬ IsConnected (complete (m + 1) ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_complete]; omega) (by rw [V_complete]; omega)

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

theorem E_compl_cartesianProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) □g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2 - 2 * ((m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) □g cycle (n + 3))
  rw [E_cartesianProduct_cycle, V_cartesianProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_cartesianProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) □g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := maxDeg_compl (G := cycle (m + 3) □g cycle (n + 3))
    (by rw [V_cartesianProduct, V_cycle, V_cycle]; positivity)
  rw [V_cartesianProduct, V_cycle, V_cycle, minDeg_cartesianProduct_cycle] at h
  omega

theorem minDeg_compl_cartesianProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) □g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := cycle (m + 3) □g cycle (n + 3))
    (by rw [V_cartesianProduct, V_cycle, V_cycle]; positivity)
  rw [V_cartesianProduct, V_cycle, V_cycle, maxDeg_cartesianProduct_cycle] at h
  omega

theorem indepNum_compl_cartesianProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) □g cycle (n + 4))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_cartesianProduct_cycle]

theorem E_compl_cartesianProduct_cycle_path (m n : ℕ) :
    ((cycle (m + 3) □g path (n + 1))ᶜ).E
      = ((m + 3) * (n + 1)).choose 2 - ((m + 3) * n + (n + 1) * (m + 3)) := by
  have h := E_compl (cycle (m + 3) □g path (n + 1))
  rw [E_cartesianProduct, E_cycle, E_path, V_cycle, V_path, V_cartesianProduct, V_cycle,
      V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_cartesianProduct_cycle_path (m n : ℕ) :
    maxDeg ((cycle (m + 3) □g path (n + 2))ᶜ) = (m + 3) * (n + 2) - 4 := by
  have h := maxDeg_compl (G := cycle (m + 3) □g path (n + 2))
    (by rw [V_cartesianProduct, V_cycle, V_path]; positivity)
  rw [V_cartesianProduct, V_cycle, V_path, minDeg_cartesianProduct_cycle_path] at h
  omega

theorem minDeg_compl_cartesianProduct_cycle_path (m n : ℕ) :
    minDeg ((cycle (m + 3) □g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := cycle (m + 3) □g path (n + 3))
    (by rw [V_cartesianProduct, V_cycle, V_path]; positivity)
  rw [V_cartesianProduct, V_cycle, V_path, maxDeg_cartesianProduct_cycle_path] at h
  omega

theorem indepNum_compl_cartesianProduct_cycle_path (m n : ℕ) :
    ((cycle (m + 4) □g path (n + 2))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_cartesianProduct_cycle_path]

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

/-! ### Complements of the tensor, strong and lexicographic products of two cycles -/

theorem E_compl_tensorProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊗g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2 - 2 * (m + 3) * (n + 3) := by
  have h := E_compl (cycle (m + 3) ⊗g cycle (n + 3))
  rw [E_tensorProduct, E_cycle, E_cycle, V_tensorProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_tensorProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ⊗g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := maxDeg_compl (G := cycle (m + 3) ⊗g cycle (n + 3))
    (by rw [V_tensorProduct, V_cycle, V_cycle]; positivity)
  rw [V_tensorProduct, V_cycle, V_cycle, minDeg_tensorProduct_cycle] at h
  omega

theorem minDeg_compl_tensorProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ⊗g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := cycle (m + 3) ⊗g cycle (n + 3))
    (by rw [V_tensorProduct, V_cycle, V_cycle]; positivity)
  rw [V_tensorProduct, V_cycle, V_cycle, maxDeg_tensorProduct_cycle] at h
  omega

theorem E_compl_strongProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊠g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2
          - ((m + 3) * (n + 3) + (n + 3) * (m + 3) + 2 * (m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) ⊠g cycle (n + 3))
  rw [E_strongProduct, E_cycle, E_cycle, V_cycle, V_cycle, V_strongProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_strongProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ⊠g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 9 := by
  have h := maxDeg_compl (G := cycle (m + 3) ⊠g cycle (n + 3))
    (by rw [V_strongProduct, V_cycle, V_cycle]; positivity)
  rw [V_strongProduct, V_cycle, V_cycle, minDeg_strongProduct_cycle] at h
  omega

theorem minDeg_compl_strongProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ⊠g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 9 := by
  have h := minDeg_compl (G := cycle (m + 3) ⊠g cycle (n + 3))
    (by rw [V_strongProduct, V_cycle, V_cycle]; positivity)
  rw [V_strongProduct, V_cycle, V_cycle, maxDeg_strongProduct_cycle] at h
  omega

theorem E_compl_lexProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) ·g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2 - ((n + 3) * (n + 3) * (m + 3) + (m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) ·g cycle (n + 3))
  rw [E_lexProduct, E_cycle, E_cycle, V_cycle, V_cycle, V_lexProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_lexProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ·g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 2 * (n + 3) - 3 := by
  have h := maxDeg_compl (G := cycle (m + 3) ·g cycle (n + 3))
    (by rw [V_lexProduct, V_cycle, V_cycle]; positivity)
  rw [V_lexProduct, V_cycle, V_cycle, minDeg_lexProduct_cycle] at h
  omega

theorem minDeg_compl_lexProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ·g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 2 * (n + 3) - 3 := by
  have h := minDeg_compl (G := cycle (m + 3) ·g cycle (n + 3))
    (by rw [V_lexProduct, V_cycle, V_cycle]; positivity)
  rw [V_lexProduct, V_cycle, V_cycle, maxDeg_lexProduct_cycle] at h
  omega

/-! ### Complements of the products of two paths and of the tensor product of complete graphs -/

theorem E_compl_tensorProduct_path (m n : ℕ) :
    ((path (m + 1) ⊗g path (n + 1))ᶜ).E = ((m + 1) * (n + 1)).choose 2 - 2 * m * n := by
  have h := E_compl (path (m + 1) ⊗g path (n + 1))
  rw [E_tensorProduct, E_path, E_path, V_tensorProduct, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_tensorProduct_path (m n : ℕ) :
    maxDeg ((path (m + 2) ⊗g path (n + 2))ᶜ) = (m + 2) * (n + 2) - 2 := by
  have h := maxDeg_compl (G := path (m + 2) ⊗g path (n + 2))
    (by rw [V_tensorProduct, V_path, V_path]; positivity)
  rw [V_tensorProduct, V_path, V_path, minDeg_tensorProduct_path] at h
  omega

theorem minDeg_compl_tensorProduct_path (m n : ℕ) :
    minDeg ((path (m + 3) ⊗g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := path (m + 3) ⊗g path (n + 3))
    (by rw [V_tensorProduct, V_path, V_path]; positivity)
  rw [V_tensorProduct, V_path, V_path, maxDeg_tensorProduct_path] at h
  omega

theorem E_compl_lexProduct_path (m n : ℕ) :
    ((path (m + 1) ·g path (n + 1))ᶜ).E
      = ((m + 1) * (n + 1)).choose 2 - ((n + 1) * (n + 1) * m + (m + 1) * n) := by
  have h := E_compl (path (m + 1) ·g path (n + 1))
  rw [E_lexProduct, E_path, E_path, V_path, V_path, V_lexProduct, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_lexProduct_path (m n : ℕ) :
    maxDeg ((path (m + 2) ·g path (n + 2))ᶜ) = (m + 2) * (n + 2) - n - 4 := by
  have h := maxDeg_compl (G := path (m + 2) ·g path (n + 2))
    (by rw [V_lexProduct, V_path, V_path]; positivity)
  rw [V_lexProduct, V_path, V_path, minDeg_lexProduct_path] at h
  omega

theorem minDeg_compl_lexProduct_path (m n : ℕ) :
    minDeg ((path (m + 3) ·g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 2 * n - 9 := by
  have h := minDeg_compl (G := path (m + 3) ·g path (n + 3))
    (by rw [V_lexProduct, V_path, V_path]; positivity)
  rw [V_lexProduct, V_path, V_path, maxDeg_lexProduct_path] at h
  omega

theorem E_compl_tensorProduct_complete (m n : ℕ) :
    ((complete m ⊗g complete n)ᶜ).E = (m * n).choose 2 - 2 * m.choose 2 * n.choose 2 := by
  have h := E_compl (complete m ⊗g complete n)
  rw [E_tensorProduct, E_complete, E_complete, V_tensorProduct, V_complete, V_complete] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_tensorProduct_complete (m n : ℕ) :
    maxDeg ((complete (m + 1) ⊗g complete (n + 1))ᶜ) = (m + 1) * (n + 1) - 1 - m * n := by
  have h := maxDeg_compl (G := complete (m + 1) ⊗g complete (n + 1))
    (by rw [V_tensorProduct, V_complete, V_complete]; positivity)
  rw [V_tensorProduct, V_complete, V_complete, minDeg_tensorProduct_complete] at h
  omega

theorem minDeg_compl_tensorProduct_complete (m n : ℕ) :
    minDeg ((complete (m + 1) ⊗g complete (n + 1))ᶜ) = (m + 1) * (n + 1) - 1 - m * n := by
  have h := minDeg_compl (G := complete (m + 1) ⊗g complete (n + 1))
    (by rw [V_tensorProduct, V_complete, V_complete]; positivity)
  rw [V_tensorProduct, V_complete, V_complete, maxDeg_tensorProduct_complete] at h
  omega

/-! ### Complements of disjoint unions and joins of two named families -/

theorem E_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ).E = ((m + 3) + (n + 3)).choose 2 - ((m + 3) + (n + 3)) := by
  have h := E_compl (cycle (m + 3) ⊕g cycle (n + 3))
  rw [E_disjUnion, E_cycle, E_cycle, V_disjUnion, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_disjUnion_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ) = m + n + 3 := by
  have h := maxDeg_compl (G := cycle (m + 3) ⊕g cycle (n + 3))
    (by rw [V_disjUnion, V_cycle, V_cycle]; omega)
  rw [V_disjUnion, V_cycle, V_cycle, minDeg_disjUnion_cycle] at h
  omega

theorem minDeg_compl_disjUnion_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ) = m + n + 3 := by
  have h := minDeg_compl (G := cycle (m + 3) ⊕g cycle (n + 3))
    (by rw [V_disjUnion, V_cycle, V_cycle]; omega)
  rw [V_disjUnion, V_cycle, V_cycle, maxDeg_disjUnion, maxDeg_cycle, maxDeg_cycle, max_self] at h
  omega

theorem E_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 1) ⊕g path (n + 1))ᶜ).E = ((m + 1) + (n + 1)).choose 2 - (m + n) := by
  have h := E_compl (path (m + 1) ⊕g path (n + 1))
  rw [E_disjUnion, E_path, E_path, V_disjUnion, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_disjUnion_path (m n : ℕ) :
    maxDeg ((path (m + 2) ⊕g path (n + 2))ᶜ) = m + n + 2 := by
  have h := maxDeg_compl (G := path (m + 2) ⊕g path (n + 2))
    (by rw [V_disjUnion, V_path, V_path]; omega)
  rw [V_disjUnion, V_path, V_path, minDeg_disjUnion_path] at h
  omega

theorem minDeg_compl_disjUnion_path (m n : ℕ) :
    minDeg ((path (m + 3) ⊕g path (n + 3))ᶜ) = m + n + 3 := by
  have h := minDeg_compl (G := path (m + 3) ⊕g path (n + 3))
    (by rw [V_disjUnion, V_path, V_path]; omega)
  rw [V_disjUnion, V_path, V_path, maxDeg_disjUnion, maxDeg_path, maxDeg_path, max_self] at h
  omega

theorem E_compl_disjUnion_complete (m n : ℕ) :
    ((complete m ⊕g complete n)ᶜ).E = (m + n).choose 2 - (m.choose 2 + n.choose 2) := by
  have h := E_compl (complete m ⊕g complete n)
  rw [E_disjUnion, E_complete, E_complete, V_disjUnion, V_complete, V_complete] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_disjUnion_complete (m n : ℕ) :
    maxDeg ((complete (m + 1) ⊕g complete (n + 1))ᶜ) = m + n + 1 - min m n := by
  have h := maxDeg_compl (G := complete (m + 1) ⊕g complete (n + 1))
    (by rw [V_disjUnion, V_complete, V_complete]; omega)
  rw [V_disjUnion, V_complete, V_complete, minDeg_disjUnion_complete] at h
  omega

theorem minDeg_compl_disjUnion_complete (m n : ℕ) :
    minDeg ((complete (m + 1) ⊕g complete (n + 1))ᶜ) = m + n + 1 - max m n := by
  have h := minDeg_compl (G := complete (m + 1) ⊕g complete (n + 1))
    (by rw [V_disjUnion, V_complete, V_complete]; omega)
  rw [V_disjUnion, V_complete, V_complete, maxDeg_disjUnion, maxDeg_complete, maxDeg_complete] at h
  omega

theorem E_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 3) ∇g cycle (n + 3))ᶜ).E
      = ((m + 3) + (n + 3)).choose 2 - ((m + 3) + (n + 3) + (m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) ∇g cycle (n + 3))
  rw [E_join, E_cycle, E_cycle, V_cycle, V_cycle, V_join, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_join_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ∇g cycle (n + 3))ᶜ) = max m n := by
  have h := maxDeg_compl (G := cycle (m + 3) ∇g cycle (n + 3))
    (by rw [V_join, V_cycle, V_cycle]; omega)
  rw [V_join, V_cycle, V_cycle, minDeg_join_cycle] at h
  omega

theorem minDeg_compl_join_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ∇g cycle (n + 3))ᶜ) = min m n := by
  have h := minDeg_compl (G := cycle (m + 3) ∇g cycle (n + 3))
    (by rw [V_join, V_cycle, V_cycle]; omega)
  rw [V_join, V_cycle, V_cycle, maxDeg_join_cycle] at h
  omega

theorem E_compl_join_path (m n : ℕ) :
    ((path (m + 1) ∇g path (n + 1))ᶜ).E
      = ((m + 1) + (n + 1)).choose 2 - (m + n + (m + 1) * (n + 1)) := by
  have h := E_compl (path (m + 1) ∇g path (n + 1))
  rw [E_join, E_path, E_path, V_path, V_path, V_join, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_join_path (m n : ℕ) :
    maxDeg ((path (m + 2) ∇g path (n + 2))ᶜ) = max m n := by
  have h := maxDeg_compl (G := path (m + 2) ∇g path (n + 2)) (by rw [V_join, V_path, V_path]; omega)
  rw [V_join, V_path, V_path, minDeg_join_path] at h
  omega

theorem minDeg_compl_join_path (m n : ℕ) :
    minDeg ((path (m + 3) ∇g path (n + 3))ᶜ) = min m n := by
  have h := minDeg_compl (G := path (m + 3) ∇g path (n + 3)) (by rw [V_join, V_path, V_path]; omega)
  rw [V_join, V_path, V_path, maxDeg_join_path] at h
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

@[simp] theorem chromNum_compl_petersen : (petersenᶜ).chromNum = 5 := by
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

theorem chromNum_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 4) ∇g cycle (n + 4))ᶜ).chromNum = max ((m + 5) / 2) ((n + 5) / 2) := by
  rw [chromNum_compl, cliqueCoverNum_join, cliqueCoverNum_cycle, cliqueCoverNum_cycle]

theorem chromNum_compl_join_path (m n : ℕ) :
    ((path m ∇g path n)ᶜ).chromNum = max ((m + 1) / 2) ((n + 1) / 2) := by
  rw [chromNum_compl, cliqueCoverNum_join, cliqueCoverNum_path, cliqueCoverNum_path]

theorem chromNum_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊕g cycle (n + 4))ᶜ).chromNum = (m + 5) / 2 + (n + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_disjUnion, cliqueCoverNum_cycle, cliqueCoverNum_cycle]

theorem chromNum_compl_disjUnion_path (m n : ℕ) :
    ((path m ⊕g path n)ᶜ).chromNum = (m + 1) / 2 + (n + 1) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_disjUnion, cliqueCoverNum_path, cliqueCoverNum_path]

theorem cliqueCoverNum_compl_friendship (n : ℕ) :
    ((friendship (n + 1))ᶜ).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_friendship]

@[simp] theorem cliqueCoverNum_compl_petersen : (petersenᶜ).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_petersen]

theorem cliqueCoverNum_compl_triangular_even (m : ℕ) :
    ((triangular (2 * m + 4))ᶜ).cliqueCoverNum = 2 * m + 3 := by
  rw [cliqueCoverNum_compl, chromNum_triangular_even]

theorem cliqueCoverNum_compl_disjUnion_cycle_even_odd (m n : ℕ) :
    ((cycle (2 * m + 2) ⊕g cycle (2 * n + 3))ᶜ).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_disjUnion_cycle_even_odd]

theorem cliqueCoverNum_compl_lexProduct_path (m n : ℕ) :
    ((path (m + 2) ·g path (n + 2))ᶜ).cliqueCoverNum = 4 := by
  rw [cliqueCoverNum_compl, chromNum_lexProduct_path]

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

theorem cliqueNum_compl_lexProduct_complete (m n : ℕ) :
    ((complete (m + 1) ·g complete (n + 1))ᶜ).cliqueNum = 1 := by
  rw [cliqueNum_compl, indepNum_lexProduct_complete]

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

theorem E_compl_lexProduct_complete (m n : ℕ) :
    ((complete m ·g complete n)ᶜ).E
      = (m * n).choose 2 - (n * n * m.choose 2 + m * n.choose 2) := by
  have h := E_compl (complete m ·g complete n)
  rw [E_lexProduct_complete, V_lexProduct, V_complete, V_complete] at h
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

theorem E_compl_strongProduct_complete (m n : ℕ) :
    ((complete m ⊠g complete n)ᶜ).E
      = (m * n).choose 2 - (m * n.choose 2 + n * m.choose 2 + 2 * m.choose 2 * n.choose 2) := by
  have h := E_compl (complete m ⊠g complete n)
  rw [E_strongProduct_complete, V_strongProduct, V_complete, V_complete] at h
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

theorem maxDeg_compl_petersen : maxDeg (petersenᶜ) = 6 := by
  have h := maxDeg_compl (G := petersen) (by rw [V_petersen]; omega)
  rw [V_petersen, minDeg_petersen] at h
  omega

theorem minDeg_compl_petersen : minDeg (petersenᶜ) = 6 := by
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

/-! ### Girth and connectivity of complements -/

theorem girth_compl_cycle (n : ℕ) : ((cycle (n + 6))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_cycle]; omega)

theorem girth_compl_path (n : ℕ) : ((path (n + 5))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_path]; omega)

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

theorem girth_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊕g cycle (n + 4))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_disjUnion, indepNum_cycle, indepNum_cycle]; omega)

theorem girth_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 4) ⊕g path (n + 4))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_disjUnion, indepNum_path, indepNum_path]; omega)

theorem girth_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 6) ∇g cycle (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_join, indepNum_cycle, indepNum_cycle]; omega)

theorem girth_compl_join_path (m n : ℕ) :
    ((path (m + 5) ∇g path n)ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_join, indepNum_path, indepNum_path]; omega)

theorem girth_compl_lineGraph (G : IsoGraph) (h : 3 ≤ G.matchNum) :
    ((lineGraph G)ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_lineGraph]; omega)

theorem diameter_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ).diameter = 2 :=
  diameter_compl_disjUnion (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
    (by rw [E_cycle, E_cycle]; omega)

theorem diameter_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 2) ⊕g path (n + 2))ᶜ).diameter = 2 :=
  diameter_compl_disjUnion (by rw [V_path]; omega) (by rw [V_path]; omega)
    (by rw [E_path, E_path]; omega)

theorem diameter_compl_disjUnion_complete (m n : ℕ) :
    ((complete (m + 2) ⊕g complete (n + 2))ᶜ).diameter = 2 := by
  refine diameter_compl_disjUnion (by rw [V_complete]; omega) (by rw [V_complete]; omega) ?_
  rw [E_complete, E_complete]
  have := Nat.choose_pos (show 2 ≤ m + 2 by omega)
  omega

/-! ### Vertex cover numbers of complements -/

@[simp] theorem coverNum_compl_eq (G : IsoGraph) : Gᶜ.coverNum = G.V - G.cliqueNum := by
  have h := coverNum_compl_add_cliqueNum G
  omega

theorem coverNum_compl_disjUnion (G H : IsoGraph) :
    ((G ⊕g H)ᶜ).coverNum = G.V + H.V - max G.cliqueNum H.cliqueNum := by
  rw [coverNum_compl_eq, V_disjUnion, cliqueNum_disjUnion]

theorem coverNum_compl_join (G H : IsoGraph) :
    ((G ∇g H)ᶜ).coverNum = G.V + H.V - (G.cliqueNum + H.cliqueNum) := by
  rw [coverNum_compl_eq, V_join, cliqueNum_join]

theorem coverNum_compl_strongProduct (G H : IsoGraph) :
    ((G ⊠g H)ᶜ).coverNum = G.V * H.V - G.cliqueNum * H.cliqueNum := by
  rw [coverNum_compl_eq, V_strongProduct, cliqueNum_strongProduct]

theorem coverNum_compl_tensorProduct (G H : IsoGraph) :
    ((G ⊗g H)ᶜ).coverNum = G.V * H.V - min G.cliqueNum H.cliqueNum := by
  rw [coverNum_compl_eq, V_tensorProduct, cliqueNum_tensorProduct]

theorem coverNum_compl_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ((G □g H)ᶜ).coverNum = G.V * H.V - max G.cliqueNum H.cliqueNum := by
  rw [coverNum_compl_eq, V_cartesianProduct, cliqueNum_cartesianProduct hG hH]

theorem coverNum_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    ((mycielskian G)ᶜ).coverNum = 2 * G.V + 1 - max G.cliqueNum 2 := by
  rw [coverNum_compl_eq, V_mycielskian, cliqueNum_mycielskian G hV]

theorem coverNum_compl_lineGraph (G : IsoGraph) (h : 3 ≤ maxDeg G) :
    ((lineGraph G)ᶜ).coverNum = G.E - maxDeg G := by
  rw [coverNum_compl_eq, V_lineGraph, cliqueNum_lineGraph_of_three_le_maxDeg h]

theorem coverNum_compl_empty (n : ℕ) : ((empty n)ᶜ).coverNum = n - min n 1 := by
  have h := coverNum_compl_add_cliqueNum (empty n)
  rw [cliqueNum_empty, V_empty] at h
  omega

theorem coverNum_compl_cycle (n : ℕ) : ((cycle (n + 4))ᶜ).coverNum = n + 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (n + 4))
  rw [cliqueNum_cycle, V_cycle] at h
  omega

theorem coverNum_compl_cycle_three : ((cycle 3)ᶜ).coverNum = 0 := by
  have h := coverNum_compl_add_cliqueNum (cycle 3)
  rw [cliqueNum_cycle_three, V_cycle] at h
  omega

theorem coverNum_compl_path (n : ℕ) : ((path (n + 2))ᶜ).coverNum = n := by
  have h := coverNum_compl_add_cliqueNum (path (n + 2))
  rw [cliqueNum_path, V_path] at h
  omega

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

theorem coverNum_compl_grotzsch : (grotzschᶜ).coverNum = 9 := by
  have h := coverNum_compl_add_cliqueNum grotzsch
  rw [cliqueNum_grotzsch, V_grotzsch] at h
  omega

@[simp] theorem coverNum_compl_petersen : (petersenᶜ).coverNum = 8 := by
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

theorem coverNum_compl_cartesianProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) □g cycle (n + 4))ᶜ).coverNum = (m + 4) * (n + 4) - 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) □g cycle (n + 4))
  rw [cliqueNum_cartesianProduct_cycle, V_cartesianProduct, V_cycle, V_cycle] at h
  omega

theorem coverNum_compl_cartesianProduct_cycle_path (m n : ℕ) :
    ((cycle (m + 4) □g path (n + 2))ᶜ).coverNum = (m + 4) * (n + 2) - 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) □g path (n + 2))
  rw [cliqueNum_cartesianProduct_cycle_path, V_cartesianProduct, V_cycle, V_path] at h
  omega

theorem coverNum_compl_tensorProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊗g cycle (n + 4))ᶜ).coverNum = (m + 4) * (n + 4) - 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ⊗g cycle (n + 4))
  rw [cliqueNum_tensorProduct, cliqueNum_cycle, cliqueNum_cycle, V_tensorProduct, V_cycle,
      V_cycle] at h
  omega

theorem coverNum_compl_tensorProduct_path (m n : ℕ) :
    ((path (m + 2) ⊗g path (n + 2))ᶜ).coverNum = (m + 2) * (n + 2) - 2 := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ⊗g path (n + 2))
  rw [cliqueNum_tensorProduct, cliqueNum_path, cliqueNum_path, V_tensorProduct, V_path, V_path] at h
  omega

theorem coverNum_compl_strongProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊠g cycle (n + 4))ᶜ).coverNum = (m + 4) * (n + 4) - 4 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ⊠g cycle (n + 4))
  rw [cliqueNum_strongProduct, cliqueNum_cycle, cliqueNum_cycle, V_strongProduct, V_cycle,
      V_cycle] at h
  omega

theorem coverNum_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊕g cycle (n + 4))ᶜ).coverNum = m + n + 6 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ⊕g cycle (n + 4))
  rw [cliqueNum_disjUnion, cliqueNum_cycle, cliqueNum_cycle, V_disjUnion, V_cycle, V_cycle] at h
  omega

theorem coverNum_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 2) ⊕g path (n + 2))ᶜ).coverNum = m + n + 2 := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ⊕g path (n + 2))
  rw [cliqueNum_disjUnion, cliqueNum_path, cliqueNum_path, V_disjUnion, V_path, V_path] at h
  omega

theorem coverNum_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 4) ∇g cycle (n + 4))ᶜ).coverNum = m + n + 4 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ∇g cycle (n + 4))
  rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_cycle, V_join, V_cycle, V_cycle] at h
  omega

theorem coverNum_compl_join_path (m n : ℕ) :
    ((path (m + 2) ∇g path (n + 2))ᶜ).coverNum = m + n := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ∇g path (n + 2))
  rw [cliqueNum_join, cliqueNum_path, cliqueNum_path, V_join, V_path, V_path] at h
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
