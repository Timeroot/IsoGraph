import IsoGraph.Values.Identities.Mycielskians

/-!
# The folded cube, and the last of the columns

The balanced complete multipartite graph in closed form, the circulant and Paley graphs under the
two operators, and the folded cube, whose table is proved here in full.

The last sections finish two columns across all the families at once: which of them are
vertex-transitive — the grid, the king graph, the unbalanced Turán graphs and the proper theta
graphs are not — and which are regular, from which the chromatic indices of the odd-order regular
graphs follow.  Two computations that do not fit anywhere else close the library: the independence
number of the torus, and the automorphism group of the hypercube.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ### Two closed forms for the balanced complete multipartite graph -/

@[simp] theorem cliqueNum_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m (d + 1))).cliqueNum = m := by
  rw [cliqueNum_completeMultipartite, List.map_replicate, show min (d + 1) 1 = 1 from by omega,
    List.sum_replicate, smul_eq_mul, Nat.mul_one]

@[simp] theorem chromNum_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m (d + 1))).chromNum = m := by
  rw [chromNum_completeMultipartite, List.map_replicate, show min (d + 1) 1 = 1 from by omega,
    List.sum_replicate, smul_eq_mul, Nat.mul_one]

theorem maxDeg_completeMultipartite_replicate_succ (m d : ℕ) :
    maxDeg (completeMultipartite (List.replicate (m + 2) (d + 1))) = (m + 1) * (d + 1) :=
  maxDeg_completeMultipartite_replicate (by omega) (by omega)

theorem minDeg_completeMultipartite_replicate_succ (m d : ℕ) :
    minDeg (completeMultipartite (List.replicate (m + 2) (d + 1))) = (m + 1) * (d + 1) :=
  minDeg_completeMultipartite_replicate (by omega) (by omega)

theorem E_pos_completeMultipartite_replicate (m d : ℕ) :
    0 < (completeMultipartite (List.replicate (m + 2) (d + 1))).E := by
  rw [E_completeMultipartite_replicate]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (by positivity)

/-! ### The line graph of a balanced complete multipartite graph -/

theorem V_lineGraph_completeMultipartite_replicate (m d : ℕ) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))).V
      = (m + 2).choose 2 * ((d + 1) * (d + 1)) := by
  rw [V_lineGraph, E_completeMultipartite_replicate]

theorem isRegularWith_lineGraph_completeMultipartite_replicate (m d : ℕ) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))).IsRegularWith
      (2 * ((m + 1) * (d + 1)) - 2) :=
  isRegularWith_lineGraph (E_pos_completeMultipartite_replicate m d)
    (degSequence_completeMultipartite_replicate (m + 2) (d + 1))

theorem maxDeg_lineGraph_completeMultipartite_replicate (m d : ℕ) :
    maxDeg (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1))))
      = 2 * ((m + 1) * (d + 1)) - 2 :=
  maxDeg_lineGraph (E_pos_completeMultipartite_replicate m d)
    (degSequence_completeMultipartite_replicate (m + 2) (d + 1))

theorem minDeg_lineGraph_completeMultipartite_replicate (m d : ℕ) :
    minDeg (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1))))
      = 2 * ((m + 1) * (d + 1)) - 2 :=
  minDeg_lineGraph (E_pos_completeMultipartite_replicate m d)
    (degSequence_completeMultipartite_replicate (m + 2) (d + 1))

theorem isConnected_lineGraph_completeMultipartite_replicate (m d : ℕ) :
    IsConnected (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))) :=
  isConnected_lineGraph (isConnected_completeMultipartite_replicate m d)
    (E_pos_completeMultipartite_replicate m d)

theorem numComponents_lineGraph_completeMultipartite_replicate (m d : ℕ) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))).numComponents = 1 :=
  numComponents_lineGraph (isConnected_completeMultipartite_replicate m d)
    (E_pos_completeMultipartite_replicate m d)

theorem diameter_lineGraph_completeMultipartite_replicate_le (m d : ℕ) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 2)))).diameter ≤ 3 := by
  have hc : IsConnected (completeMultipartite (List.replicate (m + 2) (d + 2))) :=
    isConnected_completeMultipartite_replicate m (d + 1)
  have hE : 0 < (completeMultipartite (List.replicate (m + 2) (d + 2))).E :=
    E_pos_completeMultipartite_replicate m (d + 1)
  have h := diameter_lineGraph_le hc hE
  rw [diameter_completeMultipartite_replicate] at h
  omega

theorem radius_lineGraph_completeMultipartite_replicate_le (m d : ℕ) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 2)))).radius ≤ 3 := by
  have hc : IsConnected (completeMultipartite (List.replicate (m + 2) (d + 2))) :=
    isConnected_completeMultipartite_replicate m (d + 1)
  have hE : 0 < (completeMultipartite (List.replicate (m + 2) (d + 2))).E :=
    E_pos_completeMultipartite_replicate m (d + 1)
  have h := radius_lineGraph_le hc hE
  rw [radius_completeMultipartite_replicate] at h
  omega

theorem cliqueNum_lineGraph_completeMultipartite_replicate {m d : ℕ}
    (h3 : 3 ≤ (m + 1) * (d + 1)) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))).cliqueNum
      = (m + 1) * (d + 1) := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg
    (G := completeMultipartite (List.replicate (m + 2) (d + 1)))
    (by rw [maxDeg_completeMultipartite_replicate_succ]; exact h3)
  rwa [maxDeg_completeMultipartite_replicate_succ] at hm

theorem girth_lineGraph_completeMultipartite_replicate {m d : ℕ} (h3 : 3 ≤ (m + 1) * (d + 1)) :
    (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_completeMultipartite_replicate_succ]; exact h3)

theorem not_isBipartite_lineGraph_completeMultipartite_replicate {m d : ℕ}
    (h3 : 3 ≤ (m + 1) * (d + 1)) :
    ¬ IsBipartite (lineGraph (completeMultipartite (List.replicate (m + 2) (d + 1)))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_completeMultipartite_replicate_succ]; exact h3)

/-! ### The Mycielskian of a balanced complete multipartite graph -/

@[simp] theorem V_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    (mycielskian (completeMultipartite (List.replicate m d))).V = 2 * (m * d) + 1 := by
  rw [V_mycielskian, V_completeMultipartite_replicate]

@[simp] theorem E_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    (mycielskian (completeMultipartite (List.replicate m d))).E
      = 3 * (m.choose 2 * (d * d)) + m * d := by
  rw [E_mycielskian, E_completeMultipartite_replicate, V_completeMultipartite_replicate]

@[simp] theorem chromNum_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    (mycielskian (completeMultipartite (List.replicate m (d + 1)))).chromNum = m + 1 := by
  rw [chromNum_mycielskian, chromNum_completeMultipartite_replicate]

theorem cliqueNum_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    (mycielskian (completeMultipartite (List.replicate (m + 1) (d + 1)))).cliqueNum
      = max (m + 1) 2 := by
  have hm := cliqueNum_mycielskian (completeMultipartite (List.replicate (m + 1) (d + 1)))
    (by rw [V_completeMultipartite_replicate]; positivity)
  rwa [cliqueNum_completeMultipartite_replicate] at hm

theorem maxDeg_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    maxDeg (mycielskian (completeMultipartite (List.replicate (m + 2) (d + 1))))
      = max (2 * ((m + 1) * (d + 1))) ((m + 2) * (d + 1)) := by
  rw [maxDeg_mycielskian, maxDeg_completeMultipartite_replicate_succ,
    V_completeMultipartite_replicate]

theorem isConnected_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    IsConnected (mycielskian (completeMultipartite (List.replicate (m + 2) (d + 1)))) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_completeMultipartite_replicate_succ]
  positivity

theorem radius_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    (mycielskian (completeMultipartite (List.replicate (m + 2) (d + 1)))).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_completeMultipartite_replicate_succ]
  positivity

theorem domNum_mycielskian_completeMultipartite_replicate (m d : ℕ) :
    (mycielskian (completeMultipartite (List.replicate (m + 2) (d + 2)))).domNum = 3 := by
  have h1 := domNum_mycielskian (completeMultipartite (List.replicate (m + 2) (d + 2)))
    (by rw [V_completeMultipartite_replicate]; positivity)
  rw [domNum_completeMultipartite_replicate] at h1
  omega

/-! ### The line graph of a circulant graph -/

theorem E_pos_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (hk0 : 0 < k)
    (hk : n * k = 2 * (circulant n S).E) : 0 < (circulant n S).E := by
  have h := Nat.mul_pos hn hk0
  omega

theorem two_mul_V_lineGraph_circulant {n k : ℕ} {S : List ℕ}
    (hk : n * k = 2 * (circulant n S).E) : 2 * (lineGraph (circulant n S)).V = n * k := by
  rw [V_lineGraph]
  omega

theorem isRegularWith_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (hk0 : 0 < k)
    (hk : n * k = 2 * (circulant n S).E) :
    (lineGraph (circulant n S)).IsRegularWith (2 * k - 2) :=
  isRegularWith_lineGraph (E_pos_circulant hn hk0 hk) (degSequence_circulant hn hk)

theorem maxDeg_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (hk0 : 0 < k)
    (hk : n * k = 2 * (circulant n S).E) : maxDeg (lineGraph (circulant n S)) = 2 * k - 2 :=
  maxDeg_lineGraph (E_pos_circulant hn hk0 hk) (degSequence_circulant hn hk)

theorem minDeg_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (hk0 : 0 < k)
    (hk : n * k = 2 * (circulant n S).E) : minDeg (lineGraph (circulant n S)) = 2 * k - 2 :=
  minDeg_lineGraph (E_pos_circulant hn hk0 hk) (degSequence_circulant hn hk)

theorem cliqueNum_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (h3 : 3 ≤ k)
    (hk : n * k = 2 * (circulant n S).E) : (lineGraph (circulant n S)).cliqueNum = k := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := circulant n S)
    (by rw [maxDeg_circulant hn hk]; exact h3)
  rwa [maxDeg_circulant hn hk] at hm

theorem girth_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (h3 : 3 ≤ k)
    (hk : n * k = 2 * (circulant n S).E) : (lineGraph (circulant n S)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_circulant hn hk]; exact h3)

theorem not_isBipartite_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (h3 : 3 ≤ k)
    (hk : n * k = 2 * (circulant n S).E) : ¬ IsBipartite (lineGraph (circulant n S)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_circulant hn hk]; exact h3)

theorem not_isTree_lineGraph_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (h3 : 3 ≤ k)
    (hk : n * k = 2 * (circulant n S).E) : ¬ IsTree (lineGraph (circulant n S)) :=
  not_isTree_lineGraph (by rw [maxDeg_circulant hn hk]; exact h3)

/-! ### The Mycielskian of a circulant graph -/

@[simp] theorem V_mycielskian_circulant (n : ℕ) (S : List ℕ) :
    (mycielskian (circulant n S)).V = 2 * n + 1 := by
  rw [V_mycielskian, V_circulant]

@[simp] theorem E_mycielskian_circulant (n : ℕ) (S : List ℕ) :
    (mycielskian (circulant n S)).E = 3 * (circulant n S).E + n := by
  rw [E_mycielskian, V_circulant]

theorem two_mul_E_mycielskian_circulant {n k : ℕ} {S : List ℕ}
    (hk : n * k = 2 * (circulant n S).E) :
    2 * (mycielskian (circulant n S)).E = 3 * (n * k) + 2 * n := by
  rw [E_mycielskian_circulant]
  omega

theorem maxDeg_mycielskian_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) :
    maxDeg (mycielskian (circulant n S)) = max (2 * k) n := by
  rw [maxDeg_mycielskian, maxDeg_circulant hn hk, V_circulant]

theorem minDeg_mycielskian_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) :
    minDeg (mycielskian (circulant n S)) = min (min (2 * k) (k + 1)) n := by
  have h := minDeg_mycielskian (circulant n S) (by rw [V_circulant]; exact hn)
  rwa [minDeg_circulant hn hk, V_circulant] at h

theorem isConnected_mycielskian_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (hk0 : 0 < k)
    (hk : n * k = 2 * (circulant n S).E) : IsConnected (mycielskian (circulant n S)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_circulant hn hk]
  exact hk0

theorem radius_mycielskian_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n) (hk0 : 0 < k)
    (hk : n * k = 2 * (circulant n S).E) : (mycielskian (circulant n S)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_circulant hn hk]
  exact hk0

theorem domNum_mycielskian_circulant {n : ℕ} {S : List ℕ} (hn : 0 < n) :
    (mycielskian (circulant n S)).domNum = (circulant n S).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_circulant]; exact hn)

theorem coverNum_mycielskian_circulant_le (n : ℕ) (S : List ℕ) :
    (mycielskian (circulant n S)).coverNum ≤ n + 1 := by
  have h := coverNum_mycielskian_le (circulant n S)
  rwa [V_circulant] at h

/-! ### The line graph of a Paley graph -/

theorem E_pos_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    0 < (paley q).E := by
  have h := two_mul_E_paley q hq
  have h2 : 0 < q * ((q - 1) / 2) := Nat.mul_pos (by omega) (by omega)
  omega

theorem two_mul_V_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    2 * (lineGraph (paley q)).V = q * ((q - 1) / 2) := by
  rw [V_lineGraph]
  exact two_mul_E_paley q hq

theorem maxDeg_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    maxDeg (lineGraph (paley q)) = 2 * ((q - 1) / 2) - 2 :=
  maxDeg_lineGraph (E_pos_paley q hq hq5) (degSequence_paley q hq)

theorem minDeg_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    minDeg (lineGraph (paley q)) = 2 * ((q - 1) / 2) - 2 :=
  minDeg_lineGraph (E_pos_paley q hq hq5) (degSequence_paley q hq)

theorem degSequence_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : degSequence (lineGraph (paley q))
      = List.replicate (q * ((q - 1) / 2) / 2) (2 * ((q - 1) / 2) - 2) := by
  have h := two_mul_E_paley q hq
  have hd := (isRegularWith_lineGraph_paley q hq hq5).degSequence
  rw [V_lineGraph] at hd
  rwa [show (paley q).E = q * ((q - 1) / 2) / 2 from by omega] at hd

theorem isConnected_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : IsConnected (lineGraph (paley q)) :=
  isConnected_lineGraph (isConnected_paley q hq hq5) (E_pos_paley q hq hq5)

theorem numComponents_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : (lineGraph (paley q)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_paley q hq hq5) (E_pos_paley q hq hq5)

theorem diameter_lineGraph_paley_le (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : (lineGraph (paley q)).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (isConnected_paley q hq hq5) (E_pos_paley q hq hq5)
  rw [diameter_paley q hq hq5] at h
  omega

theorem radius_lineGraph_paley_le (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : (lineGraph (paley q)).radius ≤ 3 := by
  have h := radius_lineGraph_le (isConnected_paley q hq hq5) (E_pos_paley q hq hq5)
  rw [radius_paley q hq hq5] at h
  omega

theorem cliqueNum_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq9 : 9 ≤ q) : (lineGraph (paley q)).cliqueNum = (q - 1) / 2 := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := paley q)
    (by rw [maxDeg_paley q hq]; omega)
  rwa [maxDeg_paley q hq] at hm

theorem girth_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    (lineGraph (paley q)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_paley q hq]; omega)

theorem not_isBipartite_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq9 : 9 ≤ q) : ¬ IsBipartite (lineGraph (paley q)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_paley q hq]; omega)

theorem not_isTree_lineGraph_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq9 : 9 ≤ q) : ¬ IsTree (lineGraph (paley q)) :=
  not_isTree_lineGraph (by rw [maxDeg_paley q hq]; omega)

/-! ### The Mycielskian of a Paley graph -/

@[simp] theorem V_mycielskian_paley (q : ℕ) : (mycielskian (paley q)).V = 2 * q + 1 := by
  rw [V_mycielskian, V_paley]

theorem two_mul_E_mycielskian_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    2 * (mycielskian (paley q)).E = 3 * (q * ((q - 1) / 2)) + 2 * q := by
  have h := two_mul_E_paley q hq
  rw [E_mycielskian, V_paley]
  omega

theorem maxDeg_mycielskian_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    maxDeg (mycielskian (paley q)) = max (2 * ((q - 1) / 2)) q := by
  rw [maxDeg_mycielskian, maxDeg_paley q hq, V_paley]

theorem minDeg_mycielskian_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    minDeg (mycielskian (paley q))
      = min (min (2 * ((q - 1) / 2)) ((q - 1) / 2 + 1)) q := by
  have h := minDeg_mycielskian (paley q) (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q))
  rwa [minDeg_paley q hq, V_paley] at h

theorem isConnected_mycielskian_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : IsConnected (mycielskian (paley q)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_paley q hq]
  omega

theorem radius_mycielskian_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : (mycielskian (paley q)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_paley q hq]
  omega

theorem numComponents_mycielskian_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (hq5 : 5 ≤ q) : (mycielskian (paley q)).numComponents = 1 := by
  refine numComponents_mycielskian _ ?_
  rw [minDeg_paley q hq]
  omega

theorem domNum_mycielskian_paley (q : ℕ) [NeZero q] :
    (mycielskian (paley q)).domNum = (paley q).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_paley]; exact Nat.pos_of_ne_zero (NeZero.ne q))

theorem coverNum_mycielskian_paley_le (q : ℕ) : (mycielskian (paley q)).coverNum ≤ q + 1 := by
  have h := coverNum_mycielskian_le (paley q)
  rwa [V_paley] at h

theorem le_indepNum_mycielskian_paley (q : ℕ) : q ≤ (mycielskian (paley q)).indepNum := by
  have h := V_le_indepNum_mycielskian (paley q)
  rwa [V_paley] at h

/-! ### The folded cube

`foldedCube n` is `Qₙ` with every antipodal pair joined, so it is `(n + 1)`-regular once `n ≥ 2`
and its Hamming description makes the girth, clique number and colouring arguments completely
combinatorial: two vertices are adjacent exactly when they differ in one coordinate or in all of
them. -/

/-- Each vertex of the folded cube has `n` coordinate neighbours and one antipode. -/
theorem isRegularWith_foldedCube (n : ℕ) : (foldedCube (n + 2)).IsRegularWith (n + 3) :=
  have hcard :
      ∀ (x : (CGraph.foldedCube (n + 2)).V), ((CGraph.foldedCube (n + 2)).nbrs x).card = n + 3 := by
    intro x
    let xc : Fin (n + 2) → Bool := fun i => !x i
    have hx_ne_compl2 : x ≠ xc := by
      intro h; have := congr_fun h ⟨0, by omega⟩; simp [xc] at this
    set F := fun w : Fin (n + 2) → Bool => (Finset.univ.filter (fun i => x i ≠ w i)).card
    have hs_compl : F xc = n + 2 := by
      simp [xc, F]
    have hcard_univ : ∀ w : Fin (n + 2) → Bool, F w = n + 2 → w = xc := by
      intro w hsw
      have hfull : ∀ i : Fin (n + 2), x i ≠ w i := by
        by_contra h
        push_neg at h
        have : (Finset.univ.filter (fun i => x i ≠ w i)).card ≤ n + 1 := by
          have : Finset.univ.filter (fun i => x i ≠ w i) ⊆ Finset.univ.erase h.choose := by
            intro i hi; simp at hi ⊢
            intro heq; rw [heq] at hi; exact hi h.choose_spec
          calc (Finset.univ.filter (fun i => x i ≠ w i)).card ≤ (Finset.univ.erase
              h.choose).card := Finset.card_le_card this
            _ = n + 1 := by simp
        linarith
      ext i; exact show w i = !x i from by
        have := hfull i
        cases hxi : x i with
        | true => simp [hxi] at this; simp [this]
        | false => simp [hxi] at this; simp [this]
    have hs_pos_imp_ne : ∀ w : Fin (n + 2) → Bool, F w > 0 → x ≠ w := by
      intro w hpos hne
      subst hne
      simp [F] at hpos
    -- Step 2: nbrs_foldedCube x = nbrs_hypercube x ∪ {xc}
    have hnbrs_eq : (CGraph.foldedCube (n + 2)).nbrs x =
        (CGraph.hypercube (n + 2)).nbrs x ∪ {xc} := by
      ext y
      simp only [CGraph.mem_nbrs, CGraph.foldedCube_adj]
      have convert : ∀ w : Fin (n + 2) → Bool,
          (({i : Fin (n + 2) | x i ≠ w i} : Set (Fin (n + 2))).ncard) = F w := by
        intro w
        show Set.ncard ({i : Fin (n + 2) | x i ≠ w i} : Set (Fin (n + 2))) = F w
        rw [Set.ncard_eq_toFinset_card]
        simp [F]
      simp only [Finset.mem_union, Finset.mem_singleton, CGraph.mem_nbrs, CGraph.hypercube_adj]
      -- The goal has `{i | ...}.card` which is `Nat.card (Set.setOf ...)` = `Fintype.card {i //
      -- ...}`
      have goal_card : ∀ w : Fin (n + 2) → Bool,
          Fintype.card {i : Fin (n + 2) // x i ≠ w i} = F w := by
        intro w
        show Fintype.card {i : Fin (n + 2) // x i ≠ w i} = (Finset.univ.filter (fun i => x i ≠ w
            i)).card
        rw [Fintype.card_subtype]
      -- Convert goal's `.card` (Nat.card on Set) to Fintype.card
      have hconv : ∀ w : Fin (n + 2) → Bool,
          Nat.card ({i | x i ≠ w i} : Set (Fin (n + 2))) = F w := by
        intro w
        show Nat.card {i : Fin (n + 2) // x i ≠ w i} = F w
        rw [Nat.card_eq_fintype_card]
        exact goal_card w
      show (decide (x ≠ y) && (F y == 1 || F y == n + 2)) = true ↔ (F y == 1) = true ∨ y = xc
      have beq_to_eq : ∀ (a b : ℕ), ((a == b) = true ↔ a = b) := by simp [beq_iff_eq]
      set Fy := F y with hFy_def
      simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff]
      simp only [show decide (x ≠ y) = true ↔ x ≠ y from by simp]
      rw [show ((F y == 1) = true ↔ F y = 1) from beq_to_eq _ _,
          show ((F y == n + 2) = true ↔ F y = n + 2) from beq_to_eq _ _]
      constructor
      · rintro ⟨hne, h1|h2⟩
        · left; exact h1
        · right; exact hcard_univ y h2
      · rintro (h1 | hy)
        · exact ⟨hs_pos_imp_ne y (by rw [h1]; omega), Or.inl h1⟩
        · subst hy; rw [hs_compl]; simp; exact hx_ne_compl2
    -- Step 3: disjoint
    have hnotin : xc ∉ (CGraph.hypercube (n + 2)).nbrs x := by
      simp [CGraph.nbrs, CGraph.hypercube_adj, xc]
    have hdj : Disjoint ((CGraph.hypercube (n + 2)).nbrs x) {xc} :=
      Finset.disjoint_singleton_right.mpr hnotin
    -- Step 4: card of hypercube nbrs x = n + 2
    have hcard_hyper : ((CGraph.hypercube (n + 2)).nbrs x).card = n + 2 := by
      have hreg_iso : IsoGraph.IsRegularWith (IsoGraph.hypercube (n + 2)) (n +
          2) := IsoGraph.isRegularWith_hypercube (n + 2)
      unfold IsoGraph.hypercube at hreg_iso
      rw [IsoGraph.isRegularWith_mk] at hreg_iso
      rw [CGraph.isRegularWith_iff_forall_degree] at hreg_iso
      have := CGraph.card_nbrs_eq_degree (CGraph.hypercube (n + 2)) x
      exact this ▸ hreg_iso x
    -- Step 5: conclude
    rw [hnbrs_eq, Finset.card_union_of_disjoint hdj, hcard_hyper, Finset.card_singleton]
  CGraph.isRegularWith_of_card_nbrs _ hcard

theorem minDeg_foldedCube (n : ℕ) : minDeg (foldedCube (n + 2)) = n + 3 :=
  IsRegularWith.minDeg_eq (isRegularWith_foldedCube n) (by simp [V_foldedCube])

/-- Regularity again, this time through `IsRegularWith.maxDeg_eq`. -/
theorem maxDeg_foldedCube (n : ℕ) : maxDeg (foldedCube (n + 2)) = n + 3 :=
  IsRegularWith.maxDeg_eq (isRegularWith_foldedCube n) (by simp [V_foldedCube])

/-- Handshaking on `isRegularWith_foldedCube`. -/
theorem two_mul_E_foldedCube (n : ℕ) :
    2 * (foldedCube (n + 2)).E = 2 ^ (n + 2) * (n + 3) := by
  rw [IsRegularWith.two_mul_E (isRegularWith_foldedCube n), V_foldedCube]

/-- Two coordinate flips never compose to a single flip or to the antipodal map once `n ≥ 3`, so
there is no triangle; the four-cycles of `Qₙ` survive. -/
theorem girth_foldedCube (n : ℕ) : (foldedCube (n + 3)).girth = 4 := by
  set m := n + 3
  have hm_ge_3 : 3 ≤ m := by omega
  -- Define 4 vertices forming a coordinate square
  let a : Fin m → Bool := fun _ => false
  let b : Fin m → Bool := fun i => if (i : ℕ) = 0 then true else false
  let c : Fin m → Bool := fun i => decide ((i : ℕ) = 0 ∨ (i : ℕ) = 1)
  let d : Fin m → Bool := fun i => if (i : ℕ) = 1 then true else false
  -- Key Finset facts
  have hab_filter : Finset.filter (fun i => a i ≠ b i) Finset.univ = {⟨0, by omega⟩} := by
    ext i; simp [a, b]
  have hab_card : (Finset.univ.filter fun i => a i ≠ b i).card = 1 := by rw [hab_filter]; simp
  have hab_ne : a ≠ b := fun h => by
    have h0 := congr_fun h ⟨0, by omega⟩; simp [a, b] at h0
  have hab_adj : (CGraph.foldedCube m).Adj a b = true := by
    rw [CGraph.foldedCube_adj]; simp [hab_ne, hab_card]
  -- Hamming filter for (b,c): differ only at index 1
  have hbc_filter : Finset.filter (fun i => b i ≠ c i) Finset.univ = {⟨1, by omega⟩} := by
    ext i; simp [b, c]
    constructor
    · intro h; exact Fin.ext h.1
    · intro h
      refine ⟨h.symm ▸ rfl, ?_⟩
      show (i : Fin m) ≠ 0
      subst h
      have : 1 < m := by omega
      simp
  have hbc_ne : b ≠ c := by
    intro h
    have h1 := congr_fun h ⟨1, by omega⟩
    simp [b, c] at h1
    have : 1 < m := by omega
    exact False.elim (h1 (Nat.mod_eq_of_lt this))
  have hbc_adj : (CGraph.foldedCube m).Adj b c = true := by
    rw [CGraph.foldedCube_adj]; simp [hbc_ne, hbc_filter]
  -- Hamming filter for (c,d): differ only at index 0
  have hcd_filter : Finset.filter (fun i => c i ≠ d i) Finset.univ = {⟨0, by omega⟩} := by
    ext i; simp [c, d]
    intro hi; subst hi; simp
  have hcd_ne : c ≠ d := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [c, d] at this
  have hcd_adj : (CGraph.foldedCube m).Adj c d = true := by
    rw [CGraph.foldedCube_adj]; simp [hcd_ne, hcd_filter]
  -- Hamming filter for (d,a): differ only at index 1
  have hda_filter : Finset.filter (fun i => d i ≠ a i) Finset.univ = {⟨1, by omega⟩} := by
    ext i; simp [d, a]
    exact ⟨fun h => Fin.ext h, fun h => h.symm ▸ rfl⟩
  have hda_ne : d ≠ a := by
    intro h; have h1 := congr_fun h ⟨1, by omega⟩
    simp [d, a] at h1
    have : 1 < m := by omega
    exact False.elim (h1 (Nat.mod_eq_of_lt this))
  have hda_adj : (CGraph.foldedCube m).Adj d a = true := by
    rw [CGraph.foldedCube_adj]; simp [hda_ne, hda_filter]
  have hac_ne : a ≠ c := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [a, c] at this
  have hbd_ne2 : b ≠ d := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [b, d] at this
  -- Girth ≤ 4: explicit 4-cycle
  have hgirth_le : (CGraph.foldedCube m).girth ≤ 4 := by
    apply CGraph.girth_le_four_of_square hab_adj hbc_adj hcd_adj hda_adj hac_ne hbd_ne2
  -- Not acyclic: same 4-cycle
  have hnac : ¬ (CGraph.foldedCube m).IsAcyclic := by
    apply CGraph.not_isAcyclic_of_square hab_adj hbc_adj hcd_adj hda_adj hac_ne hbd_ne2
  -- Triangle-free: need to prove
  -- Key Hamming helper: card of filter (a i ≠ b i) ≤ sum of cards for (a,c) and (c,b)
  have hamming_triangle : ∀ a b c : Fin m → Bool,
      (Finset.univ.filter (fun i => ¬a i = b i)).card ≤
        ((Finset.univ.filter (fun i => ¬a i = c i)).card +
         (Finset.univ.filter (fun i => ¬c i = b i)).card) := by
    intro a b c
    have hsub : Finset.univ.filter (fun i => ¬a i = b i) ⊆
        Finset.univ.filter (fun i => ¬a i = c i) ∪ Finset.univ.filter (fun i => ¬c i = b i) := by
      intro i hi
      simp at hi
      by_contra h
      simp [Finset.mem_union, Finset.mem_filter] at h
      exact hi (h.1.trans h.2)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- Hamming symmetry
  have hamming_symm : ∀ a b : Fin m → Bool,
      (Finset.univ.filter (fun i => ¬a i = b i)).card =
      (Finset.univ.filter (fun i => ¬b i = a i)).card := by
    intro a b; congr 1; ext i; simp [ne_comm]
  -- If card = m, then a i ≠ b i for all i, so a = not b
  have hamming_m_implies : ∀ a b : Fin m → Bool,
      (Finset.univ.filter (fun i => ¬a i = b i)).card = m → (∀ i, a i = !b i) := by
    intro a b hcard
    have huniv : Finset.univ.filter (fun i => ¬a i = b i) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.filter_subset _ _
      · simp [hcard, Fintype.card_fin]
    intro i
    have hi : i ∈ Finset.univ.filter (fun i => ¬a i = b i) := huniv.symm ▸ Finset.mem_univ i
    have hi' : a i ≠ b i := by simpa using hi
    exact (by decide : ∀ p q : Bool, p ≠ q → p = !q) _ _ hi'
  -- The three pairwise Hamming distances are each `1` or `m`.  A `(1,1,1)` triangle would be a
  -- triangle in the hypercube, which is bipartite; every case with exactly one `m` dies on the
  -- triangle inequality (`m ≥ 3 > 2`) or on a `m - 1 = 1` count; and two or more `m`s force two
  -- of the three vertices to be equal.
  have htri : ∀ x y z : (CGraph.foldedCube m).V,
      (CGraph.foldedCube m).Adj x y →
      (CGraph.foldedCube m).Adj y z →
      (CGraph.foldedCube m).Adj z x → False := by
    intro x y z hxy hyz hzx
    simp [CGraph.foldedCube_adj] at hxy hyz hzx
    obtain ⟨hxy_ne, hxy_card⟩ := hxy
    obtain ⟨hyz_ne, hyz_card⟩ := hyz
    obtain ⟨hzx_ne, hzx_card⟩ := hzx
    -- Rewrite z-x card using symmetry
    have hzx_card' : ((Finset.univ.filter (fun i => ¬z i = x i)).card = (Finset.univ.filter (fun i
        => ¬x i = z i)).card) := hamming_symm z x
    rcases hxy_card with hxy1 | hxy1 <;> rcases hyz_card with hyz1 | hyz1 <;> rcases hzx_card with
        hzx1 | hzx1
    · -- (1,1,1): all dist 1 → hypercube triangle → impossible (bipartite)
      exfalso
      have hxy_adj : CGraph.Adj (CGraph.hypercube m) (x : Fin m → Bool) (y : Fin m → Bool) := by
        simp [CGraph.hypercube_adj, hxy1]
      have hyz_adj : CGraph.Adj (CGraph.hypercube m) (y : Fin m → Bool) (z : Fin m → Bool) := by
        simp [CGraph.hypercube_adj, hyz1]
      have hzx_adj : CGraph.Adj (CGraph.hypercube m) (z : Fin m → Bool) (x : Fin m → Bool) := by
        simp [CGraph.hypercube_adj, hzx1]
      have hxz_adj : (CGraph.hypercube m).Adj x z := by
        simp [CGraph.hypercube_adj, hamming_symm x z, hzx1]
      exact absurd (CGraph.not_isBipartite_of_triangle hxy_adj hxz_adj hyz_adj
          (isBipartite_hypercube m)) (by simp)
    · -- (1,1,m): card(x,z)=m but ≤ 2 < m
      exfalso; rw [hzx_card'] at hzx1
      have : (Finset.univ.filter (fun i => ¬x i = z i)).card ≤ 2 := by
        calc _ ≤ (Finset.univ.filter (fun i => ¬x i = y i)).card + (Finset.univ.filter (fun i => ¬y
            i = z i)).card := hamming_triangle x z y
          _ = 1 + 1 := by rw [hxy1, hyz1]
          _ = 2 := by omega
      omega
    · -- (1,m,1): y = not z, so card(x,y) = card(x,not z) = m - card(x,z) = m-1, but = 1,
      -- contradiction
      exfalso
      have hy_not_z : ∀ i, y i = !z i := hamming_m_implies y z hyz1
      have hcard_xy_not_z : (Finset.univ.filter (fun i => ¬x i = y
          i)).card = m - (Finset.univ.filter (fun i => ¬x i = z i)).card := by
        have hflip : ∀ i, ¬x i = y i ↔ x i = z i :=
            by intro i; rw [hy_not_z i]; cases x i <;> cases z i <;> simp
        have h1 : Finset.univ.filter (fun i => ¬x i = y i) = Finset.univ.filter (fun i => x i = z
            i) := by ext i; simp [hflip]
        rw [h1]
        have hcard2 : (Finset.univ.filter (fun i => x i = z i)).card = m - (Finset.univ.filter (fun
            i => ¬x i = z i)).card := by
          have hflip2 : Finset.univ.filter (fun i => x i = z i) = (Finset.univ.filter (fun i => ¬x
              i = z i))ᶜ := by
            ext i; simp
          rw [hflip2, Finset.card_compl]
          simp [Fintype.card_fin]
        rw [hcard2]
      omega
    · -- (1,m,m): y = not z, x = not z → x = y, contradiction
      exfalso
      have hy_not_z : ∀ i, y i = !z i := hamming_m_implies y z hyz1
      have hx_not_z : ∀ i, x i = !z i := by
        rw [hzx_card'] at hzx1; exact hamming_m_implies x z hzx1
      exact hxy_ne (funext fun i => by rw [hy_not_z, hx_not_z])
    · -- (m,1,1): `card(x,y) ≤ card(x,z) + card(z,y) = 1 + 1 = 2 < m`
      exfalso
      have : (Finset.univ.filter (fun i => ¬x i = y i)).card ≤ (Finset.univ.filter (fun i => ¬x i =
          z i)).card + (Finset.univ.filter (fun i => ¬z i = y i)).card := hamming_triangle x y z
      rw [hzx_card'] at hzx1
      rw [hamming_symm z y] at this
      rw [hyz1] at this
      omega
    · -- (m,1,m): x=not y, z=not x → z=y, contradiction
      exfalso
      have hx_not_y : ∀ i, x i = !y i := hamming_m_implies x y hxy1
      have hz_not_x : ∀ i, z i = !x i := hamming_m_implies z x hzx1
      exact hyz_ne (funext fun i => by
        rw [hz_not_x i, hx_not_y i, Bool.not_not])
    · -- (m,m,1): x=not y, y=not z → x=z, contradiction
      exfalso
      have hx_not_y : ∀ i, x i = !y i := hamming_m_implies x y hxy1
      have hy_not_z : ∀ i, y i = !z i := hamming_m_implies y z hyz1
      exact hzx_ne (funext fun i => by rw [hx_not_y, hy_not_z, Bool.not_not])
    · -- (m,m,m): x=not y, y=not z, z=not x → x=z, contradiction
      exfalso
      have hx_not_y : ∀ i, x i = !y i := hamming_m_implies x y hxy1
      have hy_not_z : ∀ i, y i = !z i := hamming_m_implies y z hyz1
      exact hzx_ne (funext fun i => by rw [hx_not_y, hy_not_z, Bool.not_not])
  -- 4 ≤ girth
  have hgirth_ge : 4 ≤ (CGraph.foldedCube m).girth := by
    apply CGraph.four_le_girth htri hnac
  -- Conclusion
  exact le_antisymm hgirth_le hgirth_ge

theorem cliqueNum_foldedCube (n : ℕ) : (foldedCube (n + 3)).cliqueNum = 2 := by
  have hg := girth_foldedCube n
  have hcl : (foldedCube (n + 3)).cliqueNum ≤ 2 := by
    by_contra h
    push_neg at h
    have := girth_eq_three_of_cliqueNum h
    omega
  have hlo : 2 ≤ (foldedCube (n + 3)).cliqueNum :=
    two_le_cliqueNum_of_E_pos (by
      have hadj : (CGraph.foldedCube (n + 3)).Adj (fun _ ↦ false) (fun _ ↦ true) = true := by
        simp [CGraph.foldedCube_adj]
        intro h
        have := congr_fun h ⟨0, by omega⟩
        simp at this
      simp only [foldedCube_def]
      exact CGraph.E_pos_of_adj hadj)
  omega

theorem not_isAcyclic_foldedCube (n : ℕ) : ¬ IsAcyclic (foldedCube (n + 3)) := by
  intro hac
  have hg : (foldedCube (n + 3)).girth = 0 := (@girth_eq_zero_iff _).mpr hac
  rw [girth_foldedCube] at hg
  exact absurd hg (by omega)

/-- A vertex at Hamming distance `d` is reachable in `d` coordinate steps, or in one antipodal
step followed by `n - d` coordinate steps; the worst `d` gives `⌈n / 2⌉`. -/
theorem diameter_foldedCube (n : ℕ) : (foldedCube (n + 1)).diameter = (n + 2) / 2 := by
  simp only [IsoGraph.foldedCube]
  rw [IsoGraph.diameter_mk]
  set m := n + 1
  set k := (n + 2) / 2
  set hamming : (Fin m → Bool) → (Fin m → Bool) → ℕ :=
    fun x y => (Finset.univ.filter (fun i => x i ≠ y i)).card
  -- Hamming distance 0 means equality
  have hamming_zero_iff : ∀ x y, hamming x y = 0 ↔ x = y := by
    intro x y
    simp only [hamming, Finset.card_eq_zero, Finset.ext_iff]
    constructor
    · intro h
      exact funext fun i => by_contra fun hi =>
        absurd (h i).1 (by simp [hi])
    · intro h; subst h; simp
  -- Coordinate flip edge
  have hflip_adj' : ∀ (v : Fin m → Bool) (i : Fin m),
      (CGraph.foldedCube m).Adj v (fun j => if j = i then !v i else v j) := by
    intro v i
    simp [CGraph.foldedCube_adj]
    refine ⟨fun h => ?_, Or.inl ?_⟩
    · have := congr_fun h i; simp at this
    · show ({i_1 : Fin m | i_1 = i ∧ v i_1 = v i} : Finset _).card = 1
      have : ({i_1 : Fin m | i_1 = i ∧ v i_1 = v i} : Finset _) = {i} := by
        ext j; simp
        exact fun hji => hji ▸ rfl
      rw [this]; simp
  -- Hamming of flipped coordinate (where x i ≠ y i) decreases by 1
  have h_hamming_flip : ∀ (v : Fin m → Bool) (i : Fin m) (y : Fin m → Bool), v i ≠ y i →
      hamming (fun j => if j = i then !v i else v j) y = hamming v y - 1 := by
    intro v i y hne
    simp only [hamming]
    have key : ({j : Fin m | (fun j => if j = i then !v i else v j) j ≠ y j} : Finset _) =
      ({j | v j ≠ y j} : Finset _) \ {i} := by
      ext j
      by_cases hji : j = i
      · subst hji; simp [hne]
      · simp [hji]
    rw [key]
    have hi : i ∈ ({j | v j ≠ y j} : Finset _) := by simp [hne]
    rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hi,
        Finset.card_singleton]
  -- edist ≤ hamming, by induction
  have h_edist_le_hamming : ∀ x y : Fin m → Bool,
      (CGraph.foldedCube m).toSimple.edist x y ≤ (hamming x y : ℕ∞) := by
    intro x y
    have h_edist_le_hamming' : ∀ d : ℕ, (∀ a b : Fin m → Bool, hamming a b = d →
        (CGraph.foldedCube m).toSimple.edist a b ≤ (d : ℕ∞)) := by
      intro d
      induction d using Nat.strong_induction_on with | _ d ih =>
      intro a b hab
      -- Adj is symmetric
      have hamm_symm : ∀ u v, hamming u v = hamming v u := by
        intro u v
        simp only [hamming]
        simp [ne_comm]
      have hadj_symm : ∀ u v, (CGraph.foldedCube m).Adj u v → (CGraph.foldedCube m).Adj v u := by
        intro u v huv
        simp only [CGraph.foldedCube_adj] at huv ⊢
        simp [ne_comm] at huv ⊢
        exact huv
      by_cases hd0 : d = 0
      · have : hamming a b = 0 := by rw [hab, hd0]
        rw [(hamming_zero_iff a b).mp this]
        simp
      · have hd0' : 0 < d := Nat.pos_of_ne_zero hd0
        have : hamming a b > 0 := by omega
        obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
          by_contra h
          push_neg at h
          have : hamming a b = 0 := by
            simp [hamming, h]
          omega
        set aa' := fun j => if j = i then !a i else a j
        have hadj_aa' : (CGraph.foldedCube m).Adj a aa' := by
          exact (hflip_adj' a i).symm ▸ rfl
        have hadj_a'a : (CGraph.foldedCube m).Adj aa' a := hadj_symm _ _ hadj_aa'
        have hham : hamming aa' b = d - 1 := by
          rw [show aa' = (fun j => if j = i then !a i else a j) from rfl]
          rw [h_hamming_flip a i b hi, hab]
        have hgedist1 : (CGraph.foldedCube m).toSimple.edist aa' b ≤ ↑(d - 1) := ih (d -
            1) (Nat.sub_lt hd0' zero_lt_one) aa' b hham
        have hgedist2 : (CGraph.foldedCube m).toSimple.edist aa' a ≤ 1 := by
          have hw : ∃ w : (CGraph.foldedCube m).toSimple.Walk aa' a, w.length = 1 :=
            ⟨SimpleGraph.Walk.cons (hadj_a'a) (SimpleGraph.Walk.nil), by simp⟩
          obtain ⟨w, hw⟩ := hw
          exact le_trans (SimpleGraph.edist_le w) (by rw [hw]; decide)
        calc (CGraph.foldedCube m).toSimple.edist a b
            ≤ (CGraph.foldedCube m).toSimple.edist a aa' + (CGraph.foldedCube
                m).toSimple.edist aa' b :=
              SimpleGraph.edist_triangle
          _ ≤ 1 + ↑(d - 1) := by
              gcongr
              · rw [SimpleGraph.edist_comm]; exact hgedist2
          _ ≤ (d : ℕ∞) := by
              have hadd : (1 : ℕ∞) + ↑(d - 1) = ↑d := by
                have h : 1 + (d - 1) = d := Nat.add_sub_of_le hd0'
                rw [show (1 : ℕ∞) = ↑(1 : ℕ) from rfl, ← Nat.cast_add, h]
              exact hadd.le
    exact h_edist_le_hamming' _ _ _ rfl
  -- Antipode edge: !x is adjacent to x (hamming = m)
  have hflip_all_adj' : ∀ (v : Fin m → Bool),
      (CGraph.foldedCube m).Adj v (fun i => !v i) := by
    intro v
    simp [CGraph.foldedCube_adj]
    exact fun h => by
      have := congr_fun h ⟨0, Nat.zero_lt_of_lt (Nat.succ_pos n)⟩
      simp at this
  -- edist(x, !x) ≤ 1
  have h_edist_flip_all : ∀ (v : Fin m → Bool),
      (CGraph.foldedCube m).toSimple.edist v (fun i => !v i) ≤ 1 := by
    intro v
    have hadj : (CGraph.foldedCube m).toSimple.Adj v (fun i => !v i) := by
      simpa using hflip_all_adj' v
    exact le_trans (SimpleGraph.edist_le (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)) (by simp)
  -- hamming(!x, y) = m - hamming(x, y)
  have h_hamming_flip_all : ∀ (x y : Fin m → Bool),
      hamming (fun i => !x i) y = m - hamming x y := by
    intro x y
    simp only [hamming]
    have hcompl : Finset.univ.filter (fun j => (fun i => !x i) j ≠ y j) =
        Finset.univ \ (Finset.univ.filter (fun j => x j ≠ y j)) := by
      ext j; by_cases h : x j = y j <;> simp [h]
    rw [hcompl, Finset.card_sdiff, Finset.card_univ]
    simp
  -- Upper bound: edist(x,y) ≤ min(hamming(x,y), 1 + (m - hamming(x,y)))
  have h_edist_bound : ∀ (x y : Fin m → Bool),
      (CGraph.foldedCube m).toSimple.edist x y ≤ ((min (hamming x y) (1 + (m - hamming x y)) : ℕ) :
          ℕ∞) := by
    intro x y
    have h1 : (CGraph.foldedCube m).toSimple.edist x y ≤ (hamming x y :
        ℕ∞) := h_edist_le_hamming x y
    have h2 : (CGraph.foldedCube m).toSimple.edist x y ≤ 1 + ((m - hamming x y : ℕ) : ℕ∞) := by
      calc (CGraph.foldedCube m).toSimple.edist x y
          ≤ (CGraph.foldedCube m).toSimple.edist x (fun i => !x i)
            + (CGraph.foldedCube m).toSimple.edist (fun i => !x i) y :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + ((hamming (fun i => !x i) y : ℕ) : ℕ∞) := by
            exact add_le_add (h_edist_flip_all x) (h_edist_le_hamming _ _)
        _ = 1 + ((m - hamming x y : ℕ) : ℕ∞) := by rw [h_hamming_flip_all x y]
    exact le_min h1 (by exact_mod_cast h2)
  -- Lower bound: for the specific pair (all-false, first-k-true), all walks have length ≥ k.
  -- Then edist ≥ k, and combined with edist ≤ k (from upper bound + arithmetic), edist = k for that
  -- pair,
  -- so diameter ≥ k. Combined with diameter ≤ k (from edist ≤ k for all pairs), diameter = k.
  -- Step 1: ediam ≤ k
  have h_ediam_le : (CGraph.foldedCube m).toSimple.ediam ≤ (k : ℕ∞) := by
    apply SimpleGraph.ediam_le_of_edist_le
    intro x y
    have hb := h_edist_bound x y
    -- min(hamming x y, 1 + (m - hamming x y)) ≤ k for all x,y
    have hlim : hamming x y ≤ m := by
      simp only [hamming]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp [Finset.card_univ])
    have : (min (hamming x y) (1 + (m - hamming x y)) : ℕ) ≤ k := by
      simp only [min_le_iff]
      by_cases h : hamming x y ≤ k
      · left; exact h
      · right
        have h2 : k < hamming x y := lt_of_not_ge h
        have hmk : 1 + (m - hamming x y) ≤ k := by
          have h1 : hamming x y ≤ m := hlim
          have h3 : m - hamming x y ≤ k - 1 := by omega
          omega
        exact hmk
    exact_mod_cast hb.trans (WithTop.coe_le_coe.mpr this)
  -- Lower bound: construct x, y with edist(x,y) ≥ k
  -- x = all false, y = first k entries true
  set xf : Fin m → Bool := fun _ => false
  set yf : Fin m → Bool := fun i => if (i.val < k) then true else false
  have h_hamming_xy : hamming xf yf = k := by
    simp only [hamming, xf, yf]
    have hle : k ≤ m := by
      show (n + 2) / 2 ≤ n + 1; omega
    have hfilter : Finset.univ.filter (fun i : Fin m => false ≠ (if (i : ℕ) < k then true else
        false)) =
        Finset.filter (fun i : Fin m => (i : ℕ) < k) Finset.univ := by
      ext i; simp
    rw [hfilter]
    have hfun : ∀ i : Fin m, (i : ℕ) < k ↔ ∃ j : Fin k, Fin.castLE hle j = i := by
      intro i; constructor
      · intro hi; exact ⟨⟨i.val, by omega⟩, Fin.ext (by simp)⟩
      · rintro ⟨j, hj⟩; exact hj.symm ▸ j.isLt
    have hset : Finset.filter (fun i : Fin m => (i : ℕ) < k) Finset.univ =
        Finset.image (fun j : Fin k => Fin.castLE hle j) Finset.univ := by
      ext i; simp [hfun]
    rw [hset, Finset.card_image_of_injective _ (Fin.castLE_injective hle), Finset.card_fin]
  -- Lower bound: all walks from xf to yf have length ≥ k
  -- Key: for each coordinate i, the number of edges flipping coord i (call it flipCount i)
  -- satisfies flipCount i % 2 = (xf i ≠ yf i). Summing over coords where xf≠yf gives ≥ k,
  -- and Σ flipCount i = walk.length + m * (#antipodal edges). Refined argument gives walk.length ≥
  -- k.
  -- classify an edge as coord-edge at i or antipodal
  have h_edge_types : ∀ u v, (CGraph.foldedCube m).toSimple.Adj u v →
      (∃ i, v = fun j => if j = i then !u i else u j) ∨ (v = fun i => !u i) := by
    intro u v hadj
    have hadj' : (CGraph.foldedCube m).Adj u v := by
      simpa [CGraph.toSimple] using hadj
    rw [CGraph.foldedCube_adj] at hadj'
    simp [Bool.and_eq_true] at hadj'
    obtain ⟨hne, hcard⟩ := hadj'
    -- Helper: for Bool, if x ≠ y then !x = y
    have hbool : ∀ (a b : Bool), a ≠ b → b = !a := by decide +revert
    rcases hcard with hcard1 | hcardm
    · -- hamming = 1, exactly one coordinate differs
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
      have him : i ∈ ({j | u j ≠ v j} : Finset _) := by
        rw [hi]
        simp
      refine Or.inl ⟨i, funext fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; rw [if_pos rfl]; exact hbool _ _ (Finset.mem_filter.mp him).2
      · have heq : u j = v j := by
          by_contra hneq
          have hjmem : j ∈ ({j | u j ≠ v j} : Finset _) := by simp [hneq]
          rw [hi] at hjmem
          simp at hjmem
          exact hj hjmem
        rw [if_neg hj, heq]
    · -- hamming = m, all coordinates differ
      right
      funext i
      have hdiff : u i ≠ v i := by
        by_contra h
        have heq : u i = v i := by tauto
        have hne2 : ({j | u j ≠ v j} : Finset _) ≠ Finset.univ := by
          intro h
          have := Finset.ext_iff.mp h i
          simp [heq] at this
        exact absurd (Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne2))
          (by simp [hcardm, Finset.card_univ])
      exact hbool _ _ hdiff
  -- Lower bound: edist xf yf ≥ k
  -- Audit lemma by walk induction
  -- For each walk w from u to v, we extract fc_i(w) = # coord-edges at coord i, and A(w) = #
  -- antipodal edges.
  -- Key: (fc_i(w) + A(w)) % 2 = (if u i ≠ v i then 1 else 0)
  -- And length(w) = Σ_i fc_i(w) + A(w).
  -- From this, for xf→yf, length ≥ k.
  -- We prove this via a joint existence statement.
  have h_audit_exists : ∀ {u v : Fin m → Bool} (w : (CGraph.foldedCube m).toSimple.Walk u v),
      ∃ (fc : Fin m → ℕ) (a : ℕ),
        (∀ i, (fc i + a) % 2 = (if u i ≠ v i then 1 else 0)) ∧
        w.length = (∑ i, fc i) + a := by
    intro u v w
    induction w with
    | nil =>
      exact ⟨fun _ => 0, 0, fun _ => by simp, by simp⟩
    | @cons u' v' w' huv tail ih =>
      obtain ⟨fc_t, a_t, hfc_t, hlen_t⟩ := ih
      have eti := h_edge_types u' v' huv
      rcases eti with ⟨icoord, hvi⟩ | hvi
      · -- coord edge at icoord
        have huniv_icoord : v' icoord ≠ u' icoord := by
          have h := congr_fun hvi icoord; simp at h; simp [h]
        have hsame_all_j : ∀ j ≠ icoord, v' j = u' j := by
          intro j hj; have := congr_fun hvi j; simp [hj] at this; exact this
        -- fc: add 1 to coord icoord; a stays same
        let fc_cons : Fin m → ℕ := fun j => fc_t j + (if j = icoord then 1 else 0)
        refine ⟨fc_cons, a_t, ?_, ?_⟩
        · intro j
          by_cases hji : j = icoord
          · rw [hji]
            simp [fc_cons]
            have hft := hfc_t icoord
            have hvicoord : v' icoord = !u' icoord := by simp [hvi]
            rw [hvicoord] at hft
            simp at hft
            rw [show fc_t icoord + 1 + a_t = (fc_t icoord + a_t) + 1 from
                by omega, Nat.add_mod, hft]
            by_cases heq : u' icoord = w' icoord <;> simp [heq]
          · simp [fc_cons, hji]
            have hvj : v' j = u' j := hsame_all_j j hji
            have hft := hfc_t j
            rw [hvj] at hft
            by_cases heq : u' j = w' j <;> simp [heq] at hft ⊢ <;> exact hft
        · rw [SimpleGraph.Walk.length_cons huv tail, hlen_t]
          have hsum : ∑ j, (fc_t j + (if j = icoord then 1 else 0)) = ∑ j, fc_t j + 1 := by
            rw [Finset.sum_add_distrib]
            simp
          rw [hsum]; omega
      · -- antipodal edge
        have huniv : v' = fun j => !u' j := hvi
        have hfc_t' : ∀ j, (fc_t j + a_t) % 2 = (if u' j = w' j then 1 else 0) := by
          intro j
          have hft := hfc_t j
          rw [huniv] at hft
          rcases beh : u' j with _
          rcases beh2 : w' j with _
          simp [beh, beh2] at hft ⊢
          exact hft
        refine ⟨fc_t, a_t + 1, ?_, ?_⟩
        · intro j
          show (fc_t j + (a_t + 1)) % 2 = if u' j ≠ w' j then 1 else 0
          have hft := hfc_t' j
          rw [show fc_t j + (a_t + 1) = (fc_t j + a_t) + 1 from by omega, Nat.add_mod, hft]
          by_cases heq : u' j = w' j <;> simp [heq]
        · rw [SimpleGraph.Walk.length_cons huv tail, hlen_t]
          ring
  have h_reach : (CGraph.foldedCube m).toSimple.Reachable xf yf := by
    by_contra hno
    have : (CGraph.foldedCube
        m).toSimple.edist xf yf = ⊤ := SimpleGraph.edist_eq_top_of_not_reachable hno
    have hb := h_edist_bound xf yf
    rw [this] at hb
    simp at hb
  -- All walks from xf to yf have length ≥ k
  have h_walk_ge_k : ∀ (w : (CGraph.foldedCube m).toSimple.Walk xf yf), k ≤ w.length := by
    intro w
    obtain ⟨fc, a, hfc, hlen⟩ := h_audit_exists w
    -- For xf (all false) and yf (first k true):
    -- xf i ≠ yf i ↔ (i : ℕ) < k
    have hcond : ∀ i, (xf i ≠ yf i) ↔ ((i : ℕ) < k) := by
      intro i; simp [xf, yf]
    -- hamming xf yf = k, i.e., # of coords where xf ≠ yf is k
    have hfilter_card : (Finset.univ.filter (fun i => xf i ≠ yf i)).card = k := h_hamming_xy
    -- Case split on a % 2
    by_cases ha_even : a % 2 = 0
    · -- A even: for each i with xf i ≠ yf i, fc i is odd ≥ 1
      let S := Finset.univ.filter (fun i => xf i ≠ yf i)
      have hS_card : S.card = k := hfilter_card
      have hfc_ge_one : ∀ i ∈ S, 1 ≤ fc i := by
        intro i hi
        have hfi := hfc i
        have hai : xf i ≠ yf i := Finset.mem_filter.mp hi |>.2
        simp [hai] at hfi
        omega
      have hcard_le_sum : S.card ≤ ∑ i ∈ S, fc i := by
        calc S.card = ∑ i ∈ S, (1 : ℕ) := by simp
          _ ≤ ∑ i ∈ S, fc i := Finset.sum_le_sum hfc_ge_one
      rw [hS_card] at hcard_le_sum
      have : k ≤ w.length := by
        calc k ≤ ∑ i ∈ S, fc i := hcard_le_sum
        _ ≤ ∑ i, fc i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ ∑ i, fc i + a := Nat.le_add_right _ _
        _ = w.length := hlen.symm
      exact this
    · -- A odd: for each i with xf i = yf i (m-k of them), fc i is odd ≥ 1
      have ha_pos : 1 ≤ a := Nat.pos_of_ne_zero fun h => ha_even (by rw [h])
      have hfc_ge_one_odd : ∀ i, xf i = yf i → 1 ≤ fc i := by
        intro i heq
        have hfi := hfc i
        simp [heq] at hfi; omega
      have hcard_eq : (Finset.univ.filter (fun i => xf i = yf i)).card = m - k := by
        have hsum : (Finset.univ.filter (fun i => xf i = yf i)).card +
            (Finset.univ.filter (fun i => xf i ≠ yf i)).card = m := by
          have : (Finset.univ.filter (fun i => xf i = yf i)) ∪
              (Finset.univ.filter (fun i => xf i ≠ yf i)) = Finset.univ := by
            ext i; by_cases hi : xf i = yf i <;> simp [hi]
          rw [← Finset.card_union_of_disjoint
            (Finset.disjoint_filter.mpr (fun _ _ _ => by tauto)), this]
          simp
        rw [hfilter_card] at hsum; omega
      have hsum_odd_ge : ∑ i, fc i ≥ ∑ i ∈ Finset.univ.filter (fun i => xf i = yf i), fc i :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have hcard_le_sum_odd : (Finset.univ.filter (fun i => xf i = yf
          i)).card ≤ ∑ i ∈ Finset.univ.filter (fun i => xf i = yf i), fc i := by
        calc (Finset.univ.filter (fun i => xf i = yf i)).card = ∑ i ∈ Finset.univ.filter (fun i =>
            xf i = yf i), (1 : ℕ) := by simp
          _ ≤ ∑ i ∈ Finset.univ.filter (fun i => xf i = yf i), fc i := Finset.sum_le_sum (fun i hi
              => hfc_ge_one_odd i (Finset.mem_filter.mp hi |>.2))
      rw [hcard_eq] at hcard_le_sum_odd
      have hmk_le : (m : ℕ) - k + 1 ≥ k := by
        show (n + 1) - (n + 2) / 2 + 1 ≥ (n + 2) / 2
        omega
      omega
  have h_edist_ge : (k : ℕ∞) ≤ (CGraph.foldedCube m).toSimple.edist xf yf := by
    apply le_csInf
    · exact ⟨↑(h_reach.some.length), Set.mem_range_self h_reach.some⟩
    · rintro _ ⟨w, rfl⟩
      show (k : ℕ∞) ≤ ↑w.length
      exact WithTop.coe_le_coe.mpr (h_walk_ge_k w)
  have h_edist_eq : (CGraph.foldedCube m).toSimple.edist xf yf = (k : ℕ∞) := by
    apply le_antisymm
    · exact_mod_cast (h_edist_bound xf yf).trans (WithTop.coe_le_coe.mpr (by simp [h_hamming_xy]))
    · exact h_edist_ge
  have h_ediam_ge : (k : ℕ∞) ≤ (CGraph.foldedCube m).toSimple.ediam :=
    h_edist_eq ▸ SimpleGraph.edist_le_ediam
  have h_ediam_eq_nn : (CGraph.foldedCube m).toSimple.ediam = (k : ℕ∞) :=
    le_antisymm h_ediam_le h_ediam_ge
  simp only [CGraph.diameter]
  change (CGraph.foldedCube m).toSimple.diam = k
  rw [SimpleGraph.diam, h_ediam_eq_nn]
  rfl


/-- Vertex-transitive graphs have radius equal to diameter. -/
theorem radius_foldedCube (n : ℕ) : (foldedCube (n + 1)).radius = (n + 2) / 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (by simp), diameter_foldedCube]

/-- The odd folded cube is bipartite with a perfect matching, so half its vertices' worth of
edges cover it. -/
theorem cliqueCoverNum_foldedCube_odd (m : ℕ) :
    (foldedCube (2 * m + 3)).cliqueCoverNum = 2 ^ (2 * m + 2) := by
  have hm : (foldedCube (2 * m + 3)).matchNum = 2 ^ (2 * m + 2) := by
    have := matchNum_foldedCube_odd (m + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) = 2 * m + 2 by ring] at this
    exact this
  have hc := cliqueNum_foldedCube (2 * m)
  have hV : (foldedCube (2 * m + 3)).V = 2 * 2 ^ (2 * m + 2) := by
    rw [V_foldedCube]; ring
  rw [cliqueCoverNum_of_cliqueNum_le_two hc.le (by omega), hV]
  omega

/-- The folded cube is `(n + 3)`-regular on `2ⁿ⁺²` vertices. -/
theorem E_foldedCube (n : ℕ) : (foldedCube (n + 2)).E = 2 ^ (n + 1) * (n + 3) := by
  have h : 2 * (foldedCube (n + 2)).E = 2 * (2 ^ (n + 1) * (n + 3)) := by
    rw [two_mul_E_foldedCube n]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

/-- The odd folded cube is bipartite with a perfect matching, so the vertex cover takes exactly
half of it. -/
theorem coverNum_foldedCube_odd (m : ℕ) :
    (foldedCube (2 * m + 1)).coverNum = 2 ^ (2 * m) := by
  have h1 := indepNum_foldedCube_odd m
  have h2 := coverNum_add_indepNum (foldedCube (2 * m + 1))
  have hV : (foldedCube (2 * m + 1)).V = 2 * 2 ^ (2 * m) := by
    rw [V_foldedCube]; ring
  omega

/-- The folded cube `□ₙ₊₂` is `(n + 3)`-regular on `2ⁿ⁺²` vertices. -/
theorem le_domNum_foldedCube (n : ℕ) :
    2 ^ (n + 2) ≤ (foldedCube (n + 2)).domNum * (n + 4) := by
  have h := V_le_domNum_mul_maxDeg_add_one (foldedCube (n + 2))
  rw [V_foldedCube, maxDeg_foldedCube] at h
  simpa using h

/-- The matching upper bound. -/
theorem domNum_foldedCube_le (n : ℕ) :
    (foldedCube (n + 2)).domNum + n + 3 ≤ 2 ^ (n + 2) := by
  have h := domNum_add_maxDeg_le_V (foldedCube (n + 2))
  rw [V_foldedCube, maxDeg_foldedCube] at h
  omega

theorem le_edgeChromNum_foldedCube (n : ℕ) :
    n + 3 ≤ (foldedCube (n + 2)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (foldedCube (n + 2))
  rwa [maxDeg_foldedCube] at h

theorem edgeChromNum_foldedCube_le (n : ℕ) :
    (foldedCube (n + 2)).edgeChromNum ≤ 2 * n + 5 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (foldedCube (n + 2))
  rw [maxDeg_foldedCube] at h
  omega

@[simp] theorem cliqueCount_foldedCube (n : ℕ) : (foldedCube (n + 3)).cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_foldedCube]; omega)


/-! ### Complements of the folded cube -/

theorem indepNum_compl_foldedCube (n : ℕ) : ((foldedCube (n + 3))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_foldedCube]

theorem maxDeg_compl_foldedCube (n : ℕ) :
    maxDeg ((foldedCube (n + 2))ᶜ) = 2 ^ (n + 2) - 1 - (n + 3) := by
  have h := maxDeg_compl (G := foldedCube (n + 2)) (by rw [V_foldedCube]; positivity)
  rwa [V_foldedCube, minDeg_foldedCube] at h

theorem minDeg_compl_foldedCube (n : ℕ) :
    minDeg ((foldedCube (n + 2))ᶜ) = 2 ^ (n + 2) - 1 - (n + 3) := by
  have h := minDeg_compl (G := foldedCube (n + 2)) (by rw [V_foldedCube]; positivity)
  rwa [V_foldedCube, maxDeg_foldedCube] at h

theorem E_compl_foldedCube (n : ℕ) :
    ((foldedCube (n + 2))ᶜ).E = (2 ^ (n + 2)).choose 2 - 2 ^ (n + 1) * (n + 3) := by
  have h := E_compl (foldedCube (n + 2))
  rw [E_foldedCube, V_foldedCube] at h
  rw [← h, Nat.add_sub_cancel]
/-! ### The line graph of the folded cube -/

theorem E_pos_foldedCube (n : ℕ) : 0 < (foldedCube (n + 2)).E := by
  rw [E_foldedCube]
  positivity

theorem degSequence_foldedCube (n : ℕ) :
    degSequence (foldedCube (n + 2)) = List.replicate (2 ^ (n + 2)) (n + 3) := by
  have h := (isRegularWith_foldedCube n).degSequence
  rwa [V_foldedCube] at h

@[simp] theorem V_lineGraph_foldedCube (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).V = 2 ^ (n + 1) * (n + 3) := by
  rw [V_lineGraph, E_foldedCube]

theorem E_lineGraph_foldedCube (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).E = 2 ^ (n + 2) * (n + 3).choose 2 :=
  E_lineGraph_of_degSequence_replicate (degSequence_foldedCube n)

theorem isRegularWith_lineGraph_foldedCube (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).IsRegularWith (2 * (n + 3) - 2) :=
  isRegularWith_lineGraph (E_pos_foldedCube n) (degSequence_foldedCube n)

theorem maxDeg_lineGraph_foldedCube (n : ℕ) :
    maxDeg (lineGraph (foldedCube (n + 2))) = 2 * (n + 3) - 2 :=
  maxDeg_lineGraph (E_pos_foldedCube n) (degSequence_foldedCube n)

theorem minDeg_lineGraph_foldedCube (n : ℕ) :
    minDeg (lineGraph (foldedCube (n + 2))) = 2 * (n + 3) - 2 :=
  minDeg_lineGraph (E_pos_foldedCube n) (degSequence_foldedCube n)

theorem degSequence_lineGraph_foldedCube (n : ℕ) :
    degSequence (lineGraph (foldedCube (n + 2)))
      = List.replicate (2 ^ (n + 1) * (n + 3)) (2 * (n + 3) - 2) := by
  have h := (isRegularWith_lineGraph_foldedCube n).degSequence
  rwa [V_lineGraph_foldedCube] at h

theorem isConnected_lineGraph_foldedCube (n : ℕ) :
    IsConnected (lineGraph (foldedCube (n + 2))) := by
  have hc : IsConnected (foldedCube (n + 2)) := isConnected_foldedCube (n + 1)
  exact isConnected_lineGraph hc (E_pos_foldedCube n)

theorem numComponents_lineGraph_foldedCube (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).numComponents = 1 := by
  have hc : IsConnected (foldedCube (n + 2)) := isConnected_foldedCube (n + 1)
  exact numComponents_lineGraph hc (E_pos_foldedCube n)

theorem diameter_lineGraph_foldedCube_le (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).diameter ≤ (n + 3) / 2 + 1 := by
  have hc : IsConnected (foldedCube (n + 2)) := isConnected_foldedCube (n + 1)
  have h2 : (foldedCube (n + 2)).diameter = (n + 3) / 2 := diameter_foldedCube (n + 1)
  have h := diameter_lineGraph_le hc (E_pos_foldedCube n)
  omega

theorem radius_lineGraph_foldedCube_le (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).radius ≤ (n + 3) / 2 + 1 := by
  have hc : IsConnected (foldedCube (n + 2)) := isConnected_foldedCube (n + 1)
  have h2 : (foldedCube (n + 2)).radius = (n + 3) / 2 := radius_foldedCube (n + 1)
  have h := radius_lineGraph_le hc (E_pos_foldedCube n)
  omega

theorem cliqueNum_lineGraph_foldedCube (n : ℕ) :
    (lineGraph (foldedCube (n + 2))).cliqueNum = n + 3 := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := foldedCube (n + 2))
    (by rw [maxDeg_foldedCube]; omega)
  rwa [maxDeg_foldedCube] at hm

theorem girth_lineGraph_foldedCube (n : ℕ) : (lineGraph (foldedCube (n + 2))).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_foldedCube]; omega)

theorem not_isBipartite_lineGraph_foldedCube (n : ℕ) :
    ¬ IsBipartite (lineGraph (foldedCube (n + 2))) :=
  not_isBipartite_lineGraph (by rw [maxDeg_foldedCube]; omega)

theorem not_isTree_lineGraph_foldedCube (n : ℕ) : ¬ IsTree (lineGraph (foldedCube (n + 2))) :=
  not_isTree_lineGraph (by rw [maxDeg_foldedCube]; omega)

/-! ### The Mycielskian of the folded cube -/

@[simp] theorem V_mycielskian_foldedCube (n : ℕ) :
    (mycielskian (foldedCube n)).V = 2 * 2 ^ n + 1 := by
  rw [V_mycielskian, V_foldedCube]

theorem E_mycielskian_foldedCube (n : ℕ) :
    (mycielskian (foldedCube (n + 2))).E = 3 * (2 ^ (n + 1) * (n + 3)) + 2 ^ (n + 2) := by
  rw [E_mycielskian, E_foldedCube, V_foldedCube]

theorem maxDeg_mycielskian_foldedCube (n : ℕ) :
    maxDeg (mycielskian (foldedCube (n + 2))) = max (2 * (n + 3)) (2 ^ (n + 2)) := by
  rw [maxDeg_mycielskian, maxDeg_foldedCube, V_foldedCube]

theorem minDeg_mycielskian_foldedCube (n : ℕ) :
    minDeg (mycielskian (foldedCube (n + 2))) = min (n + 4) (2 ^ (n + 2)) := by
  have h := minDeg_mycielskian (foldedCube (n + 2)) (by rw [V_foldedCube]; positivity)
  rw [minDeg_foldedCube, V_foldedCube] at h
  omega

theorem isConnected_mycielskian_foldedCube (n : ℕ) :
    IsConnected (mycielskian (foldedCube (n + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_foldedCube]; omega)

theorem numComponents_mycielskian_foldedCube (n : ℕ) :
    (mycielskian (foldedCube (n + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_foldedCube]; omega)

theorem radius_mycielskian_foldedCube (n : ℕ) :
    (mycielskian (foldedCube (n + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_foldedCube]; omega)

theorem cliqueNum_mycielskian_foldedCube (n : ℕ) :
    (mycielskian (foldedCube (n + 3))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (foldedCube (n + 3)) (by rw [V_foldedCube]; positivity)
  rw [cliqueNum_foldedCube] at h
  omega

theorem four_le_girth_mycielskian_foldedCube (n : ℕ) :
    4 ≤ (mycielskian (foldedCube (n + 3))).girth := by
  have hE : 0 < (foldedCube (n + 3)).E := E_pos_foldedCube (n + 1)
  exact four_le_girth_mycielskian _ (by rw [cliqueNum_foldedCube]) hE

theorem domNum_mycielskian_foldedCube (n : ℕ) :
    (mycielskian (foldedCube n)).domNum = (foldedCube n).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_foldedCube]; positivity)

theorem coverNum_mycielskian_foldedCube_le (n : ℕ) :
    (mycielskian (foldedCube n)).coverNum ≤ 2 ^ n + 1 := by
  have h := coverNum_mycielskian_le (foldedCube n)
  rwa [V_foldedCube] at h

theorem le_indepNum_mycielskian_foldedCube (n : ℕ) :
    2 ^ n ≤ (mycielskian (foldedCube n)).indepNum := by
  have h := V_le_indepNum_mycielskian (foldedCube n)
  rwa [V_foldedCube] at h
/-! ### The Mycielskian of a theta graph -/

@[simp] theorem V_mycielskian_thetaGraph (xs : List ℕ) :
    (mycielskian (thetaGraph xs)).V = 2 * (2 + xs.sum) + 1 := by
  rw [V_mycielskian, V_thetaGraph]

theorem E_mycielskian_thetaGraph (xs : List ℕ) (h : ∀ k ∈ xs, 0 < k) :
    (mycielskian (thetaGraph xs)).E = 3 * (xs.sum + xs.length) + (2 + xs.sum) := by
  rw [E_mycielskian, E_thetaGraph xs h, V_thetaGraph]

theorem domNum_mycielskian_thetaGraph (xs : List ℕ) :
    (mycielskian (thetaGraph xs)).domNum = (thetaGraph xs).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_thetaGraph]; omega)

theorem coverNum_mycielskian_thetaGraph_le (xs : List ℕ) :
    (mycielskian (thetaGraph xs)).coverNum ≤ 2 + xs.sum + 1 := by
  have h := coverNum_mycielskian_le (thetaGraph xs)
  rwa [V_thetaGraph] at h

theorem le_indepNum_mycielskian_thetaGraph (xs : List ℕ) :
    2 + xs.sum ≤ (mycielskian (thetaGraph xs)).indepNum := by
  have h := V_le_indepNum_mycielskian (thetaGraph xs)
  rwa [V_thetaGraph] at h

theorem length_pos_of_ne_nil_thetaGraph {xs : List ℕ} (hne : xs ≠ []) : 0 < xs.length := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons a t => exact Nat.succ_pos _

theorem isConnected_mycielskian_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) : IsConnected (mycielskian (thetaGraph xs)) := by
  refine isConnected_mycielskian _ ?_
  have hl := length_pos_of_ne_nil_thetaGraph hne
  rw [minDeg_thetaGraph_of_all_one h hne]
  omega

theorem numComponents_mycielskian_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) : (mycielskian (thetaGraph xs)).numComponents = 1 := by
  refine numComponents_mycielskian _ ?_
  have hl := length_pos_of_ne_nil_thetaGraph hne
  rw [minDeg_thetaGraph_of_all_one h hne]
  omega

theorem radius_mycielskian_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) : (mycielskian (thetaGraph xs)).radius = 2 := by
  refine radius_mycielskian _ ?_
  have hl := length_pos_of_ne_nil_thetaGraph hne
  rw [minDeg_thetaGraph_of_all_one h hne]
  omega

theorem maxDeg_mycielskian_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) : maxDeg (mycielskian (thetaGraph xs))
      = max (2 * max 2 xs.length) (2 + xs.sum) := by
  rw [maxDeg_mycielskian, maxDeg_thetaGraph_of_all_one h hne, V_thetaGraph]

theorem minDeg_mycielskian_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) : minDeg (mycielskian (thetaGraph xs))
      = min (min (2 * min 2 xs.length) (min 2 xs.length + 1)) (2 + xs.sum) := by
  have hm := minDeg_mycielskian (thetaGraph xs) (by rw [V_thetaGraph]; omega)
  rwa [minDeg_thetaGraph_of_all_one h hne, V_thetaGraph] at hm

/-! ### The grid and the king graph are not vertex-transitive

A grid with at least three rows and three columns has corner vertices of degree `2` and interior
vertices of degree `4`, so it cannot be vertex-transitive; the king graph splits `3` against `8`
in the same way.  Since both have no isolated vertices, arc-transitivity fails too. -/

theorem not_isVertexTransitive_grid (m n : ℕ) :
    ¬ IsVertexTransitive (path (m + 3) □g path (n + 3)) := by
  have hmin : minDeg (path (m + 3) □g path (n + 3)) = 2 := minDeg_grid (m + 1) (n + 1)
  have hmax : maxDeg (path (m + 3) □g path (n + 3)) = 4 := maxDeg_grid m n
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg ?_ (by omega)
  rw [V_grid]
  positivity

theorem not_isArcTransitive_grid (m n : ℕ) :
    ¬ IsArcTransitive (path (m + 3) □g path (n + 3)) := by
  have hmin : minDeg (path (m + 3) □g path (n + 3)) = 2 := minDeg_grid (m + 1) (n + 1)
  exact not_isArcTransitive_of_not_isVertexTransitive (by omega)
    (not_isVertexTransitive_grid m n)

theorem not_isVertexTransitive_king (m n : ℕ) :
    ¬ IsVertexTransitive (path (m + 3) ⊠g path (n + 3)) := by
  have hmin : minDeg (path (m + 3) ⊠g path (n + 3)) = 3 := minDeg_king (m + 1) (n + 1)
  have hmax : maxDeg (path (m + 3) ⊠g path (n + 3)) = 8 := maxDeg_king m n
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg ?_ (by omega)
  rw [V_king]
  positivity

theorem not_isArcTransitive_king (m n : ℕ) :
    ¬ IsArcTransitive (path (m + 3) ⊠g path (n + 3)) := by
  have hmin : minDeg (path (m + 3) ⊠g path (n + 3)) = 3 := minDeg_king (m + 1) (n + 1)
  exact not_isArcTransitive_of_not_isVertexTransitive (by omega)
    (not_isVertexTransitive_king m n)

/-! ### The Turán graph is vertex-transitive only when the parts are equal

`T(n, r)` has parts of sizes `⌈n/r⌉` and `⌊n/r⌋`, so its degrees are `n - ⌊n/r⌋` and `n - ⌈n/r⌉`.
These agree exactly when `r ∣ n`, and in that case the graph is a balanced complete multipartite
graph, which is vertex-transitive.  When `r ∤ n` the two degrees differ by one. -/

theorem div_pred_of_not_dvd {k r : ℕ} (h : ¬ r ∣ (k + 1)) : k / r = (k + 1) / r := by
  rw [Nat.succ_div, if_neg h, Nat.add_zero]

theorem ceilDiv_of_not_dvd {n r : ℕ} (hr : 0 < r) (h : ¬ r ∣ n) :
    (n + r - 1) / r = n / r + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (dvd_zero r) h
    · exact ⟨n - 1, by omega⟩
  have he : k + 1 + r - 1 = k + r := by omega
  have h2 : (k + r) / r = k / r + 1 := Nat.add_div_right k hr
  rw [he, h2, div_pred_of_not_dvd h]

theorem not_isVertexTransitive_turan {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) (h : ¬ r ∣ n) :
    ¬ IsVertexTransitive (turan n r) := by
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · have hr1 : r = 1 := by omega
      subst hr1
      exact absurd (one_dvd n) h
    · exact hge
  have hnpos : 0 < n := by omega
  have hlt : n / r < n := Nat.div_lt_self hnpos hr2
  have hmin : minDeg (turan n r) = n - (n / r + 1) := by
    rw [minDeg_turan hr hn, ceilDiv_of_not_dvd hr h]
  have hmax : maxDeg (turan n r) = n - n / r := maxDeg_turan hr hn
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by rw [V_turan]; omega) ?_
  omega

theorem not_isArcTransitive_turan {n r : ℕ} (hr : 2 ≤ r) (hn : r ≤ n) (h : ¬ r ∣ n) :
    ¬ IsArcTransitive (turan n r) :=
  not_isArcTransitive_of_not_isVertexTransitive (minDeg_turan_pos hr hn)
    (not_isVertexTransitive_turan (by omega) hn h)

/-! ### A theta graph is vertex-transitive only when it is a cycle

With every path of length one the theta graph on `xs` is `K_{2,|xs|}` with the two hubs joined,
whose degrees are `2` and `|xs|`.  These agree only when `|xs| = 2`, the case already recorded as
`isVertexTransitive_thetaGraph_pair`. -/

theorem not_isVertexTransitive_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) (hl : xs.length ≠ 2) : ¬ IsVertexTransitive (thetaGraph xs) := by
  have hp := length_pos_of_ne_nil_thetaGraph hne
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by rw [V_thetaGraph]; omega) ?_
  rw [minDeg_thetaGraph_of_all_one h hne, maxDeg_thetaGraph_of_all_one h hne]
  omega

theorem not_isArcTransitive_thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1)
    (hne : xs ≠ []) (hl : xs.length ≠ 2) : ¬ IsArcTransitive (thetaGraph xs) := by
  have hp := length_pos_of_ne_nil_thetaGraph hne
  refine not_isArcTransitive_of_not_isVertexTransitive ?_
    (not_isVertexTransitive_thetaGraph_of_all_one h hne hl)
  rw [minDeg_thetaGraph_of_all_one h hne]
  omega

/-! ### No Mycielskian of a regular graph is transitive

`μ(G)` keeps the old degrees at `2k` on the copied vertices but gives the apex degree `|V|`, so as
soon as `G` is `k`-regular with `k ≥ 2` the Mycielskian has two different degrees.  The minimum
degree stays positive, so arc-transitivity fails as well. -/

theorem minDeg_mycielskian_pos {G : IsoGraph} (hV : 0 < G.V) (hδ : 0 < G.minDeg) :
    0 < minDeg (mycielskian G) := by
  rw [minDeg_mycielskian G hV]
  omega

theorem not_isArcTransitive_mycielskian {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hk : 2 ≤ k) (hV : 0 < G.V) : ¬ IsArcTransitive (mycielskian G) := by
  refine not_isArcTransitive_of_not_isVertexTransitive ?_
    (not_isVertexTransitive_mycielskian h hk hV)
  refine minDeg_mycielskian_pos hV ?_
  rw [h.minDeg_eq hV]
  omega

theorem not_isArcTransitive_mycielskian_cycle (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (cycle (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_cycle n) (by omega) (by simp)

theorem not_isVertexTransitive_mycielskian_complete (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (complete (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_complete (n + 3)) (by omega)
    (by rw [V_complete]; omega)

theorem not_isArcTransitive_mycielskian_complete (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (complete (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_complete (n + 3)) (by omega)
    (by rw [V_complete]; omega)

theorem not_isVertexTransitive_mycielskian_hypercube (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (hypercube (n + 2))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_hypercube (n + 2)) (by omega)
    (by rw [V_hypercube]; positivity)

theorem not_isArcTransitive_mycielskian_hypercube (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (hypercube (n + 2))) :=
  not_isArcTransitive_mycielskian (isRegularWith_hypercube (n + 2)) (by omega)
    (by rw [V_hypercube]; positivity)

theorem not_isVertexTransitive_mycielskian_petersen :
    ¬ IsVertexTransitive (mycielskian petersen) :=
  not_isVertexTransitive_mycielskian isRegularWith_petersen (by omega)
    (by rw [V_petersen]; omega)

theorem not_isArcTransitive_mycielskian_petersen :
    ¬ IsArcTransitive (mycielskian petersen) :=
  not_isArcTransitive_mycielskian isRegularWith_petersen (by omega)
    (by rw [V_petersen]; omega)

theorem not_isVertexTransitive_mycielskian_prism (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (prism (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_prism n) (by omega)
    (by rw [V_prism]; omega)

theorem not_isArcTransitive_mycielskian_prism (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (prism (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_prism n) (by omega)
    (by rw [V_prism]; omega)

theorem not_isVertexTransitive_mycielskian_cocktailParty (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (cocktailParty (n + 2))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_cocktailParty (n + 2)) (by omega)
    (by rw [V_cocktailParty]; omega)

theorem not_isArcTransitive_mycielskian_cocktailParty (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (cocktailParty (n + 2))) :=
  not_isArcTransitive_mycielskian (isRegularWith_cocktailParty (n + 2)) (by omega)
    (by rw [V_cocktailParty]; omega)

theorem not_isVertexTransitive_mycielskian_crown (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (crown (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_crown (n + 3)) (by omega)
    (by rw [V_crown]; omega)

theorem not_isArcTransitive_mycielskian_crown (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (crown (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_crown (n + 3)) (by omega)
    (by rw [V_crown]; omega)

theorem not_isVertexTransitive_mycielskian_foldedCube (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (foldedCube (n + 2))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_foldedCube n) (by omega)
    (by rw [V_foldedCube]; positivity)

theorem not_isArcTransitive_mycielskian_foldedCube (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (foldedCube (n + 2))) :=
  not_isArcTransitive_mycielskian (isRegularWith_foldedCube n) (by omega)
    (by rw [V_foldedCube]; positivity)

theorem not_isVertexTransitive_mycielskian_bipartite_self (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (bipartite (n + 2) (n + 2))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_bipartite_self (n + 2)) (by omega)
    (by rw [V_bipartite]; omega)

theorem not_isArcTransitive_mycielskian_bipartite_self (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (bipartite (n + 2) (n + 2))) :=
  not_isArcTransitive_mycielskian (isRegularWith_bipartite_self (n + 2)) (by omega)
    (by rw [V_bipartite]; omega)

theorem not_isVertexTransitive_mycielskian_triangular (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (triangular (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_triangular (n + 3)) (by omega)
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))

theorem not_isArcTransitive_mycielskian_triangular (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (triangular (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_triangular (n + 3)) (by omega)
    (by rw [V_triangular]; exact Nat.choose_pos (by omega))
/-! ### Which of the named families are regular

Every family whose minimum and maximum degree are already known can be settled at once: a
`k`-regular graph on a nonempty vertex set has `minDeg = k = maxDeg`, so the two being different
rules out regularity of *every* degree.  The positive entries (`isRegularWith_cycle`,
`isRegularWith_petersen`, …) are already in the library; these are the negative ones. -/

theorem not_isRegularWith_of_minDeg_ne_maxDeg {G : IsoGraph} (hV : 0 < G.V)
    (h : G.minDeg ≠ G.maxDeg) (k : ℕ) : ¬ G.IsRegularWith k := by
  intro hreg
  exact h ((hreg.minDeg_eq hV).trans (hreg.maxDeg_eq hV).symm)

theorem not_isRegularWith_path (n k : ℕ) : ¬ IsRegularWith (path (n + 3)) k := by
  have hmin : minDeg (path (n + 3)) = 1 := minDeg_path (n + 1)
  have hmax : maxDeg (path (n + 3)) = 2 := maxDeg_path n
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_path]; omega) (by omega) k

theorem not_isRegularWith_star (n k : ℕ) : ¬ IsRegularWith (star (n + 2)) k := by
  have hmin : minDeg (star (n + 2)) = 1 := minDeg_star (n + 1)
  have hmax : maxDeg (star (n + 2)) = n + 2 := maxDeg_star (n + 1)
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_star]; omega) (by omega) k

theorem not_isRegularWith_wheel (n k : ℕ) : ¬ IsRegularWith (wheel (n + 4)) k := by
  have hmin : minDeg (wheel (n + 4)) = 3 := minDeg_wheel (n + 1)
  have hmax : maxDeg (wheel (n + 4)) = n + 4 := maxDeg_wheel (n + 1)
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_wheel]; omega) (by omega) k

theorem not_isRegularWith_fan (n k : ℕ) : ¬ IsRegularWith (fan (n + 3)) k := by
  have hmin : minDeg (fan (n + 3)) = 2 := minDeg_fan (n + 1)
  have hmax : maxDeg (fan (n + 3)) = n + 3 := maxDeg_fan n
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_fan]; omega) (by omega) k

theorem not_isRegularWith_book (n k : ℕ) : ¬ IsRegularWith (book (n + 2)) k := by
  have hmin : minDeg (book (n + 2)) = 2 := minDeg_book (n + 1)
  have hmax : maxDeg (book (n + 2)) = n + 3 := maxDeg_book (n + 1)
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_book]; omega) (by omega) k

theorem not_isRegularWith_friendship (n k : ℕ) : ¬ IsRegularWith (friendship (n + 2)) k := by
  have hmin : minDeg (friendship (n + 2)) = 2 := minDeg_friendship (n + 1)
  have hmax : maxDeg (friendship (n + 2)) = 2 * (n + 1) + 2 := maxDeg_friendship (n + 1)
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_friendship]; omega) (by omega) k

theorem not_isRegularWith_grotzsch (k : ℕ) : ¬ grotzsch.IsRegularWith k := by
  have hmin : grotzsch.minDeg = 3 := minDeg_grotzsch
  have hmax : maxDeg grotzsch = 5 := maxDeg_grotzsch
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_grotzsch]; omega) (by omega) k

theorem not_isRegularWith_doubleStar {m n : ℕ} (h : 0 < m + n) (k : ℕ) :
    ¬ IsRegularWith (doubleStar m n) k := by
  have hmin : minDeg (doubleStar m n) = 1 := minDeg_doubleStar m n
  have hmax : maxDeg (doubleStar m n) = max m n + 1 := maxDeg_doubleStar m n
  have hlt : 0 < max m n := by omega
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_doubleStar]; omega) (by omega) k

theorem not_isRegularWith_tadpole (m j k : ℕ) : ¬ IsRegularWith (tadpole (m + 3) (j + 1)) k := by
  have hmin : minDeg (tadpole (m + 3) (j + 1)) = 1 := minDeg_tadpole m j
  have hmax : maxDeg (tadpole (m + 3) (j + 1)) = 3 := maxDeg_tadpole m j
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_tadpole]; omega) (by omega) k

theorem not_isRegularWith_lollipop (m j k : ℕ) :
    ¬ IsRegularWith (lollipop (m + 2) (j + 1)) k := by
  have hmin : minDeg (lollipop (m + 2) (j + 1)) = 1 := minDeg_lollipop m j
  have hmax : maxDeg (lollipop (m + 2) (j + 1)) = m + 2 := maxDeg_lollipop m j
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_lollipop]; omega) (by omega) k

theorem not_isRegularWith_grid (m n k : ℕ) :
    ¬ IsRegularWith (path (m + 3) □g path (n + 3)) k := by
  have hmin : minDeg (path (m + 3) □g path (n + 3)) = 2 := minDeg_grid (m + 1) (n + 1)
  have hmax : maxDeg (path (m + 3) □g path (n + 3)) = 4 := maxDeg_grid m n
  refine not_isRegularWith_of_minDeg_ne_maxDeg ?_ (by omega) k
  rw [V_grid]
  positivity

theorem not_isRegularWith_king (m n k : ℕ) :
    ¬ IsRegularWith (path (m + 3) ⊠g path (n + 3)) k := by
  have hmin : minDeg (path (m + 3) ⊠g path (n + 3)) = 3 := minDeg_king (m + 1) (n + 1)
  have hmax : maxDeg (path (m + 3) ⊠g path (n + 3)) = 8 := maxDeg_king m n
  refine not_isRegularWith_of_minDeg_ne_maxDeg ?_ (by omega) k
  rw [V_king]
  positivity

theorem not_isRegularWith_turan {n r : ℕ} (hr : 0 < r) (hn : r ≤ n) (h : ¬ r ∣ n) (k : ℕ) :
    ¬ IsRegularWith (turan n r) k := by
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · have hr1 : r = 1 := by omega
      subst hr1
      exact absurd (one_dvd n) h
    · exact hge
  have hnpos : 0 < n := by omega
  have hlt : n / r < n := Nat.div_lt_self hnpos hr2
  have hmin : minDeg (turan n r) = n - (n / r + 1) := by
    rw [minDeg_turan hr hn, ceilDiv_of_not_dvd hr h]
  have hmax : maxDeg (turan n r) = n - n / r := maxDeg_turan hr hn
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_turan]; omega) (by omega) k

/-! ### Bipartiteness of the grid and the king graph -/

@[simp] theorem isBipartite_grid (m n : ℕ) : IsBipartite (path (m + 2) □g path (n + 2)) :=
  isBipartite_cartesianProduct (isBipartite_path _) (isBipartite_path _)

theorem not_isBipartite_king (m n : ℕ) : ¬ IsBipartite (path (m + 2) ⊠g path (n + 2)) := by
  have h : (path (m + 2) ⊠g path (n + 2)).chromNum = 4 := chromNum_king m n
  rw [isBipartite_iff_chromNum_le_two, h]
  omega

/-! ### Chromatic indices of the odd-order regular graphs

Each graph here is `k`-regular on an odd number of vertices, so it cannot be `k`-edge-coloured
(a colour class is a matching, and a perfect matching needs an even number of vertices); by
Vizing its chromatic index is therefore exactly `k + 1`.  The lower bounds are already in the
library; the colourings in `CGraph` above supply the matching upper bounds. -/

theorem edgeChromNum_triangular_six : (triangular 6).edgeChromNum = 9 := by
  refine le_antisymm ?_ edgeChromNum_triangular_six_ge
  rw [show (triangular 6 : IsoGraph) = johnson 6 2 from rfl, johnson_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.johnson 6 2)
    CGraph.tri6Col CGraph.tri6Col_symm CGraph.tri6Col_proper

theorem edgeChromNum_triangular_seven : (triangular 7).edgeChromNum = 11 := by
  refine le_antisymm ?_ edgeChromNum_triangular_seven_ge
  rw [show (triangular 7 : IsoGraph) = johnson 7 2 from rfl, johnson_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.johnson 7 2)
    CGraph.tri7Col CGraph.tri7Col_symm CGraph.tri7Col_proper

theorem edgeChromNum_kneser_seven_three : (kneser 7 3).edgeChromNum = 5 := by
  refine le_antisymm ?_ edgeChromNum_kneser_seven_three_ge
  rw [kneser_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.kneser 7 3)
    CGraph.kneser73Col CGraph.kneser73Col_symm CGraph.kneser73Col_proper

theorem edgeChromNum_johnson_seven_three : (johnson 7 3).edgeChromNum = 13 := by
  refine le_antisymm ?_ edgeChromNum_johnson_seven_three_ge
  rw [johnson_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.johnson 7 3)
    CGraph.johnson73Col CGraph.johnson73Col_symm CGraph.johnson73Col_proper

theorem edgeChromNum_rook_three_three : (rook 3 3).edgeChromNum = 5 := by
  refine le_antisymm ?_ (by simpa using edgeChromNum_rook_odd_ge 0 0)
  rw [show (rook 3 3 : IsoGraph) = complete 3 □g complete 3 from rfl, complete_def 3,
    cartesianProduct_mk]
  exact edgeChromNum_mk_le_of_colouring
    (G := CGraph.cartesianProduct (CGraph.complete 3) (CGraph.complete 3))
    CGraph.rook33Col CGraph.rook33Col_symm CGraph.rook33Col_proper

theorem edgeChromNum_paley_thirteen : (paley 13).edgeChromNum = 7 := by
  refine le_antisymm ?_ ?_
  · rw [paley_def]
    exact edgeChromNum_mk_le_of_colouring (G := CGraph.paley 13)
      CGraph.paley13Col CGraph.paley13Col_symm CGraph.paley13Col_proper
  · haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
    have h := edgeChromNum_paley_ge 13 (by norm_num) (by norm_num)
    norm_num at h
    exact h

/-- **The Petersen graph is a snark**: it is cubic but not `3`-edge-colourable. -/
theorem four_le_edgeChromNum_petersen : 4 ≤ petersen.edgeChromNum := by
  rw [edgeChromNum_eq, show (petersen : IsoGraph) = ⟦CGraph.kneser 5 2⟧ from rfl, lineGraph_mk,
    chromNum_mk]
  by_contra hcon
  push_neg at hcon
  obtain ⟨C⟩ := CGraph.chromNum_le_iff_colorable.1 (Nat.lt_succ_iff.1 hcon)
  obtain ⟨e, f, hadj, heq⟩ := CGraph.petersen_no_three_colouring C
  exact C.valid (by simpa using hadj) heq

/-- **The chromatic index of the Petersen graph is four.** -/
@[simp] theorem edgeChromNum_petersen : petersen.edgeChromNum = 4 := by
  refine le_antisymm ?_ four_le_edgeChromNum_petersen
  rw [show (petersen : IsoGraph) = kneser 5 2 from rfl, kneser_def]
  exact edgeChromNum_mk_le_of_colouring (G := CGraph.kneser 5 2)
    CGraph.pet10Col CGraph.pet10Col_symm CGraph.pet10Col_proper

/-- **The Petersen graph has exactly `120` automorphisms.** -/
@[simp] theorem autCount_petersen : petersen.autCount = 120 := by
  rw [show (petersen : IsoGraph) = kneser 5 2 from rfl, kneser_def, autCount_mk]
  exact CGraph.autCount_kneser_five_two

attribute [simp] IsoGraph.girth_cycle IsoGraph.girth_tadpole IsoGraph.girth_cyclePendant

/-- Once the cycle has four or more vertices there is no triangle, so the clique number of a
cycle with pendant paths is two. -/
theorem cliqueNum_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 4) :
    (cyclePendant (m + 4) ks).cliqueNum = 2 := by
  have hg : (cyclePendant (m + 4) ks).girth = m + 4 :=
    girth_cyclePendant (m + 1) ks (by omega)
  refine le_antisymm ?_ (two_le_cliqueNum_of_E_pos ?_)
  · by_contra hc
    push_neg at hc
    have h3 := girth_eq_three_of_cliqueNum (show 3 ≤ (cyclePendant (m + 4) ks).cliqueNum by omega)
    omega
  · rw [E_cyclePendant (m + 1) ks (by omega)]
    omega


/-- **The independence number of a king graph**: `α(Pₘ ⊠ Pₙ) = ⌈m/2⌉ · ⌈n/2⌉`, the kings placed
on every other rank and every other file.  The lower bound is the general
`indepNum_mul_indepNum_le_indepNum_strongProduct` and the upper bound is the `2 × 2` blocking. -/
@[simp] theorem indepNum_king (m n : ℕ) :
    (path m ⊠g path n).indepNum = ((m + 1) / 2) * ((n + 1) / 2) := by
  refine le_antisymm ?_ ?_
  · rw [path_def, path_def, strongProduct_mk, indepNum_mk]
    exact CGraph.indepNum_strongProduct_path_le m n
  · have h := indepNum_mul_indepNum_le_indepNum_strongProduct (path m) (path n)
    rwa [indepNum_path, indepNum_path] at h

/-- **The vertex cover number of a king graph**, by Gallai. -/
@[simp] theorem coverNum_king (m n : ℕ) :
    (path m ⊠g path n).coverNum = m * n - ((m + 1) / 2) * ((n + 1) / 2) := by
  have h := (path m ⊠g path n).coverNum_add_indepNum
  rw [V_strongProduct, V_path, V_path, indepNum_king] at h
  omega

/-- **The domination number of a king graph**: `γ(Pₘ ⊠ Pₙ) = ⌈m/3⌉ · ⌈n/3⌉`, one king per
`3 × 3` block of the board. -/
@[simp] theorem domNum_king (m n : ℕ) :
    (path m ⊠g path n).domNum = ((m + 2) / 3) * ((n + 2) / 3) := by
  rw [path_def, path_def, strongProduct_mk, domNum_mk]
  exact le_antisymm (CGraph.domNum_strongProduct_path_le m n)
    (CGraph.le_domNum_strongProduct_path m n)

/-- **The independence number of a grid**: `α(Pₘ □ Pₙ) = ⌈mn/2⌉`, the larger colour class of the
checkerboard colouring.  The lower bound is `|V| ≤ χ·α` with `χ ≤ 2`, and the upper bound is the
boustrophedon pairing of the board. -/
@[simp] theorem indepNum_grid (m n : ℕ) :
    (path m □g path n).indepNum = (m * n + 1) / 2 := by
  refine le_antisymm ?_ ?_
  · rw [path_def, path_def, cartesianProduct_mk, indepNum_mk]
    exact CGraph.indepNum_cartesianProduct_path_le m n
  · have hb : IsBipartite (path m □g path n) :=
      isBipartite_cartesianProduct (isBipartite_path m) (isBipartite_path n)
    have h := V_le_chromNum_mul_indepNum (path m □g path n)
    rw [V_grid] at h
    have h2 : (path m □g path n).chromNum * (path m □g path n).indepNum
        ≤ 2 * (path m □g path n).indepNum :=
      Nat.mul_le_mul_right _ (isBipartite_iff_chromNum_le_two.1 hb)
    omega

/-- **The vertex cover number of a grid**, by Gallai: `τ = ⌊mn/2⌋`. -/
@[simp] theorem coverNum_grid (m n : ℕ) :
    (path m □g path n).coverNum = m * n / 2 := by
  have h := (path m □g path n).coverNum_add_indepNum
  rw [V_grid, indepNum_grid] at h
  omega

/-- **The matching number of a grid**: `ν(Pₘ □ Pₙ) = ⌊mn/2⌋`, a near-perfect matching along the
boustrophedon Hamiltonian path. -/
@[simp] theorem matchNum_grid (m n : ℕ) : (path m □g path n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (path m □g path n).two_mul_matchNum_le_V
    rw [V_grid] at h
    omega
  · rw [matchNum_eq, path_def, path_def, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_grid m n

/-- **The matching number of a torus**: `ν(Cₘ □ Cₙ) = ⌊mn/2⌋`.  The torus contains the grid, so
it inherits the boustrophedon matching, and `2ν ≤ n` is the matching bound. -/
@[simp] theorem matchNum_cartesianProduct_cycle (m n : ℕ) :
    (cycle m □g cycle n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (cycle m □g cycle n).two_mul_matchNum_le_V
    rw [V_cartesianProduct_cycle] at h
    omega
  · rw [matchNum_eq, cycle_def, cycle_def, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_torus m n

/-- **The matching number of a cylinder**: `ν(Cₘ □ Pₙ) = ⌊mn/2⌋`. -/
@[simp] theorem matchNum_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle m □g path n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (cycle m □g path n).two_mul_matchNum_le_V
    rw [V_cartesianProduct_cycle_path] at h
    omega
  · rw [matchNum_eq, cycle_def, path_def, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_cylinder m n

/-- **The matching number of a king graph**: `ν(Pₘ ⊠ Pₙ) = ⌊mn/2⌋`, the grid's matching again. -/
@[simp] theorem matchNum_king (m n : ℕ) : (path m ⊠g path n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (path m ⊠g path n).two_mul_matchNum_le_V
    rw [V_strongProduct, V_path, V_path] at h
    omega
  · rw [matchNum_eq, path_def, path_def, strongProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_king m n

/-! ## The torus: the independence number -/

/-- **The independence number of a torus with an even side**: `α(Cₘ □ Cₙ) = n · ⌊m/2⌋` as soon as
`n` is even.  The upper bound is the general `indepNum_cartesianProduct_le'` — at most a maximum
independent set of `Cₘ` in each of the `n` columns — and the checkerboard of
`CGraph.le_indepNum_cartesianProduct_cycle` meets it.  The checkerboard fails when both sides are
odd — its last row then neighbours its first with the same parity — and that case is
`indepNum_cartesianProduct_cycle_odd`, by a staircase instead. -/
theorem indepNum_cartesianProduct_cycle_even (m n : ℕ) (hev : n % 2 = 0) :
    (cycle (m + 3) □g cycle n).indepNum = n * ((m + 3) / 2) := by
  refine le_antisymm ?_ ?_
  · have h := indepNum_cartesianProduct_le' (cycle (m + 3)) (cycle n)
    rwa [indepNum_cycle, V_cycle, Nat.mul_comm] at h
  · rw [cycle_def, cycle_def, cartesianProduct_mk, indepNum_mk]
    exact CGraph.le_indepNum_cartesianProduct_cycle (m + 3) n hev

/-- The mirror of `indepNum_cartesianProduct_cycle_even`: `α(Cₘ □ Cₙ) = m · ⌊n/2⌋` when `m` is
even. -/
theorem indepNum_cartesianProduct_cycle_even' (m n : ℕ) (hev : m % 2 = 0) :
    (cycle m □g cycle (n + 3)).indepNum = m * ((n + 3) / 2) := by
  rw [cartesianProduct_comm]
  exact indepNum_cartesianProduct_cycle_even n m hev

/-- **The independence number of a torus with two odd sides**: with `m = 2a + 3 ≤ n = 2b + 3`,
`α(Cₘ □ Cₙ) = n · ⌊m/2⌋ = n(a + 1)`.  The upper bound is again `indepNum_cartesianProduct_le'`,
and `CGraph.le_indepNum_cartesianProduct_cycle_odd` meets it with a staircase: column `j` carries
the `a + 1` residues `w j, w j + 2, …, w j + 2a` of `ℤ/m`, where `w` walks up from `0` to
`a + b + 3` and back down, a closed `±1` walk of length `n` because `m` is odd. -/
theorem indepNum_cartesianProduct_cycle_odd (a b : ℕ) (hab : a ≤ b) :
    (cycle (2 * a + 3) □g cycle (2 * b + 3)).indepNum = (2 * b + 3) * (a + 1) := by
  refine le_antisymm ?_ ?_
  · have h := indepNum_cartesianProduct_le' (cycle (2 * a + 3)) (cycle (2 * b + 3))
    rw [indepNum_cycle, V_cycle] at h
    have he : (2 * a + 3) / 2 = a + 1 := by omega
    rw [he] at h
    exact h.trans_eq (Nat.mul_comm _ _)
  · rw [cycle_def, cycle_def, cartesianProduct_mk, indepNum_mk]
    exact CGraph.le_indepNum_cartesianProduct_cycle_odd a b hab

/-- The mirror of `indepNum_cartesianProduct_cycle_odd`, with the shorter side second. -/
theorem indepNum_cartesianProduct_cycle_odd' (a b : ℕ) (hab : b ≤ a) :
    (cycle (2 * a + 3) □g cycle (2 * b + 3)).indepNum = (2 * a + 3) * (b + 1) := by
  rw [cartesianProduct_comm]
  exact indepNum_cartesianProduct_cycle_odd b a hab

/-- **The vertex cover number of a torus with an even side**, by Gallai: `τ = n·⌈m/2⌉`. -/
theorem coverNum_cartesianProduct_cycle_even (m n : ℕ) (hev : n % 2 = 0) :
    (cycle (m + 3) □g cycle n).coverNum = n * ((m + 4) / 2) := by
  have h := (cycle (m + 3) □g cycle n).coverNum_add_indepNum
  rw [V_cartesianProduct_cycle, indepNum_cartesianProduct_cycle_even m n hev] at h
  rcases Nat.even_or_odd m with hm | hm
  · obtain ⟨k, rfl⟩ := hm
    have h1 : (k + k + 3) / 2 = k + 1 := by omega
    have h2 : (k + k + 4) / 2 = k + 2 := by omega
    rw [h1] at h
    rw [h2]
    nlinarith [h]
  · obtain ⟨k, rfl⟩ := hm
    have h1 : (2 * k + 1 + 3) / 2 = k + 2 := by omega
    have h2 : (2 * k + 1 + 4) / 2 = k + 2 := by omega
    rw [h1] at h
    rw [h2]
    nlinarith [h]

/-- **The vertex cover number of a torus with two odd sides**, by Gallai: `τ = n(a + 2)` when
`m = 2a + 3 ≤ n`. -/
theorem coverNum_cartesianProduct_cycle_odd (a b : ℕ) (hab : a ≤ b) :
    (cycle (2 * a + 3) □g cycle (2 * b + 3)).coverNum = (2 * b + 3) * (a + 2) := by
  have h := (cycle (2 * a + 3) □g cycle (2 * b + 3)).coverNum_add_indepNum
  rw [V_cartesianProduct_cycle, indepNum_cartesianProduct_cycle_odd a b hab] at h
  nlinarith [h]

/-! ## The automorphism group of the hypercube -/

/-- **The automorphism group of the hypercube** is the hyperoctahedral group `Sₙ ⋉ (ℤ/2)ⁿ`, of
order `n! · 2ⁿ`: an automorphism is a coordinate permutation followed by a translation, and no
two distinct such pairs give the same map. -/
@[simp] theorem autCount_hypercube (n : ℕ) :
    (hypercube n).autCount = n.factorial * 2 ^ n := by
  classical
  rw [hypercube, autCount_mk, CGraph.autCount]
  have hbij : Function.Bijective (CGraph.cubeAutOf n) :=
    ⟨CGraph.cubeAutOf_injective n, CGraph.cubeAutOf_surjective n⟩
  have hcard : Nat.card (CGraph.hypercube n ≃cg CGraph.hypercube n) = n.factorial * 2 ^ n := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_perm, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact hcard

end IsoGraph
