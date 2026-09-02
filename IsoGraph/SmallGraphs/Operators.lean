import IsoGraph.SmallGraphs.Mycielskians

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The operators applied to the named families

The unary operators — complement, line graph, Mycielskian — applied to the families that take a
parameter, together with the closed forms that result.  It is also where the gallery is sorted
into the regular and the irregular, and then the regular into the strongly regular and the rest.
-/

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

@[simp] theorem minDeg_completeMultipartite_replicate_succ (m d : ℕ) :
    minDeg (completeMultipartite (List.replicate (m + 2) (d + 1))) = (m + 1) * (d + 1) :=
  minDeg_completeMultipartite_replicate (by omega) (by omega)

theorem E_pos_completeMultipartite_replicate (m d : ℕ) :
    0 < (completeMultipartite (List.replicate (m + 2) (d + 1))).E := by
  rw [E_completeMultipartite_replicate]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (by positivity)

/-! ### The line graph of a balanced complete multipartite graph -/

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

theorem two_mul_E_mycielskian_circulant {n k : ℕ} {S : List ℕ}
    (hk : n * k = 2 * (circulant n S).E) :
    2 * (mycielskian (circulant n S)).E = 3 * (n * k) + 2 * n := by
  rw [E_mycielskian, V_circulant]
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
theorem isRegularWith_foldedCube (n : ℕ) : (foldedCube (n + 2)).IsRegularWith (n + 3) := by
  refine CGraph.isRegularWith_of_card_nbrs _ fun x ↦ ?_
  set xc : Fin (n + 2) → Bool := fun i ↦ !x i with hxc
  have hdist : hammingDist x xc = n + 2 := by
    simpa [Fintype.card_fin] using
      (hammingDist_eq_card_iff (x := x) (y := xc)).2 fun i ↦ by simp [hxc]
  -- the neighbours of `x` are its `n + 2` coordinate flips together with its antipode
  have hnbrs : (CGraph.foldedCube (n + 2)).nbrs x
      = (CGraph.hypercube (n + 2)).nbrs x ∪ {xc} := by
    ext y
    simp only [CGraph.mem_nbrs, Finset.mem_union, Finset.mem_singleton,
      CGraph.foldedCube_adj_hamming, CGraph.hypercube_adj_hamming]
    constructor
    · rintro ⟨-, h1 | hm⟩
      · exact Or.inl h1
      · refine Or.inr (funext fun i ↦ ?_)
        have hne := hammingDist_eq_card_iff.1 (by rw [hm, Fintype.card_fin]) i
        show y i = !x i
        revert hne
        cases x i <;> cases y i <;> simp
    · rintro (h1 | rfl)
      · exact ⟨fun h ↦ by rw [h, hammingDist_self] at h1; omega, Or.inl h1⟩
      · exact ⟨fun h ↦ by simpa [hxc] using congr_fun h ⟨0, by omega⟩, Or.inr hdist⟩
  have hnotin : xc ∉ (CGraph.hypercube (n + 2)).nbrs x := by
    rw [CGraph.mem_nbrs, CGraph.hypercube_adj_hamming, hdist]
    omega
  have hcard_hyper : ((CGraph.hypercube (n + 2)).nbrs x).card = n + 2 := by
    have hreg := IsoGraph.isRegularWith_hypercube (n + 2)
    unfold IsoGraph.hypercube at hreg
    rw [IsoGraph.isRegularWith_mk, CGraph.isRegularWith_iff_forall_degree] at hreg
    rw [CGraph.card_nbrs_eq_degree]
    exact hreg x
  rw [hnbrs, Finset.card_union_of_disjoint, hcard_hyper, Finset.card_singleton]
  exact Finset.disjoint_singleton_right.mpr hnotin

@[simp] theorem minDeg_foldedCube (n : ℕ) : minDeg (foldedCube (n + 2)) = n + 3 :=
  IsRegularWith.minDeg_eq (isRegularWith_foldedCube n) (by simp [V_foldedCube])

/-- **The folded 4-cube is the Clebsch graph**, which is strongly regular and so of diameter two;
Plesník then prices its cheapest cut at the valency.  The other folded cubes have diameter greater
than two and are not settled here. -/
theorem edgeConn_foldedCube_four : (foldedCube 4).edgeConn = 5 :=
  clebsch_srg.edgeConn_eq (by omega) (by omega)

/-- `κ` is not settled the same way — Plesník is a statement about edges — but `μ = 2` says a
separator of the Clebsch graph needs two vertices. -/
theorem two_le_vertexConn_foldedCube_four : 2 ≤ (foldedCube 4).vertexConn :=
  clebsch_srg.mu_le_vertexConn (by omega)

/-- Regularity again, this time through `IsRegularWith.maxDeg_eq`. -/
theorem maxDeg_foldedCube (n : ℕ) : maxDeg (foldedCube (n + 2)) = n + 3 :=
  IsRegularWith.maxDeg_eq (isRegularWith_foldedCube n) (by simp [V_foldedCube])

/-- Handshaking on `isRegularWith_foldedCube`. -/
theorem two_mul_E_foldedCube (n : ℕ) :
    2 * (foldedCube (n + 2)).E = 2 ^ (n + 2) * (n + 3) := by
  rw [IsRegularWith.two_mul_E (isRegularWith_foldedCube n), V_foldedCube]

/-- Take the square through the all-false vector given by flipping coordinate `0`, then `1`, then
`0` again: that bounds the girth by four.  For the matching lower bound, the three sides of a
triangle would each have Hamming length `1` or `n`, and once `n ≥ 3` none of the eight
combinations is consistent. -/
theorem girth_foldedCube (n : ℕ) : (foldedCube (n + 3)).girth = 4 := by
  set m := n + 3 with hmdef
  have hm3 : 3 ≤ m := by omega
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  -- The square through the all-false vector: flip coordinate `0`, then `1`, then `0` again.
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  have hne : i1 ≠ i0 := by simp [hi0, hi1]
  set a : Fin m → Bool := fun _ ↦ false with ha
  set b : Fin m → Bool := Function.update a i0 (!a i0) with hb
  set c : Fin m → Bool := Function.update b i1 (!b i1) with hc
  set d : Fin m → Bool := Function.update c i0 (!c i0) with hd
  have hb0 : b i0 = true := by simp [hb, ha]
  have hb1 : b i1 = false := by simp [hb, ha, Function.update_of_ne hne]
  have hc0 : c i0 = true := by simp [hc, hb0, Function.update_of_ne hne.symm]
  have hc1 : c i1 = true := by simp [hc, hb1]
  have hd0 : d i0 = false := by simp [hd, hc0]
  have hd1 : d i1 = true := by simp [hd, hc1, Function.update_of_ne hne]
  have hab := CGraph.foldedCube_adj_update m a i0
  have hbc := CGraph.foldedCube_adj_update m b i1
  have hcd := CGraph.foldedCube_adj_update m c i0
  have hda : (CGraph.foldedCube m).Adj d a = true := by
    have had : a = Function.update d i1 (!d i1) := by
      funext j
      rcases eq_or_ne j i1 with rfl | hj1
      · simp [ha, hd1]
      · rcases eq_or_ne j i0 with rfl | hj0
        · simp [ha, hd0, Function.update_of_ne hj1]
        · simp [ha, hd, hc, hb, Function.update_of_ne hj1, Function.update_of_ne hj0]
    rw [had]
    exact CGraph.foldedCube_adj_update m d i1
  have hac : a ≠ c := fun h ↦ by
    have h1 : a i1 = c i1 := congrArg (· i1) h
    rw [hc1] at h1
    simp [ha] at h1
  have hbd : b ≠ d := fun h ↦ by simpa [hb0, hd0] using congrArg (· i0) h
  -- Triangle-free: the three pairwise distances are each `1` or `m`, and none of the eight
  -- combinations survives the triangle inequality together with `m ≥ 3`.
  have hnot : ∀ u v : Fin m → Bool, hammingDist u v = m → ∀ i, u i = !v i := fun u v h =>
    hammingDist_eq_card_iff.1 (by rw [h, hcard])
  have htri : ∀ x y z : (CGraph.foldedCube m).V,
      (CGraph.foldedCube m).Adj x y → (CGraph.foldedCube m).Adj y z ->
      (CGraph.foldedCube m).Adj z x → False := by
    intro x y z hxy hyz hzx
    obtain ⟨hxy_ne, hxy_d⟩ := (CGraph.foldedCube_adj_hamming m x y).1 hxy
    obtain ⟨hyz_ne, hyz_d⟩ := (CGraph.foldedCube_adj_hamming m y z).1 hyz
    obtain ⟨hzx_ne, hzx_d⟩ := (CGraph.foldedCube_adj_hamming m z x).1 hzx
    have hxz_d : hammingDist x z = hammingDist z x := hammingDist_comm x z
    have hle : hammingDist x z ≤ m := by
      simpa [hcard] using hammingDist_le_card_fintype (x := x) (y := z)
    rcases hxy_d with h1 | h1 <;> rcases hyz_d with h2 | h2 <;> rcases hzx_d with h3 | h3
    · -- three unit steps: a triangle in the bipartite hypercube
      exact CGraph.not_isBipartite_of_triangle
          ((CGraph.hypercube_adj_hamming m x y).2 h1)
          ((CGraph.hypercube_adj_hamming m x z).2 (hxz_d.trans h3))
          ((CGraph.hypercube_adj_hamming m y z).2 h2)
        (isBipartite_hypercube m)
    · -- two unit steps cannot reach the antipode, since `m ≥ 3`
      have := hammingDist_triangle x y z
      omega
    · -- `y` is the antipode of `z`, so `x` is at distance `m - 1` from `y`, not `1`
      have hxy_eq : hammingDist x y = m - hammingDist x z := by
        have hy : y = fun i ↦ !z i := funext (hnot y z h2)
        rw [hy, hammingDist_not_right, hcard]
      omega
    · -- `y` and `x` are both the antipode of `z`, so `x = y`
      exact hxy_ne (funext fun i ↦ by rw [hnot y z h2 i, hnot x z (hxz_d.trans h3) i])
    · have := hammingDist_triangle x z y
      rw [hammingDist_comm z y] at this
      omega
    · -- `x` is the antipode of `y` and `z` of `x`, so `y = z`
      exact hyz_ne (funext fun i ↦ by rw [hnot z x h3 i, hnot x y h1 i, Bool.not_not])
    · -- `x` is the antipode of `y` and `y` of `z`, so `z = x`
      exact hzx_ne (funext fun i ↦ by rw [hnot x y h1 i, hnot y z h2 i, Bool.not_not])
    · exact hzx_ne (funext fun i ↦ by rw [hnot x y h1 i, hnot y z h2 i, Bool.not_not])
  exact le_antisymm (CGraph.girth_le_four_of_square hab hbc hcd hda hac hbd)
    (CGraph.four_le_girth htri (CGraph.not_isAcyclic_of_square hab hbc hcd hda hac hbd))

theorem cliqueNum_foldedCube (n : ℕ) : (foldedCube (n + 3)).cliqueNum = 2 := by
  have hg := girth_foldedCube n
  have hcl : (foldedCube (n + 3)).cliqueNum ≤ 2 := by
    by_contra h
    push Not at h
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

theorem not_isTree_foldedCube (n : ℕ) : ¬ IsTree (foldedCube (n + 3)) :=
  fun ht ↦ not_isAcyclic_foldedCube n ((isTree_iff_isConnected_and_isAcyclic _).1 ht).2

/-- A folded cube is regular on `2 ^ (n + 2)` vertices, and a regular self-complementary graph has
odd order. -/
theorem not_isSelfComplementary_foldedCube (n : ℕ) :
    ¬ IsSelfComplementary (foldedCube (n + 2)) := by
  intro hs
  have h := hs.odd_V_of_isRegularWith (isRegularWith_foldedCube n)
    (by rw [V_foldedCube]; exact pow_pos (by norm_num) _)
  rw [V_foldedCube] at h
  have h2 := Nat.odd_iff.1 h
  have h3 : 2 ^ (n + 2) = 4 * 2 ^ n := by ring
  omega

/-- A vertex at Hamming distance `d` is reachable in `d` coordinate steps, or in one antipodal
step followed by `n - d` coordinate steps, so no distance exceeds `n / 2` rounded up.  That
bound is attained: a walk between the all-false vector and the first-`(n+2)/2`-true one must
flip each of those coordinates an odd number of times — or, if it uses an odd number of
antipodal edges, each of the remaining ones. -/
@[simp] theorem diameter_foldedCube (n : ℕ) : (foldedCube (n + 1)).diameter = (n + 2) / 2 := by
  simp only [IsoGraph.foldedCube]
  rw [IsoGraph.diameter_mk]
  set m := n + 1 with hm
  set k := (n + 2) / 2 with hk
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  -- One step of the graph costs at most one unit of distance.
  have hstep : ∀ {x y : Fin m → Bool}, (CGraph.foldedCube m).Adj x y = true →
      (CGraph.foldedCube m).toSimple.edist x y ≤ 1 := by
    intro x y h
    have hadj : (CGraph.foldedCube m).toSimple.Adj x y := by simpa [CGraph.toSimple_adj] using h
    exact le_trans (SimpleGraph.edist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)) (by simp)
  -- Flipping the coordinates where `x` and `y` differ, one at a time, is a walk.
  have h_edist_le_hamming : ∀ x y : Fin m → Bool,
      (CGraph.foldedCube m).toSimple.edist x y ≤ (hammingDist x y : ℕ∞) := by
    have key : ∀ d : ℕ, ∀ x y : Fin m → Bool, hammingDist x y = d →
        (CGraph.foldedCube m).toSimple.edist x y ≤ (d : ℕ∞) := by
      intro d
      induction d with
      | zero => intro x y h; rw [hammingDist_eq_zero.1 h]; simp
      | succ d ih =>
        intro x y h
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          by_contra hcon
          push Not at hcon
          rw [funext hcon, hammingDist_self] at h
          omega
        have hd : hammingDist (Function.update x i (!x i)) y = d := by
          rw [hammingDist_update_not_left hi, h]
          omega
        calc (CGraph.foldedCube m).toSimple.edist x y
            ≤ (CGraph.foldedCube m).toSimple.edist x (Function.update x i (!x i))
              + (CGraph.foldedCube m).toSimple.edist (Function.update x i (!x i)) y :=
              SimpleGraph.edist_triangle
          _ ≤ 1 + (d : ℕ∞) :=
              add_le_add (hstep (CGraph.foldedCube_adj_update m x i)) (ih _ _ hd)
          _ = ((d + 1 : ℕ) : ℕ∞) := by rw [Nat.cast_add, Nat.cast_one, add_comm]
    exact fun x y ↦ key _ x y rfl
  -- The antipodal edge turns a long walk into a short one.
  have h_edist_bound : ∀ x y : Fin m → Bool,
      (CGraph.foldedCube m).toSimple.edist x y ≤
        ((min (hammingDist x y) (1 + (m - hammingDist x y)) : ℕ) : ℕ∞) := by
    intro x y
    rcases min_cases (hammingDist x y) (1 + (m - hammingDist x y)) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he]; exact h_edist_le_hamming x y
    · rw [he]
      calc (CGraph.foldedCube m).toSimple.edist x y
          ≤ (CGraph.foldedCube m).toSimple.edist x (fun i ↦ !x i)
            + (CGraph.foldedCube m).toSimple.edist (fun i ↦ !x i) y := SimpleGraph.edist_triangle
        _ ≤ 1 + (hammingDist (fun i ↦ !x i) y : ℕ∞) :=
            add_le_add (hstep (CGraph.foldedCube_adj_not m (by omega) x)) (h_edist_le_hamming _ _)
        _ = ((1 + (m - hammingDist x y) : ℕ) : ℕ∞) := by
            rw [hammingDist_not_left, hcard, Nat.cast_add, Nat.cast_one]
  have hle : ∀ x y : Fin m → Bool, hammingDist x y ≤ m := fun x y ↦ by
    simpa [hcard] using hammingDist_le_card_fintype (x := x) (y := y)
  -- Step 1: every distance is at most `k`.
  have h_ediam_le : (CGraph.foldedCube m).toSimple.ediam ≤ (k : ℕ∞) := by
    refine SimpleGraph.ediam_le_of_edist_le fun x y ↦ (h_edist_bound x y).trans ?_
    refine WithTop.coe_le_coe.mpr ?_
    have := hle x y
    simp only [min_le_iff]
    by_cases h : hammingDist x y ≤ k
    · exact Or.inl h
    · exact Or.inr (by omega)
  -- Step 2: the all-false vector and the first-`k`-true vector are `k` apart.
  set xf : Fin m → Bool := fun _ ↦ false with hxf
  set yf : Fin m → Bool := fun i ↦ decide ((i : ℕ) < k) with hyf
  have hcond : ∀ i : Fin m, xf i ≠ yf i ↔ (i : ℕ) < k := by
    intro i; simp [hxf, hyf]
  have h_hamming_xy : hammingDist xf yf = k := by
    have hlek : k ≤ m := by omega
    simp only [hammingDist]
    rw [show Finset.univ.filter (fun i : Fin m ↦ xf i ≠ yf i) =
        Finset.univ.image (fun j : Fin k ↦ Fin.castLE hlek j) by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hcond]
      exact ⟨fun hi ↦ ⟨⟨i, hi⟩, Fin.ext rfl⟩, fun ⟨j, hj⟩ ↦ hj ▸ j.isLt⟩]
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hlek), Finset.card_fin]
  -- Every walk between them flips each of the first `k` coordinates an odd number of times,
  -- unless it uses an odd number of antipodal edges, in which case it flips each of the other
  -- `m - k` coordinates an odd number of times.
  have hkey : ∀ p q : Bool, (if (!p) ≠ q then 1 else 0) + (if p ≠ q then 1 else 0) = 1 := by
    decide +revert
  have h_audit : ∀ {u v : Fin m → Bool} (w : (CGraph.foldedCube m).toSimple.Walk u v),
      ∃ (fc : Fin m → ℕ) (a : ℕ),
        (∀ i, (fc i + a) % 2 = (if u i ≠ v i then 1 else 0)) ∧
        w.length = (∑ i, fc i) + a := by
    intro u v w
    induction w with
    | nil => exact ⟨fun _ ↦ 0, 0, fun _ ↦ by simp, by simp⟩
    | @cons u' v' t huv tail ih =>
      obtain ⟨fc, a, hfc, hlen⟩ := ih
      have huv' : (CGraph.foldedCube m).Adj u' v' = true := by
        simpa [CGraph.toSimple_adj] using huv
      rcases CGraph.foldedCube_adj_cases huv' with ⟨c, rfl⟩ | rfl
      · refine ⟨fun j ↦ fc j + (if j = c then 1 else 0), a, fun j ↦ ?_, ?_⟩
        · have h := hfc j
          rcases eq_or_ne j c with rfl | hj
          · rw [Function.update_self] at h
            have := hkey (u' j) (t j)
            simp only [ite_true]
            omega
          · rw [Function.update_of_ne hj] at h
            simp only [ite_eq_right hj, Nat.add_zero]
            exact h
        · have hsum : ∑ j, (fc j + if j = c then 1 else 0) = (∑ j, fc j) + 1 := by
            rw [Finset.sum_add_distrib]; simp
          rw [SimpleGraph.Walk.length_cons, hlen, hsum]
          omega
      · refine ⟨fc, a + 1, fun j ↦ ?_, ?_⟩
        · have h : (fc j + a) % 2 = if (!u' j) ≠ t j then 1 else 0 := hfc j
          have := hkey (u' j) (t j)
          omega
        · rw [SimpleGraph.Walk.length_cons, hlen]; ring
  have h_walk_ge_k : ∀ w : (CGraph.foldedCube m).toSimple.Walk xf yf, k ≤ w.length := by
    intro w
    obtain ⟨fc, a, hfc, hlen⟩ := h_audit w
    -- On the coordinates whose parity is odd, `fc` is at least one; there are `k` of them if `a`
    -- is even and `m - k` of them if `a` is odd.
    have hbig : ∀ S : Finset (Fin m), (∀ i ∈ S, 1 ≤ fc i) → S.card + a ≤ w.length := by
      intro S hS
      have h1 : S.card ≤ ∑ i ∈ S, fc i := by
        rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum hS
      have h2 : ∑ i ∈ S, fc i ≤ ∑ i, fc i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      omega
    have hdiff : (Finset.univ.filter fun i ↦ xf i ≠ yf i).card = k := h_hamming_xy
    by_cases ha : a % 2 = 0
    · -- an even number of antipodal steps: each of the `k` differing coordinates is flipped
      have hb := hbig (Finset.univ.filter fun i ↦ xf i ≠ yf i) fun i hi ↦ by
        have h := hfc i
        rw [ite_eq_left (Finset.mem_filter.1 hi).2] at h
        omega
      omega
    · -- an odd number: each of the `m - k` agreeing coordinates is flipped instead
      have hsame : (Finset.univ.filter fun i ↦ ¬ xf i ≠ yf i).card = m - k := by
        rw [show (Finset.univ.filter fun i ↦ ¬ xf i ≠ yf i) =
            (Finset.univ.filter fun i ↦ xf i ≠ yf i)ᶜ by ext i; simp,
          Finset.card_compl, hcard, hdiff]
      have hb := hbig (Finset.univ.filter fun i ↦ ¬ xf i ≠ yf i) fun i hi ↦ by
        have h := hfc i
        rw [ite_eq_right (Finset.mem_filter.1 hi).2] at h
        omega
      omega
  have h_reach : (CGraph.foldedCube m).toSimple.Reachable xf yf := by
    by_contra hno
    have htop := SimpleGraph.edist_eq_top_of_not_reachable hno
    have hb := h_edist_bound xf yf
    rw [htop] at hb
    simp at hb
  have h_edist_eq : (CGraph.foldedCube m).toSimple.edist xf yf = (k : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · exact_mod_cast (h_edist_bound xf yf).trans (WithTop.coe_le_coe.mpr (by simp [h_hamming_xy]))
    · refine le_csInf ⟨↑h_reach.some.length, Set.mem_range_self h_reach.some⟩ ?_
      rintro _ ⟨w, rfl⟩
      exact WithTop.coe_le_coe.mpr (h_walk_ge_k w)
  have h_ediam : (CGraph.foldedCube m).toSimple.ediam = (k : ℕ∞) :=
    le_antisymm h_ediam_le (h_edist_eq ▸ SimpleGraph.edist_le_ediam)
  simp only [CGraph.diameter]
  change (CGraph.foldedCube m).toSimple.diam = k
  rw [SimpleGraph.diam, h_ediam]
  rfl

/-- Vertex-transitive graphs have radius equal to diameter. -/
@[simp] theorem radius_foldedCube (n : ℕ) : (foldedCube (n + 1)).radius = (n + 2) / 2 := by
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

/-- **The first folded cube with a domination number worth naming.**  `□₃` is `K₄,₄`, so one vertex
from each side dominates it, and the two bounds above only give `2 ≤ γ ≤ 3`. -/
@[simp] theorem domNum_foldedCube_three : (foldedCube 3).domNum = 2 := by
  rw [foldedCube_three]
  exact domNum_bipartite 2 2

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

theorem degMultiset_foldedCube (n : ℕ) :
    degMultiset (foldedCube (n + 2)) = Multiset.replicate (2 ^ (n + 2)) (n + 3) :=
  degMultiset_of_degSequence (degSequence_foldedCube n)

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
  rw [V_cartesianProduct, V_path, V_path]
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
  rw [V_strongProduct, V_path, V_path]
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
  rw [V_cartesianProduct, V_path, V_path]
  positivity

theorem not_isRegularWith_king (m n k : ℕ) :
    ¬ IsRegularWith (path (m + 3) ⊠g path (n + 3)) k := by
  have hmin : minDeg (path (m + 3) ⊠g path (n + 3)) = 3 := minDeg_king (m + 1) (n + 1)
  have hmax : maxDeg (path (m + 3) ⊠g path (n + 3)) = 8 := maxDeg_king m n
  refine not_isRegularWith_of_minDeg_ne_maxDeg ?_ (by omega) k
  rw [V_strongProduct, V_path, V_path]
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

theorem not_isRegularWith_ladder (n k : ℕ) : ¬ IsRegularWith (ladder (n + 3)) k := by
  have hmin : minDeg (ladder (n + 3)) = 2 := minDeg_ladder (n + 1)
  have hmax : maxDeg (ladder (n + 3)) = 3 := maxDeg_ladder n
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_ladder]; omega) (by omega) k

/-- A cycle with one pendant edge is the tadpole under another name, and the tadpole is already
known to be irregular. -/
theorem not_isRegularWith_cyclePendant_singleton_one (m k : ℕ) :
    ¬ IsRegularWith (cyclePendant (m + 3) [1]) k := by
  rw [cyclePendant_singleton_one]
  exact not_isRegularWith_tadpole m 0 k

/-- A theta graph all of whose paths have one interior vertex is `K_{2,ℓ}`, which is regular only
when `ℓ = 2`; three or more paths make the two branch vertices the unique vertices of top degree. -/
theorem not_isRegularWith_thetaGraph_replicate_one (m k : ℕ) :
    ¬ IsRegularWith (thetaGraph (List.replicate (m + 3) 1)) k := by
  rw [thetaGraph_of_all_one (by simp), List.length_replicate]
  intro hr
  have hV : 0 < (bipartite 2 (m + 3)).V := by rw [V_bipartite]; omega
  have h1 := hr.minDeg_eq hV
  have h2 := hr.maxDeg_eq hV
  rw [minDeg_bipartite] at h1
  rw [maxDeg_bipartite] at h2
  omega

/-! ### Which of the named families are strongly regular

A strongly regular graph is regular, so every entry in the block above rules out strong regularity
of *any* parameter set at a stroke; that is the bulk of this section.  Two further tests catch the
regular constructions.  A strongly regular graph with `μ > 0` is connected, which disposes of the
disjoint union; and one that is neither complete nor edgeless has diameter exactly two, which
disposes of the hypercube, the crown, the prism and any strong product with a long factor.

What is left over is genuinely strongly regular: the edgeless graph, the complete graph and the
line graph of a complete graph, all read off from constructions already in the library. -/

theorem not_isSRGWith_path (m n k ℓ μ : ℕ) : ¬ (path (m + 3)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_path m k h.isRegularWith

theorem not_isSRGWith_star (m n k ℓ μ : ℕ) : ¬ (star (m + 2)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_star m k h.isRegularWith

theorem not_isSRGWith_wheel (m n k ℓ μ : ℕ) : ¬ (wheel (m + 4)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_wheel m k h.isRegularWith

theorem not_isSRGWith_fan (m n k ℓ μ : ℕ) : ¬ (fan (m + 3)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_fan m k h.isRegularWith

theorem not_isSRGWith_book (m n k ℓ μ : ℕ) : ¬ (book (m + 2)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_book m k h.isRegularWith

theorem not_isSRGWith_friendship (m n k ℓ μ : ℕ) : ¬ (friendship (m + 2)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_friendship m k h.isRegularWith

theorem not_isSRGWith_grotzsch (n k ℓ μ : ℕ) : ¬ grotzsch.IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_grotzsch k h.isRegularWith

theorem not_isSRGWith_doubleStar {a b : ℕ} (hab : 0 < a + b) (n k ℓ μ : ℕ) :
    ¬ (doubleStar a b).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_doubleStar hab k h.isRegularWith

theorem not_isSRGWith_tadpole (m j n k ℓ μ : ℕ) : ¬ (tadpole (m + 3) (j + 1)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_tadpole m j k h.isRegularWith

theorem not_isSRGWith_lollipop (m j n k ℓ μ : ℕ) :
    ¬ (lollipop (m + 2) (j + 1)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_lollipop m j k h.isRegularWith

theorem not_isSRGWith_ladder (m n k ℓ μ : ℕ) : ¬ (ladder (m + 3)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_ladder m k h.isRegularWith

theorem not_isSRGWith_cyclePendant_singleton_one (m n k ℓ μ : ℕ) :
    ¬ (cyclePendant (m + 3) [1]).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_cyclePendant_singleton_one m k h.isRegularWith

theorem not_isSRGWith_thetaGraph_replicate_one (m n k ℓ μ : ℕ) :
    ¬ (thetaGraph (List.replicate (m + 3) 1)).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_thetaGraph_replicate_one m k h.isRegularWith

theorem not_isSRGWith_spider_pair {a b : ℕ} (hab : 2 ≤ a + b) (n k ℓ μ : ℕ) :
    ¬ (spider [a, b]).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_spider_pair hab h.isRegularWith

theorem not_isSRGWith_turan {v r : ℕ} (hr : 0 < r) (hv : r ≤ v) (hd : ¬ r ∣ v) (n k ℓ μ : ℕ) :
    ¬ (turan v r).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_turan hr hv hd k h.isRegularWith

theorem not_isSRGWith_mycielskian {G : IsoGraph} (hV : 0 < G.V) (hd : 2 ≤ G.minDeg)
    (n k ℓ μ : ℕ) : ¬ (mycielskian G).IsSRGWith n k ℓ μ :=
  fun h ↦ not_isRegularWith_mycielskian hV hd h.isRegularWith

/-- **A disjoint union of two nonempty graphs is not strongly regular** for any `μ > 0`: strong
regularity with a positive `μ` forces connectedness. -/
theorem not_isSRGWith_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    {n k ℓ μ : ℕ} (hμ : 0 < μ) : ¬ (G ⊕g H).IsSRGWith n k ℓ μ := by
  intro h
  have hn : 0 < n := by
    have hv := h.V_eq
    rw [V_disjUnion] at hv
    omega
  exact not_isConnected_disjUnion hG hH (h.isConnected hμ hn)

/-- **The hypercube `Qₙ` is not strongly regular for `n ≥ 3`**: its diameter is `n`, and a
strongly regular graph that is neither complete nor edgeless has diameter two. -/
theorem not_isSRGWith_hypercube (m : ℕ) {n k ℓ μ : ℕ} (hμ : 0 < μ) (hk : k + 1 < n) :
    ¬ (hypercube (m + 3)).IsSRGWith n k ℓ μ := by
  intro h
  have hd := h.diameter_eq_two hμ hk
  rw [diameter_hypercube] at hd
  omega

/-- **The crown graph is not strongly regular**: its diameter is three. -/
theorem not_isSRGWith_crown (m : ℕ) {n k ℓ μ : ℕ} (hμ : 0 < μ) (hk : k + 1 < n) :
    ¬ (crown (m + 3)).IsSRGWith n k ℓ μ := by
  intro h
  have hd := h.diameter_eq_two hμ hk
  rw [diameter_crown] at hd
  omega

/-- **The prism `Cₙ □ K₂` is not strongly regular for `n ≥ 4`**: its diameter is `⌊n/2⌋ + 1`. -/
theorem not_isSRGWith_prism (m : ℕ) {n k ℓ μ : ℕ} (hμ : 0 < μ) (hk : k + 1 < n) :
    ¬ (prism (m + 4)).IsSRGWith n k ℓ μ := by
  intro h
  have hd := h.diameter_eq_two hμ hk
  rw [show m + 4 = m + 3 + 1 from by omega, diameter_prism] at hd
  omega

/-- **A strong product with a factor of diameter three or more is not strongly regular**: the
strong product's diameter is the larger of the two. -/
theorem not_isSRGWith_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H)
    (hd : 3 ≤ max G.diameter H.diameter) {n k ℓ μ : ℕ} (hμ : 0 < μ) (hk : k + 1 < n) :
    ¬ (G ⊠g H).IsSRGWith n k ℓ μ := by
  intro h
  have h2 := h.diameter_eq_two hμ hk
  rw [diameter_strongProduct hG hH] at h2
  omega

/-! Three operators that pass an irregular factor's degree spread straight through.  In each case
the operator's minimum and maximum degrees are the *same* expression in `G.minDeg` and `G.maxDeg`,
so `G.minDeg ≠ G.maxDeg` is enough to separate them, and a graph that is not regular is neither
strongly regular nor arc-transitive.  Complementation, which swaps the two ends of the spread
instead of shifting them together, is at the end of the section. -/

/-- **A join with an irregular factor is irregular**: joining adds `H.V` to every degree of `G`. -/
theorem not_isRegularWith_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) (k : ℕ) : ¬ (G ∇g H).IsRegularWith k := by
  have hmin := minDeg_join (G := G) (H := H) hG hH
  have hmax := maxDeg_join (G := G) (H := H) hG hH
  have hle := minDeg_le_maxDeg G
  have hle' := minDeg_le_maxDeg H
  refine not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_join]; omega) ?_ k
  omega

/-- **A blow-up with an irregular base is irregular**: `G ·g H` multiplies `G`'s degrees by
`H.V`. -/
theorem not_isRegularWith_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) (k : ℕ) : ¬ (G ·g H).IsRegularWith k := by
  have hmin := minDeg_lexProduct (G := G) (H := H) hG hH
  have hmax := maxDeg_lexProduct (G := G) (H := H) hG hH
  have hle := minDeg_le_maxDeg G
  have hle' := minDeg_le_maxDeg H
  have hlt : G.minDeg * H.V < G.maxDeg * H.V := mul_lt_mul_of_pos_right (by omega) hH
  refine not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_lexProduct]; exact mul_pos hG hH) ?_ k
  rw [hmin, hmax]
  exact Nat.ne_of_lt (add_lt_add_of_lt_of_le hlt hle')

/-- **A tensor product with an irregular factor is irregular**, as long as the other factor has no
isolated vertex — without that the product can collapse to the edgeless graph. -/
theorem not_isRegularWith_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) (hδ : 0 < H.minDeg) (k : ℕ) : ¬ (G ⊗g H).IsRegularWith k := by
  have hmin := minDeg_tensorProduct (G := G) (H := H) hG hH
  have hmax := maxDeg_tensorProduct (G := G) (H := H) hG hH
  have hle := minDeg_le_maxDeg G
  have hle' := minDeg_le_maxDeg H
  have h2 : G.minDeg < G.maxDeg := by omega
  have hlt : G.minDeg * H.minDeg < G.maxDeg * H.maxDeg :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right h2 hδ) (Nat.mul_le_mul (le_refl G.maxDeg) hle')
  refine not_isRegularWith_of_minDeg_ne_maxDeg
    (by rw [V_tensorProduct]; exact mul_pos hG hH) ?_ k
  rw [hmin, hmax]
  exact Nat.ne_of_lt hlt

theorem not_isSRGWith_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) (n k ℓ μ : ℕ) : ¬ (G ∇g H).IsSRGWith n k ℓ μ :=
  fun hs ↦ not_isRegularWith_join hG hH h k hs.isRegularWith

theorem not_isSRGWith_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) (n k ℓ μ : ℕ) : ¬ (G ·g H).IsSRGWith n k ℓ μ :=
  fun hs ↦ not_isRegularWith_lexProduct hG hH h k hs.isRegularWith

theorem not_isSRGWith_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) (hδ : 0 < H.minDeg) (n k ℓ μ : ℕ) :
    ¬ (G ⊗g H).IsSRGWith n k ℓ μ :=
  fun hs ↦ not_isRegularWith_tensorProduct hG hH h hδ k hs.isRegularWith

/-- **A join with an irregular factor is not arc-transitive.**  An arc-transitive graph with an arc
at all is vertex-transitive, hence regular, and the join inherits `G`'s degree spread. -/
theorem not_isArcTransitive_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : G.minDeg ≠ G.maxDeg) : ¬ IsArcTransitive (G ∇g H) := by
  have hmin := minDeg_join (G := G) (H := H) hG hH
  have hmax := maxDeg_join (G := G) (H := H) hG hH
  have hle := minDeg_le_maxDeg G
  have hle' := minDeg_le_maxDeg H
  refine not_isArcTransitive_of_not_isVertexTransitive (by omega) ?_
  exact not_isVertexTransitive_of_minDeg_ne_maxDeg (by rw [V_join]; omega) (by omega)

/-- **The complement of an irregular graph is not arc-transitive.**  Complementation reverses the
degree spread rather than flattening it; the hypothesis `G.maxDeg + 1 < G.V` only says that the
complement still has an edge to move. -/
theorem not_isArcTransitive_compl {G : IsoGraph} (hV : 0 < G.V) (hΔ : G.maxDeg + 1 < G.V)
    (h : G.minDeg ≠ G.maxDeg) : ¬ IsArcTransitive Gᶜ := by
  have hmin := minDeg_compl (G := G) hV
  have hmax := maxDeg_compl (G := G) hV
  have hle := minDeg_le_maxDeg G
  refine not_isArcTransitive_of_not_isVertexTransitive (by omega) ?_
  exact not_isVertexTransitive_of_minDeg_ne_maxDeg (by rw [V_compl]; omega) (by omega)

/-- **The edgeless graph is strongly regular** with parameters `(n, 0, 0, 0)`: it is the complete
multipartite graph with one part. -/
theorem isSRGWith_empty (n : ℕ) : (empty n).IsSRGWith n 0 0 0 := by
  have h := isSRGWith_completeMultipartite_replicate 1 n
  rw [List.replicate_one, completeMultipartite_singleton] at h
  simpa using h

/-- **The complete graph is strongly regular** with parameters `(n, n-1, n-2, n-1)`: it is the
complete multipartite graph with `n` parts of size one.  The value of `μ` is vacuous — there are
no non-adjacent pairs — and the truncated subtraction gives the same answer as `k`. -/
theorem isSRGWith_complete (n : ℕ) : (complete n).IsSRGWith n (n - 1) (n - 2) (n - 1) := by
  have h := isSRGWith_completeMultipartite_replicate n 1
  rw [completeMultipartite_replicate_one] at h
  simpa using h

theorem isSRGWith_circulant_nil (n : ℕ) : (circulant n []).IsSRGWith n 0 0 0 := by
  rw [circulant_nil]
  exact isSRGWith_empty n

/-- **The line graph of a complete graph is strongly regular**, with the parameters of the
triangular graph `T(n)` that it is. -/
theorem isSRGWith_lineGraph_complete (n : ℕ) (hn : 4 ≤ n) :
    (lineGraph (complete n)).IsSRGWith (n.choose 2) (2 * (n - 2)) (n - 2) 4 := by
  rw [lineGraph_complete_eq_triangular]
  exact isSRGWith_triangular n hn

/-! ### Bipartiteness of the grid and the king graph -/

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
    (G := CGraph.complete 3 □g CGraph.complete 3)
    CGraph.rook33Col CGraph.rook33Col_symm CGraph.rook33Col_proper

theorem edgeChromNum_paley_thirteen : (paley 13).edgeChromNum = 7 := by
  refine le_antisymm ?_ ?_
  · rw [paley_def]
    exact edgeChromNum_mk_le_of_colouring (G := CGraph.paley 13)
      CGraph.paley13Col CGraph.paley13Col_symm CGraph.paley13Col_proper
  · have : Fact (Nat.Prime 13) := ⟨by decide⟩
    have h := edgeChromNum_paley_ge 13 (by norm_num) (by norm_num)
    norm_num at h
    exact h

/-- **The Petersen graph is a snark**: it is cubic but not `3`-edge-colourable.  Three colours are
ruled out on the fifteen vertices of the line graph, by a SAT refutation. -/
theorem four_le_edgeChromNum_petersen : 4 ≤ petersen.edgeChromNum := by
  show 3 < petersen.edgeChromNum
  graph_sat native

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
    push Not at hc
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
    rw [V_cartesianProduct, V_path, V_path] at h
    have h2 : (path m □g path n).chromNum * (path m □g path n).indepNum
        ≤ 2 * (path m □g path n).indepNum :=
      Nat.mul_le_mul_right _ (isBipartite_iff_chromNum_le_two.1 hb)
    omega

/-- **The vertex cover number of a grid**, by Gallai: `τ = ⌊mn/2⌋`. -/
@[simp] theorem coverNum_grid (m n : ℕ) :
    (path m □g path n).coverNum = m * n / 2 := by
  have h := (path m □g path n).coverNum_add_indepNum
  rw [V_cartesianProduct, V_path, V_path, indepNum_grid] at h
  omega

/-- **The matching number of a grid**: `ν(Pₘ □ Pₙ) = ⌊mn/2⌋`, a near-perfect matching along the
boustrophedon Hamiltonian path. -/
@[simp] theorem matchNum_grid (m n : ℕ) : (path m □g path n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (path m □g path n).two_mul_matchNum_le_V
    rw [V_cartesianProduct, V_path, V_path] at h
    omega
  · rw [matchNum_eq, path_def, path_def, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_grid m n

/-- **The matching number of a king graph**: `ν(Pₘ ⊠ Pₙ) = ⌊mn/2⌋`, the grid's matching again. -/
@[simp] theorem matchNum_king (m n : ℕ) : (path m ⊠g path n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (path m ⊠g path n).two_mul_matchNum_le_V
    rw [V_strongProduct, V_path, V_path] at h
    omega
  · rw [matchNum_eq, path_def, path_def, strongProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_king m n

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
