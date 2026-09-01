import IsoGraph.SmallGraphs.Circulants

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Turán graphs, crowns and cocktail party graphs

Turán graphs, friendship graphs and crown graphs.
-/

namespace IsoGraph

/-! ### Turán graphs -/

@[simp] theorem V_turan (n r : ℕ) : (turan n r).V = n := by
  rw [V_completeMultipartite, List.sum_append, List.sum_replicate, List.sum_replicate,
    smul_eq_mul, smul_eq_mul]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have hle : n % r ≤ r := (Nat.mod_lt n hr).le
    calc n % r * (n / r + 1) + (r - n % r) * (n / r)
        = (n % r + (r - n % r)) * (n / r) + n % r := by rw [Nat.add_mul]; ring
      _ = r * (n / r) + n % r := by rw [Nat.add_sub_cancel' hle]
      _ = n := Nat.div_add_mod n r

theorem turan_of_dvd {n r : ℕ} (h : r ∣ n) :
    turan n r = completeMultipartite (List.replicate r (n / r)) := by
  obtain ⟨k, rfl⟩ := h
  simp only [turan, Nat.mul_mod_right, List.replicate_zero, List.nil_append, Nat.sub_zero]

theorem turan_one (n : ℕ) : turan n 1 = empty n := by
  simp only [turan, Nat.mod_one, Nat.div_one, List.replicate_zero, List.nil_append, Nat.sub_zero,
    List.replicate_one, completeMultipartite_singleton]

theorem turan_self (n : ℕ) : turan n n = complete n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [turan]
  · simp only [turan, Nat.mod_self, Nat.div_self hn, List.replicate_zero, List.nil_append,
      Nat.sub_zero, completeMultipartite_replicate_one]

theorem turan_two (n : ℕ) : turan n 2 = bipartite ((n + 1) / 2) (n / 2) := by
  simp only [turan]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega, show (2 * m + 1) / 2 = m by omega]
    simp [List.replicate_succ, completeMultipartite_pair]
  · rw [show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega,
      show (2 * m + 1 + 1) / 2 = m + 1 by omega]
    simp [List.replicate_succ, completeMultipartite_pair]

@[simp] theorem isBipartite_turan_two (n : ℕ) : IsBipartite (turan n 2) := by
  rw [turan_two]
  exact isBipartite_bipartite _ _

@[simp] theorem chromNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) : (turan n r).chromNum = r := by
  have hq : 1 ≤ n / r := (Nat.one_le_div_iff hr).2 h
  have hle : n % r ≤ r := (Nat.mod_lt n hr).le
  have e1 : min (n / r + 1) 1 = 1 := by omega
  have e2 : min (n / r) 1 = 1 := by omega
  rw [chromNum_completeMultipartite, List.map_append, List.map_replicate, List.map_replicate, e1,
    e2, List.sum_append, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul]
  omega

@[simp] theorem cliqueNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) : (turan n r).cliqueNum = r := by
  have hq : 1 ≤ n / r := (Nat.one_le_div_iff hr).2 h
  have hle : n % r ≤ r := (Nat.mod_lt n hr).le
  have e1 : min (n / r + 1) 1 = 1 := by omega
  have e2 : min (n / r) 1 = 1 := by omega
  rw [cliqueNum_completeMultipartite, List.map_append, List.map_replicate, List.map_replicate, e1,
    e2, List.sum_append, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul]
  omega

/-! ### Friendship graphs -/

@[simp] theorem V_friendship (n : ℕ) : (friendship n).V = 2 * n + 1 := by
  simp [V_join]
  omega

@[simp] theorem E_friendship (n : ℕ) : (friendship n).E = 3 * n := by
  simp
  omega

theorem friendship_eq_join_compl_cocktailParty (n : ℕ) :
    friendship n = complete 1 ∇g (cocktailParty n)ᶜ := by
  rw [compl_cocktailParty]

@[simp] theorem indepNum_friendship (n : ℕ) : (friendship n).indepNum = max n 1 := by
  rw [friendship_eq_join_compl_cocktailParty, indepNum_join, indepNum_compl,
    cliqueNum_cocktailParty, indepNum_complete]
  omega

/-- **Independent sets of the friendship graph**: apart from the hub and the empty set, an
independent set picks at most one endpoint from each of the `n` triangles, so there are
`2ᵏ (n choose k)` of size `k ≥ 2`. -/
theorem indepCount_friendship (n k : ℕ) :
    (friendship n).indepCount (k + 2) = 2 ^ (k + 2) * n.choose (k + 2) := by
  rw [friendship_eq_join_compl_cocktailParty, indepCount_join, indepCount_compl,
    indepCount_complete, Nat.zero_add, cliqueCount_completeMultipartite_replicate]

@[simp] theorem friendship_zero : friendship 0 = complete 1 := by
  rw [friendship, cartesianProduct_comm, cartesianProduct_empty_zero, join_empty_zero]

theorem friendship_one : friendship 1 = complete 3 := by
  rw [friendship, cartesianProduct_comm, cartesianProduct_empty_one, join_complete]

@[simp] theorem chromNum_friendship (n : ℕ) : (friendship (n + 1)).chromNum = 3 := by
  rw [friendship_eq_join_compl_cocktailParty, chromNum_join, ← cliqueCoverNum_eq,
    cliqueCoverNum_cocktailParty, chromNum_complete]

@[simp] theorem cliqueNum_friendship (n : ℕ) : (friendship (n + 1)).cliqueNum = 3 := by
  rw [friendship_eq_join_compl_cocktailParty, cliqueNum_join, cliqueNum_compl,
    indepNum_cocktailParty, cliqueNum_complete]

/-- **The friendship graph has one triangle per blade.**  The blades are the edges of a perfect
matching, and joining the hub to a matching turns each edge into a triangle. -/
@[simp] theorem cliqueCount_friendship (n : ℕ) : (friendship n).cliqueCount 3 = n := by
  have hM : (empty n □g complete 2).cliqueCount 3 = 0 :=
    cliqueCount_three_eq_zero_of_isBipartite
      (isBipartite_cartesianProduct (isBipartite_empty n) isBipartite_complete_two)
  rw [show friendship n = complete 1 ∇g (empty n □g complete 2) from rfl,
    cliqueCount_join_three, hM]
  simp

@[simp] theorem cliqueCoverNum_friendship (n : ℕ) :
    (friendship (n + 1)).cliqueCoverNum = n + 1 := by
  rw [friendship_eq_join_compl_cocktailParty, cliqueCoverNum_join, cliqueCoverNum_complete,
    cliqueCoverNum_eq, compl_compl, chromNum_cocktailParty]
  omega

@[simp] theorem coverNum_friendship (n : ℕ) : (friendship (n + 1)).coverNum = n + 2 := by
  have h := coverNum_add_indepNum (friendship (n + 1))
  rw [indepNum_friendship, V_friendship] at h
  omega

@[simp] theorem isConnected_friendship (n : ℕ) : IsConnected (friendship (n + 1)) :=
  isConnected_join (by rw [V_complete]; omega) (by simp)

@[simp] theorem numComponents_friendship (n : ℕ) : (friendship (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_friendship n)

@[simp] theorem girth_friendship (n : ℕ) : (friendship (n + 1)).girth = 3 :=
  girth_join_right (by rw [V_complete]; omega) (by simp)

@[simp] theorem not_isBipartite_friendship (n : ℕ) : ¬ IsBipartite (friendship (n + 1)) :=
  not_isBipartite_of_girth_eq_three (girth_friendship n)

@[simp] theorem not_isAcyclic_friendship (n : ℕ) : ¬ IsAcyclic (friendship (n + 1)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_friendship]; omega)

@[simp] theorem not_isTree_friendship (n : ℕ) : ¬ IsTree (friendship (n + 1)) :=
  not_isTree_of_girth_pos (by rw [girth_friendship]; omega)

@[simp] theorem domNum_friendship (n : ℕ) : (friendship n).domNum = 1 :=
  (domNum_join_eq_one_iff _ _).2 (Or.inl (domNum_complete 0))

@[simp] theorem radius_friendship (n : ℕ) : (friendship (n + 1)).radius = 1 :=
  (radius_eq_one_iff_domNum_eq_one (by rw [V_friendship]; omega)).2 (domNum_friendship _)

/-- The complement of a cocktail party graph is a perfect matching, so it is one-regular. -/
theorem isRegularWith_compl_cocktailParty (n : ℕ) :
    (cocktailParty (n + 1))ᶜ.IsRegularWith 1 := by
  have h := (isRegularWith_cocktailParty (n + 1)).compl
  rwa [V_cocktailParty, show 2 * (n + 1) - 1 - (2 * (n + 1) - 2) = 1 by omega] at h

@[simp] theorem maxDeg_friendship (n : ℕ) : maxDeg (friendship (n + 1)) = 2 * n + 2 := by
  rw [friendship_eq_join_compl_cocktailParty,
    maxDeg_join (by rw [V_complete]; omega) (by rw [V_compl, V_cocktailParty]; omega),
    (isRegularWith_compl_cocktailParty n).maxDeg_eq (by rw [V_compl, V_cocktailParty]; omega),
    maxDeg_complete, V_complete, V_compl, V_cocktailParty]
  omega

@[simp] theorem minDeg_friendship (n : ℕ) : minDeg (friendship (n + 1)) = 2 := by
  rw [friendship_eq_join_compl_cocktailParty,
    minDeg_join (by rw [V_complete]; omega) (by rw [V_compl, V_cocktailParty]; omega),
    (isRegularWith_compl_cocktailParty n).minDeg_eq (by rw [V_compl, V_cocktailParty]; omega),
    minDeg_complete, V_complete, V_compl, V_cocktailParty]
  omega

@[simp] theorem diameter_friendship (n : ℕ) : (friendship (n + 2)).diameter = 2 := by
  rw [friendship_eq_join_compl_cocktailParty]
  refine diameter_join_right (by rw [V_complete]; omega) ?_
  rw [E_compl_eq, V_compl]
  refine Nat.sub_lt (Nat.choose_pos ?_) ?_
  · rw [V_cocktailParty]; omega
  · rw [E_cocktailParty]; exact Nat.mul_pos (by omega) (by omega)

/-! ### Crown graphs -/

@[simp] theorem V_crown (n : ℕ) : (crown n).V = 2 * n := by
  rw [V_tensorProduct, V_complete, V_complete]
  omega

@[simp] theorem E_crown (n : ℕ) : (crown n).E = 2 * n.choose 2 := by
  rw [E_tensorProduct, E_complete, E_complete]
  simp

theorem crown_two : crown 2 = complete 2 ⊕g complete 2 := tensorProduct_complete_two_two

theorem crown_three : crown 3 = cycle 6 := by
  rw [crown, tensorProduct_comm, ← cycle_three, tensorProduct_complete_two_cycle_three]

@[simp] theorem isBipartite_crown (n : ℕ) : IsBipartite (crown n) :=
  isBipartite_tensorProduct_right isBipartite_complete_two

@[simp] theorem isVertexTransitive_crown (n : ℕ) : IsVertexTransitive (crown n) :=
  (isVertexTransitive_complete n).tensorProduct (isVertexTransitive_complete 2)

/-- **The crown graph is arc-transitive**: it is `K_n ⊗g K_2`, and a tensor product of
arc-transitive graphs is arc-transitive. -/
@[simp] theorem isArcTransitive_crown (n : ℕ) : IsArcTransitive (crown n) :=
  (isArcTransitive_complete n).tensorProduct (isArcTransitive_complete 2)

@[simp] theorem isRegularWith_crown (n : ℕ) : (crown n).IsRegularWith (n - 1) := by
  have h := (isRegularWith_complete n).tensorProduct (isRegularWith_complete 2)
  rwa [show (2 : ℕ) - 1 = 1 from rfl, Nat.mul_one] at h

@[simp] theorem cliqueNum_crown (n : ℕ) : (crown (n + 2)).cliqueNum = 2 := by
  rw [crown, cliqueNum_tensorProduct, cliqueNum_complete, cliqueNum_complete]
  omega

@[simp] theorem chromNum_crown (n : ℕ) : (crown (n + 2)).chromNum = 2 := by
  rw [crown, tensorProduct_comm]
  exact chromNum_tensorProduct_eq_two isBipartite_complete_two
    (by rw [E_complete]; exact Nat.choose_pos (by omega))
    (by rw [E_complete]; exact Nat.choose_pos (by omega))

/-! ### The fan's degree sequence, and the radius of a line graph -/

@[simp] theorem degSequence_fan (n : ℕ) :
    degSequence (fan (n + 3)) = [2, 2] ++ List.replicate (n + 1) 3 ++ [n + 3] := by
  rw [degSequence_eq_sort, fan, degMultiset_join, degMultiset_complete, degMultiset_path]
  simp [V_path]
  -- List.Pairwise for the target
  have hle1 : ∀ x ∈ List.replicate (n + 1) 3 ++ [n + 3], 2 ≤ x := by
    simp [List.mem_append, List.mem_replicate]
  have hle2 : List.Pairwise (· ≤ ·) (List.replicate (n + 1) 3 ++ [n + 3]) := by
    rw [List.pairwise_append]
    exact ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_singleton _ _,
      fun x hx y hy => by simp at hx hy; omega⟩
  have hpairwise : (2 :: 2 :: (List.replicate (n + 1) 3 ++ [n + 3])).Pairwise (· ≤ ·) := by
    rw [List.pairwise_cons]
    simp
    exact hle2
  have hmultiset : ((2 :: 2 :: (List.replicate (n + 1) 3 ++ [n + 3]) : List ℕ) : Multiset ℕ) =
    (2 ::ₘ 2 ::ₘ 3 ::ₘ (n + 3) ::ₘ Multiset.replicate n 3 : Multiset ℕ) := by
    have heq : ∀ (l : List ℕ) (a : ℕ), Multiset.count a (↑l : Multiset ℕ) = List.count a l := by
      intro l a; induction l with
      | nil => simp
      | cons b l ih => simp
    apply Multiset.ext.mpr
    intro a
    simp [heq]
    simp [List.count_cons, List.count_append, List.count_replicate]
    simp [Multiset.count_cons, Multiset.count_replicate]
    rcases eq_or_ne a 2 with ha2 | ha2 <;> rcases eq_or_ne a 3 with ha3 | ha3 <;>
      rcases eq_or_ne a (n + 3) with ha4 | ha4 <;> simp [ha2, ha3, ha4, eq_comm] <;>
      first
        | omega
        | (split_ifs; all_goals omega)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba ↦ le_antisymm hab hba)
    (Multiset.pairwise_sort _ (· ≤ ·)) hpairwise
    (Multiset.coe_eq_coe.mp (by rw [Multiset.sort_eq, hmultiset]))

@[simp] theorem degMultiset_fan (n : ℕ) :
    degMultiset (fan (n + 3))
      = (n + 3) ::ₘ (Multiset.replicate 2 2 + Multiset.replicate (n + 1) 3) := by
  rw [← coe_degSequence, degSequence_fan]
  exact Multiset.coe_eq_coe.2 (List.perm_append_singleton _ _)

/-! ### Turán graphs, the balanced case -/

@[simp] theorem E_turan_of_dvd {n r : ℕ} (h : r ∣ n) :
    (turan n r).E = r.choose 2 * (n / r * (n / r)) := by
  rw [turan_of_dvd h, E_completeMultipartite_replicate]

theorem isRegularWith_turan_of_dvd {n r : ℕ} (h : r ∣ n) :
    (turan n r).IsRegularWith ((r - 1) * (n / r)) := by
  rw [turan_of_dvd h]
  exact isRegularWith_of_degSequence (degSequence_completeMultipartite_replicate r (n / r))

theorem isConnected_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 2 ≤ r) (hd : 1 ≤ n / r) :
    IsConnected (turan n r) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  obtain ⟨d, hdeq⟩ : ∃ d, n / (m + 2) = d + 1 := ⟨n / (m + 2) - 1, by omega⟩
  rw [turan_of_dvd h, hdeq]
  exact isConnected_completeMultipartite_replicate m d

theorem diameter_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 2 ≤ r) (hd : 2 ≤ n / r) :
    (turan n r).diameter = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  obtain ⟨d, hdeq⟩ : ∃ d, n / (m + 2) = d + 2 := ⟨n / (m + 2) - 2, by omega⟩
  rw [turan_of_dvd h, hdeq, diameter_completeMultipartite_replicate]

theorem domNum_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 2 ≤ r) (hd : 2 ≤ n / r) :
    (turan n r).domNum = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  obtain ⟨d, hdeq⟩ : ∃ d, n / (m + 2) = d + 2 := ⟨n / (m + 2) - 2, by omega⟩
  rw [turan_of_dvd h, hdeq, domNum_completeMultipartite_replicate]

theorem matchNum_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 2 ≤ r) (hd : 1 ≤ n / r) :
    (turan n r).matchNum = n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  obtain ⟨d, hdeq⟩ : ∃ d, n / (m + 2) = d + 1 := ⟨n / (m + 2) - 1, by omega⟩
  have hn : (m + 2) * (d + 1) = n := by
    rw [← hdeq]; exact Nat.mul_div_cancel' h
  rw [turan_of_dvd h, hdeq, matchNum_completeMultipartite_replicate, hn]

theorem indepNum_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 0 < r) :
    (turan n r).indepNum = n / r := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [turan_of_dvd h, indepNum_completeMultipartite, List.max?_replicate]
  simp

@[simp] theorem coverNum_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 0 < r) :
    (turan n r).coverNum = n - n / r := by
  have hc := coverNum_add_indepNum (turan n r)
  rw [indepNum_turan_of_dvd h hr, V_turan] at hc
  have : n / r ≤ n := Nat.div_le_self n r
  omega

/-! ### Turán graphs with at least three parts -/

@[simp] theorem girth_turan {n r : ℕ} (hr : 3 ≤ r) (h : r ≤ n) : (turan n r).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_turan (by omega) h]; omega)

@[simp] theorem not_isBipartite_turan {n r : ℕ} (hr : 3 ≤ r) (h : r ≤ n) :
    ¬ IsBipartite (turan n r) :=
  not_isBipartite_of_girth_eq_three (girth_turan hr h)

@[simp] theorem not_isAcyclic_turan {n r : ℕ} (hr : 3 ≤ r) (h : r ≤ n) :
    ¬ IsAcyclic (turan n r) :=
  not_isAcyclic_of_girth_pos (by rw [girth_turan hr h]; omega)

@[simp] theorem not_isTree_turan {n r : ℕ} (hr : 3 ≤ r) (h : r ≤ n) : ¬ IsTree (turan n r) :=
  not_isTree_of_girth_pos (by rw [girth_turan hr h]; omega)

/-- **A Turán graph with at least two parts is not self-complementary**: with `r ≤ n` none of the
`r` parts is empty, so the graph is a join and its complement falls apart. -/
theorem not_isSelfComplementary_turan {n r : ℕ} (h2 : 2 ≤ r) (hr : r ≤ n) :
    ¬ IsSelfComplementary (turan n r) := by
  have hmod : n % r < r := Nat.mod_lt _ (by omega)
  have hdiv : 1 ≤ n / r := (Nat.one_le_div_iff (by omega)).2 hr
  rw [turan]
  refine not_isSelfComplementary_completeMultipartite ?_ ?_
  · rw [List.length_append, List.length_replicate, List.length_replicate]
    omega
  · intro d hd
    rcases List.mem_append.1 hd with h | h
    · rw [List.eq_of_mem_replicate h]; omega
    · rw [List.eq_of_mem_replicate h]; omega

/-! ### More crown graphs -/

@[simp] theorem crown_zero : crown 0 = empty 0 := by
  rw [crown, complete_zero, tensorProduct_comm, tensorProduct_empty, V_complete]

@[simp] theorem crown_one : crown 1 = empty 2 := by
  rw [crown, complete_one, tensorProduct_comm, tensorProduct_empty, V_complete]

/-! ### Independence and matching for the new families -/

theorem indepNum_crown (n : ℕ) : (crown (n + 2)).indepNum = n + 2 := by
  apply le_antisymm
  · -- Upper bound: indepNum ≤ n + 2
    have hvt := isVertexTransitive_crown (n + 2)
    have hclique := cliqueNum_crown n
    have hcard := V_crown (n + 2)
    have h := indepNum_mul_cliqueNum_le_V hvt
    rw [hclique, hcard] at h
    omega
  · -- Lower bound: n + 2 ≤ indepNum
    have htensor : crown (n + 2) = complete (n + 2) ⊗g complete 2 := rfl
    rw [htensor]
    have := V_mul_indepNum_le_indepNum_tensorProduct (complete (n + 2)) (complete 2)
    rw [V_complete, indepNum_complete] at this
    simp at this
    omega

/-- **The crown `K_n × K_2` has a perfect matching**: pair `(i, 0)` with `(i + 1, 1)`; consecutive
first coordinates differ and the second coordinates differ, so each pair is an edge of the tensor
product, and the `n + 2` pairs are disjoint. -/
theorem matchNum_crown (n : ℕ) : (crown (n + 2)).matchNum = n + 2 := by
  refine le_antisymm ?_ ?_
  · have h1 := two_mul_matchNum_le_V (crown (n + 2))
    rw [V_crown] at h1
    omega
  · show n + 2 ≤ (IsoGraph.complete (n + 2) ⊗g IsoGraph.complete 2).matchNum
    rw [IsoGraph.complete, IsoGraph.complete, tensorProduct_mk, matchNum_mk]
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun i : Fin (n + 2) ↦ (i, (⟨0, by omega⟩ : Fin 2)))
      (fun i : Fin (n + 2) ↦ (i + 1, (⟨1, by omega⟩ : Fin 2))) ?_ ?_)
    · intro i
      rw [CGraph.tensorProduct_adj]
      simp
    · intro i j hij
      refine ⟨fun h ↦ hij (congrArg Prod.fst h), fun h ↦ ?_, fun h ↦ ?_, fun h ↦ hij ?_⟩
      · have := congrArg (fun q ↦ (Prod.snd q).val) h
        simp at this
      · have := congrArg (fun q ↦ (Prod.snd q).val) h
        simp at this
      · have h1 : (i + 1 : Fin (n + 2)) = j + 1 := congrArg Prod.fst h
        simpa using h1

/-- **The friendship graph has a near-perfect matching**: take one edge from each of the `n`
triangles, namely the rung `(i, 0) — (i, 1)` of the `i`-th copy of `K₂`. The hub is left over. -/
theorem matchNum_friendship (n : ℕ) : (friendship n).matchNum = n := by
  refine le_antisymm ?_ ?_
  · have h := (friendship n).two_mul_matchNum_le_V
    rw [V_friendship] at h
    omega
  · show n ≤ (IsoGraph.complete 1 ∇g IsoGraph.empty n □g IsoGraph.complete 2).matchNum
    rw [IsoGraph.complete, IsoGraph.complete, IsoGraph.empty, cartesianProduct_mk, join_mk,
      matchNum_mk]
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun i : Fin n ↦ Sum.inr (i, (⟨0, by omega⟩ : Fin 2)))
      (fun i : Fin n ↦ Sum.inr (i, (⟨1, by omega⟩ : Fin 2))) ?_ ?_)
    · intro i
      rw [CGraph.join_adj_inr_inr, CGraph.cartesianProduct_adj]
      simp
    · intro i j hij
      have hne : ∀ a b : Fin 2, ∀ k l : Fin n, k ≠ l →
          (Sum.inr (k, a) : (CGraph.complete 1).V ⊕ ((CGraph.empty n).V × (CGraph.complete 2).V)) ≠
            Sum.inr (l, b) := by
        intro a b k l hkl h
        exact hkl (congrArg Prod.fst (Sum.inr.inj h))
      exact ⟨hne _ _ _ _ hij, hne _ _ _ _ hij, hne _ _ _ _ hij, hne _ _ _ _ hij⟩

@[simp] theorem indepNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    (turan n r).indepNum = (n + r - 1) / r := by
  unfold turan
  simp [indepNum_completeMultipartite]
  set a := n / r
  set k := n % r
  have max_rep : ∀ (x n : ℕ), (List.replicate (n + 1) x).max? = some x := by
    intro x n; induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.max?_cons, ih]; simp
  have hmax0 : ∀ (p a : ℕ), p > 0 →
      ((List.replicate 0 (a + 1) ++ List.replicate p a).max?.getD 0 = a) := by
    intro p a hp
    simp [List.replicate_zero, List.nil_append]
    obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [max_rep, Option.getD_some]
  have hmax : ∀ (k p : ℕ) (a : ℕ),
      k > 0 → ((List.replicate k (a + 1) ++ List.replicate p a).max?.getD 0 = a + 1) := by
    intro k p a hk
    induction k with
    | zero => omega
    | succ k ih =>
      have : List.replicate (k + 1) (a + 1) ++ List.replicate p a =
          (a + 1) :: (List.replicate k (a + 1) ++ List.replicate p a) := by
        rw [List.replicate_succ, List.cons_append]
      rw [this, List.max?_cons]
      simp [Option.getD_some]
      rcases L : (List.replicate k (a + 1) ++ List.replicate p a).max? with _ | x
      · simp
      · have hx_mem : x ∈ List.replicate k (a + 1) ++ List.replicate p a := by
          exact List.max?_mem L
        have hx_le : x ≤ a + 1 := by
          rw [List.mem_append] at hx_mem
          rcases hx_mem with hx_mem | hx_mem
          · have := List.mem_replicate.mp hx_mem; omega
          · have := List.mem_replicate.mp hx_mem; omega
        rw [Option.elim_some]
        rw [max_eq_left hx_le]
  -- Helper: (r * q + r - 1) / r = q when r > 0
  have turan_dep_zero : ∀ (q : ℕ), (r * q + r - 1) / r = q := by
    intro q
    have hge : q * r ≤ r * q + r - 1 := by
      rw [mul_comm]
      exact Nat.le_sub_one_of_lt (by omega)
    have hlt : r * q + r - 1 < r * (q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.sub_lt_self (by positivity) (by omega)
    exact le_antisymm (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hlt))
      (Nat.le_div_iff_mul_le hr |>.mpr (by omega))
  -- Helper: (r * q + r + (m-1)) / r = q + 1 when 1 ≤ m < r
  have turan_dep_pos : ∀ (q m : ℕ), 1 ≤ m → m < r → (r * q + r + (m - 1)) / r = q + 1 := by
    intro q m hm_pos hm_lt
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
    have hge : (q + 1) * r ≤ r * q + r + (m - 1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q r]
      omega
    have hm1_lt_r : m - 1 < r := by omega
    have hlt : r * q + r + (m - 1) < r * (q + 2) := by
      show r * q + r + (m - 1) < r * q + r + r
      omega
    exact le_antisymm (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hlt))
      (Nat.le_div_iff_mul_le hr |>.mpr (by omega))
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- k = 0, so r ∣ n
    have hdam : r * a + k = n := Nat.div_add_mod n r
    rw [hk0, add_zero] at hdam
    rw [← hdam, hk0]
    simp
    have : (List.replicate r a).max?.getD 0 = a := by
      obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      rw [max_rep, Option.getD_some]
    rw [this]
    rw [turan_dep_zero a]
  · -- k > 0
    rw [hmax k (r - k) a hk0]
    set q := n / r
    set m := n % r
    have hdam : r * q + m = n := Nat.div_add_mod n r
    have hm_pos : 1 ≤ m := hk0
    have hm_lt : m < r := Nat.mod_lt n hr
    have hdiv_rhs : n + r - 1 = r * q + r + (m - 1) := by
      rw [show n = r * q + m from hdam.symm]
      omega
    rw [hdiv_rhs]
    rw [turan_dep_pos q m hm_pos hm_lt]

/-- **The Turán graph on an odd number of vertices and two parts is not Hamiltonian.**  Its two
parts are `m` and `m + 1`, so the larger one is an independent set on more than half the graph,
and a spanning cycle would have to alternate between the parts.  For every other `T(n, r)` with
`3 ≤ n` and `2 ≤ r` the parts are balanced enough and the graph *is* Hamiltonian, but that
direction needs the cycle and is not proved here. -/
theorem not_isHamiltonian_turan_two {m : ℕ} (hm : 1 ≤ m) :
    ¬ (turan (2 * m + 1) 2).IsHamiltonian :=
  not_isHamiltonian_of_V_lt_two_mul_indepNum (by rw [V_turan]; omega)
    (by rw [V_turan, indepNum_turan (by omega) (by omega)]; omega)

/-- **Independent sets of a Turán graph stay inside one part**, and the parts come in only two
sizes: `n % r` of them hold `n / r + 1` vertices and the rest hold `n / r`. -/
@[simp] theorem indepCount_turan (n r k : ℕ) :
    (turan n r).indepCount (k + 1)
      = n % r * (n / r + 1).choose (k + 1) + (r - n % r) * (n / r).choose (k + 1) := by
  unfold turan
  rw [indepCount_completeMultipartite, List.map_append, List.map_replicate, List.map_replicate,
    List.sum_append, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul]

@[simp] theorem coverNum_crown (n : ℕ) : (crown (n + 2)).coverNum = n + 2 := by
  have h := coverNum_add_indepNum (crown (n + 2))
  rw [indepNum_crown, V_crown] at h
  omega

@[simp] theorem coverNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    (turan n r).coverNum = n - (n + r - 1) / r := by
  have hc := coverNum_add_indepNum (turan n r)
  rw [indepNum_turan hr h, V_turan] at hc
  omega

theorem isConnected_crown (n : ℕ) : IsConnected (crown (n + 3)) := by
  simp only [crown, IsoGraph.complete, tensorProduct_mk, IsoGraph.isConnected_mk]
  have hna : 3 ≤ n + 3 := by omega
  set i0 : Fin (n+3) := ⟨0, by omega⟩
  set i1 : Fin (n+3) := ⟨1, by omega⟩
  set i2 : Fin (n+3) := ⟨2, by omega⟩
  have hi0_ne_i1 : i0 ≠ i1 := by simp [i0, i1]
  have hi0_ne_i2 : i0 ≠ i2 := by simp [i0, i2]
  have hi1_ne_i2 : i1 ≠ i2 := by simp [i1, i2]
  have hi1_ne_i0 : i1 ≠ i0 := hi0_ne_i1.symm
  have hi2_ne_i0 : i2 ≠ i0 := hi0_ne_i2.symm
  have hi2_ne_i1 : i2 ≠ i1 := hi1_ne_i2.symm
  -- Adjacency in tensor product: CGraph.Adj = true ↔ i≠j ∧ b≠c
  have hadj_true : ∀ (i j : Fin (n+3)) (b c : Fin 2),
      i ≠ j ∧ b ≠ c →
        ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).Adj (i, b) (j, c) = true := by
    intro i j b c h
    rw [CGraph.tensorProduct_adj, CGraph.complete_adj, CGraph.complete_adj]
    simp [h]
  -- One-hop reachability from adjacency
  have hreach_one : ∀ {u v : Fin (n+3) × Fin 2},
      ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).Adj u v = true →
        SimpleGraph.Reachable
          ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).toSimple u v := by
    intro u v huv
    have : ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).toSimple.Adj u v :=
      (CGraph.toSimple_adj _ _ _).mpr huv
    exact this.reachable
  unfold CGraph.IsConnected
  have : Nonempty ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).V :=
    Nonempty.intro ((i0, (0 : Fin 2)) : Fin (n+3) × Fin 2)
  apply SimpleGraph.Connected.mk
  · -- All vertices reachable from (i0, 0)
    have hreach_to_base : ∀ (i : Fin (n+3)) (b : Fin 2),
        SimpleGraph.Reachable ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).toSimple
          (i, b) (i0, (0 : Fin 2)) := by
      intro i b
      fin_cases b
      · -- b = 0
        by_cases hi : i = i0
        · subst hi; exact SimpleGraph.Reachable.refl _
        · exact (hreach_one (hadj_true i i0 0 1 ⟨hi, by decide⟩)).trans
            ((hreach_one (hadj_true i0 i1 1 0 ⟨hi0_ne_i1, by decide⟩)).trans
              ((hreach_one (hadj_true i1 i2 0 1 ⟨hi1_ne_i2, by decide⟩)).trans
                (hreach_one (hadj_true i2 i0 1 0 ⟨hi2_ne_i0, by decide⟩))))
      · -- b = 1
        by_cases hi : i = i0
        · subst hi
          exact (hreach_one (hadj_true i0 i1 1 0 ⟨hi0_ne_i1, by decide⟩)).trans
              ((hreach_one (hadj_true i1 i2 0 1 ⟨hi1_ne_i2, by decide⟩)).trans
                (hreach_one (hadj_true i2 i0 1 0 ⟨hi2_ne_i0, by decide⟩)))
        · exact hreach_one (hadj_true i i0 1 0 ⟨hi, by decide⟩)
    intro u v
    obtain ⟨i, b⟩ := u
    obtain ⟨j, c⟩ := v
    exact (hreach_to_base i b).trans (hreach_to_base j c).symm

@[simp] theorem numComponents_crown (n : ℕ) : (crown (n + 3)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_crown n)

theorem crown_eq_compl_rook (n : ℕ) : crown n = (rook n 2)ᶜ := (compl_rook n 2).symm

@[simp] theorem compl_crown (n : ℕ) : (crown n)ᶜ = rook n 2 := by
  rw [crown_eq_compl_rook, compl_compl]

theorem cliqueCoverNum_crown (n : ℕ) : (crown (n + 2)).cliqueCoverNum = n + 2 := by
  rw [cliqueCoverNum_eq, crown, ← compl_rook, compl_compl]
  have : (n + 2 : ℕ) = (n + 1) + 1 := by omega
  have : (2 : ℕ) = (1 : ℕ) + 1 := by omega
  rw [‹(n + 2 : ℕ) = (n + 1) + 1›, ‹(2 : ℕ) = (1 : ℕ) + 1›]
  rw [chromNum_rook]
  omega

theorem girth_crown (n : ℕ) : (crown (n + 4)).girth = 4 := by
  rw [crown, complete_def, complete_def, tensorProduct_mk, girth_mk]
  set G := CGraph.complete (n + 4)
  set H := CGraph.complete 2
  -- Helper lemmas about adj in complete graphs
  have hG_adj : ∀ (i j : Fin (n + 4)), i ≠ j → G.Adj i j := fun i j hij => by
    rw [CGraph.complete_adj]; exact decide_eq_true_eq.mpr hij
  have hG_not_adj_self : ∀ (i : Fin (n + 4)), ¬G.Adj i i := fun i => by
    rw [CGraph.complete_adj]; simp
  have hG01 : G.Adj (0 : Fin (n + 4)) (1 : Fin (n + 4)) := hG_adj _ _ (by simp)
  have hne12 : (1 : Fin (n + 4)) ≠ (2 : Fin (n + 4)) := by
    intro h
    exact absurd (Fin.ext_iff.mp h)
      (by simp [Nat.mod_eq_of_lt (by omega : 1 < n+4),
        Nat.mod_eq_of_lt (by omega : 2 < n+4)])
  have hne23 : (2 : Fin (n + 4)) ≠ (3 : Fin (n + 4)) := by
    intro h
    exact absurd (Fin.ext_iff.mp h)
      (by simp [Nat.mod_eq_of_lt (by omega : 2 < n+4),
        Nat.mod_eq_of_lt (by omega : 3 < n+4)])
  have hne30 : (3 : Fin (n + 4)) ≠ (0 : Fin (n + 4)) := by
    intro h
    exact absurd (Fin.ext_iff.mp h)
      (by simp [Nat.mod_eq_of_lt (by omega : 3 < n+4),
        Nat.mod_eq_of_lt (by omega : 0 < n+4)])
  have h02 : (0 : Fin (n + 4)) ≠ (2 : Fin (n + 4)) := by
    intro h
    exact absurd (Fin.ext_iff.mp h)
      (by simp [Nat.mod_eq_of_lt (by omega : 0 < n+4),
        Nat.mod_eq_of_lt (by omega : 2 < n+4)])
  have h13 : (1 : Fin (n + 4)) ≠ (3 : Fin (n + 4)) := by
    intro h
    exact absurd (Fin.ext_iff.mp h)
      (by simp [Nat.mod_eq_of_lt (by omega : 1 < n+4),
        Nat.mod_eq_of_lt (by omega : 3 < n+4)])
  have hG12 : G.Adj (1 : Fin (n + 4)) (2 : Fin (n + 4)) := hG_adj _ _ hne12
  have hG23 : G.Adj (2 : Fin (n + 4)) (3 : Fin (n + 4)) := hG_adj _ _ hne23
  have hG30 : G.Adj (3 : Fin (n + 4)) (0 : Fin (n + 4)) := hG_adj _ _ hne30
  have hH01 : H.Adj (0 : Fin 2) (1 : Fin 2) := by
    rw [CGraph.complete_adj]; decide
  have hH10 : H.Adj (1 : Fin 2) (0 : Fin 2) := by
    rw [CGraph.complete_adj]; decide
  -- The four vertices of our 4-cycle
  let v0 : G.V × H.V := ((0 : Fin (n + 4)), (0 : Fin 2))
  let v1 : G.V × H.V := ((1 : Fin (n + 4)), (1 : Fin 2))
  let v2 : G.V × H.V := ((2 : Fin (n + 4)), (0 : Fin 2))
  let v3 : G.V × H.V := ((3 : Fin (n + 4)), (1 : Fin 2))
  have hv0v1 : (G.tensorProduct H).Adj v0 v1 := by
    dsimp only [v0, v1]
    rw [CGraph.tensorProduct_adj]; simp [hG01, hH01]
  have hv1v2 : (G.tensorProduct H).Adj v1 v2 := by
    dsimp only [v1, v2]
    rw [CGraph.tensorProduct_adj]; simp [hG12, hH10]
  have hv2v3 : (G.tensorProduct H).Adj v2 v3 := by
    dsimp only [v2, v3]
    rw [CGraph.tensorProduct_adj]; simp [hG23, hH01]
  have hv3v0 : (G.tensorProduct H).Adj v3 v0 := by
    dsimp only [v3, v0]
    rw [CGraph.tensorProduct_adj]; simp [hG30, hH10]
  have hv0v2 : v0 ≠ v2 := by
    intro h; have := congrArg Prod.fst h; exact absurd this h02
  have hv1v3 : v1 ≠ v3 := by
    intro h; have := congrArg Prod.fst h; exact absurd this h13
  apply le_antisymm
  · exact CGraph.girth_le_four_of_square hv0v1 hv1v2 hv2v3 hv3v0 hv0v2 hv1v3
  · exact CGraph.four_le_girth_of_isBipartite
      (CGraph.IsBipartite.tensorProduct_right
        ⟨fun i => if i.val = 0 then false else true,
        fun i j hij => by
          rw [CGraph.complete_adj] at hij
          -- `fin_cases` names the vertices through the graph's own `FinEnum`, as
          -- `equiv.symm 0` and `equiv.symm 1`; `decide` finishes what `simp_all` cannot see
          fin_cases i <;> fin_cases j <;> simp_all <;> decide⟩)
      (CGraph.not_isAcyclic_of_square hv0v1 hv1v2 hv2v3 hv3v0 hv0v2 hv1v3)

@[simp] theorem maxDeg_crown (n : ℕ) : maxDeg (crown (n + 2)) = n + 1 := by
  rw [(isRegularWith_crown (n + 2)).maxDeg_eq (by rw [V_crown]; omega)]
  omega

@[simp] theorem minDeg_crown (n : ℕ) : minDeg (crown (n + 2)) = n + 1 := by
  rw [(isRegularWith_crown (n + 2)).minDeg_eq (by rw [V_crown]; omega)]
  omega

/-- Two adjacent vertices dominate a crown graph: they lie in different halves of the
bipartition and between them see every other vertex, while no vertex is universal. -/
@[simp] theorem domNum_crown (n : ℕ) : (crown (n + 2)).domNum = 2 := by
  show IsoGraph.domNum (complete (n + 2) ⊗g complete 2) = 2
  dsimp only [IsoGraph.complete]
  rw [tensorProduct_mk, IsoGraph.domNum_mk]
  -- Upper bound: {(0,0), (0,1)} dominates
  have hdom : (CGraph.complete (n + 2) ⊗g CGraph.complete 2).IsDominatingSet
      {((0 : Fin (n+2)), (0 : Fin 2)), ((0 : Fin (n+2)), (1 : Fin 2))} := by
    intro ⟨a, b⟩
    simp only [CGraph.tensorProduct_adj, Finset.mem_insert, Finset.mem_singleton,
      CGraph.complete_adj]
    -- b : Fin 2 (definitionally)
    have hb : b = (0 : Fin 2) ∨ b = (1 : Fin 2) := Fin.exists_fin_two.mp ⟨b, rfl⟩
    rcases hb with rfl | rfl
    · simp
      by_cases ha : a = (0 : Fin (n+2))
      · left; left; exact Prod.ext ha (by rfl)
      · right; exact fun h => ha h.symm
    · simp
      by_cases ha : a = (0 : Fin (n+2))
      · left; right; exact Prod.ext ha (by rfl)
      · right; exact fun h => ha h.symm
  -- Upper bound: domNum ≤ 2
  have hle : (CGraph.complete (n + 2) ⊗g CGraph.complete 2).domNum ≤ 2 :=
    CGraph.domNum_le_card_of_isDominatingSet hdom
  -- Lower bound: no universal vertex, so domNum ≠ 1
  have hno_univ : ¬ ∃ v : (CGraph.complete (n + 2) ⊗g CGraph.complete 2).V, ∀ u, u ≠ v →
        (CGraph.complete (n + 2) ⊗g CGraph.complete 2).Adj v u := by
    rintro ⟨vv, hv⟩
    set a := vv.1
    set b := vv.2
    set b' : Fin 2 :=
      if b = (⟨0, by omega⟩ : Fin 2) then (⟨1, by omega⟩ : Fin 2) else (⟨0, by omega⟩ : Fin 2)
    set w : (CGraph.complete (n + 2) ⊗g CGraph.complete 2).V := (a, b')
    have hbne : b' ≠ b := by
      have hb_cases : b = (⟨0, by omega⟩ : Fin 2) ∨ b = (⟨1, by omega⟩ : Fin 2) :=
        Fin.exists_fin_two.mp ⟨b, rfl⟩
      rcases hb_cases with h | h <;> simp [b', h]
      exact Fin.ne_of_val_ne (by decide)
    have hne : w ≠ vv := fun h =>
      hbne (by have := congr_arg Prod.snd h; dsimp [w, b'] at this; exact this)
    have hadj := hv w hne
    simp [CGraph.tensorProduct_adj, CGraph.complete_adj, w, b'] at hadj
    exact absurd hadj.1 (by simp [a])
  have hnot1 :
      ¬ (CGraph.complete (n + 2) ⊗g CGraph.complete 2).domNum = 1 := by
    rw [CGraph.domNum_eq_one_iff]; exact hno_univ
  -- domNum > 0
  let G'' : CGraph := CGraph.complete (n + 2) ⊗g CGraph.complete 2
  have hpos : 0 < G''.domNum :=
    @CGraph.domNum_pos G'' (by
      show 0 < FinEnum.card G''.V
      simp [G'', CGraph.card_complete])
  rw [show (CGraph.complete (n + 2) ⊗g CGraph.complete 2) = G'' from rfl]
    at hle hnot1 ⊢
  omega

@[simp] theorem not_isAcyclic_crown (n : ℕ) : ¬ IsAcyclic (crown (n + 4)) :=
  not_isAcyclic_of_girth_pos (by rw [girth_crown]; omega)

@[simp] theorem not_isTree_crown (n : ℕ) : ¬ IsTree (crown (n + 4)) :=
  not_isTree_of_girth_pos (by rw [girth_crown]; omega)

/-- Any two vertices of a crown graph are at distance at most three, and the two ends of a
removed matching edge realise that bound. -/
theorem diameter_crown (n : ℕ) : (crown (n + 3)).diameter = 3 := by
  rw [crown, complete_def, complete_def, tensorProduct_mk, diameter_mk]
  have hadj : ∀ (i j : Fin (n + 3)) (x y : Fin 2),
      (CGraph.complete (n + 3) ⊗g CGraph.complete 2).toSimple.Adj (i, x) (j, y) ↔
        i ≠ j ∧ x ≠ y := by
    intro i j x y
    simp [CGraph.toSimple_adj, CGraph.tensorProduct_adj, CGraph.complete_adj]
  -- Three or more rows means we can always dodge one or two of them.
  have hpick1 : ∀ i j : Fin (n + 3), ∃ k : Fin (n + 3), k ≠ i ∧ k ≠ j := by
    intro i j
    have h : ∃ c : ℕ, c < n + 3 ∧ c ≠ i.1 ∧ c ≠ j.1 := by
      by_cases hi0 : i.1 = 0
      · by_cases hj1 : j.1 = 1
        · exact ⟨2, by omega, by omega, by omega⟩
        · exact ⟨1, by omega, by omega, by omega⟩
      · by_cases hj0 : j.1 = 0
        · by_cases hi1 : i.1 = 1
          · exact ⟨2, by omega, by omega, by omega⟩
          · exact ⟨1, by omega, by omega, by omega⟩
        · exact ⟨0, by omega, by omega, by omega⟩
    obtain ⟨c, hc, hci, hcj⟩ := h
    exact ⟨⟨c, hc⟩, Fin.ne_of_val_ne hci, Fin.ne_of_val_ne hcj⟩
  have hpick2 : ∀ i : Fin (n + 3), ∃ k m : Fin (n + 3), k ≠ m ∧ k ≠ i ∧ m ≠ i := by
    intro i
    have h : ∃ c d : ℕ, c < n + 3 ∧ d < n + 3 ∧ c ≠ d ∧ c ≠ i.1 ∧ d ≠ i.1 := by
      by_cases hi0 : i.1 = 0
      · exact ⟨1, 2, by omega, by omega, by omega, by omega, by omega⟩
      · by_cases hi1 : i.1 = 1
        · exact ⟨0, 2, by omega, by omega, by omega, by omega, by omega⟩
        · exact ⟨0, 1, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨c, d, hc, hd, hcd, hci, hdi⟩ := h
    exact ⟨⟨c, hc⟩, ⟨d, hd⟩, Fin.ne_of_val_ne hcd, Fin.ne_of_val_ne hci, Fin.ne_of_val_ne hdi⟩
  have hflip : ∀ x : Fin 2, 1 - x ≠ x := by decide
  have key : ∀ (i j : Fin (n + 3)) (x y : Fin 2),
      ∃ p : (CGraph.complete (n + 3) ⊗g CGraph.complete 2).toSimple.Walk (i, x) (j, y),
        p.length ≤ 3 := by
    intro i j x y
    by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy
        exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · -- Same row, other column: leave the row, cross, and come back.
        obtain ⟨k, m, hkm, hki, hmi⟩ := hpick2 i
        have e1 := (hadj i k x y).2 ⟨fun h ↦ hki h.symm, hxy⟩
        have e2 := (hadj k m y x).2 ⟨hkm, fun h ↦ hxy h.symm⟩
        have e3 := (hadj m i x y).2 ⟨hmi, hxy⟩
        exact ⟨.cons e1 (.cons e2 (.cons e3 .nil)), by simp⟩
    · -- Other row: one hop, or two through a third row.
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨k, hki, hkj⟩ := hpick1 i j
        have e1 := (hadj i k x (1 - x)).2 ⟨fun h ↦ hki h.symm, fun h ↦ hflip x h.symm⟩
        have e2 := (hadj k j (1 - x) x).2 ⟨hkj, hflip x⟩
        exact ⟨.cons e1 (.cons e2 .nil), by simp⟩
      · exact ⟨.cons ((hadj i j x y).2 ⟨hij, hxy⟩) .nil, by simp⟩
  -- Two vertices in the same row are non-adjacent with no common neighbour.
  have hne : ∀ (w1 : Fin (n + 3)) (w2 : Fin 2),
      (CGraph.complete (n + 3) ⊗g CGraph.complete 2).toSimple.Adj
          ((0 : Fin (n + 3)), (0 : Fin 2)) (w1, w2) →
      ¬ (CGraph.complete (n + 3) ⊗g CGraph.complete 2).toSimple.Adj (w1, w2)
          ((0 : Fin (n + 3)), (1 : Fin 2)) := by
    intro w1 w2 h1 h2
    rw [hadj] at h1 h2
    have h : ∀ z : Fin 2, (0 : Fin 2) ≠ z → z ≠ 1 → False := by decide
    exact h w2 h1.2 h2.2
  have hab : ((0 : Fin (n + 3)), (0 : Fin 2)) ≠ ((0 : Fin (n + 3)), (1 : Fin 2)) := by
    intro h
    have h2 : (0 : Fin 2) = 1 := congrArg Prod.snd h
    exact absurd h2 (by decide)
  exact CGraph.diameter_eq_of_walks _ 3 (a := ((0 : Fin (n + 3)), (0 : Fin 2)))
    (b := ((0 : Fin (n + 3)), (1 : Fin 2))) (fun u v ↦ key u.1 v.1 u.2 v.2)
    fun p ↦ SimpleGraph.three_le_length_of_no_common_neighbour hab
      (by rw [hadj]; simp) (fun w hw hw' ↦ hne w.1 w.2 hw hw') p

/-- A crown graph is vertex-transitive, so its radius matches its diameter. -/
@[simp] theorem radius_crown (n : ℕ) : (crown (n + 3)).radius = 3 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_crown _), diameter_crown]

/-- Cliques of a complete multipartite graph meet each part at most once, so covering a Turán
graph by cliques takes as many cliques as its largest part has vertices. -/
@[simp] theorem cliqueCoverNum_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    (turan n r).cliqueCoverNum = (n + r - 1) / r := by
  rw [← indepNum_eq_cliqueCoverNum_completeMultipartite, indepNum_turan hr h]

theorem cliqueCoverNum_turan_of_dvd {n r : ℕ} (h : r ∣ n) (hr : 0 < r) :
    (turan n r).cliqueCoverNum = n / r := by
  rw [← indepNum_eq_cliqueCoverNum_completeMultipartite, indepNum_turan_of_dvd h hr]

/-- The edges a Turán graph is missing from the complete graph are exactly those inside its
parts. -/
theorem E_turan (n r : ℕ) :
    (turan n r).E + ((n % r) * ((n / r + 1).choose 2) + (r - n % r) * ((n / r).choose 2))
      = n.choose 2 := by
  have h := E_completeMultipartite
    (List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r))
  have hs : (List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r)).sum = n := by
    rw [← V_completeMultipartite]; exact V_turan n r
  rw [hs, List.map_append, List.sum_append, List.map_replicate, List.map_replicate,
    List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul] at h
  exact h

/-- A Turán graph with at least two parts, none of them empty, is connected. -/
theorem isConnected_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) : IsConnected (turan n r) := by
  have hd : 1 ≤ n / r := (Nat.one_le_div_iff (by omega)).2 h
  have hmr : n % r < r := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos (n % r) with hm | hm
  · exact isConnected_turan_of_dvd (Nat.dvd_of_mod_eq_zero hm) hr hd
  · rw [turan, completeMultipartite_append]
    refine isConnected_join ?_ ?_ <;>
      rw [V_completeMultipartite, List.sum_replicate, smul_eq_mul] <;>
      exact Nat.mul_pos (by omega) (by omega)

@[simp] theorem numComponents_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    (turan n r).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_turan hr h)

/-- With more parts available than vertices to fill them every part is a singleton, so the
Turán graph is complete. -/
@[simp] theorem turan_of_lt {n r : ℕ} (h : n < r) : turan n r = complete n := by
  simp only [turan, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
  rw [completeMultipartite_append, completeMultipartite_replicate_one]
  have : completeMultipartite (List.replicate (r - n) 0) = empty 0 := by
    induction (r - n) with
    | zero => simp
    | succ k ih => rw [List.replicate_succ, completeMultipartite_zero_cons, ih]
  rw [this, join_empty_zero]

/-- A Turán graph whose parts all have at least two vertices needs two dominating vertices:
no single vertex is universal, and one vertex from each of two different parts suffices. -/
theorem domNum_turan {n r : ℕ} (hr : 2 ≤ r) (h : 2 * r ≤ n) : (turan n r).domNum = 2 := by
  by_cases hdvd : r ∣ n
  · have hdiv : 2 ≤ n / r := by
      have h1 := Nat.div_mul_cancel hdvd
      nlinarith
    exact domNum_turan_of_dvd hdvd hr hdiv
  · -- General case: turan n r = join G H with G, H nonempty and domNum ≠ 1 for both
    have hturan : turan n r =
        completeMultipartite (List.replicate (n % r) (n / r + 1)) ∇g
          completeMultipartite (List.replicate (r - n % r) (n / r)) := by
      rw [turan, completeMultipartite_append]
    rw [hturan]
    have hr0 : 0 < r := by omega
    have hnrx : 2 ≤ n / r := by
      exact Nat.le_div_iff_mul_le hr0 |>.mpr h
    have hvG : 0 < (completeMultipartite (List.replicate (n % r) (n / r + 1))).V := by
      rw [V_completeMultipartite_replicate]
      exact Nat.mul_pos
        (Nat.pos_of_ne_zero (by intro h0; exact hdvd (Nat.dvd_of_mod_eq_zero h0))) (by omega)
    have hvH : 0 < (completeMultipartite (List.replicate (r - n % r) (n / r))).V := by
      rw [V_completeMultipartite_replicate]
      exact Nat.mul_pos (Nat.sub_pos_of_lt (Nat.mod_lt _ hr0)) (by omega)
    -- Helper: domNum of completeMultipartite(replicate k d) ≠ 1 when d ≥ 2, k ≥ 1
    -- Case k = 1: graph is empty d, domNum = d ≥ 2
    -- Case k ≥ 2: graph has domNum = 2 by domNum_completeMultipartite_replicate
    have hdom_ne_one_replicate (k d : ℕ) (hk : 0 < k) (hd : 2 ≤ d) :
        (completeMultipartite (List.replicate k d)).domNum ≠ 1 := by
      rcases k with _ | _ | k
      · omega
      · -- k = 1: completeMultipartite [d] = empty d
        have : List.replicate (0 + 1) d = [d] := by simp
        rw [this, completeMultipartite_singleton]
        simp [domNum_empty]
        omega
      · -- k + 2 ≥ 2 parts of size d ≥ 2
        obtain ⟨d', hd'⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
        rw [hd', show List.replicate (k + 2) (d' + 2) = List.replicate (k + 2) (d' + 2) from rfl]
        have := domNum_completeMultipartite_replicate k d'
        omega
    have hNG := hdom_ne_one_replicate (n % r) (n / r + 1)
      (Nat.pos_of_ne_zero (by intro h0; exact hdvd (Nat.dvd_of_mod_eq_zero h0))) (by omega)
    have hNH := hdom_ne_one_replicate (r - n % r) (n / r)
      (Nat.sub_pos_of_lt (Nat.mod_lt _ hr0)) hnrx
    exact domNum_join_eq_two hvG hvH hNG hNH

@[simp] theorem degSequence_crown (n : ℕ) :
    degSequence (crown (n + 2)) = List.replicate (2 * n + 4) (n + 1) := by
  have h := (isRegularWith_crown (n + 2)).degSequence
  rw [V_crown] at h
  rw [h, show 2 * (n + 2) = 2 * n + 4 from by omega, show n + 2 - 1 = n + 1 from by omega]

@[simp] theorem degMultiset_crown (n : ℕ) :
    degMultiset (crown (n + 2)) = Multiset.replicate (2 * n + 4) (n + 1) :=
  degMultiset_of_degSequence (degSequence_crown n)

theorem degSequence_turan_of_dvd {n r : ℕ} (h : r ∣ n) :
    degSequence (turan n r) = List.replicate n ((r - 1) * (n / r)) := by
  have hd := (isRegularWith_turan_of_dvd h).degSequence
  rwa [V_turan] at hd

@[simp] theorem degSequence_compl_cocktailParty (n : ℕ) :
    degSequence (cocktailParty (n + 1))ᶜ = List.replicate (2 * n + 2) 1 := by
  have h := (isRegularWith_compl_cocktailParty n).degSequence
  rw [V_compl, V_cocktailParty] at h
  rw [h, show 2 * (n + 1) = 2 * n + 2 from by omega]

@[simp] theorem degSequence_ladder_two : degSequence (ladder 2) = List.replicate 4 2 := by
  have h := isRegularWith_ladder_two.degSequence
  rwa [V_ladder] at h

/-! ### Degree sequences of line graphs of regular graphs -/

@[simp] theorem degSequence_lineGraph_petersen :
    degSequence (lineGraph petersen) = List.replicate 15 4 := by
  have h := isRegularWith_lineGraph_petersen.degSequence
  rwa [V_lineGraph, E_petersen] at h

@[simp] theorem degSequence_lineGraph_prism (n : ℕ) :
    degSequence (lineGraph (prism (n + 3))) = List.replicate (3 * (n + 3)) 4 := by
  have h := (isRegularWith_lineGraph_prism n).degSequence
  rwa [V_lineGraph, E_prism] at h

theorem degMultiset_lineGraph_prism (n : ℕ) :
    degMultiset (lineGraph (prism (n + 3))) = Multiset.replicate (3 * (n + 3)) 4 :=
  degMultiset_of_degSequence (degSequence_lineGraph_prism n)

theorem degSequence_lineGraph_hypercube (n : ℕ) :
    degSequence (lineGraph (hypercube (n + 1)))
      = List.replicate ((n + 1) * 2 ^ n) (2 * (n + 1) - 2) := by
  have h2 : 2 * (hypercube (n + 1)).E = 2 * ((n + 1) * 2 ^ n) := by
    rw [E_hypercube, pow_succ]; ring
  have hE : (hypercube (n + 1)).E = (n + 1) * 2 ^ n :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2
  have h := (isRegularWith_lineGraph_hypercube n).degSequence
  rwa [V_lineGraph, hE] at h

theorem degSequence_lineGraph_cocktailParty (n : ℕ) :
    degSequence (lineGraph (cocktailParty (n + 2)))
      = List.replicate ((n + 2) * (2 * (n + 2) - 2)) (2 * (2 * (n + 2) - 2) - 2) := by
  have h := (isRegularWith_lineGraph_cocktailParty n).degSequence
  rwa [V_lineGraph, E_cocktailParty] at h

theorem degSequence_lineGraph_bipartite_self (n : ℕ) :
    degSequence (lineGraph (bipartite (n + 1) (n + 1)))
      = List.replicate ((n + 1) * (n + 1)) (2 * (n + 1) - 2) := by
  have h := (isRegularWith_lineGraph_bipartite_self n).degSequence
  rwa [V_lineGraph, E_bipartite] at h

theorem degSequence_lineGraph_triangular {n : ℕ} (hn : 4 ≤ n) :
    degSequence (lineGraph (triangular n))
      = List.replicate (n * (n - 1).choose 2) (2 * (2 * (n - 2)) - 2) := by
  have h := (isRegularWith_lineGraph_triangular n hn).degSequence
  rwa [V_lineGraph, E_triangular] at h

theorem degSequence_lineGraph_kneser {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    degSequence (lineGraph (kneser n k))
      = List.replicate (n.choose k * (n - k).choose k / 2) (2 * (n - k).choose k - 2) := by
  have h := (isRegularWith_lineGraph_kneser n k hk hkn).degSequence
  rwa [V_lineGraph, E_kneser n hk] at h

/-- Every vertex of a friendship graph other than the hub lies in exactly one triangle, so all
but one degree is two and the hub takes the rest. -/
@[simp] theorem degSequence_friendship (n : ℕ) :
    degSequence (friendship (n + 1)) = List.replicate (2 * n + 2) 2 ++ [2 * n + 2] := by
  rw [friendship_eq_join_compl_cocktailParty, compl_cocktailParty]
  rw [degSequence_eq_sort, degMultiset_join, degMultiset_complete,
    degMultiset_cartesianProduct, degMultiset_empty, degMultiset_complete,
    V_cartesianProduct, V_empty, V_complete]
  rw [V_complete]
  simp
  have h1 : (n + 1) * 2 = 2 * n + 2 := by omega
  rw [h1]
  have h2 : Multiset.replicate n 2 + Multiset.replicate n 2 = Multiset.replicate (2 * n) 2 := by
    rw [show 2 * n = n + n from by omega]
    rw [Multiset.replicate_add]
  rw [h2]
  -- Goal: sort of multiset = replicate (2*n+2) 2 ++ [2*n+2]
  -- Multiset = 2 ::ₘ 2 ::ₘ (2*n+2) ::ₘ replicate (2*n) 2
  -- = replicate (2*n+2) 2 + {2*n+2}
  have h3 : (2 ::ₘ 2 ::ₘ (2 * n + 2) ::ₘ Multiset.replicate (2 * n) 2) =
    Multiset.replicate (2 * n + 2) 2 + {2 * n + 2} := by
    show 2 ::ₘ 2 ::ₘ (2 * n + 2) ::ₘ Multiset.replicate (2 * n) 2 =
      Multiset.replicate (2 * n + 2) 2 + {2 * n + 2}
    have h3' : ∀ x : ℕ,
        Multiset.count x (2 ::ₘ 2 ::ₘ (2 * n + 2) ::ₘ Multiset.replicate (2 * n) 2) =
        Multiset.count x (Multiset.replicate (2 * n + 2) 2 + {2 * n + 2}) := by
      intro x
      simp [Multiset.count_cons, Multiset.count_replicate, Multiset.count_singleton]
    ext x
    exact h3' x
  rw [h3, add_comm,
    show ({2 * n + 2} : Multiset ℕ) = (([2 * n + 2] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (List.pairwise_singleton _ _) fun x hx b hb ↦ ?_
  rw [List.eq_of_mem_replicate hx, List.mem_singleton] at *
  omega

@[simp] theorem degMultiset_friendship (n : ℕ) :
    degMultiset (friendship (n + 1)) = (2 * n + 2) ::ₘ Multiset.replicate (2 * n + 2) 2 := by
  rw [← coe_degSequence, degSequence_friendship]
  exact Multiset.coe_eq_coe.2 (List.perm_append_singleton _ _)

/-- A vertex of a Turán graph sees everything outside its own part, so the largest degree
belongs to a vertex of a smallest part. -/
@[simp] theorem maxDeg_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    maxDeg (turan n r) = n - n / r := by
  let ds : List ℕ := List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r)
  have hds : turan n r = completeMultipartite ds := rfl
  rw [hds]
  -- Key facts about ds
  have hsum : ds.sum = n := by
    simp [ds, List.sum_append, List.sum_replicate]
    have hle : n % r ≤ r := Nat.mod_lt n hr |>.le
    calc n % r * (n / r + 1) + (r - n % r) * (n / r)
        = (n % r + (r - n % r)) * (n / r) + n % r := by rw [Nat.add_mul]; ring
      _ = r * (n / r) + n % r := by rw [Nat.add_sub_cancel' hle]
      _ = n := Nat.div_add_mod n r
  have hmin : ∀ x ∈ ds, n / r ≤ x := by
    intro x hx
    simp [ds, List.mem_append, List.mem_replicate] at hx
    omega
  simp only [completeMultipartite_def]
  rw [maxDeg_mk]
  have hdeg_formula : ∀ v : (CGraph.completeMultipartite ds).V,
      (CGraph.completeMultipartite ds).toSimple.degree v = n - ds.get v.1 := by
    intro v
    rw [SimpleGraph.degree, CGraph.neighborFinset_eq_nbrs, CGraph.nbrs_completeMultipartite,
      CGraph.card_filter_fst_notMem]
    have hsingleton : ({v.1} : Finset (Fin ds.length))ᶜ = Finset.univ \ {v.1} := by rfl
    rw [hsingleton]
    have h_univ_diff : (Finset.univ \ {v.1} : Finset (Fin ds.length)) = Finset.univ \ {v.1} := rfl
    have h_sum_univ : ∑ j : Fin ds.length, ds.get j = ds.sum := by
      have h1 : Fintype.card (Σ i : Fin ds.length, Fin (ds.get i))
          = ∑ i : Fin ds.length, ds.get i := by
        simp [Fintype.card_sigma, Fintype.card_fin]
      have h2 : FinEnum.card (CGraph.completeMultipartite ds).V = ds.sum :=
        CGraph.card_completeMultipartite ds
      rw [← h2, ← h1, FinEnum.card_eq_fintypeCard']
      exact Fintype.card_congr' rfl
    have h_eq : ∑ j ∈ (Finset.univ \ {v.1} : Finset (Fin ds.length)), ds.get j
        + ∑ j ∈ ({v.1} : Finset (Fin ds.length)), ds.get j = ds.sum := by
      rw [← h_sum_univ, ← Finset.sum_sdiff
        (show ({v.1} : Finset (Fin ds.length)) ⊆ Finset.univ from Finset.subset_univ _)]
    rw [Finset.sum_singleton] at h_eq
    omega
  have hdeg_le : ∀ v : (CGraph.completeMultipartite ds).V,
      (CGraph.completeMultipartite ds).toSimple.degree v ≤ n - n / r := by
    intro v
    rw [hdeg_formula]
    exact Nat.sub_le_sub_left (hmin _ (ds.get_mem _)) _
  have hvert_small_part : ∃ i : Fin ds.length, ds.get i = n / r := by
    have hlen : ds.length = r := by
      simp [ds, List.length_append, List.length_replicate]
      exact Nat.add_sub_of_le (Nat.mod_lt n hr |>.le)
    refine ⟨⟨n % r, by rw [hlen]; exact Nat.mod_lt n hr⟩, ?_⟩
    simp [ds]
  have hexists : ∃ v : (CGraph.completeMultipartite ds).V,
      (CGraph.completeMultipartite ds).toSimple.degree v = n - n / r := by
    obtain ⟨i, hi⟩ := hvert_small_part
    have hpos : 0 < ds.get i := by rw [hi]; exact Nat.div_pos h hr
    exact ⟨⟨i, ⟨0, hpos⟩⟩, by rw [hdeg_formula, hi]⟩
  exact CGraph.maxDeg_eq_of_degMultiset
    (CGraph.mem_degMultiset.mpr hexists)
    (fun d hd => by
      obtain ⟨v, hv⟩ := CGraph.mem_degMultiset.mp hd
      exact hv ▸ hdeg_le v)

/-- No vertex of a Turán graph whose parts all have at least two vertices is universal, and
any two vertices have a common neighbour, so its radius is two. -/
@[simp] theorem radius_turan {n r : ℕ} (hr : 2 ≤ r) (h : 2 * r ≤ n) : (turan n r).radius = 2 := by
  have hV : 1 < (turan n r).V := by rw [V_turan]; omega
  -- No universal vertex, so radius ≠ 1
  have hne : (turan n r).radius ≠ 1 := by
    intro h
    rw [radius_eq_one_iff_domNum_eq_one hV, domNum_turan hr (by omega)] at h
    omega
  -- diameter ≤ 2
  have hdiam : (turan n r).diameter ≤ 2 := by
    rw [turan, completeMultipartite_def, IsoGraph.diameter_mk]
    set L := List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r)
    have hlen' : L.length = r := by
      simp [L, List.length_append, List.length_replicate]
      exact Nat.add_sub_of_le (Nat.mod_lt n (by omega)).le
    have hpartPos : ∀ i : Fin L.length, 0 < L.get i := by
      intro i
      simp only [L]
      have hi : (i : ℕ)
          < (List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r)).length :=
        i.isLt
      have hmod_lt : n % r < r := Nat.mod_lt n (by omega)
      have hn0' : 0 < n / r := Nat.div_pos (by omega) (by omega)
      have hforall : ∀ x ∈ (List.replicate (n % r) (n / r + 1)
          ++ List.replicate (r - n % r) (n / r)), 0 < x := by
        intro x hx
        simp [List.mem_append, List.mem_replicate] at hx
        rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact Nat.zero_lt_succ _; exact hn0']
      exact hforall _ (List.get_mem _ ⟨i.val, hi⟩)
    have hdiam_le : (CGraph.completeMultipartite L).toSimple.ediam ≤ 2 := by
      apply SimpleGraph.ediam_le_of_edist_le
      intro u v
      by_cases huv : u = v
      · rw [huv]; simp
      by_cases hadj : (CGraph.completeMultipartite L).toSimple.Adj u v
      · have := SimpleGraph.edist_eq_one_iff_adj.2 hadj
        exact le_trans this.le (by decide)
      · rw [CGraph.toSimple_adj] at hadj
        rw [CGraph.completeMultipartite_adj, decide_eq_true_eq] at hadj
        push Not at hadj
        have hlen_pos : 1 < L.length := by rw [hlen']; omega
        obtain ⟨k, hk⟩ : ∃ k : Fin L.length, k ≠ u.1 := by
          by_contra h'
          push Not at h'
          have h1 := h' ⟨0, by omega⟩
          have h2 := h' ⟨1, hlen_pos⟩
          have := congrArg Fin.val (h1.trans h2.symm)
          simp at this
        set w : (CGraph.completeMultipartite L).V := ⟨k, 0, hpartPos k⟩
        have hne1 : u.1 ≠ k := hk.symm
        have hne2 : v.1 ≠ k := by intro heq; exact hk (hadj ▸ heq).symm
        have hadj1 : (CGraph.completeMultipartite L).toSimple.Adj u w := by
          dsimp only [w]
          simp [CGraph.toSimple_adj, CGraph.completeMultipartite_adj, hne1]
        have hadj2 : (CGraph.completeMultipartite L).toSimple.Adj v w := by
          dsimp only [w]
          simp [CGraph.toSimple_adj, CGraph.completeMultipartite_adj, hne2]
        exact le_trans (SimpleGraph.edist_le (SimpleGraph.Walk.cons hadj1
          (SimpleGraph.Walk.cons (SimpleGraph.Adj.symm hadj2) (SimpleGraph.Walk.nil)))) (by simp)
    have h2 := ENat.toNat_le_toNat hdiam_le (by simp)
    simp [CGraph.diameter, SimpleGraph.diam]
    have : ENat.toNat 2 = 2 := by trivial
    omega
  have hdiam2 : (turan n r).diameter ≤ 2 := hdiam
  have hc := isConnected_turan hr (by omega : r ≤ n)
  have h3 := radius_pos hc hV
  have h2 := radius_le_diameter (turan n r)
  have : (turan n r).radius ≤ 2 := le_trans h2 hdiam2
  have h4 : 1 ≤ (turan n r).radius := h3
  have h5 : (turan n r).radius ≤ 2 := this
  omega

/-- Dually to the maximum degree, the smallest degree of a Turán graph belongs to a vertex of
a largest part. -/
@[simp] theorem minDeg_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    minDeg (turan n r) = n - (n + r - 1) / r := by
  -- Helper: compute (r * m + s) / r = m when s < r
  have div_helper (m s : ℕ) (hs : s < r) : (r * m + s) / r = m := by
    rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hs, Nat.add_zero]
  have sub_one_div (q : ℕ) : (r * (q + 1) - 1) / r = q := by
    rw [show r * (q + 1) - 1 = r * q + (r - 1) from by rw [Nat.mul_succ]; omega]
    exact div_helper q (r - 1) (by omega)
  have div_zero : r * (n / r) / r = n / r := div_helper (n / r) 0 (by omega)
  by_cases hdvd : r ∣ n
  · -- Case: r divides n
    rw [turan_of_dvd hdvd]
    rw [minDeg_completeMultipartite_replicate hr (Nat.div_pos h hr)]
    have hn : n = r * (n / r) := (Nat.mul_div_cancel' hdvd).symm
    have h2 : (n + r - 1) / r = n / r := by
      rw [hn]
      have h3 : r * (n / r) + r - 1 = r * (n / r + 1) - 1 := by rw [Nat.mul_add]; omega
      rw [h3, sub_one_div, div_zero]
    rw [h2, hn, div_zero]
    clear h2 h hn div_zero sub_one_div div_helper
    have hgoal : (r - 1) * (n / r) = r * (n / r) - n / r := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [hgoal]
  · -- Case: r does not divide n
    set k := n % r
    have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
    have hk_lt : k < r := Nat.mod_lt n hr
    have hv1 : n = r * (n / r) + k := by rw [Nat.div_add_mod]
    -- Key: (r * q + k + r - 1) = r * (q + 1) + (k - 1)
    have hreassoc : r * (n / r) + k + r - 1 = r * (n / r + 1) + (k - 1) := by
      rw [show r * (n / r + 1) = r * (n / r) + r from by ring]
      omega
    have h2 : (n + r - 1) / r = n / r + 1 := by
      rw [show n + r - 1 = r * (n / r + 1) + (k - 1) from by omega,
        div_helper (n / r + 1) (k - 1) (by omega)]
    have hturan : turan n r =
        completeMultipartite (List.replicate k (n / r + 1)) ∇g
          completeMultipartite (List.replicate (r - k) (n / r)) := by
      rw [turan, completeMultipartite_append]
    rw [hturan]
    have hndiv_pos : 0 < n / r := Nat.div_pos h hr
    rw [minDeg_join
      (by rw [V_completeMultipartite_replicate]; positivity)
      (by
        rw [V_completeMultipartite_replicate]
        exact Nat.mul_pos (Nat.sub_pos_of_lt hk_lt) hndiv_pos)]
    rw [minDeg_completeMultipartite_replicate hk_pos (by omega : 0 < n / r + 1)]
    rw [minDeg_completeMultipartite_replicate (Nat.sub_pos_of_lt hk_lt) hndiv_pos]
    rw [V_completeMultipartite_replicate, V_completeMultipartite_replicate]
    rw [h2]
    clear h2
    set q := n / r
    have hrq : r * (q + 1) = r * q + r := Nat.mul_succ r q
    simp only [hrq] at *
    -- Each of the three arithmetic facts is linear once distributivity splits off the `q`s.
    have hmul : (r - 1) * q = r * q - q := Nat.sub_one_mul r q
    have hqle : q ≤ r * q := Nat.le_mul_of_pos_left q hr
    have hnr1 : (r - 1) * q + (k - 1) = n - (q + 1) := by omega
    rw [hnr1.symm]
    have harg1_eq : (k - 1) * (q + 1) + (r - k) * q = (r - 1) * q + (k - 1) := by
      have h1 : (k - 1) * q + (r - k) * q = (r - 1) * q := by
        rw [← Nat.add_mul, show k - 1 + (r - k) = r - 1 from by omega]
      rw [Nat.mul_succ]
      omega
    have harg2_ge : k * (q + 1) + (r - k - 1) * q ≥ (r - 1) * q + (k - 1) := by
      have h1 : (r - k - 1) * q + k * q = (r - 1) * q := by
        rw [← Nat.add_mul, show r - k - 1 + k = r - 1 from by omega]
      rw [Nat.mul_succ]
      omega
    rw [harg1_eq]
    exact min_eq_left harg2_ge

/-- A Paley graph on `q` vertices has a near-perfect matching: the pairs `{2i, 2i+1}` are
edges, since `1` is always a square. -/
@[simp] theorem matchNum_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).matchNum = q / 2 := by
  have hupper : 2 * (paley q).matchNum ≤ q := by
    have := two_mul_matchNum_le_V (paley q)
    simpa using this
  have hq_ge_2 : 2 ≤ q := Nat.Prime.two_le Fact.out
  have hlt : ∀ i : Fin (q / 2), 2 * (i : ℕ) + 1 < q := fun i ↦ by omega
  have hmatch_ge : q / 2 ≤ (paley q).matchNum := by
    rw [IsoGraph.paley_def, matchNum_mk]
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun i : Fin (q / 2) ↦ (⟨2 * (i : ℕ), by have := hlt i; omega⟩ : Fin q))
      (fun i : Fin (q / 2) ↦ (⟨2 * (i : ℕ) + 1, hlt i⟩ : Fin q)) ?_ ?_)
    · -- The two ends of the `i`-th rung differ by `1`, and `1` is a square in every field.
      intro i
      have hiq_val : ((i : ℕ) : ZMod q).val = (i : ℕ) :=
        ZMod.val_cast_of_lt (by have := hlt i; omega)
      have hval2 : ZMod.val (2 : ZMod q) = 2 := by
        rw [show (2 : ZMod q) = (2 : ℕ) by rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have ha_val : (2 * (i : ℕ) : ZMod q).val = 2 * (i : ℕ) := by
        simp [ZMod.val_mul, hval2, hiq_val, Nat.mod_eq_of_lt (show 2 * (i : ℕ) < q by
          have := hlt i; omega)]
      have hb_val : (2 * (i : ℕ) + 1 : ZMod q).val = 2 * (i : ℕ) + 1 := by
        simp [ZMod.val_add, ha_val, ZMod.val_one, Nat.mod_eq_of_lt (hlt i)]
      rw [show (⟨2 * (i : ℕ), by have := hlt i; omega⟩ : Fin q)
            = zmodEquivFin q (2 * (i : ℕ) : ZMod q) from by ext; simp [zmodEquivFin, ha_val],
        show (⟨2 * (i : ℕ) + 1, hlt i⟩ : Fin q)
            = zmodEquivFin q (2 * (i : ℕ) + 1 : ZMod q) from by ext; simp [zmodEquivFin, hb_val],
        CGraph.paley_adj_eq, CGraph.paleyField_adj]
      · rw [show (2 * (i : ℕ) + 1 : ZMod q) - (2 * (i : ℕ) : ZMod q) = 1 from by ring]
        -- `paleyField` counts and compares with the instances its `FinEnum` induces, so the
        -- character here is not the one ambient typeclass search would find for `ZMod q`
        exact decide_eq_true
          ((CGraph.quadraticChar_eq_one_iff (F := ZMod q) 1).2 ⟨1, one_ne_zero, by ring⟩)
      · rw [← @FinEnum.card_eq_fintypeCard (ZMod q) _ FinEnum.instFintype]
        exact hq
    · -- Rungs with different indices share no endpoint: their labels have different halves.
      intro i j hij
      have hv : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (Fin.ext h)
      have key : ∀ (m n : ℕ) (hm : m < q) (hn : n < q), m ≠ n → (⟨m, hm⟩ : Fin q) ≠ ⟨n, hn⟩ :=
        fun _ _ _ _ h he ↦ h (congrArg Fin.val he)
      exact ⟨key _ _ _ _ (by omega), key _ _ _ _ (by omega), key _ _ _ _ (by omega),
        key _ _ _ _ (by omega)⟩
  omega

/-- Two vertices of a Turán graph in the same part are at distance two, everything else at
distance one. -/
theorem diameter_turan {n r : ℕ} (hr : 2 ≤ r) (h : 2 * r ≤ n) : (turan n r).diameter = 2 := by
  have hr_pos : 0 < r := by omega
  have hnr : n / r ≥ 2 := by
    rw [ge_iff_le, Nat.le_div_iff_mul_le hr_pos]
    omega
  set k := n % r
  set a := n / r
  have hk_lt_r : k < r := Nat.mod_lt n hr_pos
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- k = 0, so r ∣ n. Use diameter_turan_of_dvd.
    exact diameter_turan_of_dvd (Nat.dvd_of_mod_eq_zero hk0) hr hnr
  · -- k > 0 case
    have hk1 : 1 ≤ k := hk0
    have hrk_pos : 0 < r - k := by omega
    -- Rewrite turan using cons on the list
    have hdet : turan n r = empty (a + 1) ∇g
        completeMultipartite (List.replicate (k - 1) (a + 1) ++ List.replicate (r - k) a) := by
      unfold turan
      rw [show List.replicate k (a + 1) = (a + 1) :: List.replicate (k - 1) (a + 1) from by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk1).symm, List.replicate_succ]
        rfl]
      rw [List.cons_append, completeMultipartite_cons]
    rw [hdet]
    apply diameter_join_left
    · -- 0 < V of completeMultipartite rest
      rw [V_completeMultipartite]
      have : (List.replicate (k - 1) (a + 1) ++ List.replicate (r - k) a).sum
          = (k - 1) * (a + 1) + (r - k) * a := by
        simp [List.sum_replicate, List.sum_append]
      rw [this]
      nlinarith
    · -- E(empty (a+1)) < (empty (a+1)).V.choose 2
      rw [E_empty, V_empty]
      exact Nat.choose_pos (by omega)

/-- Parts of size two make a cocktail party graph. -/
@[simp] theorem turan_two_mul_self (r : ℕ) : turan (2 * r) r = cocktailParty r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [turan, cocktailParty]
  · rw [turan_of_dvd ⟨2, by ring⟩, Nat.mul_div_cancel _ hr]

/-- **Equal parts make a blow-up**: a balanced Turán graph is `K_r` with every vertex blown up
to an independent set of size `n / r`. -/
theorem turan_eq_lexProduct_of_dvd {n r : ℕ} (h : r ∣ n) :
    turan n r = complete r ·g empty (n / r) := by
  rw [turan_of_dvd h, completeMultipartite_replicate]

/-- The complement of a balanced Turán graph is `r` disjoint cliques. -/
theorem compl_turan_of_dvd {n r : ℕ} (h : r ∣ n) :
    (turan n r)ᶜ = empty r □g complete (n / r) := by
  rw [turan_of_dvd h, compl_completeMultipartite_replicate]

/-- The complement of a cocktail party graph, read off the Turán graph it is. -/
theorem compl_turan_two_mul_self (r : ℕ) :
    (turan (2 * r) r)ᶜ = empty r □g complete 2 := by
  rw [turan_two_mul_self, compl_cocktailParty]

/-- A Paley graph is `(q-1)/2`-regular on `q` vertices, so it has `q(q-1)/4` edges. -/
@[simp] theorem E_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    4 * (paley q).E = q * (q - 1) := by
  have h := (isRegularWith_paley q hq).two_mul_E
  rw [V_paley] at h
  have h2 : 2 * ((q - 1) / 2) = q - 1 := by omega
  calc 4 * (paley q).E = 2 * (2 * (paley q).E) := by ring
    _ = 2 * (q * ((q - 1) / 2)) := by rw [h]
    _ = q * (2 * ((q - 1) / 2)) := by ring
    _ = q * (q - 1) := by rw [h2]

/-- **The friendship graph is class one.**  It is `n + 2` triangles glued at a hub, so the hub has
degree `2n + 4`; give the spoke to `(i, b)` the colour `2i + b`, and the rail of the `i`-th
triangle a colour that neither of its two spokes carries. -/
theorem edgeChromNum_friendship (n : ℕ) :
    (friendship (n + 2)).edgeChromNum = 2 * n + 4 := by
  refine le_antisymm ?_ ?_
  · have hfr : (friendship (n + 2) : IsoGraph) = ⟦CGraph.friendship (n + 2)⟧ := by
      simp only [friendship, complete_def, empty_def]
      rw [cartesianProduct_mk, join_mk]
    rw [hfr]
    have hfin2 : ∀ b c c' : Fin 2, b ≠ c → b ≠ c' → c = c' := by decide
    -- Spoke `(i, b)` gets colour `2i + b`; the rail of triangle `i` gets colour `2` if `i = 0`
    -- and colour `0` otherwise — in both cases a colour neither of its spokes carries.
    let col : (Fin 1 ⊕ (Fin (n + 2) × Fin 2)) → (Fin 1 ⊕ (Fin (n + 2) × Fin 2)) →
        Fin (2 * n + 4) := fun a b ↦
      match a, b with
      | Sum.inl _, Sum.inl _ => ⟨0, by omega⟩
      | Sum.inl _, Sum.inr (i, b) => ⟨2 * i.val + b.val, by omega⟩
      | Sum.inr (i, b), Sum.inl _ => ⟨2 * i.val + b.val, by omega⟩
      | Sum.inr (i, _), Sum.inr (j, _) =>
          ⟨if i.val = 0 ∧ j.val = 0 then 2 else 0, by split <;> omega⟩
    have hspoke_l : ∀ (x : Fin 1) (i : Fin (n + 2)) (b : Fin 2),
        (col (Sum.inl x) (Sum.inr (i, b))).val = 2 * i.val + b.val := fun _ _ _ ↦ rfl
    have hspoke_r : ∀ (x : Fin 1) (i : Fin (n + 2)) (b : Fin 2),
        (col (Sum.inr (i, b)) (Sum.inl x)).val = 2 * i.val + b.val := fun _ _ _ ↦ rfl
    have hrailc : ∀ (i j : Fin (n + 2)) (b c : Fin 2),
        (col (Sum.inr (i, b)) (Sum.inr (j, c))).val = if i.val = 0 ∧ j.val = 0 then 2 else 0 :=
      fun _ _ _ _ ↦ rfl
    have hsym : ∀ a b, col a b = col b a := by
      rintro (x | ⟨i, b⟩) (y | ⟨j, c⟩)
      · rfl
      · rfl
      · rfl
      · exact Fin.ext (by rw [hrailc i j b c, hrailc j i c b]; split_ifs <;> omega)
    -- Two rim vertices are adjacent only if they are the two ends of one rail.
    have hrail : ∀ (i j : Fin (n + 2)) (b c : Fin 2),
        (CGraph.friendship (n + 2)).Adj (Sum.inr (i, b)) (Sum.inr (j, c)) = true →
          i = j ∧ b ≠ c := by
      intro i j b c h
      simpa using h
    have hhub : ∀ x y : Fin 1,
        (CGraph.friendship (n + 2)).Adj (Sum.inl x) (Sum.inl y) = false := by
      intro x y
      rw [Subsingleton.elim (α := Fin 1) x y]
      exact Bool.eq_false_iff.2 ((CGraph.friendship (n + 2)).loopless _)
    refine edgeChromNum_mk_le_of_colouring col hsym ?_
    show ∀ u v w : Fin 1 ⊕ (Fin (n + 2) × Fin 2),
      (CGraph.friendship (n + 2)).Adj u v = true → (CGraph.friendship (n + 2)).Adj u w = true →
        v ≠ w → col u v ≠ col u w
    rintro (x | ⟨i, b⟩) (y | ⟨j, c⟩) (z | ⟨j', c'⟩) huv huw hvw
    · rw [hhub] at huv; exact absurd huv (by simp)
    · rw [hhub] at huv; exact absurd huv (by simp)
    · rw [hhub] at huw; exact absurd huw (by simp)
    · -- two spokes at the hub: their colours read off the rim vertex
      refine fun h ↦ hvw (congrArg Sum.inr ?_)
      have hv := congrArg Fin.val h
      rw [hspoke_l x j c, hspoke_l x j' c'] at hv
      have := c.isLt; have := c'.isLt
      rw [show j = j' from Fin.ext (by omega), show c = c' from Fin.ext (by omega)]
    · exact absurd (congrArg Sum.inl (Subsingleton.elim (α := Fin 1) y z)) hvw
    · -- a spoke and a rail at a rim vertex
      obtain ⟨hij, -⟩ := hrail i j' b c' huw
      refine Fin.ne_of_val_ne ?_
      rw [hspoke_r y i b, hrailc i j' b c', ← hij]
      have := b.isLt
      split <;> omega
    · obtain ⟨hij, -⟩ := hrail i j b c huv
      refine Fin.ne_of_val_ne ?_
      rw [hrailc i j b c, hspoke_r z i b, ← hij]
      have := b.isLt
      split <;> omega
    · -- both rails: a rim vertex lies on only one, so `v = w`
      obtain ⟨rfl, hbc⟩ := hrail i j b c huv
      obtain ⟨rfl, hbc'⟩ := hrail i j' b c' huw
      exact absurd (congrArg Sum.inr (congrArg (Prod.mk i) (hfin2 b c c' hbc hbc'))) hvw
  · have h1 := maxDeg_le_edgeChromNum (friendship (n + 2))
    have h2 : maxDeg (friendship (n + 2)) = 2 * n + 4 := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      exact maxDeg_friendship (n + 1) ▸ by omega
    omega

/-- The complement of the friendship graph: the hub becomes isolated and the petals become a
cocktail party graph. -/
@[simp] theorem compl_friendship (n : ℕ) :
    (friendship n)ᶜ = empty 1 ⊕g cocktailParty n := by
  rw [friendship, compl_join, compl_complete, ← compl_cocktailParty, compl_compl]

/-- The complement of a Turán graph is `r` disjoint cliques, `n % r` of them one vertex larger
than the others. -/
theorem compl_turan (n r : ℕ) :
    (turan n r)ᶜ
      = empty (n % r) □g complete (n / r + 1) ⊕g empty (r - n % r) □g complete (n / r) := by
  rw [turan, completeMultipartite_append, compl_join, compl_completeMultipartite_replicate,
    compl_completeMultipartite_replicate]

/-- The complement of the triangular graph is the Kneser graph `K(n, 2)`. -/
@[simp] theorem compl_triangular (n : ℕ) : (triangular n)ᶜ = kneser n 2 := by
  rw [triangular_eq_compl_kneser, compl_compl]

/-- The complement of the Kneser graph `K(n, 2)` is the triangular graph. -/
@[simp] theorem compl_kneser_two (n : ℕ) : (kneser n 2)ᶜ = triangular n :=
  (triangular_eq_compl_kneser n).symm

/-- A Turán graph with at least two parts has a near-perfect matching: pair the vertices up
in round-robin order, so consecutive vertices land in different parts. -/
theorem matchNum_turan {n r : ℕ} (hr : 2 ≤ r) (_h : r ≤ n) : (turan n r).matchNum = n / 2 := by
  apply le_antisymm
  · have h1 := two_mul_matchNum_le_V (turan n r)
    rw [V_turan] at h1
    omega
  · -- Number the vertices round robin: `j` goes to part `j % r`, in slot `j / r`.  Then `2t` and
    -- `2t + 1` land in different parts, so the `n / 2` pairs `{2t, 2t + 1}` are disjoint edges.
    set m := n % r with hm_def
    set q := n / r with hq_def
    set L : List ℕ := List.replicate m (q + 1) ++ List.replicate (r - m) q
    set H : CGraph := CGraph.completeMultipartite L
    have hturan : turan n r = ⟦H⟧ := by rfl
    rw [hturan, matchNum_mk]
    have hLlen : L.length = r := by
      simp [L, List.length_append, List.length_replicate]
      have := Nat.mod_lt n (by linarith : 0 < r)
      omega
    have hpos_r : 0 < r := by linarith
    have hmod_lt : n % r < r := Nat.mod_lt n hpos_r
    have hLget : ∀ (i : Fin r),
        L.get ⟨i, by rw [hLlen]; exact i.2⟩ = if i.val < m then q + 1 else q := by
      intro ⟨i, hi⟩
      simp only [L]
      simp [List.getElem_append]
    -- vertex `j` sits in part `j % r`, slot `j / r`; the slot fits because `j < n`
    let f : Fin n → H.V := fun j =>
      ⟨⟨j.val % r, show j.val % r < L.length from hLlen.symm ▸ Nat.mod_lt _ hpos_r⟩, ⟨j.val / r, by
        rw [hLget ⟨j.val % r, Nat.mod_lt _ hpos_r⟩]
        dsimp only
        have hj : (j : ℕ) < n := j.isLt
        have hdj := Nat.div_add_mod (j : ℕ) r
        have hdn := Nat.div_add_mod n r
        have hdle : (j : ℕ) / r ≤ n / r := Nat.div_le_div_right hj.le
        split_ifs with hlt
        · omega
        · rcases eq_or_lt_of_le hdle with heq | hlt2
          · rw [heq] at hdj
            omega
          · exact hlt2⟩⟩
    have hf_inj : Function.Injective f := by
      intro ⟨j1, hj1⟩ ⟨j2, hj2⟩ hfeq
      have hf1 : (j1 : ℕ) % r = (j2 : ℕ) % r := by
        have h1 := congr_arg (fun x : H.V => x.1.val) hfeq
        simp [f] at h1 ⊢
        exact h1
      have hf2 : (j1 : ℕ) / r = (j2 : ℕ) / r := by
        have := congr_arg (fun x : H.V => x.2.val) hfeq
        simp [f] at this
        exact this
      have hdecomp1 := Nat.div_add_mod j1 r
      have hdecomp2 := Nat.div_add_mod j2 r
      clear f hfeq hLget hLlen hpos_r hmod_lt
      have heq : j1 = j2 := by
        rw [← hdecomp1, ← hdecomp2, hf1, hf2]
      exact Fin.ext heq
    have hf_adj : ∀ j1 j2 : Fin n, H.Adj (f j1) (f j2) ↔ (j1.val % r ≠ j2.val % r) := by
      intro j1 j2
      rw [CGraph.completeMultipartite_adj]
      simp [f]
    -- `2t` and `2t + 1` are never congruent mod `r ≥ 2`
    have hedge : ∀ t : Fin (n / 2),
        H.Adj (f ⟨2 * t.val, by omega⟩) (f ⟨2 * t.val + 1, by omega⟩) := by
      intro t
      rw [hf_adj]
      intro h
      have hdvd : r ∣ 1 := by simpa using (Nat.modEq_iff_dvd' (Nat.le_succ _)).1 h
      have := Nat.le_of_dvd one_pos hdvd
      omega
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun t : Fin (n / 2) ↦ f ⟨2 * t.val, by omega⟩)
      (fun t : Fin (n / 2) ↦ f ⟨2 * t.val + 1, by omega⟩) hedge ?_)
    intro t t' htt'
    have hne : ∀ (x y : ℕ) (hx : x < n) (hy : y < n), x ≠ y → f ⟨x, hx⟩ ≠ f ⟨y, hy⟩ :=
      fun _ _ _ _ hxy he ↦ hxy (congrArg Fin.val (hf_inj he))
    have ht : (t : ℕ) ≠ (t' : ℕ) := fun hval ↦ htt' (Fin.ext hval)
    exact ⟨hne _ _ _ _ (by omega), hne _ _ _ _ (by omega), hne _ _ _ _ (by omega),
      hne _ _ _ _ (by omega)⟩

end IsoGraph

namespace CGraph

/-- The crown graph on eight vertices is the four-rung prism: both are `K₄ × K₂`, once as a tensor
product and once as a cartesian one. -/
def crownFour : crown 4 ≃cg prism 4 :=
  isoOfAdj
    (⟨fun p ↦ ![![(0, 0), (2, 1)], ![(2, 0), (0, 1)], ![(1, 1), (3, 0)], ![(3, 1), (1, 0)]]
        p.1 p.2,
      fun p ↦ ![![(0, 0), (1, 1)], ![(3, 1), (2, 0)], ![(1, 0), (0, 1)], ![(2, 1), (3, 0)]]
        p.1 p.2, by decide, by decide⟩ :
        (Fin 4 × Fin 2) ≃ (Fin 4 × Fin 2))
    (by decide)

end CGraph

namespace IsoGraph

/-- The crown graph on eight vertices is the cube: both are `K₄ × K₂`, once as a tensor product
and once as the four-rung prism. -/
theorem crown_four : crown 4 = hypercube 3 := by
  rw [hypercube_three]
  show complete 4 ⊗g complete 2 = cycle 4 □g complete 2
  simp only [isoTransfer]
  exact Quotient.sound ⟨CGraph.crownFour⟩

end IsoGraph
