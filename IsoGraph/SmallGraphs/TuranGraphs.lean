import IsoGraph.SmallGraphs.Circulants

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

theorem matchNum_crown (n : ℕ) : (crown (n + 2)).matchNum = n + 2 := by
  rw [matchNum_eq]
  apply le_antisymm
  · have h1 := two_mul_matchNum_le_V (crown (n + 2))
    rw [V_crown] at h1
    rw [matchNum_eq] at h1; omega
  · -- Lower bound: construct indep set of size n+2 in lineGraph
    show n + 2 ≤ (IsoGraph.lineGraph (complete (n + 2) ⊗g complete 2)).indepNum
    simp only [IsoGraph.complete_def, IsoGraph.tensorProduct_mk, IsoGraph.lineGraph_mk,
      IsoGraph.indepNum_mk]
    -- Goal: n + 2 ≤ the line graph's independence number
    -- indepNum for CGraph = toSimple.indepNum
    -- We exhibit n+2 pairwise disjoint edges of the tensorProduct graph.
    set m := n + 2
    set H := CGraph.complete m ⊗g CGraph.complete 2
    -- Vertex type of H: Fin m × Fin 2
    -- Edge i: between (i, 0) and (i+1, 1) in Fin m × Fin 2
    -- These are edges since i ≠ i+1 (mod m, and m ≥ 2) and 0 ≠ 1.
    -- They're pairwise disjoint.
    have hm2 : 2 ≤ m := by omega
    -- The edge as a vertex of lineGraph H
    let mkEdge : Fin m → (H.lineGraph).V := fun i =>
      ⟨Sym2.mk ((i, (0 : Fin 2)), ((i + 1 : Fin m), (1 : Fin 2))), by
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.tensorProduct_adj,
          CGraph.complete_adj, CGraph.complete_adj]
        simp⟩
    -- Show mkEdge is injective
    have h_inj : Function.Injective mkEdge := by
      intro i j hij
      have hsym2 : Sym2.mk ((i, (0 : Fin 2)), ((i + 1 : Fin m), (1 : Fin 2))) =
        Sym2.mk ((j, (0 : Fin 2)), ((j + 1 : Fin m), (1 : Fin 2))) := by
        exact congr_arg Subtype.val hij
      rw [Sym2.eq_iff] at hsym2
      rcases hsym2 with h | h
      · exact congr_arg (fun p : Fin m × Fin 2 => p.1) h.1
      · exfalso
        have := congr_arg (fun v : Fin m × Fin 2 => v.2) h.1
        simp at this
    -- The image finset
    let s := Finset.univ.image mkEdge
    have hcard : s.card = n + 2 := by
      rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]
    -- Show no shared vertices between distinct edges (as Finset membership)
    have hno_share : ∀ i j : Fin m, i ≠ j →
        ∀ v, v ∈ (mkEdge i).val → v ∉ (mkEdge j).val := by
      intro i j hij v hv1 hv2
      simp [mkEdge] at hv1 hv2
      rcases hv1 with rfl | hv1
      · rcases hv2 with hv2 | hv2
        · exfalso; apply hij; exact congr_arg Prod.fst hv2
        · exfalso; have := congr_arg Prod.snd hv2; simp at this
          exact absurd this (Fin.ne_of_val_ne (by decide))
      · rcases hv2 with hv2 | hv2
        · exfalso
          have h := hv1.symm.trans hv2
          have := congr_arg Prod.snd h
          simp at this
          exact absurd this (Fin.ne_of_val_ne (by decide))
        · exfalso; apply hij
          have h1 : (i + 1 : Fin m) = j + 1 := congr_arg Prod.fst (hv1.symm.trans hv2)
          simp at h1
          exact Fin.ext (by omega)
    -- Show s is an independent set in lineGraph H
    have hind : (H.lineGraph).toSimple.IsIndepSet (s : Set (H.lineGraph.V)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro e he f hf hef
      obtain ⟨i, _, heq⟩ := Finset.mem_coe.mp he |> Finset.mem_image.mp
      obtain ⟨j, _, hfq⟩ := Finset.mem_coe.mp hf |> Finset.mem_image.mp
      subst heq; subst hfq
      by_cases h : i = j
      · exact absurd (h ▸ rfl) hef
      · simp [CGraph.toSimple_adj, CGraph.lineGraph_adj, h_inj.ne h]
        exact fun v hv1 => hno_share i j h v hv1
    rw [show m = n + 2 from rfl]
    exact hcard.symm.le.trans (hind.card_le_indepNum)

theorem matchNum_friendship (n : ℕ) : (friendship n).matchNum = n := by
  apply le_antisymm
  · -- Upper bound: 2 * matchNum ≤ V = 2*n+1, so matchNum ≤ n
    have h := (friendship n).two_mul_matchNum_le_V
    rw [V_friendship] at h
    omega
  · -- Lower bound: exhibit n pairwise disjoint edges (one from each triangle)
    rw [matchNum_eq]
    rw [friendship]
    have join_mk : ∀ (G H : CGraph),
          ⟦G⟧ ∇g ⟦H⟧ = ⟦G ∇g H⟧ := by
      intro G H
      rw [IsoGraph.join, compl_mk, compl_mk, disjUnion_mk, compl_mk]
      rfl
    simp only [IsoGraph.complete, IsoGraph.empty]
    simp only [cartesianProduct_mk]
    rw [join_mk, IsoGraph.lineGraph_mk, IsoGraph.indepNum_mk]
    -- Goal: n ≤ the line graph's independence number
    set G' : CGraph :=
      CGraph.complete 1 ∇g CGraph.empty n □g CGraph.complete 2
    let mkEdge : Fin n → Sym2 G'.V :=
      fun i => Sym2.mk (Sum.inr (i, (0 : Fin 2)), Sum.inr (i, (1 : Fin 2)))
    have hedge : ∀ i : Fin n, mkEdge i ∈ G'.toSimple.edgeSet := by
      intro i
      rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.join_adj_inr_inr,
        CGraph.cartesianProduct_adj, CGraph.empty_adj, CGraph.complete_adj]
      simp
    let lineVer : Fin n → (CGraph.lineGraph G').V := fun i => ⟨mkEdge i, hedge i⟩
    have hrung_inj : Function.Injective lineVer := by
      intro i j hij
      let e : Sym2 G'.V := mkEdge j
      have hval : mkEdge i = e := by
        exact congrArg Subtype.val hij
      have hmem : (Sum.inr (i, (0 : Fin 2)) : G'.V) ∈ e := by
        rw [← hval]
        exact Sym2.mem_iff.mpr (Or.inl rfl)
      rcases Sym2.mem_iff.mp hmem with h | h <;> simp at h
      · obtain ⟨hi, _⟩ := Prod.ext_iff.mp h; exact hi
      · exfalso; apply_fun (fun p : Fin n × Fin 2 => p.2) at h; simp at h
    have hrung_not_adj :
        ∀ i j : Fin n, i ≠ j → ¬(CGraph.lineGraph G').toSimple.Adj (lineVer i) (lineVer j) := by
      intro i j hij
      rw [CGraph.toSimple_adj, CGraph.lineGraph_adj]
      have : ¬∃ v, v ∈ (lineVer i).1 ∧ v ∈ (lineVer j).1 := by
        intro ⟨v, hv_i, hv_j⟩
        simp [lineVer, mkEdge, Sym2.mem_iff] at hv_i hv_j
        rcases hv_i with rfl | rfl
        · rcases hv_j with h | h
          · exfalso; apply hij; exact Prod.ext_iff.mp (Sum.inr.inj h) |>.1
          · exfalso; have := congr_arg (fun p : Fin n × Fin 2 => p.2) (Sum.inr.inj h); simp at this
        · rcases hv_j with h | h
          · exfalso; have := congr_arg (fun p : Fin n × Fin 2 => p.2) (Sum.inr.inj h); simp at this
          · exfalso; apply hij; exact Prod.ext_iff.mp (Sum.inr.inj h) |>.1
      simp [this, hrung_inj.ne hij]
    have hrung_indep :
        (CGraph.lineGraph G').toSimple.IsIndepSet
          (Finset.univ.image lineVer : Set (CGraph.lineGraph G').V) := by
      intro e he f hf hef
      rw [Finset.coe_image, Set.mem_image] at he hf
      obtain ⟨i, _, rfl⟩ := he
      obtain ⟨j, _, rfl⟩ := hf
      exact hrung_not_adj i j (by intro h; exact hef (h ▸ rfl))
    have hrung_card : (Finset.univ.image lineVer).card = n := by
      rw [Finset.card_image_of_injective _ hrung_inj, Finset.card_univ, Fintype.card_fin]
    have := hrung_indep.card_le_indepNum
    rw [hrung_card] at this
    exact this

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
  haveI : Nonempty ((CGraph.complete (n+3)).tensorProduct (CGraph.complete 2)).V :=
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
  let G : SimpleGraph (Fin (n + 3) × Fin 2) :=
    (CGraph.complete (n + 3) ⊗g CGraph.complete 2).toSimple
  have h_adj : ∀ p q : Fin (n + 3) × Fin 2, G.Adj p q ↔ p.1 ≠ q.1 ∧ p.2 ≠ q.2 := by
    intro p q
    simp [G, CGraph.toSimple_adj, CGraph.tensorProduct_adj, CGraph.complete_adj]
  change G.diam = 3
  set a0 : Fin (n + 3) := ⟨0, by omega⟩
  set a1 : Fin (n + 3) := ⟨1, by omega⟩
  set a2 : Fin (n + 3) := ⟨2, by omega⟩
  have ha0_ne_a1 : a0 ≠ a1 := by simp [a0, a1]
  have ha0_ne_a2 : a0 ≠ a2 := by simp [a0, a2]
  have ha1_ne_a2 : a1 ≠ a2 := by simp [a1, a2]
  have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x; rcases x with ⟨_ | _ | _, _⟩ <;> simp
    omega
  -- Helpers for Fin 2 inequalities
  have h0_ne_1 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  -- Any walk of length ≤ 2 from (a0,0) to (a0,1) is impossible
  -- (a0,0) and (a0,1) share a first coordinate, and their second coordinates exhaust Fin 2
  have h_not_adj : ¬G.Adj (a0, 0) (a0, 1) := by simp [h_adj]
  have h_no_common_neighbor :
      ∀ w : Fin (n + 3) × Fin 2, G.Adj (a0, 0) w → G.Adj w (a0, 1) → False := by
    intro w hw1 hw2
    rw [h_adj] at hw1 hw2
    rcases hfin2 w.2 with h2 | h2 <;> simp [h2] at hw1 hw2
  -- Walk of length 3: (a0,0)-(a1,1)-(a2,0)-(a0,1)
  have h_adj_01 : G.Adj (a0, 0) (a1, 1) := by simp [h_adj]; tauto
  have h_adj_12 : G.Adj (a1, 1) (a2, 0) := by simp [h_adj]; tauto
  have h_adj_23 : G.Adj (a2, 0) (a0, 1) := by simp [h_adj]; tauto
  let w3 : G.Walk (a0, 0) (a0, 1) :=
    SimpleGraph.Walk.cons h_adj_01
      (SimpleGraph.Walk.cons h_adj_12
        (SimpleGraph.Walk.cons h_adj_23 (SimpleGraph.Walk.nil)))
  have hw3_len : w3.length = 3 := by simp [w3]
  -- All walks from (i,x) to (j,y) have parity of length = (x ≠ y ? odd : even)
  -- G is bipartite: color by second coordinate
  let color : Fin (n + 3) × Fin 2 → Bool := fun p => decide (p.2 = 1)
  have h_color_flip : ∀ p q, G.Adj p q → color p ≠ color q := by
    intro p q hpq
    rw [h_adj] at hpq
    unfold color at ⊢
    rcases hfin2 p.2 with hp2 | hp2 <;> rcases hfin2 q.2 with hq2 | hq2 <;> simp [hp2, hq2] at hpq ⊢
  have h_bip : G.IsBipartite := by
    exact ⟨fun p => if color p then 1 else 0, fun {p q} hpq => by
      have hcf := h_color_flip p q hpq
      simp [color] at hcf ⊢
      split_ifs at hcf ⊢ <;> simp_all⟩
  -- parity of walk length relates to colors of endpoints
  have h_walk_parity_gen : ∀ {u v : Fin (n + 3) × Fin 2} (w : G.Walk u v),
      (color u = color v ↔ Even w.length) ∧ (color u ≠ color v ↔ Odd w.length) := by
    intro u v w
    induction w using SimpleGraph.Walk.recOn with
    | nil => simp
    | @cons u' v' w' huv tail ih =>
      rw [SimpleGraph.Walk.length_cons]
      have hflip : color u' ≠ color v' := h_color_flip u' v' huv
      have ⟨ih_iff1, ih_iff2⟩ := ih
      rcases hu : color u' with hu | hu <;>
      rcases hv : color v' with hv | hv <;>
      rcases hw : color w' with hw | hw <;>
      simp [hu, hv, hw] at hflip ih_iff1 ih_iff2 ⊢
      · -- false, true, false: Odd tail.length → Even (tail.length + 1)
        obtain ⟨k, hk⟩ := ih_iff2; rw [hk]; simp [Nat.even_add]
      · -- false, true, true: Even tail.length → Odd (tail.length + 1)
        obtain ⟨k, hk⟩ := ih_iff1; rw [hk]; simp
      · -- true, false, false: Even tail.length → Odd (tail.length + 1)
        obtain ⟨k, hk⟩ := ih_iff1; rw [hk]; simp
      · -- true, false, true: Odd tail.length → Even (tail.length + 1)
        obtain ⟨k, hk⟩ := ih_iff2; rw [hk]; simp [Nat.even_add]
  have hcolor_0 : color (a0, 0) = false := by simp [color]
  have hcolor_1 : color (a0, 1) = true := by simp [color]
  have hcolor_diff : color (a0, 0) ≠ color (a0, 1) := by simp [hcolor_0, hcolor_1]
  -- Reachability
  have h_reach : G.Reachable (a0, 0) (a0, 1) := ⟨w3⟩
  have h_ne_verts : ((a0, 0) : Fin (n + 3) × Fin 2) ≠ (a0, 1) := by simp
  -- Any walk from (a0,0) to (a0,1) has odd length
  have h_walk_odd : ∀ (w : G.Walk (a0, 0) (a0, 1)), Odd w.length := by
    intro w; exact (h_walk_parity_gen w).2.mp hcolor_diff
  -- No walk of length 0 or 1
  have h_walk_len_pos : ∀ (w : G.Walk (a0, 0) (a0, 1)), 0 < w.length := by
    intro w
    by_contra h
    push_neg at h
    have hlen0 : w.length = 0 := by omega
    rcases w with ⟨_ | _, _⟩; simp [SimpleGraph.Walk.length] at hlen0
  -- No walk of length 1 (not adjacent)
  have h_walk_ne_1 : ∀ (w : G.Walk (a0, 0) (a0, 1)), w.length ≠ 1 := by
    intro w hw
    have hadj : G.Adj (a0, 0) (a0, 1) := by
      have hlen : w.length = 1 := hw
      exact w.adj_of_length_eq_one hlen
    exact h_not_adj hadj
  -- Any walk from (a0,0) to (a0,1) has length ≥ 3
  have h_walk_len_ge_3 : ∀ (w : G.Walk (a0, 0) (a0, 1)), 3 ≤ w.length := by
    intro w
    have hoa := h_walk_odd w
    have hne0 := h_walk_len_pos w
    have hne1 := h_walk_ne_1 w
    rcases hoa with ⟨k, hk⟩
    rcases k with _ | _ | k <;> simp [hk] at hne0 hne1 ⊢
  -- edist ≥ 3 via walk-length lower bound
  have h_edist_ge_3 : 3 ≤ G.edist (a0, 0) (a0, 1) := by
    by_contra hlt
    push_neg at hlt
    -- edist < 3, so there exists a walk of length < 3 (in ℕ)
    -- edist is an infimum over walks, so a bound below 3 exhibits a walk shorter than 3.
    have h_reach' : G.Reachable (a0, 0) (a0, 1) := h_reach
    have h_lt_nat : ∃ w : G.Walk (a0, 0) (a0, 1), w.length < 3 := by
      rw [SimpleGraph.edist] at hlt
      have hne : (⨅ w : G.Walk (a0, 0) (a0, 1), (w.length : ℕ∞)) < 3 := hlt
      have hnonempty : Nonempty (G.Walk (a0, 0) (a0, 1)) :=
        ⟨h_reach'.some⟩
      have := exists_lt_of_ciInf_lt hne
      obtain ⟨w, hw⟩ := this
      exact ⟨w, WithTop.coe_lt_coe.mp hw⟩
    exact absurd h_lt_nat (not_exists.mpr fun w => not_lt.mpr (h_walk_len_ge_3 w))
  -- edist ≤ 3
  have h_edist_le_3 : G.edist (a0, 0) (a0, 1) ≤ 3 := by
    calc G.edist (a0, 0) (a0, 1) ≤ ↑w3.length := SimpleGraph.edist_le w3
      _ ≤ 3 := by rw [hw3_len]; exact WithTop.coe_le_coe.mpr le_rfl
  -- So edist (a0,0) (a0,1) = 3
  have h_edist_eq_3 : G.edist (a0, 0) (a0, 1) = 3 := by
    exact le_antisymm h_edist_le_3 h_edist_ge_3
  -- Key adjacencies
  have h_from_hub0 : ∀ i : Fin (n + 3), i ≠ a0 → G.Adj (a0, 0) (i, 1) := by
    intro i hi; rw [h_adj]; exact ⟨hi.symm, h0_ne_1⟩
  have h_from_hub1 : ∀ i : Fin (n + 3), i ≠ a0 → G.Adj (a0, 1) (i, 0) := by
    intro i hi; rw [h_adj]; exact ⟨hi.symm, h0_ne_1.symm⟩
  have h_to_hub0 : ∀ i : Fin (n + 3), i ≠ a0 → G.Adj (i, 0) (a0, 1) := by
    intro i hi; rw [h_adj]; exact ⟨hi, h0_ne_1⟩
  -- Hub pick: given i ≠ j, find k ∈ {a0,a1,a2} with a0 ≠ k, a1 ≠ k, a2 ≠ k... no, k ≠ i and k ≠ j
  have h_hub_pick : ∀ (i j : Fin (n + 3)), i ≠ j →
      ∃ k : Fin (n + 3), k ≠ i ∧ k ≠ j ∧ (k = a0 ∨ k = a1 ∨ k = a2) := by
    intro i j hij
    -- At least one of a0,a1,a2 is ≠ i and ≠ j, since |{i,j}| ≤ 2 < 3.
    -- We case-split on whether i ∈ {a0,a1,a2}.
    by_cases hi0 : i = a0
    · subst hi0
      by_cases hj0 : j = a0
      · exfalso; exact hij hj0.symm
      by_cases hj1 : j = a1
      · subst hj1; exact ⟨a2, ha0_ne_a2.symm, ha1_ne_a2.symm, Or.inr (Or.inr rfl)⟩
      · by_cases hj2 : j = a2
        · subst hj2; exact ⟨a1, ha0_ne_a1.symm, ha1_ne_a2, Or.inr (Or.inl rfl)⟩
        · exact ⟨a1, ha0_ne_a1.symm, Ne.symm hj1, Or.inr (Or.inl rfl)⟩
    · by_cases hi1 : i = a1
      · subst hi1
        by_cases hj1 : j = a1
        · exfalso; exact hij hj1.symm
        by_cases hj0 : j = a0
        · subst hj0; exact ⟨a2, ha1_ne_a2.symm, ha0_ne_a2.symm, Or.inr (Or.inr rfl)⟩
        · by_cases hj2 : j = a2
          · subst hj2; exact ⟨a0, ha0_ne_a1, ha0_ne_a2, Or.inl rfl⟩
          · exact ⟨a0, ha0_ne_a1, Ne.symm hj0, Or.inl rfl⟩
      · by_cases hi2 : i = a2
        · subst hi2
          by_cases hj2 : j = a2
          · exfalso; exact hij hj2.symm
          by_cases hj0 : j = a0
          · subst hj0; exact ⟨a1, ha1_ne_a2, ha0_ne_a1.symm, Or.inr (Or.inl rfl)⟩
          · by_cases hj1 : j = a1
            · subst hj1; exact ⟨a0, ha0_ne_a2, ha0_ne_a1, Or.inl rfl⟩
            · exact ⟨a0, ha0_ne_a2, Ne.symm hj0, Or.inl rfl⟩
        · -- i ≠ a0,a1,a2
          by_cases hj0 : j = a0
          · subst hj0; exact ⟨a1, Ne.symm hi1, ha0_ne_a1.symm, Or.inr (Or.inl rfl)⟩
          · by_cases hj1 : j = a1
            · subst hj1; exact ⟨a0, Ne.symm hi0, ha0_ne_a1, Or.inl rfl⟩
            · by_cases hj2 : j = a2
              · subst hj2; exact ⟨a0, Ne.symm hi0, ha0_ne_a2, Or.inl rfl⟩
              · exact ⟨a0, Ne.symm hi0, Ne.symm hj0, Or.inl rfl⟩
  -- Extra hub adjacencies
  have h_from_hub_a1_0 : ∀ i : Fin (n + 3), i ≠ a1 → G.Adj (a1, 0) (i, 1) := by
    intro i hi; rw [h_adj]; exact ⟨hi.symm, h0_ne_1⟩
  have h_from_hub_a1_1 : ∀ i : Fin (n + 3), i ≠ a1 → G.Adj (a1, 1) (i, 0) := by
    intro i hi; rw [h_adj]; exact ⟨hi.symm, h0_ne_1.symm⟩
  have h_from_hub_a2_0 : ∀ i : Fin (n + 3), i ≠ a2 → G.Adj (a2, 0) (i, 1) := by
    intro i hi; rw [h_adj]; exact ⟨hi.symm, h0_ne_1⟩
  have h_from_hub_a2_1 : ∀ i : Fin (n + 3), i ≠ a2 → G.Adj (a2, 1) (i, 0) := by
    intro i hi; rw [h_adj]; exact ⟨hi.symm, h0_ne_1.symm⟩
  have h_to_hub_a1_0 : ∀ i : Fin (n + 3), i ≠ a1 → G.Adj (i, 0) (a1, 1) := by
    intro i hi; rw [h_adj]; exact ⟨hi, h0_ne_1⟩
  have h_to_hub_a1_1 : ∀ i : Fin (n + 3), i ≠ a1 → G.Adj (i, 1) (a1, 0) := by
    intro i hi; rw [h_adj]; exact ⟨hi, h0_ne_1.symm⟩
  have h_to_hub_a2_0 : ∀ i : Fin (n + 3), i ≠ a2 → G.Adj (i, 0) (a2, 1) := by
    intro i hi; rw [h_adj]; exact ⟨hi, h0_ne_1⟩
  have h_to_hub_a2_1 : ∀ i : Fin (n + 3), i ≠ a2 → G.Adj (i, 1) (a2, 0) := by
    intro i hi; rw [h_adj]; exact ⟨hi, h0_ne_1.symm⟩
  -- Two distinct hubs ≠ any given i
  have h_two_hub_ne : ∀ i : Fin (n + 3), ∃ k m : Fin (n + 3), k ≠ i ∧ m ≠ i ∧ k ≠ m ∧
      (k = a0 ∨ k = a1 ∨ k = a2) ∧ (m = a0 ∨ m = a1 ∨ m = a2) := by
    intro i
    by_cases hi0 : i = a0
    · subst hi0
      exact ⟨a1, a2, ha0_ne_a1.symm, ha0_ne_a2.symm, ha1_ne_a2, Or.inr (Or.inl rfl),
        Or.inr (Or.inr rfl)⟩
    · by_cases hi1 : i = a1
      · subst hi1
        exact ⟨a0, a2, ha0_ne_a1, ha1_ne_a2.symm, ha0_ne_a2, Or.inl rfl,
          Or.inr (Or.inr rfl)⟩
      · by_cases hi2 : i = a2
        · subst hi2
          exact ⟨a0, a1, ha0_ne_a2, ha1_ne_a2, ha0_ne_a1, Or.inl rfl,
            Or.inr (Or.inl rfl)⟩
        · exact ⟨a0, a1, Ne.symm hi0, Ne.symm hi1, ha0_ne_a1, Or.inl rfl, Or.inr (Or.inl rfl)⟩
  -- Walk (i,x) → (i, 1-x) of length 3 for any i
  have h_walk_flip : ∀ (i : Fin (n + 3)) (x : Fin 2), G.edist (i, x) (i, 1 - x) ≤ 3 := by
    intro i x
    obtain ⟨k, m, hki, hmi, hkm, hkm_mem, hm_mem⟩ := h_two_hub_ne i
    have hx_ne : x ≠ 1 - x := by
      rcases hfin2 x with rfl | rfl <;> simp [h0_ne_1]
    let ed1 : G.Adj (i, x) (k, 1 - x) := by
      rw [h_adj]; simp; exact ⟨Ne.symm hki, hx_ne⟩
    let ed2 : G.Adj (k, 1 - x) (m, x) := by
      rw [h_adj]; simp; exact ⟨hkm, hx_ne.symm⟩
    let ed3 : G.Adj (m, x) (i, 1 - x) := by
      rw [h_adj]; simp; exact ⟨hmi, hx_ne⟩
    have h1' : G.edist (i, x) (k, 1 - x) ≤ 1 := by
      exact le_trans (G.edist_le (SimpleGraph.Walk.cons ed1 SimpleGraph.Walk.nil)) (by simp)
    have h2' : G.edist (k, 1 - x) (m, x) ≤ 1 := by
      exact le_trans (G.edist_le (SimpleGraph.Walk.cons ed2 SimpleGraph.Walk.nil)) (by simp)
    have h3' : G.edist (m, x) (i, 1 - x) ≤ 1 := by
      exact le_trans (G.edist_le (SimpleGraph.Walk.cons ed3 SimpleGraph.Walk.nil)) (by simp)
    calc G.edist (i, x) (i, 1 - x)
        ≤ G.edist (i, x) (k, 1 - x) + G.edist (k, 1 - x) (i, 1 - x) := G.edist_triangle
      _ ≤ G.edist (i, x) (k, 1 - x) + (G.edist (k, 1 - x) (m, x) + G.edist (m, x) (i, 1 - x)) := by
          gcongr; exact G.edist_triangle
      _ ≤ 1 + (1 + 1) := by gcongr
      _ = 3 := by norm_cast
  -- All pairwise edist ≤ 3
  have h_edist_le_three : ∀ (u v : Fin (n + 3) × Fin 2), G.edist u v ≤ 3 := by
    intro ⟨i, x⟩ ⟨j, y⟩
    by_cases h1 : i = j
    · subst h1
      by_cases h2 : x = y
      · subst h2; rw [SimpleGraph.edist_self]; exact le_trans (by simp) (le_refl (3 : ℕ∞))
      · have : y = 1 - x := by
          rcases hfin2 x with rfl | rfl <;> rcases hfin2 y with rfl | rfl <;> simp at h2 ⊢
        rw [this]; exact h_walk_flip i x
    · by_cases h2 : x = y
      · obtain ⟨k, hk_ne_i, hk_ne_j, hk_mem⟩ := h_hub_pick i j h1
        have hflip_adj1 : G.Adj (i, x) (k, 1 - x) := by
          rw [h_adj]; simp
          exact ⟨Ne.symm hk_ne_i, by rcases hfin2 x with rfl | rfl <;> simp [h0_ne_1]⟩
        have hflip_adj2 : G.Adj (k, 1 - x) (j, x) := by
          rw [h_adj]; simp; exact ⟨hk_ne_j, by rcases hfin2 x with rfl | rfl <;> simp [h0_ne_1]⟩
        have h1' : G.edist (i, x) (k, 1 - x) ≤ 1 := by
          exact le_trans (G.edist_le (SimpleGraph.Walk.cons hflip_adj1 SimpleGraph.Walk.nil))
            (by simp)
        have h2' : G.edist (k, 1 - x) (j, x) ≤ 1 := by
          exact le_trans (G.edist_le (SimpleGraph.Walk.cons hflip_adj2 SimpleGraph.Walk.nil))
            (by simp)
        subst h2
        calc G.edist (i, x) (j, x)
            ≤ G.edist (i, x) (k, 1 - x) + G.edist (k, 1 - x) (j, x) := G.edist_triangle
          _ ≤ 1 + 1 := by gcongr
          _ ≤ 3 := by decide
      · have hadj : G.Adj (i, x) (j, y) := by
          rw [h_adj]; simp
          exact ⟨h1, by
            rcases hfin2 x with rfl | rfl <;> rcases hfin2 y with rfl | rfl <;> simp at h2 ⊢⟩
        have : G.edist (i, x) (j, y) ≤ 1 := by
          exact le_trans (G.edist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)) (by simp)
        exact this.trans (by norm_cast)
  have h_ediam_le : G.ediam ≤ 3 := SimpleGraph.ediam_le_of_edist_le h_edist_le_three
  have h_ediam_ge : (3 : ℕ∞) ≤ G.ediam := by
    rw [← h_edist_eq_3]
    exact SimpleGraph.edist_le_ediam
  have h_ediam_eq : G.ediam = 3 := le_antisymm h_ediam_le h_ediam_ge
  rw [SimpleGraph.diam, h_ediam_eq]
  rfl

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
  rw [h3]
  rw [add_comm]
  -- Goal: sort ({2*n+2} + replicate (2*n+2) 2) (· ≤ ·) = replicate (2*n+2) 2 ++ [2*n+2]
  -- I need to prove a sort equality. Let me use the approach from sort_replicate_append inline.
  set m := 2 * n + 2
  set l := List.replicate m 2 ++ [m]
  have hperm : (l : Multiset ℕ) = Multiset.replicate m 2 + {m} := by
    simp [l]
    have : ∀ (l1 l2 : List ℕ), (l1 ++ l2 : Multiset ℕ) = (l1 : Multiset ℕ) + (l2 : Multiset ℕ) := by
      intro l1 l2; induction l1 with
      | nil => simp
      | cons a t ih => simp
    rw [this, Multiset.coe_replicate, Multiset.coe_singleton]
  -- l is pairwise sorted: twos inside the block, and every two is at most the hub degree
  have hl_sorted : List.Pairwise (fun x1 x2 => x1 ≤ x2) l := by
    simp [l, List.pairwise_append, List.pairwise_replicate]
    omega
  have hsort_sorted : List.Pairwise (fun x1 x2 => x1 ≤ x2)
      (Multiset.sort ({m} + Multiset.replicate m 2) (fun x1 x2 => x1 ≤ x2)) :=
    Multiset.pairwise_sort _ _
  have hperm2 : (Multiset.sort ({m} + Multiset.replicate m 2) (fun x1 x2 => x1 ≤ x2) : Multiset ℕ) =
      ({m} + Multiset.replicate m 2 : Multiset ℕ) := by
    exact Multiset.sort_eq _ _
  have hperm4 :
      (Multiset.sort ({m} + Multiset.replicate m 2) (fun x1 x2 => x1 ≤ x2) : List ℕ).Perm l := by
    exact Multiset.coe_eq_coe.mp (hperm2.trans (hperm.symm ▸ Multiset.add_comm _ _))
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba) hsort_sorted
    hl_sorted hperm4

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
        push_neg at hadj
        have hlen_pos : 1 < L.length := by rw [hlen']; omega
        obtain ⟨k, hk⟩ : ∃ k : Fin L.length, k ≠ u.1 := by
          by_contra h'
          push_neg at h'
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
    clear n h
    have hm : r * (m + 1) = r * m + r := Nat.mul_succ r m
    have hle : r * m ≤ r * m + s := by omega
    have hlt : r * m + s < r * m + r := by omega
    have hlt2 : r * m + s < r * (m + 1) := by rw [hm]; omega
    have upper : (r * m + s) / r < m + 1 := Nat.div_lt_of_lt_mul hlt2
    have lower : m ≤ (r * m + s) / r := by
      rw [Nat.le_div_iff_mul_le hr]
      rw [mul_comm]
      omega
    omega
  have sub_one_div (q : ℕ) : (r * (q + 1) - 1) / r = q := by
    clear n h div_helper
    have hm : r * (q + 1) = r * q + r := Nat.mul_succ r q
    have hge : r * q ≤ r * (q + 1) - 1 := by rw [hm]; omega
    have hlt : r * (q + 1) - 1 < r * (q + 1) := by omega
    exact le_antisymm
      (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hlt))
      (Nat.le_div_iff_mul_le hr |>.mpr (by rw [hm]; rw [mul_comm]; omega))
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
    have hnr1 : (r - 1) * q + (k - 1) = n - (q + 1) := by
      rw [hv1]
      have : (r - 1) * q + (k - 1) + (q + 1) = r * q + k := by
        have h1 : (r - 1) * q + q = r * q := by
          have hsub : r - 1 + 1 = r := Nat.sub_add_cancel hr
          have h2 : (r - 1) * q + q = ((r - 1) + 1) * q := by
            simp [add_mul]
          rw [h2, hsub]
        omega
      exact Eq.symm (Nat.sub_eq_of_eq_add this.symm)
    rw [hnr1.symm]
    have hkr : k - 1 + (r - k) = r - 1 := by omega
    have harg1_eq : (k - 1) * (q + 1) + (r - k) * q = (r - 1) * q + (k - 1) := by
      have h1 : (k - 1) * (q + 1) + (r - k) * q = ((k - 1) * q + (r - k) * q) + (k - 1) := by
        rw [Nat.mul_add]
        omega
      rw [h1, ← Nat.add_mul, hkr]
    have harg2_ge : k * (q + 1) + (r - k - 1) * q ≥ (r - 1) * q + (k - 1) := by
      have : k * q + k + (r - k - 1) * q ≥ (r - 1) * q + (k - 1) := by
        have : (r - 1) * q = (r - k - 1) * q + k * q := by
          have : r - 1 = r - k - 1 + k := by omega
          rw [this, Nat.add_mul]
        rw [this]
        omega
      exact this
    rw [harg1_eq]
    exact min_eq_left harg2_ge

/-- A Paley graph on `q` vertices has a near-perfect matching: the pairs `{2i, 2i+1}` are
edges, since `1` is always a square. -/
@[simp] theorem matchNum_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).matchNum = q / 2 := by
  have hupper : 2 * (paley q).matchNum ≤ q := by
    have := two_mul_matchNum_le_V (paley q)
    simp at this
    exact this
  have hle : (paley q).matchNum ≤ q / 2 := by omega
  set k := q / 2
  have hq2k1 : q = 2 * k + 1 := by omega
  have hq_ge_2 : 2 ≤ q := Nat.Prime.two_le Fact.out
  have hk_pos : 0 < k := Nat.div_pos hq_ge_2 (by omega)
  -- Work at CGraph level to exhibit a matching of size k in paley q.
  -- The edges {{2i, 2i+1} : i : Fin k} are pairwise disjoint edges of paley q.
  have hmatch_ge : k ≤ (paley q).matchNum := by
    rw [matchNum_eq]
    rw [IsoGraph.paley_def]
    rw [lineGraph_mk, indepNum_mk]
    -- Vertices of paley q are Fin q with values 0..q-1.
    -- Edges {{2i, 2i+1} | i : Fin k} are in paley q because difference = 1 is a QR.
    -- They are pairwise disjoint, giving an indep set of size k in lineGraph.
    set G' : CGraph := CGraph.paley q
    have h2i_lt : ∀ i : Fin k, (2 * (i : ℕ) : ℕ) < q := by
      intro i; omega
    have h2i1_lt : ∀ i : Fin k, (2 * (i : ℕ) + 1 : ℕ) < q := by
      intro i; omega
    let mkEdge : Fin k → Sym2 (Fin q) := fun i =>
      Sym2.mk ⟨(⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q), (⟨2 * (i : ℕ) + 1, h2i1_lt i⟩ : Fin q)⟩
    have hne2 : ∀ i : Fin k,
        (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) ≠ (⟨2 * (i : ℕ) + 1, h2i1_lt i⟩ : Fin q) := by
      intro i h
      have := congr_arg (fun x : Fin q => x.val) h
      simp at this
    -- Adjacency in paley q: need qrTable q[1]! = true
    have hadj_inner : ∀ i : Fin k,
        G'.Adj (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) (⟨2 * (i : ℕ) + 1, h2i1_lt i⟩ : Fin q) := by
      intro i
      let a : ZMod q := (2 * (i : ℕ) : ZMod q)
      let b : ZMod q := (2 * (i : ℕ) + 1 : ZMod q)
      have hiq_val : ((i : Fin k) : ZMod q).val = (i : ℕ) := by
        exact ZMod.val_cast_of_lt (by omega)
      have hval2 : ZMod.val (2 : ZMod q) = 2 := by
        rw [show (2 : ZMod q) = (2 : ℕ) by rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have hval1 : ZMod.val (1 : ZMod q) = 1 := by
        simp [ZMod.val_one]
      have ha_val : a.val = 2 * (i : ℕ) := by
        simp [a, ZMod.val_mul, hval2, hiq_val, Nat.mod_eq_of_lt (h2i_lt i)]
      have hb_val : b.val = 2 * (i : ℕ) + 1 := by
        simp [b, ZMod.val_mul, hval2, hiq_val, ZMod.val_add, hval1, Nat.mod_eq_of_lt (h2i1_lt i)]
      have h1 : (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) = zmodEquivFin q a := by
        ext; simp [zmodEquivFin, ha_val]
      have h2 : (⟨2 * (i : ℕ) + 1, h2i1_lt i⟩ : Fin q) = zmodEquivFin q b := by
        ext; simp [zmodEquivFin, hb_val]
      rw [h1, h2, CGraph.paley_adj_eq, CGraph.paleyField_adj]
      · have hba : b - a = (1 : ZMod q) := by simp [a, b]
        rw [hba]
        -- `paleyField` counts and compares with the instances its `FinEnum` induces, so the
        -- character here is not the one ambient typeclass search would find for `ZMod q`
        exact decide_eq_true
          ((CGraph.quadraticChar_eq_one_iff (F := ZMod q) 1).2 ⟨1, one_ne_zero, by ring⟩)
      · rw [← @FinEnum.card_eq_fintypeCard (ZMod q) _ FinEnum.instFintype]
        exact hq
    let edgeVer : Fin k → (CGraph.lineGraph G').V := fun i =>
      ⟨mkEdge i, by
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
        exact hadj_inner i⟩
    -- edgeVer is injective
    have heng_inj : Function.Injective edgeVer := by
      intro i j hij
      have hval : mkEdge i = mkEdge j := by
        exact congrArg Subtype.val hij
      have hmem : (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) ∈ (mkEdge j) := by
        rw [← hval]
        exact Sym2.mem_mk_left _ _
      rw [Sym2.mem_iff] at hmem; rcases hmem with h | h
      · -- ⟨2*i,...⟩ = ⟨2*j,...⟩ as Fin q, and 2*i, 2*j < q, so i = j
        have h' : (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) = ⟨2 * (j : ℕ), h2i_lt j⟩ := h
        have hval : (i : ℕ) = (j : ℕ) := by
          have := congr_arg (fun x : Fin q => x.val) h'
          simp at this
          exact this
        exact Fin.ext hval
      · -- ⟨2*i,...⟩ = ⟨2*j+1,...⟩ : Fin q, impossible by parity (both < q)
        exfalso
        have hval : 2 * (i : ℕ) = 2 * (j : ℕ) + 1 := by
          have := Fin.ext_iff.mp h
          simp at this
          exact this
        omega
    -- edgeVer images are pairwise non-adjacent (edges are disjoint)
    have heng_disjoint : ∀ i j : Fin k, i ≠ j →
        ∀ v, v ∉ (mkEdge i) ∨ v ∉ (mkEdge j) := by
      intro i j hij v
      by_contra h
      push_neg at h
      obtain ⟨hv1, hv2⟩ := h
      rw [Sym2.mem_iff] at hv1 hv2
      rcases hv1 with hv1 | hv1 <;> rcases hv2 with hv2 | hv2
      · -- v = 2i = 2j: gives i = j, contradicting hij
        exfalso
        have hfin : (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) = ⟨2 * (j : ℕ), h2i_lt j⟩ :=
          hv1.symm.trans hv2
        have := congr_arg (fun x : Fin q => x.val) hfin
        simp at this
        exact hij (Fin.ext this)
      · -- v = 2i = 2j+1: parity contradiction
        exfalso
        have hfin : (⟨2 * (i : ℕ), h2i_lt i⟩ : Fin q) = ⟨2 * (j : ℕ) + 1, h2i1_lt j⟩ :=
          hv1.symm.trans hv2
        have := congr_arg (fun x : Fin q => x.val) hfin
        simp at this
        omega
      · -- v = 2i+1 = 2j: parity contradiction
        exfalso
        have hfin : (⟨2 * (i : ℕ) + 1, h2i1_lt i⟩ : Fin q) = ⟨2 * (j : ℕ), h2i_lt j⟩ :=
          hv1.symm.trans hv2
        have := congr_arg (fun x : Fin q => x.val) hfin
        simp at this
        omega
      · -- v = 2i+1 = 2j+1: gives i = j, contradicting hij
        exfalso
        have hfin : (⟨2 * (i : ℕ) + 1, h2i1_lt i⟩ : Fin q) = ⟨2 * (j : ℕ) + 1, h2i1_lt j⟩ :=
          hv1.symm.trans hv2
        have := congr_arg (fun x : Fin q => x.val) hfin
        simp at this
        exact hij (Fin.ext this)
    have heng_not_adj : ∀ i j : Fin k, i ≠ j →
        ¬(CGraph.lineGraph G').toSimple.Adj (edgeVer i) (edgeVer j) := by
      intro i j hij
      rw [CGraph.toSimple_adj, CGraph.lineGraph_adj]
      simp [heng_inj.ne hij]
      intro v hv_i hv_j
      obtain h | h := heng_disjoint i j hij v <;> [exact h hv_i; exact h hv_j]
    -- Build the independent set
    let S : Set (CGraph.lineGraph G').V := Set.range edgeVer
    have hS_indep : SimpleGraph.IsIndepSet (CGraph.lineGraph G').toSimple S := by
      intro e he f hf hef
      obtain ⟨i, _, rfl⟩ := Set.mem_range.mp he
      obtain ⟨j, _, rfl⟩ := Set.mem_range.mp hf
      have hi : i ≠ j := fun h => hef (h ▸ rfl)
      exact heng_not_adj i j hi
    have hS_card : S.toFinset.card = k := by
      show (Set.range edgeVer).toFinset.card = k
      rw [Set.toFinset_range]
      rw [Finset.card_image_of_injective _ heng_inj, Finset.card_univ, Fintype.card_fin]
    have hS_indep' :
        SimpleGraph.IsIndepSet (CGraph.lineGraph (CGraph.paley q)).toSimple ↑S.toFinset := by
      rw [Set.coe_toFinset]
      exact hS_indep
    exact hS_card ▸ SimpleGraph.IsIndepSet.card_le_indepNum hS_indep'
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

/-- `fin_cases` enumerates a vertex type through the `Fintype` its `FinEnum` induces, which names
the elements `equiv.symm 0`, `equiv.symm 1`, … rather than as numerals; a `match` on `0`/`1` then
never reduces.  Stating the dichotomy on `Fin 2` itself sidesteps that: it applies to any vertex
type definitionally equal to `Fin 2`, and hands back the numerals. -/
private theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by decide +revert

/-- The friendship graph is class one: colour the spokes at the hub with `2n` colours and each
triangle edge with a colour missing at both of its ends. -/
theorem edgeChromNum_friendship (n : ℕ) :
    (friendship (n + 2)).edgeChromNum = 2 * n + 4 := by
  rw [edgeChromNum_eq]
  apply le_antisymm
  · -- Upper bound: need chromNum (lineGraph (friendship (n+2))) ≤ 2*n+4
    rw [show lineGraph (friendship (n + 2)) = ⟦(lineGraph (friendship (n + 2))).toCGraph⟧ from
      (IsoGraph.mk_toCGraph _).symm]
    rw [chromNum_mk, CGraph.chromNum_le_iff_colorable]
    simp only [friendship, complete_def, empty_def]
    haveI : DecidableEq (Fin 1) := inferInstance
    haveI : DecidableEq (Fin (n + 2)) := inferInstance
    haveI : DecidableEq (Fin 2) := inferInstance
    rw [cartesianProduct_mk, join_mk, lineGraph_mk]
    rw [IsoGraph.toCGraph_mk]
    set G' := (CGraph.complete 1).join ((CGraph.empty (n + 2)).cartesianProduct (CGraph.complete 2))
    set L' := CGraph.lineGraph G'
    let icanL : L'.canonicalize ≃cg L' := L'.isoCanonicalize.symm
    have htransfer : L'.toSimple.Colorable (2 * n + 4) →
           L'.canonicalize.toSimple.Colorable (2 * n + 4) := by
      intro ⟨c, hc⟩
      exact ⟨fun v => c (icanL v), fun {u v} huv => hc (icanL.toSimpleIso.map_rel_iff.mpr huv)⟩
    apply htransfer
    set m := n + 2
    -- We need L'.toSimple.Colorable (2 * m) where L' = lineGraph G'
    -- G'.V = Fin 1 ⊕ (Fin m × Fin 2)
    -- Edges of G': spokes {inl (), inr (i,b)} and rails {inr (i,0), inr (i,1)}
    -- Coloring of lineGraph G': color each edge (Sym2 of G'.V) with a value in Fin (2*m).
    -- spoke(i,b) ↦ 2*i + b, rail i ↦ (2*i + 2) % (2*m)
    let spokeColor : Fin m → Fin 2 → Fin (2 * m) := fun i b => ⟨2 * i.val + b.val, by omega⟩
    -- Define a function on Sym2 (Fin 1 ⊕ (Fin m × Fin 2)) → Fin (2*m) using Quot.lift
    -- First define on ordered pairs, showing symmetry.
    let colorPair : (Fin 1 ⊕ (Fin m × Fin 2)) → (Fin 1 ⊕ (Fin m × Fin 2)) → Fin (2 * m) :=
      fun a b =>
      match a, b with
      | Sum.inl 0, Sum.inl 0 => 0
      | Sum.inl 0, Sum.inr (i, b) => spokeColor i b
      | Sum.inr (i, b), Sum.inl 0 => spokeColor i b
      | Sum.inr (i, b), Sum.inr (j, c) =>
        if i = j ∧ b = 0 ∧ c = 1 then
          ⟨(2 * i.val + 2) % (2 * m), by exact Nat.mod_lt _ (by omega)⟩
        else if i = j ∧ b = 1 ∧ c = 0 then
          ⟨(2 * i.val + 2) % (2 * m), by exact Nat.mod_lt _ (by omega)⟩
        else 0
    -- colorPair is symmetric
    have fin1_zero : ∀ (x : Fin 1), x = 0 := fun x => Fin.eq_zero x
    have hsym : ∀ a b : Fin 1 ⊕ (Fin m × Fin 2), colorPair a b = colorPair b a := by
      intro a b
      rcases a with x | ⟨i, b0⟩ <;> rcases b with y | ⟨j, c0⟩
      · simp [colorPair, fin1_zero x, fin1_zero y]
      · simp [colorPair, fin1_zero x]
      · simp [colorPair, fin1_zero y]
      · simp only [colorPair]
        by_cases hij : i = j
        · subst hij; rcases fin_two_cases b0 with rfl | rfl <;> rcases fin_two_cases c0 with rfl | rfl <;> simp
        · have : ¬(j = i) := fun h => hij h.symm
          simp [hij, this]
    -- Lift colorPair to Sym2
    let colorOnSym2 : Sym2 (Fin 1 ⊕ (Fin m × Fin 2)) → Fin (2 * m) :=
      Quot.lift (fun p => colorPair p.1 p.2) (fun p q hpq => by
        simp at hpq
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact hsym _ _)
    -- Coloring of line graph
    let c : (CGraph.lineGraph G').V → Fin (2 * m) := fun e => colorOnSym2 e.1
    -- Show c is a proper coloring
    refine ⟨c, fun {e f} hef => ?_⟩
    simp [CGraph.toSimple] at hef
    rw [CGraph.lineGraph_adj] at hef
    simp [SimpleGraph.completeGraph] at *
    obtain ⟨hef_ne, ⟨v, hv_e, hv_f⟩⟩ := hef
    obtain ⟨ea, hea⟩ := e
    obtain ⟨eb, heb⟩ := f
    dsimp only [c, colorOnSym2] at *
    induction ea using Sym2.ind with
    | h a b =>
      simp [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at hea
      rcases a with a | ⟨i, b0⟩ <;> rcases b with b | ⟨j, c0⟩
      · -- inl-inl: impossible, complete 1 has no edges
        rw [CGraph.join_adj_inl_inl] at hea
        simp [CGraph.complete] at hea
        obtain rfl := Fin.eq_zero a; obtain rfl := Fin.eq_zero b; simp at hea
      · -- inl-inr: spoke
        obtain rfl := Fin.eq_zero a
        -- ea = s(inl 0, inr (j, c0)), a spoke, color = spokeColor j c0
        induction eb using Sym2.ind with
        | h a' b' =>
          simp [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at heb
          rcases a' with a'' | ⟨i', b''⟩ <;> rcases b' with b''' | ⟨j', c''⟩
          · -- eb inl-inl: impossible
            rw [CGraph.join_adj_inl_inl] at heb
            simp [CGraph.complete] at heb
            obtain rfl := Fin.eq_zero a''; obtain rfl := Fin.eq_zero b'''; simp at heb
          · -- eb inl-inr: spoke
            obtain rfl := Fin.eq_zero a''
            simp [colorPair, spokeColor] at *
            intro h
            apply hef_ne
            have hj : j = j' := by
              apply Fin.ext; omega
            subst hj; rcases fin_two_cases c0 with rfl | rfl <;> rcases fin_two_cases c'' with rfl | rfl <;> simp_all
          · -- eb inr-inl: spoke
            rw [CGraph.join_adj_inr_inl] at heb
            simp at heb
            obtain rfl := Fin.eq_zero b'''
            simp [colorPair, spokeColor] at *
            intro h
            apply hef_ne
            have hj : j = i' := by
              apply Fin.ext; omega
            subst hj; rcases fin_two_cases c0 with rfl | rfl <;> rcases fin_two_cases b'' with rfl | rfl <;> simp_all
          · -- eb inr-inr: rail
            rw [CGraph.join_adj_inr_inr] at heb
            rw [CGraph.cartesianProduct_adj] at heb
            simp [CGraph.empty_adj, CGraph.complete_adj] at heb
            simp [colorPair, spokeColor] at *
            obtain ⟨rfl, hbc_ne⟩ := heb
            -- hv_f : v = inr (i', b'') ∨ v = inr (i', c'')
            -- hv_e : v = inl 0 ∨ v = inr (j, c0)
            -- v can't be inl 0 ( eb has no inl endpoint), so v = inr (j, c0) = inr (i',某)
            -- Hence j = i'.
            have hj : j = i' := by
              -- v must be inr (j, c0) since eb has no inl
              have hv_eq : v = Sum.inr (j, c0) := by
                rcases hv_e with hv_e | hv_e
                · rcases hv_f with h | h <;> simp [hv_e] at h
                · exact hv_e
              rcases hv_f with h | h <;> simp [hv_eq] at h
              · exact (Prod.ext_iff.mp (Sum.inr_injective h)).1
              · exact (Prod.ext_iff.mp (Sum.inr_injective h)).1
            subst hj
            simp at *
            rcases fin_two_cases b'' with rfl | rfl <;> rcases fin_two_cases c'' with rfl | rfl <;> simp at hbc_ne ⊢ <;>
              all_goals (
                let jj := (j : Fin m).val
                have hjlt : jj < m := j.isLt
                unfold Lean.Internal.coeM at *
                intro h
                have hle : 2 * jj + 2 ≤ 2 * m := by omega
                rcases fin_two_cases c0 with rfl | rfl <;> simp at *
                · have key : (2 * jj + 2) % (2 * m) ≠ 2 * jj := by
                    by_cases hlt : 2 * jj + 2 < 2 * m
                    · rw [Nat.mod_eq_of_lt hlt]; omega
                    · have heq : 2 * jj + 2 = 2 * m := by omega
                      rw [heq, Nat.mod_self]; omega
                  exact key h.symm
                · have key : ((2 * (j : Fin m).val + 2) % (2 * m)) % 2 = 0 := by
                    rw [Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * m)]
                    simp
                  have h1 : (2 * (j : Fin m).val + 1) % 2 = 1 := by omega
                  omega)
      · -- inr-inl: spoke
        obtain rfl := Fin.eq_zero b
        induction eb using Sym2.ind with
        | h a' b' =>
          simp [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at heb
          rcases a' with a'' | ⟨i', b''⟩ <;> rcases b' with b''' | ⟨j', c''⟩
          · -- eb inl-inl: impossible
            rw [CGraph.join_adj_inl_inl] at heb
            simp [CGraph.complete] at heb
            obtain rfl := Fin.eq_zero a''; obtain rfl := Fin.eq_zero b'''; simp at heb
          · -- eb inl-inr: spoke, both spokes sharing inl 0
            obtain rfl := Fin.eq_zero a''
            simp [colorPair, spokeColor] at *
            intro h
            apply hef_ne
            have hij : i = j' := by
              apply Fin.ext; omega
            subst hij
            rcases fin_two_cases b0 with rfl | rfl <;> rcases fin_two_cases c'' with rfl | rfl <;> simp_all
          · -- eb inr-inl: spoke, same vertex must match
            rw [CGraph.join_adj_inr_inl] at heb
            simp at heb
            obtain rfl := Fin.eq_zero b'''
            simp [colorPair, spokeColor] at *
            intro h
            apply hef_ne
            have hij : i = i' := by
              apply Fin.ext; omega
            subst hij; rcases fin_two_cases b0 with rfl | rfl <;> rcases fin_two_cases b'' with rfl | rfl <;> simp_all
          · -- eb inr-inr: rail, spoke vs rail
            rw [CGraph.join_adj_inr_inr] at heb
            rw [CGraph.cartesianProduct_adj] at heb
            simp [CGraph.empty_adj, CGraph.complete_adj] at heb
            simp [colorPair, spokeColor] at *
            obtain ⟨rfl, hbc_ne⟩ := heb
            have hv_eq : v = Sum.inr (i, b0) := by
              rcases hv_e with hv_e | hv_e <;> rcases hv_f with hv_f | hv_f <;>
                simp [hv_e] at *
            have hij : i = i' := by
              rcases hv_f with h | h <;> simp [hv_eq] at h
              · exact (Prod.ext_iff.mp (Sum.inr_injective h)).1
              · exact (Prod.ext_iff.mp (Sum.inr_injective h)).1
            subst hij
            simp at *
            rcases fin_two_cases b'' with rfl | rfl <;> rcases fin_two_cases c'' with rfl | rfl <;> simp at hbc_ne ⊢ <;>
              all_goals (
                let jj := (i : Fin m).val
                have hjlt : jj < m := i.isLt
                unfold Lean.Internal.coeM at *
                intro h
                have hle : 2 * jj + 2 ≤ 2 * m := by omega
                rcases fin_two_cases b0 with rfl | rfl <;> simp at *
                · have key : (2 * jj + 2) % (2 * m) ≠ 2 * jj := by
                    by_cases hlt : 2 * jj + 2 < 2 * m
                    · rw [Nat.mod_eq_of_lt hlt]; omega
                    · have heq : 2 * jj + 2 = 2 * m := by omega
                      rw [heq, Nat.mod_self]; omega
                  exact key h.symm
                · have key : ((2 * (i : Fin m).val + 2) % (2 * m)) % 2 = 0 := by
                    rw [Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * m)]
                    simp
                  have h1 : (2 * (i : Fin m).val + 1) % 2 = 1 := by omega
                  omega)
      · -- inr-inr: rail
        rw [CGraph.join_adj_inr_inr] at hea
        rw [CGraph.cartesianProduct_adj] at hea
        simp [CGraph.empty_adj, CGraph.complete_adj] at hea
        simp [colorPair, spokeColor] at *
        obtain ⟨rfl, hbc_ne⟩ := hea
        -- Set jj before simp might eliminate i
        set jj := (i : Fin m).val
        have hjlt : jj < m := i.isLt
        induction eb using Sym2.ind with
        | h a' b' =>
          simp [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at heb
          rcases a' with a'' | ⟨i', b''⟩ <;> rcases b' with b''' | ⟨j', c''⟩
          · -- eb inl-inl: impossible
            rw [CGraph.join_adj_inl_inl] at heb
            simp [CGraph.complete] at heb
            obtain rfl := Fin.eq_zero a''; obtain rfl := Fin.eq_zero b'''; simp at heb
          · -- eb inl-inr: spoke, rail vs spoke
            obtain rfl := Fin.eq_zero a''
            simp at *
            have hv_eq : v = Sum.inr (j', c'') := by
              rcases hv_f with hv_f | hv_f
              · rcases hv_e with hv_e | hv_e <;> simp [hv_f] at *
              · exact hv_f
            have hij : j' = i := by
              rcases hv_e with hv_e | hv_e <;> simp [hv_eq] at hv_e
              · exact (Prod.ext_iff.mp (Sum.inr_injective hv_e)).1
              · exact (Prod.ext_iff.mp (Sum.inr_injective hv_e)).1
            subst hij
            simp at *
            unfold Lean.Internal.coeM at *
            intro h
            rcases fin_two_cases b0 with rfl | rfl <;> rcases fin_two_cases c0 with rfl | rfl <;> simp at hbc_ne ⊢ <;>
              all_goals (
                rcases fin_two_cases c'' with rfl | rfl <;> simp at *
                · have key : (2 * jj + 2) % (2 * m) ≠ 2 * jj := by
                    by_cases hlt : 2 * jj + 2 < 2 * m
                    · rw [Nat.mod_eq_of_lt hlt]; omega
                    · have heq : 2 * jj + 2 = 2 * m := by omega
                      rw [heq, Nat.mod_self]; omega
                  exact key h
                · have key : ((2 * jj + 2) % (2 * m)) % 2 = 0 := by
                    rw [Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * m)]
                    simp
                  have h1 : (2 * jj + 1) % 2 = 1 := by omega
                  omega)
          · -- eb inr-inl: spoke, rail vs spoke
            rw [CGraph.join_adj_inr_inl] at heb
            simp at heb
            obtain rfl := Fin.eq_zero b'''
            simp at *
            have hv_eq : v = Sum.inr (i', b'') := by
              rcases hv_f with hv_f | hv_f <;>
                rcases hv_e with hv_e | hv_e <;> simp [hv_f] at *
            have hij : i' = i := by
              rcases hv_e with hv_e | hv_e <;> simp [hv_eq] at hv_e
              · exact (Prod.ext_iff.mp (Sum.inr_injective hv_e)).1
              · exact (Prod.ext_iff.mp (Sum.inr_injective hv_e)).1
            subst hij
            simp at *
            unfold Lean.Internal.coeM at *
            intro h
            have hle : 2 * jj + 2 ≤ 2 * m := by omega
            rcases fin_two_cases b0 with rfl | rfl <;> rcases fin_two_cases c0 with rfl | rfl <;> simp at hbc_ne ⊢ <;>
              all_goals (
                rcases fin_two_cases b'' with rfl | rfl <;> simp at *
                · have key : (2 * jj + 2) % (2 * m) ≠ 2 * jj := by
                    by_cases hlt : 2 * jj + 2 < 2 * m
                    · rw [Nat.mod_eq_of_lt hlt]; omega
                    · have heq : 2 * jj + 2 = 2 * m := by omega
                      rw [heq, Nat.mod_self]; omega
                  exact key h
                · have key : ((2 * jj + 2) % (2 * m)) % 2 = 0 := by
                    rw [Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * m)]
                    simp
                  have h1 : (2 * jj + 1) % 2 = 1 := by omega
                  omega)
          · -- eb inr-inr: rail, rail vs rail
            rw [CGraph.join_adj_inr_inr] at heb
            rw [CGraph.cartesianProduct_adj] at heb
            simp [CGraph.empty_adj, CGraph.complete_adj] at heb
            simp at *
            obtain ⟨rfl, hb''_ne⟩ := heb
            have hij : i' = i := by
              rcases hv_e with hv_e | hv_e <;> rcases hv_f with hv_f | hv_f
              · exact ((Prod.ext_iff.mp (Sum.inr_injective (hv_e.symm.trans hv_f))).1).symm
              · exact ((Prod.ext_iff.mp (Sum.inr_injective (hv_e.symm.trans hv_f))).1).symm
              · exact (Prod.ext_iff.mp (Sum.inr_injective (hv_f.symm.trans hv_e))).1
              · exact (Prod.ext_iff.mp (Sum.inr_injective (hv_f.symm.trans hv_e))).1
            subst hij
            simp at *
            rcases fin_two_cases b0 with rfl | rfl <;> rcases fin_two_cases c0 with rfl | rfl <;> rcases fin_two_cases b'' with rfl | rfl <;> rcases fin_two_cases c'' with rfl | rfl <;> simp_all
  · -- Lower bound: 2*n+4 ≤ chromNum (lineGraph (friendship (n+2)))
    have h1 := maxDeg_le_edgeChromNum (friendship (n + 2))
    rw [edgeChromNum_eq] at h1
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
theorem matchNum_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) : (turan n r).matchNum = n / 2 := by
  apply le_antisymm
  · -- Upper bound
    have h1 := two_mul_matchNum_le_V (turan n r)
    rw [V_turan] at h1
    omega
  · -- Lower bound: construct a matching of size n/2
    -- Strategy: use matchNum_complete (n) = n/2 and turan n r ≤ complete n ... 
    -- No, matchNum is antitone for subgraphs, so that gives upper bound.
    -- Instead, construct explicit matching.
    -- turan n r = completeMultipartite L where L has r parts of sizes q or q+1.
    -- We can form a matching of size n/2 by pairing vertices in round-robin order.
    rw [matchNum_eq]
    set m := n % r with hm_def
    set q := n / r with hq_def
    set L : List ℕ := List.replicate m (q + 1) ++ List.replicate (r - m) q
    set H : CGraph := CGraph.completeMultipartite L
    have hturan : turan n r = ⟦H⟧ := by rfl
    rw [hturan, lineGraph_mk, indepNum_mk]
    have hLlen : L.length = r := by
      simp [L, List.length_append, List.length_replicate]
      have := Nat.mod_lt n (by linarith : 0 < r)
      omega
    have hLsum : L.sum = n := by
      simp [L, hm_def, hq_def]
      have hle : n % r < r := Nat.mod_lt n (by linarith)
      rw [hLlen] at *
      have hmod_div := Nat.div_add_mod n r
      have hle2 : n % r ≤ r := le_of_lt ‹_›
      have hgoal : n % r * (n / r + 1) + (r - n % r) * (n / r) = r * (n / r) + n % r := by
        have h1 : (r - n % r) * (n / r) = r * (n / r) - (n % r) * (n / r) := Nat.sub_mul _ _ _
        rw [h1, Nat.mul_add]
        have hmq_le_rq : n % r * (n / r) ≤ r * (n / r) := Nat.mul_le_mul_right _ hle2
        omega
      linarith
    -- Now prove lower bound: indepNum (lineGraph H) ≥ n/2
    -- f : Fin n → H.V by round-robin assignment
    have hpos_r : 0 < r := by linarith
    have hmod_lt : n % r < r := Nat.mod_lt n hpos_r
    -- For j : Fin n, the part index is ⟨j % L.length, ...⟩ = ⟨j % r, ...⟩ (using hLlen)
    -- and the vertex-in-part index is j / r, which is < L.get ⟨j % r, ...⟩
    -- because L.get ⟨j%r, _⟩ ≥ n/r = q, and j/r ≤ q, with j/r < q when L.get = q.
    -- L.get i = q+1 if i.val < m, else q.
    -- j < n = r*q + m. If j%r < m, part size q+1, j/r ≤ q < q+1 ✓.
    -- If j%r ≥ m, then j = r*(j/r) + (j%r) ≥ r*(j/r) + m, so r*(j/r) < r*q + m = n,
    --   and j%r ≥ m means r*(j/r) ≤ n - m = r*q, but j < n forces r*(j/r) < r*q, so j/r < q. ✓
    -- Helper: for i : Fin r, L.get ⟨i, ...⟩ = if i < m then q+1 else q
    have hLget : ∀ (i : Fin r),
        L.get ⟨i, by rw [hLlen]; exact i.2⟩ = if i.val < m then q + 1 else q := by
      intro ⟨i, hi⟩
      simp only [L]
      simp [List.getElem_append]
    -- f : Fin n → H.V by round-robin
    let f : Fin n → H.V := fun j =>
      ⟨⟨j.val % r, show j.val % r < L.length from hLlen.symm ▸ Nat.mod_lt _ hpos_r⟩, ⟨j.val / r, by
        have hj' : j.val < n := j.isLt
        rw [hLget ⟨j.val % r, Nat.mod_lt _ hpos_r⟩]
        split_ifs with h
        · rw [hq_def]
          clear hLget hLlen hLsum h
          have hj' : (j : ℕ) < n := j.isLt
          have hqm2 : n = r * (n / r) + n % r := by
            have := Nat.div_add_mod n r; linarith
          have h1 : (j : ℕ) < r * (n / r) + r := by omega
          have h2 : r * (n / r) + r = r * (n / r + 1) := by ring
          rw [h2] at h1
          exact Nat.div_lt_of_lt_mul h1
        · rw [hq_def]
          clear hLget hLlen hLsum
          have hj' : (j : ℕ) < n := j.isLt
          have hqm2 : n = r * (n / r) + n % r := by
            have := Nat.div_add_mod n r; linarith
          have hval_ge : n % r ≤ (j : ℕ) % r := not_lt.mp h
          clear h
          have hj_decomp := Nat.div_add_mod (j : ℕ) r
          have hj_mod_lt := Nat.mod_lt (j : ℕ) hpos_r
          have hqr_pos : 0 < n / r := Nat.div_pos (by omega) hpos_r
          have h_jdiv_lt : (j : ℕ) / r < n / r := by
            have := hj_decomp
            nlinarith
          have h1 : (j : ℕ) < r * (n / r) := by nlinarith
          exact Nat.div_lt_of_lt_mul h1⟩⟩
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
      clear f hfeq hLget hLlen hLsum hpos_r hmod_lt
      have heq : j1 = j2 := by
        rw [← hdecomp1, ← hdecomp2, hf1, hf2]
      exact Fin.ext heq
    have hf_adj : ∀ j1 j2 : Fin n, H.Adj (f j1) (f j2) ↔ (j1.val % r ≠ j2.val % r) := by
      intro j1 j2
      rw [CGraph.completeMultipartite_adj]
      simp [f]
    have hedge_exists : ∀ t : Fin (n / 2),
        H.Adj (f ⟨2 * t.val, by omega⟩) (f ⟨2 * t.val + 1, by omega⟩) := by
      intro t
      rw [hf_adj]
      intro h
      have h2 : (2 * (t : ℕ) + 1) % r = (2 * (t : ℕ)) % r := by exact_mod_cast h.symm
      set x := (2 * (t : ℕ)) % r
      have hx_lt : x < r := Nat.mod_lt _ hpos_r
      have h4 : x = (x + 1) % r := by
        have h1mod : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
        show x = ((2 * (t : ℕ)) % r + 1) % r
        rw [← h2]
        rw [Nat.add_mod, h1mod]
      by_cases hx1 : x + 1 < r
      · rw [Nat.mod_eq_of_lt hx1] at h4; omega
      · have : x + 1 = r := by omega
        rw [this, Nat.mod_self] at h4; omega
    -- Build independent set in lineGraph H: the n/2 edges (f(2t), f(2t+1))
    let edgeFn : Fin (n / 2) → (H.lineGraph).V := fun t =>
      ⟨Sym2.mk ((f ⟨2 * t.val, by omega⟩), (f ⟨2 * t.val + 1, by omega⟩)),
       (by simpa [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] using hedge_exists t)⟩
    have h_edge_inj : Function.Injective edgeFn := by
      intro t t' h_eq
      have := congr_arg Subtype.val h_eq
      simp at this
      rw [Sym2.eq_iff] at this
      rcases this with h | h
      · have := hf_inj h.1
        simp [Fin.ext_iff] at this
        exact Fin.ext (by omega)
      · exfalso
        have h1 := hf_inj h.1
        simp at h1
        omega
    let S := Finset.image edgeFn Finset.univ
    have hS_card : S.card = n / 2 := by
      rw [Finset.card_image_of_injective _ h_edge_inj, Finset.card_fin]
    have hS_ind : SimpleGraph.IsIndepSet H.lineGraph.toSimple (S : Set (H.lineGraph.V)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro e he f' hf' hef
      have he' : e ∈ S := by simpa using he
      have hfq' : f' ∈ S := by simpa using hf'
      obtain ⟨t, -, ht⟩ := Finset.mem_image.mp he'
      obtain ⟨t', -, ht'⟩ := Finset.mem_image.mp hfq'
      subst ht; subst ht'
      by_cases h : t = t'
      · exfalso; apply hef; simp [h]
      · simp only [CGraph.toSimple_adj, CGraph.lineGraph_adj, edgeFn]
        simp [hf_inj.eq_iff]
        intro hne hor
        exact ⟨⟨hne, by omega⟩, by omega, hne⟩
    exact hS_card.ge.trans (hS_ind.card_le_indepNum)

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
