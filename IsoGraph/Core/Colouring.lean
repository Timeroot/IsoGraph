import IsoGraph.Core.Symmetry

/-!
# Colourings, cliques, independent sets, covers and matchings

The invariants that count sets of vertices or edges — the chromatic number and index, the clique
and independence numbers, the clique cover, vertex cover, domination and matching numbers — for the
core constructions.  Greedy colouring, Nordhaus–Gaddum, Gallai's identities, König's theorem and
the small Ramsey numbers are here as well, since everything in this file leans on them.
-/

section
open Fintype

/-! ## Complementation, on isomorphism classes

Every other construction that takes a graph is carried across to `IsoGraph` in
`IsoGraph/Core/Quotient.lean`, by `@[toIsoGraph]` on its congruence.  The complement is the same
lift — `Quotient.map CGraph.compl`, with `compl_mk` true by `rfl` — but written out by hand, and
written out here, for two reasons:

* it carries the `Compl IsoGraph` instance, so that `Gᶜ` elaborates to `Compl.compl G` — which
  `simp` does not match against a bridge stated with `IsoGraph.compl`.  The bridge has to be
  stated in the notation the rest of the library uses, and the attribute has no way to know that;
* `johnsonTwoIso` and `paleyIso`, further down this file, are tagged `@[toIsoGraph]` where they
  stand, and the equations that generates are about complements.
-/

end

namespace CGraph

section
open Fintype

/-! ## Invariants of the constructions

What the invariants of `IsoGraph/Invariants/Basic.lean` come to on the graphs above.
-/

end

section
open Fintype
variable (G H : CGraph)

@[simp] theorem indepNum_empty (n : ℕ) : (empty n).indepNum = n := by
  rw [indepNum, empty_toSimple]
  simp [SimpleGraph.indepNum]
  let hIndep : ∀ (s : Finset (Fin n)), (⊥ : SimpleGraph (Fin n)).IsIndepSet s := by
    intro s u _ v _ huv hadj
    exact hadj
  have hset : {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} = Set.Iic n := by
    ext m
    rw [Set.mem_setOf_eq, Set.mem_Iic]
    change (∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) m s) ↔ m ≤ n
    constructor
    · rintro ⟨s, hs_indep, hs_card⟩
      exact hs_card ▸ (Finset.card_le_univ s).trans (by simp [Fintype.card_fin])
    · intro hm
      if h : m < n then
        exact ⟨Finset.image (fun i : Fin m => ⟨i, by omega⟩ : Fin m → Fin n) Finset.univ, hIndep _, by
          rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congr_arg Fin.val h)), Finset.card_fin]⟩
      else
        push_neg at h
        have heq : m = n := le_antisymm hm h
        subst heq
        exact ⟨Finset.univ, hIndep _, by simp [Fintype.card_fin]⟩
  have mem_0 : 0 ∈ {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} := by
    exact ⟨∅, hIndep ∅, by simp⟩
  have mem_n : n ∈ {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} := by
    exact ⟨Finset.univ, hIndep Finset.univ, by simp [Fintype.card_fin]⟩
  have bound : ∀ x, x ∈ {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} → x ≤ n := by
    intro x hx; rw [hset] at hx; exact hx
  have h_bdd : BddAbove {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} :=
    ⟨n, bound⟩
  change sSup {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} = n
  exact le_antisymm (csSup_le ⟨0, mem_0⟩ fun x hx => bound x hx)
    (le_csSup h_bdd mem_n)

@[simp] theorem cliqueNum_empty (n : ℕ) : (empty n).cliqueNum = min n 1 := by
  simp [cliqueNum, empty_toSimple]
  unfold SimpleGraph.cliqueNum
  apply le_antisymm
  · -- Every clique has size ≤ min n 1
    apply csSup_le'
    rintro k ⟨s, hs⟩
    have hk := hs.1
    have hpadj := hs.2
    have hkn : s.card ≤ n := by
      calc s.card ≤ FinEnum.card (empty n).V := FinEnum.card_le s
        _ = n := card_empty n
    have hk1 : s.card ≤ 1 := by
      rw [Finset.card_le_one]
      exact fun x hx y hy => Classical.not_not.1 fun hne => by
        have := hk hx hy hne
        simp at this
    omega
  · -- min n 1 ≤ sSup
    apply le_csSup
    · -- bounded above
      exact ⟨n, fun k ⟨s, hs⟩ => by
        have := hs.2
        rw [← this]
        calc s.card ≤ FinEnum.card (empty n).V := FinEnum.card_le s
          _ = n := card_empty n⟩
    · -- min n 1 is in the set
      rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · push_cast [min_eq_right (Nat.succ_le_of_lt hn)]
        exact ⟨{⟨0, hn⟩}, by simp⟩

@[simp] theorem indepNum_compl : Gᶜ.indepNum = G.cliqueNum := by
  simp [indepNum, cliqueNum, compl_toSimple, SimpleGraph.indepNum_compl]

@[simp] theorem cliqueNum_compl : Gᶜ.cliqueNum = G.indepNum := by
  rw [← indepNum_compl Gᶜ, compl_compl]

@[simp] theorem cliqueNum_complete (n : ℕ) : (complete n).cliqueNum = n := by
  simp [cliqueNum, complete_toSimple]
  rw [SimpleGraph.cliqueNum]
  have hmem : n ∈ {m | ∃ s : Finset (Fin n), (⊤ : SimpleGraph (Fin n)).IsNClique m s} := by
    refine ⟨Finset.univ, ?_⟩
    show SimpleGraph.IsNClique (⊤ : SimpleGraph (Fin n)) n Finset.univ
    letI : DecidableEq (Fin n) := inferInstance
    have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
    have hcl : (⊤ : SimpleGraph (Fin n)).IsClique (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
      simp [SimpleGraph.IsClique, Set.Pairwise]
    exact ⟨hcl, hc⟩
  have hle : ∀ m ∈ {m | ∃ s : Finset (Fin n), (⊤ : SimpleGraph (Fin n)).IsNClique m s}, m ≤ n := by
    rintro m ⟨s, hs⟩
    show m ≤ n
    obtain ⟨hcl, hcard⟩ := hs
    rw [← hcard]
    exact le_trans (Finset.card_le_univ s) (le_of_eq (Fintype.card_fin n))
  exact csSup_eq_of_forall_le_of_forall_lt_exists_gt (by exact ⟨n, hmem⟩) hle fun m hm => ⟨n, hmem, hm⟩

@[simp] theorem indepNum_complete (n : ℕ) : (complete n).indepNum = min n 1 := by
  simp [complete_toSimple, CGraph.indepNum]
  unfold SimpleGraph.indepNum
  -- ⊤ : SimpleGraph (Fin n), indepNum = sSup {k | ∃ s, ⊤.IsNIndepSet k s}
  -- Key: in ⊤, IsNIndepSet k s ↔ s.card = k ∧ s.card ≤ 1
  have h_adj_top : ∀ (x y : Fin n), (⊤ : SimpleGraph (Fin n)).Adj x y ↔ x ≠ y := by
    intro x y; simp [SimpleGraph.top_adj]
  have h_isIndep_top : ∀ (s : Finset (Fin n)), (⊤ : SimpleGraph (Fin n)).IsIndepSet s ↔ s.card ≤ 1 := by
    intro s
    constructor
    · -- IsIndepSet ⊤ s → s.card ≤ 1
      intro h
      by_contra hlt
      push_neg at hlt
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
      have hna := h hx hy hxy
      exact hna (h_adj_top x y |>.mpr hxy)
    · -- s.card ≤ 1 → IsIndepSet ⊤ s
      intro h x hx y hy hne
      exfalso
      have : ∀ z ∈ s, z = x := by
        intro z hz
        by_contra hne'
        have : s.card ≥ 2 := by
          have h1 : ({x, z} : Finset (Fin n)).card = 2 := by
            rw [Finset.card_pair (fun hzx => hne' hzx.symm)]
          exact h1 ▸ Finset.card_le_card (by exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hz))
        omega
      exact hne (this y hy).symm
  have h_indep : ∀ (s : Finset (Fin n)) (k : ℕ), SimpleGraph.IsNIndepSet (G := (⊤ : SimpleGraph (Fin n))) k s ↔ s.card = k ∧ s.card ≤ 1 := by
    intro s k
    constructor
    · intro h
      cases h with
      | mk hi hc => exact ⟨hc, h_isIndep_top s |>.mp hi⟩
    · intro ⟨hcard, hiset⟩
      exact SimpleGraph.IsNIndepSet.mk (h_isIndep_top s |>.mpr hiset) hcard
  -- sSup = min n 1
  apply le_antisymm
  · -- sSup ≤ min n 1
    apply csSup_le'
    rintro k ⟨s, hs⟩
    have hinfo := h_indep s k |>.mp hs
    have hk1 : k ≤ 1 := hinfo.1 ▸ hinfo.2
    have hkn : k ≤ n := hinfo.1 ▸ (show s.card ≤ n from FinEnum.card_le s)
    exact le_min hkn hk1
  · -- min n 1 ≤ sSup
    have hbdd : BddAbove {n_1 : ℕ | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊤ : SimpleGraph (Fin n))) n_1 s} := by
      exact ⟨n, fun k ⟨s, hs⟩ => by
        have := h_indep s k |>.mp hs
        have h1 := this.1
        have h2 : s.card ≤ n := FinEnum.card_le s
        rw [h1] at h2
        exact h2⟩
    -- Show min n 1 is in the set
    have hmem : min n 1 ∈ {n_1 : ℕ | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊤ : SimpleGraph (Fin n))) n_1 s} := by
      by_cases hn : n = 0
      · subst hn
        simp
        exact ⟨∅, SimpleGraph.IsNIndepSet.mk (by trivial) rfl⟩
      · -- n ≥ 1, so min n 1 = 1
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hmin : min n 1 = 1 := min_eq_right hn1
        rw [hmin]
        exact ⟨{⟨0, hn1⟩}, SimpleGraph.IsNIndepSet.mk (by simp [SimpleGraph.IsIndepSet]) (by simp)⟩
    exact le_csSup hbdd hmem

@[simp] theorem indepNum_cycle (n : ℕ) : (cycle (n + 3)).indepNum = (n + 3) / 2 := by
  unfold CGraph.indepNum SimpleGraph.indepNum
  set m := n + 3
  -- Adjacency in cycle m: toSimple.Adj i j ↔ i ≠ j ∧ ((i+1)%m == j ∨ (j+1)%m == i)
  have habj : ∀ (i j : Fin m), (cycle m).toSimple.Adj i j ↔ i ≠ j ∧ (((i.val + 1) % m == j.val) ∨ ((j.val + 1) % m == i.val)) := by
    intro i j
    simp [cycle, ofRel_adj, CGraph.toSimple_adj]
  -- The shift map i ↦ (i+1) % m is a bijection on Fin m
  let shift : Fin m → Fin m := fun i => ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩
  have hshift_eq : ∀ i : Fin m, shift i = i + 1 := by
    intro i; exact Fin.ext (by simp [shift, Fin.val_add])
  have hshift_bijective : Function.Bijective shift := by
    refine ⟨?_, ?_⟩
    · -- injective
      intro i j hij
      rw [hshift_eq] at hij
      exact add_right_cancel hij
    · -- surjective
      intro j
      refine ⟨j + ⟨m - 1, by omega⟩, ?_⟩
      rw [hshift_eq]
      have hlast : (⟨m - 1, by omega⟩ : Fin m) + 1 = 0 := by
        ext; simp [Fin.val_add]
        have : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        simp [this]
      rw [add_assoc, hlast, add_zero]
  have hshift_inj := hshift_bijective.1
  have hshift_surj := hshift_bijective.2
  -- For any i : Fin m, i ≠ shift i (since m ≥ 3)
  have hne_shift : ∀ i : Fin m, i ≠ shift i := by
    intro i hi
    have hshift_eq_i : shift i = i + 1 := hshift_eq i
    rw [hshift_eq_i] at hi
    have h1 : (i + 1 : Fin m) = i := hi.symm
    have h2 : (1 : Fin m) = 0 := by
      have := congr_arg (· + (-i : Fin m)) h1
      simp [add_assoc] at this
    exact absurd (Fin.ext_iff.mp h2) (by simp; omega)
  -- For any i : Fin m, Adj i (shift i)
  have hadj_shift : ∀ i : Fin m, (cycle m).toSimple.Adj i (shift i) := by
    intro i
    rw [habj]
    exact ⟨hne_shift i, Or.inl (by simp [shift])⟩
  -- For any independent set s, shift(s) is disjoint from s
  have hdisjoint : ∀ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) →
      Disjoint s (s.map ⟨shift, hshift_inj⟩) := by
    intro s hs
    rw [Finset.disjoint_left]
    intro z hz hzm
    obtain ⟨y, hy, hyz⟩ := Finset.mem_map.mp hzm
    have hyz' : shift y = z := hyz
    have hadyz : (cycle m).toSimple.Adj y z := by
      subst hyz'
      exact hadj_shift y
    have hyz_ne : y ≠ z := by
      intro heq; rw [heq.symm] at hyz'; exact hne_shift y hyz'.symm
    exact hs hy hz hyz_ne hadyz
  -- So |s| + |shift(s)| ≤ m, i.e., 2|s| ≤ m
  have hupper : ∀ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) →
      2 * s.card ≤ m := by
    intro s hs
    have hd := hdisjoint s hs
    have hcard_map : (s.map ⟨shift, hshift_inj⟩).card = s.card := by
      exact Finset.card_map (⟨shift, hshift_inj⟩ : Fin m ↪ Fin m)
    have hcard_union : (s ∪ s.map ⟨shift, hshift_inj⟩).card = 2 * s.card := by
      rw [Finset.card_union_of_disjoint hd, hcard_map, two_mul]
    exact hcard_union ▸ le_trans (Finset.card_le_univ _) (by simp)
  have hupper' : ∀ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) →
      s.card ≤ m / 2 := by
    intro s hindep
    rw [Nat.le_div_iff_mul_le zero_lt_two]
    linarith [hupper s hindep]
  -- Flower: there exists an independent set of size m/2
  have flower : ∃ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) ∧ s.card = m / 2 := by
    -- Use the set of odd-valued vertices
    let s := Finset.image (fun (a : Fin (m / 2)) => ⟨2 * a.val + 1, by omega⟩ : Fin (m / 2) → Fin m) Finset.univ
    refine ⟨s, ?_, ?_⟩
    · -- s is independent
      intro x hx y hy hxy hadj
      rw [Finset.mem_coe, Finset.mem_image] at hx
      rw [Finset.mem_coe, Finset.mem_image] at hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      rw [habj] at hadj
      obtain ⟨hne, hcase⟩ := hadj
      have ha_lt : a.val < m / 2 := a.isLt
      have hb_lt : b.val < m / 2 := b.isLt
      have h2a1_lt_m : 2 * a.val + 1 < m := by omega
      have h2b1_lt_m : 2 * b.val + 1 < m := by omega
      -- Fin.val of our constructed elements
      have hval_a : ((⟨2 * a.val + 1, by omega⟩ : Fin m).val) = 2 * a.val + 1 := by
        simp
      have hval_b : ((⟨2 * b.val + 1, by omega⟩ : Fin m).val) = 2 * b.val + 1 := by
        simp
      -- (v+1) as Fin m: (2*k+1)+1 = 2*k+2. Two cases: 2*k+2 < m or 2*k+2 = m.
      -- In either case ((v+1).val) is even.
      have h2a2_le_m : 2 * a.val + 2 ≤ m := by omega
      have h2b2_le_m : 2 * b.val + 2 ≤ m := by omega
      -- (v1+1).val = (2*a+2) % m, which is even
      have hv1p1_val : ((⟨2 * a.val + 1, by omega⟩ : Fin m) + 1).val = (2 * a.val + 2) % m := by
        simp [Fin.val_add]
      have hv2p1_val : ((⟨2 * b.val + 1, by omega⟩ : Fin m) + 1).val = (2 * b.val + 2) % m := by
        simp [Fin.val_add]
      -- (2*k+2) % m is even since 2*k+2 ≤ m
      have heven_mod : ∀ k : ℕ, 2 * k + 2 ≤ m → ((2 * k + 2) % m) % 2 = 0 := by
        intro k hk
        by_cases hlt : 2 * k + 2 < m
        · rw [Nat.mod_eq_of_lt hlt]
          omega
        · have heq : 2 * k + 2 = m := by omega
          rw [heq, Nat.mod_self]
      have heven_v1 : ((⟨2 * a.val + 1, by omega⟩ : Fin m) + 1).val % 2 = 0 := by rw [hv1p1_val]; exact heven_mod a h2a2_le_m
      have heven_v2 : ((⟨2 * b.val + 1, by omega⟩ : Fin m) + 1).val % 2 = 0 := by rw [hv2p1_val]; exact heven_mod b h2b2_le_m
      -- adjacency requires even == odd, impossible
      rcases hcase with h | h
      · simp at h
        have h1 := heven_mod a h2a2_le_m
        rw [h] at h1
        omega
      · simp at h
        have h1 := heven_mod b h2b2_le_m
        rw [h] at h1
        omega
    · -- s has size m/2
      rw [Finset.card_image_of_injective _ (fun i j hij => by
        have := Fin.ext_iff.mp hij
        simp at this
        omega), Finset.card_fin]
  -- Now combine to get sSup = m/2
  have hindep_empty : (cycle m).toSimple.IsIndepSet (∅ : Set (Fin m)) := by
    simp [SimpleGraph.IsIndepSet]
  have hmem : m / 2 ∈ {n | ∃ s : Finset (Fin m), (cycle m).toSimple.IsNIndepSet n s} := by
    obtain ⟨s, hind, hcard⟩ := flower
    exact ⟨s, SimpleGraph.IsNIndepSet.mk hind hcard⟩
  have hbdd : BddAbove {n | ∃ s : Finset (Fin m), (cycle m).toSimple.IsNIndepSet n s} := by
    exact ⟨m, fun k ⟨s, hs⟩ => by
      rcases hs with ⟨hs_indep, hs_card⟩
      rw [hs_card.symm]
      show s.card ≤ m
      exact le_trans (FinEnum.card_le s) (card_cycle m |> le_of_eq)⟩
  have hnonempty : ({n | ∃ s : Finset (Fin m), (cycle m).toSimple.IsNIndepSet n s}).Nonempty := by
    exact ⟨0, (∅ : Finset (Fin m)), SimpleGraph.IsNIndepSet.mk (by simp [SimpleGraph.IsIndepSet]) rfl⟩
  apply le_antisymm
  · apply csSup_le hnonempty
    intro b hb
    obtain ⟨s, hs⟩ := hb
    rcases hs with ⟨hs_indep, hs_card⟩
    rw [← hs_card]
    exact hupper' s hs_indep
  · apply le_csSup hbdd hmem

@[simp] theorem indepNum_disjUnion : (G ⊕g H).indepNum = G.indepNum + H.indepNum := by
  simp only [CGraph.indepNum]
  -- The LHS graph is isomorphic to G.toSimple.sum H.toSimple
  have heq : (G.disjUnion H).toSimple = G.toSimple.sum H.toSimple := by
    ext x y
    simp [SimpleGraph.sum_adj, CGraph.toSimple_adj]
    cases x <;> cases y <;> simp [disjUnion_adj_inl_inl, disjUnion_adj_inr_inr, disjUnion_adj_inl_inr, disjUnion_adj_inr_inl]
  rw [heq]
  unfold SimpleGraph.indepNum
  set G' := G.toSimple
  set H' := H.toSimple
  classical
  set SG := {n : ℕ | ∃ s : Finset G.V, G'.IsNIndepSet n s} with SG_def
  set SH := {n : ℕ | ∃ s : Finset H.V, H'.IsNIndepSet n s} with SH_def
  set SL := {n : ℕ | ∃ s : Finset (G.V ⊕ H.V), (G' ⊕g H').IsNIndepSet n s} with SL_def
  --SG, SH bounded above
  have hSG_bdd : BddAbove SG := ⟨FinEnum.card G.V, fun n ⟨s, hs⟩ => hs.card_eq ▸ FinEnum.card_le s⟩
  have hSH_bdd : BddAbove SH := ⟨FinEnum.card H.V, fun n ⟨s, hs⟩ => hs.card_eq ▸ FinEnum.card_le s⟩
  have hSL_bdd : BddAbove SL := ⟨FinEnum.card G.V + FinEnum.card H.V, fun n ⟨s, hs⟩ => by
    rw [← hs.card_eq]
    exact s.card_le_univ.trans (by simp [Fintype.card_sum])⟩
  -- Step: SG + SH ⊆ SL (construct indep set in sum from indep sets in each side)
  have h_add_mem : ∀ a ∈ SG, ∀ b ∈ SH, a + b ∈ SL := by
    rintro a ha b hb
    obtain ⟨sG, hsG⟩ := ha
    obtain ⟨sH, hsH⟩ := hb
    let embL : G.V ↪ G.V ⊕ H.V := ⟨Sum.inl, Sum.inl_injective⟩
    let embR : H.V ↪ G.V ⊕ H.V := ⟨Sum.inr, Sum.inr_injective⟩
    have hdisjoint : Disjoint (Finset.map embL sG) (Finset.map embR sH) := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      simp [Finset.mem_map] at hxL hxR
      obtain ⟨a, ha, rfl⟩ := hxL
      obtain ⟨b, hb, hb'⟩ := hxR
      cases hb'
    have hasmp : (Finset.map embL sG ⊔ Finset.map embR sH) = Finset.map embL sG ∪ Finset.map embR sH := rfl
    have hc : (Finset.map embL sG ⊔ Finset.map embR sH).card = a + b := by
      rw [hasmp, Finset.card_union_of_disjoint hdisjoint]
      simp [Finset.card_map, embL, embR, hsG.card_eq, hsH.card_eq]
    refine ⟨sG.map embL ⊔ sH.map embR, ?_, hc⟩
    show (G' ⊕g H').IsIndepSet (↑(sG.map embL ⊔ sH.map embR))
    unfold SimpleGraph.IsIndepSet
    simp
    intro v hv w hw hvw
    simp only [Set.mem_union, Set.mem_image] at hv hw
    rcases hv with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;> rcases hw with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;>
      simp at hvw ⊢
    · intro hadj; exact hsG.1 hx hy hvw (by simpa using hadj)
    · intro hadj; exact hsH.1 hx hy hvw (by simpa using hadj)
  -- 0 ∈ SG and 0 ∈ SH (empty independent set)
  have h0_SG : 0 ∈ SG := ⟨∅, by simp [SimpleGraph.IsNIndepSet.mk, SimpleGraph.IsIndepSet]⟩
  have h0_SH : 0 ∈ SH := ⟨∅, by simp [SimpleGraph.IsNIndepSet.mk, SimpleGraph.IsIndepSet]⟩
  -- Every element of SL is ≤ sSup SG + sSup SH
  have h_le_each : ∀ n ∈ SL, n ≤ sSup SG + sSup SH := by
    intro n hn
    obtain ⟨s, hs⟩ := hn
    -- Define sL and sR as finsets of vertices in G.V and H.V whose inl/inr is in s
    let sL := Finset.filter (fun a => (Sum.inl a : G.V ⊕ H.V) ∈ s) Finset.univ
    let sR := Finset.filter (fun b => (Sum.inr b : G.V ⊕ H.V) ∈ s) Finset.univ
    -- sL is indep in G', sR is indep in H'
    have hsL_ind : G'.IsIndepSet (sL : Set G.V) := by
      unfold SimpleGraph.IsIndepSet
      intro a ha c hc hac
      simp [sL] at ha hc
      have hsum_adj : ¬(G' ⊕g H').Adj (Sum.inl a) (Sum.inl c) := by
        have := hs.1 ha hc (Sum.inl_injective.ne hac)
        simpa [SimpleGraph.sum_adj] using this
      simpa [SimpleGraph.sum_adj] using hsum_adj
    have hsR_ind : H'.IsIndepSet (sR : Set H.V) := by
      unfold SimpleGraph.IsIndepSet
      intro b hb d hd hbd
      simp [sR] at hb hd
      have hsum_adj : ¬(G' ⊕g H').Adj (Sum.inr b) (Sum.inr d) := by
        have := hs.1 hb hd (Sum.inr_injective.ne hbd)
        simpa [SimpleGraph.sum_adj] using this
      simpa [SimpleGraph.sum_adj] using hsum_adj
    -- card s = card sL + card sR
    have hcard : s.card = sL.card + sR.card := by
      let embL : G.V ↪ G.V ⊕ H.V := ⟨Sum.inl, Sum.inl_injective⟩
      let embR : H.V ↪ G.V ⊕ H.V := ⟨Sum.inr, Sum.inr_injective⟩
      have hsum_eq : s = sL.map embL ∪ sR.map embR := by
        ext v
        simp [sL, sR, embL, embR, Finset.mem_map, Finset.mem_union, Finset.mem_filter, Finset.mem_univ]
        cases v <;> simp
      have hdisjoint : Disjoint (sL.map embL) (sR.map embR) := by
        rw [Finset.disjoint_left]
        intro x hxL hxR
        simp [embL, embR, Finset.mem_map] at hxL hxR
        obtain ⟨a, ha, rfl⟩ := hxL
        obtain ⟨b, hb, hb'⟩ := hxR
        cases hb'
      rw [hsum_eq, Finset.card_union_of_disjoint hdisjoint,
          Finset.card_map embL,
          Finset.card_map embR]
    -- sL.card ≤ sSup SG, sR.card ≤ sSup SH
    have hcard_L : sL.card ≤ sSup SG := by
      apply le_csSup hSG_bdd
      exact ⟨sL, ⟨hsL_ind, rfl⟩⟩
    have hcard_R : sR.card ≤ sSup SH := by
      apply le_csSup hSH_bdd
      exact ⟨sR, ⟨hsR_ind, rfl⟩⟩
    rw [← hs.card_eq, hcard]
    exact add_le_add hcard_L hcard_R
  -- RHS ≤ LHS: sSup SG + sSup SH ≤ sSup SL
  have h_sum_subset : {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} ⊆ SL := by
    rintro n ⟨a, ha, b, hb, rfl⟩; exact h_add_mem a ha b hb
  have h_nonempty_sum : (∃ n, n ∈ {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n}) := ⟨0 + 0, 0, h0_SG, 0, h0_SH, rfl⟩
  have h_bdd_sum : BddAbove {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} := by
    exact ⟨sSup SG + sSup SH, fun n ⟨a, ha, b, hb, hn⟩ => hn ▸ add_le_add (le_csSup hSG_bdd ha) (le_csSup hSH_bdd hb)⟩
  have h_sSup_sum_le : sSup {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} ≤ sSup SL :=
    csSup_le h_nonempty_sum (fun n hn => le_csSup hSL_bdd (h_sum_subset hn))
  have h_sSup_mem (S : Set ℕ) (hSne : S.Nonempty) (hSbb : BddAbove S) : sSup S ∈ S := by
    have hfin : S.Finite := Set.Finite.subset (Set.finite_Iic hSbb.choose) (fun x hx => hSbb.choose_spec hx)
    have hmem_aux : hfin.toFinset.max' (hSne.imp (fun x hx => hfin.mem_toFinset.mpr hx)) ∈ S := by
      have := Finset.max'_mem (hfin.toFinset) (hSne.imp (fun x hx => hfin.mem_toFinset.mpr hx))
      exact hfin.mem_toFinset.mp this
    have hsSup_eq_max' : sSup S = hfin.toFinset.max' (hSne.imp (fun x hx => hfin.mem_toFinset.mpr hx)) := by
      apply le_antisymm
      · exact csSup_le hSne (fun x hx => Finset.le_max' _ _ (hfin.mem_toFinset.mpr hx))
      · apply le_csSup hSbb hmem_aux
    rw [hsSup_eq_max']
    exact hmem_aux
  have h_sSup_add : sSup SG + sSup SH ≤ sSup {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} := by
    exact le_csSup h_bdd_sum ⟨sSup SG, h_sSup_mem SG ⟨0, h0_SG⟩ hSG_bdd, sSup SH, h_sSup_mem SH ⟨0, h0_SH⟩ hSH_bdd, rfl⟩
  have h_rtl : sSup SG + sSup SH ≤ sSup SL := le_trans h_sSup_add h_sSup_sum_le
  -- LHS ≤ RHS: sSup SL ≤ sSup SG + sSup SH
  have h_ltr : sSup SL ≤ sSup SG + sSup SH := by
    apply csSup_le'
    intro n hn
    exact h_le_each n hn
  exact le_antisymm h_ltr h_rtl

@[simp] theorem cliqueNum_disjUnion :
    (G ⊕g H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  simp only [CGraph.cliqueNum]
  letI := Classical.decEq G.V
  letI := Classical.decEq H.V
  let SG := G.toSimple
  let SH := H.toSimple
  let SD := (G.disjUnion H).toSimple
  show SD.cliqueNum = max SG.cliqueNum SH.cliqueNum
  unfold SimpleGraph.cliqueNum
  -- Define the sets of achievable clique sizes
  set SC := {n : ℕ | ∃ s : Finset (G.V ⊕ H.V), SD.IsNClique n s}
  set SSG := {n : ℕ | ∃ s : Finset G.V, SG.IsNClique n s}
  set SSH := {n : ℕ | ∃ s : Finset H.V, SH.IsNClique n s}
  -- Helper: Fintype.card of G.V ⊕ H.V bounds all clique sizes in SD
  have hbound : ∀ n ∈ SC, n ≤ Fintype.card (G.V ⊕ H.V) := by
    rintro n ⟨s, hs⟩
    have hcard := hs.card_eq
    rw [← hcard]
    exact s.card_le_univ
  -- SC is bounded above
  have hSC_bdd : BddAbove SC := ⟨Fintype.card (G.V ⊕ H.V), hbound⟩
  -- Lower bounds: embedding cliques from G and H into disjUnion
  have hSSG : ∀ n ∈ SSG, n ≤ sSup SC := by
    rintro n ⟨s, hs⟩
    apply le_csSup hSC_bdd
    use s.map (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ G.V ⊕ H.V)
    constructor
    · -- IsClique / pairwise adj
      intro a ha b hb hab
      simp [Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have hxy : x ≠ y := fun heq => hab (by rw [heq])
      show SD.Adj (Sum.inl x) (Sum.inl y)
      simp only [SD, CGraph.toSimple]
      rw [disjUnion_adj_inl_inl]
      rcases hs with ⟨hadj, hcard⟩
      exact hadj hx hy hxy
    · -- card
      rw [Finset.card_map]; exact hs.card_eq
  have hSSH : ∀ n ∈ SSH, n ≤ sSup SC := by
    rintro n ⟨s, hs⟩
    apply le_csSup hSC_bdd
    use s.map (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ G.V ⊕ H.V)
    constructor
    · -- IsClique / pairwise adj
      intro a ha b hb hab
      simp [Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have hxy : x ≠ y := fun heq => hab (by rw [heq])
      show SD.Adj (Sum.inr x) (Sum.inr y)
      simp only [SD, CGraph.toSimple]
      rw [disjUnion_adj_inr_inr]
      rcases hs with ⟨hadj, hcard⟩
      exact hadj hx hy hxy
    · rw [Finset.card_map]
      exact hs.card_eq
  -- SSG is bounded above
  have hSSG_bdd : BddAbove SSG := ⟨FinEnum.card G.V, fun n ⟨s, hs⟩ => by
    rw [← hs.card_eq]; exact FinEnum.card_le s⟩
  -- SSH is bounded above
  have hSSH_bdd : BddAbove SSH := ⟨FinEnum.card H.V, fun n ⟨s, hs⟩ => by
    rw [← hs.card_eq]; exact FinEnum.card_le s⟩
  -- Lower bound from G: SG.cliqueNum ≤ SD.cliqueNum
  have hle_G : sSup SSG ≤ sSup SC := by
    apply csSup_le _ hSSG
    exact ⟨0, ∅, by simp⟩
  -- Lower bound from H
  have hle_H : sSup SSH ≤ sSup SC := by
    apply csSup_le _ hSSH
    exact ⟨0, ∅, by simp⟩
  -- Lower bound: max ≤ SD
  have hlower : max (sSup SSG) (sSup SSH) ≤ sSup SC := max_le hle_G hle_H
  -- Upper bound: SD ≤ max
  -- Key: every SD-clique comes from G or H
  -- If s is a clique in SD containing an inl vertex, then all vertices of s are inl.
  have hclique_inl : ∀ (s : Finset (G.V ⊕ H.V)) (n : ℕ) (x₀ : G.V),
      Sum.inl x₀ ∈ s → SD.IsNClique n s →
      ∃ t : Finset G.V, SG.IsNClique n t ∧ s = t.map (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ G.V ⊕ H.V) := by
    intro s n x₀ hinx₀ hnc
    have hall_inl : ∀ y ∈ s, ∃ a : G.V, y = Sum.inl a := by
      intro y hy
      cases y with
      | inl a => exact ⟨a, rfl⟩
      | inr b =>
        exfalso
        rcases hnc with ⟨hclique, _⟩
        have hineq : (Sum.inl x₀ : G.V ⊕ H.V) ≠ Sum.inr b := by intro h; cases h
        have hadj : SD.Adj (Sum.inl x₀) (Sum.inr b) := hclique hinx₀ hy hineq
        simp [SD, CGraph.toSimple, disjUnion_adj_inl_inr] at hadj
    let decoder : G.V ⊕ H.V → G.V := Sum.elim id (fun _ => x₀)
    have hinl_decoder : ∀ y ∈ s, Sum.inl (decoder y) = y := by
      intro y hy; obtain ⟨a, rfl⟩ := hall_inl y hy; simp [decoder]
    let t := s.image decoder
    have ht_card : t.card = s.card := by
      rw [Finset.card_image_of_injOn]
      intro y hy z hz h_eq
      have hy' := hinl_decoder y hy
      have hz' := hinl_decoder z hz
      exact hy'.symm.trans (congr_arg Sum.inl h_eq ▸ hz')
    have hs_card : s.card = n := hnc.card_eq
    refine ⟨t, ?_, ?_⟩
    · have ht_n : t.card = n := ht_card.symm ▸ hs_card
      exact ⟨fun a ha b hb hab => by
        rw [Finset.mem_coe, Finset.mem_image] at ha hb
        obtain ⟨y, hy, rfl⟩ := ha
        obtain ⟨z, hz, rfl⟩ := hb
        show SG.Adj (decoder y) (decoder z)
        rcases hnc with ⟨hclique, _⟩
        have hadj := hclique hy hz (by intro heq; apply hab; rw [heq])
        show SG.Adj (decoder y) (decoder z)
        rw [CGraph.toSimple_adj]
        show G.Adj (decoder y) (decoder z) = true
        rw [← disjUnion_adj_inl_inl G H (decoder y) (decoder z)]
        rw [hinl_decoder y hy, hinl_decoder z hz]
        rw [CGraph.toSimple_adj] at hadj
        exact hadj, ht_n⟩
    · show s = t.map (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ G.V ⊕ H.V)
      ext y
      simp [Finset.mem_map]
      exact ⟨fun hy => ⟨decoder y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hinl_decoder y hy⟩,
             fun ⟨a, ha, hxy⟩ => by
               obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
               have heq : Sum.inl a = z := Eq.trans (congr_arg Sum.inl hza.symm) (hinl_decoder z hz)
               exact hxy.symm ▸ heq ▸ hz⟩
  -- Similarly for inr.
  have hclique_inr : ∀ (s : Finset (G.V ⊕ H.V)) (x₀ : H.V),
      Sum.inr x₀ ∈ s → SD.IsNClique s.card s →
      ∃ t : Finset H.V, SH.IsNClique t.card t ∧ s = t.map (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ G.V ⊕ H.V) := by
    intro s x₀ hinx₀ hnc
    have hall_inr : ∀ y ∈ s, ∃ b : H.V, y = Sum.inr b := by
      intro y hy
      cases y with
      | inl a =>
        exfalso
        rcases hnc with ⟨hclique, _⟩
        have hineq : (Sum.inr x₀ : G.V ⊕ H.V) ≠ Sum.inl a := by intro h; cases h
        have hadj : SD.Adj (Sum.inr x₀) (Sum.inl a) := hclique hinx₀ hy hineq
        simp [SD, CGraph.toSimple, disjUnion_adj_inr_inl] at hadj
      | inr b => exact ⟨b, rfl⟩
    let encoder : G.V ⊕ H.V → H.V := Sum.elim (fun _ => x₀) id
    have hinr_encoder : ∀ y ∈ s, Sum.inr (encoder y) = y := by
      intro y hy; obtain ⟨b, rfl⟩ := hall_inr y hy; simp [encoder]
    let t := s.image encoder
    have ht_card : t.card = s.card := by
      rw [Finset.card_image_of_injOn]
      intro y hy z hz h_eq
      have hy' := hinr_encoder y hy
      have hz' := hinr_encoder z hz
      exact hy'.symm.trans (congr_arg Sum.inr h_eq ▸ hz')
    refine ⟨t, ?_, ?_⟩
    · exact ⟨fun a ha b hb hab => by
        rw [Finset.mem_coe, Finset.mem_image] at ha hb
        obtain ⟨y, hy, rfl⟩ := ha
        obtain ⟨z, hz, rfl⟩ := hb
        show SH.Adj (encoder y) (encoder z)
        rcases hnc with ⟨hclique, _⟩
        have hadj := hclique hy hz (by intro heq; apply hab; exact (congr_arg encoder heq))
        show SH.Adj (encoder y) (encoder z)
        rw [CGraph.toSimple_adj]
        show H.Adj (encoder y) (encoder z) = true
        rw [← disjUnion_adj_inr_inr G H (encoder y) (encoder z)]
        rw [hinr_encoder y hy, hinr_encoder z hz]
        rw [CGraph.toSimple_adj] at hadj
        exact hadj, rfl⟩
    · show s = t.map (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ G.V ⊕ H.V)
      ext y
      simp [Finset.mem_map]
      exact ⟨fun hy => ⟨encoder y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hinr_encoder y hy⟩,
             fun ⟨a, ha, hxy⟩ => by
               obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
               have heq : Sum.inr a = z := Eq.trans (congr_arg Sum.inr hza.symm) (hinr_encoder z hz)
               exact hxy.symm ▸ heq ▸ hz⟩
  have hmem : ∀ n ∈ SC, n ∈ SSG ∨ n ∈ SSH := by
    rintro n ⟨s, hs⟩
    by_cases hempty : s = ∅
    · subst hempty
      have hn0 : n = 0 := hs.card_eq.symm
      subst hn0
      left; exact ⟨∅, by simp⟩
    · obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hempty
      cases v with
      | inl x =>
        left
        obtain ⟨t, ht1, ht2⟩ := hclique_inl s n x hv hs
        exact ⟨t, ht1⟩
      | inr x =>
        right
        have hs_card_eq : s.card = n := hs.card_eq
        have hs' : SD.IsNClique s.card s := ⟨by rcases hs with ⟨hc, _⟩; exact hc, rfl⟩
        obtain ⟨t, ht1, ht2⟩ := hclique_inr s x hv hs'
        have : t.card = n := by
          have := congr_arg Finset.card ht2
          simp [Finset.card_map] at this
          exact this.symm ▸ hs_card_eq
        exact ⟨t, this ▸ ht1⟩
  have hupper : sSup SC ≤ max (sSup SSG) (sSup SSH) := by
    apply csSup_le
    · exact ⟨0, ⟨∅, by simp⟩⟩
    · intro n hn
      rcases hmem n hn with h | h
      · exact le_max_of_le_left (le_csSup hSSG_bdd h)
      · exact le_max_of_le_right (le_csSup hSSH_bdd h)
  exact le_antisymm hupper hlower

@[simp] theorem cliqueNum_join :
    (G ∇g H).cliqueNum = G.cliqueNum + H.cliqueNum := by
  simp only [join, cliqueNum_compl, indepNum_disjUnion, indepNum_compl]

@[simp] theorem indepNum_join :
    (G ∇g H).indepNum = max G.indepNum H.indepNum := by
  -- The goal: (join G H).toSimple.indepNum = max G.toSimple.indepNum H.toSimple.indepNum
  -- Join has all cross edges, so indep sets don't span both sides.
  -- I'll prove it by showing both ≤ and ≥.
  rw [join, indepNum_compl]
  -- Helper: cliqueNum monotone under embedding
  have cliqueNum_le_of_emb {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      {G : SimpleGraph X} {H : SimpleGraph Y} (f : G ↪g H) : G.cliqueNum ≤ H.cliqueNum := by
    unfold SimpleGraph.cliqueNum
    apply csSup_le_csSup
    · exact ⟨Fintype.card Y, fun n ⟨t, ht⟩ => ht.card_eq ▸ Finset.card_le_univ t⟩
    · exact ⟨0, ⟨∅, by simp [SimpleGraph.isNClique_empty]⟩⟩
    · rintro n ⟨s, hs⟩
      have hcard : (s.map f.toEmbedding).card = n := by simp [hs.card_eq]
      have hclique : H.IsClique ((fun a => f a) '' ↑s) := by
        intro a ha b hb hab
        simp at ha hb hab
        obtain ⟨xa, hxa, rfl⟩ := ha
        obtain ⟨xb, hxb, rfl⟩ := hb
        have hne : xa ≠ xb := by
          intro heq; exact hab (by rw [heq])
        exact f.map_rel_iff.mpr (hs.isClique hxa hxb hne)
      have heq : ((fun a => f a) '' (s : Set X)) = ↑(s.map f.toEmbedding) := by
        ext y; simp
      rw [heq] at hclique
      exact ⟨_, SimpleGraph.IsNClique.mk hclique hcard⟩
  -- Embed Gᶜ and Hᶜ into disjUnion Gᶜ Hᶜ
  have hge_left : cliqueNum Gᶜ ≤ cliqueNum (Gᶜ ⊕g Hᶜ) := by
    apply cliqueNum_le_of_emb
    exact { toFun := Sum.inl, inj' := Sum.inl_injective,
            map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion] }
  have hge_right : cliqueNum Hᶜ ≤ cliqueNum (Gᶜ ⊕g Hᶜ) := by
    apply cliqueNum_le_of_emb
    exact { toFun := Sum.inr, inj' := Sum.inr_injective,
            map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion] }
  have hge : max (cliqueNum Gᶜ) (cliqueNum Hᶜ) ≤ cliqueNum (Gᶜ ⊕g Hᶜ) := max_le hge_left hge_right
  -- Cross pairs are not adjacent in disjUnion
  have hno_cross : ∀ (a : Gᶜ.V) (b : Hᶜ.V),
      ¬(Gᶜ ⊕g Hᶜ).toSimple.Adj (Sum.inl a) (Sum.inr b) := by
    simp [CGraph.toSimple, disjUnion]
  -- Any clique in disjUnion is in one side
  have clique_one_side : ∀ (C : Finset (Gᶜ.V ⊕ Hᶜ.V))
      (hC : (Gᶜ ⊕g Hᶜ).toSimple.IsNClique C.card C),
      (∀ x ∈ C, x.isLeft = true) ∨ (∀ x ∈ C, x.isRight = true) := by
    intro C hC
    by_contra h
    push_neg at h
    obtain ⟨hx, hy⟩ := h
    obtain ⟨px, hpx, hx'⟩ := hx
    obtain ⟨py, hpy, hy'⟩ := hy
    obtain ⟨b, rfl⟩ : ∃ b, px = Sum.inr b := by
      match px with
      | Sum.inl a => simp at hx'
      | Sum.inr b => exact ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, py = Sum.inl c := by
      match py with
      | Sum.inl c => exact ⟨c, rfl⟩
      | Sum.inr d => simp at hy'
    exact hno_cross c b (hC.isClique hpx hpy (by intro h; cases h))
  have hle : cliqueNum (Gᶜ ⊕g Hᶜ) ≤ max (cliqueNum Gᶜ) (cliqueNum Hᶜ) := by
    let embL : Gᶜ.toSimple ↪g (Gᶜ ⊕g Hᶜ).toSimple :=
      { toFun := Sum.inl, inj' := Sum.inl_injective,
        map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion] }
    let embR : Hᶜ.toSimple ↪g (Gᶜ ⊕g Hᶜ).toSimple :=
      { toFun := Sum.inr, inj' := Sum.inr_injective,
        map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion] }
    simp only [CGraph.cliqueNum, SimpleGraph.cliqueNum]
    apply csSup_le
    · exact ⟨0, ⟨∅, by simp [SimpleGraph.isNClique_empty]⟩⟩
    · intro n hn
      obtain ⟨C, hC⟩ := hn
      have hside : (∀ x ∈ C, ∃ a : Gᶜ.V, x = Sum.inl a) ∨ (∀ x ∈ C, ∃ b : Hᶜ.V, x = Sum.inr b) := by
        by_contra h
        push_neg at h
        obtain ⟨hx, hy⟩ := h
        obtain ⟨px, hpx, hx'⟩ := hx
        obtain ⟨py, hpy, hy'⟩ := hy
        obtain ⟨b, rfl⟩ : ∃ b, px = Sum.inr b := by
          match px with
          | Sum.inl a => exfalso; exact hx' a rfl
          | Sum.inr b => exact ⟨b, rfl⟩
        obtain ⟨c, rfl⟩ : ∃ c, py = Sum.inl c := by
          match py with
          | Sum.inl c => exact ⟨c, rfl⟩
          | Sum.inr d => exfalso; exact hy' d rfl
        exact hno_cross c b (hC.isClique hpx hpy (by intro h; cases h))
      rcases hside with hleft | hright
      · -- All inl: Dav = {a | inl a ∈ C} is an n-clique in Gᶜ
        let Dav : Finset Gᶜ.V := Finset.univ.filter (fun a => Sum.inl a ∈ C)
        have hinl_mem : ∀ x ∈ C, ∃ a, x = Sum.inl a := hleft
        have hDav_eq : Dav.map ⟨Sum.inl, Sum.inl_injective⟩ = C := by
          ext x; simp [Dav, Finset.mem_map]
          refine ⟨fun ⟨a, ha, hx⟩ => hx ▸ ha, fun hx => ?_⟩
          obtain ⟨a, ha'⟩ := hinl_mem x hx
          have ha_Dav : a ∈ Dav := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha'.symm ▸ hx⟩
          exact ⟨a, ha'.symm ▸ hx, ha'.symm⟩
        have hdav_card : Dav.card = n := by
          have h1 := congr_arg Finset.card hDav_eq
          simp [Finset.card_map] at h1
          exact h1.trans hC.card_eq
        have hdav_clique : Gᶜ.toSimple.IsClique (Dav : Set Gᶜ.V) := by
          intro a1 ha1 a2 ha2 ha12
          have ha1C : Sum.inl a1 ∈ C := Finset.mem_filter.mp (Finset.mem_coe.mp ha1) |>.2
          have ha2C : Sum.inl a2 ∈ C := Finset.mem_filter.mp (Finset.mem_coe.mp ha2) |>.2
          have hadj' : (Gᶜ ⊕g Hᶜ).toSimple.Adj (Sum.inl a1) (Sum.inl a2) :=
            hC.isClique (by exact ha1C) (by exact ha2C) (by intro h; exact ha12 (embL.injective h))
          exact embL.map_adj_iff.mp hadj'
        have hbddG : BddAbove {m | ∃ s : Finset Gᶜ.V, Gᶜ.toSimple.IsNClique m s} :=
          ⟨Fintype.card Gᶜ.V, fun m ⟨s, hs⟩ => hs.card_eq ▸ Finset.card_le_univ s⟩
        have hnG : n ∈ {m | ∃ s : Finset Gᶜ.V, Gᶜ.toSimple.IsNClique m s} :=
          ⟨Dav, SimpleGraph.IsNClique.mk hdav_clique hdav_card⟩
        exact le_max_of_le_left (le_csSup hbddG hnG)
      · let Dav : Finset Hᶜ.V := Finset.univ.filter (fun b => Sum.inr b ∈ C)
        have hinr_mem : ∀ x ∈ C, ∃ b, x = Sum.inr b := hright
        have hDav_eq : Dav.map ⟨Sum.inr, Sum.inr_injective⟩ = C := by
          ext x; simp [Dav, Finset.mem_map]
          refine ⟨fun ⟨b, hb, hx⟩ => hx ▸ hb, fun hx => ?_⟩
          obtain ⟨b, hb'⟩ := hinr_mem x hx
          have hb_Dav : b ∈ Dav := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb'.symm ▸ hx⟩
          exact ⟨b, hb'.symm ▸ hx, hb'.symm⟩
        have hdav_card : Dav.card = n := by
          have h1 := congr_arg Finset.card hDav_eq
          simp [Finset.card_map] at h1
          exact h1.trans hC.card_eq
        have hdav_clique : Hᶜ.toSimple.IsClique (Dav : Set Hᶜ.V) := by
          intro b1 hb1 b2 hb2 hb12
          have h1 : Sum.inr b1 ∈ C := Finset.mem_filter.mp (Finset.mem_coe.mp hb1) |>.2
          have h2 : Sum.inr b2 ∈ C := Finset.mem_filter.mp (Finset.mem_coe.mp hb2) |>.2
          have hadj' : (Gᶜ ⊕g Hᶜ).toSimple.Adj (Sum.inr b1) (Sum.inr b2) :=
            hC.isClique h1 h2 (by intro h; exact hb12 (embR.injective h))
          exact embR.map_adj_iff.mp hadj'
        have hbddH : BddAbove {m | ∃ s : Finset Hᶜ.V, Hᶜ.toSimple.IsNClique m s} :=
          ⟨Fintype.card Hᶜ.V, fun m ⟨s, hs⟩ => hs.card_eq ▸ Finset.card_le_univ s⟩
        have hnH : n ∈ {m | ∃ s : Finset Hᶜ.V, Hᶜ.toSimple.IsNClique m s} :=
          ⟨Dav, SimpleGraph.IsNClique.mk hdav_clique hdav_card⟩
        exact le_max_of_le_right (le_csSup hbddH hnH)
  have hle' : (Gᶜ.disjUnion Hᶜ).cliqueNum ≤ max G.indepNum H.indepNum := by
    rw [cliqueNum_compl, cliqueNum_compl] at hle; exact hle
  have hge' : max G.indepNum H.indepNum ≤ (Gᶜ.disjUnion Hᶜ).cliqueNum := by
    rw [cliqueNum_compl, cliqueNum_compl] at hge; exact hge
  exact le_antisymm hle' hge'

@[simp] theorem indepNum_lexProduct :
    (G ·g H).indepNum = G.indepNum * H.indepNum := by
  simp only [CGraph.indepNum]
  unfold SimpleGraph.indepNum
  have hlex : ∀ (p q : G.V × H.V),
      (G ·g H).toSimple.Adj p q ↔
        (G.toSimple.Adj p.1 q.1 ∧ p.1 ≠ q.1) ∨ (p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2 ∧ p.2 ≠ q.2) := by
    intro p q
    obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
    simp only [CGraph.toSimple_adj, lexProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
    constructor
    · rintro (h | ⟨hac, hbd⟩)
      · exact Or.inl ⟨h, fun hac => G.loopless c (hac ▸ h)⟩
      · exact Or.inr ⟨hac, hbd, fun hbd' => H.loopless d (hbd' ▸ hbd)⟩
    · rintro (⟨h, -⟩ | ⟨hac, hbd, -⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hac, hbd⟩
  -- Key lemma: independence number of lex product
  -- α(G[H]) = α(G) * α(H)
  -- We prove by showing both ≤ and ≥ directions for sSup
  unfold SimpleGraph.indepNum at *
  -- Let's obtain witnesses for αG and αH
  -- indepNum is sSup of {n | ∃ s, IsNIndepSet n s}
  -- We need:
  -- (1) ∀ S indep in lexProduct, #S ≤ αG * αH  (so sSup ≤ αG * αH)
  -- (2) ∃ S indep in lexProduct with #S = αG * αH (so αG * αH ≤ sSup)
  -- All sets of indep-set sizes are nonempty and bounded above
  set SG := {n : ℕ | ∃ s : Finset G.V, G.toSimple.IsNIndepSet n s}
  set SH := {n : ℕ | ∃ s : Finset H.V, H.toSimple.IsNIndepSet n s}
  set SGH := {n : ℕ | ∃ s : Finset (G.V × H.V), (G ·g H).toSimple.IsNIndepSet n s}
  have hSG_ne : SG.Nonempty := ⟨0, ⟨∅, by intro x; simp, rfl⟩⟩
  have hSH_ne : SH.Nonempty := ⟨0, ⟨∅, by intro x; simp, rfl⟩⟩
  have hSGH_ne : SGH.Nonempty := ⟨0, ⟨∅, by intro x; simp, rfl⟩⟩
  have hSG_bdd : BddAbove SG := ⟨FinEnum.card G.V, fun n ⟨s, hs⟩ ↦ hs.card_eq.symm ▸ FinEnum.card_le s⟩
  have hSH_bdd : BddAbove SH := ⟨FinEnum.card H.V, fun n ⟨s, hs⟩ ↦ hs.card_eq.symm ▸ FinEnum.card_le s⟩
  have hSGH_bdd : BddAbove SGH :=
    ⟨FinEnum.card G.V * FinEnum.card H.V, fun n ⟨s, hs⟩ ↦
      hs.card_eq.symm ▸ le_trans s.card_le_univ (by simp [Fintype.card_prod])⟩
  -- Key: indepNum is attained. Use that {n | ...} is a set of naturals that is nonempty and
  -- bounded above, and for ℕ, sSup is attained when the set is "compact" (finite). 
  -- We use `Nat.exists_max_image` on the finite type `Finset G.V`.
  -- indepNum G = sSup {n | ∃ s, IsNIndepSet n s} = max {|s| : s is indep in G}
  -- So there exists an indep set of size indepNum G.
  -- SG is finite (image of a subset of Finset G.V under card)
  have hSG_finite : SG.Finite := by
    exact Set.Finite.subset (Set.toFinite (Finset.image (fun s : Finset G.V => s.card) (Finset.univ : Finset (Finset G.V))))
      (fun n hn => by rcases hn with ⟨s, hs⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.card_eq⟩))
  have hSH_finite : SH.Finite := by
    exact Set.Finite.subset (Set.toFinite (Finset.image (fun s : Finset H.V => s.card) (Finset.univ : Finset (Finset H.V))))
      (fun n hn => by rcases hn with ⟨s, hs⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.card_eq⟩))
  have hSGH_finite : SGH.Finite := by
    exact Set.Finite.subset (Set.toFinite (Finset.image (fun s : Finset (G.V × H.V) => s.card) (Finset.univ : Finset (Finset (G.V × H.V)))))
      (fun n hn => by rcases hn with ⟨s, hs⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.card_eq⟩))
  -- For finite nonempty sets of ℕ, sSup is attained
  have attained_G : ∃ s : Finset G.V, G.toSimple.IsIndepSet (s : Set G.V) ∧ s.card = G.toSimple.indepNum := by
    have hmem : G.toSimple.indepNum ∈ SG := by
      exact Nat.sSup_mem hSG_ne hSG_bdd
    rcases hmem with ⟨s, hs⟩
    exact ⟨s, hs.isIndepSet, hs.card_eq⟩
  have attained_H : ∃ s : Finset H.V, H.toSimple.IsIndepSet (s : Set H.V) ∧ s.card = H.toSimple.indepNum := by
    have hmem : H.toSimple.indepNum ∈ SH := by
      exact Nat.sSup_mem hSH_ne hSH_bdd
    rcases hmem with ⟨s, hs⟩
    exact ⟨s, hs.isIndepSet, hs.card_eq⟩
  -- Lower bound: product of max indep sets is indep in lexProduct
  obtain ⟨sG, hsG_ind, hsG_card⟩ := attained_G
  obtain ⟨sH, hsH_ind, hsH_card⟩ := attained_H
  let sGH := sG ×ˢ sH
  have hprod_indep : (G ·g H).toSimple.IsIndepSet (sGH : Set (G.V × H.V)) := by
    intro p hp q hq hadj
    change p ∈ (sG ×ˢ sH : Finset (G.V × H.V)) at hp
    change q ∈ (sG ×ˢ sH : Finset (G.V × H.V)) at hq
    rw [Finset.mem_product] at hp hq
    rcases hp with ⟨hap, hbp⟩; rcases hq with ⟨haq, hbq⟩
    rw [hlex]
    intro h
    rcases h with ⟨hadj1, hne1⟩ | ⟨heq, hadj2, hne2⟩
    · exact absurd hadj1 (hsG_ind hap haq hne1)
    · exact absurd hadj2 (hsH_ind hbp hbq hne2)
  have hprod_card : sGH.card = G.toSimple.indepNum * H.toSimple.indepNum := by
    rw [Finset.card_product, hsG_card, hsH_card]
  have hmem_GH : G.toSimple.indepNum * H.toSimple.indepNum ∈ SGH :=
    ⟨sGH, hprod_indep, hprod_card⟩
  -- sSup ≤ ... : upper bound
  have hupper : ∀ n ∈ SGH, n ≤ G.toSimple.indepNum * H.toSimple.indepNum := by
    intro n ⟨s, hs_ind, hs_card⟩
    rw [← hs_card]
    -- projG is indep in G
    let projG := s.image Prod.fst
    have hprojG_ind : G.toSimple.IsIndepSet (projG : Set G.V) := by
      intro a ha a' ha' hadj haa'
      rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
      rcases Finset.mem_image.mp ha' with ⟨q, hq, rfl⟩
      have hpq : p ≠ q := by intro heq; exact hadj (congr_arg Prod.fst heq)
      exfalso; apply hs_ind hp hq hpq; exact (hlex p q).mpr (Or.inl ⟨haa', hadj⟩)
    --projG.card ≤ indepNum G
    have hproj_card_le : projG.card ≤ G.toSimple.indepNum := by
      apply le_csSup hSG_bdd
      exact ⟨projG, ⟨hprojG_ind, rfl⟩⟩
    -- Each fiber has size ≤ indepNum H
    let fiber (a : G.V) : Finset (G.V × H.V) := s.filter (fun x => x.1 = a)
    have hfiber_card : ∀ a, (fiber a).card ≤ H.toSimple.indepNum := by
      intro a
      -- fiber a is in bijection with a subset of H.V that's indep
      let fibersnd : Finset H.V := (fiber a).image Prod.snd
      have hfib_ind : H.toSimple.IsIndepSet (fibersnd : Set H.V) := by
        intro b hb b' hb' hab hadj
        rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
        rcases Finset.mem_image.mp hb' with ⟨q, hq, rfl⟩
        simp [fiber, Finset.mem_filter] at hp hq
        have hpq : p ≠ q := by intro heq; exact hab (Prod.ext_iff.mp heq |>.2)
        exact absurd ((hlex p q).mpr (Or.inr ⟨hp.2.trans hq.2.symm, hadj, hab⟩)) (hs_ind hp.1 hq.1 hpq)
      have hfib_card : (fiber a).card = fibersnd.card := by
        rw [Finset.card_image_of_injOn (f := Prod.snd) (fun p hp q hq h => by
          simp [fiber] at hp hq
          exact Prod.ext (hp.2.trans hq.2.symm) h)]
      have hfib_le : fibersnd.card ≤ H.toSimple.indepNum := by
        apply le_csSup hSH_bdd; exact ⟨fibersnd, hfib_ind, rfl⟩
      exact hfib_card.symm ▸ hfib_le
    have hcard_fiberwise : s.card = ∑ a ∈ projG, (fiber a).card := by
      have h_union : s = projG.biUnion fiber := by
        ext ⟨x1, x2⟩
        simp [projG, fiber]
        exact fun h => ⟨x2, h⟩
      rw [h_union, Finset.card_biUnion]
      intro a ha b hb hab
      exact Finset.disjoint_left.mpr (fun x hx hx' => hab (by simp [fiber] at hx hx'; exact hx.2.symm.trans hx'.2))
    calc s.card = ∑ a ∈ projG, (fiber a).card := hcard_fiberwise
      _ ≤ ∑ _ ∈ projG, H.toSimple.indepNum := Finset.sum_le_sum fun a ha => hfiber_card a
      _ = projG.card * H.toSimple.indepNum := by simp
      _ ≤ G.toSimple.indepNum * H.toSimple.indepNum := Nat.mul_le_mul_right _ hproj_card_le
  have hlower : G.toSimple.indepNum * H.toSimple.indepNum ≤ sSup SGH := by
    apply le_csSup hSGH_bdd hmem_GH
  exact le_antisymm (csSup_le hSGH_ne hupper) hlower

@[simp] theorem cliqueNum_strongProduct :
    (G ⊠g H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  unfold CGraph.cliqueNum
  -- cliqueNum G = G.toSimple.cliqueNum = sSup {n | ∃ s, G.toSimple.IsNClique n s}
  set sG := G.toSimple
  set sH := H.toSimple
  set sGH := (G.strongProduct H).toSimple
  -- The adjacency in sGH: for p q : G.V × H.V,
  -- sGH.Adj p q ↔ p ≠ q ∧ ((p.1 = q.1 ∨ sG.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ sH.Adj p.2 q.2))
  have hasAdj : ∀ p q : G.V × H.V,
    sGH.Adj p q ↔ p ≠ q ∧ ((p.1 = q.1 ∨ sG.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ sH.Adj p.2 q.2)) := by
    intro p q
    simp [sGH, strongProduct_adj, CGraph.toSimple]
    simp [sG, sH]
  -- cliqueNum unfolds to sSup of clique sizes
  -- We prove both directions.
  -- Get witnesses of max cliques in G and H
  have h0G : ∃ s : Finset G.V, sG.IsNClique 0 s := ⟨∅, by simp⟩
  have h0H : ∃ s : Finset H.V, sH.IsNClique 0 s := ⟨∅, by simp⟩
  have hωG_nonempty : {n | ∃ s : Finset G.V, sG.IsNClique n s}.Nonempty := ⟨0, h0G⟩
  have hωG_bdd : BddAbove {n | ∃ s : Finset G.V, sG.IsNClique n s} := by
    exact ⟨FinEnum.card G.V, fun n ⟨s, hs⟩ ↦ by rw [← hs.2]; exact FinEnum.card_le s⟩
  have hωH_nonempty : {n | ∃ s : Finset H.V, sH.IsNClique n s}.Nonempty := ⟨0, h0H⟩
  have hωH_bdd : BddAbove {n | ∃ s : Finset H.V, sH.IsNClique n s} := by
    exact ⟨FinEnum.card H.V, fun n ⟨s, hs⟩ ↦ by rw [← hs.2]; exact FinEnum.card_le s⟩
  -- cliqueNum = sSup of clique sizes (already unfolded)
  -- Helper: clique sizes are ≤ cliqueNum
  have card_le_cliqueNum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) : n ≤ G.cliqueNum := by
    rw [SimpleGraph.cliqueNum]
    exact le_csSup
      ⟨Fintype.card V, fun m ⟨t, ht⟩ ↦ ht.2 ▸ Finset.card_le_univ t⟩
      ⟨s, hs⟩
  -- Upper bound on clique size in strong product
  have upper : ∀ u : Finset (G.V × H.V), sGH.IsNClique u.card u → u.card ≤ sG.cliqueNum * sH.cliqueNum := by
    intro u hu
    -- Let πG be the image of u under first projection
    let projG := Finset.image (fun p : G.V × H.V => p.1) u
    -- For each g, fiber size
    let fiber := fun g => Finset.filter (fun p => p.1 = g) u
    -- Project to H for a fixed g
    let projHfiber := fun g => Finset.image (fun p : G.V × H.V => p.2) (fiber g)
    -- Step 1: projG is a clique in sG
    have projG_clique : sG.IsClique projG := by
      intro g1 hg1 g2 hg2 hne
      obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hg1
      obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp hg2
      have hne2 : p1 ≠ p2 := by intro h; exact hne (by simp [h])
      have hadj := hu.1 hp1 hp2 hne2
      rw [hasAdj] at hadj
      exact hadj.2.1.resolve_left (fun h => hne (h ▸ rfl))
    -- Step 2: Each fiber's image in H is a clique
    have fiber_clique : ∀ g ∈ projG, sH.IsClique (projHfiber g) := by
      intro g hg h1 hh1 h2 hh2 hne
      obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hh1
      obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp hh2
      have hne2 : p1 ≠ p2 := fun h => hne (by simp [h])
      have hp1uv : p1 ∈ u ∧ p1.1 = g := by simpa [fiber] using hp1
      have hp2uv : p2 ∈ u ∧ p2.1 = g := by simpa [fiber] using hp2
      have hadj := hu.1 hp1uv.1 hp2uv.1 hne2
      rw [hasAdj] at hadj
      have hp1p2 : p1.1 = p2.1 := hp1uv.2 ▸ hp2uv.2.symm
      rw [hp1p2] at hadj
      exact hadj.2.2.resolve_left hne
    -- Step 3: Each fiber has size ≤ sH.cliqueNum
    have fiber_size_bound : ∀ g ∈ projG, (fiber g).card ≤ sH.cliqueNum := by
      intro g hg
      have hclique_H := fiber_clique g hg
      have hcard_eq : (fiber g).card = (projHfiber g).card := by
        dsimp only [projHfiber, fiber]
        exact (Finset.card_image_of_injOn (fun p1 hp1 p2 hp2 h => by
          have h1 : p1.1 = g := (Finset.mem_filter.mp hp1).2
          have h2 : p2.1 = g := (Finset.mem_filter.mp hp2).2
          exact Prod.ext (h1 ▸ h2.symm) h)).symm
      rw [hcard_eq]
      exact card_le_cliqueNum sH ⟨hclique_H, rfl⟩
    -- Step 4: u.card ≤ projG.card * sH.cliqueNum
    have u_card_bound : u.card ≤ projG.card * sH.cliqueNum := by
      have hsum : u.card = ∑ g ∈ projG, (fiber g).card := by
        have h_decomp : ∀ p, p ∈ u ↔ ∃ g ∈ projG, p ∈ fiber g := by
          intro p
          constructor
          · intro hp
            exact ⟨p.1, Finset.mem_image_of_mem _ hp, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
          · rintro ⟨g, hg, hp⟩
            exact (Finset.mem_filter.mp hp).1
        have h_union : u = projG.biUnion fiber := by ext p; simp [h_decomp, Finset.mem_biUnion]
        rw [h_union]
        apply Finset.card_biUnion
        intro g hg g' hg' hne
        show Disjoint (fiber g) (fiber g')
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact hne ((Finset.mem_filter.mp hp1).2 ▸ (Finset.mem_filter.mp hp2).2)
      exact hsum ▸ Finset.sum_le_card_nsmul _ _ _ fiber_size_bound
    -- Step 5: projG.card ≤ sG.cliqueNum
    have projG_card_bound : projG.card ≤ sG.cliqueNum := by
      exact card_le_cliqueNum sG ⟨projG_clique, rfl⟩
    exact le_trans u_card_bound (Nat.mul_le_mul_right _ projG_card_bound)
  -- So cliqueNumGH ≤ cliqueNumG * cliqueNumH
  have upper_sSup : sGH.cliqueNum ≤ sG.cliqueNum * sH.cliqueNum := by
    rw [SimpleGraph.cliqueNum]
    have hωGH_nonempty : {n | ∃ s : Finset (G.V × H.V), sGH.IsNClique n s}.Nonempty := ⟨0, ⟨∅, by simp⟩⟩
    apply csSup_le hωGH_nonempty
    rintro n ⟨s, hs⟩
    obtain ⟨hclique, hcard⟩ := hs
    have hncard : sGH.IsNClique s.card s := ⟨hclique, rfl⟩
    have := upper s hncard
    exact hcard ▸ this
  -- Lower bound: ωG * ωH ≤ ωGH
  -- Build sizes_G and sizes_H finsets of clique sizes
  let cliques_G := Finset.univ.powerset.filter (fun (s : Finset G.V) => sG.IsClique s)
  let sizes_G := cliques_G.image (fun s => s.card)
  have hsizes_G_ne : sizes_G.Nonempty := ⟨0, Finset.mem_image.mpr ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [SimpleGraph.IsClique]⟩, rfl⟩⟩
  let cliques_H := Finset.univ.powerset.filter (fun (s : Finset H.V) => sH.IsClique s)
  let sizes_H := cliques_H.image (fun s => s.card)
  have hsizes_H_ne : sizes_H.Nonempty := ⟨0, Finset.mem_image.mpr ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [SimpleGraph.IsClique]⟩, rfl⟩⟩
  -- cliqueNum = sup' of the sizes finset
  have hset_eq_G : {n | ∃ s : Finset G.V, sG.IsNClique n s} = (sizes_G : Set ℕ) := by
    ext n
    simp [sizes_G, cliques_G]
    exact ⟨fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩, fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩⟩
  have hset_eq_H : {n | ∃ s : Finset H.V, sH.IsNClique n s} = (sizes_H : Set ℕ) := by
    ext n
    simp [sizes_H, cliques_H]
    exact ⟨fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩, fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩⟩
  have hcliqueNum_eq_G : sG.cliqueNum = sizes_G.max' hsizes_G_ne := by
    rw [SimpleGraph.cliqueNum, hset_eq_G]
    have hωG_ne' : ((sizes_G : Set ℕ)).Nonempty := by rw [← hset_eq_G]; exact hωG_nonempty
    have hωG_bd' : BddAbove (sizes_G : Set ℕ) := by rw [← hset_eq_G]; exact hωG_bdd
    have hmem : (sizes_G.max' hsizes_G_ne : ℕ) ∈ (sizes_G : Set ℕ) := Finset.max'_mem sizes_G hsizes_G_ne
    exact le_antisymm
      (csSup_le hωG_ne' (fun n hn => Finset.le_max' _ _ hn))
      (le_csSup hωG_bd' hmem)
  have hcliqueNum_eq_H : sH.cliqueNum = sizes_H.max' hsizes_H_ne := by
    rw [SimpleGraph.cliqueNum, hset_eq_H]
    have hωH_ne' : ((sizes_H : Set ℕ)).Nonempty := by rw [← hset_eq_H]; exact hωH_nonempty
    have hωH_bd' : BddAbove (sizes_H : Set ℕ) := by rw [← hset_eq_H]; exact hωH_bdd
    have hmem : (sizes_H.max' hsizes_H_ne : ℕ) ∈ (sizes_H : Set ℕ) := Finset.max'_mem sizes_H hsizes_H_ne
    exact le_antisymm
      (csSup_le hωH_ne' (fun n hn => Finset.le_max' _ _ hn))
      (le_csSup hωH_bd' hmem)
  -- Get attained max cliques in G and H
  have hsGmax_mem : sizes_G.max' hsizes_G_ne ∈ sizes_G := Finset.max'_mem sizes_G hsizes_G_ne
  have hsHmax_mem : sizes_H.max' hsizes_H_ne ∈ sizes_H := Finset.max'_mem sizes_H hsizes_H_ne
  obtain ⟨sGmax, hsGmax_mem', hsGmax_card⟩ := Finset.mem_image.mp hsGmax_mem
  obtain ⟨sHmax, hsHmax_mem', hsHmax_card⟩ := Finset.mem_image.mp hsHmax_mem
  have hsGmax_clique : sG.IsClique sGmax := (Finset.mem_filter.mp hsGmax_mem').2
  have hsHmax_clique : sH.IsClique sHmax := (Finset.mem_filter.mp hsHmax_mem').2
  -- sGmax is a clique in G, sHmax is a clique in H
  -- Their product is a clique in sGH
  let u := sGmax.product sHmax
  have hu_clique_carrier : sGH.IsClique (↑(sGmax.product sHmax) : Set (G.V × H.V)) := by
    intro p hp q hq hpq
    simp at hp hq
    obtain ⟨hpG, hpH⟩ := hp
    obtain ⟨hqG, hqH⟩ := hq
    rw [hasAdj]
    refine ⟨hpq, ?_, ?_⟩
    · by_cases h1 : p.1 = q.1
      · exact Or.inl h1
      · exact Or.inr (hsGmax_clique hpG hqG h1)
    · by_cases h2 : p.2 = q.2
      · exact Or.inl h2
      · exact Or.inr (hsHmax_clique hpH hqH h2)
  have hu_clique : sGH.IsNClique (sGmax.card * sHmax.card) (sGmax.product sHmax) := by
    exact ⟨hu_clique_carrier, Finset.card_product sGmax sHmax⟩
  have hu_clique' : sGH.IsNClique (sizes_G.max' hsizes_G_ne * sizes_H.max' hsizes_H_ne) (sGmax.product sHmax) := by
    rwa [hsGmax_card, hsHmax_card] at hu_clique
  have hlower : sG.cliqueNum * sH.cliqueNum ≤ sGH.cliqueNum := by
    rw [hcliqueNum_eq_G, hcliqueNum_eq_H]
    exact card_le_cliqueNum sGH hu_clique'
  exact le_antisymm upper_sSup hlower

end

section
open Fintype

/-! ## Strongly regular families

`isSRGWith_compl` above already turns one strongly regular graph into another.  Here are three
infinite families proved from scratch, via `isSRGWith_of`: the square rook's graphs, the Kneser
graphs on pairs (`kneser 5 2` is the Petersen graph) and — as the complement of the latter — the
triangular graphs.  `IsoGraph/SmallGraphs/Defs/SRG.lean` reads the concrete entries of its table off
these. -/

end

section
open Fintype
variable {m n : ℕ}

/-! ### Paley graphs

`paley q` is a Cayley graph on `ZMod q` with the nonzero squares as connection set, so the whole
question is a character sum.  Write `χ = quadraticChar F` for the quadratic character of a finite
field `F` with `q ≡ 1 mod 4` elements; then `χ (-1) = 1`, so `χ (y - x) = 1` is a symmetric
relation and

* `#{u | χ u = 1} = (q - 1) / 2`, from `∑ u, χ u = 0`;
* `#{u | χ u = 1 ∧ χ (u - a) = 1} = (q - 3 - 2 * χ a) / 4` for `a ≠ 0`, from the same plus
  `∑ u, χ (u * (u - a)) = -1`.

Translating by `x` turns those two counts into the degree and the common-neighbour count, which
is exactly `isSRGWith_of`.  The last step, `paleyIso`, identifies `paley q` — which is written on
`Fin q` and reads its adjacency out of `qrTable` — with the field version over `ZMod q`. -/

end

section
open Fintype

/-! ## Transitivity of the constructions

`CGraph.IsVertexTransitive` and `CGraph.IsArcTransitive` are decidable, but only by enumerating
the `n!` permutations of the vertex type, which is hopeless past a handful of vertices.  The
lemmas here settle whole families at once by exhibiting the automorphisms directly.

Everything factors through `ofRel`: an automorphism of `ofRel V r` is a permutation of `V`
preserving the *symmetrised* relation `r x y || r y x`, which is a weaker — and so easier to
supply — obligation than preserving `r` itself.  That weakening is what lets the reflections of a
cycle count as automorphisms even though they reverse the successor relation. -/

end

section
open Fintype
variable (G : CGraph)

/-! ### Line graphs

Vertices of `lineGraph G` are edges of `G`, so an automorphism of `G` acts on them, and an
automorphism carrying one arc to another carries one edge to the other. -/

end

section
variable {G H : CGraph}

/-- A clique of `G □ H` lives in a single row or a single column, so the cartesian product has the
larger of the two clique numbers.  Both factors have to be nonempty: otherwise the product is the
empty graph, whose clique number is `0`. -/
@[toIsoGraph]
theorem cliqueNum_cartesianProduct {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (G □g H).cliqueNum = max G.cliqueNum H.cliqueNum :=
  cliqueNum_of_cartesian_adj (S := G.toSimple) (T := H.toSimple)
    (P := (G □g H).toSimple) (Classical.arbitrary G.V)
      (Classical.arbitrary H.V) fun p q ↦ by
      simp only [CGraph.toSimple_adj, cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]

/-- The tensor product has the smaller of the two clique numbers. -/
theorem cliqueNum_tensorProduct (G H : CGraph) :
    (G ⊗g H).cliqueNum = min G.cliqueNum H.cliqueNum :=
  cliqueNum_of_tensor_adj (S := G.toSimple) (T := H.toSimple)
    (P := (G ⊗g H).toSimple) fun p q ↦ by
      simp only [CGraph.toSimple_adj, tensorProduct_adj, Bool.and_eq_true]

/-- The lexicographic product multiplies clique numbers, just like the strong product. -/
theorem cliqueNum_lexProduct (G H : CGraph) :
    (G ·g H).cliqueNum = G.cliqueNum * H.cliqueNum :=
  cliqueNum_of_lex_adj (S := G.toSimple) (T := H.toSimple)
    (P := (G ·g H).toSimple) fun p q ↦ by
      simp only [CGraph.toSimple_adj, lexProduct_adj, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]

theorem chromNum_le_iff_colorable {G : CGraph} {n : ℕ} : G.chromNum ≤ n ↔ G.toSimple.Colorable n := by
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable, ← coe_chromNum, Nat.cast_le]

theorem colorable_chromNum {G : CGraph} : G.toSimple.Colorable G.chromNum := chromNum_le_iff_colorable.1 le_rfl

/-- **An explicit colouring bounds the chromatic number.**  The witness direction of
`chromNum ≤ k`, in the form a computed colouring comes in: a function to `Fin k` whose properness
is a decidable statement about `Adj`. -/
theorem chromNum_le_of_colouring {G : CGraph} {k : ℕ} (c : G.V → Fin k)
    (h : ∀ u v : G.V, G.Adj u v = true → c u ≠ c v) : G.chromNum ≤ k := by
  refine chromNum_le_iff_colorable.2 ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro u v huv
  exact h u v ((toSimple_adj _ _ _).1 huv)

theorem le_chromNum_iff {G : CGraph} {n : ℕ} : n ≤ G.chromNum ↔ ∀ m, G.toSimple.Colorable m → n ≤ m := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, SimpleGraph.le_chromaticNumber_iff_colorable]

theorem chromNum_eq_iff {G : CGraph} {n : ℕ} :
    G.chromNum = n ↔ G.toSimple.Colorable n ∧ ∀ m, G.toSimple.Colorable m → n ≤ m := by
  rw [le_antisymm_iff, chromNum_le_iff_colorable, le_chromNum_iff]

/-! ### Values of the chromatic number -/

theorem chromNum_eq_of_chromaticNumber {G : CGraph} {n : ℕ}
    (h : G.toSimple.chromaticNumber = n) : G.chromNum = n := by
  rw [← Nat.cast_inj (R := ℕ∞), coe_chromNum, h]

@[toIsoGraph chromNum_le_V]
theorem chromNum_le_card (G : CGraph) : G.chromNum ≤ FinEnum.card G.V := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, FinEnum.card_eq_fintypeCard' (α := G.V)]
  exact SimpleGraph.chromaticNumber_le_card

/-- A clique needs one colour per vertex, so `ω(G) ≤ χ(G)`. -/
@[toIsoGraph]
theorem cliqueNum_le_chromNum (G : CGraph) : G.cliqueNum ≤ G.chromNum := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.cliqueNum_le_chromaticNumber

theorem two_le_chromNum_of_adj {G : CGraph} {a b : G.V} (h : G.Adj a b) : 2 ≤ G.chromNum := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.two_le_chromaticNumber_of_adj h

@[simp, toIsoGraph] theorem chromNum_empty_zero : (empty 0).chromNum = 0 :=
  chromNum_eq_of_chromaticNumber (by
    haveI : IsEmpty (empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
    rw [empty_toSimple]
    exact SimpleGraph.chromaticNumber_eq_zero_of_isEmpty)

@[simp, toIsoGraph] theorem chromNum_empty (n : ℕ) : (empty (n + 1)).chromNum = 1 :=
  chromNum_eq_of_chromaticNumber (by
    haveI : Nonempty (empty (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))
    rw [empty_toSimple]
    exact SimpleGraph.chromaticNumber_bot (V := (empty (n + 1)).V))

/-- **`K_n` needs `n` colours.** -/
@[simp, toIsoGraph] theorem chromNum_complete (n : ℕ) : (complete n).chromNum = n :=
  chromNum_eq_of_chromaticNumber (by rw [complete_toSimple, SimpleGraph.chromaticNumber_top,
    ← FinEnum.card_eq_fintypeCard', card_complete])

@[simp, toIsoGraph] theorem chromNum_path (n : ℕ) : (path (n + 2)).chromNum = 2 :=
  chromNum_eq_of_chromaticNumber (by
    rw [path_toSimple]; exact SimpleGraph.chromaticNumber_pathGraph _ (by omega))

/-- **An even cycle is bipartite.** -/
@[toIsoGraph]
theorem chromNum_cycle_even (m : ℕ) : (cycle (2 * m + 2)).chromNum = 2 :=
  chromNum_eq_of_chromaticNumber (by
    rw [cycle_toSimple]
    exact SimpleGraph.chromaticNumber_cycleGraph_of_even _ (by omega) ⟨m + 1, by omega⟩)

/-- **An odd cycle needs three colours.** -/
@[toIsoGraph]
theorem chromNum_cycle_odd (m : ℕ) : (cycle (2 * m + 3)).chromNum = 3 :=
  chromNum_eq_of_chromaticNumber (by
    rw [cycle_toSimple]
    exact SimpleGraph.chromaticNumber_cycleGraph_of_odd _ (by omega) ⟨m + 1, by omega⟩)

/-- **Colouring the two halves of a disjoint union is independent.** -/
@[simp, toIsoGraph] theorem chromNum_disjUnion (G H : CGraph) :
    (G ⊕g H).chromNum = max G.chromNum H.chromNum := by
  have hmax : ((max G.chromNum H.chromNum : ℕ) : ℕ∞)
      = max (G.chromNum : ℕ∞) (H.chromNum : ℕ∞) := by
    rcases le_total G.chromNum H.chromNum with h | h
    · rw [max_eq_right h, max_eq_right (Nat.cast_le.2 h)]
    · rw [max_eq_left h, max_eq_left (Nat.cast_le.2 h)]
  rw [← Nat.cast_inj (R := ℕ∞), coe_chromNum, toSimple_disjUnion,
    SimpleGraph.chromaticNumber_sum, hmax, coe_chromNum, coe_chromNum]

/-- An edge is a two-clique. -/
theorem two_le_cliqueNum {G : CGraph} {a b : G.V} (hab : G.Adj a b) : 2 ≤ G.cliqueNum := by
  classical
  have hne : a ≠ b := ((toSimple_adj G a b).2 hab).ne
  have hcl : G.toSimple.IsClique ((({a, b} : Finset G.V)) : Set G.V) := by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.isClique_pair.2 fun _ ↦ (toSimple_adj G a b).2 hab
  have := SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl)
  rwa [Finset.card_pair hne] at this

/-- A single vertex is a one-clique. -/
theorem one_le_cliqueNum_of_vertex {G : CGraph} (a : G.V) : 1 ≤ G.cliqueNum := by
  classical
  have hcl : G.toSimple.IsClique ((({a} : Finset G.V)) : Set G.V) := by simp
  have := SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl)
  simpa using this

/-- **A nonempty graph has a clique**: a single vertex is one. -/
@[toIsoGraph]
theorem one_le_cliqueNum {G : CGraph} [Nonempty G.V] : 1 ≤ G.cliqueNum :=
  one_le_cliqueNum_of_vertex (Classical.arbitrary G.V)

@[toIsoGraph]
theorem two_le_cliqueNum_of_E_pos {G : CGraph} (h : 0 < G.E) : 2 ≤ G.cliqueNum := by
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos h
  exact two_le_cliqueNum hab

/-- **A list of pairwise adjacent vertices bounds the clique number below.**  Both hypotheses are
decidable, so a clique found by machine is checked by `decide`. -/
theorem le_cliqueNum_of_nodup {G : CGraph} {l : List G.V} (hnd : l.Nodup)
    (h : ∀ u ∈ l, ∀ v ∈ l, u ≠ v → G.Adj u v = true) : l.length ≤ G.cliqueNum := by
  classical
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
  have hcl : G.toSimple.IsClique (↑l.toFinset : Set G.V) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe, List.mem_toFinset] at hu hv
    rw [toSimple_adj]
    exact h u hu v hv huv
  show l.length ≤ G.toSimple.cliqueNum
  rw [← hcard]
  exact SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl)

/-! ### Maximum and minimum degree -/

/-! ### Greedy colouring and Nordhaus–Gaddum -/

end

section
variable {G H : CGraph}
variable {X : Type} [Fintype X] [DecidableEq X]

/-- **Greedy colouring**: a graph all of whose degrees are at most `d` is `(d + 1)`-colourable.
The colouring is built one vertex at a time: a vertex has at most `d` neighbours already
coloured, so one of the `d + 1` colours is still free for it. -/
private theorem colorable_of_forall_degree_le (S : SimpleGraph X) [DecidableRel S.Adj] {d : ℕ}
    (hd : ∀ v, S.degree v ≤ d) : S.Colorable (d + 1) := by
  classical
  have key : ∀ s : Finset X, ∃ c : X → Fin (d + 1),
      ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨fun _ ↦ 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨k, hk⟩ : ∃ k : Fin (d + 1), k ∉ (S.neighborFinset a).image c := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (Fin (d + 1))) ⊆ (S.neighborFinset a).image c :=
          fun k _ ↦ hcon k
        have h1 := Finset.card_le_card hsub
        have h2 : ((S.neighborFinset a).image c).card ≤ d :=
          le_trans (Finset.card_image_le) (hd a)
        rw [Finset.card_univ, Fintype.card_fin] at h1
        omega
      refine ⟨Function.update c a k, fun x hx y hy hxy ↦ ?_⟩
      have hax : ∀ z ∈ s, z ≠ a := fun z hz h ↦ ha (h ▸ hz)
      rcases Finset.mem_insert.1 hx with rfl | hx' <;>
        rcases Finset.mem_insert.1 hy with rfl | hy'
      · exact absurd rfl hxy.ne
      · rw [Function.update_self, Function.update_of_ne (hax y hy')]
        intro h
        exact hk (Finset.mem_image.2 ⟨y, by simp [hxy], h.symm⟩)
      · rw [Function.update_self, Function.update_of_ne (hax x hx')]
        intro h
        exact hk (Finset.mem_image.2 ⟨x, by simp [hxy.symm], h⟩)
      · rw [Function.update_of_ne (hax x hx'), Function.update_of_ne (hax y hy')]
        exact hc x hx' y hy' hxy
  obtain ⟨c, hc⟩ := key Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c fun {x y} hxy ↦
    hc x (Finset.mem_univ x) y (Finset.mem_univ y) hxy⟩

end

section
variable {G H : CGraph}

/-! ### Greedy colouring -/

/-- **The greedy bound** `χ ≤ Δ + 1`. -/
@[toIsoGraph]
theorem chromNum_le_maxDeg_add_one (G : CGraph) : G.chromNum ≤ G.maxDeg + 1 := by
  classical
  exact chromNum_le_iff_colorable.2
    (colorable_of_forall_degree_le G.toSimple fun v ↦ G.degree_le_maxDeg v)

/-- Contrapositive of the greedy bound: a `k`-chromatic graph has a vertex of degree `k - 1`. -/
theorem chromNum_le_maxDeg (G : CGraph) (h : 2 ≤ G.chromNum) : G.chromNum - 1 ≤ G.maxDeg := by
  have := G.chromNum_le_maxDeg_add_one
  omega

/-! ### Colouring around a maximum independent set -/

/-- Colour a maximum independent set with a single colour and every other vertex with its own:
`χ ≤ |V| - α + 1`. -/
@[toIsoGraph chromNum_le_V_sub_indepNum_add_one]
theorem chromNum_le_card_sub_indepNum_add_one (G : CGraph) :
    G.chromNum ≤ FinEnum.card G.V - G.indepNum + 1 := by
  classical
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcard' : s.card = G.indepNum := hcard
  have hcompl : Fintype.card {v : G.V // v ∉ s} = FinEnum.card G.V - G.indepNum := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hcard', ← FinEnum.card_eq_fintypeCard']
  obtain ⟨e⟩ : Nonempty ({v : G.V // v ∉ s} ≃ Fin (FinEnum.card G.V - G.indepNum)) :=
    ⟨Fintype.equivFinOfCardEq hcompl⟩
  set f : G.V → ℕ := fun v ↦ if h : v ∈ s then 0 else (e ⟨v, h⟩ : ℕ) + 1 with hf
  refine chromNum_le_iff_colorable.2 ((SimpleGraph.colorable_iff_exists_bdd_nat_coloring _).2
    ⟨SimpleGraph.Coloring.mk f ?_, fun v ↦ ?_⟩)
  · intro x y hxy
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · exact absurd hxy (hs (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hxy.ne)
    · simp [hf, hx, hy]
    · simp [hf, hx, hy]
    · simp only [hf, dif_neg hx, dif_neg hy, ne_eq, Nat.add_right_cancel_iff]
      intro h
      exact hxy.ne (congrArg Subtype.val (e.injective (Fin.val_injective h)))
  · show f v < _
    by_cases h : v ∈ s
    · simp [hf, h]
    · simp only [hf, dif_neg h]
      have := (e ⟨v, h⟩).isLt
      omega

/-- The same bound in additive form. -/
@[toIsoGraph chromNum_add_indepNum_le_V_add_one]
theorem chromNum_add_indepNum_le_card_add_one (G : CGraph) :
    G.chromNum + G.indepNum ≤ FinEnum.card G.V + 1 := by
  have h := G.chromNum_le_card_sub_indepNum_add_one
  have h2 : G.indepNum ≤ FinEnum.card G.V := by
    obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
    have hcard' : G.indepNum = s.card := hcard.symm
    rw [hcard', ← FinEnum.card_univ]
    exact Finset.card_le_univ s
  omega

end

section
variable {G H : CGraph}
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The number of colours needed to colour just the vertices of `s` properly, ignoring every
vertex outside `s`.  This is the chromatic number of the subgraph induced on `s`, phrased so
that induction can add one vertex at a time. -/
private noncomputable def chromOn (S : SimpleGraph X) (s : Finset X) : ℕ :=
  sInf {n | ∃ c : X → ℕ, (∀ v ∈ s, c v < n) ∧ ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y}

omit [Fintype X] [DecidableEq X] in
private theorem chromOn_le {S : SimpleGraph X} {s : Finset X} {n : ℕ} (c : X → ℕ)
    (hb : ∀ v ∈ s, c v < n) (hp : ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y) :
    chromOn S s ≤ n :=
  Nat.sInf_le ⟨c, hb, hp⟩

omit [DecidableEq X] in
private theorem exists_chromOn_coloring (S : SimpleGraph X) (s : Finset X) :
    ∃ c : X → ℕ, (∀ v ∈ s, c v < chromOn S s) ∧
      ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y := by
  have hne : {n | ∃ c : X → ℕ, (∀ v ∈ s, c v < n) ∧
      ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y}.Nonempty := by
    refine ⟨Fintype.card X, fun v ↦ (Fintype.equivFin X v : ℕ),
      fun v _ ↦ (Fintype.equivFin X v).isLt, fun x _ y _ hxy h ↦ ?_⟩
    exact hxy.ne ((Fintype.equivFin X).injective (Fin.val_injective h))
  exact Nat.sInf_mem hne

omit [Fintype X] [DecidableEq X] in
private theorem chromOn_empty (S : SimpleGraph X) : chromOn S ∅ = 0 :=
  Nat.le_zero.1 (chromOn_le (fun _ ↦ 0) (by simp) (by simp))

private theorem chromOn_insert_le (S : SimpleGraph X) (a : X) (s : Finset X) :
    chromOn S (insert a s) ≤ chromOn S s + 1 := by
  obtain ⟨c, hb, hp⟩ := exists_chromOn_coloring S s
  refine chromOn_le (Function.update c a (chromOn S s)) ?_ ?_
  · intro v hv
    rcases eq_or_ne v a with rfl | hva
    · rw [Function.update_self]; omega
    · rw [Function.update_of_ne hva]
      have := hb v ((Finset.mem_insert.1 hv).resolve_left hva)
      omega
  · intro x hx y hy hxy
    rcases eq_or_ne x a with rfl | hxa
    · rcases eq_or_ne y x with rfl | hyx
      · exact absurd rfl hxy.ne
      · rw [Function.update_self, Function.update_of_ne hyx]
        exact fun h ↦ absurd (hb y ((Finset.mem_insert.1 hy).resolve_left hyx)) (by omega)
    · rcases eq_or_ne y a with rfl | hya
      · rw [Function.update_self, Function.update_of_ne hxa]
        exact fun h ↦ absurd (hb x ((Finset.mem_insert.1 hx).resolve_left hxa)) (by omega)
      · rw [Function.update_of_ne hxa, Function.update_of_ne hya]
        exact hp x ((Finset.mem_insert.1 hx).resolve_left hxa)
          y ((Finset.mem_insert.1 hy).resolve_left hya) hxy

/-- If the neighbours of `a` inside `s` fit into a set smaller than `χ(s)`, then `a` can reuse
one of the colours already in play: adding it costs nothing. -/
private theorem chromOn_insert_le_of_lt (S : SimpleGraph X) {a : X} {s t : Finset X} (ha : a ∉ s)
    (ht : ∀ v ∈ s, S.Adj a v → v ∈ t) (hlt : t.card < chromOn S s) :
    chromOn S (insert a s) ≤ chromOn S s := by
  obtain ⟨c, hb, hp⟩ := exists_chromOn_coloring S s
  obtain ⟨k, hk⟩ : ((Finset.range (chromOn S s)) \ (t.image c)).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.le_card_sdiff (t.image c) (Finset.range (chromOn S s))
    have h2 : (t.image c).card ≤ t.card := Finset.card_image_le
    have h3 : (Finset.range (chromOn S s)).card = chromOn S s := Finset.card_range _
    omega
  rw [Finset.mem_sdiff, Finset.mem_range] at hk
  obtain ⟨hklt, hkni⟩ := hk
  have hane : ∀ v ∈ s, v ≠ a := fun v hv h ↦ ha (h ▸ hv)
  refine chromOn_le (Function.update c a k) ?_ ?_
  · intro v hv
    rcases eq_or_ne v a with rfl | hva
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hva]
      exact hb v ((Finset.mem_insert.1 hv).resolve_left hva)
  · intro x hx y hy hxy
    rcases eq_or_ne x a with rfl | hxa
    · have hys : y ∈ s := (Finset.mem_insert.1 hy).resolve_left (Ne.symm hxy.ne)
      rw [Function.update_self, Function.update_of_ne (hane y hys)]
      exact fun h ↦ hkni (Finset.mem_image.2 ⟨y, ht y hys hxy, h.symm⟩)
    · rcases eq_or_ne y a with rfl | hya
      · have hxs : x ∈ s := (Finset.mem_insert.1 hx).resolve_left hxa
        rw [Function.update_self, Function.update_of_ne (hane x hxs)]
        exact fun h ↦ hkni (Finset.mem_image.2 ⟨x, ht x hxs hxy.symm, h⟩)
      · rw [Function.update_of_ne hxa, Function.update_of_ne hya]
        exact hp x ((Finset.mem_insert.1 hx).resolve_left hxa)
          y ((Finset.mem_insert.1 hy).resolve_left hya) hxy

/-- **Nordhaus–Gaddum, sum form**, in the `chromOn` formulation: colouring `s` in `S` and in its
complement together costs at most `|s| + 1` colours. -/
private theorem chromOn_add_chromOn_compl_le (S : SimpleGraph X) (s : Finset X) :
    chromOn S s + chromOn Sᶜ s ≤ s.card + 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp [chromOn_empty]
  | insert a s ha ih =>
    have h1 := chromOn_insert_le S a s
    have h2 := chromOn_insert_le Sᶜ a s
    rw [Finset.card_insert_of_notMem ha]
    by_cases hA : chromOn S (insert a s) ≤ chromOn S s
    · omega
    by_cases hB : chromOn Sᶜ (insert a s) ≤ chromOn Sᶜ s
    · omega
    have hpa : chromOn S s ≤ (s.filter fun v ↦ S.Adj a v).card := by
      by_contra hcon
      push_neg at hcon
      exact hA (chromOn_insert_le_of_lt S ha (fun v hv hadj ↦ Finset.mem_filter.2 ⟨hv, hadj⟩) hcon)
    have hqa : chromOn Sᶜ s ≤ (s.filter fun v ↦ ¬ S.Adj a v).card := by
      by_contra hcon
      push_neg at hcon
      refine hB (chromOn_insert_le_of_lt Sᶜ ha (fun v hv hadj ↦ Finset.mem_filter.2 ⟨hv, ?_⟩) hcon)
      exact (SimpleGraph.compl_adj S a v).1 hadj |>.2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := s) (p := fun v ↦ S.Adj a v)
    omega

end

section
variable {G H : CGraph}

private theorem chromNum_eq_chromOn_univ (G : CGraph) :
    G.chromNum = chromOn G.toSimple Finset.univ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨c, hb, hp⟩ := exists_chromOn_coloring G.toSimple Finset.univ
    refine chromNum_le_iff_colorable.2 ((SimpleGraph.colorable_iff_exists_bdd_nat_coloring _).2
      ⟨SimpleGraph.Coloring.mk c fun {x y} hxy ↦
        hp x (Finset.mem_univ x) y (Finset.mem_univ y) hxy, fun v ↦ hb v (Finset.mem_univ v)⟩)
  · obtain ⟨C, hC⟩ := (SimpleGraph.colorable_iff_exists_bdd_nat_coloring _).1 G.colorable_chromNum
    exact chromOn_le (fun v ↦ C v) (fun v _ ↦ hC v)
      (fun x _ y _ hxy ↦ C.valid hxy)

/-- **Nordhaus–Gaddum, sum form**: `χ(G) + χ(Gᶜ) ≤ |V| + 1`. -/
@[toIsoGraph chromNum_add_chromNum_compl_le_V_add_one]
theorem chromNum_add_chromNum_compl_le_card_add_one (G : CGraph) :
    G.chromNum + Gᶜ.chromNum ≤ FinEnum.card G.V + 1 := by
  have h := chromOn_add_chromOn_compl_le G.toSimple (Finset.univ : Finset G.V)
  rw [FinEnum.card_univ] at h
  rwa [G.chromNum_eq_chromOn_univ, show Gᶜ.chromNum = chromOn G.toSimpleᶜ Finset.univ from
    by rw [Gᶜ.chromNum_eq_chromOn_univ, compl_toSimple]]

end

section
variable {G H : CGraph}
variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Being `n`-clique-free is the same as having clique number below `n`. -/
theorem cliqueFree_iff_cliqueNum_lt {S : SimpleGraph X} {n : ℕ} :
    S.CliqueFree n ↔ S.cliqueNum < n := by
  constructor
  · intro hcf
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs⟩ := S.exists_isNClique_cliqueNum
    obtain ⟨t, hts, htc⟩ :=
      Finset.exists_subset_card_eq (n := n) (show n ≤ s.card by rw [hs.card_eq]; exact hcon)
    exact hcf t ⟨hs.isClique.subset (by exact_mod_cast hts), htc⟩
  · intro hlt s hs
    exact absurd (hs.card_eq ▸ hs.isClique.card_le_cliqueNum) (by omega)

omit [DecidableEq X] in
/-- **Turán's theorem**, in the loose form `2r·|E| ≤ (r - 1)·|V|²`: a graph with no `K_{r+1}`
has at most as many edges as the Turán graph, which has at most that many. -/
theorem mul_card_edgeFinset_le_of_cliqueFree {S : SimpleGraph X} [DecidableRel S.Adj]
    {r : ℕ} (hr : 0 < r) (cf : S.CliqueFree (r + 1)) :
    2 * r * S.edgeFinset.card ≤ (r - 1) * (Fintype.card X) ^ 2 := by
  classical
  obtain ⟨H, _, maxH⟩ := SimpleGraph.exists_isTuranMaximal (V := X) hr
  have h1 : S.edgeFinset.card ≤ H.edgeFinset.card := maxH.2 cf
  have h3 : H.edgeFinset.card = (SimpleGraph.turanGraph (Fintype.card X) r).edgeFinset.card :=
    ((SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp maxH).some.card_edgeFinset_eq
  calc 2 * r * S.edgeFinset.card
      ≤ 2 * r * (SimpleGraph.turanGraph (Fintype.card X) r).edgeFinset.card := by
        rw [← h3]; exact Nat.mul_le_mul_left _ h1
    _ ≤ (r - 1) * (Fintype.card X) ^ 2 := SimpleGraph.mul_card_edgeFinset_turanGraph_le

omit [DecidableEq X] in
/-- **The key pigeonhole step.**  If `v` has three neighbours in `T`, then either two of them are
adjacent — giving a triangle through `v` — or they are pairwise non-adjacent, giving a triangle in
the complement. -/
private theorem three_le_cliqueNum_of_neighbors (T : SimpleGraph X) (v : X) (A : Finset X)
    (hA : ∀ x ∈ A, T.Adj v x) (hcard : 3 ≤ A.card) :
    3 ≤ T.cliqueNum ∨ 3 ≤ Tᶜ.cliqueNum := by
  classical
  by_cases hex : ∃ x ∈ A, ∃ y ∈ A, T.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hex
    left
    have hcl : T.IsNClique 3 {v, x, y} :=
      SimpleGraph.is3Clique_triple_iff.2 ⟨hA x hx, hA y hy, hxy⟩
    have := hcl.isClique.card_le_cliqueNum
    rwa [hcl.card_eq] at this
  · push_neg at hex
    right
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 3) hcard
    have hcl : Tᶜ.IsClique (t : Set X) := by
      intro x hx y hy hxy
      exact ⟨hxy, hex x (hts (Finset.mem_coe.1 hx)) y (hts (Finset.mem_coe.1 hy))⟩
    have := hcl.card_le_cliqueNum
    rwa [htc] at this

/-- **Ramsey's theorem for `R(3, 3)`, complement form**: on six or more vertices, either the graph
or its complement contains a triangle.  Fix a vertex `v`: of the five other vertices, three are
neighbours of `v` or three are non-neighbours, and either way the pigeonhole step above applies. -/
private theorem three_le_cliqueNum_or_compl (T : SimpleGraph X) (h : 6 ≤ Fintype.card X) :
    3 ≤ T.cliqueNum ∨ 3 ≤ Tᶜ.cliqueNum := by
  classical
  obtain ⟨v⟩ : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  set N := T.neighborFinset v with hN
  set M := (Finset.univ : Finset X) \ insert v N with hM
  have hvN : v ∉ N := by simp [hN]
  have hins := Finset.card_le_univ (insert v N)
  rw [Finset.card_insert_of_notMem hvN] at hins
  have hcards : N.card + M.card + 1 = Fintype.card X := by
    rw [hM, Finset.card_univ_diff, Finset.card_insert_of_notMem hvN]
    omega
  have hMadj : ∀ x ∈ M, Tᶜ.Adj v x := by
    intro x hx
    rw [hM, Finset.mem_sdiff, Finset.mem_insert] at hx
    push_neg at hx
    refine (SimpleGraph.compl_adj _ _ _).2 ⟨fun hvx ↦ hx.2.1 hvx.symm, fun hadj ↦ hx.2.2 ?_⟩
    rw [hN, SimpleGraph.mem_neighborFinset]
    exact hadj
  rcases (show 3 ≤ N.card ∨ 3 ≤ M.card by omega) with hc | hc
  · exact three_le_cliqueNum_of_neighbors T v N
      (fun x hx ↦ (SimpleGraph.mem_neighborFinset _ _ _).1 hx) hc
  · have := three_le_cliqueNum_of_neighbors Tᶜ v M hMadj hc
    rw [or_comm] at this
    simpa using this

omit [Fintype X] [DecidableEq X] in
/-- **Erdős–Szekeres**: inside any vertex set of size at least `C(s + t, s)` there is a clique of
size `s` or a clique of size `t` in the complement.  The induction is the classical one: pick a
vertex `v` of `u`, split the rest into the neighbours `A` and non-neighbours `B` of `v`; Pascal's
rule says `|A| ≥ C(s - 1 + t, s - 1)` or `|B| ≥ C(s + t - 1, s)`, and in each case the smaller
instance either already gives what is wanted or gives a set that `v` extends. -/
private theorem exists_clique_or_clique_compl (T : SimpleGraph X) :
    ∀ (s t : ℕ) (u : Finset X), (s + t).choose s ≤ u.card →
      (∃ c ⊆ u, T.IsClique (c : Set X) ∧ c.card = s) ∨
      (∃ c ⊆ u, Tᶜ.IsClique (c : Set X) ∧ c.card = t) := by
  classical
  intro s
  induction s with
  | zero => exact fun t u _ ↦ Or.inl ⟨∅, by simp, by simp, rfl⟩
  | succ s ihs =>
    intro t
    induction t with
    | zero => exact fun u _ ↦ Or.inr ⟨∅, by simp, by simp, rfl⟩
    | succ t iht =>
      intro u hu
      have hpascal : (s + 1 + (t + 1)).choose (s + 1)
          = (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        have e1 : s + 1 + (t + 1) = s + t + 1 + 1 := by omega
        have e2 : s + (t + 1) = s + t + 1 := by omega
        have e3 : s + 1 + t = s + t + 1 := by omega
        rw [e1, e2, e3, Nat.choose_succ_succ]
      have hpos : 0 < u.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hu
      obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
      set A := (u.erase v).filter (fun x ↦ T.Adj v x) with hA
      set B := (u.erase v).filter (fun x ↦ ¬ T.Adj v x) with hB
      have hsplit : A.card + B.card = (u.erase v).card :=
        Finset.card_filter_add_card_filter_not _
      have herase : (u.erase v).card = u.card - 1 := Finset.card_erase_of_mem hv
      have hAu : A ⊆ u := fun x hx ↦ Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
      have hBu : B ⊆ u := fun x hx ↦ Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
      rcases (show (s + (t + 1)).choose s ≤ A.card ∨ (s + 1 + t).choose (s + 1) ≤ B.card by
        omega) with hc | hc
      · rcases ihs (t + 1) A hc with ⟨c, hcA, hcl, hcard⟩ | ⟨c, hcA, hcl, hcard⟩
        · left
          have hvc : v ∉ c := fun hmem ↦
            (Finset.mem_erase.1 (Finset.mem_filter.1 (hcA hmem)).1).1 rfl
          refine ⟨insert v c, ?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.1 hx with rfl | hx
            · exact hv
            · exact hAu (hcA hx)
          · rw [Finset.coe_insert]
            exact hcl.insert fun b hb _ ↦ (Finset.mem_filter.1 (hcA (Finset.mem_coe.1 hb))).2
          · rw [Finset.card_insert_of_notMem hvc, hcard]
        · exact Or.inr ⟨c, fun x hx ↦ hAu (hcA hx), hcl, hcard⟩
      · rcases iht B hc with ⟨c, hcB, hcl, hcard⟩ | ⟨c, hcB, hcl, hcard⟩
        · exact Or.inl ⟨c, fun x hx ↦ hBu (hcB hx), hcl, hcard⟩
        · right
          have hvc : v ∉ c := fun hmem ↦
            (Finset.mem_erase.1 (Finset.mem_filter.1 (hcB hmem)).1).1 rfl
          refine ⟨insert v c, ?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.1 hx with rfl | hx
            · exact hv
            · exact hBu (hcB hx)
          · rw [Finset.coe_insert]
            refine hcl.insert fun b hb hne ↦ (SimpleGraph.compl_adj _ _ _).2 ⟨hne, ?_⟩
            exact (Finset.mem_filter.1 (hcB (Finset.mem_coe.1 hb))).2
          · rw [Finset.card_insert_of_notMem hvc, hcard]

end

section
variable {G H : CGraph}

/-! ### The Ramsey number `R(3, 3)` -/

/-- **`R(3, 3) ≤ 6`**: any graph on at least six vertices has three mutually adjacent vertices or
three mutually non-adjacent ones. -/
@[toIsoGraph]
theorem three_le_cliqueNum_or_three_le_indepNum (G : CGraph) (h : 6 ≤ FinEnum.card G.V) :
    3 ≤ G.cliqueNum ∨ 3 ≤ G.indepNum := by
  classical
  have := three_le_cliqueNum_or_compl G.toSimple
    (by rwa [← FinEnum.card_eq_fintypeCard'] : 6 ≤ Fintype.card G.V)
  rwa [SimpleGraph.cliqueNum_compl] at this

/-- Triangle-free form: a triangle-free graph on six or more vertices has three pairwise
non-adjacent vertices. -/
@[toIsoGraph]
theorem three_le_indepNum_of_cliqueNum_le_two (G : CGraph) (h : 6 ≤ FinEnum.card G.V)
    (hcl : G.cliqueNum ≤ 2) : 3 ≤ G.indepNum := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · omega
  · exact h'

/-! ### Ramsey numbers in general -/

/-- **Ramsey's theorem**, `R(s, t) ≤ C(s + t, s)`: a graph on at least `C(s + t, s)` vertices has
a clique on `s` vertices or an independent set on `t` vertices. -/
@[toIsoGraph]
theorem le_cliqueNum_or_le_indepNum (G : CGraph) {s t : ℕ}
    (h : (s + t).choose s ≤ FinEnum.card G.V) : s ≤ G.cliqueNum ∨ t ≤ G.indepNum := by
  classical
  rcases exists_clique_or_clique_compl G.toSimple s t Finset.univ
      (by rwa [FinEnum.card_univ]) with ⟨c, -, hcl, hcard⟩ | ⟨c, -, hcl, hcard⟩
  · exact Or.inl (hcard ▸ hcl.card_le_cliqueNum)
  · refine Or.inr ?_
    have := hcl.card_le_cliqueNum
    rw [hcard, SimpleGraph.cliqueNum_compl] at this
    exact this

end

section
variable {G H : CGraph}
variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- **Gallai's identity** at the level of `SimpleGraph`: the complement of a vertex cover is an
independent set and vice versa, so `τ + α = |V|`. -/
private theorem vertexCoverNum_toNat_add_indepNum (S : SimpleGraph X) :
    S.vertexCoverNum.toNat + S.indepNum = Fintype.card X := by
  classical
  obtain ⟨s, hs⟩ := S.exists_isNIndepSet_indepNum
  have hα : s.card = S.indepNum := hs.card_eq
  have hαle : S.indepNum ≤ Fintype.card X := by
    rw [← hα, ← Finset.card_univ]
    exact Finset.card_le_univ s
  -- `τ ≤ |V| - α`, using the complement of a maximum independent set as a cover.
  have hle : S.vertexCoverNum.toNat + S.indepNum ≤ Fintype.card X := by
    have hcov : S.IsVertexCover ((s : Set X)ᶜ) :=
      SimpleGraph.isVertexCover_compl.2 hs.isIndepSet
    have h1 := hcov.vertexCoverNum_le
    rw [← Finset.coe_compl, Set.encard_coe_eq_coe_finsetCard, Finset.card_compl] at h1
    have h2 : S.vertexCoverNum.toNat ≤ Fintype.card X - s.card := by
      have := ENat.toNat_le_toNat h1 (by simp)
      simpa using this
    omega
  -- `|V| - α ≤ τ`, since the complement of a minimum cover is independent.
  have hge : Fintype.card X ≤ S.vertexCoverNum.toNat + S.indepNum := by
    obtain ⟨c, hcard, hcov⟩ := S.vertexCoverNum_exists
    have hind : S.IsIndepSet cᶜ := SimpleGraph.isIndepSet_compl_iff_isVertexCover.2 hcov
    have hfin : S.IsIndepSet ((cᶜ.toFinset : Finset X) : Set X) := by
      rwa [Set.coe_toFinset]
    have h1 : (cᶜ.toFinset : Finset X).card ≤ S.indepNum := hfin.card_le_indepNum
    have h2 : c.toFinset.card + cᶜ.toFinset.card = Fintype.card X := by
      rw [Set.toFinset_compl, Finset.card_compl]
      have := Finset.card_le_univ c.toFinset
      omega
    have h3 : S.vertexCoverNum.toNat = c.toFinset.card := by
      have hc : c.encard = (c.toFinset.card : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
      rw [← hcard, hc]
      simp
    omega
  omega

omit [DecidableEq X] in
/-- A minimum vertex cover, as a `Finset`. -/
private theorem exists_cover_finset (S : SimpleGraph X) :
    ∃ C : Finset X, (∀ ⦃x y⦄, S.Adj x y → x ∈ C ∨ y ∈ C) ∧
      C.card = S.vertexCoverNum.toNat := by
  classical
  obtain ⟨c, hcard, hcov⟩ := S.vertexCoverNum_exists
  refine ⟨c.toFinset, fun x y hxy ↦ ?_, ?_⟩
  · simpa using hcov hxy
  · have hc : c.encard = (c.toFinset.card : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
    rw [← hcard, hc]
    simp

/-- **Every edge meets the cover**, so the edges are covered by the incidence sets of the `τ`
cover vertices, each of which has at most `Δ` edges: `|E| ≤ τ·Δ`. -/
theorem card_edgeFinset_le_vertexCoverNum_mul_maxDegree (S : SimpleGraph X)
    [DecidableRel S.Adj] :
    S.edgeFinset.card ≤ S.vertexCoverNum.toNat * S.maxDegree := by
  classical
  obtain ⟨C, hC, hcard⟩ := exists_cover_finset S
  have hsub : S.edgeFinset ⊆ C.biUnion (fun v ↦ S.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hC he with hx | hy
    · exact Finset.mem_biUnion.2 ⟨x, hx, by
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨(SimpleGraph.mem_edgeSet _).2 he, by simp⟩⟩
    · exact Finset.mem_biUnion.2 ⟨y, hy, by
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨(SimpleGraph.mem_edgeSet _).2 he, by simp⟩⟩
  calc S.edgeFinset.card ≤ (C.biUnion (fun v ↦ S.incidenceFinset v)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ C, (S.incidenceFinset v).card := Finset.card_biUnion_le
    _ ≤ C.card * S.maxDegree := by
        rw [← smul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun v _ ↦ ?_
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact SimpleGraph.degree_le_maxDegree S v
    _ = S.vertexCoverNum.toNat * S.maxDegree := by rw [hcard]

end

section
variable {G H : CGraph}

/-! ### The vertex cover number -/

/-- **Gallai's identity**: a set of vertices is a vertex cover exactly when its complement is
independent, so `τ(G) + α(G) = |V|`. -/
@[toIsoGraph]
theorem coverNum_add_indepNum (G : CGraph) :
    G.coverNum + G.indepNum = FinEnum.card G.V := by
  classical
  rw [FinEnum.card_eq_fintypeCard']
  exact vertexCoverNum_toNat_add_indepNum G.toSimple

/-- A vertex cover needs at most one vertex per edge. -/
@[toIsoGraph]
theorem coverNum_le_E (G : CGraph) : G.coverNum ≤ G.E := by
  classical
  have h := G.toSimple.vertexCoverNum_le_encard_edgeSet
  have he : G.toSimple.edgeSet.encard = (G.E : ℕ∞) := by
    rw [← SimpleGraph.coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard]
    rfl
  rw [he] at h
  simpa using ENat.toNat_le_toNat h (by simp)

/-- A graph with an edge is not independent as a whole. -/
@[toIsoGraph indepNum_lt_V_of_E_pos]
theorem indepNum_lt_card_of_E_pos (G : CGraph) (h : 0 < G.E) :
    G.indepNum < FinEnum.card G.V := by
  classical
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos h
  obtain ⟨s, hs⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcards : s.card = G.indepNum := hs.card_eq
  have hle : G.indepNum ≤ FinEnum.card G.V := by
    rw [← hcards, ← FinEnum.card_univ]
    exact Finset.card_le_univ s
  rcases Nat.lt_or_ge G.indepNum (FinEnum.card G.V) with h' | h'
  · exact h'
  · exfalso
    have huniv : s = Finset.univ :=
      Finset.eq_univ_of_card s (by rw [hcards, ← FinEnum.card_eq_fintypeCard']; omega)
    have hmem : ∀ x : G.V, x ∈ (s : Set G.V) := by
      intro x
      rw [huniv]
      simp
    exact hs.isIndepSet (hmem a) (hmem b) ((toSimple_adj _ _ _).2 hab).ne
      ((toSimple_adj _ _ _).2 hab)

end

section
variable {G H : CGraph}
variable {G : CGraph}

/-- The automorphism group of `G`, as a `Finset` of permutations of the vertex type.  Working
with permutations rather than with `G ≃cg G` keeps everything inside `Fintype` land. -/
private def autFinset (G : CGraph) : Finset (Equiv.Perm G.V) :=
  Finset.univ.filter fun σ ↦ ∀ x y, G.Adj (σ x) (σ y) = G.Adj x y

private theorem mem_autFinset {σ : Equiv.Perm G.V} :
    σ ∈ autFinset G ↔ ∀ x y, G.Adj (σ x) (σ y) = G.Adj x y := by
  simp [autFinset]

private theorem one_mem_autFinset : (1 : Equiv.Perm G.V) ∈ autFinset G := by
  rw [mem_autFinset]; intro x y; rfl

private theorem mul_mem_autFinset {σ τ : Equiv.Perm G.V} (hσ : σ ∈ autFinset G)
    (hτ : τ ∈ autFinset G) : σ * τ ∈ autFinset G := by
  rw [mem_autFinset] at hσ hτ ⊢
  intro x y
  simp only [Equiv.Perm.mul_apply]
  rw [hσ, hτ]

private theorem inv_mem_autFinset {σ : Equiv.Perm G.V} (hσ : σ ∈ autFinset G) :
    σ⁻¹ ∈ autFinset G := by
  rw [mem_autFinset] at hσ ⊢
  intro x y
  have h := hσ (σ⁻¹ x) (σ⁻¹ y)
  simpa using h.symm

private theorem mem_autFinset_of_iso (σ : G ≃cg G) : σ.toEquiv ∈ autFinset G := by
  rw [mem_autFinset]
  intro x y
  exact σ.adj_eq x y

/-- All fibres of the map `σ ↦ σ c` have the same size, for a vertex-transitive graph: the
fibre over `(c, v)` is carried onto the fibre over `(c', v')` by `σ ↦ β σ α` for automorphisms
`α : c' ↦ c` and `β : v ↦ v'`. -/
private theorem card_autFinset_filter_eq (hvt : G.IsVertexTransitive) (c v c' v' : G.V) :
    ((autFinset G).filter fun σ ↦ σ c = v).card
      = ((autFinset G).filter fun σ ↦ σ c' = v').card := by
  obtain ⟨a, ha⟩ := hvt c' c
  obtain ⟨b, hb⟩ := hvt v v'
  set α : Equiv.Perm G.V := a.toEquiv with hα
  set β : Equiv.Perm G.V := b.toEquiv with hβ
  have hαmem : α ∈ autFinset G := mem_autFinset_of_iso a
  have hβmem : β ∈ autFinset G := mem_autFinset_of_iso b
  have hac : α c' = c := ha
  have hbv : β v = v' := hb
  refine Finset.card_nbij' (fun σ ↦ β * σ * α) (fun τ ↦ β⁻¹ * τ * α⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hσ ⊢
    refine ⟨mul_mem_autFinset (mul_mem_autFinset hβmem hσ.1) hαmem, ?_⟩
    simp only [Equiv.Perm.mul_apply, hac, hσ.2, hbv]
  · intro τ hτ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hτ ⊢
    refine ⟨mul_mem_autFinset (mul_mem_autFinset (inv_mem_autFinset hβmem) hτ.1)
      (inv_mem_autFinset hαmem), ?_⟩
    have hc : α⁻¹ c = c' := by rw [← hac]; simp
    have hv : β⁻¹ v' = v := by rw [← hbv]; simp
    simp only [Equiv.Perm.mul_apply, hc, hτ.2, hv]
  · intro σ _
    group
  · intro τ _
    group

end

section
variable {G H : CGraph}

/-! ### The clique–coclique bound -/

/-- **The clique–coclique bound**: in a vertex-transitive graph, `α · ω ≤ |V|`.

The proof is a double count of the pairs `(σ, c)` with `σ` an automorphism, `c` a vertex of a
fixed maximum clique `C`, and `σ c` in a fixed maximum independent set `S`.  For each `σ` there
is at most one such `c`, since `σ C` is a clique and `S` is independent; on the other hand each
of the `|C| · |S|` pairs `(c, v)` is realised by exactly `|Aut G| / |V|` automorphisms, because
the action is transitive. -/
@[toIsoGraph indepNum_mul_cliqueNum_le_V]
theorem indepNum_mul_cliqueNum_le_card (G : CGraph) (hvt : G.IsVertexTransitive) :
    G.indepNum * G.cliqueNum ≤ FinEnum.card G.V := by
  classical
  obtain ⟨S, hS, hScard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  obtain ⟨C, hC, hCcard⟩ := G.toSimple.exists_isNClique_cliqueNum
  rcases Finset.eq_empty_or_nonempty C with rfl | ⟨c₀, hc₀⟩
  · rw [Finset.card_empty] at hCcard
    have hz : G.cliqueNum = 0 := hCcard.symm
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
  set Γ : Finset (Equiv.Perm G.V) := autFinset G with hΓ
  set m : ℕ := (Γ.filter fun σ ↦ σ c₀ = c₀).card with hm
  -- every fibre has size `m`
  have hfib : ∀ c v : G.V, (Γ.filter fun σ ↦ σ c = v).card = m := fun c v ↦
    card_autFinset_filter_eq hvt c v c₀ c₀
  -- the fibres over a fixed `c` partition the automorphism group
  have hcard : Γ.card = FinEnum.card G.V * m := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := fun σ : Equiv.Perm G.V ↦ σ c₀) (s := Γ) (t := Finset.univ)
      (fun x _ ↦ by simp)
    rw [this]
    rw [Finset.sum_congr rfl fun v _ ↦ hfib c₀ v, Finset.sum_const, FinEnum.card_univ,
      smul_eq_mul]
  -- the double count
  set N : ℕ := ∑ σ ∈ Γ, (C.filter fun c ↦ σ c ∈ S).card with hN
  have hupper : N ≤ Γ.card := by
    have hone : ∀ σ ∈ Γ, (C.filter fun c ↦ σ c ∈ S).card ≤ 1 := by
      intro σ hσ
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hne
      have hadj : G.toSimple.Adj x y := hC hx.1 hy.1 hne
      have hadj' : G.toSimple.Adj (σ x) (σ y) := by
        rw [toSimple_adj] at hadj ⊢
        rw [(mem_autFinset.1 hσ) x y]
        exact hadj
      exact hS hx.2 hy.2 (fun h ↦ hne (σ.injective h)) hadj'
    calc N ≤ Γ.card • 1 := Finset.sum_le_card_nsmul _ _ 1 hone
      _ = Γ.card := by simp
  have hlower : N = C.card * (S.card * m) := by
    have h1 : N = ∑ c ∈ C, (Γ.filter fun σ ↦ σ c ∈ S).card := by
      simp only [hN, Finset.card_filter]
      exact Finset.sum_comm
    have h2 : ∀ c : G.V, (Γ.filter fun σ ↦ σ c ∈ S).card = S.card * m := by
      intro c
      have h3 := Finset.card_eq_sum_card_fiberwise
        (f := fun σ : Equiv.Perm G.V ↦ σ c) (s := Γ.filter fun σ ↦ σ c ∈ S) (t := S)
        (fun x hx ↦ (Finset.mem_filter.1 hx).2)
      rw [h3]
      have h4 : ∀ v ∈ S, ((Γ.filter fun σ ↦ σ c ∈ S).filter fun σ ↦ σ c = v).card = m := by
        intro v hv
        rw [Finset.filter_filter]
        rw [Finset.filter_congr (q := fun σ ↦ σ c = v) fun σ _ ↦
          ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hv, h⟩⟩]
        exact hfib c v
      rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul]
    rw [h1, Finset.sum_congr rfl fun c _ ↦ h2 c, Finset.sum_const, smul_eq_mul]
  -- put the two halves together and cancel the common factor `m`
  have hmpos : 0 < m := by
    rw [hm]
    refine Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨one_mem_autFinset, rfl⟩⟩
  have hfinal : S.card * C.card * m ≤ FinEnum.card G.V * m := by
    calc S.card * C.card * m = C.card * (S.card * m) := by ring
      _ = N := hlower.symm
      _ ≤ Γ.card := hupper
      _ = FinEnum.card G.V * m := hcard
  have := Nat.le_of_mul_le_mul_right hfinal hmpos
  rwa [hScard, hCcard] at this

/-! ### The domination number -/

theorem domNum_le_card_of_isDominatingSet {s : Finset G.V} (h : G.IsDominatingSet s) :
    G.domNum ≤ s.card :=
  Nat.sInf_le ⟨s, rfl, h⟩

/-- A dominating set of the minimum size `γ`. -/
theorem exists_isDominatingSet_domNum (G : CGraph) :
    ∃ s : Finset G.V, s.card = G.domNum ∧ G.IsDominatingSet s := by
  have hne : {n | ∃ s : Finset G.V, s.card = n ∧ G.IsDominatingSet s}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, rfl, isDominatingSet_univ G⟩
  obtain ⟨s, hcard, hs⟩ := Nat.sInf_mem hne
  exact ⟨s, hcard, hs⟩

@[toIsoGraph domNum_le_V]
theorem domNum_le_card (G : CGraph) : G.domNum ≤ FinEnum.card G.V := by
  have := domNum_le_card_of_isDominatingSet (isDominatingSet_univ G)
  rwa [FinEnum.card_univ] at this

@[simp, toIsoGraph]
theorem domNum_eq_zero_iff (G : CGraph) :
    G.domNum = 0 ↔ FinEnum.card G.V = 0 := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
    rw [h, Finset.card_eq_zero] at hcard
    subst hcard
    rw [FinEnum.card_eq_zero_iff]
    refine ⟨fun v ↦ ?_⟩
    rcases hs v with hv | ⟨u, hu, -⟩
    · simp at hv
    · simp at hu
  · intro h
    have := G.domNum_le_card
    omega

@[toIsoGraph]
theorem domNum_pos (G : CGraph) (h : 0 < FinEnum.card G.V) : 0 < G.domNum := by
  have := (G.domNum_eq_zero_iff).not.2 (by omega : ¬ FinEnum.card G.V = 0)
  omega

/-- A vertex adjacent to everything else dominates on its own. -/
theorem domNum_eq_one_of_universal {v : G.V} (h : ∀ u, u ≠ v → G.Adj v u) : G.domNum = 1 := by
  have hdom : G.IsDominatingSet {v} := by
    intro u
    by_cases huv : u = v
    · exact Or.inl (by simp [huv])
    · exact Or.inr ⟨v, by simp, h u huv⟩
  have h1 := domNum_le_card_of_isDominatingSet hdom
  rw [Finset.card_singleton] at h1
  have h2 : 0 < FinEnum.card G.V := FinEnum.card_pos_iff.2 ⟨v⟩
  have := G.domNum_pos h2
  omega

/-- **The degree bound** `|V| ≤ γ·(Δ + 1)`: each vertex of a dominating set covers itself and at
most `Δ` neighbours. -/
@[toIsoGraph V_le_domNum_mul_maxDeg_add_one]
theorem card_le_domNum_mul_maxDeg_add_one (G : CGraph) :
    FinEnum.card G.V ≤ G.domNum * (G.maxDeg + 1) := by
  classical
  obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
  have hsub : (Finset.univ : Finset G.V)
      ⊆ s.biUnion fun u ↦ insert u (G.toSimple.neighborFinset u) := by
    intro v _
    rcases hs v with hv | ⟨u, hu, hadj⟩
    · exact Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_insert_self _ _⟩
    · refine Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_insert_of_mem ?_⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact (toSimple_adj _ _ _).2 hadj
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := s)
    (t := fun u ↦ insert u (G.toSimple.neighborFinset u))
  have h3 : ∀ u ∈ s, (insert u (G.toSimple.neighborFinset u)).card ≤ G.maxDeg + 1 := by
    intro u _
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := G.degree_le_maxDeg u
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have h4 := Finset.sum_le_card_nsmul _ _ _ h3
  rw [FinEnum.card_univ] at h1
  rw [smul_eq_mul, hcard] at h4
  omega

/-- **`γ ≤ α`**: a *maximum* independent set is dominating, since a vertex it failed to dominate
could be added to it. -/
@[toIsoGraph]
theorem domNum_le_indepNum (G : CGraph) : G.domNum ≤ G.indepNum := by
  classical
  obtain ⟨S, hS, hScard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hdom : G.IsDominatingSet S := by
    intro v
    by_contra hcon
    push_neg at hcon
    obtain ⟨hv, hne⟩ := hcon
    have hnadj : ∀ u ∈ S, ¬ G.toSimple.Adj u v := by
      intro u hu hadj
      exact hne u hu ((toSimple_adj _ _ _).1 hadj)
    have hins : G.toSimple.IsIndepSet (insert v (S : Set G.V)) := by
      refine (Set.pairwise_insert_of_symmetric ?_).2 ⟨hS, ?_⟩
      · intro a b hab h
        exact hab h.symm
      · intro b hb _
        exact fun h ↦ hnadj b hb h.symm
    rw [← Finset.coe_insert] at hins
    have hcard := hins.card_le_indepNum
    rw [Finset.card_insert_of_notMem hv, hScard] at hcard
    omega
  have h := domNum_le_card_of_isDominatingSet hdom
  rw [hScard] at h
  exact h

/-- **`γ + Δ ≤ |V|`**: the complement of the neighbourhood of a vertex of maximum degree is
dominating. -/
@[toIsoGraph domNum_add_maxDeg_le_V]
theorem domNum_add_maxDeg_le_card (G : CGraph) : G.domNum + G.maxDeg ≤ FinEnum.card G.V := by
  classical
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : FinEnum.card G.V = 0 := FinEnum.card_eq_zero_iff.2 hemp
    have h2 := G.domNum_le_card
    have h3 : G.maxDeg = 0 := by rw [maxDeg, SimpleGraph.maxDegree_of_isEmpty]
    omega
  obtain ⟨v₀⟩ := hne
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  set T : Finset G.V := Finset.univ \ G.toSimple.neighborFinset v with hT
  have hdom : G.IsDominatingSet T := by
    intro u
    by_cases hu : u ∈ T
    · exact Or.inl hu
    · refine Or.inr ⟨v, ?_, ?_⟩
      · rw [hT, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, by simp⟩
      · rw [hT, Finset.mem_sdiff] at hu
        push_neg at hu
        have := hu (Finset.mem_univ u)
        rw [SimpleGraph.mem_neighborFinset] at this
        exact (toSimple_adj _ _ _).2 (by simpa using this)
  have hcardT : T.card = FinEnum.card G.V - G.maxDeg := by
    rw [hT, Finset.card_univ_diff, SimpleGraph.card_neighborFinset_eq_degree, hv,
      ← FinEnum.card_eq_fintypeCard']
  have h1 := domNum_le_card_of_isDominatingSet hdom
  have h2 : G.maxDeg < FinEnum.card G.V := @maxDeg_lt_card G ⟨v₀⟩
  omega

/-- **`γ ≤ τ`** for a graph with no isolated vertex: a vertex cover dominates, since every vertex
has an edge and the far end of it is in the cover. -/
@[toIsoGraph]
theorem domNum_le_coverNum (G : CGraph) (h : 1 ≤ G.minDeg) : G.domNum ≤ G.coverNum := by
  classical
  obtain ⟨C, hC, hCcard⟩ := exists_cover_finset G.toSimple
  have hdom : G.IsDominatingSet C := by
    intro v
    by_cases hv : v ∈ C
    · exact Or.inl hv
    · have hdeg : 1 ≤ G.toSimple.degree v := le_trans h (G.minDeg_le_degree v)
      have hne : (G.toSimple.neighborFinset v).Nonempty := by
        rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
        omega
      obtain ⟨u, hu⟩ := hne
      rw [SimpleGraph.mem_neighborFinset] at hu
      rcases hC hu with hmem | hmem
      · exact absurd hmem hv
      · exact Or.inr ⟨u, hmem, (toSimple_adj _ _ _).2 hu.symm⟩
  have := domNum_le_card_of_isDominatingSet hdom
  rw [hCcard] at this
  exact this

/-! ### The domination number of the small families -/

@[toIsoGraph]
theorem domNum_empty (n : ℕ) : (empty n).domNum = n := by
  refine le_antisymm ?_ ?_
  · have := (empty n).domNum_le_card
    rwa [card_empty] at this
  · obtain ⟨s, hcard, hs⟩ := (empty n).exists_isDominatingSet_domNum
    have huniv : s = Finset.univ := by
      refine Finset.eq_univ_iff_forall.2 fun v ↦ ?_
      rcases hs v with hv | ⟨u, -, hadj⟩
      · exact hv
      · simp at hadj
    rw [huniv, FinEnum.card_univ, card_empty] at hcard
    omega

@[toIsoGraph]
theorem domNum_complete (n : ℕ) : (complete (n + 1)).domNum = 1 :=
  domNum_eq_one_of_universal (v := (0 : Fin (n + 1))) fun u hu ↦ by
    simpa using Ne.symm hu

/-- A graph is dominated by a single vertex exactly when it has a universal vertex. -/
theorem domNum_eq_one_iff (G : CGraph) :
    G.domNum = 1 ↔ ∃ v : G.V, ∀ u, u ≠ v → G.Adj v u := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
    rw [h, Finset.card_eq_one] at hcard
    obtain ⟨v, rfl⟩ := hcard
    refine ⟨v, fun u hu ↦ ?_⟩
    rcases hs u with hmem | ⟨w, hw, hadj⟩
    · exact absurd (Finset.mem_singleton.1 hmem) hu
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact hadj
  · rintro ⟨v, hv⟩
    exact domNum_eq_one_of_universal hv

/-- The apex of a join with a single vertex sees the whole graph, so it dominates it. -/
theorem domNum_join_complete_one (G : CGraph) :
    (complete 1 ∇g G).domNum = 1 := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  haveI : Subsingleton ((complete 1)ᶜ).V := inferInstanceAs (Subsingleton (Fin 1))
  refine domNum_eq_one_of_universal
    (v := (Sum.inl (0 : Fin 1) : (complete 1 ∇g G).V)) fun u hu ↦ ?_
  rcases u with a | b
  · exact absurd (congrArg Sum.inl (Subsingleton.elim a (0 : Fin 1))) hu
  · exact join_adj_inl_inr (complete 1) G _ b

/-! ### The clique number of the Mycielskian -/

/-- The Mycielskian creates no new cliques: apart from the edges at the apex, every clique is a
clique of `G` in disguise. -/
@[toIsoGraph]
theorem cliqueNum_mycielskian (G : CGraph) [Nonempty G.V] :
    (mycielskian G).cliqueNum = max G.cliqueNum 2 := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  apply le_antisymm
  · obtain ⟨t, ht, hcard⟩ := (mycielskian G).toSimple.exists_isNClique_cliqueNum
    show (mycielskian G).toSimple.cliqueNum ≤ _
    rw [← hcard]
    by_cases hnone : (none : (mycielskian G).V) ∈ t
    · -- the apex is adjacent only to the copies, which are pairwise non-adjacent
      refine le_trans ?_ (le_max_right _ _)
      by_contra hc
      push_neg at hc
      have hcard' : 1 < (t.erase none).card := by
        rw [Finset.card_erase_of_mem hnone]
        omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard'
      have hinr : ∀ z ∈ t.erase none, ∃ b, z = some (.inr b) := by
        intro z hz
        have hzn : z ≠ none := Finset.ne_of_mem_erase hz
        have hadj := ht (by simpa using hnone) (by simpa using Finset.mem_of_mem_erase hz)
          (Ne.symm hzn)
        match z, hzn with
        | some (.inl b), _ => simp [CGraph.toSimple_adj] at hadj
        | some (.inr b), _ => exact ⟨b, rfl⟩
      obtain ⟨b, rfl⟩ := hinr x hx
      obtain ⟨c, rfl⟩ := hinr y hy
      have := ht (by simpa using Finset.mem_of_mem_erase hx)
        (by simpa using Finset.mem_of_mem_erase hy) hxy
      simp [CGraph.toSimple_adj] at this
    · -- no apex: forgetting which copy a vertex is in gives a clique of `G` of the same size
      refine le_trans ?_ (le_max_left _ _)
      set f : (mycielskian G).V → G.V := fun x ↦ x.elim a₀ (Sum.elim id id) with hf
      have hadj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → G.Adj (f x) (f y) = true := by
        intro x hx y hy hxy
        have h := ht (by simpa using hx) (by simpa using hy) hxy
        match x, (by rintro rfl; exact hnone hx : x ≠ none),
            y, (by rintro rfl; exact hnone hy : y ≠ none) with
        | some (.inl b), _, some (.inl c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inl b), _, some (.inr c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inr b), _, some (.inl c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inr b), _, some (.inr c), _ => simp [CGraph.toSimple_adj] at h
      have hinj : Set.InjOn f t := by
        intro x hx y hy hfxy
        by_contra hxy
        have := hadj x hx y hy hxy
        rw [hfxy] at this
        exact absurd this (by simp [G.loopless])
      have hclique : G.toSimple.IsClique ((t.image f : Finset G.V) : Set G.V) := by
        intro u hu v hv huv
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨y, hy, rfl⟩ := hv
        rw [CGraph.toSimple_adj]
        exact hadj x hx y hy fun h ↦ huv (by rw [h])
      calc t.card = (t.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ G.cliqueNum := hclique.card_le_cliqueNum
  · refine max_le ?_ ?_
    · -- `G` embeds as the `inl` copy
      obtain ⟨t, ht, hcard⟩ := G.toSimple.exists_isNClique_cliqueNum
      have hemb : Function.Injective (fun a : G.V ↦ (some (.inl a) : (mycielskian G).V)) := by
        intro a b h
        simpa using h
      have hclique : (mycielskian G).toSimple.IsClique
          ((t.map ⟨_, hemb⟩ : Finset (mycielskian G).V) : Set (mycielskian G).V) := by
        intro u hu v hv huv
        simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
          Function.Embedding.coeFn_mk] at hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨y, hy, rfl⟩ := hv
        have := ht hx hy fun h ↦ huv (by rw [h])
        rw [CGraph.toSimple_adj] at this ⊢
        simpa using this
      calc G.cliqueNum = (t.map ⟨_, hemb⟩).card := by
            rw [Finset.card_map]; exact hcard.symm
        _ ≤ (mycielskian G).cliqueNum := hclique.card_le_cliqueNum
    · -- the apex together with any copy is an edge
      have hclique : (mycielskian G).toSimple.IsClique
          (({none, some (.inr a₀)} : Finset (mycielskian G).V) :
            Set (mycielskian G).V) := by
        intro u hu v hv huv
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
          simp_all [CGraph.toSimple_adj]
      have hcard : ({none, some (.inr a₀)} : Finset (mycielskian G).V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
      calc (2 : ℕ) = ({none, some (.inr a₀)} : Finset (mycielskian G).V).card := hcard.symm
        _ ≤ (mycielskian G).cliqueNum := hclique.card_le_cliqueNum

/-- Mycielski's construction preserves triangle-freeness. -/
@[toIsoGraph]
theorem cliqueNum_mycielskian_eq_two (G : CGraph) [Nonempty G.V]
    (h : G.cliqueNum ≤ 2) : (mycielskian G).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian]
  omega

/-- **Domination is additive over components**: the two sides of a disjoint union have to be
dominated separately, and any two dominating sets can be put side by side. -/
@[toIsoGraph]
theorem domNum_disjUnion (G H : CGraph) :
    (G ⊕g H).domNum = G.domNum + H.domNum := by
  apply le_antisymm
  · obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
    obtain ⟨t, ht, htdom⟩ := H.exists_isDominatingSet_domNum
    have h := domNum_le_card_of_isDominatingSet (isDominatingSet_disjSum hsdom htdom)
    rwa [Finset.card_disjSum, hs, ht] at h
  · obtain ⟨u, hu, hudom⟩ := (G ⊕g H).exists_isDominatingSet_domNum
    have hG : G.IsDominatingSet u.toLeft := by
      intro v
      rcases hudom (Sum.inl v) with h | ⟨w, hw, hadj⟩
      · exact Or.inl (Finset.mem_toLeft.2 h)
      · rcases w with a | b
        · exact Or.inr ⟨a, Finset.mem_toLeft.2 hw, by simpa using hadj⟩
        · simp at hadj
    have hH : H.IsDominatingSet u.toRight := by
      intro v
      rcases hudom (Sum.inr v) with h | ⟨w, hw, hadj⟩
      · exact Or.inl (Finset.mem_toRight.2 h)
      · rcases w with a | b
        · simp at hadj
        · exact Or.inr ⟨b, Finset.mem_toRight.2 hw, by simpa using hadj⟩
    have h1 := domNum_le_card_of_isDominatingSet hG
    have h2 := domNum_le_card_of_isDominatingSet hH
    have h3 : u.toLeft.card + u.toRight.card = u.card :=
      Finset.card_toLeft_add_card_toRight
    omega

/-- One vertex from each side dominates a join. -/
@[toIsoGraph]
theorem domNum_join_le_two (G H : CGraph)
    [Nonempty G.V] [Nonempty H.V] : (G ∇g H).domNum ≤ 2 := by
  obtain ⟨a⟩ := ‹Nonempty G.V›
  obtain ⟨b⟩ := ‹Nonempty H.V›
  have hdom : (G ∇g H).IsDominatingSet {Sum.inl a, Sum.inr b} := by
    intro v
    rcases v with x | y
    · by_cases h : x = a
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨Sum.inr b, by simp, join_adj_inr_inl G H b x⟩
    · by_cases h : y = b
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨Sum.inl a, by simp, join_adj_inl_inr G H a y⟩
  have h := domNum_le_card_of_isDominatingSet hdom
  have hcard : ({Sum.inl a, Sum.inr b} : Finset (G ∇g H).V).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  omega

/-- A single vertex dominates a join exactly when it is universal on its own side: the other side
is seen for free. -/
theorem domNum_join_eq_one_iff (G H : CGraph) :
    (G ∇g H).domNum = 1 ↔ G.domNum = 1 ∨ H.domNum = 1 := by
  rw [domNum_eq_one_iff, domNum_eq_one_iff, domNum_eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    rcases v with a | b
    · refine Or.inl ⟨a, fun u hu ↦ ?_⟩
      have := hv (Sum.inl u) fun h ↦ hu (Sum.inl_injective h)
      simpa using this
    · refine Or.inr ⟨b, fun u hu ↦ ?_⟩
      have := hv (Sum.inr u) fun h ↦ hu (Sum.inr_injective h)
      simpa using this
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Sum.inl a, fun u hu ↦ ?_⟩
      rcases u with c | d
      · rw [join_adj_inl_inl]
        exact ha c fun h ↦ hu (congrArg Sum.inl h)
      · exact join_adj_inl_inr G H a d
    · refine ⟨Sum.inr b, fun u hu ↦ ?_⟩
      rcases u with c | d
      · exact join_adj_inr_inl G H b c
      · rw [join_adj_inr_inr]
        exact hb d fun h ↦ hu (congrArg Sum.inr h)

/-- Without a universal vertex on either side, a join needs exactly two dominating vertices. -/
@[toIsoGraph]
theorem domNum_join_eq_two (G H : CGraph)
    [Nonempty G.V] [Nonempty H.V] (hG : G.domNum ≠ 1) (hH : H.domNum ≠ 1) :
    (G ∇g H).domNum = 2 := by
  haveI : Nonempty (G ∇g H).V := ⟨Sum.inl (Classical.arbitrary G.V)⟩
  have h1 := domNum_join_le_two G H
  have h2 := (G ∇g H).domNum_pos (FinEnum.card_pos_iff.2 ‹Nonempty (G ∇g H).V›)
  have h3 : (G ∇g H).domNum ≠ 1 := fun h ↦ by
    rcases (domNum_join_eq_one_iff G H).1 h with h | h
    · exact hG h
    · exact hH h
  omega

/-- A dominating set of `G`, spread over every fibre, dominates `G □ H`. -/
@[toIsoGraph]
theorem domNum_cartesianProduct_le (G H : CGraph) :
    (G □g H).domNum ≤ G.domNum * FinEnum.card H.V := by
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  have hdom : (G □g H).IsDominatingSet (s ×ˢ Finset.univ) := by
    rintro ⟨x, y⟩
    rcases hsdom x with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
    · refine Or.inr ⟨(u, y), Finset.mem_product.2 ⟨hu, Finset.mem_univ _⟩, ?_⟩
      rw [cartesianProduct_adj]
      simp [hadj]
  have h := domNum_le_card_of_isDominatingSet hdom
  rwa [Finset.card_product, FinEnum.card_univ, hs] at h

/-! ### Domination in the graph products -/

/-- **Vizing's bound for the strong product**: a product of dominating sets dominates, because a
vertex of `G ⊠ H` is either equal or adjacent to a dominator in each coordinate. -/
@[toIsoGraph]
theorem domNum_strongProduct_le (G H : CGraph) :
    (G ⊠g H).domNum ≤ G.domNum * H.domNum := by
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  obtain ⟨t, ht, htdom⟩ := H.exists_isDominatingSet_domNum
  have hdom : (G ⊠g H).IsDominatingSet (s ×ˢ t) := by
    rintro ⟨x, y⟩
    have hx : ∃ u ∈ s, u = x ∨ G.Adj u x = true := by
      rcases hsdom x with h | ⟨u, hu, hadj⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨u, hu, Or.inr hadj⟩
    have hy : ∃ v ∈ t, v = y ∨ H.Adj v y = true := by
      rcases htdom y with h | ⟨v, hv, hadj⟩
      · exact ⟨y, h, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr hadj⟩
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    by_cases hpq : ((u, v) : (G ⊠g H).V) = (x, y)
    · exact Or.inl (hpq ▸ Finset.mem_product.2 ⟨hu, hv⟩)
    · refine Or.inr ⟨(u, v), Finset.mem_product.2 ⟨hu, hv⟩, ?_⟩
      rw [strongProduct_adj]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
      exact ⟨hpq, hux, hvy⟩
  have h := domNum_le_card_of_isDominatingSet hdom
  rwa [Finset.card_product, hs, ht] at h

/-- Forgetting the second coordinate turns a dominating set of `G[H]` into one of `G`. -/
@[toIsoGraph]
theorem domNum_le_domNum_lexProduct (G H : CGraph)
    [Nonempty H.V] : G.domNum ≤ (G ·g H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (G ·g H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (G ·g H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [lexProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with h1 | ⟨h1, -⟩
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- **A blow-up by a dominated graph does not change the domination number**: if some vertex of `H`
sees all of `H`, then a dominating set of `G` lifted into that vertex's fibre dominates `G[H]`. -/
@[toIsoGraph]
theorem domNum_lexProduct (G H : CGraph)
    (hH : H.domNum = 1) : (G ·g H).domNum = G.domNum := by
  obtain ⟨x, hx⟩ := (domNum_eq_one_iff H).1 hH
  haveI : Nonempty H.V := ⟨x⟩
  refine le_antisymm ?_ (domNum_le_domNum_lexProduct G H)
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  have hdom : (G ·g H).IsDominatingSet (s.image fun v ↦ (v, x)) := by
    rintro ⟨u, y⟩
    rcases hsdom u with h | ⟨v, hv, hadj⟩
    · by_cases hy : y = x
      · exact Or.inl (Finset.mem_image.2 ⟨u, h, by rw [hy]⟩)
      · refine Or.inr ⟨(u, x), Finset.mem_image.2 ⟨u, h, rfl⟩, ?_⟩
        rw [lexProduct_adj]
        simp [hx y hy]
    · refine Or.inr ⟨(v, x), Finset.mem_image.2 ⟨v, hv, rfl⟩, ?_⟩
      rw [lexProduct_adj]
      simp [hadj]
  refine le_trans (domNum_le_card_of_isDominatingSet hdom) ?_
  rw [Finset.card_image_of_injective _ fun a b hab ↦ congrArg Prod.fst hab, hs]

/-- Forgetting the second coordinate turns a dominating set of `G □ H` into one of `G`. -/
@[toIsoGraph]
theorem domNum_le_domNum_cartesianProduct (G H : CGraph)
    [Nonempty H.V] : G.domNum ≤ (G □g H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (G □g H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (G □g H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [cartesianProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- Forgetting the second coordinate turns a dominating set of `G ⊠ H` into one of `G`. -/
@[toIsoGraph]
theorem domNum_le_domNum_strongProduct (G H : CGraph)
    [Nonempty H.V] : G.domNum ≤ (G ⊠g H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (G ⊠g H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (G ⊠g H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [strongProduct_adj] at hadj
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hadj
      rcases hadj.2.1 with h1 | h1
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- **A product of independent sets is independent in the strong product**, so
`α(G) · α(H) ≤ α(G ⊠ H)`.  This is the inequality behind the Shannon capacity of a graph. -/
@[toIsoGraph]
theorem indepNum_mul_indepNum_le_indepNum_strongProduct (G H : CGraph)
 :
    G.indepNum * H.indepNum ≤ (G ⊠g H).indepNum := by
  have h := indepNum_anti (strongProduct_le_lexProduct G H)
  rwa [show (G ·g H).toSimple.indepNum = G.indepNum * H.indepNum from
    indepNum_lexProduct G H] at h

/-- The same product set is independent in the (sparser) cartesian product. -/
@[toIsoGraph]
theorem indepNum_mul_indepNum_le_indepNum_cartesianProduct (G H : CGraph)
 :
    G.indepNum * H.indepNum ≤ (G □g H).indepNum :=
  le_trans (indepNum_mul_indepNum_le_indepNum_strongProduct G H)
    (indepNum_anti (cartesianProduct_le_strongProduct G H))

/-- In the tensor product a whole slab `S ×ˢ univ` over an independent set `S` is independent,
because every tensor edge moves in *both* coordinates: `α(G) · |V(H)| ≤ α(G × H)`. -/
@[toIsoGraph indepNum_mul_V_le_indepNum_tensorProduct]
theorem indepNum_mul_card_le_indepNum_tensorProduct (G H : CGraph)
 :
    G.indepNum * FinEnum.card H.V ≤ (G ⊗g H).indepNum := by
  classical
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hind : (G ⊗g H).toSimple.IsIndepSet
      ((s ×ˢ (Finset.univ : Finset H.V) : Finset (G.V × H.V)) : Set (G.V × H.V)) := by
    intro p hp q hq hpq hadj
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    rw [CGraph.toSimple_adj, tensorProduct_adj, Bool.and_eq_true] at hadj
    have hne : p.1 ≠ q.1 := fun h ↦ G.loopless q.1 (h ▸ hadj.1)
    exact hs hp.1 hq.1 hne hadj.1
  calc G.indepNum * FinEnum.card H.V
      = (s ×ˢ (Finset.univ : Finset H.V)).card := by
        rw [Finset.card_product, hcard, FinEnum.card_univ]
        rfl
    _ ≤ _ := hind.card_le_indepNum

/-- Fibrewise counting: an independent set of `G □ H` meets each fibre `{a} × V(H)` in an
independent set of `H`, so `α(G □ H) ≤ |V(G)| · α(H)`. -/
@[toIsoGraph]
theorem indepNum_cartesianProduct_le (G H : CGraph) :
    (G □g H).indepNum ≤ FinEnum.card G.V * H.indepNum := by
  classical
  obtain ⟨s, hs, hcard⟩ := (G □g H).toSimple.exists_isNIndepSet_indepNum
  have hfib : ∀ a : G.V, (s.filter fun p ↦ p.1 = a).card ≤ H.indepNum := by
    intro a
    have hindH : H.toSimple.IsIndepSet
        (((s.filter fun p ↦ p.1 = a).image Prod.snd : Finset H.V) : Set H.V) := by
      intro y hy z hz hyz hadj
      rw [Finset.mem_coe, Finset.mem_image] at hy hz
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨q, hq, rfl⟩ := hz
      rw [Finset.mem_filter] at hp hq
      refine hs hp.1 hq.1 (fun h ↦ hyz (congrArg Prod.snd h)) ?_
      rw [CGraph.toSimple_adj, cartesianProduct_adj]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨hp.2.trans hq.2.symm, hadj⟩
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd
      (fun p hp ↦ Finset.mem_image_of_mem _ hp) ?_) hindH.card_le_indepNum
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) hpq
  have hsum : s.card = ∑ a : G.V, (s.filter fun p ↦ p.1 = a).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ ↦ Finset.mem_univ p.1
  calc (G □g H).indepNum = s.card := hcard.symm
    _ = ∑ a : G.V, (s.filter fun p ↦ p.1 = a).card := hsum
    _ ≤ ∑ _a : G.V, H.indepNum := Finset.sum_le_sum fun a _ ↦ hfib a
    _ = FinEnum.card G.V * H.indepNum := by
        rw [Finset.sum_const, FinEnum.card_univ, smul_eq_mul]

/-- The strong product has at least as many edges as the cartesian one, so the same bound holds. -/
@[toIsoGraph]
theorem indepNum_strongProduct_le (G H : CGraph) :
    (G ⊠g H).indepNum ≤ FinEnum.card G.V * H.indepNum :=
  le_trans (indepNum_anti (cartesianProduct_le_strongProduct G H))
    (indepNum_cartesianProduct_le G H)

/-! ### Nordhaus–Gaddum for the domination number -/

/-- **`γ(G) + γ(Gᶜ) ≤ |V| + 1`.**  Each graph satisfies `γ + Δ ≤ |V|`, and complementation turns
the maximum degree into `|V| - 1 - δ`, so the two bounds add up with `δ ≤ Δ` to spare. -/
@[toIsoGraph domNum_add_domNum_compl_le_V_add_one]
theorem domNum_add_domNum_compl_le_card_add_one (G : CGraph) :
    G.domNum + Gᶜ.domNum ≤ FinEnum.card G.V + 1 := by
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : FinEnum.card G.V = 0 := FinEnum.card_eq_zero_iff.2 hemp
    have h2 := G.domNum_le_card
    have h3 := Gᶜ.domNum_le_card
    have h4 : FinEnum.card Gᶜ.V = FinEnum.card G.V := rfl
    omega
  haveI := hne
  obtain ⟨v₀⟩ := hne
  have h1 := G.domNum_add_maxDeg_le_card
  have h2 := Gᶜ.domNum_add_maxDeg_le_card
  rw [maxDeg_compl (G := G), show FinEnum.card Gᶜ.V = FinEnum.card G.V from rfl] at h2
  have h3 := G.minDeg_le_maxDeg
  have h4 := @CGraph.maxDeg_lt_card G ⟨v₀⟩
  omega

/-- Two vertices in different components dominate the complement: whatever `x` is, it is
unreachable from one of them, hence adjacent to it in `Gᶜ`. -/
theorem domNum_compl_le_two_of_not_reachable (G : CGraph) {a b : G.V}
    (h : ¬ G.toSimple.Reachable a b) : Gᶜ.domNum ≤ 2 := by
  classical
  have hdom : Gᶜ.IsDominatingSet ({a, b} : Finset G.V) := by
    intro x
    by_cases hxa : x = a
    · exact Or.inl (by simp [hxa])
    by_cases hxb : x = b
    · exact Or.inl (by simp [hxb])
    by_cases hr : G.toSimple.Reachable a x
    · refine Or.inr ⟨b, by simp, ?_⟩
      have hbx : ¬ G.toSimple.Reachable b x := fun hbx ↦ h (hr.trans hbx.symm)
      simpa using compl_adj_of_not_reachable G hbx
    · exact Or.inr ⟨a, by simp, by simpa using compl_adj_of_not_reachable G hr⟩
  refine le_trans (domNum_le_card_of_isDominatingSet hdom) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- A disconnected graph has a complement that two vertices dominate. -/
@[toIsoGraph]
theorem domNum_compl_le_two_of_not_isConnected (G : CGraph) [Nonempty G.V]
    (h : ¬ G.IsConnected) : Gᶜ.domNum ≤ 2 := by
  rw [IsConnected, SimpleGraph.connected_iff] at h
  push_neg at h
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.toSimple.Reachable a b := by
    by_contra hc
    push_neg at hc
    exact absurd (h fun a b ↦ hc a b) (not_isEmpty_iff.2 ‹Nonempty G.V›)
  exact domNum_compl_le_two_of_not_reachable G hab

/-- A graph and its complement cannot both have a universal vertex once there are two vertices,
so `3 ≤ γ(G) + γ(Gᶜ)`. -/
@[toIsoGraph]
theorem three_le_domNum_add_domNum_compl (G : CGraph)
    (hV : 2 ≤ FinEnum.card G.V) : 3 ≤ G.domNum + Gᶜ.domNum := by
  have hG : 0 < G.domNum := G.domNum_pos (by omega)
  have hGc : 0 < Gᶜ.domNum :=
    Gᶜ.domNum_pos (by rw [show FinEnum.card Gᶜ.V = FinEnum.card G.V from rfl]; omega)
  by_contra hc
  have h1 : G.domNum = 1 := by omega
  have h2 : Gᶜ.domNum = 1 := by omega
  obtain ⟨v, hv⟩ := (domNum_eq_one_iff G).1 h1
  obtain ⟨w, hw⟩ := (domNum_eq_one_iff Gᶜ).1 h2
  by_cases hvw : w = v
  · subst hvw
    obtain ⟨u, hu⟩ : ∃ u : G.V, u ≠ w := by
      by_contra hc'
      push_neg at hc'
      have : FinEnum.card G.V ≤ 1 := by
        rw [FinEnum.card_eq_fintypeCard']
        exact Fintype.card_le_one_iff.2 fun a b ↦ (hc' a).trans (hc' b).symm
      omega
    have h3 := hv u hu
    have h4 := hw u hu
    rw [compl_adj] at h4
    simp [h3] at h4
  · have h3 := hv w hvw
    have h4 := hw v (fun h ↦ hvw h.symm)
    rw [compl_adj] at h4
    rw [G.symm v w] at h3
    simp [h3] at h4

/-! ### Nordhaus–Gaddum for the clique and independence numbers -/

/-- A single vertex is a one-element independent set. -/
theorem one_le_indepNum_of_vertex {G : CGraph} (a : G.V) : 1 ≤ G.indepNum := by
  classical
  have hind : G.toSimple.IsIndepSet ((({a} : Finset G.V)) : Set G.V) := by
    intro x hx y hy hxy
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  simpa using hind.card_le_indepNum

/-- **A nonempty graph has an independent vertex**: a single vertex is an independent set. -/
@[toIsoGraph]
theorem one_le_indepNum {G : CGraph} [Nonempty G.V] : 1 ≤ G.indepNum :=
  one_le_indepNum_of_vertex (Classical.arbitrary G.V)

/-- Two distinct non-adjacent vertices form a two-element independent set. -/
theorem two_le_indepNum {G : CGraph} {a b : G.V} (hab : a ≠ b) (h : ¬ G.Adj a b) :
    2 ≤ G.indepNum := by
  classical
  have hind : G.toSimple.IsIndepSet ((({a, b} : Finset G.V)) : Set G.V) := by
    intro x hx y hy hxy hadj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rw [toSimple_adj] at hadj
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · exact h hadj
    · exact h ((G.symm _ _).symm ▸ hadj)
    · exact hxy rfl
  have := hind.card_le_indepNum
  rwa [Finset.card_pair hab] at this

/-- **A list of pairwise non-adjacent vertices bounds the independence number below.**  The
counterpart of `le_cliqueNum_of_nodup`, and the witness direction that `graph_sat` does not do. -/
theorem le_indepNum_of_nodup {G : CGraph} {l : List G.V} (hnd : l.Nodup)
    (h : ∀ u ∈ l, ∀ v ∈ l, u ≠ v → G.Adj u v = false) : l.length ≤ G.indepNum := by
  classical
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
  have hind : G.toSimple.IsIndepSet (↑l.toFinset : Set G.V) := by
    intro u hu v hv huv hadj
    simp only [Finset.mem_coe, List.mem_toFinset] at hu hv
    rw [toSimple_adj, h u hu v hv huv] at hadj
    exact Bool.false_ne_true hadj
  show l.length ≤ G.toSimple.indepNum
  rw [← hcard]
  exact hind.card_le_indepNum

/-- **Nordhaus–Gaddum for the clique number**: `ω(G) + α(G) ≤ |V| + 1`, since `ω ≤ χ` and
`χ(G) + α(G) ≤ |V| + 1`.  Equality holds for both the complete and the edgeless graph. -/
@[toIsoGraph cliqueNum_add_indepNum_le_V_add_one]
theorem cliqueNum_add_indepNum_le_card_add_one (G : CGraph) :
    G.cliqueNum + G.indepNum ≤ FinEnum.card G.V + 1 :=
  le_trans (Nat.add_le_add_right G.cliqueNum_le_chromNum _)
    G.chromNum_add_indepNum_le_card_add_one

/-- On two or more vertices, `3 ≤ ω(G) + α(G)`: any two distinct vertices are either adjacent,
giving a two-clique, or non-adjacent, giving a two-element independent set. -/
@[toIsoGraph]
theorem three_le_cliqueNum_add_indepNum (G : CGraph) (hV : 2 ≤ FinEnum.card G.V) :
    3 ≤ G.cliqueNum + G.indepNum := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := G.V)
    (by rw [← FinEnum.card_eq_fintypeCard']; omega)
  by_cases h : G.Adj a b
  · have h1 := two_le_cliqueNum h
    have h2 := one_le_indepNum_of_vertex a
    omega
  · have h1 := one_le_cliqueNum_of_vertex a
    have h2 := two_le_indepNum hab h
    omega

/-- A matching is an independent set in the line graph, and its edges use `2ν` distinct
vertices, so `2ν ≤ n`. -/
theorem two_mul_indepNum_lineGraph_le_card (G : CGraph) :
    2 * (lineGraph G).indepNum ≤ FinEnum.card G.V := by
  classical
  obtain ⟨S, hS, hcard⟩ := (lineGraph G).toSimple.exists_isNIndepSet_indepNum
  have hb : (S.biUnion fun e ↦ e.1.toFinset).card = ∑ e ∈ S, e.1.toFinset.card := by
    refine Finset.card_biUnion fun e he f hf hef ↦ ?_
    exact disjoint_of_not_adj_lineGraph G hef (hS (by simpa using he) (by simpa using hf) hef)
  have hsum : ∑ e ∈ S, e.1.toFinset.card = 2 * S.card := by
    rw [Finset.sum_congr rfl fun e _ ↦
      Sym2.card_toFinset_of_not_isDiag e.1 (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hle : (S.biUnion fun e ↦ e.1.toFinset).card ≤ FinEnum.card G.V :=
    le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq FinEnum.card_univ)
  have hdef : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  omega

/-- **Every graph has a maximum matching whose vertices dominate all the edges**, in the counting
form `|V| ≤ α(G) + 2ν(G)`. -/
theorem card_le_indepNum_add_two_mul_indepNum_lineGraph (G : CGraph) :
    FinEnum.card G.V ≤ G.indepNum + 2 * (lineGraph G).indepNum := by
  classical
  obtain ⟨M, hM, hMcard⟩ := (lineGraph G).toSimple.exists_isNIndepSet_indepNum
  have hb : (M.biUnion fun e ↦ e.1.toFinset).card = ∑ e ∈ M, e.1.toFinset.card := by
    refine Finset.card_biUnion fun e he f hf hef ↦ ?_
    exact disjoint_of_not_adj_lineGraph G hef (hM (by simpa using he) (by simpa using hf) hef)
  have hsum : ∑ e ∈ M, e.1.toFinset.card = 2 * M.card := by
    rw [Finset.sum_congr rfl fun e _ ↦
      Sym2.card_toFinset_of_not_isDiag e.1 (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hle := (isIndepSet_sdiff_biUnion hM hMcard).card_le_indepNum
  have hsdiff : (Finset.univ \ M.biUnion fun e ↦ e.1.toFinset).card
      = FinEnum.card G.V - (M.biUnion fun e ↦ e.1.toFinset).card := by
    rw [Finset.card_sdiff, FinEnum.card_univ, Finset.inter_univ]
  have hsub : (M.biUnion fun e ↦ e.1.toFinset).card ≤ FinEnum.card G.V :=
    le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq FinEnum.card_univ)
  have hdef : G.indepNum = G.toSimple.indepNum := rfl
  have hdefL : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  omega

/-! ### Edge colourings by hand

An edge colouring is a vertex colouring of the line graph, and the translation between the two is
pure `Sym2` bookkeeping that has no business being repeated once per graph.  The next theorem does
it once: hand it a symmetric function on *ordered* pairs of vertices which separates any two edges
at a common vertex, and it produces the bound on the chromatic number of the line graph.  Values on
non-adjacent pairs are junk and are never looked at, so the colouring can be written down as a
plain formula with no side conditions. -/

/-- An explicit proper edge colouring bounds the chromatic number of the line graph, hence the
edge chromatic number.  The colouring is a symmetric function on ordered pairs; only its values
on edges matter, so its values elsewhere are unconstrained. -/
theorem chromNum_lineGraph_le_of_edgeColouring {G : CGraph} {k : ℕ}
    (c : G.V → G.V → Fin k) (hsymm : ∀ x y, c x y = c y x)
    (hproper : ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w) :
    (lineGraph G).chromNum ≤ k := by
  rw [chromNum_le_iff_colorable]
  refine ⟨SimpleGraph.Coloring.mk (fun e ↦ Sym2.lift ⟨c, hsymm⟩ e.1) ?_⟩
  intro e f hef
  have hadj : (lineGraph G).Adj e f = true := hef
  rw [lineGraph_adj] at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hadj
  obtain ⟨hne, v, hve, hvf⟩ := hadj
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hve
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.1 hvf
  have hxy : x ≠ y := fun h ↦ hne (Subtype.ext (by rw [hx, hy, h]))
  have hvx : G.Adj v x = true := by
    have h := e.2
    rw [hx, SimpleGraph.mem_edgeSet] at h
    exact h
  have hvy : G.Adj v y = true := by
    have h := f.2
    rw [hy, SimpleGraph.mem_edgeSet] at h
    exact h
  show Sym2.lift ⟨c, hsymm⟩ e.1 ≠ Sym2.lift ⟨c, hsymm⟩ f.1
  rw [hx, hy, Sym2.lift_mk, Sym2.lift_mk]
  exact hproper v x y hvx hvy hxy

theorem indepNum_mycielskian_cycle_five : (mycielskian (cycle 5)).indepNum = 5 := by
  have h := SimpleGraph.maximumIndepSet_card_eq_indepNum _ isMaximumIndepSet_grotzschShadows
  rw [show (mycielskian (cycle 5)).indepNum = (mycielskian (cycle 5)).toSimple.indepNum from rfl,
    ← h, card_grotzschShadows]

/-! ## The girth of the decorated cycles

`girth_cycle` says a cycle has no shortcut; the tadpole and the cycle-with-pendants say that
gluing a tree onto a cycle adds no cycle at all.  The two proofs share the same three pieces: a
general `girth_le_card_of_map` for the upper bound, `cycleList_two_nbrs` (each vertex of a closed
nodup chain has two distinct neighbours in it) to show every chain vertex lies on the cycle, and
`no_short_cycleList_of_labels`, which pushes such a chain into `cycle M` and appeals to
`cycle_no_short_cycleList`.
-/

/-! ## The grid and the king graph: independence, covering, domination, matching -/

/-- Two kings in the same `2 × 2` block of the board are a single move apart, so rounding both
coordinates down to the block index is injective on an independent set. -/
theorem indepNum_strongProduct_path_le (m n : ℕ) :
    (path m ⊠g path n).indepNum ≤ ((m + 1) / 2) * ((n + 1) / 2) := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (path m ⊠g path n).toSimple.exists_isNIndepSet_indepNum
  have hmaps : ∀ p ∈ s, ((p.1.1 / 2, p.2.1 / 2) : ℕ × ℕ) ∈
      (Finset.range ((m + 1) / 2)) ×ˢ (Finset.range ((n + 1) / 2)) := by
    intro p _
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hinj : ∀ p ∈ (s : Set (path m ⊠g path n).V), ∀ q ∈ (s : Set (path m ⊠g path n).V),
      ((p.1.1 / 2, p.2.1 / 2) : ℕ × ℕ) = (q.1.1 / 2, q.2.1 / 2) → p = q := by
    intro p hp q hq heq
    by_contra hpq
    have hd1 : p.1.1 / 2 = q.1.1 / 2 := congrArg Prod.fst heq
    have hd2 : p.2.1 / 2 = q.2.1 / 2 := congrArg Prod.snd heq
    refine hs hp hq hpq ?_
    rw [CGraph.toSimple_adj, strongProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
    refine ⟨hpq, ?_, ?_⟩
    · by_cases he : p.1.1 = q.1.1
      · exact Or.inl (Fin.ext he)
      · exact Or.inr ((path_adj_val m p.1 q.1).2 ⟨he, by omega⟩)
    · by_cases he : p.2.1 = q.2.1
      · exact Or.inl (Fin.ext he)
      · exact Or.inr ((path_adj_val n p.2 q.2).2 ⟨he, by omega⟩)
  calc (path m ⊠g path n).indepNum
      = s.card := hcard.symm
    _ ≤ ((Finset.range ((m + 1) / 2)) ×ˢ (Finset.range ((n + 1) / 2))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ((m + 1) / 2) * ((n + 1) / 2) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **Kings every third rank and file dominate the board.**  The king at block `(a, b)` sits on
square `(3a + 1, 3b + 1)`, pushed back to the last rank or file when that would fall off the
board, and covers the whole `3 × 3` block. -/
theorem domNum_strongProduct_path_le (m n : ℕ) :
    (path m ⊠g path n).domNum ≤ ((m + 2) / 3) * ((n + 2) / 3) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  let f : ℕ × ℕ → (path m ⊠g path n).V := fun ab ↦
    (⟨min (3 * ab.1 + 1) (m - 1), by omega⟩, ⟨min (3 * ab.2 + 1) (n - 1), by omega⟩)
  have hf1 : ∀ ab : ℕ × ℕ, (f ab).1.1 = min (3 * ab.1 + 1) (m - 1) := fun _ ↦ rfl
  have hf2 : ∀ ab : ℕ × ℕ, (f ab).2.1 = min (3 * ab.2 + 1) (n - 1) := fun _ ↦ rfl
  have hmem : ∀ v : (path m ⊠g path n).V, f (v.1.1 / 3, v.2.1 / 3) ∈
        (Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)).image f := by
    intro v
    refine Finset.mem_image_of_mem f ?_
    have h1 := v.1.isLt
    have h2 := v.2.isLt
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hdom : (path m ⊠g path n).IsDominatingSet
      ((Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)).image f) := by
    intro v
    have h1 := v.1.isLt
    have h2 := v.2.isLt
    have e1 := hf1 (v.1.1 / 3, v.2.1 / 3)
    have e2 := hf2 (v.1.1 / 3, v.2.1 / 3)
    by_cases hv : f (v.1.1 / 3, v.2.1 / 3) = v
    · exact Or.inl (hv ▸ hmem v)
    · refine Or.inr ⟨f (v.1.1 / 3, v.2.1 / 3), hmem v, ?_⟩
      rw [strongProduct_adj]
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
      exact ⟨hv, path_step_or_eq _ _ (by omega), path_step_or_eq _ _ (by omega)⟩
  simpa [Finset.card_product] using
    (domNum_le_card_of_isDominatingSet hdom).trans (Finset.card_image_le)

/-- **A king cannot cover two squares three files apart.**  The `⌈m/3⌉ · ⌈n/3⌉` squares with both
coordinates divisible by `3` have pairwise disjoint closed neighbourhoods, so every dominating set
has at least that many kings — rounding a king's coordinates to the block it covers is onto. -/
theorem le_domNum_strongProduct_path (m n : ℕ) :
    ((m + 2) / 3) * ((n + 2) / 3) ≤ (path m ⊠g path n).domNum := by
  classical
  obtain ⟨s, hcard, hs⟩ := (path m ⊠g path n).exists_isDominatingSet_domNum
  rw [← hcard]
  have hsurj : Set.SurjOn (fun p : (path m ⊠g path n).V ↦
      (((p.1.1 + 1) / 3, (p.2.1 + 1) / 3) : ℕ × ℕ)) ↑s
      ↑(Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)) := by
    rintro ⟨a, b⟩ hab
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hab
    obtain ⟨ha, hb⟩ := hab
    have ha3 : 3 * a < m := by omega
    have hb3 : 3 * b < n := by omega
    have hkey : ∀ u : (path m ⊠g path n).V,
        (u.1.1 = 3 * a ∨ u.1.1 + 1 = 3 * a ∨ 3 * a + 1 = u.1.1) →
        (u.2.1 = 3 * b ∨ u.2.1 + 1 = 3 * b ∨ 3 * b + 1 = u.2.1) →
        (((u.1.1 + 1) / 3, (u.2.1 + 1) / 3) : ℕ × ℕ) = (a, b) := by
      intro u h1 h2
      simp only [Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
    rcases hs ((⟨3 * a, ha3⟩, ⟨3 * b, hb3⟩) :
        (path m ⊠g path n).V) with hv | ⟨u, hu, hadj⟩
    · exact ⟨_, hv, hkey _ (Or.inl rfl) (Or.inl rfl)⟩
    · rw [strongProduct_adj] at hadj
      simp only [Bool.and_eq_true] at hadj
      exact ⟨u, hu, hkey u (val_step_or_eq_of_path_step hadj.2.1)
        (val_step_or_eq_of_path_step hadj.2.2)⟩
  calc ((m + 2) / 3) * ((n + 2) / 3)
      = (Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)).card := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]
    _ ≤ s.card := Finset.card_le_card_of_surjOn _ hsurj

/-- **The independence number of a grid is at most `⌈mn/2⌉`.**  The boustrophedon numbering is a
Hamiltonian path, so pairing up the squares numbered `2i` and `2i + 1` partitions the board into
`⌈mn/2⌉` edges and single squares, and an independent set meets each of them once. -/
theorem indepNum_cartesianProduct_path_le (m n : ℕ) :
    (path m □g path n).indepNum ≤ (m * n + 1) / 2 := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (path m □g path n).toSimple.exists_isNIndepSet_indepNum
  let L : (path m □g path n).V → ℕ := fun p ↦
    p.1.1 * n + (if p.1.1 % 2 = 0 then p.2.1 else n - 1 - p.2.1)
  have hLval : ∀ p : (path m □g path n).V,
      L p = p.1.1 * n + (if p.1.1 % 2 = 0 then p.2.1 else n - 1 - p.2.1) := fun _ ↦ rfl
  have hLlt : ∀ p : (path m □g path n).V, L p < m * n := by
    intro p
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    have h3 : (p.1.1 + 1) * n ≤ m * n := Nat.mul_le_mul_right n h1
    have h4 : (p.1.1 + 1) * n = p.1.1 * n + n := by ring
    have h5 : (if p.1.1 % 2 = 0 then p.2.1 else n - 1 - p.2.1) < n := by split; omega; omega
    rw [hLval]
    omega
  have hstep : ∀ p q : (path m □g path n).V, L p + 1 = L q → (path m □g path n).Adj p q = true := by
    intro p q h
    have h1 := p.2.isLt
    have h2 := q.2.isLt
    rw [hLval, hLval] at h
    rw [cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rcases snake_step h1 h2 h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact Or.inl ⟨Fin.ext hx, (path_adj_val n p.2 q.2).2 ⟨by omega, by omega⟩⟩
    · exact Or.inr ⟨(path_adj_val m p.1 q.1).2 ⟨by omega, by omega⟩, Fin.ext hy⟩
  have hmaps : ∀ p ∈ s, L p / 2 ∈ Finset.range ((m * n + 1) / 2) := by
    intro p _
    have := hLlt p
    simp only [Finset.mem_range]
    omega
  have hinj : ∀ p ∈ (s : Set (path m □g path n).V),
      ∀ q ∈ (s : Set (path m □g path n).V), L p / 2 = L q / 2 → p = q := by
    intro p hp q hq heq
    by_contra hpq
    have hne : L p ≠ L q := by
      intro he
      rw [hLval, hLval] at he
      obtain ⟨h1, h2⟩ := snake_inj p.2.isLt q.2.isLt he
      exact hpq (Prod.ext (Fin.ext h1) (Fin.ext h2))
    have hadj : (path m □g path n).Adj p q = true := by
      rcases (by omega : L p + 1 = L q ∨ L q + 1 = L p) with h | h
      · exact hstep p q h
      · rw [(path m □g path n).symm]
        exact hstep q p h
    exact hs hp hq hpq (by rw [CGraph.toSimple_adj]; exact hadj)
  calc (path m □g path n).indepNum
      = s.card := hcard.symm
    _ ≤ (Finset.range ((m * n + 1) / 2)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (m * n + 1) / 2 := Finset.card_range _

/-! ### Matchings from a list of disjoint edges -/

/-- **`k` pairwise disjoint edges give `ν ≥ k`.**  Each edge is a vertex of the line graph, and
disjointness is exactly non-adjacency there. -/
theorem le_indepNum_lineGraph_of_pairing {G : CGraph} {k : ℕ}
    (a b : Fin k → G.V) (hadj : ∀ i, G.Adj (a i) (b i) = true)
    (hdisj : ∀ i j : Fin k, i ≠ j → a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j) :
    k ≤ (lineGraph G).indepNum := by
  classical
  let E : Fin k → (lineGraph G).V := fun i ↦
    ⟨Sym2.mk (a i, b i), by rw [SimpleGraph.mem_edgeSet, toSimple_adj]; exact hadj i⟩
  have hEinj : Function.Injective E := by
    intro i j hij
    by_contra hne
    obtain ⟨h1, h2, h3, h4⟩ := hdisj i j hne
    have hval : Sym2.mk (a i, b i) = Sym2.mk (a j, b j) := congrArg Subtype.val hij
    rcases Sym2.eq_iff.1 hval with ⟨he, _⟩ | ⟨he, _⟩
    · exact h1 he
    · exact h2 he
  let S : Finset (lineGraph G).V := Finset.univ.image E
  have hScard : S.card = k := by
    rw [Finset.card_image_of_injective _ hEinj, Finset.card_fin]
  have hSindep : (lineGraph G).toSimple.IsIndepSet (S : Set (lineGraph G).V) := by
    intro e he f hf hef
    simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at he hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    have hij : i ≠ j := fun h ↦ hef (by rw [h])
    obtain ⟨h1, h2, h3, h4⟩ := hdisj i j hij
    rw [toSimple_adj, lineGraph_adj]
    simp only [E, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Sym2.mem_iff, not_and, not_exists]
    rintro - v (rfl | rfl) (h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  have := hSindep.card_le_indepNum
  rwa [hScard] at this

/-- **The boustrophedon matching of a board.**  Pairing the square numbered `2i` with the one
numbered `2i + 1` gives `⌊mn/2⌋` disjoint edges in any graph on the board that contains the grid
adjacencies. -/
theorem le_indepNum_lineGraph_board {m n : ℕ} (G : CGraph)
    (φ : (path m).V × (path n).V → G.V) (hφ : Function.Injective φ)
    (hadj : ∀ p q : (path m).V × (path n).V,
      ((p.1 = q.1 ∧ (p.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = p.2.1)) ∨ (p.2 = q.2 ∧ p.1.1 + 1 = q.1.1)) →
      G.Adj (φ p) (φ q) = true) :
    m * n / 2 ≤ (lineGraph G).indepNum := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  let P : ℕ → (path m).V × (path n).V := fun k ↦
    (⟨min (k / n) (m - 1), by omega⟩,
      ⟨if (k / n) % 2 = 0 then k % n else n - 1 - k % n,
        by have := Nat.mod_lt k hn; split; omega; omega⟩)
  have hProw : ∀ k, (P k).1.1 = min (k / n) (m - 1) := fun _ ↦ rfl
  have hPcol : ∀ k, (P k).2.1 = if (k / n) % 2 = 0 then k % n else n - 1 - k % n := fun _ ↦ rfl
  have hPval : ∀ k, k < m * n →
      (P k).1.1 * n + (if (P k).1.1 % 2 = 0 then (P k).2.1 else n - 1 - (P k).2.1) = k := by
    intro k hk
    have hdiv : k / n < m := (Nat.div_lt_iff_lt_mul hn).2 hk
    have hmod : k % n < n := Nat.mod_lt k hn
    have hrow : (P k).1.1 = k / n := by rw [hProw]; omega
    rw [hrow, hPcol]
    split_ifs with hpar
    · exact Nat.div_add_mod' k n
    · rw [show n - 1 - (n - 1 - k % n) = k % n by omega]
      exact Nat.div_add_mod' k n
  have hPinj : ∀ s t, s < m * n → t < m * n → P s = P t → s = t := by
    intro s t hs ht hst
    rw [← hPval s hs, ← hPval t ht, hst]
  have hstep : ∀ s, s + 1 < m * n → G.Adj (φ (P s)) (φ (P (s + 1))) = true := by
    intro s hs
    refine hadj _ _ ?_
    have h1 := hPval s (by omega)
    have h2 := hPval (s + 1) hs
    have hy := (P s).2.isLt
    have hy' := (P (s + 1)).2.isLt
    rcases snake_step (n := n) (x := (P s).1.1) (y := (P s).2.1) (x' := (P (s + 1)).1.1)
      (y' := (P (s + 1)).2.1) hy hy' (by omega) with ⟨hx, hcol⟩ | ⟨hcol, hx⟩
    · exact Or.inl ⟨Fin.ext hx, hcol⟩
    · exact Or.inr ⟨Fin.ext hcol, hx⟩
  have hlt : ∀ i : Fin (m * n / 2), 2 * i.1 + 1 < m * n := by
    intro i
    have := i.isLt
    omega
  refine le_indepNum_lineGraph_of_pairing (fun i ↦ φ (P (2 * i.1)))
    (fun i ↦ φ (P (2 * i.1 + 1))) (fun i ↦ hstep _ (hlt i)) ?_
  have hne : ∀ s t, s < m * n → t < m * n → s ≠ t → φ (P s) ≠ φ (P t) := by
    intro s t hs ht hst h
    exact hst (hPinj s t hs ht (hφ h))
  intro i j hij
  have hij' : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
  exact ⟨hne _ _ (by have := hlt i; omega) (by have := hlt j; omega) (by omega),
    hne _ _ (by have := hlt i; omega) (hlt j) (by omega),
    hne _ _ (hlt i) (by have := hlt j; omega) (by omega),
    hne _ _ (hlt i) (hlt j) (by omega)⟩

/-! ### The independence number of a torus with an even side -/

/-- **The checkerboard on a torus with an even side.**  Take the first even number of rows and,
in row `a`, the columns congruent to `a` mod `2`.  Two chosen squares in the same row are two
columns apart, and two in adjacent rows are in columns of opposite parity, so the set is
independent; the wrap-around is safe in the column direction because `n` is even, and in the row
direction because the last row used is `2⌊m/2⌋ - 1`, which is adjacent to row `0` only when `m`
is even, when it has the opposite parity. -/
theorem le_indepNum_cartesianProduct_cycle (m n : ℕ) (hev : n % 2 = 0) :
    n * (m / 2) ≤ (cycle m □g cycle n).indepNum := by
  classical
  let Φ : Fin (2 * (m / 2)) × Fin (n / 2) → (cycle m □g cycle n).V := fun ab ↦
    (⟨ab.1.1, by have := ab.1.isLt; omega⟩, ⟨2 * ab.2.1 + ab.1.1 % 2, by have := ab.2.isLt; omega⟩)
  have hΦ1 : ∀ ab, (Φ ab).1.1 = ab.1.1 := fun _ ↦ rfl
  have hΦ2 : ∀ ab, (Φ ab).2.1 = 2 * ab.2.1 + ab.1.1 % 2 := fun _ ↦ rfl
  have hrow : ∀ ab, (Φ ab).1.1 < m := by
    intro ab; rw [hΦ1]; have := ab.1.isLt; omega
  have hcol : ∀ ab, (Φ ab).2.1 < n := by
    intro ab; rw [hΦ2]; have := ab.2.isLt; omega
  have hinj : Function.Injective Φ := by
    intro x y h
    have h1 : (Φ x).1.1 = (Φ y).1.1 := by rw [h]
    have h2 : (Φ x).2.1 = (Φ y).2.1 := by rw [h]
    simp only [hΦ1] at h1
    simp only [hΦ2] at h2
    exact Prod.ext (Fin.ext h1) (Fin.ext (by omega))
  set S : Finset (cycle m □g cycle n).V := Finset.univ.image Φ with hS
  have hindep : (cycle m □g cycle n).toSimple.IsIndepSet
      (S : Set (cycle m □g cycle n).V) := by
    intro p hp q hq _
    simp only [hS, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hp hq
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    have hx1 := x.1.isLt
    have hx2 := x.2.isLt
    have hy1 := y.1.isLt
    have hy2 := y.2.isLt
    rw [toSimple_adj, cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and]
    refine ⟨fun heq hadj ↦ ?_, fun hadj heq ↦ ?_⟩
    · have hv := (cycle_adj_val n (Φ x).2 (Φ y).2).1 hadj
      have hr : (Φ x).1.1 = (Φ y).1.1 := by rw [heq]
      rw [mod_succ_norm (hcol x), mod_succ_norm (hcol y)] at hv
      simp only [hΦ1] at hr
      simp only [hΦ2] at hv
      rcases hv.2 with hv | hv <;> split_ifs at hv <;> omega
    · have hv := (cycle_adj_val m (Φ x).1 (Φ y).1).1 hadj
      have hc : (Φ x).2.1 = (Φ y).2.1 := by rw [heq]
      rw [mod_succ_norm (hrow x), mod_succ_norm (hrow y)] at hv
      simp only [hΦ2] at hc
      simp only [hΦ1] at hv
      rcases hv.2 with hv | hv <;> split_ifs at hv <;> omega
  have hcard : S.card = n * (m / 2) := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
    have hn2 : 2 * (n / 2) = n := by omega
    calc 2 * (m / 2) * (n / 2) = m / 2 * (2 * (n / 2)) := by ring
      _ = n * (m / 2) := by rw [hn2]; ring
  exact hcard ▸ hindep.card_le_indepNum

/-- **The chromatic index of a cartesian product is at most the sum of the two factors'.** -/
theorem chromNum_lineGraph_cartesianProduct_le {G H : CGraph}
    {k l : ℕ} (c : G.V → G.V → Fin k) (d : H.V → H.V → Fin l)
    (hc : ∀ x y, c x y = c y x) (hd : ∀ x y, d x y = d y x)
    (hcp : ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w)
    (hdp : ∀ u v w : H.V, H.Adj u v = true → H.Adj u w = true → v ≠ w → d u v ≠ d u w) :
    (lineGraph (G □g H)).chromNum ≤ k + l := by
  refine chromNum_lineGraph_le_of_edgeColouring (G := G □g H) (prodCol c d)
    (prodCol_symm hc hd) ?_
  intro u v w huv huw hvw
  rw [cartesianProduct_adj] at huv huw
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at huv huw
  unfold prodCol
  have hu1 : ∀ x : G.V × H.V, G.Adj u.1 x.1 = true → ¬ u.1 = x.1 := by
    intro x hx h
    rw [← h] at hx
    exact G.loopless u.1 hx
  rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases huw with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [if_pos h1, if_pos h3]
    have hne : v.2 ≠ w.2 := fun h ↦ hvw (Prod.ext (h1 ▸ h3) h)
    refine fun hh ↦ hdp u.2 v.2 w.2 h2 h4 hne (Fin.ext ?_)
    have hval := congrArg Fin.val hh
    simp only [Fin.natAdd] at hval
    omega
  · rw [if_pos h1, if_neg (hu1 w h3)]
    intro hh
    have hval := congrArg Fin.val hh
    simp only [Fin.natAdd, Fin.castAdd, Fin.castLE] at hval
    have := (c u.1 w.1).isLt
    omega
  · rw [if_neg (hu1 v h1), if_pos h3]
    intro hh
    have hval := congrArg Fin.val hh
    simp only [Fin.natAdd, Fin.castAdd, Fin.castLE] at hval
    have := (c u.1 v.1).isLt
    omega
  · rw [if_neg (hu1 v h1), if_neg (hu1 w h3)]
    have hne : v.1 ≠ w.1 := fun h ↦ hvw (Prod.ext h (h2 ▸ h4))
    refine fun hh ↦ hcp u.1 v.1 w.1 h1 h3 hne (Fin.ext ?_)
    have hval := congrArg Fin.val hh
    simp only [Fin.castAdd, Fin.castLE] at hval
    omega

/-- **The staircase on a torus with two odd sides.** -/
theorem le_indepNum_cartesianProduct_cycle_odd (a b : ℕ) (hab : a ≤ b) :
    (2 * b + 3) * (a + 1) ≤
      (cycle (2 * a + 3) □g cycle (2 * b + 3)).indepNum := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℕ,
      w = fun j ↦ if j ≤ a + b + 3 then j else 2 * (a + b + 3) - j := ⟨_, rfl⟩
  have hstep : ∀ j j' : ℕ, j < 2 * b + 3 → (j + 1) % (2 * b + 3) = j' →
      w j + 1 ≡ w j' [MOD 2 * a + 3] ∨ w j' + 1 ≡ w j [MOD 2 * a + 3] := by
    intro j j' hj hj'
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hlt | heq
    · have hjj : j' = j + 1 := by rw [← hj']; exact Nat.mod_eq_of_lt hlt
      subst hjj
      simp only [hw]
      split_ifs with h1 h2 h2
      · exact Or.inl (Nat.ModEq.refl _)
      · refine Or.inr ?_
        have he : 2 * (a + b + 3) - (j + 1) + 1 = j := by omega
        rw [he]
      · exact absurd h2 (by omega)
      · refine Or.inr ?_
        have he : 2 * (a + b + 3) - (j + 1) + 1 = 2 * (a + b + 3) - j := by omega
        rw [he]
    · have hj0 : j = 2 * b + 2 := by omega
      have hj'0 : j' = 0 := by rw [← hj', hj0]; simp
      subst hj0; subst hj'0
      simp only [hw]
      rcases eq_or_lt_of_le hab with rfl | hlt'
      · refine Or.inl ?_
        rw [if_pos (by omega), if_pos (by omega)]
        show (2 * a + 2 + 1) % (2 * a + 3) = 0 % (2 * a + 3)
        simp
      · refine Or.inr ?_
        rw [if_pos (by omega)]
        have he : (if 2 * b + 2 ≤ a + b + 3 then 2 * b + 2
            else 2 * (a + b + 3) - (2 * b + 2)) = 2 * a + 3 + 1 := by
          split_ifs with h <;> omega
        rw [he]
        show (0 + 1) % (2 * a + 3) = (2 * a + 3 + 1) % (2 * a + 3)
        rw [Nat.add_mod_left]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin (2 * b + 3) × Fin (a + 1) →
      (cycle (2 * a + 3) □g cycle (2 * b + 3)).V,
      Φ = fun x ↦ (⟨(w x.1.1 + 2 * x.2.1) % (2 * a + 3), Nat.mod_lt _ (by omega)⟩, x.1) :=
    ⟨_, rfl⟩
  have hΦ1 : ∀ x, (Φ x).1.1 = (w x.1.1 + 2 * x.2.1) % (2 * a + 3) := by simp [hΦ]
  have hΦ2 : ∀ x, (Φ x).2 = x.1 := by simp [hΦ]
  have hinj : Function.Injective Φ := by
    intro x y h
    have h2 : x.1 = y.1 := by rw [← hΦ2 x, ← hΦ2 y, h]
    have h1 : (Φ x).1.1 = (Φ y).1.1 := by rw [h]
    rw [hΦ1, hΦ1, h2] at h1
    have hme : w y.1.1 + 2 * x.2.1 ≡ w y.1.1 + 2 * y.2.1 [MOD 2 * a + 3] := h1
    have h3 : 2 * x.2.1 ≡ 2 * y.2.1 [MOD 2 * a + 3] := Nat.ModEq.add_left_cancel' _ hme
    have hx := x.2.isLt
    have hy := y.2.isLt
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact Prod.ext h2 (Fin.ext (by omega))
  set S : Finset (cycle (2 * a + 3) □g cycle (2 * b + 3)).V := Finset.univ.image Φ with hS
  have hindep : (cycle (2 * a + 3) □g cycle (2 * b + 3)).toSimple.IsIndepSet
      (S : Set (cycle (2 * a + 3) □g cycle (2 * b + 3)).V) := by
    intro P hP Q hQ _
    simp only [hS, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hP hQ
    obtain ⟨x, rfl⟩ := hP
    obtain ⟨y, rfl⟩ := hQ
    have hxi := x.2.isLt
    have hyi := y.2.isLt
    have hxj := x.1.isLt
    have hyj := y.1.isLt
    rw [toSimple_adj, cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and]
    refine ⟨fun heq hadj ↦ ?_, fun hadj heq ↦ ?_⟩
    · have hrow : (w x.1.1 + 2 * x.2.1) % (2 * a + 3)
          = (w y.1.1 + 2 * y.2.1) % (2 * a + 3) := by
        rw [← hΦ1, ← hΦ1, heq]
      have hv := (cycle_adj_val (2 * b + 3) (Φ x).2 (Φ y).2).1 hadj
      rw [hΦ2, hΦ2] at hv
      rcases hv.2 with hc | hc
      · rcases hstep x.1.1 y.1.1 hxj hc with h | h
        · exact staircase_clash a (w x.1.1) (w y.1.1) x.2.1 y.2.1 (by omega) (by omega) h hrow
        · exact staircase_clash a (w y.1.1) (w x.1.1) y.2.1 x.2.1 (by omega) (by omega) h
            hrow.symm
      · rcases hstep y.1.1 x.1.1 hyj hc with h | h
        · exact staircase_clash a (w y.1.1) (w x.1.1) y.2.1 x.2.1 (by omega) (by omega) h
            hrow.symm
        · exact staircase_clash a (w x.1.1) (w y.1.1) x.2.1 y.2.1 (by omega) (by omega) h hrow
    · have hcol : x.1 = y.1 := by rw [← hΦ2 x, ← hΦ2 y, heq]
      have hv := (cycle_adj_val (2 * a + 3) (Φ x).1 (Φ y).1).1 hadj
      rw [hΦ1, hΦ1, hcol] at hv
      rcases hv.2 with hr | hr
      · rw [Nat.mod_add_mod] at hr
        exact staircase_same a (w y.1.1) x.2.1 y.2.1 (by omega) (by omega) hr
      · rw [Nat.mod_add_mod] at hr
        exact staircase_same a (w y.1.1) y.2.1 x.2.1 (by omega) (by omega) hr
  have hcard : S.card = (2 * b + 3) * (a + 1) := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  exact hcard ▸ hindep.card_le_indepNum

end

end CGraph

namespace IsoGraph

/-! ### Cliques, independent sets and diameter -/

@[simp] theorem indepNum_empty (n : ℕ) : (empty n).indepNum = n := CGraph.indepNum_empty n

@[simp] theorem cliqueNum_empty (n : ℕ) : (empty n).cliqueNum = min n 1 :=
  CGraph.cliqueNum_empty n

@[simp] theorem cliqueNum_complete (n : ℕ) : (complete n).cliqueNum = n :=
  CGraph.cliqueNum_complete n

@[simp] theorem indepNum_complete (n : ℕ) : (complete n).indepNum = min n 1 :=
  CGraph.indepNum_complete n

@[simp] theorem indepNum_cycle (n : ℕ) : (cycle (n + 3)).indepNum = (n + 3) / 2 :=
  CGraph.indepNum_cycle n

@[simp] theorem indepNum_compl (G : IsoGraph) : Gᶜ.indepNum = G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, indepNum_mk, cliqueNum_mk]
  exact CGraph.indepNum_compl _

@[simp] theorem cliqueNum_compl (G : IsoGraph) : Gᶜ.cliqueNum = G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, indepNum_mk, cliqueNum_mk]
  exact CGraph.cliqueNum_compl _

@[simp] theorem indepNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).indepNum = G.indepNum + H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.indepNum_disjUnion _ _

@[simp] theorem cliqueNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.cliqueNum_disjUnion _ _

@[simp] theorem cliqueNum_join (G H : IsoGraph) :
    (G ∇g H).cliqueNum = G.cliqueNum + H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_join _ _

@[simp] theorem indepNum_join (G H : IsoGraph) :
    (G ∇g H).indepNum = max G.indepNum H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, indepNum_mk, indepNum_mk, indepNum_mk]
  exact CGraph.indepNum_join _ _

@[simp] theorem indepNum_lexProduct (G H : IsoGraph) :
    (G ·g H).indepNum = G.indepNum * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_lexProduct _ _

@[simp] theorem cliqueNum_strongProduct (G H : IsoGraph) :
    (G ⊠g H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_strongProduct _ _

/-! ### Clique numbers of the cartesian, tensor and lexicographic products -/

@[simp] theorem cliqueNum_tensorProduct (G H : IsoGraph) :
    (G ⊗g H).cliqueNum = min G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_tensorProduct _ _

@[simp] theorem cliqueNum_lexProduct (G H : IsoGraph) :
    (G ·g H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_lexProduct _ _

theorem ne_of_indepNum_ne {G H : IsoGraph} (h : G.indepNum ≠ H.indepNum) : G ≠ H :=
  ne_of_apply_ne indepNum h

theorem ne_of_cliqueNum_ne {G H : IsoGraph} (h : G.cliqueNum ≠ H.cliqueNum) : G ≠ H :=
  ne_of_apply_ne cliqueNum h

/-- Two graphs with different chromatic numbers are different graphs. -/
theorem ne_of_chromNum_ne {G H : IsoGraph} (h : G.chromNum ≠ H.chromNum) : G ≠ H :=
  ne_of_apply_ne chromNum h

/-! ### Greedy colouring -/

/-- A `k`-chromatic graph has a vertex of degree at least `k - 1`. -/
theorem chromNum_sub_one_le_maxDeg (G : IsoGraph) : G.chromNum - 1 ≤ G.maxDeg := by
  have := G.chromNum_le_maxDeg_add_one
  omega

/-- The product counterpart of the sum bound, by AM–GM: `4·χ(G)·χ(Gᶜ) ≤ (|V| + 1)²`. -/
theorem four_mul_chromNum_mul_chromNum_compl_le (G : IsoGraph) :
    4 * (G.chromNum * Gᶜ.chromNum) ≤ (G.V + 1) ^ 2 := by
  have h := G.chromNum_add_chromNum_compl_le_V_add_one
  nlinarith [sq_nonneg (G.chromNum - Gᶜ.chromNum : ℤ)]

/-! ### Ramsey numbers in general -/

/-- The diagonal case, in the crude but memorable form `4^s` — since `C(2s, s) ≤ 2^(2s)`. -/
theorem le_cliqueNum_or_le_indepNum_of_pow (G : IsoGraph) {s : ℕ} (h : 4 ^ s ≤ G.V) :
    s ≤ G.cliqueNum ∨ s ≤ G.indepNum := by
  refine G.le_cliqueNum_or_le_indepNum (le_trans ?_ h)
  calc (s + s).choose s ≤ 2 ^ (s + s) := Nat.choose_le_two_pow _ _
    _ = 4 ^ s := by rw [← two_mul, pow_mul]; norm_num

theorem coverNum_eq (G : IsoGraph) : G.coverNum = G.V - G.indepNum := by
  have := G.coverNum_add_indepNum
  omega

theorem indepNum_eq_V_sub_coverNum (G : IsoGraph) : G.indepNum = G.V - G.coverNum := by
  have := G.coverNum_add_indepNum
  omega

theorem coverNum_le_V (G : IsoGraph) : G.coverNum ≤ G.V := by
  have := G.coverNum_add_indepNum
  omega

/-- In the complement, Gallai reads `τGᶜ + ω(G) = |V|`. -/
theorem coverNum_compl_add_cliqueNum (G : IsoGraph) :
    Gᶜ.coverNum + G.cliqueNum = G.V := by
  have := Gᶜ.coverNum_add_indepNum
  rwa [indepNum_compl, V_compl] at this

/-! ### The vertex cover table -/

@[simp] theorem coverNum_empty (n : ℕ) : (empty n).coverNum = 0 := by
  rw [coverNum_eq, V_empty, indepNum_empty]
  omega

@[simp] theorem coverNum_complete (n : ℕ) : (complete n).coverNum = n - 1 := by
  rw [coverNum_eq, V_complete, indepNum_complete]
  omega

@[simp] theorem coverNum_cycle (n : ℕ) : (cycle (n + 3)).coverNum = (n + 3) - (n + 3) / 2 := by
  rw [coverNum_eq, V_cycle, indepNum_cycle]

@[simp] theorem coverNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).coverNum = G.coverNum + H.coverNum := by
  rw [coverNum_eq, coverNum_eq, coverNum_eq, V_disjUnion, indepNum_disjUnion]
  have := G.coverNum_add_indepNum
  have := H.coverNum_add_indepNum
  omega

/-- A vertex cover meets every edge, so a graph with an edge needs one, and conversely a graph
with no edges needs none. -/
theorem coverNum_pos (G : IsoGraph) (h : 0 < G.E) : 0 < G.coverNum := by
  have h1 := G.coverNum_add_indepNum
  have h2 := G.indepNum_lt_V_of_E_pos h
  omega

@[simp] theorem coverNum_eq_zero_iff (G : IsoGraph) : G.coverNum = 0 ↔ G.E = 0 := by
  constructor
  · intro h
    by_contra hcon
    exact absurd (G.coverNum_pos (by omega)) (by omega)
  · intro h
    have := G.coverNum_le_E
    omega

/-! ### Self-complementary graphs -/

/-- A self-complementary graph has as many vertices in its largest independent set as in its
largest clique. -/
theorem indepNum_eq_cliqueNum_of_compl_eq {G : IsoGraph} (h : Gᶜ = G) :
    G.indepNum = G.cliqueNum := by
  conv_lhs => rw [← h]
  rw [indepNum_compl]

/-- A self-complementary *vertex-transitive* graph has `ω² ≤ |V|`, since `α = ω` there. -/
theorem cliqueNum_sq_le_V_of_compl_eq {G : IsoGraph} (h : IsVertexTransitive G)
    (hc : Gᶜ = G) : G.cliqueNum ^ 2 ≤ G.V := by
  have hα := indepNum_eq_cliqueNum_of_compl_eq hc
  have hle := indepNum_mul_cliqueNum_le_V h
  rw [hα, ← pow_two] at hle
  exact hle

/-- A `k`-regular graph needs at least `|V|/(k + 1)` vertices to dominate it. -/
theorem le_domNum_of_regular {G : IsoGraph} {k : ℕ} (h : G.maxDeg = k) :
    G.V ≤ G.domNum * (k + 1) := by
  rw [← h]; exact G.V_le_domNum_mul_maxDeg_add_one

/-! ### The radius -/

@[simp] theorem domNum_join_eq_one_iff (G H : IsoGraph) :
    (G ∇g H).domNum = 1 ↔ G.domNum = 1 ∨ H.domNum = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, domNum_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_join_eq_one_iff _ _

/-! ### Domination in the graph products -/

/-- Two universal vertices give a universal vertex of the strong product. -/
theorem domNum_strongProduct_eq_one {G H : IsoGraph} (hG : G.domNum = 1) (hH : H.domNum = 1) :
    (G ⊠g H).domNum = 1 := by
  have hGV : 0 < G.V := by
    rcases Nat.eq_zero_or_pos G.V with h | h
    · rw [← domNum_eq_zero_iff] at h; omega
    · exact h
  have hHV : 0 < H.V := by
    rcases Nat.eq_zero_or_pos H.V with h | h
    · rw [← domNum_eq_zero_iff] at h; omega
    · exact h
  have h1 := domNum_strongProduct_le G H
  have h2 : 0 < (G ⊠g H).domNum :=
    domNum_pos (by rw [V_strongProduct]; exact Nat.mul_pos hGV hHV)
  rw [hG, hH] at h1
  omega

/-- The domination number of a strong product sits between the larger factor value and the
product of the two. -/
theorem max_domNum_le_domNum_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.domNum H.domNum ≤ (G ⊠g H).domNum := by
  refine max_le (domNum_le_domNum_strongProduct G _ hH) ?_
  rw [strongProduct_comm]
  exact domNum_le_domNum_strongProduct H _ hG

/-- The mirror bound `α(G □ H) ≤ α(G) · |V(H)|`. -/
theorem indepNum_cartesianProduct_le' (G H : IsoGraph) :
    (G □g H).indepNum ≤ G.indepNum * H.V := by
  rw [cartesianProduct_comm, mul_comm]
  exact indepNum_cartesianProduct_le H G

/-- The mirror bound `α(G ⊠ H) ≤ α(G) · |V(H)|`. -/
theorem indepNum_strongProduct_le' (G H : IsoGraph) :
    (G ⊠g H).indepNum ≤ G.indepNum * H.V := by
  rw [strongProduct_comm, mul_comm]
  exact indepNum_strongProduct_le H G

/-- Squeezing the two bounds: a product with a complete graph has independence number exactly
`α(G)`, because `α(K_n) = 1` for `n ≠ 0`. -/
theorem indepNum_cartesianProduct_complete_le (G : IsoGraph) (n : ℕ) :
    (G □g complete n).indepNum ≤ G.indepNum * n := by
  have h := indepNum_cartesianProduct_le' G (complete n)
  rwa [V_complete] at h

/-! ### Vertex covers of the products -/

/-- Gallai turns the exact independence number of a lexicographic product into an exact cover
number: `τ(G[H]) = |V(G)|·|V(H)| - α(G)·α(H)`. -/
@[simp] theorem coverNum_lexProduct (G H : IsoGraph) :
    (G ·g H).coverNum = G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_lexProduct, indepNum_lexProduct]

/-- A cover of a join must contain one whole side. -/
@[simp] theorem coverNum_join (G H : IsoGraph) :
    (G ∇g H).coverNum = min (G.coverNum + H.V) (G.V + H.coverNum) := by
  rw [coverNum_eq, V_join, indepNum_join]
  have := G.coverNum_add_indepNum
  have := H.coverNum_add_indepNum
  omega

/-- The independent set bound `α(G)·α(H) ≤ α(G □ H)` becomes an upper bound on `τ`. -/
theorem coverNum_cartesianProduct_le (G H : IsoGraph) :
    (G □g H).coverNum ≤ G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_cartesianProduct]
  exact Nat.sub_le_sub_left (indepNum_mul_indepNum_le_indepNum_cartesianProduct G H) _

/-- The same bound for the strong product. -/
theorem coverNum_strongProduct_le (G H : IsoGraph) :
    (G ⊠g H).coverNum ≤ G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_strongProduct]
  exact Nat.sub_le_sub_left (indepNum_mul_indepNum_le_indepNum_strongProduct G H) _

/-! ### Nordhaus–Gaddum for the domination number -/

/-- The two Nordhaus–Gaddum bounds together. -/
theorem domNum_add_domNum_compl_mem_Icc {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.domNum + Gᶜ.domNum ∧ G.domNum + Gᶜ.domNum ≤ G.V + 1 :=
  ⟨three_le_domNum_add_domNum_compl hV, G.domNum_add_domNum_compl_le_V_add_one⟩

/-! ### Nordhaus–Gaddum for the clique and independence numbers -/

/-- The independence numbers of a graph and its complement: `α(G) + α(Gᶜ) ≤ |V| + 1`. -/
theorem indepNum_add_indepNum_compl_le_V_add_one (G : IsoGraph) :
    G.indepNum + Gᶜ.indepNum ≤ G.V + 1 := by
  rw [indepNum_compl, Nat.add_comm]
  exact G.cliqueNum_add_indepNum_le_V_add_one

/-- The clique numbers of a graph and its complement: `ω(G) + ω(Gᶜ) ≤ |V| + 1`. -/
theorem cliqueNum_add_cliqueNum_compl_le_V_add_one (G : IsoGraph) :
    G.cliqueNum + Gᶜ.cliqueNum ≤ G.V + 1 := by
  rw [cliqueNum_compl]
  exact G.cliqueNum_add_indepNum_le_V_add_one

/-- The matching lower bound for the complement pair. -/
theorem three_le_indepNum_add_indepNum_compl {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.indepNum + Gᶜ.indepNum := by
  rw [indepNum_compl, Nat.add_comm]
  exact three_le_cliqueNum_add_indepNum hV

theorem three_le_cliqueNum_add_cliqueNum_compl {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.cliqueNum + Gᶜ.cliqueNum := by
  rw [cliqueNum_compl]
  exact three_le_cliqueNum_add_indepNum hV

/-! ### Nordhaus–Gaddum for the vertex cover number -/

/-- Colour every vertex of a minimum vertex cover with its own colour and everything else with
one shared colour: `χ(G) ≤ τ(G) + 1`. -/
theorem chromNum_le_coverNum_add_one (G : IsoGraph) : G.chromNum ≤ G.coverNum + 1 := by
  have h := G.chromNum_le_V_sub_indepNum_add_one
  rwa [← coverNum_eq] at h

/-- Since `ω ≤ χ`, a graph with a small vertex cover has small cliques too. -/
theorem cliqueNum_le_coverNum_add_one (G : IsoGraph) : G.cliqueNum ≤ G.coverNum + 1 :=
  le_trans G.cliqueNum_le_chromNum G.chromNum_le_coverNum_add_one

/-- The exact Gallai bookkeeping for a graph and its complement: the four numbers
`τ(G)`, `τGᶜ`, `α(G)` and `ω(G)` add up to `2|V|`, because `τGᶜ = |V| - ω(G)`. -/
theorem coverNum_add_coverNum_compl_add_indepNum_add_cliqueNum (G : IsoGraph) :
    G.coverNum + Gᶜ.coverNum + (G.indepNum + G.cliqueNum) = 2 * G.V := by
  have h1 := G.coverNum_add_indepNum
  have h2 := G.coverNum_compl_add_cliqueNum
  omega

/-- **Nordhaus–Gaddum, upper bound**: `τ(G) + τGᶜ ≤ 2|V| - 3` once there are two vertices,
dual to `3 ≤ α + ω`. -/
theorem coverNum_add_coverNum_compl_le {G : IsoGraph} (hV : 2 ≤ G.V) :
    G.coverNum + Gᶜ.coverNum ≤ 2 * G.V - 3 := by
  have h1 := G.coverNum_add_coverNum_compl_add_indepNum_add_cliqueNum
  have h2 := three_le_cliqueNum_add_indepNum hV
  omega

/-- Consequently `γ(G) + α(G) ≤ |V|` for a graph with no isolated vertices. -/
theorem domNum_add_indepNum_le_V {G : IsoGraph} (h : 1 ≤ G.minDeg) :
    G.domNum + G.indepNum ≤ G.V := by
  have h1 := domNum_le_coverNum h
  have h2 := G.coverNum_add_indepNum
  omega

/-- Greedy colouring of the line graph: `χ'(G) ≤ 2Δ - 1`.  Vizing's theorem improves this to
`Δ + 1`, but that is a much deeper fact. -/
theorem edgeChromNum_le_two_mul_maxDeg_sub_one (G : IsoGraph) :
    G.edgeChromNum ≤ 2 * G.maxDeg - 1 := by
  rcases Nat.eq_zero_or_pos G.maxDeg with h | h
  · have hE := G.two_mul_E_le_V_mul_maxDeg
    rw [h, Nat.mul_zero] at hE
    have h2 : chromNum (lineGraph G) ≤ (lineGraph G).V := chromNum_le_V _
    rw [V_lineGraph] at h2
    rw [edgeChromNum_eq, h]
    omega
  · have h1 := (lineGraph G).chromNum_le_maxDeg_add_one
    have h2 := G.maxDeg_lineGraph_le
    rw [edgeChromNum_eq]
    omega

@[simp] theorem edgeChromNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).edgeChromNum = max G.edgeChromNum H.edgeChromNum := by
  rw [edgeChromNum_eq, lineGraph_disjUnion, chromNum_disjUnion, edgeChromNum_eq, edgeChromNum_eq]

/-! ### The matching number

The matching number `ν(G)` is the independence number of the line graph, again by definition
(`Invariants/Derived.lean`), so `matchNum_eq` is what the bounds below rewrite with. -/

theorem matchNum_le_E (G : IsoGraph) : G.matchNum ≤ G.E := by
  have h := (lineGraph G).coverNum_add_indepNum
  rw [V_lineGraph] at h
  rw [matchNum_eq]
  omega

/-- Each of the `ν` edges of a maximum matching uses two private vertices. -/
@[toIsoGraph two_mul_matchNum_le_V]
theorem _root_.CGraph.two_mul_matchNum_le_card (G : CGraph) : 2 * G.matchNum ≤ FinEnum.card G.V :=
  CGraph.two_mul_indepNum_lineGraph_le_card G

/-- Gallai's identity in the line graph: an edge cover of `L(G)` complements a matching. -/
theorem coverNum_lineGraph_add_matchNum (G : IsoGraph) :
    coverNum (lineGraph G) + G.matchNum = G.E := by
  have h := (lineGraph G).coverNum_add_indepNum
  rw [matchNum_eq]
  rwa [V_lineGraph] at h

@[simp] theorem matchNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).matchNum = G.matchNum + H.matchNum := by
  rw [matchNum_eq, lineGraph_disjUnion, indepNum_disjUnion, matchNum_eq, matchNum_eq]

/-! ### The clique cover number

The clique cover number `θ(G)` is the chromatic number of the complement
(`Invariants/Derived.lean`), so every statement about it is a statement about `chromNum` in
disguise. -/

@[simp] theorem cliqueCoverNum_compl (G : IsoGraph) :
    Gᶜ.cliqueCoverNum = G.chromNum := by
  rw [cliqueCoverNum_eq, compl_compl]

@[simp] theorem chromNum_compl (G : IsoGraph) :
    Gᶜ.chromNum = G.cliqueCoverNum := by
  rw [cliqueCoverNum_eq]

/-- `α ≤ θ`, the complement of `ω ≤ χ`: a clique cover needs a separate clique for each vertex
of an independent set. -/
theorem indepNum_le_cliqueCoverNum (G : IsoGraph) : G.indepNum ≤ G.cliqueCoverNum := by
  rw [cliqueCoverNum_eq, ← cliqueNum_compl]
  exact cliqueNum_le_chromNum _

theorem cliqueCoverNum_le_V (G : IsoGraph) : G.cliqueCoverNum ≤ G.V := by
  have h := chromNum_le_V Gᶜ
  rw [cliqueCoverNum_eq]
  rwa [V_compl] at h

/-- `C₅` is self-complementary, so `θ(C₅) = χ(C₅) = 3` even though `ω(C₅) = 2`. -/
@[simp] theorem cliqueCoverNum_cycle_five : (cycle 5).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_eq, compl_cycle_five, show (5 : ℕ) = 2 * 1 + 3 by ring, chromNum_cycle_odd]

/-- The Nordhaus–Gaddum upper bound, in clique cover form. -/
theorem chromNum_add_cliqueCoverNum_le_V_add_one (G : IsoGraph) :
    G.chromNum + G.cliqueCoverNum ≤ G.V + 1 := by
  rw [cliqueCoverNum_eq]; exact G.chromNum_add_chromNum_compl_le_V_add_one

theorem matchNum_complete_le (n : ℕ) : (complete n).matchNum ≤ n / 2 := by
  have h := two_mul_matchNum_le_V (complete n)
  rw [V_complete] at h
  omega

/-! ### Domination, independence and regularity -/

/-- The domination number of a path is `⌈n/3⌉`. -/
@[simp] theorem domNum_path (n : ℕ) : (path (n + 1)).domNum = (n + 3) / 3 := by
  simp only [IsoGraph.path, domNum_mk, CGraph.domNum]

  apply le_antisymm
  · -- domNum ≤ (n+3)/3: construct dominating set of size (n+3)/3
    apply csInf_le
    · exact ⟨0, fun x ⟨s, _, _⟩ => Nat.zero_le _⟩
    · -- Exhibit a dominating set of size (n+3)/3
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with hk | hk | hk
      · -- n = 3*a
        obtain ⟨a, rfl⟩ : ∃ a, n = 3 * a := ⟨n / 3, by omega⟩
        let S : Finset (Fin (3 * a + 1)) :=
          Finset.image (fun i : Fin (a + 1) => ⟨3 * i.val, by omega⟩) Finset.univ
        refine ⟨S, ?_, ?_⟩
        · rw [Finset.card_image_of_injective _ fun i j h => Fin.ext
            (by have := congr_arg Fin.val h; simp at this; omega), Finset.card_fin]
          simp
        · intro v
          show v ∈ S ∨ ∃ u ∈ S, (CGraph.path (3 * a + 1)).Adj u v
          dsimp only [S]
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          set i := v.val / 3
          have hi : i < a + 1 := by omega
          have hmod_v : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
          rcases hmod_v with hm0 | hm1 | hm2
          · left
            have hvval : v.val = 3 * i := by omega
            exact ⟨⟨i, hi⟩, Fin.ext (by simp; omega)⟩
          · right
            set ui : Fin (a + 1) := ⟨i, hi⟩
            set u : Fin (3 * a + 1) := ⟨3 * ui.val, by omega⟩
            have huv_ne : u ≠ v := by
              intro h
              have := congr_arg Fin.val h
              dsimp [u, ui] at this
              omega
            have hadj : (u : ℕ) + 1 = v.val := by
              simp [u, ui]
              have := Nat.div_add_mod v.val 3
              omega
            exact ⟨u, ⟨ui, rfl⟩, by
              rw [CGraph.path_adj]
              simp [huv_ne, hadj]⟩
          · right
            have hi_lt_a : i < a := by omega
            set ui : Fin (a + 1) := ⟨i + 1, by omega⟩
            set u : Fin (3 * a + 1) := ⟨3 * ui.val, by omega⟩
            have huv_ne : u ≠ v := by
              intro h
              have := congr_arg Fin.val h
              dsimp [u, ui] at this
              omega
            have hadj : v.val + 1 = (u : ℕ) := by
              simp [u, ui]
              rw [← Nat.div_add_mod v.val 3, hm2]
              omega
            exact ⟨u, ⟨ui, rfl⟩, by
              rw [CGraph.path_adj]
              simp [huv_ne, hadj]⟩
      · -- n = 3*a + 1
        obtain ⟨a, rfl⟩ : ∃ a, n = 3 * a + 1 := ⟨n / 3, by omega⟩
        let S : Finset (Fin (3 * a + 2)) :=
          Finset.image (fun i : Fin (a + 1) => ⟨3 * i + 1, by omega⟩) Finset.univ
        refine ⟨S, ?_, ?_⟩
        · rw [Finset.card_image_of_injective _ fun i j h => Fin.ext
            (by have := congr_arg Fin.val h; simp at this; omega), Finset.card_fin]
          simp; omega
        · intro v
          show v ∈ S ∨ ∃ u ∈ S, (CGraph.path (3 * a + 2)).Adj u v
          dsimp only [S]
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          set i := v.val / 3
          have hi : i < a + 1 := by omega
          have hmod_v : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
          rcases hmod_v with hm0 | hm1 | hm2
          · right
            set ui : Fin (a + 1) := ⟨i, hi⟩
            set u : Fin (3 * a + 2) := ⟨3 * ui.val + 1, by omega⟩
            have huv_ne : u ≠ v := by
              intro h
              have := congr_arg Fin.val h
              dsimp [u, ui] at this
              omega
            have hadj : v.val + 1 = (u : ℕ) := by
              simp [u, ui]
              rw [← Nat.div_add_mod v.val 3, hm0]
              dsimp [i]
            exact ⟨u, ⟨ui, rfl⟩, by
              rw [CGraph.path_adj]
              simp [huv_ne, hadj]⟩
          · left
            have hvval : v.val = 3 * i + 1 := by omega
            exact ⟨⟨i, hi⟩, Fin.ext (by simp; omega)⟩
          · right
            set ui : Fin (a + 1) := ⟨i, hi⟩
            set u : Fin (3 * a + 2) := ⟨3 * ui.val + 1, by omega⟩
            have huv_ne : u ≠ v := by
              intro h
              have := congr_arg Fin.val h
              dsimp [u, ui] at this
              omega
            have hadj : (u : ℕ) + 1 = v.val := by simp [u, ui]; rw [← Nat.div_add_mod v.val 3, hm2]
            exact ⟨u, ⟨ui, rfl⟩, by
              rw [CGraph.path_adj]
              simp [huv_ne, hadj]⟩
      · -- n = 3*a + 2
        obtain ⟨a, rfl⟩ : ∃ a, n = 3 * a + 2 := ⟨n / 3, by omega⟩
        let S : Finset (Fin (3 * a + 3)) :=
          Finset.image (fun i : Fin (a + 1) => ⟨3 * i + 1, by omega⟩) Finset.univ
        refine ⟨S, ?_, ?_⟩
        · rw [Finset.card_image_of_injective _ fun i j h => Fin.ext
            (by have := congr_arg Fin.val h; simp at this; omega), Finset.card_fin]
          simp; omega
        · intro v
          show v ∈ S ∨ ∃ u ∈ S, (CGraph.path (3 * a + 3)).Adj u v
          dsimp only [S]
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          set i := v.val / 3
          have hi : i < a + 1 := by omega
          have hmod_v : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
          rcases hmod_v with hm0 | hm1 | hm2
          · right
            set ui : Fin (a + 1) := ⟨i, hi⟩
            set u : Fin (3 * a + 3) := ⟨3 * ui.val + 1, by omega⟩
            have huv_ne : u ≠ v := by
              intro h
              have := congr_arg Fin.val h
              dsimp [u, ui] at this
              omega
            have hadj : v.val + 1 = (u : ℕ) := by
              simp [u, ui]
              rw [← Nat.div_add_mod v.val 3, hm0]
              dsimp [i]
            exact ⟨u, ⟨ui, rfl⟩, by
              rw [CGraph.path_adj]
              simp [huv_ne, hadj]⟩
          · left
            have hvval : v.val = 3 * i + 1 := by omega
            exact ⟨⟨i, hi⟩, Fin.ext (by simp; omega)⟩
          · right
            set ui : Fin (a + 1) := ⟨i, hi⟩
            set u : Fin (3 * a + 3) := ⟨3 * ui.val + 1, by omega⟩
            have huv_ne : u ≠ v := by
              intro h
              have := congr_arg Fin.val h
              dsimp [u, ui] at this
              omega
            have hadj : (u : ℕ) + 1 = v.val := by simp [u, ui]; rw [← Nat.div_add_mod v.val 3, hm2]
            exact ⟨u, ⟨ui, rfl⟩, by
              rw [CGraph.path_adj]
              simp [huv_ne, hadj]⟩
  · -- (n+3)/3 ≤ domNum: every dominating set has size ≥ (n+3)/3
    apply le_csInf
    · -- Nonempty
      refine ⟨FinEnum.card (CGraph.path (n + 1)).V, ⟨Finset.univ, FinEnum.card_univ,
        CGraph.isDominatingSet_univ (CGraph.path (n + 1))⟩⟩
    · -- Lower bound on every element
      intro k ⟨s, hk, hs⟩
      rw [← hk]
      -- V of path (n+1) is Fin (n+1)
      -- Define T = {v : Fin (n+1) | v.val % 3 = 0}. |T| = (n+3)/3.
      -- Each dominator covers at most one element of T (indices within 1, mod 3 argument).
      --Every element of T is dominated, so |T| ≤ |s|.
      simp only [CGraph.path, CGraph.ofRel, CGraph.IsDominatingSet] at hs
      -- Every vertex v : Fin (n+1) is in s or adjacent to something in s (per hs)
      -- Define T = {v : Fin (n+1) | v.val % 3 = 0}. |T| = (n+3)/3.
      set T : Finset (Fin (n + 1)) := Finset.filter (fun v : Fin (n + 1) => v.val % 3 = 0)
        Finset.univ
      have hcard_T : T.card = (n + 3) / 3 := by
        set m := (n + 3) / 3
        -- There are exactly m elements in {0,...,n} divisible by 3, namely 0,3,...,3*(m-1)
        have : T = Finset.image (fun i : Fin m => ⟨3 * i.val, by omega⟩ : Fin m → Fin (n + 1))
          Finset.univ := by
          ext v
          simp [T, Finset.mem_image, Finset.mem_univ]
          constructor
          · intro hv
            exact ⟨⟨v.val / 3, by omega⟩, by ext; simp; omega⟩
          · rintro ⟨i, hi, rfl⟩
            simp
        rw [this, Finset.card_image_of_injective]
        · simp
        · intro a b h; simp at h; exact Fin.ext (by omega)
      -- Each u ∈ s can "cover" at most one element of T.
      -- Define a function covering each t ∈ T by some u ∈ s that dominates t.
      -- Then injectivity (mod 3 argument) gives |T| ≤ |s|.
      -- Step: for each t ∈ T, pick a dominator u ∈ s.
      -- Dominator u for t means: t = u (t ∈ s) or Adj u t (u adjacent to t, i.e., |u.val - t.val| =
      -- 1).
      -- In either case, t.val ∈ {u.val - 1, u.val, u.val + 1} (within bounds).
      -- Two distinct elements of T have indices both ≡ 0 mod 3, so they differ by ≥ 3.
      -- Hence no u can dominate two distinct elements of T. ⇒ injection T → s.
      -- Step 1: For each t ∈ T, obtain u ∈ s dominating t.
      have hcover : ∀ t ∈ T, ∃ u ∈ s, (t : ℕ) = u.val ∨ (u.val + 1 = (t : ℕ) ∨ (t : ℕ) + 1 = u.val)
        := by
        intro t ht
        specialize hs t
        rcases hs with hts | ⟨u, hus, hadj⟩
        · exact ⟨t, hts, Or.inl rfl⟩
        · simp at hadj
          obtain ⟨hne, hadj|hado⟩ := hadj
          · exact ⟨u, hus, Or.inr (Or.inl hadj)⟩
          · exact ⟨u, hus, Or.inr (Or.inr hado)⟩
      -- Step 2: Each u ∈ s covers at most one element of T (mod 3 argument)
      -- For each t ∈ T, hcover gives a dominator in s.
      -- Key lemma: no u ∈ s covers two distinct elements of T.
      have hunique : ∀ u ∈ s, ∀ t1 ∈ T, ∀ t2 ∈ T,
          ((t1 : ℕ) = u.val ∨ u.val + 1 = (t1 : ℕ) ∨ (t1 : ℕ) + 1 = u.val) →
          ((t2 : ℕ) = u.val ∨ u.val + 1 = (t2 : ℕ) ∨ (t2 : ℕ) + 1 = u.val) → t1 = t2 := by
        intro u hu t1 ht1 t2 ht2 p1 p2
        have ht1T : (t1 : ℕ) % 3 = 0 := Finset.mem_filter.mp ht1 |>.2
        have ht2T : (t2 : ℕ) % 3 = 0 := Finset.mem_filter.mp ht2 |>.2
        -- Each of t1.val, t2.val is in {u.val-1, u.val, u.val+1}
        -- Two numbers ≡ 0 mod 3 in an interval of 3 consecutive integers must be equal.
        have : (t1 : ℕ) % 3 = (t2 : ℕ) % 3 := by omega
        -- More: they differ by at most 2, and both ≡ 0 mod 3, so they're equal.
        have hle : (t1 : ℕ) ≤ (t2 : ℕ) + 2 := by omega
        have hge : (t2 : ℕ) ≤ (t1 : ℕ) + 2 := by omega
        have h_eq_val : (t1 : ℕ) = (t2 : ℕ) := by omega
        exact Fin.ext h_eq_val
      -- Build an injection from T to s.
      -- f (as a function on the subtype T) gives dominators in s.
      -- hunique (rephrased for the subtype) gives injectivity.
      choose f hf using hcover
      have hcard_le : T.card ≤ s.card := by
        let g : T → s := fun t => ⟨f t.val t.property, hf t.val t.property |>.1⟩
        have hg_inj : Function.Injective g := by
          intro t1 t2 h_eq
          have p1 := (hf t1.val t1.property).2
          have p2 := (hf t2.val t2.property).2
          have h_eq' : f t1.val t1.property = f t2.val t2.property := by
            exact congr_arg Subtype.val h_eq
          rw [h_eq'] at p1
          have heq := hunique (f t2.val t2.property) (hf t2.val t2.property |>.1) t1.val t1.property
            t2.val t2.property p1 p2
          exact Subtype.ext heq
        have himage : Finset.image (fun t : T => (g t : (CGraph.path (n+1)).V)) Finset.univ ⊆ s :=
          by
          intro u hu
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
          exact (g t).property
        have h1 : (Finset.image (fun t : T => (g t : (CGraph.path (n+1)).V)) Finset.univ).card =
          T.card := by
          rw [Finset.card_image_of_injective _ (fun a b h => hg_inj (Subtype.ext h))]
          simp
        exact h1 ▸ Finset.card_le_card himage
      rw [← hcard_T]
      exact hcard_le

/-! ### The line graph invariants that are edge invariants by definition

Two of the line graph's invariants are simply other names for invariants of the base graph:
a proper colouring of `L(G)` is a proper edge colouring of `G`, and an independent set in
`L(G)` is a matching in `G`. -/

@[simp] theorem chromNum_lineGraph (G : IsoGraph) : (lineGraph G).chromNum = G.edgeChromNum :=
  (edgeChromNum_eq G).symm

@[simp] theorem indepNum_lineGraph (G : IsoGraph) : (lineGraph G).indepNum = G.matchNum :=
  (matchNum_eq G).symm

@[simp] theorem coverNum_lineGraph (G : IsoGraph) :
    (lineGraph G).coverNum = G.E - G.matchNum := by
  have h := (lineGraph G).coverNum_add_indepNum
  rw [V_lineGraph, indepNum_lineGraph] at h
  omega

/-- **A clique in a line graph is a star or a triangle**, so once some vertex has degree three
the largest star wins and the clique number of the line graph is the maximum degree. -/
theorem cliqueNum_lineGraph_of_three_le_maxDeg {G : IsoGraph} (h : 3 ≤ maxDeg G) :
    (lineGraph G).cliqueNum = maxDeg G := by
  apply le_antisymm
  · induction G using Quotient.inductionOn with | _ g =>
    have hmax : maxDeg ⟦g⟧ = maxDeg ⟦g.canonicalize⟧ := by rw [mk_canonicalize g]
    rw [maxDeg_mk] at h
    have hcmax : g.maxDeg = g.canonicalize.maxDeg := by
      rw [← maxDeg_mk, hmax, maxDeg_mk]
    rw [hcmax] at h
    rw [← mk_canonicalize g, lineGraph_mk, cliqueNum_mk, maxDeg_mk]
    set H := g.canonicalize
    -- Helper: extract adjacency in L(H) as sharing a vertex
    have lineGraph_adj_def : ∀ e f : (CGraph.lineGraph H).V,
        (CGraph.lineGraph H).Adj e f ↔ e ≠ f ∧ ∃ v : H.V, v ∈ (e.1 : Sym2 H.V) ∧ v ∈ (f.1 : Sym2
          H.V) := by
      intro e f; rw [CGraph.lineGraph_adj]; simp [Bool.and_eq_true]
    -- Helper: elements of S are edges of H
    have key : ∀ (S : Finset (CGraph.lineGraph H).V), (CGraph.lineGraph H).toSimple.IsClique (S :
      Set (CGraph.lineGraph H).V) → S.card ≤ H.maxDeg := by
      intro S hS
      -- From hS, distinct elements of S share a vertex
      have hclique : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ∃ v : H.V, v ∈ (e.1 : Sym2 H.V) ∧ v ∈ (f.1 : Sym2
        H.V) := by
        intro e he f hf hef
        have := hS he hf hef
        rw [CGraph.toSimple_adj, lineGraph_adj_def] at this
        exact this.2
      have hinj : Function.Injective (fun e : (CGraph.lineGraph H).V => e.1) := by
        intro e f hef; exact Subtype.ext hef
      -- Common vertex case: if some v is incident to all edges in S, then |S| ≤ deg(v) ≤ maxDeg
      by_cases hstar : ∃ v : H.V, ∀ e ∈ S, v ∈ (e.1 : Sym2 H.V)
      · -- Star case
        obtain ⟨v, hv⟩ := hstar
        have himage : Finset.image (fun e : (CGraph.lineGraph H).V => e.1) S ⊆
          H.toSimple.incidenceFinset v := by
          intro e he
          simp [Finset.mem_image] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          simp [SimpleGraph.mem_incidenceFinset]
          exact ⟨e₀.2, hv e₀ he₀⟩
        calc S.card = (Finset.image (fun e : (CGraph.lineGraph H).V => e.1) S).card := by
              rw [Finset.card_image_of_injective _ hinj]
          _ ≤ (H.toSimple.incidenceFinset v).card := Finset.card_le_card himage
          _ = H.toSimple.degree v := SimpleGraph.card_incidenceFinset_eq_degree H.toSimple v
          _ ≤ H.maxDeg := H.degree_le_maxDeg v
      · -- No common vertex: show |S| ≤ 3
        have hcard_le_3 : S.card ≤ 3 := by
          by_contra hcontra
          push_neg at hcontra
          have hge4 : 4 ≤ S.card := by omega
          -- Pick two distinct edges e₁, e₂ in S
          obtain ⟨e₁, he₁, e₂, he₂, hef₁₂⟩ : ∃ e₁ ∈ S, ∃ e₂ ∈ S, e₁ ≠ e₂ := by
            have : 1 < S.card := by omega
            obtain ⟨e₁, he₁, e₂, he₂, hef⟩ := Finset.one_lt_card.mp this
            exact ⟨e₁, he₁, e₂, he₂, hef⟩
          -- e₁ and e₂ share a vertex v (clique property)
          obtain ⟨v, hv_e1, hv_e2⟩ := hclique e₁ he₁ e₂ he₂ hef₁₂
          -- By hstar, some edge e₃ ∈ S does not contain v
          obtain ⟨e₃, he₃, hv_not_e3⟩ : ∃ e₃ ∈ S, v ∉ (e₃.1 : Sym2 H.V) := by
            push_neg at hstar; exact hstar v
          have hef₁₃ : e₁ ≠ e₃ := by intro h; subst h; exact hv_not_e3 hv_e1
          have hef₂₃ : e₂ ≠ e₃ := by intro h; subst h; exact hv_not_e3 hv_e2
          -- e₃ shares u₁ with e₁
          have haj_e1_e3 := hS he₁ he₃ hef₁₃
          rw [CGraph.toSimple_adj, lineGraph_adj_def] at haj_e1_e3
          obtain ⟨u₁, hu₁_e1, hu₁_e3⟩ := haj_e1_e3.2
          have huv₁ : u₁ ≠ v := by intro h; rw [h] at hu₁_e3; exact hv_not_e3 hu₁_e3
          -- e₃ shares u₂ with e₂
          have haj_e2_e3 := hS he₂ he₃ hef₂₃
          rw [CGraph.toSimple_adj, lineGraph_adj_def] at haj_e2_e3
          obtain ⟨u₂, hu₂_e2, hu₂_e3⟩ := haj_e2_e3.2
          have huv₂ : u₂ ≠ v := by intro h; rw [h] at hu₂_e3; exact hv_not_e3 hu₂_e3
          have hne_u : u₁ ≠ u₂ := by
            intro heq
            have : e₁.1 = e₂.1 := by
              have : u₁ ∈ (e₂.1 : Sym2 H.V) := heq.symm ▸ hu₂_e2
              exact Sym2.eq_of_ne_mem huv₁ hu₁_e1 hv_e1 this hv_e2
            exact hef₁₂ (Subtype.ext this)
          -- e₃.1 has exactly members u₁ and u₂ (card 2, no loops)
          have he3_edge : e₃.1 ∈ H.toSimple.edgeSet := e₃.2
          have he3_not_diag : ¬(e₃.1).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he3_edge
          have hcard_e3 : e₃.1.toFinset.card = 2 :=
            Sym2.card_toFinset_of_not_isDiag e₃.1 he3_not_diag
          have hu1_in_e3 : u₁ ∈ e₃.1.toFinset := Sym2.mem_toFinset.mpr hu₁_e3
          have hu2_in_e3 : u₂ ∈ e₃.1.toFinset := Sym2.mem_toFinset.mpr hu₂_e3
          have hne_uv : u₁ ≠ u₂ := hne_u
          -- e₁.1 has exactly members v and u₁
          have he1_edge : e₁.1 ∈ H.toSimple.edgeSet := e₁.2
          have he1_not_diag : ¬(e₁.1).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he1_edge
          have hcard_e1 : e₁.1.toFinset.card = 2 :=
            Sym2.card_toFinset_of_not_isDiag e₁.1 he1_not_diag
          have hv_in_e1 : v ∈ e₁.1.toFinset := Sym2.mem_toFinset.mpr hv_e1
          have hu1_in_e1 : u₁ ∈ e₁.1.toFinset := Sym2.mem_toFinset.mpr hu₁_e1
          -- Similarly for e₂
          have he2_edge : e₂.1 ∈ H.toSimple.edgeSet := e₂.2
          have he2_not_diag : ¬(e₂.1).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he2_edge
          have hcard_e2 : e₂.1.toFinset.card = 2 :=
            Sym2.card_toFinset_of_not_isDiag e₂.1 he2_not_diag
          have hv_in_e2 : v ∈ e₂.1.toFinset := Sym2.mem_toFinset.mpr hv_e2
          have hu2_in_e2 : u₂ ∈ e₂.1.toFinset := Sym2.mem_toFinset.mpr hu₂_e2
          -- e₁.1.toFinset = {v, u₁}, e₂.1.toFinset = {v, u₂}, e₃.1.toFinset = {u₁, u₂}
          -- There exists e₄ ∈ S \ {e₁, e₂, e₃}
          have hsub : {e₁, e₂, e₃} ⊆ S := by
            simp [Finset.insert_subset_iff, he₁, he₂, he₃]
          have hcard_sub : ({e₁, e₂, e₃} : Finset (CGraph.lineGraph H).V).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [hef₂₃]
            · intro h; simp_all
          have hS_minus_card : (S \ {e₁, e₂, e₃}).card > 0 := by
            have h1 := Finset.card_sdiff_of_subset hsub
            omega
          obtain ⟨e₄, he₄_mem⟩ := Finset.card_pos.mp hS_minus_card
          have he₄_mem' := he₄_mem
          obtain ⟨he₄_in_S, he₄_not_in_triple⟩ := Finset.mem_sdiff.mp he₄_mem'
          simp [Finset.mem_insert, Finset.mem_singleton] at he₄_not_in_triple
          obtain ⟨he₄_ne₁', he₄_ne₂', he₄_ne₃'⟩ := he₄_not_in_triple
          -- e₄.1 is also an edge
          have he4_edge : e₄.1 ∈ H.toSimple.edgeSet := e₄.2
          -- Adjacency gives shared vertices
          have haj_e4_e3 := hS he₄_in_S he₃ he₄_ne₃'
          have haj_e4_e1 := hS he₄_in_S he₁ he₄_ne₁'
          have haj_e4_e2 := hS he₄_in_S he₂ he₄_ne₂'
          rw [CGraph.toSimple_adj, lineGraph_adj_def] at haj_e4_e3 haj_e4_e1 haj_e4_e2
          -- e₄ adjacent to e₃: e₄.1 ≠ e₃.1 and share a vertex
          -- e₄ adjacent to e₁: e₄.1 ≠ e₁.1 and share a vertex
          -- e₄ adjacent to e₂: e₄.1 ≠ e₂.1 and share a vertex
          -- e₁.1 has v, u₁ (v ≠ u₁), e₂.1 has v, u₂ (v ≠ u₂), e₃.1 has u₁, u₂ (u₁ ≠ u₂)
          -- e₄.1 must intersect each of these. With |e₄.1| = 2, this forces e₄.1 = one of them.
          -- Use Sym2.eq_of_ne_mem: if a ≠ b, a ∈ s, b ∈ s, a ∈ t, b ∈ t, and s,t are non-diag
          -- edges, then s = t.
          -- We show e₄.1 = e₁.1, e₂.1, or e₃.1, contradicting he₄_ne.*
          obtain ⟨he4_adj3, w, hw_e4, hw_e3⟩ := haj_e4_e3
          obtain ⟨he4_adj1, z, hz_e4, hz_e1⟩ := haj_e4_e1
          obtain ⟨he4_adj2, y, hy_e4, hy_e2⟩ := haj_e4_e2
          -- e₃.1 contains u₁, u₂ (u₁ ≠ u₂). e₄.1 shares w with e₃.1.
          -- Since e₃.1 is non-diag with u₁,u₂ ∈ e₃.1 and u₁ ≠ u₂,
          -- any vertex in e₃.1 is u₁ or u₂... but we don't need that.
          -- Instead, we directly check: e₄.1 intersects e₃.1 ({u₁,u₂}), e₁.1 ({v,u₁}), e₂.1
          -- ({v,u₂}).
          -- e₄.1 has two endpoints. To intersect all three pairs, it must equal one of them.
          -- Case analysis on which endpoint of e₄.1 lies in e₃.1.
          -- w ∈ e₄.1 ∩ e₃.1. Since u₁,u₂ ∈ e₃.1 and e₃.1 is not diag with those two members,
          -- e₃.1 = Sym2.mk (u₁, u₂). So w = u₁ or w = u₂.
          have hsye_e3 : e₃.1 = Sym2.mk (u₁, u₂) := by
            exact Sym2.eq_of_ne_mem hne_uv hu₁_e3 hu₂_e3 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _
              _)
          have hsye_e1 : e₁.1 = Sym2.mk (v, u₁) := by
            exact Sym2.eq_of_ne_mem huv₁.symm hv_e1 hu₁_e1 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right
              _ _)
          have hsye_e2 : e₂.1 = Sym2.mk (v, u₂) := by
            exact Sym2.eq_of_ne_mem huv₂.symm hv_e2 hu₂_e2 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right
              _ _)
          have hw_cases : w = u₁ ∨ w = u₂ := by
            rw [hsye_e3] at hw_e3; exact Sym2.mem_iff.mp hw_e3
          -- Now: e₄.1 ≠ e₃.1, e₄.1 ≠ e₁.1, e₄.1 ≠ e₂.1 (from adjacency ≠)
          -- and e₄.1 shares a vertex with each.
          -- w = u₁ or u₂ (from e₃ intersection)
          -- We also know z ∈ e₄.1 ∩ e₁.1, y ∈ e₄.1 ∩ e₂.1
          -- e₁.1 = Sym2.mk (v, u₁), so z = v or z = u₁
          have hz_cases : z = v ∨ z = u₁ := by
            rw [hsye_e1] at hz_e1; exact Sym2.mem_iff.mp hz_e1
          -- e₂.1 = Sym2.mk (v, u₂), so y = v or y = u₂
          have hy_cases : y = v ∨ y = u₂ := by
            rw [hsye_e2] at hy_e2; exact Sym2.mem_iff.mp hy_e2
          -- e₄.1 has two elements, one of which is w ∈ {u₁,u₂}.
          -- If w = u₁ and z = u₁ and y = u₂: e₄.1 has u₁, u₂ → e₄.1 = e₃.1, contradiction.
          -- We go case by case and derive contradiction in each.
          -- Derive concrete Sym2 membership in e₄.1
          have hw'_e4 : w ∈ (e₄.1 : Sym2 H.V) := hw_e4
          have hz'_e4 : z ∈ (e₄.1 : Sym2 H.V) := hz_e4
          have hy'_e4 : y ∈ (e₄.1 : Sym2 H.V) := hy_e4
          rcases hw_cases with hwu₁ | hwu₂
          · -- w = u₁
            have hu1_in_e4 : u₁ ∈ (e₄.1 : Sym2 H.V) := hwu₁ ▸ hw_e4
            rcases hz_cases with hzv | hzv
            · -- z = v
              have hv_in_e4 : v ∈ (e₄.1 : Sym2 H.V) := hzv ▸ hz_e4
              exfalso; apply he4_adj1; exact hinj (Sym2.eq_of_ne_mem huv₁.symm hv_in_e4 hu1_in_e4
                hv_e1 hu₁_e1)
            · -- z = u₁
              rcases hy_cases with hyv | hyu2
              · -- y = v
                have hv_in_e4 : v ∈ (e₄.1 : Sym2 H.V) := hyv ▸ hy_e4
                exfalso; apply he4_adj1; exact hinj (Sym2.eq_of_ne_mem huv₁.symm hv_in_e4 hu1_in_e4
                  hv_e1 hu₁_e1)
              · -- y = u₂
                have hu2_in_e4 : u₂ ∈ (e₄.1 : Sym2 H.V) := hyu2 ▸ hy_e4
                exfalso; apply he4_adj3; exact hinj (Sym2.eq_of_ne_mem hne_uv hu1_in_e4 hu2_in_e4
                  hu₁_e3 hu₂_e3)
          · -- w = u₂
            have hu2_in_e4 : u₂ ∈ (e₄.1 : Sym2 H.V) := hwu₂ ▸ hw_e4
            rcases hz_cases with hzv | hzv
            · -- z = v
              have hv_in_e4 : v ∈ (e₄.1 : Sym2 H.V) := hzv ▸ hz_e4
              exfalso; apply he4_adj2; exact hinj (Sym2.eq_of_ne_mem huv₂ hu2_in_e4 hv_in_e4 hu₂_e2
                hv_e2)
            · -- z = u₁
              have hu1_in_e4 : u₁ ∈ (e₄.1 : Sym2 H.V) := hzv ▸ hz_e4
              exfalso; apply he4_adj3; exact hinj (Sym2.eq_of_ne_mem hne_uv hu1_in_e4 hu2_in_e4
                hu₁_e3 hu₂_e3)
        exact le_trans hcard_le_3 h
    obtain ⟨t, ht, hcard⟩ := (CGraph.lineGraph H).toSimple.exists_isNClique_cliqueNum
    simp only [CGraph.cliqueNum] at hcard ⊢
    exact hcard ▸ key t ht
  · exact G.maxDeg_le_cliqueNum_lineGraph

/-! ### Möbius ladders

`circulant (2 * m) [1, m]` is the Möbius ladder: a `2m`-cycle with every pair of opposite
vertices joined.  The two smallest ones are graphs we already know.

Both live on `CGraph` first: the four-vertex one is an equality of graphs, since the two sides
carry the same adjacency on the same `Fin 4`, and the six-vertex one is a genuine relabelling. -/

/-- An independent set of `μ G` meets the shadows in at most everything and the original copy in
an independent set. -/
theorem indepNum_mycielskian_le (G : IsoGraph) (hV : 0 < G.V) :
    (mycielskian G).indepNum ≤ G.V + G.indepNum := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g] at *
    simp only [indepNum_mk, V_mk]
    rw [mycielskian_mk, indepNum_mk]
    set G' := g.canonicalize
    set n := FinEnum.card G'.V

    -- Helper embeddings
    let inlEmb : G'.V → (G'.mycielskian).V := fun a => some (Sum.inl a)
    let inrEmb : G'.V → (G'.mycielskian).V := fun a => some (Sum.inr a)
    have hinl_inj : Function.Injective inlEmb := by
      intro a b h; exact Sum.inl_injective (Option.some_injective _ h)
    have hinr_inj : Function.Injective inrEmb := by
      intro a b h; exact Sum.inr_injective (Option.some_injective _ h)
    have hinl_adj : ∀ a b : G'.V, (G'.mycielskian).Adj (inlEmb a) (inlEmb b) = G'.Adj a b := by
      intro a b; rfl
    have hnone_inr_adj : ∀ a : G'.V, (G'.mycielskian).Adj none (inrEmb a) = true := by
      intro a; rfl
    -- inr vertices are pairwise non-adjacent in μG'
    have hinr_not_adj : ∀ a b : G'.V, (G'.mycielskian).Adj (inrEmb a) (inrEmb b) = false := by
      intro a b; simp [inrEmb, CGraph.mycielskian_adj_inr_inr]
    --key: any indep set s of μG' has |s| ≤ n + α(G')
    have key : ∀ (s : Finset ((G'.mycielskian).V)), (G'.mycielskian).toSimple.IsIndepSet (↑s) →
        s.card ≤ n + G'.indepNum := by
      intro s hs_ind
      -- The inl-vertices of s, as a Finset of G'.V
      let A : Finset G'.V := Finset.univ.filter (fun a => inlEmb a ∈ s)
      -- The inr-vertices of s, as a Finset of G'.V  
      let B : Finset G'.V := Finset.univ.filter (fun a => inrEmb a ∈ s)
      -- Key facts about A and B
      -- A is an indep set in G'
      have hA_indep : G'.toSimple.IsIndepSet (A : Set G'.V) := by
        intro a ha b hb hab
        simp [A] at ha hb
        intro hadj
        have hnot_adj := hs_ind ha hb (hinl_inj.ne hab)
        simp [CGraph.toSimple_adj] at hnot_adj
        rw [hinl_adj] at hnot_adj
        simp [CGraph.toSimple_adj] at hadj
        simp [hnot_adj] at hadj
      have hA_card : A.card ≤ G'.indepNum := hA_indep.card_le_indepNum
      -- B.card ≤ n
      have hB_card : B.card ≤ n := by
        have : B.card ≤ FinEnum.card G'.V := FinEnum.card_le B
        exact this
      -- The inlEmb image of A has size |A|
      have himage_inl : (Finset.image inlEmb
          A).card = A.card := Finset.card_image_of_injective _ hinl_inj
      -- The inrEmb image of B has size |B|
      have himage_inr : (Finset.image inrEmb
          B).card = B.card := Finset.card_image_of_injective _ hinr_inj
      -- none is not in any inlEmb or inrEmb image
      have hnone_not_inl : none ∉ Finset.image inlEmb A := by simp [inlEmb]
      have hnone_not_inr : none ∉ Finset.image inrEmb B := by simp [inrEmb]
      -- inlEmb images and inrEmb images are disjoint
      have hdisl : Disjoint (Finset.image inlEmb A) (Finset.image inrEmb B) := by
        rw [Finset.disjoint_left]
        intro v hvl hvr
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hvl
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hvr
        simp [inlEmb, inrEmb] at hb
        have := Option.some_injective _ hb
        exact Sum.inl_ne_inr this.symm
      -- Case split on none ∈ s
      -- Subset relations
      have hs_sub_caseA : none ∈ s → s ⊆ {none} ∪ Finset.image inlEmb A := by
        intro hnone v hv
        cases v with
        | none => simp
        | some x =>
          cases x with
          | inl a =>
            have : some (Sum.inl a) ∈ Finset.image inlEmb A := by
              simp [Finset.mem_image, A]
              exact ⟨a, hv, rfl⟩
            rw [Finset.mem_union]
            exact Or.inr this
          | inr a =>
            exfalso
            have hne : (none : G'.mycielskian.V) ≠ some (Sum.inr a) := by simp
            have := hs_ind hnone hv hne
            simp [inrEmb, hnone_inr_adj a] at this
      have hs_sub_caseB : none ∉ s → s ⊆ Finset.image inlEmb A ∪ Finset.image inrEmb B := by
        intro hnone v hv
        cases v with
        | none => exact absurd hv hnone
        | some x =>
          cases x with
          | inl a =>
            have : some (Sum.inl a) ∈ Finset.image inlEmb A := by
              simp [Finset.mem_image, A]
              exact ⟨a, hv, rfl⟩
            rw [Finset.mem_union]
            exact Or.inl this
          | inr a =>
            have : some (Sum.inr a) ∈ Finset.image inrEmb B := by
              simp [Finset.mem_image, B]
              exact ⟨a, hv, rfl⟩
            rw [Finset.mem_union]
            exact Or.inr this
      -- B = ∅ when none ∈ s
      have hB_empty : none ∈ s → B = ∅ := by
        intro hnone
        ext a; simp [B]
        intro ha_mem
        exfalso
        have hne : (none : G'.mycielskian.V) ≠ some (Sum.inr a) := by simp
        have := hs_ind hnone ha_mem hne
        simp [inrEmb, hnone_inr_adj a] at this
      -- Case split on none ∈ s
      by_cases hnone : none ∈ s
      · have hs_subA := hs_sub_caseA hnone
        have hcard : s.card ≤ 1 + A.card := by
          calc s.card ≤ ({none} ∪ Finset.image inlEmb A).card := Finset.card_le_card hs_subA
            _ = 1 + A.card := by
              rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hnone_not_inl)]
              simp [himage_inl]
        have hn : 0 < n := hV
        omega
      · have hs_subB' := hs_sub_caseB hnone
        have hcardB' : s.card ≤ A.card + B.card := by
          calc s.card ≤ (Finset.image inlEmb A ∪ Finset.image inrEmb B).card :=
              Finset.card_le_card hs_subB'
            _ = A.card + B.card := by
              rw [Finset.card_union_of_disjoint hdisl, himage_inl, himage_inr]
        linarith

    have goal : (CGraph.mycielskian G').indepNum ≤ n + G'.indepNum := by
      unfold CGraph.indepNum
      rw [SimpleGraph.indepNum]
      have hbdd : BddAbove {n | ∃ s : Finset ((G'.mycielskian).V),
          (G'.mycielskian).toSimple.IsNIndepSet n s} :=
        ⟨Fintype.card _, fun k ⟨s, hs⟩ => by
          rw [← hs.card_eq]
          exact Finset.card_le_univ s⟩
      apply csSup_le'
      · intro k hk
        obtain ⟨s, hs⟩ := hk
        rcases hs with ⟨hs_ind, hs_card⟩
        rw [← hs_card]
        unfold CGraph.indepNum at key
        exact key s hs_ind
    exact goal

/-- The `|V(G)|` shadows are an independent set, so the complementary cover is small. -/
theorem coverNum_mycielskian_le (G : IsoGraph) : (mycielskian G).coverNum ≤ G.V + 1 := by
  have h1 := coverNum_add_indepNum (mycielskian G)
  have h2 := V_le_indepNum_mycielskian G
  rw [V_mycielskian] at h1
  omega

/-- Covering `μ G` costs at least one more than covering `G`. -/
theorem coverNum_lt_coverNum_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    G.coverNum + 1 ≤ (mycielskian G).coverNum := by
  have h1 := coverNum_add_indepNum (mycielskian G)
  have h2 := coverNum_add_indepNum G
  have h3 := indepNum_mycielskian_le G hV
  rw [V_mycielskian] at h1
  omega

/-- Greedy colouring bounds the clique number too, since `ω ≤ χ ≤ Δ + 1`. -/
theorem cliqueNum_le_maxDeg_add_one (G : IsoGraph) : G.cliqueNum ≤ maxDeg G + 1 :=
  le_trans (cliqueNum_le_chromNum G) (chromNum_le_maxDeg_add_one G)

/-- Transporting `CGraph.chromNum_lineGraph_le_of_edgeColouring` to the quotient: an explicit
symmetric colouring of the ordered pairs, proper on the edges, bounds the chromatic index. -/
theorem edgeChromNum_mk_le_of_colouring {G : CGraph} {k : ℕ}
    (c : G.V → G.V → Fin k) (hsymm : ∀ x y, c x y = c y x)
    (hproper : ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w) :
    edgeChromNum ⟦G⟧ ≤ k := by
  rw [edgeChromNum_eq, lineGraph_mk, chromNum_mk]
  exact CGraph.chromNum_lineGraph_le_of_edgeColouring c hsymm hproper

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

theorem indepNum_lexProduct_complete (m n : ℕ) :
    (complete (m + 1) ·g complete (n + 1)).indepNum = 1 := by
  have h := indepNum_lexProduct (complete (m + 1)) (complete (n + 1))
  rw [indepNum_complete, indepNum_complete, Nat.min_eq_right (by omega : 1 ≤ m + 1),
    Nat.min_eq_right (by omega : 1 ≤ n + 1)] at h
  omega

theorem chromNum_disjUnion_cycle_even_odd (m n : ℕ) :
    (cycle (2 * m + 2) ⊕g cycle (2 * n + 3)).chromNum = 3 := by
  have h := chromNum_disjUnion (cycle (2 * m + 2)) (cycle (2 * n + 3))
  rw [chromNum_cycle_even, chromNum_cycle_odd] at h
  omega

theorem cliqueNum_compl_lexProduct_complete (m n : ℕ) :
    ((complete (m + 1) ·g complete (n + 1))ᶜ).cliqueNum = 1 := by
  rw [cliqueNum_compl, indepNum_lexProduct_complete]

/-- A dominating vertex of the second factor makes the lexicographic product dominated exactly as
its first factor is. -/
theorem domNum_lexProduct_complete (G : IsoGraph) (n : ℕ) :
    (G ·g complete (n + 1)).domNum = G.domNum :=
  domNum_lexProduct G (domNum_complete n)

theorem domNum_strongProduct_complete (m n : ℕ) :
    (complete (m + 1) ⊠g complete (n + 1)).domNum = 1 :=
  domNum_strongProduct_eq_one (domNum_complete m) (domNum_complete n)

/-! ### The Mycielskian of a complete graph -/

theorem cliqueNum_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 1))).cliqueNum = max (m + 1) 2 := by
  have h := cliqueNum_mycielskian (complete (m + 1)) (by rw [V_complete]; omega)
  rw [cliqueNum_complete] at h
  omega

theorem cliqueNum_lineGraph_mycielskian {G : IsoGraph} (h3 : 3 ≤ max (2 * maxDeg G) G.V) :
    (lineGraph (mycielskian G)).cliqueNum = max (2 * maxDeg G) G.V := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := mycielskian G)
    (by rw [maxDeg_mycielskian]; exact h3)
  rwa [maxDeg_mycielskian] at hm

/-! ### The Mycielskian of a line graph -/

theorem cliqueNum_mycielskian_lineGraph {G : IsoGraph} (hE : 0 < G.E) (h : 3 ≤ G.maxDeg) :
    (mycielskian (lineGraph G)).cliqueNum = G.maxDeg := by
  have hm := cliqueNum_mycielskian (lineGraph G) (by rw [V_lineGraph]; exact hE)
  rw [cliqueNum_lineGraph_of_three_le_maxDeg h] at hm
  omega

theorem coverNum_mycielskian_lineGraph_le (G : IsoGraph) :
    (mycielskian (lineGraph G)).coverNum ≤ G.E + 1 := by
  have h := coverNum_mycielskian_le (lineGraph G)
  rwa [V_lineGraph] at h

theorem cliqueNum_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) :
    (mycielskian (mycielskian G)).cliqueNum = max G.cliqueNum 2 := by
  have h1 := cliqueNum_mycielskian (mycielskian G) (by rw [V_mycielskian]; omega)
  rw [cliqueNum_mycielskian G hV] at h1
  omega

theorem cliqueNum_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G + maxDeg H) :
    (lineGraph (G □g H)).cliqueNum = maxDeg G + maxDeg H := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G □g H)
    (by rw [maxDeg_cartesianProduct hG hH]; exact h3)
  rwa [maxDeg_cartesianProduct hG hH] at hm

theorem cliqueNum_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ max (maxDeg G + H.V) (G.V + maxDeg H)) :
    (lineGraph (G ∇g H)).cliqueNum = max (maxDeg G + H.V) (G.V + maxDeg H) := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G ∇g H)
    (by rw [maxDeg_join hG hH]; exact h3)
  rwa [maxDeg_join hG hH] at hm

theorem cliqueNum_lineGraph_compl {G : IsoGraph} (hG : 0 < G.V) (h3 : 3 ≤ G.V - 1 - minDeg G) :
    (lineGraph Gᶜ).cliqueNum = G.V - 1 - minDeg G := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := Gᶜ)
    (by rw [maxDeg_compl hG]; exact h3)
  rwa [maxDeg_compl hG] at hm

theorem cliqueNum_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) :
    (mycielskian (G ∇g H)).cliqueNum = max (G.cliqueNum + H.cliqueNum) 2 := by
  have hm := cliqueNum_mycielskian (G ∇g H) (by rw [V_join]; omega)
  rwa [cliqueNum_join] at hm

theorem cliqueNum_mycielskian_compl {G : IsoGraph} (hG : 0 < G.V) :
    (mycielskian Gᶜ).cliqueNum = max G.indepNum 2 := by
  have hm := cliqueNum_mycielskian Gᶜ (by rw [V_compl]; exact hG)
  rwa [cliqueNum_compl] at hm

theorem cliqueNum_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * maxDeg H) :
    (lineGraph (G ⊗g H)).cliqueNum = maxDeg G * maxDeg H := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G ⊗g H)
    (by rw [maxDeg_tensorProduct hG hH]; exact h3)
  rwa [maxDeg_tensorProduct hG hH] at hm

theorem cliqueNum_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * H.V + maxDeg H) :
    (lineGraph (G ·g H)).cliqueNum = maxDeg G * H.V + maxDeg H := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := G ·g H)
    (by rw [maxDeg_lexProduct hG hH]; exact h3)
  rwa [maxDeg_lexProduct hG hH] at hm

theorem cliqueNum_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (mycielskian (G ⊗g H)).cliqueNum = max (min G.cliqueNum H.cliqueNum) 2 := by
  have hm := cliqueNum_mycielskian (G ⊗g H) (by rw [V_tensorProduct]; exact Nat.mul_pos hG hH)
  rwa [cliqueNum_tensorProduct] at hm

theorem cliqueNum_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (mycielskian (G ·g H)).cliqueNum = max (G.cliqueNum * H.cliqueNum) 2 := by
  have hm := cliqueNum_mycielskian (G ·g H) (by rw [V_lexProduct]; exact Nat.mul_pos hG hH)
  rwa [cliqueNum_lexProduct] at hm

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
  rw [V_cartesianProduct, V_cycle, V_cycle, indepNum_cartesianProduct_cycle_even m n hev] at h
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
  rw [V_cartesianProduct, V_cycle, V_cycle, indepNum_cartesianProduct_cycle_odd a b hab] at h
  nlinarith [h]

end IsoGraph
