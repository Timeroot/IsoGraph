import IsoGraph.SmallGraphs.Grotzsch

/-!
# Trees, decorated cycles and theta graphs

Tadpoles, lollipops, double stars, spiders and theta graphs: the two-parameter families built by
decorating a cycle or a path.
-/

namespace IsoGraph

/-! ### Tadpoles, lollipops, double stars and theta graphs

The four decorated families are all `CGraph.ofEdges` on an explicit edge list, so the
counting lemmas below are all instances of "the list has no duplicates, no self-loops and no
reversed pairs, therefore `E` is its length".  The remaining invariants come from the shape:
a lollipop's clique is its largest, a tadpole's junction is its only degree-three vertex, and a
double star always has a pendant. -/

/-- The double star has one central edge and `m + n` pendant edges. -/
theorem E_doubleStar (m n : ℕ) : (doubleStar m n).E = m + n + 1 := by
  simp only [doubleStar]
  rw [IsoGraph.E_mk]
  set G : CGraph := CGraph.ofEdges (2 + m + n)
    ((0, 1) :: (((List.range m).map fun i ↦ (0, 2 + i)) ++
      ((List.range n).map fun i ↦ (1, 2 + m + i))))
  have heq : G = CGraph.doubleStar m n := rfl
  -- G.Adj is definitionally (CGraph.doubleStar m n).Adj
  let root : G.V := ⟨0, by omega⟩
  have hreach : ∀ v : G.V, G.toSimple.Reachable root v := by
    intro v
    by_cases hv0 : v.val = 0
    · have : v = root := Fin.ext hv0; rw [this]
    by_cases hv1 : v.val = 1
    · have hv_eq : v = ⟨1, by omega⟩ := Fin.ext hv1
      rw [hv_eq]
      have hadj : G.Adj root ⟨1, by omega⟩ = true := by
        change (CGraph.doubleStar m n).Adj root ⟨1, by omega⟩ = true
        rw [CGraph.doubleStar_adj_val]
        dsimp [root]
        simp
      exact SimpleGraph.Adj.reachable (show G.toSimple.Adj root ⟨1, by omega⟩ by simpa using hadj)
    · -- v.val ≥ 2
      by_cases hv_m : v.val < 2 + m
      · have hadj : G.Adj root v = true := by
          change (CGraph.doubleStar m n).Adj root v = true
          rw [CGraph.doubleStar_adj_val]
          dsimp [root]
          simp; omega
        exact SimpleGraph.Adj.reachable (show G.toSimple.Adj root v by simpa using hadj)
      · have hadj : G.Adj ⟨1, by omega⟩ v = true := by
          change (CGraph.doubleStar m n).Adj ⟨1, by omega⟩ v = true
          rw [CGraph.doubleStar_adj_val]
          simp; omega
        have hreach1 : G.toSimple.Reachable root ⟨1, by omega⟩ := by
          have hadj1 : G.Adj root ⟨1, by omega⟩ = true := by
            change (CGraph.doubleStar m n).Adj root ⟨1, by omega⟩ = true
            rw [CGraph.doubleStar_adj_val]
            dsimp [root]
            simp
          exact
            SimpleGraph.Adj.reachable (show G.toSimple.Adj root ⟨1, by omega⟩ by simpa using hadj1)
        exact hreach1.trans (SimpleGraph.Adj.reachable
          (show G.toSimple.Adj ⟨1, by omega⟩ v by simpa using hadj))
  have hconn : G.IsConnected := by
    unfold CGraph.IsConnected
    have : Nonempty G.V := ⟨root⟩
    apply SimpleGraph.Connected.mk
    intro u v
    exact (hreach u).symm.trans (hreach v)
  have hlower : m + n + 1 ≤ G.E := by
    have h1 := hconn.card_le_E_add_one
    have hcard : FinEnum.card G.V = 2 + m + n := by simp [G]
    rw [hcard] at h1; omega
  have hdeg_bound : ∀ v : G.V,
      G.toSimple.degree v ≤
    if v.val = 0 then m + 1
    else if v.val = 1 then n + 1
    else 1 := by
    intro v
    simp only [SimpleGraph.degree]
    have hadj_eq : ∀ u w : G.V, G.Adj u w = true ↔
      (u.1 ≠ w.1 ∧
        (((u.1 = 0 ∧ w.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ w.1 ∧ w.1 < 2 + m) ∨
            (u.1 = 1 ∧ 2 + m ≤ w.1 ∧ w.1 < 2 + m + n)) ∨
          ((w.1 = 0 ∧ u.1 = 1) ∨ (w.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + m) ∨
            (w.1 = 1 ∧ 2 + m ≤ u.1 ∧ u.1 < 2 + m + n)))) := by
      intro u w; exact CGraph.doubleStar_adj_val m n u w
    -- neighborFinset characterization helper
    let oneEle : G.V := ⟨1, by omega⟩
    -- For any w, if Adj v w = true, then w satisfies certain val conditions
    by_cases hv0 : v.val = 0
    · simp [hv0]
      have hv_eq : v = root := Fin.ext hv0
      rw [hv_eq]
      have hneigh_root :
          ∀ w : G.V, G.Adj root w = true → w.val = 1 ∨ (2 ≤ w.val ∧ w.val < 2 + m) := by
        intro w hw
        rw [hadj_eq] at hw
        simp [root] at hw
        omega
      have hsub : G.toSimple.neighborFinset root ⊆
        Finset.univ.filter (fun w => w.val = 1 ∨ (2 ≤ w.val ∧ w.val < 2 + m)) := by
        intro w hw
        simp [SimpleGraph.mem_neighborFinset] at hw
        simp [Finset.mem_filter]; exact hneigh_root w hw
      have hcard_le : Finset.card (Finset.univ.filter (fun w : G.V => w.val = 1 ∨ (2 ≤ w.val ∧
          w.val < 2 + m))) ≤ m + 1 := by
        have hsub2 : Finset.univ.filter (fun w : G.V => w.val = 1 ∨ (2 ≤ w.val ∧ w.val < 2 + m)) ⊆
          {oneEle} ∪ Finset.image (fun i : Fin m => ⟨2 + i.val, by omega⟩) Finset.univ := by
          intro w hw
          simp [Finset.mem_filter] at hw
          simp [Finset.mem_image, Finset.mem_univ]
          rcases hw with h | h
          · left; exact Fin.ext h
          · right
            obtain ⟨h2, hlt⟩ := h
            set a : Fin m := ⟨w.val - 2, by omega⟩
            have hge2 : 2 ≤ w.val := h2
            have hfa : (fun i : Fin m => Fin.mk (2 + i.val) (by omega) : Fin m → G.V) a = w := by
              ext; simp [a, hge2]
            exact ⟨a, hfa⟩
        have hcard_image : Finset.card (Finset.image (fun i : Fin m => Fin.mk (2 + i.val)
            (by omega) : Fin m → G.V) Finset.univ) ≤ m := by
          exact le_trans (Finset.card_image_le) (by simp)
        have : Finset.card ({oneEle} ∪ Finset.image (fun i : Fin m => Fin.mk (2 + i.val) (by omega)
            : Fin m → G.V) Finset.univ) ≤ 1 + m := by
          exact le_trans (Finset.card_union_le _ _) (add_le_add (by simp) hcard_image)
        have h1 : 1 + m = m + 1 := by omega
        rw [h1] at this
        exact le_trans (Finset.card_le_card hsub2) this
      exact le_trans (Finset.card_le_card hsub) hcard_le
    · by_cases hv1 : v.val = 1
      · simp [hv1]
        have hv_eq : v = oneEle := Fin.ext hv1
        rw [hv_eq]
        have hneigh_one :
            ∀ w : G.V, G.Adj oneEle w = true → w.val = 0 ∨ (2 + m ≤ w.val ∧ w.val < 2 + m + n) := by
          intro w hw
          rw [hadj_eq] at hw
          simp [oneEle] at hw
          by_cases hw0 : w = root
          · left; exact congr_arg Fin.val hw0
          · right
            obtain ⟨_, hcases⟩ := hw
            rcases hcases with h | h | h
            · exact ⟨h, w.isLt⟩
            · exfalso; exact hw0 h
            · exfalso; omega
        have hsub : G.toSimple.neighborFinset oneEle ⊆
          {root} ∪ Finset.image (fun i : Fin n => ⟨2 + m + i.val, by omega⟩) Finset.univ := by
          intro w hw
          simp [SimpleGraph.mem_neighborFinset] at hw
          obtain h | h := hneigh_one w hw
          · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr (Fin.ext h))
          · obtain ⟨h2, hlt⟩ := h
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨w.val - (2 + m), by omega⟩,
                Finset.mem_univ _, Fin.ext (by simp; omega)⟩)
        have hcard_image : Finset.card (Finset.image (fun i : Fin n => Fin.mk (2 + m + i.val)
            (by omega) : Fin n → G.V) Finset.univ) ≤ n := by
          exact le_trans (Finset.card_image_le) (by simp)
        have hcard_le : Finset.card (G.toSimple.neighborFinset oneEle) ≤ n + 1 := by
          have := Finset.card_le_card hsub
          calc Finset.card (G.toSimple.neighborFinset oneEle)
              ≤ Finset.card ({root} ∪ Finset.image (fun i : Fin n => Fin.mk (2 + m + i.val)
                  (by omega) : Fin n → G.V) Finset.univ) := this
            _ ≤ Finset.card {root} + Finset.card (Finset.image (fun i : Fin n => Fin.mk (2 + m +
                i.val) (by omega) : Fin n → G.V) Finset.univ) :=
                Finset.card_union_le _ _
            _ ≤ 1 + n := by exact add_le_add (by simp [Finset.card_singleton]) hcard_image
            _ = n + 1 := by omega
        exact hcard_le
      · simp [hv0, hv1]
        by_cases hv_m : v.val < 2 + m
        · -- v connected to root only
          have hv2 : 2 ≤ v.val := by omega
          have hneigh_pendant_m : ∀ w : G.V, G.Adj v w = true → w.val = 0 := by
            intro w hw
            rw [hadj_eq] at hw
            simp [hv2, hv0, hv1, hv_m] at hw
            rcases hw with ⟨hne, h | h⟩
            · exact congr_arg Fin.val h
            · exfalso; omega
          have hsub : G.toSimple.neighborFinset v ⊆ {root} := by
            intro w hw
            simp [SimpleGraph.mem_neighborFinset] at hw
            exact Finset.mem_singleton.mpr (Fin.ext (hneigh_pendant_m w hw))
          exact Finset.card_le_card hsub |> le_trans <| by simp
        · -- v connected to oneEle only
          have hge : 2 + m ≤ v.val := by omega
          have hneigh_pendant_n : ∀ w : G.V, G.Adj v w = true → w.val = 1 := by
            intro w hw
            rw [hadj_eq] at hw
            simp [hge, hv0, hv1] at hw
            omega
          have hsub : G.toSimple.neighborFinset v ⊆ {oneEle} := by
            intro w hw
            simp [SimpleGraph.mem_neighborFinset] at hw
            exact Finset.mem_singleton.mpr (Fin.ext (hneigh_pendant_n w hw))
          exact Finset.card_le_card hsub |> le_trans <| by simp
  have hsum_bound : ∑ v : G.V, G.toSimple.degree v ≤ 2 * (m + n + 1) := by
    calc ∑ v : G.V, G.toSimple.degree v
        ≤ ∑ v : G.V, (if v.val = 0 then m + 1 else if v.val = 1 then n + 1 else 1) :=
          Finset.sum_le_sum fun v _ => hdeg_bound v
      _ = 2 * (m + n + 1) := by
          have hGV : G.V = Fin (2 + m + n) := rfl
          rw [← Equiv.sum_comp (Equiv.cast hGV).symm]
          simp [Equiv.cast]
          have hfun : ∀ x : Fin (2 + m + n),
            (if x = 0 then m + 1 else if (x : ℕ) = 1 then n + 1 else 1) =
            (if (x : ℕ) = 0 then m + 1 else if (x : ℕ) = 1 then n + 1 else 1) := by
            intro x; by_cases hx : x = 0 <;> simp [hx]
          rw [Finset.sum_congr rfl (fun x _ => hfun x)]
          set f : ℕ → ℕ := fun i => if i = 0 then m + 1 else if i = 1 then n + 1 else 1
          have hsum_eq :
              ∑ x : Fin (2 + m + n), f (x : ℕ) = ∑ i ∈ Finset.range (2 + m + n), f i := by
            rw [Finset.sum_range]
          rw [hsum_eq]
          have hsum_computed :
              ∀ k ≥ 2, ∑ i ∈ Finset.range k, f i = (m + 1) + (n + 1) + (k - 2) := by
            intro k hk
            induction k, hk using Nat.le_induction with
            | base => simp [Finset.sum_range_succ, f]
            | succ k hk ih =>
              rw [Finset.sum_range_succ, ih]
              have hk1 : k ≠ 0 := by omega
              have hk2 : k ≠ 1 := by omega
              simp [f, hk1, hk2]
              omega
          rw [hsum_computed (2 + m + n) (by omega)]
          omega
  have hE := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple
  unfold CGraph.E at hE
  have hull : G.E ≤ m + n + 1 := by
    unfold CGraph.E
    omega
  rw [← heq]
  exact le_antisymm hull hlower

/-- The lollipop is a clique plus a path. -/
theorem E_lollipop (m k : ℕ) : (lollipop (m + 1) k).E = (m + 1).choose 2 + k := by
  -- Helper: for ofEdges with a list of pairs (i,j) where i < j for all entries,
  -- all indices < n, and the list is nodup, E = list.length.
  have ofEdges_E_of_lt : ∀ (n : ℕ) (es : List (ℕ × ℕ)),
      (∀ p ∈ es, p.1 < p.2) →
      (∀ p ∈ es, p.2 < n) →
      List.Nodup es →
      (CGraph.ofEdges n es).E = es.length := by
    intro n es hlt hbound hnup
    induction es with
    | nil =>
      rw [CGraph.ofEdges_nil, CGraph.E_empty]; rfl
    | cons p es' ih =>
      -- ofEdges n (p :: es') = ofEdges n (es' ++ [p]) by commutativity of disjunction in contains
      have heq : CGraph.ofEdges n (p :: es') = CGraph.ofEdges n (es' ++ [p]) := by
        apply CGraph.ofEdges_congr n _ _ _
        intro x y hne
        simp [List.mem_cons, List.mem_append]
        tauto
      rw [heq]
      -- Restrict hypotheses to es'
      have hlt' : ∀ q ∈ es', q.1 < q.2 := fun q hq => hlt q (List.mem_cons_of_mem _ hq)
      have hfun : ∀ q ∈ p :: es', q.1 < n := fun q hq => lt_trans (hlt q hq) (hbound q hq)
      have hbound' : ∀ q ∈ es', q.2 < n := fun q hq => hbound q (List.mem_cons_of_mem _ hq)
      have hnup' : es'.Nodup := hnup.tail
      have ihm := ih hlt' hbound' hnup'
      -- The edge from p
      have hp_mem : p ∈ p :: es' := List.mem_cons_self
      set ep : Sym2 (Fin n) := Sym2.mk (⟨p.1, hfun p hp_mem⟩, ⟨p.2, hbound p hp_mem⟩)
      -- ep is not in edgeFinset of ofEdges n es'
      have hnotin : ep ∉ (CGraph.ofEdges n es').toSimple.edgeFinset := by
        intro hmem
        simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple, CGraph.ofEdges, CGraph.ofRel] at hmem
        obtain ⟨hne, hm ⟩ := hmem
        have hp12 : p.1 < p.2 := hlt p hp_mem
        have hpn : p ∉ es' := (List.nodup_cons.mp hnup).1
        -- ep.1 = ⟨p.1, ...⟩, ep.2 = ⟨p.2, ...⟩ as Fin n
        -- hm : ((↑ep.1, ↑ep.2) ∈ es' ∨ (↑ep.2, ↑ep.1) ∈ es')
        -- But ↑ep.1 = p.1 and ↑ep.2 = p.2 (definitionally, from how ep is constructed)
        -- So hm says (p.1, p.2) ∈ es' ∨ (p.2, p.1) ∈ es'
        -- Both are impossible: first by hpn, second by hlt' (would give p.2 < p.1)
        rcases hm with h | h
        · exact hpn h
        · have := hlt' (p.2, p.1) h
          omega
      -- edgeFinset of ofEdges n (es' ++ [p]) = edgeFinset of ofEdges n es' ∪ {ep}
      have hedgeFinset : (CGraph.ofEdges n (es' ++ [p])).toSimple.edgeFinset =
          (CGraph.ofEdges n es').toSimple.edgeFinset ∪ {ep} := by
        ext e
        simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple, CGraph.ofEdges, CGraph.ofRel,
          List.mem_append]
        induction e using Sym2.ind with
        | _ a b =>
          simp only [SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet]
          dsimp only [ep]
          rw [Sym2.eq_iff]
          simp only [Fin.ext_iff]
          -- Convert Fin constructor equalities to Nat equalities
          have : ∀ (x : Fin n) (v : ℕ) (hv : v < n), (x = ⟨v, hv⟩ ↔ x.1 = v) := by
            intro x v hv; simp [Fin.ext_iff]
          rw [this a p.1 (hfun p hp_mem), this b p.2 (hbound p hp_mem),
              this a p.2 (hbound p hp_mem), this b p.1 (hfun p hp_mem)]
          set a' : ℕ := a.val
          set b' : ℕ := b.val
          rcases p with ⟨p1, p2⟩
          simp [Prod.mk.injEq]
          have hpnotin_es' : (p1, p2) ∉ es' := by
            intro h; exact (List.nodup_cons.mp hnup).1 h
          have hp12 : p1 < p2 := by simpa using hlt (p1, p2) hp_mem
          have hp21notin_es' : (p2, p1) ∉ es' := by
            intro h; have := hlt' (p2, p1) h; omega
          have hp12ne : p1 ≠ p2 := hp12.ne
          set A := (a', b') ∈ es'
          set B := a' = p1 ∧ b' = p2
          set C := (b', a') ∈ es'
          set D := b' = p1 ∧ a' = p2
          simp only [A, B, C, D] at *
          have hDflip : a' = p2 ∧ b' = p1 ↔ D := by constructor <;> intro h <;> exact ⟨h.2, h.1⟩
          rw [hDflip]
          rw [show b' = p1 ∧ a' = p2 ↔ D from Iff.rfl]
          have hNe_from_B : B → ¬a' = b' := by intro ⟨ha, hb⟩; omega
          have hNe_from_D : D → ¬a' = b' := by intro ⟨hb, ha⟩; omega
          -- Goal: Ne ∧ ((A ∨ B) ∨ C ∨ D) ↔ (B ∨ D) ∨ Ne ∧ (A ∨ C)
          set Ne := ¬a' = b'
          show Ne ∧ ((A ∨ B) ∨ C ∨ D) ↔ (B ∨ D) ∨ Ne ∧ (A ∨ C)
          constructor
          · intro h
            rcases h with ⟨Ne, hmem⟩
            rcases hmem with hAB | hCD
            · rcases hAB with hA | hB
              · exact Or.inr ⟨Ne, Or.inl hA⟩
              · exact Or.inl (Or.inl hB)
            · rcases hCD with hC | hD_val
              · exact Or.inr ⟨Ne, Or.inr hC⟩
              · exact Or.inl (Or.inr hD_val)
          · intro h
            rcases h with hBD | ⟨Ne, hAC⟩
            · rcases hBD with hB | hD_val
              · exact ⟨hNe_from_B hB, Or.inl (Or.inr hB)⟩
              · exact ⟨hNe_from_D hD_val, Or.inr (Or.inr hD_val)⟩
            · rcases hAC with hA | hC
              · exact ⟨Ne, Or.inl (Or.inl hA)⟩
              · exact ⟨Ne, Or.inr (Or.inl hC)⟩
      unfold CGraph.E at ihm ⊢
      rw [hedgeFinset, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnotin)]
      rw [Finset.card_singleton]
      rw [ihm]
      rfl
  -- Apply helper to lollipop
  simp only [lollipop, CGraph.lollipop, IsoGraph.E_mk]
  have hvalid : (∀ p ∈ CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k, p.1 < p.2) := by
    intro p hp
    simp [List.mem_append] at hp
    rcases hp with h | h
    · rw [CGraph.mem_cliqueEdges] at h; exact h.1
    · rw [CGraph.mem_legEdges] at h
      rcases h with h | h
      · rcases h with ⟨hp1, hp2, hk⟩; simp [hp1, hp2]
      · rcases h with ⟨hoff, hp2, hlim⟩; simp [hp2]
  have hbound :
      (∀ p ∈ CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k, p.2 < m + 1 + k) := by
    intro p hp
    simp [List.mem_append] at hp
    rcases hp with h | h
    · rw [CGraph.mem_cliqueEdges] at h; omega
    · rw [CGraph.mem_legEdges] at h
      rcases h with h | h
      · rcases h with ⟨hp1, hp2, hk⟩; simp [hp2]; exact hk
      · rcases h with ⟨hoff, hp2, hlim⟩; simp [hp2]; omega
  have hclique_nodup : ∀ m, (CGraph.cliqueEdges m).Nodup := by
    intro m
    induction m with
    | zero => simp [CGraph.cliqueEdges]
    | succ n ih =>
      unfold CGraph.cliqueEdges
      have hsource : (List.range (n + 1)).Nodup := List.nodup_range
      have hinners : ∀ i ∈ List.range (n + 1), ((List.filter (fun x => decide (i < x)) (List.range
          (n + 1))).map (i, ·)).Nodup := by
        intro i hi
        have hsub : List.Sublist (List.filter (fun x => decide (i < x)) (List.range (n +
            1))) (List.range (n + 1)) := List.filter_sublist
        have hnup_inner := List.Sublist.nodup hsub hsource
        exact List.Nodup.map (show Function.Injective (fun x : ℕ => (i, x)) from fun x y h =>
            by injection h) hnup_inner
      -- Now prove flatMap nodup
      have hflat_nodup : ∀ {l : List ℕ}, l.Nodup → (∀ i ∈ l, ((List.filter (fun x => decide (i <
          x)) (List.range (n + 1))).map (i, ·)).Nodup) →
          (∀ i ∈ l, ∀ j ∈ l, i ≠ j → ∀ x, x ∈ ((List.filter (fun x => decide (i < x)) (List.range
              (n + 1))).map (i, ·)) →
            x ∉ ((List.filter (fun x => decide (j < x)) (List.range (n + 1))).map (j, ·))) →
          (l.flatMap (fun i => (List.filter (fun x => decide (i < x)) (List.range (n + 1))).map (i,
              ·))).Nodup := by
        intro l hlnodup hinner hdj
        induction l with
        | nil => simp
        | cons a l ihl =>
          simp only [List.flatMap_cons]
          apply List.Nodup.append
          · exact hinner a List.mem_cons_self
          · exact
              ihl (List.nodup_cons.mp hlnodup).2 (fun i hi => hinner i (List.mem_cons_of_mem a hi))
              (fun i hi j hj hij => hdj i (List.mem_cons_of_mem a hi) j (List.mem_cons_of_mem a hj)
                  hij)
          · intro x hx1 hx2
            have ha_notin_l : a ∉ l := (List.nodup_cons.mp hlnodup).1
            rcases List.mem_map.mp hx1 with ⟨b, hb1, hb2⟩
            subst hb2
            rcases List.mem_flatMap.mp hx2 with ⟨j, hj1, hj2⟩
            rcases List.mem_map.mp hj2 with ⟨c, hc1, hc2⟩
            have := Prod.ext_iff.mp hc2
            rcases this with ⟨rfl, _⟩
            exact ha_notin_l hj1
      exact hflat_nodup hsource hinners (fun i hi j hj hij x hx1 hx2 => by
        obtain ⟨a, _, ha2⟩ := List.mem_map.mp hx1
        obtain ⟨b, _, hb2⟩ := List.mem_map.mp hx2
        have hab : (i, a) = (j, b) := ha2.trans hb2.symm
        have hij' : i = j := by simpa using congr_arg Prod.fst hab
        exact hij hij'
      )
  have hleg_nodup : ∀ k, (CGraph.legEdges 0 (m + 1) k).Nodup := by
    intro k; induction k with
    | zero => simp [CGraph.legEdges_zero]
    | succ j ih =>
      simp [CGraph.legEdges_succ]
      have : (List.range j).Nodup := List.nodup_range
      exact List.Nodup.map (fun x y h => by injection h with h1 h2; omega) this
  have hleg_len : ∀ k, (CGraph.legEdges 0 (m + 1) k).length = k := by
    intro k; induction k with
    | zero => simp [CGraph.legEdges_zero]
    | succ j ih => simp [CGraph.legEdges_succ, List.length_cons]
  have hnup : (CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k).Nodup := by
    apply List.Nodup.append (hclique_nodup (m + 1)) (hleg_nodup k)
    intro a ha1 ha2
    -- a ∈ cliqueEdges (m+1) and a ∈ legEdges 0 (m+1) k
    -- From mem_cliqueEdges: a.1 < a.2 < m+1
    -- From mem_legEdges: (a.1 = 0 ∧ a.2 = m+1 ∧ 0 < k) ∨ (m+1 ≤ a.1 ∧ a.2 = a.1+1 ∧ a.1+1 < m+1+k)
    -- Both cases give contradiction since a.2 < m+1 but legEdges requires a.2 ≥ m+1
    rw [CGraph.mem_cliqueEdges] at ha1
    rw [CGraph.mem_legEdges] at ha2
    rcases ha2 with ⟨h1, h2, h3⟩ | ⟨hoff, hp2, hlim⟩
    · -- (0, m+1) case: but cliqueEdges requires a.2 < m+1, i.e. m+1 < m+1, contradiction
      rw [h1, h2] at ha1; omega
    · -- (p, p+1) with m+1 ≤ p case: but cliqueEdges requires a.2 < m+1, i.e. p+1 < m+1,
      -- contradiction with m+1 ≤ p
      rw [hp2] at ha1; omega
  have hclique_len : ∀ m, (CGraph.cliqueEdges m).length = m.choose 2 := by
    intro m
    have hvalid' : ∀ p ∈ CGraph.cliqueEdges m, p.1 < p.2 := by
      intro p hp; rw [CGraph.mem_cliqueEdges] at hp; exact hp.1
    have hbound' : ∀ p ∈ CGraph.cliqueEdges m, p.2 < m := by
      intro p hp; rw [CGraph.mem_cliqueEdges] at hp; exact hp.2
    have h1 := ofEdges_E_of_lt m (CGraph.cliqueEdges m) hvalid' hbound' (hclique_nodup m)
    rw [CGraph.ofEdges_cliqueEdges, CGraph.E_complete] at h1
    exact h1.symm
  rw [ofEdges_E_of_lt (m + 1 + k) _ hvalid hbound hnup, List.length_append, hclique_len, hleg_len]

/-- The tadpole is a cycle plus a path: `m + k` edges on `m + k` vertices. -/
theorem E_tadpole (m k : ℕ) : (tadpole (m + 3) k).E = m + 3 + k := by
  simp only [IsoGraph.E_mk, tadpole_def, CGraph.E]
  unfold CGraph.tadpole
  rw [show CGraph.ofEdges (m + 3 + k) (CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k) =
      CGraph.tadpole (m + 3) k from rfl]
  -- Helper: injectivity of the path edge maps
  let inj1 : Function.Injective (fun i : ℕ => (i, i + 1) : ℕ → ℕ × ℕ) := fun a b h => by injection h
  let inj2 : Function.Injective (fun i : ℕ => (i + (m + 3), i + 1 + (m + 3)) : ℕ → ℕ × ℕ) :=
    fun a b h => by injection h; omega
  -- Prove nodup of cycleEdges (m+3)
  have hnodup_cycle : List.Nodup (CGraph.cycleEdges (m + 3)) := by
    induction m + 3 with
    | zero => simp [CGraph.cycleEdges_zero]
    | succ n ih =>
      rw [CGraph.cycleEdges_succ]
      apply List.Nodup.append
      · exact List.Nodup.map inj1 List.nodup_range
      · exact List.nodup_singleton _
      · simp [List.mem_map]
  -- Prove nodup of legEdges 0 (m+3) k
  have hnodup_leg : List.Nodup (CGraph.legEdges 0 (m + 3) k) := by
    induction k with
    | zero => simp [CGraph.legEdges_zero]
    | succ j ih =>
      rw [CGraph.legEdges_succ]
      apply List.Nodup.cons
      · simp [List.mem_map, List.mem_range]
      · exact List.Nodup.map inj2 List.nodup_range
  -- Prove disjointness
  have hdisjoint : Disjoint (CGraph.cycleEdges (m + 3)).toFinset
      (CGraph.legEdges 0 (m + 3) k).toFinset := by
    rw [Finset.disjoint_left]
    intro p hpcy hple
    simp only [List.mem_toFinset] at hpcy hple
    rw [CGraph.mem_cycleEdges] at hpcy
    rw [CGraph.mem_legEdges] at hple
    rcases hpcy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hple with ⟨h3, h4, _⟩ | ⟨h3, h4, h5⟩ <;> omega
  -- es.length = m+3+k
  have hlen_cycle : List.length (CGraph.cycleEdges (m + 3)) = m + 3 := by
    induction m + 3 with
    | zero => simp [CGraph.cycleEdges_zero]
    | succ n ih =>
      rw [CGraph.cycleEdges_succ, List.length_append, List.length_map, List.length_range,
          List.length_singleton]
  have hlen_leg : List.length (CGraph.legEdges 0 (m + 3) k) = k := by
    induction k with
    | zero => simp [CGraph.legEdges_zero]
    | succ j ih =>
      rw [CGraph.legEdges_succ, List.length_cons, List.length_map, List.length_range]
  have hes_len : (CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k).length = m + 3 + k := by
    simp [hlen_cycle, hlen_leg]
  -- Bound on edge endpoints
  have habound : ∀ p ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k,
      p.1 < m + 3 + k ∧ p.2 < m + 3 + k := by
    intro p hp
    simp [List.mem_append] at hp
    rcases hp with h | h
    · rw [CGraph.mem_cycleEdges] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega
    · rw [CGraph.mem_legEdges] at h
      rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩ <;> constructor <;> omega
  -- No self-loops
  have hes_no_loop : ∀ p ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k, p.1 ≠ p.2 := by
    intro p hp
    simp [List.mem_append] at hp
    rcases hp with h | h
    · rw [CGraph.mem_cycleEdges] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rw [CGraph.mem_legEdges] at h
      rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩ <;> omega
  -- No reverse duplicates
  have hes_no_rev : ∀ a b : ℕ, a ≠ b →
      ((a, b) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k →
       (b, a) ∉ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k) := by
    intro a b hab hmem
    simp [List.mem_append, CGraph.mem_legEdges] at hmem ⊢
    rcases hmem with h | h | h | h <;> omega
  -- adjacency characterization
  let G := CGraph.tadpole (m + 3) k
  have hadj : ∀ v u : G.V, G.toSimple.Adj v u ↔
      v ≠ u ∧ ((v.val, u.val) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k ∨
                (u.val, v.val) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k) := by
    intro v u
    rw [CGraph.toSimple_adj, CGraph.tadpole_adj_val]
    simp
    rw [not_congr (Fin.ext_iff.symm)]
    tauto
  -- adjFinset.card = 2 * es.length
  let es := CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k
  let adjFinset : Finset (G.V × G.V) := Finset.filter (fun p => G.toSimple.Adj p.1 p.2) Finset.univ
  have hnodup_es : es.Nodup := List.Nodup.append hnodup_cycle hnodup_leg
    (List.disjoint_left.mpr fun p hp hq => Finset.disjoint_left.mp hdisjoint (List.mem_toFinset.mpr
        hp) (List.mem_toFinset.mpr hq))
  have hes_finset_card : es.toFinset.card = es.length := List.toFinset_card_of_nodup hnodup_es
  -- Build adjFinset.card = 2 * es.length
  -- Key: there's a bijection es.toFinset × Bool ≃ adjFinset
  -- Each edge (a,b) in es gives two adjacent pairs in adjFinset: (a,b) and (b,a)
  have hes_no_loop' : ∀ p ∈ es.toFinset, p.1 ≠ p.2 := by
    intro p hp; exact hes_no_loop p (List.mem_toFinset.mp hp)
  have hes_no_rev' : ∀ a b : ℕ, a ≠ b →
      ((a, b) ∈ es.toFinset → (b, a) ∉ es.toFinset) := by
    intro a b hab hmem
    exact fun hmem2 => hes_no_rev a b hab (List.mem_toFinset.mp hmem) (List.mem_toFinset.mp hmem2)
  have hcard_adj : adjFinset.card = 2 * es.length := by
    let attached := { p : ℕ × ℕ // p ∈ es.toFinset }
    let toAdj (x : attached × Bool) : adjFinset :=
      let pp : ℕ × ℕ := x.1.val
      have hpes' : pp ∈ es.toFinset := by
        exact x.1.property
      let hpes := List.mem_toFinset.mp hpes'
      let hv1 : G.V := ⟨pp.1, (habound pp hpes).1⟩
      let hv2 : G.V := ⟨pp.2, (habound pp hpes).2⟩
      if x.2 = Bool.true then
        ⟨(hv2, hv1),
         Finset.mem_filter.mpr ⟨Finset.mem_univ _,
           (hadj hv2 hv1).mpr
             ⟨fun heq =>
               have h : pp.2 = pp.1 := Fin.ext_iff.mp heq
               hes_no_loop' pp hpes' (by omega),
              Or.inr hpes⟩⟩⟩
      else
        ⟨(hv1, hv2),
         Finset.mem_filter.mpr ⟨Finset.mem_univ _,
           (hadj hv1 hv2).mpr
             ⟨fun heq =>
               have h : pp.1 = pp.2 := Fin.ext_iff.mp heq
               hes_no_loop' pp hpes' (by omega),
              Or.inl hpes⟩⟩⟩
    let inftyAdj (x : adjFinset) : attached × Bool := by
      let hv : G.V := x.val.1
      let hu : G.V := x.val.2
      have hx2 : G.toSimple.Adj hv hu := by simpa [adjFinset, hv, hu] using x.2
      have hor : (hv.val, hu.val) ∈ es ∨ (hu.val, hv.val) ∈ es := (hadj hv hu).mp hx2 |>.2
      if h : (hv.val, hu.val) ∈ es then
        exact ⟨⟨(hv.val, hu.val), List.mem_toFinset.mpr h⟩, Bool.false⟩
      else
        have h' : (hu.val, hv.val) ∈ es := (or_iff_not_imp_left.mp hor) h
        exact ⟨⟨(hu.val, hv.val), List.mem_toFinset.mpr h'⟩, Bool.true⟩
    have h_left_inv : ∀ x : attached × Bool, inftyAdj (toAdj x) = x := by
      intro ⟨⟨pp, hpes'⟩, b⟩
      dsimp only [toAdj, inftyAdj]
      rcases b with (_ | _)
      · -- b = false: toAdj gives (hv1, hv2) with adj proof using Or.inl hpes
        -- inftyAdj: checks (pp.1, pp.2) ∈ es → true, so returns (⟨(pp.1,pp.2), ...⟩, false)
        have hpes_list : pp ∈ es := List.mem_toFinset.mp hpes'
        dsimp [And.rec]
        simp [hpes_list]
      · -- b = true
        have hpes_list' : pp ∈ es.toFinset := hpes'
        have hpes_list : pp ∈ es := List.mem_toFinset.mp hpes_list'
        have hno_rev : (pp.2, pp.1) ∉ es := by
          intro h
          exact hes_no_rev' pp.1 pp.2 (hes_no_loop' pp hpes_list') (List.mem_toFinset.mpr
              hpes_list) (List.mem_toFinset.mpr h)
        simp [hno_rev]
    have h_right_inv : ∀ x : adjFinset, toAdj (inftyAdj x) = x := by
      intro ⟨p, hp⟩
      simp only [inftyAdj, toAdj]
      let hv := p.1
      let hu := p.2
      have hx2 : G.toSimple.Adj hv hu := by
        simpa [adjFinset] using hp
      have hor : (hv.val, hu.val) ∈ es ∨ (hu.val, hv.val) ∈ es :=
        (hadj hv hu).mp hx2 |>.2
      show toAdj (inftyAdj ⟨p, hp⟩) = ⟨p, hp⟩
      simp only [inftyAdj]
      by_cases h2 : ((↑⟨p, hp⟩ : adjFinset).val.1.val, (↑⟨p, hp⟩ : adjFinset).val.2.val) ∈ es
      · -- (hv,hu) ∈ es: inftyAdj gives (⟨(hv,hu),_⟩, false), toAdj gives ⟨(hv,hu),_⟩
        simp [h2]
        dsimp [toAdj]
      · -- (hv,hu) ∉ es, so (hu,hv) ∈ es by hor
        have h3 : ((↑⟨p, hp⟩ : adjFinset).val.2.val, (↑⟨p, hp⟩ : adjFinset).val.1.val) ∈ es := by
          simpa [hv, hu] using (or_iff_not_imp_left.mp hor) h2
        simp [h2]
        dsimp [toAdj]
    let h_equiv : attached × Bool ≃ adjFinset :=
      { toFun := toAdj
        invFun := inftyAdj
        left_inv := h_left_inv
        right_inv := h_right_inv }
    have hcard_attached : Fintype.card attached = es.toFinset.card := by
      have h : attached ≃ ↥es.toFinset :=
        { toFun := fun x => ⟨x.val, x.property⟩
          invFun := fun x => ⟨x.val, x.property⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun x => Subtype.ext rfl }
      rw [Fintype.card_congr h]
      exact Fintype.card_coe es.toFinset
    have h1 := Fintype.card_congr h_equiv
    simp [Fintype.card_prod, hcard_attached, hes_finset_card] at h1
    linarith
  -- Connect to edgeFinset via handshaking
  have hhand : ∑ v : G.V, G.toSimple.degree v = 2 * G.toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple
  have hadjFinset_card : adjFinset.card = ∑ v : G.V, G.toSimple.degree v := by
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset]
    have h1 : adjFinset = Finset.biUnion Finset.univ (fun v => Finset.image (fun u => (v, u))
        (Finset.filter (G.toSimple.Adj v ·) Finset.univ)) := by
      ext ⟨v, u⟩
      simp [adjFinset, Finset.mem_biUnion, Finset.mem_image]
    rw [h1, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro v _
      rw [Finset.card_image_of_injective _ (fun a b h => by injection h)]
      simp
    · intro v _ w _ hvw
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp
      dsimp at hp
      rw [Finset.mem_image] at hp
      obtain ⟨u, hu, rfl⟩ := hp
      intro h
      dsimp at h
      rw [Finset.mem_image] at h
      obtain ⟨u', hu', hpp'⟩ := h
      have := congr_arg Prod.fst hpp'
      simp at this
      exact hvw this.symm
  rw [hadjFinset_card] at hcard_adj
  linarith [hes_len]

/-- The theta graph's `i`-th path contributes `xs[i] + 1` edges.  The hypothesis rules out the
repeated pole-to-pole edge that two zeroes in the list would give. -/
theorem E_thetaGraph (xs : List ℕ) (h : ∀ k ∈ xs, 0 < k) :
    (thetaGraph xs).E = xs.sum + xs.length := by
  -- Step 1: Show (thetaEdges 2 xs).length = xs.sum + xs.length
  have hlen : ∀ (off : ℕ) (xs : List ℕ), (∀ k ∈ xs, 0 < k) → (CGraph.thetaEdges off
      xs).length = xs.sum + xs.length := by
    intro off xs hxs; induction xs generalizing off with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with _ | hd
      · have h0 : 0 ∈ (0 :: tl) := by simp [List.mem_cons]
        exact absurd (hxs 0 h0) (by norm_num)
      · have ih' := ih (off + hd + 1) (fun k hk => hxs k (List.mem_cons.mpr (Or.inr hk)))
        simp [CGraph.thetaEdges, List.length_append, List.length_map, List.length_range]
        omega
  -- Step 2: The edge set of thetaGraph xs is in bijection with thetaEdges 2 xs
  -- (when all xs elements are positive, thetaEdges has no duplicates, no self-loops, no reverse
  -- pairs)
  -- So (thetaGraph xs).E = (thetaEdges 2 xs).length = xs.sum + xs.length
  rw [thetaGraph_def, E_mk]
  -- Goal: (CGraph.thetaGraph xs).E = xs.sum + xs.length
  -- thetaGraph xs = ofEdges (2 + xs.sum) (thetaEdges 2 xs)
  -- We need: (ofEdges (2 + xs.sum) (thetaEdges 2 xs)).E = (thetaEdges 2 xs).length
  -- then use hlen.
  -- Helper: for any "good" edge list es on vertices Fin n, (ofEdges n es).E = es.length
  -- Standalone helper: each element contributes to exactly one bucket
  have hsum_fst : ∀ {n : ℕ} {es : List (ℕ × ℕ)}, (∀ p ∈ es, p.1 < n) →
      ∑ i : Fin n, (es.filter (fun p => p.1 = i.val)).length = es.length := by
    intro n es hen
    induction es with
    | nil => simp
    | cons e es' ih =>
      simp [List.filter_cons]
      have hgoal : ∀ (x : Fin n),
          ((if e.1 = (x : ℕ) then e :: List.filter (fun p => decide (p.1 = ↑x)) es'
            else List.filter (fun p => decide (p.1 = ↑x)) es')).length =
          (List.filter (fun p => decide (p.1 = ↑x)) es').length + (if e.1 = (x : ℕ) then 1 else
              0) := by
        intro x; split_ifs <;> simp [List.length_cons]
      simp_rw [hgoal]
      rw [Finset.sum_add_distrib]
      have hif : ∑ i : Fin n, (if e.1 = (i : ℕ) then 1 else 0) = 1 := by
        have hmem : e.1 < n := hen e (by simp)
        have : ∀ x : Fin n, (e.1 = (x : ℕ)) ↔ x = ⟨e.1, hmem⟩ := by
          intro x; exact ⟨fun h => Fin.ext h.symm, fun h => h ▸ rfl⟩
        simp [this]
      rw [hif]
      simp
      exact ih (fun p hp => hen p (List.mem_cons.mpr (Or.inr hp)))
  have hsum_snd : ∀ {n : ℕ} {es : List (ℕ × ℕ)}, (∀ p ∈ es, p.2 < n) →
      ∑ i : Fin n, (es.filter (fun p => p.2 = i.val)).length = es.length := by
    intro n es hen
    induction es with
    | nil => simp
    | cons e es' ih =>
      simp [List.filter_cons]
      have hgoal : ∀ (x : Fin n),
          ((if e.2 = (x : ℕ) then e :: List.filter (fun p => decide (p.2 = ↑x)) es'
            else List.filter (fun p => decide (p.2 = ↑x)) es')).length =
          (List.filter (fun p => decide (p.2 = ↑x)) es').length + (if e.2 = (x : ℕ) then 1 else
              0) := by
        intro x; split_ifs <;> simp [List.length_cons]
      simp_rw [hgoal]
      rw [Finset.sum_add_distrib]
      have hif : ∑ i : Fin n, (if e.2 = (i : ℕ) then 1 else 0) = 1 := by
        have hmem : e.2 < n := hen e (by simp)
        have : ∀ x : Fin n, (e.2 = (x : ℕ)) ↔ x = ⟨e.2, hmem⟩ := by
          intro x; exact ⟨fun h => Fin.ext h.symm, fun h => h ▸ rfl⟩
        simp [this]
      rw [hif]
      simp
      exact ih (fun p hp => hen p (List.mem_cons.mpr (Or.inr hp)))
  have ofEdges_E_helper : ∀ {n : ℕ} {es : List (ℕ × ℕ)},
      (∀ p ∈ es, p.1 < n ∧ p.2 < n) →
      (∀ p ∈ es, p.1 ≠ p.2) →
      (∀ p ∈ es, (p.2, p.1) ∉ es) →
      es.Nodup →
      (CGraph.ofEdges n es).E = es.length := by
    intro n es hn hnooops hnorev hnodup
    induction es with
    | nil =>
      have : CGraph.ofEdges n [] = CGraph.empty n := by
        exact CGraph.ext' rfl (heq_of_eq (funext fun i => funext fun j =>
            by simp [CGraph.ofEdges, CGraph.empty]))
      rw [this, CGraph.E_empty, List.length_nil]
    | cons e es' ih =>
      unfold CGraph.E
      set ue : Fin n := ⟨e.1, (hn e (by simp)).1⟩
      set ve : Fin n := ⟨e.2, (hn e (by simp)).2⟩
      set edge_e : Sym2 (Fin n) := Sym2.mk (ue, ve)
      have he_not_in_es' : e ∉ es' := by
        intro h
        have hd := hnodup
        simp [List.nodup_cons] at hd
        exact hd.1 h
      have hrev_not_in_es' : (e.2, e.1) ∉ es' := by
        intro h
        have hmem : (e.2, e.1) ∈ e :: es' := by simp [h]
        exact absurd (hnorev (e.2, e.1) hmem) (by simp [List.mem_cons])
      have hdisjoint : edge_e ∉ (CGraph.ofEdges n es').toSimple.edgeFinset := by
        intro he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj,
            CGraph.ofEdges_adj_val] at he
        rcases he.2 with h | h
        · exact he_not_in_es' h
        · exact hrev_not_in_es' h
      -- Now show the edgeFinset equality
      have hedgeFinset_eq : (CGraph.ofEdges n (e :: es')).toSimple.edgeFinset =
          (insert edge_e (CGraph.ofEdges n es').toSimple.edgeFinset) := by
        ext x
        show x ∈ (CGraph.ofEdges n (e :: es')).toSimple.edgeFinset ↔
            x ∈ insert edge_e (CGraph.ofEdges n es').toSimple.edgeFinset
        have hdef : (CGraph.ofEdges n (e :: es')).V = Fin n := rfl
        change x ∈ (CGraph.ofEdges n (e :: es')).toSimple.edgeFinset ↔
            x ∈ insert edge_e (CGraph.ofEdges n es').toSimple.edgeFinset at *
        induction x using Sym2.ind with
        | h u v =>
          simp [SimpleGraph.mem_edgeFinset, Finset.mem_insert, SimpleGraph.mem_edgeSet,
            CGraph.toSimple_adj, CGraph.ofEdges_adj_val]
          dsimp only [CGraph.ofEdges, CGraph.ofRel] at u v
          simp only [edge_e]
          rw [Sym2.eq_iff]
          have heq1 : (u = ue ↔ ↑u = e.1) := by simp [ue, Fin.ext_iff]
          have heq2 : (v = ve ↔ ↑v = e.2) := by simp [ve, Fin.ext_iff]
          have heq3 : (u = ve ↔ ↑u = e.2) := by simp [ve, Fin.ext_iff]
          have heq4 : (v = ue ↔ ↑v = e.1) := by simp [ue, Fin.ext_iff]
          have heq5 : ((↑u, ↑v) = e ↔ ↑u = e.1 ∧ ↑v = e.2) := Prod.ext_iff
          have heq6 : ((↑v, ↑u) = e ↔ ↑v = e.1 ∧ ↑u = e.2) := Prod.ext_iff
          rw [heq5, heq6, heq1, heq2, heq3, heq4]
          have hnooops_e : e.1 ≠ e.2 := hnooops e (by simp)
          have huvFin : (u : ℕ) = (v : ℕ) ↔ u = v := Fin.ext_iff.symm
          have hA_notC : (↑u = e.1 ∧ ↑v = e.2) → ¬(↑u = ↑v) := by
            intro ⟨ha, hb⟩ huv
            have huv' : (u : ℕ) = (v : ℕ) := congr_arg (fun x : Fin n => (x : ℕ)) huv
            exact hnooops_e (by rw [ha, hb] at huv'; exact huv')
          have hB_notC : (↑v = e.1 ∧ ↑u = e.2) → ¬(↑u = ↑v) := by
            intro ⟨ha, hb⟩ huv
            have huv' : (u : ℕ) = (v : ℕ) := congr_arg (fun x : Fin n => (x : ℕ)) huv
            exact hnooops_e (by rw [hb, ha] at huv'; exact huv'.symm)
          have hB'_notC : (↑v = e.1 ∧ ↑u = e.2) → ¬(↑u = ↑v) := hB_notC
          have hB_eq_B' : (↑u = e.2 ∧ ↑v = e.1) ↔ (↑v = e.1 ∧ ↑u = e.2) := and_comm
          have hAB_notC : (↑u = e.1 ∧ ↑v = e.2 ∨ ↑u = e.2 ∧ ↑v = e.1) → ¬(↑u = ↑v) := by
            rintro (hA | hB'')
            · exact hA_notC hA
            · exact hB_notC ⟨hB''.2, hB''.1⟩
          constructor
          · rintro ⟨hne, hmem⟩
            rcases hmem with hAD | hBD' | hF
            · rcases hAD with hA | hD
              · exact .inl (.inl hA)
              · exact .inr ⟨hne, .inl hD⟩
            · exact .inl (.inr (hB_eq_B'.mpr hBD'))
            · exact .inr ⟨hne, .inr hF⟩
          · rintro (hAB | ⟨hne, hDF⟩)
            · have hnotC := hAB_notC hAB
              exact ⟨by intro huv; exact hnotC (Fin.ext_iff.mpr huv),
                     Or.elim hAB (fun hA => Or.inl (Or.inl hA))
                       (fun hB'' => Or.inr (Or.inl (hB_eq_B'.mp hB'')))⟩
            · exact ⟨hne, Or.elim hDF (fun hD => Or.inl (Or.inr hD)) (fun hF => Or.inr (Or.inr hF))⟩
      rw [hedgeFinset_eq, Finset.card_insert_of_notMem hdisjoint]
      simp [List.length_cons]
      exact ih
        (fun p hp => ⟨(hn p (by simp [hp])).1, (hn p (by simp [hp])).2⟩)
        (fun p hp => hnooops p (by simp [hp]))
        (fun p hp => by
          have h := hnorev p (by simp [hp])
          exact fun hm => h (by simp [hm]))
        hnodup.tail
  have htheta_good_off : ∀ (off : ℕ) (xs : List ℕ),
      (∀ k ∈ xs, 0 < k) → off ≥ 2 →
      (∀ p ∈ CGraph.thetaEdges off xs, p.1 < off + xs.sum ∧ p.2 < off + xs.sum) ∧
      (∀ p ∈ CGraph.thetaEdges off xs, p.1 ≠ p.2) ∧
      (∀ p ∈ CGraph.thetaEdges off xs, (p.2, p.1) ∉ CGraph.thetaEdges off xs) ∧
      (CGraph.thetaEdges off xs).Nodup := by
    intro off xs hxshit offge2
    induction xs generalizing off with
    | nil =>
      simp [CGraph.thetaEdges]
    | cons hd tl ih =>
      have hhdpos : 0 < hd := hxshit hd (List.mem_cons_self ..)
      have ih' := ih (off + hd) (fun k hk => hxshit k (List.mem_cons_of_mem hd hk)) (by omega)
      rw [CGraph.thetaEdges_cons off hd tl]
      simp only [List.sum_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      -- Destructure ih'
      set ih1 := ih'.1
      set ih2 := ih'.2.1
      set ih3 := ih'.2.2.1
      set ih4 := ih'.2.2.2
      -- 1. Bounds
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · have := CGraph.mem_thetaEdges_bound off [hd] p.1 p.2 hp1
          simp [List.sum_cons, List.sum_nil] at this; omega
        · have := ih1 p hp2; constructor <;> omega
      -- 2. No self-loops
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · rw [CGraph.mem_thetaEdges_single] at hp1
          rcases hp1 with ⟨rfl, hp1eq, hp2eq⟩ | ⟨hpos, hp1eq, hp2eq⟩ | ⟨hpos, hp1eq, hp2eq⟩ | ⟨h1,
              hp2eq, h3⟩ <;> omega
        · exact ih'.2.1 p hp2
      -- 3. No reverse duplicates
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · -- p in block1
          have hnot_block1 : (p.2, p.1) ∉ CGraph.thetaEdges off [hd] := by
            rw [CGraph.mem_thetaEdges_single]
            rw [CGraph.mem_thetaEdges_single] at hp1
            rcases hp1 with h | h | h | h
            · omega
            · rcases h with ⟨hpos, hp1eq, hp2eq⟩
              simp [hp1eq, hp2eq]
              omega
            · rcases h with ⟨hpos, hp1eq, hp2eq⟩
              simp [hp1eq, hp2eq]
              omega
            · rcases h with ⟨h1, hp2eq, h3⟩
              simp [hp2eq]
              omega
          intro hmem
          rcases List.mem_append.mp hmem with h' | h'
          · exact absurd h' hnot_block1
          · rw [CGraph.mem_thetaEdges_single] at hp1
            rcases hp1 with h | h | h | h
            · omega
            · -- p = (0, off), reverse = (off, 0). Block2 first coord off: off < 2? No. off+hd ≤
              -- off? No.
              have hb2 := CGraph.mem_thetaEdges_bound (off + hd) tl p.2 p.1 h'
              omega
            · -- p = (off+hd-1, 1), reverse = (1, off+hd-1). Block2 second coord off+hd-1: <2? No
              -- (≥2). ≥ off+hd? No.
              have hb2 := CGraph.mem_thetaEdges_bound (off + hd) tl p.2 p.1 h'
              omega
            · -- chain edge: off ≤ p.1, p.2 = p.1+1, p.1+1 < off+hd. Reverse: (p.2, p.1) = (p.1+1,
              -- p.1).
              -- Block2 first coord p.2 = p.1+1: <2? p.1+1 < 2 → p.1 < 1, but off ≤ p.1, off≥2,
              -- contradiction.
              -- ≥ off+hd? p.1+1 ≥ off+hd, but p.1+1 < off+hd, contradiction.
              have hb2 := CGraph.mem_thetaEdges_bound (off + hd) tl p.2 p.1 h'
              omega
        · -- p in block2
          have hrev_block2 : (p.2, p.1) ∉ CGraph.thetaEdges (off + hd) tl := ih'.2.2.1 p hp2
          intro hmem
          rcases List.mem_append.mp hmem with h' | h'
          · rw [CGraph.mem_thetaEdges_single] at h'
            have hbound2 := CGraph.mem_thetaEdges_bound (off + hd) tl p.1 p.2 hp2
            rcases h' with h'' | h'' | h'' | h'' <;> omega
          · exact absurd h' hrev_block2
      -- 4. Nodup
      · have hblk1_nodup : (CGraph.thetaEdges off [hd]).Nodup := by
          rcases hd with _ | k
          · omega
          · simp [CGraph.thetaEdges]
            refine ⟨fun h => by omega, ?_⟩
            have hinj : Function.Injective (fun i : ℕ => (off + i, off + i + 1)) := by
              intro a b hab; injection hab with h1 h2; omega
            have hnodup_range : ∀ m : ℕ, (List.range m).Nodup := fun m => by
              induction m with
              | zero => simp
              | succ n ih =>
                rw [List.range_succ]
                exact List.Nodup.append ih (List.nodup_singleton n) (by simp [List.mem_range])
            exact List.Nodup.map hinj (hnodup_range k)
        have hdisjoint : ∀ e ∈ CGraph.thetaEdges off [hd], e ∉ CGraph.thetaEdges (off + hd) tl := by
          intro ⟨p1, p2⟩ hp1
          rw [CGraph.mem_thetaEdges_single] at hp1
          by_contra hmem
          have hb2 := CGraph.mem_thetaEdges_bound (off + hd) tl p1 p2 hmem
          rcases hp1 with h | h | h | h
          · rcases h with ⟨rfl, _, _⟩; omega
          · rcases h with ⟨_, rfl, rfl⟩
            omega
          · rcases h with ⟨_, rfl, rfl⟩
            omega
          · rcases h with ⟨h1, rfl, h3⟩
            omega
        exact List.Nodup.append hblk1_nodup ih'.2.2.2 hdisjoint
  have htheta_good := htheta_good_off 2 xs h (by omega)
  have heq : (CGraph.thetaGraph xs).E = (CGraph.thetaEdges 2 xs).length := by
    rw [CGraph.thetaGraph]
    exact ofEdges_E_helper htheta_good.1 htheta_good.2.1 htheta_good.2.2.1 htheta_good.2.2.2
  rw [heq, hlen 2 xs h]

/-- A lollipop on at least three clique vertices contains a triangle. -/
theorem girth_lollipop (m k : ℕ) : (lollipop (m + 3) k).girth = 3 := by
  simp [IsoGraph.lollipop, IsoGraph.girth_mk]
  set n := m + 3 + k
  have hn3 : 3 ≤ n := by omega
  have h1lt : 1 < n := by omega
  have h2lt : 2 < n := by omega
  have hv0 : (0 : Fin n).1 = 0 := by simp
  have hv1 : (1 : Fin n).1 = 1 := by simp [Nat.mod_eq_of_lt h1lt]
  have hv2 : (2 : Fin n).1 = 2 := by simp [Nat.mod_eq_of_lt h2lt]
  have hmem01 : ((0, 1) : (ℕ × ℕ)) ∈ CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k :=
    List.mem_append_left _ (by simp [CGraph.mem_cliqueEdges])
  have hmem12 : ((1, 2) : (ℕ × ℕ)) ∈ CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k :=
    List.mem_append_left _ (by simp [CGraph.mem_cliqueEdges])
  have hmem02 : ((0, 2) : (ℕ × ℕ)) ∈ CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k :=
    List.mem_append_left _ (by simp [CGraph.mem_cliqueEdges])
  have h01 : (CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).Adj (0
      : Fin n) (1 : Fin n) := by
    rw [CGraph.ofEdges_adj_val]
    rw [hv0, hv1]
    exact ⟨by simp, Or.inl hmem01⟩
  have h12 : (CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).Adj (1
      : Fin n) (2 : Fin n) := by
    rw [CGraph.ofEdges_adj_val, hv1, hv2]
    exact ⟨by simp, Or.inl hmem12⟩
  have h20 : (CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).Adj (2
      : Fin n) (0 : Fin n) := by
    rw [CGraph.ofEdges_adj_val, hv2, hv0]
    exact ⟨by simp, Or.inr hmem02⟩
  have : CGraph.lollipop (m + 3) k = CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++
      CGraph.legEdges 0 (m + 3) k) := rfl
  rw [this]
  exact CGraph.girth_eq_three_of_triangle h01 h12 h20

/-- A double star always has a vertex of degree one — a pendant, or an endpoint of the central
edge when there are no pendants. -/
theorem minDeg_doubleStar (m n : ℕ) : minDeg (doubleStar m n) = 1 := by
  simp [IsoGraph.doubleStar, IsoGraph.minDeg]
  apply le_antisymm
  · -- minDeg ≤ 1: exhibit a vertex of degree ≤ 1
    by_cases hm : m = 0
    · by_cases hn : n = 0
      · subst hm; subst hn
        let v : (CGraph.doubleStar 0 0).V := ⟨0, by omega⟩
        have h : (CGraph.doubleStar 0 0).toSimple.degree v = 1 := by native_decide
        exact le_trans (CGraph.minDeg_le_degree _ v) h.le
      · subst hm
        have h2lt : 2 < 2 + n := by omega
        let v : (CGraph.doubleStar 0 n).V := ⟨2, h2lt⟩
        have hadj : ∀ w : (CGraph.doubleStar 0 n).V, (CGraph.doubleStar 0 n).Adj v w = (w = ⟨1,
            by omega⟩) := by
          intro w
          rw [CGraph.doubleStar_adj_val]
          simp [v]
          constructor
          · rintro ⟨hne, h1, _⟩; exact Fin.ext h1
          · rintro rfl; simp; omega
        have hdeg : (CGraph.doubleStar 0 n).toSimple.degree v = 1 := by
          rw [SimpleGraph.degree, CGraph.neighborFinset_eq_nbrs]
          have hnbs : (CGraph.doubleStar 0 n).nbrs v = {⟨1, by omega⟩} := by
            ext w; simp [CGraph.mem_nbrs, hadj]
          rw [hnbs, Finset.card_singleton]
        exact (CGraph.minDeg_le_degree _ v).trans hdeg.le
    · -- m > 0: vertex 2 is pendant attached to 0
      have hm1 : 0 < m := Nat.pos_of_ne_zero hm
      have h2lt : 2 < 2 + m + n := by omega
      let v : (CGraph.doubleStar m n).V := ⟨2, h2lt⟩
      have hdeg : (CGraph.doubleStar m n).toSimple.degree v = 1 := by
        rw [SimpleGraph.degree, CGraph.neighborFinset_eq_nbrs]
        have hnbs : (CGraph.doubleStar m n).nbrs v = {⟨0, by omega⟩} := by
          ext w
          simp [CGraph.mem_nbrs, CGraph.doubleStar_adj_val, v]
          constructor
          · rintro ⟨hne, h | h⟩ <;> exact Fin.ext (by omega)
          · intro hw; subst hw; simp; omega
        rw [hnbs, Finset.card_singleton]
      exact (CGraph.minDeg_le_degree _ v).trans hdeg.le
  · -- 1 ≤ minDeg: every vertex has degree ≥ 1
    apply CGraph.le_minDeg_of_forall (⟨0, by omega⟩ : (CGraph.doubleStar m n).V)
    intro v
    have hvlt : v.1 < 2 + m + n := v.isLt
    have hpos : 0 < (CGraph.doubleStar m n).toSimple.degree v := by
      rw [SimpleGraph.degree_pos_iff_exists_adj]
      by_cases h0 : v.1 = 0
      · exact ⟨⟨1, by omega⟩, by simp [CGraph.doubleStar_adj_val, h0]⟩
      · by_cases h1 : v.1 = 1
        · exact ⟨⟨0, by omega⟩, by simp [CGraph.doubleStar_adj_val, h1]⟩
        · by_cases hlow : v.1 < 2 + m
          · exact ⟨⟨0, by omega⟩,
              by simp [CGraph.doubleStar_adj_val, h0, h1, show 2 ≤ v.1 from by omega, hlow]⟩
          · exact ⟨⟨1, by omega⟩,
              by simp [CGraph.doubleStar_adj_val, h0, h1, show 2 + m ≤ v.1 from by omega]⟩
    omega

/-- The coordinate edges alone already connect the cube. -/
theorem isConnected_foldedCube (n : ℕ) : IsConnected (foldedCube (n + 1)) := by
  simp only [IsoGraph.foldedCube, IsoGraph.isConnected_mk, CGraph.IsConnected]
  have key : ∀ x y : Fin (n + 1) → Bool,
      (CGraph.hypercube (n + 1)).Adj x y → (CGraph.foldedCube (n + 1)).Adj x y := by
    intro x y hadj
    simp only [CGraph.hypercube_adj, CGraph.foldedCube_adj] at hadj ⊢
    have hne : x ≠ y := by
      by_contra hxy; simp [hxy] at hadj
    simp [hne, hadj]
  have hle : (CGraph.hypercube (n + 1)).toSimple ≤ (CGraph.foldedCube (n + 1)).toSimple := by
    intro x y h; rw [CGraph.toSimple_adj]; exact key x y h
  have hconn : (CGraph.hypercube (n + 1)).toSimple.Connected := isConnected_hypercube (n + 1)
  show SimpleGraph.Connected (CGraph.foldedCube (n + 1)).toSimple
  haveI hne : Nonempty (CGraph.foldedCube (n + 1)).V := by
    exact ⟨fun _ => false⟩
  exact SimpleGraph.Connected.mk
    (fun u v => by
      have hreach : (CGraph.hypercube (n + 1)).toSimple.Reachable u v := hconn.preconnected u v
      exact hreach.mono hle)

theorem numComponents_foldedCube (n : ℕ) : (foldedCube (n + 1)).numComponents = 1 :=
  (numComponents_eq_one_iff (foldedCube (n + 1))).mpr (isConnected_foldedCube n)

/-- For odd `n` the antipodal map reverses parity, so the folded cube is bipartite and the two
parity classes are the extremal independent sets. -/
theorem chromNum_foldedCube_odd {n : ℕ} (hn : n % 2 = 1) : (foldedCube n).chromNum = 2 := by
  rw [chromNum_eq_two_iff]
  refine ⟨isBipartite_foldedCube_odd hn, ?_⟩
  rw [foldedCube_def, E_mk]
  have hne' : (fun _ : Fin n => Bool.false) ≠ (fun _ : Fin n => Bool.true) := by
    intro h; exact absurd (congr_fun h ⟨0, Nat.pos_of_ne_zero (by omega)⟩) (by simp)
  have hadj : (CGraph.foldedCube n).Adj (fun _ => false) (fun _ => true) := by
    simp [CGraph.foldedCube_adj, hne']
  have hex : Sym2.mk (fun _ => (false : Bool), fun _ => (true : Bool)) ∈ (CGraph.foldedCube
      n).toSimple.edgeFinset := by
    simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple_adj, hne']
  have hne'' : (CGraph.foldedCube n).toSimple.edgeFinset.Nonempty := ⟨_, hex⟩
  unfold CGraph.E
  exact Finset.card_pos.mpr hne''

/-- A connected regular bipartite graph has a perfect matching, so `α = |V| / 2`. -/
theorem indepNum_foldedCube_odd (m : ℕ) : (foldedCube (2 * m + 1)).indepNum = 2 ^ (2 * m) := by
  have hn : (2 * m + 1) % 2 = 1 := by omega
  have hchi := chromNum_foldedCube_odd hn
  have hchi_iff := chromNum_eq_two_iff.mp hchi
  have hE := hchi_iff.2
  have hVT := isVertexTransitive_foldedCube (2 * m + 1)
  have hV := V_foldedCube (2 * m + 1)
  have h1 := V_le_chromNum_mul_indepNum (foldedCube (2 * m + 1))
  rw [hchi, hV] at h1
  have h2 := two_mul_indepNum_le_V hVT hE
  rw [hV] at h2
  ring_nf at h1 h2 ⊢
  omega

theorem matchNum_foldedCube_odd (m : ℕ) : (foldedCube (2 * m + 1)).matchNum = 2 ^ (2 * m) := by
  -- Upper bound: 2 * matchNum ≤ V = 2^(2*m+1)
  have hUB : 2 * (foldedCube (2 * m + 1)).matchNum ≤ 2 ^ (2 * m + 1) := by
    exact le_trans (two_mul_matchNum_le_V _) (V_foldedCube _).le
  rw [pow_succ] at hUB
  -- Lower bound: exhibit antipodal matching of size 2^(2*m)
  rw [matchNum_eq]
  -- Need: 2^(2*m) ≤ indepNum (lineGraph (foldedCube (2*m+1)))
  -- Lower bound via antipodal-style matching... actually use coordinate edge matching
  -- For each x : Fin (2*m) → Bool, v0 x and v1 x differ in exactly bit 0,
  -- so {v0 x, v1 x} is a coordinate edge (Hamming dist 1) in foldedCube (2*m+1).
  -- These 2^(2*m) edges are pairwise disjoint.
  have hUB2 : indepNum (lineGraph (foldedCube (2 * m + 1))) ≤ 2 ^ (2 * m) := by
    rw [matchNum_eq] at hUB; omega
  have hLB_cgraph : 2 ^ (2 * m) ≤ (CGraph.foldedCube (2 * m + 1)).lineGraph.indepNum := by
    let v0 : (Fin (2 * m) → Bool) → (Fin (2 * m + 1) → Bool) := fun x => Fin.cons false x
    let v1 : (Fin (2 * m) → Bool) → (Fin (2 * m + 1) → Bool) := fun x => Fin.cons true x
    have huv_adj : ∀ x : Fin (2 * m) → Bool, (CGraph.foldedCube (2 * m + 1)).Adj (v0 x) (v1 x) := by
      intro x
      rw [CGraph.foldedCube_adj]
      dsimp [v0, v1]
      have hdiff : (Finset.univ.filter (fun i : Fin (2 * m + 1) =>
          ¬(Fin.cons false x : Fin (2 * m + 1) → Bool) i = (Fin.cons true x : Fin (2 * m + 1) →
              Bool) i)) = {0} := by
        ext i
        simp [Fin.cons]
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      rw [hdiff]
      simp
    let edgeVertex : (Fin (2 * m) → Bool) → (CGraph.lineGraph (CGraph.foldedCube (2 * m +
        1))).V := fun x =>
      ⟨Sym2.mk (v0 x, v1 x), by
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
        exact huv_adj x⟩
    let S : Finset (CGraph.lineGraph (CGraph.foldedCube (2 * m +
        1))).V := Finset.univ.image edgeVertex
    have hv0_inj : Function.Injective v0 := by
      intro x y h; simp [v0] at h; exact h
    have hdisjoint : ∀ x y : (Fin (2 * m) → Bool), x ≠ y →
        ¬∃ v : Fin (2 * m + 1) → Bool, v ∈ (Sym2.mk (v0 x, v1 x) : Sym2 (Fin (2 * m + 1) → Bool)) ∧
          v ∈ (Sym2.mk (v0 y, v1 y) : Sym2 (Fin (2 * m + 1) → Bool)) := by
      intro x y hxy ⟨v, hv1, hv2⟩
      rw [Sym2.mem_iff] at hv1 hv2
      rcases hv1 with rfl | rfl
      · rcases hv2 with h1 | h1
        · exact hxy (hv0_inj h1)
        · have h2 := congr_fun h1 0; simp [v0, v1] at h2
      · rcases hv2 with h1 | h1
        · have h2 := congr_fun h1 0; simp [v0, v1] at h2
        · exact hxy (by simpa [v1] using h1)
    have hS_indep : (CGraph.lineGraph (CGraph.foldedCube (2 * m + 1))).toSimple.IsIndepSet S := by
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
    have hinj : Function.Injective edgeVertex := by
      intro x y hxy
      have hsym2 : Sym2.mk (v0 x, v1 x) = Sym2.mk (v0 y, v1 y) := Subtype.ext_iff.mp hxy
      rcases Sym2.eq_iff.1 hsym2 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hv0_inj h1
      · have h2 := congr_fun h1 0; simp [v0, v1] at h2
    have hS_card : S.card = 2 ^ (2 * m) := by
      rw [Finset.card_image_of_injective _ hinj]
      simp [Finset.card_univ]
    exact hS_card ▸ hS_indep.card_le_indepNum
  have hLB : 2 ^ (2 * m) ≤ indepNum (lineGraph (foldedCube (2 * m + 1))) := by
    show 2 ^ (2 * m) ≤ indepNum (lineGraph (foldedCube (2 * m + 1)))
    rw [show (foldedCube (2 * m + 1) : IsoGraph) = ⟦CGraph.foldedCube (2 * m + 1)⟧ from rfl,
      lineGraph_mk, indepNum_mk]
    exact hLB_cgraph
  exact le_antisymm hUB2 hLB

/-- The junction of a tadpole's cycle and its tail is the only vertex of degree three. -/
theorem maxDeg_tadpole (m k : ℕ) : maxDeg (tadpole (m + 3) (k + 1)) = 3 := by
  rw [tadpole_def, maxDeg_mk]
  -- Show 3 ∈ degMultiset by exhibiting vertex 0
  have hmem : 3 ∈ (CGraph.tadpole (m + 3) (k + 1)).degMultiset := by
    rw [CGraph.mem_degMultiset]
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [← CGraph.card_nbrs_eq_degree]
    -- Characterize the neighbor set of vertex 0
    have hnbrs0 : (CGraph.tadpole (m + 3) (k + 1)).nbrs ⟨0, by omega⟩ =
      {⟨1, by omega⟩, ⟨m + 2, by omega⟩, ⟨m + 3, by omega⟩} := by
      apply Finset.ext
      intro w
      simp [CGraph.nbrs, CGraph.tadpole_adj_val]
      constructor
      · rintro ⟨hne, hw | hw⟩
        · rcases hw with h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inr (Fin.ext h))
        · exact Or.inr (Or.inl (Fin.ext hw))
      · rintro (h | h | h)
        · subst h; simp
        · subst h; simp
        · subst h; simp
    rw [hnbrs0]
    have h12 : (⟨1, by omega⟩ : (CGraph.tadpole (m + 3) (k + 1)).V) ≠ ⟨m + 2, by omega⟩ := by
      intro h; simp at h
    have h13 : (⟨1, by omega⟩ : (CGraph.tadpole (m + 3) (k + 1)).V) ≠ ⟨m + 3, by omega⟩ := by
      intro h; simp at h
    have h23 : (⟨m + 2, by omega⟩ : (CGraph.tadpole (m + 3) (k + 1)).V) ≠ ⟨m + 3, by omega⟩ := by
      intro h; simp at h
    simp [h12, h13, h23]
  have hle : ∀ v : (CGraph.tadpole (m + 3) (k + 1)).V,
      (CGraph.tadpole (m + 3) (k + 1)).toSimple.degree v ≤ 3 := by
    intro v
    rw [← CGraph.card_nbrs_eq_degree]
    -- The neighbor set of v is contained in the union of:
    -- - cycle neighbors (at most 2 vertices in range [0, m+2])
    -- - leg neighbors (at most 2 vertices in range [m+3, m+3+k], plus possibly 0)
    -- We'll show nbrs v ⊆ S for an explicit small S.
    -- Characterize membership in legEdges
    have hleg_mem : ∀ a b : ℕ,
        (a, b) ∈ CGraph.legEdges 0 (m + 3) (k + 1) ↔
          (a = 0 ∧ b = m + 3) ∨ (∃ j < k, a = m + 3 + j ∧ b = m + 3 + j + 1) := by
      intro a b
      rw [CGraph.mem_legEdges]
      simp
      constructor
      · rintro (⟨rfl, rfl, _⟩ | ⟨hle, rfl, hlt⟩)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨a - (m + 3), by omega, by omega, by omega⟩
      · rintro (⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
        · simp
        · exact Or.inr ⟨by omega, rfl, by omega⟩
    -- Characterize adjacency in tadpole
    have hadj_char : ∀ u v : (CGraph.tadpole (m + 3) (k + 1)).V,
        (CGraph.tadpole (m + 3) (k + 1)).Adj u v ↔
          u.1 ≠ v.1 ∧
          ((v.1 = u.1 + 1 ∧ u.1 + 1 < m + 3) ∨ (u.1 + 1 = m + 3 ∧ v.1 = 0) ∨
           (u.1 = v.1 + 1 ∧ v.1 + 1 < m + 3) ∨ (v.1 + 1 = m + 3 ∧ u.1 = 0) ∨
           (u.1 = 0 ∧ v.1 = m + 3) ∨ (v.1 = 0 ∧ u.1 = m + 3) ∨
           (∃ j < k, u.1 = m + 3 + j ∧ v.1 = m + 3 + j + 1) ∨
           (∃ j < k, v.1 = m + 3 + j ∧ u.1 = m + 3 + j + 1) ∨
           (∃ j < k, u.1 = m + 3 + j + 1 ∧ v.1 = m + 3 + j) ∨
           (∃ j < k, v.1 = m + 3 + j + 1 ∧ u.1 = m + 3 + j)) := by
      intro u v
      rw [CGraph.tadpole_adj_val]
      simp only [List.mem_append]
      rw [CGraph.mem_cycleEdges, hleg_mem, CGraph.mem_cycleEdges, hleg_mem]
      aesop
    -- Now bound degree of v
    set i := v.1
    set N := CGraph.nbrs (CGraph.tadpole (m + 3) (k + 1)) v with hN_def
    have hN_char : N = Finset.filter (fun w : (CGraph.tadpole (m + 3) (k + 1)).V =>
        i ≠ w.1 ∧
          ((w.1 = i + 1 ∧ i + 1 < m + 3) ∨ (i + 1 = m + 3 ∧ w.1 = 0) ∨
           (i = w.1 + 1 ∧ w.1 + 1 < m + 3) ∨ (w.1 + 1 = m + 3 ∧ i = 0) ∨
           (i = 0 ∧ w.1 = m + 3) ∨ (w.1 = 0 ∧ i = m + 3) ∨
           (∃ j < k, i = m + 3 + j ∧ w.1 = m + 3 + j + 1) ∨
           (∃ j < k, w.1 = m + 3 + j ∧ i = m + 3 + j + 1) ∨
           (∃ j < k, i = m + 3 + j + 1 ∧ w.1 = m + 3 + j) ∨
           (∃ j < k, w.1 = m + 3 + j + 1 ∧ i = m + 3 + j))
      ) Finset.univ := by
      ext w
      show w ∈ N ↔ w ∈ Finset.filter _ Finset.univ
      simp [hN_def, hadj_char, i]
    -- The .1 map is injective on Fin
    have hinj : Function.Injective (fun w : (CGraph.tadpole (m + 3) (k + 1)).V =>
        w.1) := fun a b h => Fin.ext h
    -- For each region of i, N is contained in an explicit small finset.
    -- Region i = 0: N ⊆ {⟨1,...⟩, ⟨m+2,...⟩, ⟨m+3,...⟩}
    -- Region 0 < i < m+3: N ⊆ {⟨i-1,...⟩, ⟨i+1,...⟩}
    -- Region i = m+3: N ⊆ {⟨0,...⟩, ⟨m+4,...⟩} (if k ≥ 1)
    -- Region m+3 < i < m+3+k: N ⊆ {⟨i-1,...⟩, ⟨i+1,...⟩}
    -- Region i = m+3+k: N ⊆ {⟨i-1,...⟩}
    have hi_valid : i < m + k + 4 := by omega
    -- Get membership from hN_char
    have hmem_filter : ∀ w, w ∈ N ↔
        i ≠ w.1 ∧
          ((w.1 = i + 1 ∧ i + 1 < m + 3) ∨ (i + 1 = m + 3 ∧ w.1 = 0) ∨
           (i = w.1 + 1 ∧ w.1 + 1 < m + 3) ∨ (w.1 + 1 = m + 3 ∧ i = 0) ∨
           (i = 0 ∧ w.1 = m + 3) ∨ (w.1 = 0 ∧ i = m + 3) ∨
           (∃ j < k, i = m + 3 + j ∧ w.1 = m + 3 + j + 1) ∨
           (∃ j < k, w.1 = m + 3 + j ∧ i = m + 3 + j + 1) ∨
           (∃ j < k, i = m + 3 + j + 1 ∧ w.1 = m + 3 + j) ∨
           (∃ j < k, w.1 = m + 3 + j + 1 ∧ i = m + 3 + j)) := by
      intro w; rw [hN_char, Finset.mem_filter]; simp
    -- Bound degree of v by bounding |N|
    -- Use image under .1 to work in ℕ (avoids Fin membership繁琐)
    let f : (CGraph.tadpole (m + 3) (k + 1)).V → ℕ := (·.1)
    have hf_inj : Function.Injective f := hinj
    have hN_card : N.card = (N.image f).card := by
      rw [Finset.card_image_of_injective _ hf_inj]
    rw [hN_card]
    have himage : ∀ x, x ∈ N.image f ↔ ∃ w ∈ N, f w = x := by simp [Finset.mem_image]
    by_cases hi0 : i = 0;
    · -- Region i = 0: image N ⊆ {1, m+2, m+3}
      rw [hi0] at hmem_filter
      have himagesub : N.image f ⊆ ({1, m + 2, m + 3} : Finset ℕ) := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := himage _ |>.mp hx
        rw [hmem_filter] at hw
        obtain ⟨hne, hw1⟩ := hw
        simp only [Nat.zero_add] at hw1
        rcases hw1 with h | h | h | h | h | h | ⟨j, hj, hj1, hj2⟩ | ⟨j, hj, hj1, hj2⟩ | ⟨j, hj,
            hj1, hj2⟩ | ⟨j, hj, hj1, hj2⟩
        · rw [show f w = 1 from h.1]; simp
        · exfalso; omega
        · exfalso; omega
        · rw [show f w = m + 2 from by simp [f]; omega]; simp
        · rw [show f w = m + 3 from h.2]; simp
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      exact le_trans (Finset.card_mono himagesub) (by
        have : ({1, m + 2, m + 3} : Finset ℕ).card ≤ 3 := by
          calc ({1, m + 2, m + 3} : Finset ℕ).card
              ≤ ({m + 2, m + 3} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
            _ ≤ (({(m + 3)} : Finset ℕ).card + 1) + 1 := by
                exact Nat.add_le_add_right (Finset.card_insert_le _ _) _
            _ ≤ (1 + 1) + 1 := by
                exact Nat.add_le_add_right (Finset.card_singleton _ ▸ le_rfl) _
            _ = 3 := by omega
        exact this)
    · -- i ≠ 0: image N ⊆ {0, i-1, i+1}
      have himagesub : N.image f ⊆ ({0, i - 1, i + 1} : Finset ℕ) := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := himage _ |>.mp hx
        rw [hmem_filter] at hw
        obtain ⟨hne, hw1⟩ := hw
        rcases hw1 with h | h | h | h | h | h | ⟨j, hj, hj1, hj2⟩ | ⟨j, hj, hj1, hj2⟩ | ⟨j, hj,
            hj1, hj2⟩ | ⟨j, hj, hj1, hj2⟩
        · rw [show f w = i + 1 from h.1]; simp
        · have hf0 : (f w : ℕ) = 0 := by show (w.1 : ℕ) = 0; exact h.2
          rw [hf0]; simp
        · rw [show f w = i - 1 from by simp [f]; omega]; simp
        · exfalso; exact hi0 h.2
        · exfalso; exact hi0 h.1
        · have hf0 : (f w : ℕ) = 0 := by show (w.1 : ℕ) = 0; exact h.1
          rw [hf0]; simp
        · rw [show f w = i + 1 from by simp [f]; omega]; simp
        · rw [show f w = i - 1 from by simp [f]; omega]; simp
        · rw [show f w = i - 1 from by simp [f]; omega]; simp
        · rw [show f w = i + 1 from by simp [f]; omega]; simp
      exact le_trans (Finset.card_mono himagesub) (by
        have : ({0, i - 1, i + 1} : Finset ℕ).card ≤ 3 := by
          have := Finset.card_insert_le 0 {i - 1, i + 1}
          have := Finset.card_insert_le (i - 1) {(i + 1)}
          simp [Finset.card_singleton] at *
          omega
        exact this)
  exact CGraph.maxDeg_eq_of_degMultiset hmem (fun d hd => by
    obtain ⟨v, hv⟩ := CGraph.mem_degMultiset.1 hd
    rw [← hv]
    exact hle v)

/-- The two centres of a double star have degrees `m + 1` and `n + 1`; every other vertex is
pendant. -/
theorem maxDeg_doubleStar (m n : ℕ) : maxDeg (doubleStar m n) = max m n + 1 := by
  change (CGraph.doubleStar m n).maxDeg = max m n + 1
  let h0 : (0 : ℕ) < 2 + m + n := by omega
  let h1 : (1 : ℕ) < 2 + m + n := by omega
  let f0 : Fin m → Fin (2 + m + n) := fun i => ⟨2 + (i : ℕ), by omega⟩
  let f1 : Fin n → Fin (2 + m + n) := fun i => ⟨2 + m + (i : ℕ), by omega⟩
  have hadj : ∀ (v w : (CGraph.doubleStar m n).V),
      (CGraph.doubleStar m n).Adj v w =
      (v.1 ≠ w.1 ∧
        (((v.1 = 0 ∧ w.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ w.1 ∧ w.1 < 2 + m) ∨
            (v.1 = 1 ∧ 2 + m ≤ w.1 ∧ w.1 < 2 + m + n)) ∨
          ((w.1 = 0 ∧ v.1 = 1) ∨ (w.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + m) ∨
            (w.1 = 1 ∧ 2 + m ≤ v.1 ∧ v.1 < 2 + m + n)))) := by
    intro v w
    simp only [CGraph.doubleStar, CGraph.ofEdges_adj_val, CGraph.mem_doubleStarEdges]
  -- neighborFinset for vertex 0
  have hneighborFinset_0 : (CGraph.doubleStar m n).toSimple.neighborFinset ⟨0, h0⟩ =
      {⟨1, h1⟩} ∪ Finset.image f0 Finset.univ := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    have hadj0w := hadj ⟨0, h0⟩ w
    rw [CGraph.toSimple_adj, hadj0w]
    simp
    constructor
    · rintro ⟨hne, hw | ⟨hge, hlt⟩⟩
      · left; exact Fin.ext_iff.mpr hw
      · right
        let a : Fin m := ⟨w.val - 2, by omega⟩
        have hv : (a : ℕ) = w.val - 2 := rfl
        have hlt2 : w.val - 2 < 2 + m + n := by omega
        have : f0 a = w := by
          ext; dsimp [f0]; rw [hv]; omega
        exact ⟨a, this⟩
    · rintro (rfl | ⟨a, ha⟩)
      · simp
      · rw [show w = ⟨2 + (a : ℕ), by omega⟩ from ha.symm]
        simp; omega
  -- neighborFinset for vertex 1
  have hneighborFinset_1 : (CGraph.doubleStar m n).toSimple.neighborFinset ⟨1, h1⟩ =
      {⟨0, h0⟩} ∪ Finset.image f1 Finset.univ := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    have hadj1w := hadj ⟨1, h1⟩ w
    rw [CGraph.toSimple_adj, hadj1w]
    simp
    constructor
    · rintro ⟨hne, hw | hw | ⟨hweq1, _, _⟩⟩
      · right
        let a : Fin n := ⟨w.val - (2 + m), by omega⟩
        have hv : (a : ℕ) = w.val - (2 + m) := rfl
        have hlt2 : w.val - (2 + m) < 2 + m + n := by omega
        have : f1 a = w := by
          ext; dsimp [f1]; rw [hv]; omega
        exact ⟨a, this⟩
      · left; exact hw
      · exfalso; omega
    · rintro (rfl | ⟨a, ha⟩)
      · simp
      · rw [show w = ⟨2 + m + (a : ℕ), by omega⟩ from ha.symm]
        simp
        omega
  -- degrees of vertices 0 and 1
  have hdisjoint_0 :
      Disjoint ({⟨1, h1⟩} : Finset (CGraph.doubleStar m n).V) (Finset.image f0 Finset.univ) := by
    rw [Finset.disjoint_left]
    simp [Finset.mem_image, f0]
    intro a ha
    have := congr_arg (fun x : Fin (2+m+n) => x.val) ha
    simp at this
    omega
  have hinj_0 : Function.Injective f0 := by
    intro i j h
    have := congr_arg (fun x : Fin (2 + m + n) => x.val) h
    simp [f0] at this
    exact Fin.ext this
  have himage_card_0 : (Finset.image f0 Finset.univ).card = m := by
    rw [Finset.card_image_of_injective Finset.univ hinj_0]
    simp [Finset.card_univ]
  have hdeg_0 : (CGraph.doubleStar m n).toSimple.degree ⟨0, h0⟩ = m + 1 := by
    rw [SimpleGraph.degree, hneighborFinset_0, Finset.card_union_of_disjoint hdisjoint_0,
        himage_card_0]
    rw [Finset.card_singleton]
    omega
  have hdisjoint_1 :
      Disjoint ({⟨0, h0⟩} : Finset (CGraph.doubleStar m n).V) (Finset.image f1 Finset.univ) := by
    rw [Finset.disjoint_left]
    simp [Finset.mem_image, f1]
    intro a ha
    have := congr_arg (fun x : Fin (2+m+n) => x.val) ha
    simp at this
  have hinj_1 : Function.Injective f1 := by
    intro i j h
    have := congr_arg (fun x : Fin (2 + m + n) => x.val) h
    simp [f1] at this
    exact Fin.ext this
  have himage_card_1 : (Finset.image f1 Finset.univ).card = n := by
    rw [Finset.card_image_of_injective Finset.univ hinj_1]
    simp [Finset.card_univ]
  have hdeg_1 : (CGraph.doubleStar m n).toSimple.degree ⟨1, h1⟩ = n + 1 := by
    rw [SimpleGraph.degree, hneighborFinset_1, Finset.card_union_of_disjoint hdisjoint_1,
        himage_card_1]
    rw [Finset.card_singleton]
    omega
  have hadj_simple : ∀ v w, (CGraph.doubleStar m n).toSimple.Adj v w ↔
      (v.1 ≠ w.1 ∧
        (((v.1 = 0 ∧ w.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ w.1 ∧ w.1 < 2 + m) ∨
            (v.1 = 1 ∧ 2 + m ≤ w.1 ∧ w.1 < 2 + m + n)) ∨
          ((w.1 = 0 ∧ v.1 = 1) ∨ (w.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + m) ∨
            (w.1 = 1 ∧ 2 + m ≤ v.1 ∧ v.1 < 2 + m + n)))) := by
    intro v w
    rw [CGraph.toSimple_adj]
    exact iff_of_eq (hadj v w)
  have hdeg_le_one : ∀ v : (CGraph.doubleStar m n).V, v ≠ ⟨0, h0⟩ → v ≠ ⟨1, h1⟩ →
      (CGraph.doubleStar m n).toSimple.degree v ≤ 1 := by
    intro v hv0 hv1
    rw [SimpleGraph.degree]
    have hv0' : (v.val : ℕ) ≠ 0 := by intro h; exact hv0 (Fin.ext h)
    have hv1' : (v.val : ℕ) ≠ 1 := by intro h; exact hv1 (Fin.ext h)
    have hvlt : (v.val : ℕ) < 2 + m + n := v.2
    have hsub_one : ∀ w, (CGraph.doubleStar m n).toSimple.Adj v w → w = ⟨0, h0⟩ ∨ w = ⟨1, h1⟩ := by
      intro w hw
      rw [hadj_simple] at hw
      obtain ⟨hne, hwCases⟩ := hw
      -- All 6 cases in hwCases give: w.val = 0 ∨ w.val = 1 (using hv0', hv1' to eliminate v-val
      -- cases)
      have hw0_or_1 : w.val = 0 ∨ w.val = 1 := by
        cases hwCases with
        | inl h =>
          rcases h with h1 | h1 | h1
          · exfalso; exact hv0' h1.1
          · exfalso; exact hv0' h1.1
          · exfalso; exact hv1' h1.1
        | inr h =>
          rcases h with h1 | h1 | h1
          · left; exact h1.1
          · left; exact h1.1
          · right; exact h1.1
      rcases hw0_or_1 with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    by_cases hcase : v.val < 2 + m
    · have : SimpleGraph.neighborFinset (CGraph.doubleStar m n).toSimple v ⊆ {⟨0, h0⟩} := by
        intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        rcases hsub_one w hw with rfl | rfl
        · exact Finset.mem_singleton_self _
        · have hw2 := hadj_simple v ⟨1, h1⟩ |>.mp hw
          have : (⟨1, h1⟩ : Fin (2 + m + n)).val = 1 := rfl
          rw [this] at hw2
          omega
      exact Finset.card_le_card this
    · push_neg at hcase
      have : SimpleGraph.neighborFinset (CGraph.doubleStar m n).toSimple v ⊆ {⟨1, h1⟩} := by
        intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        rcases hsub_one w hw with rfl | rfl
        · have hw2 := hadj_simple v ⟨0, h0⟩ |>.mp hw
          have : (⟨0, h0⟩ : Fin (2 + m + n)).val = 0 := rfl
          rw [this] at hw2
          omega
        · exact Finset.mem_singleton_self _
      exact Finset.card_le_card this
  apply CGraph.maxDeg_eq_of_degMultiset
  · -- max m n + 1 ∈ degMultiset
    rw [CGraph.mem_degMultiset]
    by_cases hmn : m ≥ n
    · exact ⟨⟨0, h0⟩, by rw [hdeg_0]; simp [hmn]⟩
    · push_neg at hmn
      exact ⟨⟨1, h1⟩, by rw [hdeg_1]; simp [show max m n = n from max_eq_right (le_of_lt hmn)]⟩
  · -- all degrees ≤ max m n + 1
    intro d hd
    rw [CGraph.mem_degMultiset] at hd
    obtain ⟨v, hv⟩ := hd
    by_cases hv0 : v = ⟨0, h0⟩
    · subst hv0; linarith [hdeg_0, le_max_left m n]
    · by_cases hv1 : v = ⟨1, h1⟩
      · subst hv1; linarith [hdeg_1, le_max_right m n]
      · rw [← hv]
        exact le_trans (hdeg_le_one v hv0 hv1) (by omega)

/-- The clique a lollipop is built from is its largest. -/
theorem cliqueNum_lollipop (m k : ℕ) : (lollipop (m + 2) k).cliqueNum = m + 2 := by
  simp only [IsoGraph.lollipop_def, IsoGraph.cliqueNum_mk]
  -- Work at CGraph level
  let G : CGraph := CGraph.lollipop (m + 2) k
  -- Helper: bound all clique sizes
  let bdd : BddAbove {n : ℕ | ∃ s : Finset G.V, G.toSimple.IsNClique n s} :=
    ⟨FinEnum.card G.V, fun n hn => by
      obtain ⟨s, hs⟩ := hn
      exact hs.card_eq ▸ FinEnum.card_le s⟩
  have hnonempty : ({n : ℕ | ∃ s : Finset G.V, G.toSimple.IsNClique n s}).Nonempty :=
    ⟨0, ∅, by simp⟩
  have hlower : (m + 2 : ℕ) ≤ G.cliqueNum := by
    unfold CGraph.cliqueNum SimpleGraph.cliqueNum
    apply le_csSup bdd
    let emb : Fin (m + 2) → G.V := fun i => ⟨i.val, by omega⟩
    let s := Finset.image emb Finset.univ
    have hemb_inj : Function.Injective emb := by
      intro a b h
      have := congr_arg Fin.val h
      simp [emb] at this
      exact Fin.ext this
    have hs_card : s.card = m + 2 := by
      simp [s, Finset.card_image_of_injective _ hemb_inj, Finset.card_univ]
    have hs_clique : G.toSimple.IsClique (s : Set G.V) := by
      intro u hu v hv huv
      simp [s] at hu hv
      obtain ⟨au, _, rfl⟩ := hu
      obtain ⟨av, _, rfl⟩ := hv
      change (CGraph.ofEdges (m + 2 + k) (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges 0 (m + 2)
          k)).Adj ⟨au.val, by omega⟩ ⟨av.val, by omega⟩ = true
      rw [CGraph.ofEdges_adj_val]
      refine ⟨?_, ?_⟩
      · intro heq; exact huv (Fin.ext heq)
      · rcases lt_or_gt_of_ne (show au.val ≠ av.val from fun heq => huv (Fin.ext heq)) with h | h
        · left; exact List.mem_append_left _ (CGraph.mem_cliqueEdges _ _ _ |>.mpr ⟨h, av.2⟩)
        · right; exact List.mem_append_left _ (CGraph.mem_cliqueEdges _ _ _ |>.mpr ⟨h, au.2⟩)
    exact ⟨s, ⟨hs_clique, hs_card⟩⟩
  have hcolorable : G.toSimple.Colorable (m + 2) := by
    let color : Fin (m + 2 + k) → Fin (m + 2) := fun v =>
      if h : v.val < m + 2 then ⟨v.val, by omega⟩
      else if ((v.val - (m + 2)) % 2) = 0 then ⟨1, by omega⟩
      else ⟨0, by omega⟩
    -- Key lemma: consecutive leg vertices (as Fin) have different colors
    have leg_diff : ∀ (p : Fin (m + 2 + k)) (hp_bound : p.val + 1 < m + 2 + k),
        m + 2 ≤ p.val → color p ≠ color ⟨p.val + 1, hp_bound⟩ := by
      intro p hp_bound hp
      show color p ≠ color ⟨p.val + 1, hp_bound⟩
      unfold color
      have hnot_lt : ¬(p.val < m + 2) := not_lt.mpr hp
      have hnot_lt2 : ¬(p.val + 1 < m + 2) := by omega
      simp only [hnot_lt, hnot_lt2]
      set off := p.val - (m + 2)
      have : (p.val + 1 : ℕ) - (m + 2) = off + 1 := by omega
      have : (p.val : ℕ) - (m + 1) = off + 1 := by omega
      simp [*]
      rcases Nat.mod_two_eq_zero_or_one off with h | h <;> simp [h, Nat.add_mod]
    have colorable_all : ∀ (u v : Fin (m + 2 + k)), G.Adj u v → color u ≠ color v := by
      intro u v huv
      change (CGraph.ofEdges (m + 2 + k) (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges 0 (m + 2)
          k)).Adj u v at huv
      rw [CGraph.ofEdges_adj_val] at huv
      rcases huv with ⟨hne, heng | heng⟩
      clear G hlower bdd hnonempty
      · rw [List.mem_append] at heng
        rcases heng with h | h
        · -- clique edge: u < v < m+2
          have hclique := (CGraph.mem_cliqueEdges _ _ _ |>.mp h)
          have hvll : v.val < m + 2 := hclique.2
          have hull_u : u.val < m + 2 := by omega
          simp [color, hull_u, hvll]
          intro heq
          exact hne (congr_arg Fin.val (Fin.val_inj.mp heq))
        · -- leg edge (u, v): either (0, m+2) or (p, p+1)
          rw [CGraph.mem_legEdges] at h
          rcases h with h0 | hpath
          · obtain ⟨hu0, hv0, hk⟩ := h0
            simp [color, hu0, hv0]
          · obtain ⟨hu_ge, hv_eq, hu_lt⟩ := hpath
            have hv_fin : v = ⟨u.val + 1, by omega⟩ := by
              apply Fin.ext; simp; omega
            rw [hv_fin]
            exact leg_diff u hu_lt hu_ge
      · rw [List.mem_append] at heng
        rcases heng with h | h
        · -- clique edge (v, u): v < u < m+2
          have hclique_vu := (CGraph.mem_cliqueEdges _ _ _ |>.mp h)
          have hvull : v.val < m + 2 := by omega
          have hull_u : u.val < m + 2 := hclique_vu.2
          simp [color, hvull, hull_u]
          intro heq
          exact hne (congr_arg Fin.val (Fin.val_inj.mp heq))
        · -- leg edge (v, u): v=p, u=p+1
          rw [CGraph.mem_legEdges] at h
          rcases h with h0 | hpath
          · obtain ⟨hv0, hu0, hk⟩ := h0
            simp [color, hv0, hu0]
          · obtain ⟨hv_ge, hu_eq, hv_lt⟩ := hpath
            have hu_fin : u = ⟨v.val + 1, by omega⟩ := by
              apply Fin.ext; simp; omega
            rw [hu_fin]
            exact (leg_diff v hv_lt hv_ge).symm
    exact ⟨SimpleGraph.Coloring.mk color
        (by intro u v huv; exact colorable_all u v (by rw [CGraph.toSimple_adj] at huv; exact huv))⟩
  have hchrom : G.chromNum ≤ m + 2 := by
    rw [CGraph.chromNum_le_iff_colorable]
    exact hcolorable
  have hupper : G.cliqueNum ≤ m + 2 :=
    le_trans (CGraph.cliqueNum_le_chromNum G) hchrom
  exact le_antisymm hupper hlower

/-- Greedily colouring the tail of a lollipop needs no colour beyond the clique's. -/
theorem chromNum_lollipop (m k : ℕ) : (lollipop (m + 2) k).chromNum = m + 2 := by
  simp [IsoGraph.lollipop, IsoGraph.chromNum_mk]
  rw [CGraph.chromNum_eq_iff]
  -- We need: Colorable (m+2) and ∀ m', Colorable m' → m+2 ≤ m'
  constructor
  · -- Colorable with m+2 colors
    have : (m + 2) ≥ 2 := by omega
    -- Define the coloring: clique vertices get color = their index, path vertices get alternating
    -- colors 1,2
    let f : Fin (m + 2 + k) → Fin (m + 2) := fun v =>
      if h : v.val < m + 2 then ⟨v.val, by omega⟩
      else ⟨1 - ((v.val - (m + 2)) % 2), by omega⟩
    have hproper : ∀ {u v : Fin (m + 2 + k)},
        (CGraph.ofEdges (m + 2 + k) (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges 0 (m + 2)
            k)).Adj u v = true →
        f u ≠ f v := by
      intro u v huv
      rw [CGraph.ofEdges_adj_val] at huv
      obtain ⟨hne, huv' | huv'⟩ := huv
      · -- edge (u, v)
        rw [List.mem_append] at huv'
        rcases huv' with hu' | hv'
        · -- u,v in clique
          rw [CGraph.mem_cliqueEdges] at hu'
          obtain ⟨hlt, hb⟩ := hu'
          simp [f, show (u : ℕ) < m + 2 from hlt.trans hb, show (v : ℕ) < m + 2 from hb]
          exact hne
        · -- edge in legEdges
          rw [CGraph.mem_legEdges] at hv'
          rcases hv' with (⟨hu0, hvleg, hkpos⟩ | ⟨humble, hv_eq, hvbound⟩)
          · -- (0, m+2): f 0 = 0, f (m+2) = 1 - 0 = 1
            have hu0' : u = 0 := Fin.ext hu0
            have hvleg' : v = ⟨m + 2, by omega⟩ := Fin.ext hvleg
            simp [f, hu0', hvleg']
          · -- (u, u+1) in path: both ≥ m+2, offsets j and j+1 have different parities
            have hu_ge : m + 2 ≤ (u : ℕ) := humble
            have hv_eq' : (v : ℕ) = (u : ℕ) + 1 := hv_eq
            simp [f, show ¬((u : ℕ) < m + 2) from by omega,
                  show ¬((v : ℕ) < m + 2) from by omega]
            rw [hv_eq']
            set j : ℕ := (u : ℕ) - (m + 2)
            simp [show (↑u + 1 - (m + 2) : ℕ) = j + 1 from by omega]
            have hm2 : 2 ≤ m + 2 := this
            rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega
      · -- edge (v, u): handle symmetrically
        rw [List.mem_append] at huv'
        rcases huv' with hv' | hu'
        · rw [CGraph.mem_cliqueEdges] at hv'
          obtain ⟨hlt, hb⟩ := hv'
          simp [f, show (v : ℕ) < m + 2 from hlt.trans hb, show (u : ℕ) < m + 2 from hb]
          exact hne
        · rw [CGraph.mem_legEdges] at hu'
          rcases hu' with (⟨hu0, hvleg, hkpos⟩ | ⟨humble, hu_eq, hvbound⟩)
          · -- (m+2, 0): f (m+2) = 1, f 0 = 0
            have hv0' : v = 0 := Fin.ext hu0
            have huleg' : u = ⟨m + 2, by omega⟩ := Fin.ext hvleg
            simp [f, hv0', huleg']
          · -- (v, v+1) in path swapped: u = v+1, both ≥ m+2
            have hv_ge : m + 2 ≤ (v : ℕ) := humble
            simp [f, show ¬((v : ℕ) < m + 2) from by omega,
                  show ¬((u : ℕ) < m + 2) from by omega]
            rw [hu_eq]
            set j : ℕ := (v : ℕ) - (m + 2)
            simp [show (↑v + 1 - (m + 2) : ℕ) = j + 1 from by omega]
            have hm2 : 2 ≤ m + 2 := this
            rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega
    unfold CGraph.toSimple
    show SimpleGraph.Colorable _ _
    refine ⟨SimpleGraph.Coloring.mk f (fun {u v} huv ↦ hproper ?_)⟩
    simp [CGraph.lollipop] at huv
    exact huv
  · -- Lower bound: lollipop contains a clique of size m+2, so chromNum ≥ m+2
    have hlb : (m + 2 : ℕ) ≤ (CGraph.lollipop (m + 2) k).chromNum := by
      have hchrom_le : (CGraph.complete (m + 2)).toSimple.chromaticNumber ≤ (CGraph.lollipop (m +
          2) k).toSimple.chromaticNumber := by
        apply SimpleGraph.chromaticNumber_mono_of_hom
        refine ⟨Fin.castLE (by omega : m + 2 ≤ m + 2 + k), fun {a b} hab ↦ ?_⟩
        simp only [CGraph.lollipop, CGraph.toSimple, CGraph.ofEdges_adj_val]
        have hne : a.val ≠ b.val := by
          intro he
          have : a = b := Fin.ext he
          simp [CGraph.complete, this] at hab
        have ha : a.val < m + 2 := a.isLt
        have hb : b.val < m + 2 := b.isLt
        let f : Fin (m + 2) → Fin (m + 2 + k) := Fin.castLE (by omega : m + 2 ≤ m + 2 + k)
        have hne2 : (f a).val ≠ (f b).val := by
          simp [f, Fin.castLE]; exact hne
        have hclique : ((f a).val, (f b).val) ∈ CGraph.cliqueEdges (m + 2) ∨
          ((f b).val, (f a).val) ∈ CGraph.cliqueEdges (m + 2) := by
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · left; rw [CGraph.mem_cliqueEdges]; exact ⟨hlt, hb⟩
          · right; rw [CGraph.mem_cliqueEdges]; exact ⟨hlt, ha⟩
        exact ⟨hne2, Or.elim hclique (fun h => Or.inl (List.mem_append_left _ h)) (fun h => Or.inr
            (List.mem_append_left _ h))⟩
      rw [CGraph.complete_toSimple, SimpleGraph.chromaticNumber_top,
          ← FinEnum.card_eq_fintypeCard, CGraph.card_complete] at hchrom_le
      rw [CGraph.chromNum]
      exact ENat.toNat_le_toNat hchrom_le (CGraph.chromaticNumber_ne_top _)
    intro m_1 hm_1
    exact le_trans hlb (CGraph.chromNum_le_iff_colorable.mpr hm_1)

/-- Every pendant of a double star, and nothing else. -/
theorem indepNum_doubleStar (m n : ℕ) :
    (doubleStar (m + 1) (n + 1)).indepNum = m + n + 2 := by
  -- Work at CGraph level
  set G := CGraph.doubleStar (m + 1) (n + 1)
  -- V = m + n + 4
  have hV : FinEnum.card G.V = m + n + 4 := by
    simp [G, CGraph.card_doubleStar]; omega
  -- Two disjoint edges: (0,2) and (1, m+3)
  -- Any vertex cover needs ≥ 2 vertices, so coverNum ≥ 2, so indepNum ≤ V - 2 = m+n+2
  -- Also pendants (≥2) form indep set of size m+n+2, so indepNum ≥ m+n+2
  -- Key CGraph facts work at toSimple level
  -- Step A: Indep set of size m+n+2 (pendants with val ≥ 2)
  let s : Finset G.V := Finset.univ.filter (fun v : G.V => 2 ≤ v.1)
  have hs_card : s.card = m + n + 2 := by
    have heq : s = Finset.image (fun i : Fin (m + n + 2) => ⟨i.val + 2, by omega⟩ : Fin (m + n + 2)
        → G.V) (Finset.univ : Finset (Fin (m + n + 2))) := by
      ext v
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hv2
        exact ⟨⟨v.1 - 2, by omega⟩, Fin.ext (Nat.sub_add_cancel hv2)⟩
      · rintro ⟨i, rfl⟩
        simp
    rw [heq]
    rw [Finset.card_image_of_injective _ (fun i j h => by
      have := congr_arg Fin.val h; simp at this; exact Fin.ext this)]
    simp
  have hs_indep : G.toSimple.IsIndepSet (s : Set G.V) := by
    intro v hv w hw hvw
    simp [s] at hv hw
    rw [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
    omega
  have hindep_ge : m + n + 2 ≤ G.indepNum := by
    rw [← hs_card]
    exact hs_indep.card_le_indepNum
  -- Step B: coverNum ≥ 2 (disjoint edges (0,2) and (1, m+3))  
  have h_cover_02 : G.toSimple.Adj ⟨0, by omega⟩ ⟨2, by omega⟩ := by
    simp [G, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
  have h_cover_1_m3 : G.toSimple.Adj ⟨1, by omega⟩ ⟨2 + (m + 1), by omega⟩ := by
    simp [G, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]; omega
  have h_disjoint : (⟨0, by omega⟩ : G.V) ≠ (⟨1, by omega⟩ : G.V) ∧
      (⟨0, by omega⟩ : G.V) ≠ (⟨2 + (m + 1), by omega⟩ : G.V) ∧
      (⟨2, by omega⟩ : G.V) ≠ (⟨1, by omega⟩ : G.V) ∧
      (⟨2, by omega⟩ : G.V) ≠ (⟨2 + (m + 1), by omega⟩ : G.V) := by
    simp [Fin.ext_iff]; omega
  set a : G.V := ⟨0, by omega⟩
  set b : G.V := ⟨2, by omega⟩
  set c : G.V := ⟨1, by omega⟩
  set d : G.V := ⟨2 + (m + 1), by omega⟩
  have hab : G.toSimple.Adj a b := h_cover_02
  have hcd : G.toSimple.Adj c d := h_cover_1_m3
  have hdad : a ≠ b ∧ a ≠ d ∧ a ≠ c ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congr_arg Fin.val h <;> simp [a, b, c,
        d] at this <;> omega
  have hge_pair : ∀ (u v : G.V), u ≠ v → 2 ≤ ({u, v} : Set G.V).encard := by
    intro u v huv; rw [Set.encard_pair huv]
  have le_two_of_mem {C : Set G.V} {u v : G.V} (huv : u ≠ v) (hu : u ∈ C) (hv : v ∈
      C) : 2 ≤ C.encard := by
    exact le_trans (hge_pair u v huv) (Set.encard_mono (Set.insert_subset_iff.mpr ⟨hu,
        Set.singleton_subset_iff.mpr hv⟩))
  have hcover_ge_enat : 2 ≤ G.toSimple.vertexCoverNum := by
    have hvc_lower : ∀ C : Set G.V, G.toSimple.IsVertexCover C → 2 ≤ C.encard := by
      intro C hC
      have ha_or_b : a ∈ C ∨ b ∈ C := hC hab
      have hc_or_d : c ∈ C ∨ d ∈ C := hC hcd
      rcases ha_or_b with ha | hb <;> rcases hc_or_d with hc | hd
      · exact le_trans (hge_pair a c hdad.2.2.1) (Set.encard_mono (Set.insert_subset_iff.mpr ⟨ha,
          Set.singleton_subset_iff.mpr hc⟩))
      · exact le_trans (hge_pair a d hdad.2.1) (Set.encard_mono (Set.insert_subset_iff.mpr ⟨ha,
          Set.singleton_subset_iff.mpr hd⟩))
      · exact le_trans (hge_pair b c hdad.2.2.2.1) (Set.encard_mono (Set.insert_subset_iff.mpr ⟨hb,
          Set.singleton_subset_iff.mpr hc⟩))
      · exact le_trans (hge_pair b d hdad.2.2.2.2.1) (Set.encard_mono (Set.insert_subset_iff.mpr
          ⟨hb, Set.singleton_subset_iff.mpr hd⟩))
    apply le_csInf
    · exact ⟨_, ⟨Set.univ, rfl⟩⟩
    · rintro _ ⟨C, rfl⟩
      by_cases hC : G.toSimple.IsVertexCover C
      · simp [hC]
        exact hvc_lower C hC
      · simp [hC]

  have hcover_ge : 2 ≤ G.coverNum := by
    have hfin : G.toSimple.vertexCoverNum ≠ ⊤ := by
      have hcov : G.toSimple.IsVertexCover (Set.univ : Set
          G.V) := fun x y _ => Or.inl (Set.mem_univ x)
      have h1 := hcov.vertexCoverNum_le
      have hne : (Set.univ : Set G.V).encard ≠ ⊤ := by simp [Set.encard_univ]
      intro h; apply hne; exact le_antisymm le_top (h ▸ h1)
    unfold CGraph.coverNum
    apply ENat.toNat_le_toNat hcover_ge_enat hfin
  
  -- Step C: Combine
  have hadd : G.coverNum + G.indepNum = FinEnum.card G.V :=
    CGraph.coverNum_add_indepNum G
  rw [hV] at hadd
  show G.indepNum = m + n + 2
  omega

/-- A cycle with a path glued to it stays connected. -/
theorem isConnected_tadpole (m k : ℕ) : IsConnected (tadpole (m + 3) k) := by
  unfold IsoGraph.tadpole
  rw [IsoGraph.isConnected_mk]
  show CGraph.IsConnected _
  simp only [CGraph.IsConnected]
  haveI : Nonempty (CGraph.tadpole (m + 3) k).V := by
    show Nonempty (Fin (m + 3 + k))
    exact ⟨0, by omega⟩
  apply SimpleGraph.Connected.mk
  · -- Preconnected: use reachability from 0
    have hreach : ∀ (v : Fin (m + 3 + k)),
        (CGraph.tadpole (m + 3) k).toSimple.Reachable
          (⟨0, by omega⟩ : Fin (m + 3 + k)) v := by
      intro v
      by_cases hv : (v : ℕ) < m + 3
      · -- cycle part: reach via forward cycle edges 0→1→...→v
        let vi := (v : ℕ)
        -- Reachability to all cycle vertices by induction on index
        have hall : ∀ (i : ℕ) (hi : i < m + 3),
            (CGraph.tadpole (m + 3) k).toSimple.Reachable
              (⟨0, by omega⟩ : Fin (m + 3 + k)) (⟨i, by omega⟩ : Fin (m + 3 + k)) := by
          intro i hi
          induction i with
          | zero => exact SimpleGraph.Reachable.refl _
          | succ j ih =>
            have ihj : ∀ (hj : j < m + 3), (CGraph.tadpole (m + 3) k).toSimple.Reachable
                (⟨0, by omega⟩ : Fin (m + 3 + k)) (⟨j, by omega⟩ : Fin (m + 3 + k)) := ih
            have hj_lt_m3 : j + 1 < m + 3 := hi
            have ihj' := ihj (by omega)
            have hadj : (CGraph.tadpole (m + 3) k).Adj ⟨j, by omega⟩ ⟨j + 1, by omega⟩ := by
              rw [CGraph.tadpole_adj_val]
              simp only []
              refine ⟨by omega, Or.inl ?_⟩
              rw [List.mem_append]
              exact Or.inl ((CGraph.mem_cycleEdges (m + 3) j (j + 1)).mpr
                (Or.inl ⟨rfl, by omega⟩))
            obtain ⟨w⟩ := ihj'
            exact ⟨w.concat hadj⟩
        exact hall vi (by omega)
      · -- tail part: reach via leg edges 0→m+3→m+4→...→v
        have hk_pos : 0 < k := by omega
        -- Helper: show (0, m+3) is in legEdges 0 (m+3) k
        have hleg0 : (0, m + 3) ∈ CGraph.legEdges 0 (m + 3) k := by
          rw [CGraph.mem_legEdges]
          exact Or.inl ⟨rfl, rfl, hk_pos⟩
        -- Edge (m+3+j, m+3+j+1) ∈ legEdges for j+1 < k
        have hledge_succ : ∀ j, j + 1 < k →
            (m + 3 + j, m + 3 + j + 1) ∈ CGraph.legEdges 0 (m + 3) k := by
          intro j hj
          rw [CGraph.mem_legEdges]
          exact Or.inr ⟨by omega, by omega, by omega⟩
        -- Show reachability to all tail vertices by induction on t
        let tailV : ∀ t, t < k → Fin (m + 3 + k) := fun t ht => ⟨m + 3 + t, by omega⟩
        have hall_tail : ∀ t (ht : t < k),
            (CGraph.tadpole (m + 3) k).toSimple.Reachable
              (⟨0, by omega⟩ : Fin (m + 3 + k)) (tailV t ht) := by
          intro t ht
          induction t with
          | zero =>
            show (CGraph.tadpole (m + 3) k).toSimple.Reachable
              (⟨0, by omega⟩ : Fin (m + 3 + k)) (tailV 0 ht)
            have hadj : (CGraph.tadpole (m + 3) k).Adj ⟨0, by omega⟩ (tailV 0 ht) := by
              simp only [tailV]
              rw [CGraph.tadpole_adj_val]
              simp only []
              exact ⟨by omega, Or.inl (by rw [List.mem_append]; right; exact hleg0)⟩
            obtain ⟨w⟩ := SimpleGraph.Reachable.refl _
            exact ⟨w.concat hadj⟩
          | succ j ih =>
            show (CGraph.tadpole (m + 3) k).toSimple.Reachable
              (⟨0, by omega⟩ : Fin (m + 3 + k)) (tailV (j + 1) ht)
            have ihj : j < k := by omega
            have ihj' := ih ihj
            have hadj : (CGraph.tadpole (m + 3) k).Adj (tailV j ihj) (tailV (j + 1) ht) := by
              simp only [tailV]
              rw [CGraph.tadpole_adj_val]
              simp only []
              have hmem : (m + 3 + j, m + 3 + (j + 1)) ∈ CGraph.legEdges 0 (m +
                  3) k := hledge_succ j (by omega)
              exact ⟨by omega, Or.inl (by rw [List.mem_append]; right; exact hmem)⟩
            obtain ⟨w⟩ := ihj'
            exact ⟨w.concat hadj⟩
        set t := (v : ℕ) - (m + 3)
        have ht_lt_k : t < k := by
          simp only [t]
          omega
        have hv_eq : v = tailV t ht_lt_k := by
          simp [tailV, t]
          have hle : m + 3 ≤ (v : ℕ) := by omega
          apply Fin.ext
          simp
          omega
        rw [hv_eq]
        exact hall_tail t ht_lt_k
    intro u v
    exact (hreach u).symm.trans (hreach v)

theorem numComponents_tadpole (m k : ℕ) : (tadpole (m + 3) k).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tadpole m k)

/-- The far end of the tail is the unique pendant. -/
theorem minDeg_tadpole (m k : ℕ) : minDeg (tadpole (m + 3) (k + 1)) = 1 := by
  rw [tadpole_def, minDeg_mk]
  apply le_antisymm
  · -- minDeg ≤ 1: the far end vertex has degree 1
    let v : (CGraph.tadpole (m + 3) (k + 1)).V := ⟨m + 3 + k, by omega⟩
    have hv1' : v.1 = m + 3 + k := rfl
    have hdeg_le : (CGraph.tadpole (m + 3) (k + 1)).toSimple.degree v ≤ 1 := by
      rw [← CGraph.card_nbrs_eq_degree]
      -- The neighbor set of v is a subset of a singleton, so card ≤ 1.
      -- v.1 = m+3+k. CycleEdges (m+3) involves only vertices < m+3, so no cycle edges incident.
      -- legEdges 0 (m+3) (k+1) has edge (0, m+3) and edges (m+3+j, m+3+j+1) for j < k+1.
      -- v.1 = m+3+k appears in legEdges only as second endpoint of (m+2+k, m+3+k) when k≥1,
      -- or as second endpoint of (0, m+3) when k=0.
      -- So at most one neighbor.
      have hsub : (CGraph.tadpole (m + 3) (k + 1)).nbrs v ⊆
          if k = 0 then {(⟨0, by omega⟩ : (CGraph.tadpole (m + 3) (k + 1)).V)}
          else {(⟨m + 2 + k, by omega⟩ : (CGraph.tadpole (m + 3) (k + 1)).V)} := by
        split
        · -- k = 0
          intro w hw
          rw [CGraph.mem_nbrs] at hw
          rw [CGraph.tadpole_adj_val] at hw
          rw [hv1'] at hw
          rw [List.mem_append, List.mem_append] at hw
          rw [CGraph.mem_cycleEdges, CGraph.mem_legEdges, CGraph.mem_cycleEdges,
              CGraph.mem_legEdges] at hw
          rcases hw with ⟨hne, hor⟩
          rcases hor with h | h
          · rcases h with h | h <;> omega
          · rcases h with h | h
            · rcases h with h | h <;> omega
            · rcases h with h | h
              · exact Finset.mem_singleton.mpr (Fin.ext_iff.mpr h.1)
              · omega
        · -- k ≠ 0
          intro w hw
          rw [CGraph.mem_nbrs] at hw
          rw [CGraph.tadpole_adj_val] at hw
          rw [hv1'] at hw
          rw [List.mem_append, List.mem_append] at hw
          rw [CGraph.mem_cycleEdges, CGraph.mem_legEdges, CGraph.mem_cycleEdges,
              CGraph.mem_legEdges] at hw
          rcases hw with ⟨hne, hor⟩
          rcases hor with h | h
          · rcases h with h | h <;> omega
          · rcases h with h | h
            · omega
            · rcases h with h | h
              · omega
              · rcases h with ⟨hle, hvw, hlt⟩
                have hvw' : w.1 = m + 2 + k := by omega
                exact Finset.mem_singleton.mpr (Fin.ext_iff.mpr hvw')
      split_ifs at hsub with hk
      · exact Finset.card_le_one.mpr (fun x hx y hy =>
          by rw [Finset.mem_singleton.mp (hsub hx), Finset.mem_singleton.mp (hsub hy)])
      · exact Finset.card_le_one.mpr (fun x hx y hy =>
          by rw [Finset.mem_singleton.mp (hsub hx), Finset.mem_singleton.mp (hsub hy)])
    exact le_trans (CGraph.minDeg_le_degree _ v) hdeg_le
  · -- 1 ≤ minDeg: every vertex has degree ≥ 1
    apply CGraph.le_minDeg_of_forall (⟨0, by omega⟩ : (CGraph.tadpole (m + 3) (k + 1)).V)
    intro v
    -- Exhibit a neighbor of v to show degree ≥ 1
    have hneighbor : ∃ w : (CGraph.tadpole (m + 3) (k + 1)).V, (CGraph.tadpole (m + 3) (k +
        1)).Adj v w = true := by
      by_cases hv0 : v.1 = 0
      · exact ⟨⟨1, by omega⟩, by rw [CGraph.tadpole_adj_val]; simp [hv0]⟩
      · by_cases hvm : v.1 < m + 3
        · refine ⟨⟨v.1 - 1, by omega⟩, ?_⟩
          rw [CGraph.tadpole_adj_val]
          simp [hv0]
          omega
        · by_cases hv_leg : v.1 = m + 3
          · exact ⟨⟨0, by omega⟩, by rw [CGraph.tadpole_adj_val]; simp [hv_leg]⟩
          · have hv_gt : m + 3 < v.1 := by omega
            refine ⟨⟨v.1 - 1, by omega⟩, ?_⟩
            rw [CGraph.tadpole_adj_val]
            simp
            omega
    exact (CGraph.toSimple (CGraph.tadpole (m + 3) (k +
        1))).degree_pos_iff_exists_adj v |>.mpr hneighbor

/-- A cycle of length four or more is triangle free, and gluing on a path adds no clique. -/
theorem cliqueNum_tadpole (m k : ℕ) : (tadpole (m + 4) k).cliqueNum = 2 := by
  -- Triangle-freeness at IsoGraph level
  unfold IsoGraph.tadpole
  rw [IsoGraph.cliqueNum_mk]
  -- Lower bound: 2 ≤ cliqueNum from E > 0
  have h2 : 2 ≤ (CGraph.tadpole (m + 4) k).cliqueNum := by
    apply CGraph.two_le_cliqueNum_of_E_pos
    show 0 < (CGraph.tadpole (m + 4) k).E
    have hE := IsoGraph.E_tadpole (m + 1) k
    show 0 < (CGraph.tadpole ((m + 1) + 3) k).E
    rw [show m + 4 = (m + 1) + 3 from by omega]
    simp [IsoGraph.tadpole_def] at hE
    rw [hE]
    omega
  -- Upper bound: cliqueNum ≤ 2 from triangle-freeness
  have htri2 : ∀ (x y z : (CGraph.tadpole (m + 4) k).V),
      (CGraph.tadpole (m + 4) k).Adj x y →
      (CGraph.tadpole (m + 4) k).Adj y z →
      (CGraph.tadpole (m + 4) k).Adj z x → False := by
    intro x y z hxy hyz hzx
    rw [CGraph.tadpole_adj_val] at hxy hyz hzx
    simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hxy hyz hzx
    omega
  have hle : (CGraph.tadpole (m + 4) k).cliqueNum ≤ 2 := by
    by_contra hcon
    have hcon2 : 3 ≤ (CGraph.tadpole (m + 4) k).cliqueNum := by omega
    have hg : (CGraph.tadpole (m + 4) k).girth = 3 :=
      CGraph.girth_eq_three_of_cliqueNum hcon2
    have hnac : ¬ (CGraph.tadpole (m + 4) k).IsAcyclic := by
      intro hac; rw [CGraph.girth_eq_zero_iff.mpr hac] at hg; omega
    have := CGraph.four_le_girth htri2 hnac
    omega
  omega

/-- A clique with a path glued to it stays connected. -/
theorem isConnected_lollipop (m k : ℕ) : IsConnected (lollipop (m + 1) k) := by
  rw [lollipop_def, IsoGraph.isConnected_mk, CGraph.IsConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨0, by omega⟩⟩⟩
  let G := CGraph.ofEdges (m + 1 + k) (CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k)
  have hG : (CGraph.lollipop (m + 1) k).toSimple = G.toSimple := rfl
  show SimpleGraph.Preconnected G.toSimple
  -- Reachable to root (vertex 0) for every vertex
  let root : G.V := ⟨0, by omega⟩
  have hreach : ∀ (v : G.V), G.toSimple.Reachable v root := by
    intro v
    by_cases hvclique : v.1 < m + 1
    · -- v is in the clique
      by_cases hv0 : v = root
      · rw [hv0]
      · have hv0' : v.1 ≠ 0 := by
          intro h; apply hv0; exact Fin.ext h
        have huv : G.Adj v root := by
          rw [CGraph.ofEdges_adj_val]
          have : root.1 = 0 := rfl
          simp [this]
          exact ⟨fun h => hv0' (by rw [h]; rfl), Or.inl ⟨Nat.pos_of_ne_zero hv0', by omega⟩⟩
        exact ⟨SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil⟩
    · -- v is in the leg: v.1 ≥ m+1
      push_neg at hvclique
      -- Convert hvclique to Nat
      have hvclique' : m + 1 ≤ v.1 := by
        exact_mod_cast hvclique
      -- Helper: leg vertex ⟨m+1+jj, hj⟩ has .1 = m+1+jj
      let legV : ∀ (jj : ℕ) (hj : m + 1 + jj < m + 1 + k), G.V := fun jj hj => ⟨m + 1 + jj, hj⟩
      have legV_val : ∀ (jj : ℕ) (hj : m + 1 + jj < m + 1 + k), (legV jj hj).1 = m + 1 + jj := by
        intro jj hj; rfl
      -- Base leg vertex (jj=0) is adjacent to root
      have hleg_adj_zero : k > 0 → G.Adj (legV 0 (by omega)) root := by
        intro hk
        rw [CGraph.ofEdges_adj_val]
        simp only [root, ne_eq]
        rw [legV_val]
        exact ⟨by omega, Or.inr (by
          rw [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges]
          exact Or.inr (Or.inl ⟨rfl, rfl, hk⟩))⟩
      -- Reachability of leg vertices by induction on jj
      have hreachLeg : ∀ (jj : ℕ) (hj : m + 1 + jj < m + 1 + k), jj < k →
          G.toSimple.Reachable (legV jj hj) root := by
        intro jj hj hj'
        induction jj with
        | zero =>
          exact ⟨SimpleGraph.Walk.cons (hleg_adj_zero (by omega)) SimpleGraph.Walk.nil⟩
        | succ ii hii =>
          have hiik : ii < k := by omega
          have hii_bound : m + 1 + ii < m + 1 + k := by omega
          have hu_reach : G.toSimple.Reachable (legV ii hii_bound) root := hii hii_bound hiik
          have hwu_bound : m + 1 + (ii + 1) < m + 1 + k := hj
          have hadj_w_u : G.Adj (legV (ii + 1) hwu_bound) (legV ii hii_bound) := by
            rw [CGraph.ofEdges_adj_val]
            simp only [ne_eq]
            rw [legV_val, legV_val]
            exact ⟨by omega, Or.inr (by
              rw [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges]
              exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩
          exact ⟨SimpleGraph.Walk.cons hadj_w_u hu_reach.some⟩
      -- Now handle v: v = legV (v.1 - (m+1)) ...
      have hv_bound : m + 1 + (v.1 - (m + 1)) < m + 1 + k := by omega
      have hv_lt : v.1 - (m + 1) < k := by omega
      have hv_eq : v = legV (v.1 - (m + 1)) hv_bound := by
        apply Fin.ext
        rw [legV_val]
        omega
      rw [hv_eq]
      exact hreachLeg _ hv_bound hv_lt
  intro u v
  exact (hreach u).trans (hreach v).symm

theorem numComponents_lollipop (m k : ℕ) : (lollipop (m + 1) k).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_lollipop m k)

/-- Every pendant hangs off one of the two centres, and the centres are joined. -/
theorem isConnected_doubleStar (m n : ℕ) : IsConnected (doubleStar m n) := by
  unfold IsoGraph.IsConnected IsoGraph.doubleStar
  simp
  -- Goal: CGraph.IsConnected (CGraph.doubleStar m n)
  simp only [CGraph.IsConnected]
  rw [SimpleGraph.connected_iff]
  -- All vertices reachable from 0.
  set N := 2 + m + n
  -- Define helper: adjacency in toSimple at key pairs
  let G := CGraph.doubleStar m n
  have adj_0_1 : G.toSimple.Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    rw [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
    simp
  -- For each i < m, edge (0, 2+i)
  have bound_0 : 0 < N := by omega
  have bound_1 : 1 < N := by omega
  have hPendant0Fin : ∀ (i : ℕ), i < m → 2 + i < N := by intro i hi; omega
  have hPendant1Fin : ∀ (i : ℕ), i < n → 2 + m + i < N := by intro i hi; omega
  have h_pendant0 : ∀ (i : ℕ) (hi : i < m),
      G.toSimple.Adj ⟨0, bound_0⟩ ⟨2 + i, hPendant0Fin i hi⟩ := by
    intro i hi
    rw [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
    simp; omega
  have h_pendant1 : ∀ (i : ℕ) (hi : i < n),
      G.toSimple.Adj ⟨1, bound_1⟩ ⟨2 + m + i, hPendant1Fin i hi⟩ := by
    intro i hi
    rw [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
    simp; omega
  -- Reachable from 0 to all vertices
  have hreach_base : G.toSimple.Reachable ⟨0, bound_0⟩ ⟨1, bound_1⟩ :=
    adj_0_1.reachable
  have hreach_pendant0 : ∀ (i : ℕ) (hi : i < m),
      G.toSimple.Reachable ⟨0, bound_0⟩ ⟨2 + i, hPendant0Fin i hi⟩ :=
    fun i hi => (h_pendant0 i hi).reachable
  have hreach_pendant1 : ∀ (i : ℕ) (hi : i < n),
      G.toSimple.Reachable ⟨0, bound_0⟩ ⟨2 + m + i, hPendant1Fin i hi⟩ := by
    intro i hi
    exact hreach_base.trans ((h_pendant1 i hi).reachable)
  -- Now prove reachability for all vertices by case analysis
  have hreach : ∀ (u : Fin N), G.toSimple.Reachable ⟨0, bound_0⟩ u := by
    intro ⟨v, hv⟩
    by_cases hv0 : v = 0
    · subst hv0
      exact SimpleGraph.Reachable.refl _
    by_cases hv1 : v = 1
    · subst hv1
      exact hreach_base
    by_cases hv2 : v < 2 + m
    · obtain ⟨i, hi, hi2⟩ : ∃ i, i < m ∧ 2 + i = v := by
        exact ⟨v - 2, by omega, by omega⟩
      have heq : (⟨2 + i, hPendant0Fin i hi⟩ : G.V) = ⟨v, hv⟩ := Fin.ext hi2
      exact heq ▸ hreach_pendant0 i hi
    · obtain ⟨i, hi, hi2⟩ : ∃ i, i < n ∧ 2 + m + i = v := by
        exact ⟨v - (2 + m), by omega, by omega⟩
      have heq : (⟨2 + m + i, hPendant1Fin i hi⟩ : G.V) = ⟨v, hv⟩ := Fin.ext hi2
      exact heq ▸ hreach_pendant1 i hi
  refine ⟨fun u v => (hreach u).symm.trans (hreach v), ⟨⟨0, bound_0⟩⟩⟩

theorem numComponents_doubleStar (m n : ℕ) : (doubleStar m n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_doubleStar m n)

/-- A double star has `m + n + 1` edges on `m + n + 2` vertices and is connected. -/
theorem isTree_doubleStar (m n : ℕ) : IsTree (doubleStar m n) := by
  exact (IsoGraph.isTree_iff (doubleStar m n)).mpr ⟨isConnected_doubleStar m n,
      by rw [E_doubleStar, V_doubleStar]; omega⟩

theorem girth_doubleStar (m n : ℕ) : (doubleStar m n).girth = 0 := by
  rw [girth_eq_zero_iff]
  exact (isTree_iff_isConnected_and_isAcyclic _).mp (isTree_doubleStar m n) |>.2

/-- The central edge is the largest clique in a tree. -/
theorem cliqueNum_doubleStar (m n : ℕ) : (doubleStar m n).cliqueNum = 2 := by
  apply cliqueNum_of_isTree (h := isTree_doubleStar m n)
  show 2 ≤ (doubleStar m n).V
  simp
  omega

theorem chromNum_doubleStar (m n : ℕ) : (doubleStar m n).chromNum = 2 := by
  simp only [doubleStar, IsoGraph.chromNum_mk]
  rw [CGraph.chromNum_eq_iff]
  -- Goal: (CGraph.doubleStar m n).toSimple.Colorable 2 ∧ ∀ m_1, ... → 2 ≤ m_1
  constructor
  · rw [← CGraph.isBipartite_iff_colorable]
    -- Construct a 2-coloring: vertices 0 and ≥ 2+m get color true,
    -- vertices 1 and 2..2+m-1 get color false.
    set c : (CGraph.doubleStar m
        n).V → Bool := fun v => if v.val = 0 ∨ 2 + m ≤ v.val then true else false
    refine ⟨c, ?_⟩
    intro a b hab
    rw [CGraph.doubleStar_adj_val] at hab
    have ha_val : a.val < 2 + m + n := a.isLt
    have hb_val : b.val < 2 + m + n := b.isLt
    simp only [c]
    -- The goal is about decide on Nat propositions given Nat hypotheses from adj_val.
    -- We case-split on the 6 cases from the disjunction using ` omega`-friendly approach.
    -- First, rewrite the Bool goal into a Prop goal.
    have key : (a.val = 0 ∨ 2 + m ≤ a.val) ↔ ¬(b.val = 0 ∨ 2 + m ≤ b.val) := by
      constructor
      · intro ha; by_contra hb; omega
      · intro hb; by_contra ha; push_neg at ha; omega
    show (if a.val = 0 ∨ 2 + m ≤ a.val then true else
        false) ≠ if b.val = 0 ∨ 2 + m ≤ b.val then true else false
    split <;> simp_all
  · intro m_1 hcol
    have hadj : (CGraph.doubleStar m n).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      simp [CGraph.doubleStar_adj_val]
    have h := CGraph.two_le_chromNum_of_adj hadj
    rw [CGraph.le_chromNum_iff] at h
    exact h m_1 hcol

/-- The two centres dominate, and one vertex cannot. -/
theorem domNum_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).domNum = 2 := by
  simp only [IsoGraph.doubleStar, IsoGraph.domNum_mk]
  let G := CGraph.doubleStar (m + 1) (n + 1)
  -- Upper bound: {0, 1} is dominating
  have hub : G.domNum ≤ 2 := by
    let v0 : G.V := ⟨0, by omega⟩
    let v1 : G.V := ⟨1, by omega⟩
    have hdom : G.IsDominatingSet {v0, v1} := by
      intro v
      simp only [v0, v1]
      by_cases hv0 : v = ⟨0, by omega⟩
      · exact Or.inl (by simp [hv0])
      · by_cases hv1 : v = ⟨1, by omega⟩
        · exact Or.inl (by simp [hv1])
        · right
          have hv0' : v.val ≠ 0 := by intro h; apply hv0; exact Fin.ext h
          have hv1' : v.val ≠ 1 := by intro h; apply hv1; exact Fin.ext h
          by_cases hpend0 : 2 ≤ v.val ∧ v.val < 2 + (m + 1)
          · exact ⟨v0, by simp [v0], by
              rw [CGraph.doubleStar_adj_val]
              simp [v0, hv0']
              omega⟩
          · push_neg at hpend0
            have hpend1 : 2 + (m + 1) ≤ v.val ∧ v.val < 2 + (m + 1) + (n + 1) := by omega
            exact ⟨v1, by simp [v1], by
              rw [CGraph.doubleStar_adj_val]
              simp [v1, hv1']
              omega⟩
    have h1 := CGraph.domNum_le_card_of_isDominatingSet hdom
    have hcard : ({v0, v1} : Finset G.V).card = 2 := by
      rw [Finset.card_pair]
      exact ne_of_apply_ne (fun x => x.val) (by simp [v0, v1])
    rw [hcard] at h1
    exact h1
  -- Helper: compute .val of literal vertices in G
  let mk0 : G.V := ⟨0, by omega⟩
  let mk1 : G.V := ⟨1, by omega⟩
  let mkpend0 : Fin (m + 1) → G.V := fun i => ⟨2 + i.val, by omega⟩
  let mkpend1 : Fin (n + 1) → G.V := fun i => ⟨2 + (m + 1) + i.val, by omega⟩
  have hval_0 : mk0.val = 0 := rfl
  have hval_1 : mk1.val = 1 := rfl
  have hval_pend0 : ∀ (i : Fin (m + 1)), (mkpend0 i).val = 2 + (i : ℕ) := by
    intro i; show (⟨2 + i.val, by omega⟩ : Fin (2 + (m + 1) + (n + 1))).val = 2 + (i : ℕ); rfl
  have hval_pend1 : ∀ (i : Fin (n + 1)), (mkpend1 i).val = 2 + (m + 1) + (i : ℕ) := by
    intro i; show (⟨2 + (m + 1) + i.val, by omega⟩ : Fin (2 + (m + 1) + (n + 1))).val = 2 + (m +
        1) + (i : ℕ); rfl
  -- No vertex is universal in doubleStar (m+1) (n+1)
  have huniv : ∀ v : G.V, ∃ u : G.V, u ≠ v ∧ ¬G.Adj v u := by
    intro v
    by_cases hv0 : v.val = 0
    · -- v = mk0; pick mkpend1 ⟨0,...⟩ which is not adj to mk0... wait, pendants of 1 are not adj to
      -- 0.
      refine ⟨mkpend1 ⟨0, by omega⟩, ?_, ?_⟩
      · intro h; rw [← h] at hv0; simp [hval_pend1] at hv0
      · have hmk10 : (mkpend1 ⟨0, by omega⟩ : G.V).val = 2 + (m + 1) + 0 := by
          simpa using hval_pend1 ⟨0, by omega⟩
        rw [CGraph.doubleStar_adj_val, hmk10, hv0]
        omega
    · by_cases hv1 : v.val = 1
      · -- v = mk1; pick mkpend0 ⟨0,...⟩ not adj to mk1
        refine ⟨mkpend0 ⟨0, by omega⟩, ?_, ?_⟩
        · intro h; rw [← h] at hv1; simp [hval_pend0] at hv1
        · rw [CGraph.doubleStar_adj_val]
          simp [hval_pend0, hv1]
      · -- v is a pendant of 0 or 1, but not 0 or 1 itself. v.val ≥ 2.
        by_cases hvpend0 : v.val < 2 + (m + 1)
        · -- v is a pendant of 0; pick mk1 (center 1) — pendants of 0 are not adj to 1
          refine ⟨mk1, ?_, ?_⟩
          · intro h; rw [← h] at hv1; simp [hval_1] at hv1
          · rw [CGraph.doubleStar_adj_val]
            simp [hval_1, hv0, hv1, hvpend0]
        · -- v.val ≥ 2+(m+1), so v is a pendant of 1; pick mk0
          refine ⟨mk0, ?_, ?_⟩
          · intro h; rw [← h] at hv0; simp [hval_0] at hv0
          · rw [CGraph.doubleStar_adj_val]
            simp [hval_0, hv0]
            omega
  have hlow : G.domNum ≠ 1 := by
    intro h
    rw [CGraph.domNum_eq_one_iff] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨u, hne, hna⟩ := huniv v
    exact hna (hv u hne)
  -- Combine
  have hpos : 0 < G.domNum := by
    apply CGraph.domNum_pos
    exact FinEnum.card_pos_iff.mpr ⟨⟨0, by omega⟩⟩
  have h1 : 1 < G.domNum := by omega
  change G.domNum = 2
  omega

/-- Match each centre to one of its own pendants; a third edge would need a third centre. -/
theorem matchNum_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).matchNum = 2 := by
  apply le_antisymm
  · -- matchNum ≤ 2 via coverNum ≤ 2
    apply le_trans (matchNum_le_coverNum _) _
    simp only [IsoGraph.doubleStar, coverNum_mk]
    -- {0, 1} is a vertex cover of doubleStar (m+1)(n+1)
    let S : Set (CGraph.doubleStar (m + 1) (n + 1)).V := {⟨0, by omega⟩, ⟨1, by omega⟩}
    have hvc : SimpleGraph.IsVertexCover (CGraph.doubleStar (m + 1) (n + 1)).toSimple S := by
      intro u v huv
      rw [CGraph.toSimple_adj] at huv
      rw [CGraph.doubleStar_adj_val] at huv
      rcases huv with ⟨hne, hcases⟩
      -- In all 6 cases, either u.1 ∈ {0,1} or v.1 ∈ {0,1}
      have : u.1 = 0 ∨ u.1 = 1 ∨ v.1 = 0 ∨ v.1 = 1 := by omega
      set e0 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨0, by omega⟩
      set e1 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨1, by omega⟩
      rcases this with h | h | h | h
      · left; rw [Set.mem_insert_iff]; exact Or.inl (Fin.ext (h.trans (by simp)))
      · left; rw [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Fin.ext (h.trans
          (by simp)))
      · right; rw [Set.mem_insert_iff]; exact Or.inl (Fin.ext (h.trans (by simp)))
      · right; rw [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Fin.ext (h.trans
          (by simp)))
    have hne : (⟨0, by omega⟩ : (CGraph.doubleStar (m + 1) (n + 1)).V) ≠ ⟨1, by omega⟩ := by
      intro h; simp at h
    have henc : S.encard = 2 := by
      rw [show S = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Set _) from rfl]
      rw [Set.encard_pair hne]
    rw [CGraph.coverNum]
    have h1 := hvc.vertexCoverNum_le.trans henc.le
    exact ENat.toNat_le_toNat h1 (by simp)
  · -- 2 ≤ matchNum: exhibit two disjoint edges
    rw [matchNum_eq, IsoGraph.doubleStar, lineGraph_mk, indepNum_mk]
    let G := CGraph.doubleStar (m + 1) (n + 1)
    -- Edge e1 = s(⟨0,...⟩, ⟨2,...⟩) is in G
    let ve0 : G.V := ⟨0, by omega⟩
    let ve2 : G.V := ⟨2, by omega⟩
    let ve1 : G.V := ⟨1, by omega⟩
    let ve2m1 : G.V := ⟨2 + (m + 1), by omega⟩
    have he1_mem : s(ve0, ve2) ∈ G.toSimple.edgeSet := by
      simp [G, SimpleGraph.mem_edgeSet, CGraph.toSimple]
      rw [CGraph.doubleStar_adj_val]
      simp [ve0, ve2]
    have he2_mem : s(ve1, ve2m1) ∈ G.toSimple.edgeSet := by
      simp [G, SimpleGraph.mem_edgeSet, CGraph.toSimple]
      rw [CGraph.doubleStar_adj_val]
      simp [ve1, ve2m1]
      omega
    let ev1 : (CGraph.lineGraph G).V := ⟨s(ve0, ve2), he1_mem⟩
    let ev2 : (CGraph.lineGraph G).V := ⟨s(ve1, ve2m1), he2_mem⟩
    -- They're not adjacent in lineGraph: edges are disjoint
    have hve0_ne_ve1 : ve0 ≠ ve1 := by
      intro h; have := congr_arg Fin.val h; simp [ve0, ve1] at this
    have hve0_ne_ve2m1 : ve0 ≠ ve2m1 := by
      intro h; have := congr_arg Fin.val h; simp [ve0, ve2m1] at this; omega
    have hve2_ne_ve1 : ve2 ≠ ve1 := by
      intro h; have := congr_arg Fin.val h; simp [ve2, ve1] at this
    have hve2_ne_ve2m1 : ve2 ≠ ve2m1 := by
      intro h; have := congr_arg Fin.val h; simp [ve2, ve2m1] at this
    have he_disjoint : ¬ ∃ v : G.V, v ∈ (s(ve0, ve2) : Sym2 G.V) ∧ v ∈ (s(ve1, ve2m1) : Sym2
        G.V) := by
      intro ⟨v, hv1, hv2⟩
      simp at hv1 hv2
      rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
      · exact hve0_ne_ve1 h
      · exact hve0_ne_ve2m1 h
      · exact hve2_ne_ve1 h
      · exact hve2_ne_ve2m1 h
    have hve0_not_in_ev2 : ve0 ∉ (s(ve1, ve2m1) : Sym2 G.V) := by
      intro hv
      simp at hv
      rcases hv with h | h <;> [exact hve0_ne_ve1 h; exact hve0_ne_ve2m1 h]
    have hne : ev1 ≠ ev2 := by
      intro h
      have h1 : (s(ve0, ve2) : Sym2 G.V) = s(ve1, ve2m1) := congrArg Subtype.val h
      have hmem1 : ve0 ∈ (s(ve0, ve2) : Sym2 G.V) := Sym2.mem_mk_left _ _
      rw [h1] at hmem1
      exact hve0_not_in_ev2 hmem1
    have hna : ¬ (CGraph.lineGraph G).Adj ev1 ev2 := by
      rw [CGraph.lineGraph_adj]
      have hdisj : ¬ ∃ v : G.V, v ∈ (↑ev1.1 : Sym2 G.V) ∧ v ∈ (↑ev2.1 : Sym2 G.V) := he_disjoint
      simp [hne, hdisj]
    exact CGraph.two_le_indepNum hne hna

/-- The far end of the tail is the unique pendant. -/
theorem minDeg_lollipop (m k : ℕ) : minDeg (lollipop (m + 2) (k + 1)) = 1 := by
  simp only [IsoGraph.lollipop, IsoGraph.minDeg_mk]
  set G := CGraph.lollipop (m + 2) (k + 1)
  
  set v_last : G.V := ⟨m + k + 2, by omega⟩
  -- Connectivity of G
  have hconn : G.IsConnected := by
    have := isConnected_lollipop (m + 1) (k + 1)
    rw [IsoGraph.lollipop, IsoGraph.isConnected_mk] at this
    exact this
  -- All vertices have degree ≥ 1
  have hall : ∀ v : G.V, 1 ≤ G.toSimple.degree v := by
    intro v
    have hvadj : ∃ w : G.V, G.Adj v w := by
      -- Construct a neighbor based on v.val
      set ev := v.val
      set em := m + 2
      set ek := k + 1
      set en := m + k + 3
      by_cases hev : ev < em
      · -- v is in the clique
        by_cases hev0 : ev = 0
        · -- Use neighbor m+2 (first leg vertex)
          refine ⟨⟨em, by omega⟩, ?_⟩
          show (CGraph.ofEdges _ _).Adj v ⟨em, by omega⟩ = true
          simp [CGraph.ofEdges, CGraph.ofRel_adj]
          have hv0 : v = ⟨0, by omega⟩ := Fin.ext hev0
          simp [hv0]
          omega
        · -- Use neighbor 0
          refine ⟨⟨0, by omega⟩, ?_⟩
          exact (CGraph.ofEdges_adj_val _ _ _ _).2 ⟨hev0, Or.inr (List.mem_append_left _
              (by rw [CGraph.mem_cliqueEdges]; exact ⟨Nat.pos_of_ne_zero hev0, hev⟩))⟩
      · -- v is on the leg (ev ≥ em)
        by_cases hev_eq : ev = em
        · -- neighbor is 0, edge (0, em) in legEdges
          refine ⟨⟨0, by omega⟩, ?_⟩
          have hv_ne_zero : v ≠ ⟨0, by omega⟩ := by
            intro h; simp [h, ev, em] at hev_eq
          dsimp only [G, CGraph.lollipop]
          rw [CGraph.ofEdges_adj_val]
          have hv_val : v.val = m + 2 := hev_eq
          rw [hv_val]
          simp
        · -- ev > em, use neighbor with val = ev - 1 (leg edge (ev-1, ev))
          have hev_gt : ev > em := by omega
          have hevd1 : ev - 1 ≥ em := by omega
          have hevd1_lt : ev - 1 + 1 < em + ek := by omega
          refine ⟨⟨ev - 1, by omega⟩, ?_⟩
          dsimp only [G, CGraph.lollipop]
          rw [CGraph.ofEdges_adj_val]
          have hEv1_lt_en' : ev - 1 < m + 2 + (k + 1) := by omega
          have hEv1_val : (⟨ev - 1, hEv1_lt_en'⟩ : G.V).val = ev - 1 := rfl
          rw [hEv1_val]
          refine ⟨by omega, Or.inr ?_⟩
          exact List.mem_append_right _
              (by rw [CGraph.mem_legEdges]; exact Or.inr ⟨hevd1, by omega, hevd1_lt⟩)
    exact Nat.lt_of_lt_of_le zero_lt_one (G.toSimple.degree_pos_iff_exists_adj v |>.2 hvadj)
  -- The last vertex has degree = 1  
  have hdeg_last : G.toSimple.degree v_last = 1 := by
    dsimp only [G, CGraph.lollipop]
    rw [← CGraph.card_nbrs_eq_degree]
    have hvlast_val : v_last.val = m + k + 2 := rfl
    -- Hall gives degree ≥ 1
    have hcard_ge : 1 ≤ ((CGraph.ofEdges _ _).nbrs v_last).card := by
      have := hall v_last
      rwa [CGraph.card_nbrs_eq_degree]
    -- Case split on k
    by_cases hk0 : k = 0
    · -- k = 0: nbrs v_last = {⟨0,...⟩}
      subst hk0
      set w0 : G.V := ⟨0, by omega⟩
      have hnbrs : (CGraph.ofEdges (m + 2 + (0 + 1)) (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges
          0 (m + 2) (0 + 1))).nbrs v_last = {w0} := by
        ext w
        simp [CGraph.mem_nbrs]
        rw [CGraph.ofEdges_adj_val, hvlast_val]
        constructor
        · intro ⟨hne, hmem⟩
          simp [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges] at hmem
          rcases hmem with hmem | hmem
          · omega
          · rcases hmem with hmem | hmem
            · exact hmem
            · exfalso; omega
        · intro hew
          subst hew
          simp only [w0]
          refine ⟨by omega, Or.inr (List.mem_append_right _ ?_)⟩
          rw [CGraph.mem_legEdges]
          exact Or.inl ⟨rfl, rfl, Nat.succ_pos _⟩
      rw [hnbrs]
      exact Finset.card_singleton w0
    · -- k ≥ 1: nbrs v_last = {⟨m+k+1,...⟩}
      set w2 : G.V := ⟨m + k + 1, by omega⟩
      have hnbrs : (CGraph.ofEdges (m + 2 + (k + 1)) (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges
          0 (m + 2) (k + 1))).nbrs v_last = {w2} := by
        ext w
        simp [CGraph.mem_nbrs]
        rw [CGraph.ofEdges_adj_val, hvlast_val]
        constructor
        · intro ⟨hne, hmem⟩
          simp [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges] at hmem
          rcases hmem with hmem | hmem
          · omega
          · rcases hmem with hmem | hmem
            · omega
            · have hv2 : w2.val = m + k + 1 := rfl
              exact Fin.ext (hmem.2.1.symm.trans hv2)
        · rintro rfl
          simp only [w2]
          refine ⟨by omega, Or.inr ?_⟩
          apply List.mem_append_right
          rw [CGraph.mem_legEdges]
          exact Or.inr ⟨by omega, by omega, by omega⟩
      rw [hnbrs]; exact Finset.card_singleton w2
  -- Combine
  show G.minDeg = 1
  have h1 : G.minDeg ≤ 1 := le_trans (CGraph.minDeg_le_degree G v_last) hdeg_last.le
  have h2 : 1 ≤ G.minDeg := CGraph.le_minDeg_of_forall v_last hall
  exact le_antisymm h1 h2

/-- The junction has the `m + 1` clique edges plus the first tail edge. -/
theorem maxDeg_lollipop (m k : ℕ) : maxDeg (lollipop (m + 2) (k + 1)) = m + 2 := by
  change (CGraph.lollipop (m + 2) (k + 1)).maxDeg = m + 2
  -- G = lollipop (m+2) (k+1)
  -- Vertex 0 has degree m+2
  have hdeg0 : (CGraph.lollipop (m + 2) (k + 1)).toSimple.degree ⟨0, by omega⟩ = m + 2 := by
    rw [← CGraph.card_nbrs_eq_degree]
    -- Characterize nbrs of ⟨0,...⟩
    let n := m + 2 + (k + 1)
    have h0 : (0 : ℕ) < n := by omega
    -- Every vertex v with v.1 ∈ {1,...,m+1,m+2} is a neighbor, and only those.
    have hnbrs : (CGraph.lollipop (m + 2) (k + 1)).nbrs ⟨0, h0⟩ = Finset.image (fun i : Fin (m + 2)
        => ⟨i.val + 1, by omega⟩) Finset.univ := by
      apply Finset.ext
      intro w
      simp only [CGraph.lollipop, CGraph.nbrs, Finset.mem_filter, Finset.mem_image,
        Finset.mem_univ, true_and]
      rw [CGraph.ofEdges_adj_val]
      constructor
      · rintro ⟨hne, heng⟩
        simp only [CGraph.mem_cliqueEdges, CGraph.mem_legEdges, List.mem_append] at heng
        rcases heng with heng | heng
        · rcases heng with heng | heng | heng
          · -- case 1: 0 < w.val ∧ w.val < m+2
            exact ⟨⟨w.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
          · -- case 2: w.val = m+2
            exact ⟨⟨m + 1, by omega⟩, Fin.ext (by simp; omega)⟩
          · omega
        · omega
      · rintro ⟨i, rfl⟩
        simp only [CGraph.mem_cliqueEdges, CGraph.mem_legEdges, List.mem_append]
        refine ⟨by omega, ?_⟩
        by_cases hi : (i : ℕ) < m + 1
        · exact Or.inl (Or.inl (by omega))
        · have hi2 : (i : ℕ) = m + 1 := by omega
          apply Or.inl
          apply Or.inr
          simp [hi2]
    rw [hnbrs]
    rw [Finset.card_image_of_injective _ (fun a b h =>
        by exact Fin.ext (by have := congr_arg Fin.val h; simp at this; omega))]
    rw [Finset.card_univ, Fintype.card_fin]
  have hmem : (m + 2 : ℕ) ∈ (CGraph.lollipop (m + 2) (k + 1)).degMultiset :=
    CGraph.mem_degMultiset.mpr ⟨⟨0, by omega⟩, hdeg0⟩
  have hule : ∀ v : (CGraph.lollipop (m + 2) (k + 1)).V, (CGraph.lollipop (m + 2) (k +
      1)).toSimple.degree v ≤ m + 2 := by
    intro v
    rw [← CGraph.card_nbrs_eq_degree]
    -- Characterize: Adj v w ↔ ...
    have hadj : ∀ w : (CGraph.lollipop (m + 2) (k + 1)).V, (CGraph.lollipop (m + 2) (k +
        1)).Adj v w ↔
      v.val ≠ w.val ∧
        ((v.val < w.val ∧ w.val < m + 2) ∨
         (0 < k + 1 ∧ v.val = 0 ∧ w.val = m + 2) ∨
         (m + 2 ≤ v.val ∧ w.val = v.val + 1 ∧ v.val + 1 < m + 2 + (k + 1)) ∨
         (w.val < v.val ∧ v.val < m + 2) ∨
         (0 < k + 1 ∧ w.val = 0 ∧ v.val = m + 2) ∨
         (m + 2 ≤ w.val ∧ v.val = w.val + 1 ∧ w.val + 1 < m + 2 + (k + 1))) := by
      intro w
      simp only [CGraph.lollipop, CGraph.ofEdges_adj_val]
      simp only [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges]
      grind
    have hv_lt : v.val < m + 2 + (k + 1) := v.2
    by_cases hvcl : v.val < m + 2
    · -- v is a clique vertex
      -- nbrs v ⊆ {w | w.val < m+2 ∧ w ≠ v} ∪ {⟨m+2,...⟩}
      -- This set has card ≤ (m+2-1)+1 = m+2
      let cliqueSet : Finset ((CGraph.lollipop (m + 2) (k + 1)).V) :=
        Finset.filter (fun w => w.val < m + 2 ∧ w.val ≠ v.val) Finset.univ
      have hnbrs_sub : (CGraph.lollipop (m + 2) (k + 1)).nbrs v ⊆ cliqueSet ∪ {⟨m + 2,
          by omega⟩} := by
        intro w hw
        rw [CGraph.mem_nbrs] at hw
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, cliqueSet]
        rcases (hadj w).mp hw with ⟨hne, hcases⟩
        rcases hcases with h1 | h2 | h3 | h4 | h5 | h6
        · -- v < w < m+2: w is in clique, w ≠ v
          exact Or.inl ⟨h1.2, hne.symm⟩
        · -- v = 0, w = m+2
          have : w.val = m + 2 := by omega
          exact Or.inr (Fin.ext this)
        · -- m+2 ≤ v, contradicting hvcl
          exfalso; omega
        · -- w < v < m+2: w is in clique, w ≠ v
          exact Or.inl ⟨by omega, hne.symm⟩
        · -- w = 0, v = m+2, contradicting hvcl
          exfalso; omega
        · -- m+2 ≤ w, v = w+1, so v ≥ m+3, contradicting hvcl
          exfalso; omega
      let cliqueAll : Finset ((CGraph.lollipop (m + 2) (k + 1)).V) :=
        Finset.filter (fun w : Fin (m + 2 + (k + 1)) => w.val < m + 2) Finset.univ
      have hcard_cliqueSet : cliqueSet.card ≤ m + 1 := by
        have hcliqueSet_sub : cliqueSet ⊆ cliqueAll \ {v} := by
          intro w hw
          simp [cliqueSet, cliqueAll, Finset.mem_sdiff, Finset.mem_filter] at hw ⊢
          exact ⟨hw.1, fun h => hw.2 (by rw [h])⟩
        have hcard_cliqueAll : cliqueAll.card = m + 2 := by
          have heq : cliqueAll = Finset.image (fun i : Fin (m + 2) => ⟨i.val, by omega⟩ : Fin (m +
              2) → Fin (m + 2 + (k + 1))) Finset.univ := by
            ext (w : Fin (m + 2 + (k + 1))); simp [cliqueAll, Finset.mem_image, Finset.mem_univ,
                true_and]
            exact ⟨fun h => ⟨⟨w.val, h⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.2⟩
          rw [heq, Finset.card_image_of_injective _ (fun a b h => Fin.ext
              (by have := congr_arg Fin.val h; simp at this; omega)), Finset.card_univ,
                  Fintype.card_fin]
        have hv_in_clique : v ∈ cliqueAll := by simp [cliqueAll, hvcl]
        have hcard_diff : (cliqueAll \ {v}).card = m + 1 := by
          rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hv_in_clique),
              hcard_cliqueAll, Finset.card_singleton]
          omega
        exact le_trans (Finset.card_mono hcliqueSet_sub) hcard_diff.le
      have hcard_nbrs_clique : ((CGraph.lollipop (m + 2) (k + 1)).nbrs v).card ≤ m + 2 := by
        calc ((CGraph.lollipop (m + 2) (k + 1)).nbrs v).card
            ≤ (cliqueSet ∪ {⟨m + 2, by omega⟩}).card := Finset.card_mono hnbrs_sub
          _ ≤ cliqueSet.card + 1 := Finset.card_union_le _ _
          _ ≤ m + 1 + 1 := by omega
          _ = m + 2 := by omega
      exact hcard_nbrs_clique
    · -- v is a leg vertex (m+2 ≤ v.val)
      have hvge : m + 2 ≤ v.val := by omega
      -- For leg vertices, degree ≤ 2. Then 2 ≤ m + 2.
      -- Define f : nbrs v → Bool by f w = (w.val < v.val).
      -- This is injective (by hadj analysis), so card ≤ 2.
      have hdeg_le_2 : ((CGraph.lollipop (m + 2) (k + 1)).nbrs v).card ≤ 2 := by
        set S := (CGraph.lollipop (m + 2) (k + 1)).nbrs v
        -- Define g : S → Bool by g w = (w.val < v.val). This is injective.
        have hinj : ∀ w1 ∈ S, ∀ w2 ∈ S, (w1.val < v.val ↔ w2.val < v.val) → w1 = w2 := by
          intro w1 hw1 w2 hw2 hbooll
          rw [CGraph.mem_nbrs] at hw1 hw2
          rw [hadj w1] at hw1; rw [hadj w2] at hw2
          obtain ⟨hne1, hc1⟩ := hw1; obtain ⟨hne2, hc2⟩ := hw2
          set a1 := w1.val; set a2 := w2.val; set bv := v.val
          -- Eliminate impossible cases for w1: bv ≥ m+2 eliminates cases where bv < a1 ∧ a1 < m+2,
          -- a1 < bv ∧ bv < m+2, bv = 0 case
          have hw1_valid :
            (m + 2 ≤ bv ∧ a1 = bv + 1 ∧ bv + 1 < m + 2 + (k + 1)) ∨
            (0 < k + 1 ∧ a1 = 0 ∧ bv = m + 2) ∨
            (m + 2 ≤ a1 ∧ bv = a1 + 1 ∧ a1 + 1 < m + 2 + (k + 1)) := by
            rcases hc1 with h | h | h | h | h | h
            · exact absurd (by omega : bv < a1) (not_lt_of_ge (by omega))
            · exfalso; omega
            · exact Or.inl h
            · exfalso; omega
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hw2_valid :
            (m + 2 ≤ bv ∧ a2 = bv + 1 ∧ bv + 1 < m + 2 + (k + 1)) ∨
            (0 < k + 1 ∧ a2 = 0 ∧ bv = m + 2) ∨
            (m + 2 ≤ a2 ∧ bv = a2 + 1 ∧ a2 + 1 < m + 2 + (k + 1)) := by
            rcases hc2 with h | h | h | h | h | h
            · exact absurd (by omega : bv < a2) (not_lt_of_ge (by omega))
            · exfalso; omega
            · exact Or.inl h
            · exfalso; omega
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          -- bool values: T3→false, T5→true (0 < m+2), T6→true (a < bv since bv = a+1)
          rcases hw1_valid with ⟨_, ha1_eq, _⟩ | ⟨_, ha1_eq, hbv_eq⟩ | ⟨_, hbv_eq, _⟩
          · rcases hw2_valid with ⟨_, ha2_eq, _⟩ | ⟨_, ha2_eq, hbv_eq2⟩ | ⟨_, hbv_eq2, _⟩
            · exact Fin.ext (by omega)
            · exfalso; simp [ha1_eq] at hbooll; omega
            · exfalso; simp [ha1_eq] at hbooll; omega
          · rcases hw2_valid with ⟨_, ha2_eq, _⟩ | ⟨_, ha2_eq, hbv_eq2⟩ | ⟨_, hbv_eq2, _⟩
            · exfalso; simp [ha1_eq] at hbooll; omega
            · exact Fin.ext (by omega)
            · exfalso; omega
          · rcases hw2_valid with ⟨_, ha2_eq, _⟩ | ⟨_, ha2_eq, hbv_eq2⟩ | ⟨_, hbv_eq2, _⟩
            · exfalso; simp [hbv_eq] at hbooll; omega
            · exfalso; omega
            · exact Fin.ext (by omega)
        -- Injectivity into Bool (which has card 2) gives card S ≤ 2.
        -- Map each neighbor to Fin 2: 0 if w.val < v.val, 1 otherwise. This is injective.
        let f : S → Fin 2 := fun ⟨w, hw⟩ => if w.val < v.val then 0 else 1
        have hf_inj : Function.Injective f := by
          intro ⟨w1, hw1⟩ ⟨w2, hw2⟩ heq
          have hbooll : (w1.val < v.val ↔ w2.val < v.val) := by
            simp only [f] at heq
            show (w1.val < v.val ↔ w2.val < v.val)
            by_cases h1 : w1.val < v.val <;> by_cases h2 : w2.val < v.val <;> simp [h1, h2] at heq ⊢
          exact Subtype.ext (hinj w1 hw1 w2 hw2 hbooll)
        have := Fintype.card_le_of_injective f hf_inj
        simp [Fintype.card_fin] at this
        exact this
      omega
  exact @CGraph.maxDeg_eq_of_degMultiset (CGraph.lollipop (m + 2) (k + 1)) (m + 2) hmem (fun d hd
      => by
    rw [CGraph.mem_degMultiset] at hd
    obtain ⟨v, hv⟩ := hd
    rw [← hv]
    exact hule v)

/-- An even cycle with a tail is bipartite, and it has an edge. -/
theorem chromNum_tadpole_even (m k : ℕ) : (tadpole (2 * m + 4) k).chromNum = 2 := by
  refine chromNum_eq_two_iff.mpr ⟨?_, ?_⟩
  · have := isBipartite_tadpole_even (m + 2) k
    rwa [show 2 * (m + 2) = 2 * m + 4 from by ring] at this
  · have := E_tadpole (2 * m + 1) k
    rw [show 2 * m + 1 + 3 = 2 * m + 4 from by ring] at this
    omega

/-- A spider is a tree, so it has one edge fewer than it has vertices. -/
theorem E_spider (legs : List ℕ) : (spider legs).E = legs.sum := by
  rw [spider_def, E_mk]
  -- Helper: pathEdges length
  have hpath_edges_len : ∀ (l : List ℕ), l.length ≥ 1 → (CGraph.pathEdges
      l).length = l.length - 1 := by
    intro l hl
    induction l with
    | nil => exfalso; simp at hl
    | cons a l ih =>
      cases l with
      | nil => simp [CGraph.pathEdges]
      | cons b l' =>
        simp [CGraph.pathEdges]
        have ih2 := ih (by simp)
        simp [List.length_cons] at ih2 ⊢
        omega
  have hleg_edges_len : ∀ (v off k : ℕ), (CGraph.legEdges v off k).length = k := by
    intro v off k
    simp only [CGraph.legEdges]
    have : (v :: (List.range k).map (fun x => x + off)).length = k + 1 := by
      simp [List.length_cons, List.length_map, List.length_range]
    rw [hpath_edges_len _ (by omega)]
    omega
  have hlen : ∀ (off : ℕ) (ks : List ℕ), (CGraph.spiderEdges off ks).length = ks.sum := by
    intro off ks; induction ks generalizing off with
    | nil => simp [CGraph.spiderEdges]
    | cons k rest ih =>
      simp [CGraph.spiderEdges, List.length_append, hleg_edges_len, ih, List.sum_cons]
  have hlts : ∀ (off : ℕ) (ks : List ℕ), 0 < off →
      (∀ p ∈ CGraph.spiderEdges off ks, p.1 < p.2) := by
    intro off ks hoff
    induction ks generalizing off with
    | nil => simp [CGraph.spiderEdges]
    | cons k rest ih =>
      simp [CGraph.spiderEdges, List.mem_append]
      intro a b hp
      rcases hp with h | h
      · rcases h with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩
        · omega
        · omega
      · exact ih (off + k) (by omega) (a, b) h
  have hbounds2 : ∀ (off : ℕ) (ks : List ℕ), 0 < off →
      (∀ p ∈ CGraph.spiderEdges off ks, p.2 < off + ks.sum) := by
    intro off ks hoff p hpq
    exact (CGraph.mem_spiderEdges_bound off ks p.1 p.2 hpq).2.2
  -- legEdges 0 off k is nodup for any off, k (from mem_legEdges, edges are (0,off) and (p,p+1) for
  -- off≤p<off+k-1, all distinct)
  have hleg_nodup : ∀ (off k : ℕ), (CGraph.legEdges 0 off k).Nodup := by
    intro off k
    induction k with
    | zero => simp [CGraph.legEdges_zero]
    | succ j ih =>
      simp [CGraph.legEdges_succ]
      have inj : Function.Injective (fun i : ℕ => (i + off, i + 1 + off)) :=
        fun a b h => by injection h with h1 h2; omega
      exact List.Nodup.map inj List.nodup_range
  have hnoup : ∀ (off : ℕ) (ks : List ℕ), 0 < off →
      (CGraph.spiderEdges off ks).Nodup := by
    intro off ks hoff
    induction ks generalizing off with
    | nil => simp [CGraph.spiderEdges]
    | cons k rest ih =>
      rw [CGraph.spiderEdges]
      apply List.Nodup.append (hleg_nodup off k) (ih (off + k) (by omega))
      intro p hmem_leg hmem_spider
      rw [CGraph.mem_legEdges] at hmem_leg
      have hb := CGraph.mem_spiderEdges_bound (off + k) rest p.1 p.2 hmem_spider
      rcases hmem_leg with ⟨h1, h2, hk⟩ | ⟨h1, h2, h3⟩
      · omega
      · omega
  have ofEdges_E_of_lt_local : ∀ (n : ℕ) (es : List (ℕ × ℕ)),
      (∀ p ∈ es, p.1 < p.2) →
      (∀ p ∈ es, p.2 < n) →
      List.Nodup es →
      (CGraph.ofEdges n es).E = es.length := by
    intro n es hlt hbound hnup
    induction es with
    | nil => rw [CGraph.ofEdges_nil, CGraph.E_empty]; rfl
    | cons p es' ih =>
      have heq : CGraph.ofEdges n (p :: es') = CGraph.ofEdges n (es' ++ [p]) := by
        apply CGraph.ofEdges_congr n _ _ _
        intro x y hne
        simp [List.mem_cons, List.mem_append]
        tauto
      rw [heq]
      have hlt' : ∀ q ∈ es', q.1 < q.2 := fun q hq => hlt q (List.mem_cons_of_mem _ hq)
      have hfun : ∀ q ∈ p :: es', q.1 < n := fun q hq => lt_trans (hlt q hq) (hbound q hq)
      have hbound' : ∀ q ∈ es', q.2 < n := fun q hq => hbound q (List.mem_cons_of_mem _ hq)
      have hnup' : es'.Nodup := hnup.tail
      have ihm := ih hlt' hbound' hnup'
      have hp_mem : p ∈ p :: es' := List.mem_cons_self
      set ep : Sym2 (Fin n) := Sym2.mk (⟨p.1, hfun p hp_mem⟩, ⟨p.2, hbound p hp_mem⟩)
      have hnotin : ep ∉ (CGraph.ofEdges n es').toSimple.edgeFinset := by
        intro hmem
        simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple, CGraph.ofEdges, CGraph.ofRel] at hmem
        obtain ⟨hne, hm ⟩ := hmem
        have hp12 : p.1 < p.2 := hlt p hp_mem
        have hpn : p ∉ es' := (List.nodup_cons.mp hnup).1
        rcases hm with h | h
        · exact hpn h
        · have := hlt' (p.2, p.1) h
          omega
      have hedgeFinset : (CGraph.ofEdges n (es' ++ [p])).toSimple.edgeFinset =
          (CGraph.ofEdges n es').toSimple.edgeFinset ∪ {ep} := by
        ext e
        simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple, CGraph.ofEdges, CGraph.ofRel,
          List.mem_append]
        induction e using Sym2.ind with
        | _ a b =>
          simp only [SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet]
          dsimp only [ep]
          rw [Sym2.eq_iff]
          simp only [Fin.ext_iff]
          have : ∀ (x : Fin n) (v : ℕ) (hv : v < n), (x = ⟨v, hv⟩ ↔ x.1 = v) := by
            intro x v hv; simp [Fin.ext_iff]
          rw [this a p.1 (hfun p hp_mem), this b p.2 (hbound p hp_mem),
              this a p.2 (hbound p hp_mem), this b p.1 (hfun p hp_mem)]
          set a' : ℕ := a.val
          set b' : ℕ := b.val
          rcases p with ⟨p1, p2⟩
          simp [Prod.mk.injEq]
          have hpnotin_es' : (p1, p2) ∉ es' := by
            intro h; exact (List.nodup_cons.mp hnup).1 h
          have hp12 : p1 < p2 := by simpa using hlt (p1, p2) hp_mem
          have hp21notin_es' : (p2, p1) ∉ es' := by
            intro h; have := hlt' (p2, p1) h; omega
          have hp12ne : p1 ≠ p2 := hp12.ne
          set A := (a', b') ∈ es'
          set B := a' = p1 ∧ b' = p2
          set C := (b', a') ∈ es'
          set D := b' = p1 ∧ a' = p2
          simp only [A, B, C, D] at *
          have hDflip : a' = p2 ∧ b' = p1 ↔ D := by constructor <;> intro h <;> exact ⟨h.2, h.1⟩
          rw [hDflip]
          rw [show b' = p1 ∧ a' = p2 ↔ D from Iff.rfl]
          have hNe_from_B : B → ¬a' = b' := by intro ⟨ha, hb⟩; omega
          have hNe_from_D : D → ¬a' = b' := by intro ⟨hb, ha⟩; omega
          set Ne := ¬a' = b'
          show Ne ∧ ((A ∨ B) ∨ C ∨ D) ↔ (B ∨ D) ∨ Ne ∧ (A ∨ C)
          constructor
          · intro h
            rcases h with ⟨Ne, hmem⟩
            rcases hmem with hAB | hCD
            · rcases hAB with hA | hB
              · exact Or.inr ⟨Ne, Or.inl hA⟩
              · exact Or.inl (Or.inl hB)
            · rcases hCD with hC | hD_val
              · exact Or.inr ⟨Ne, Or.inr hC⟩
              · exact Or.inl (Or.inr hD_val)
          · intro h
            rcases h with hBD | ⟨Ne, hAC⟩
            · rcases hBD with hB | hD_val
              · exact ⟨hNe_from_B hB, Or.inl (Or.inr hB)⟩
              · exact ⟨hNe_from_D hD_val, Or.inr (Or.inr hD_val)⟩
            · rcases hAC with hA | hC
              · exact ⟨Ne, Or.inl (Or.inl hA)⟩
              · exact ⟨Ne, Or.inr (Or.inl hC)⟩
      unfold CGraph.E at ihm ⊢
      rw [hedgeFinset, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnotin)]
      rw [Finset.card_singleton]
      rw [ihm]
      simp
  unfold CGraph.spider
  rw [ofEdges_E_of_lt_local (1 + legs.sum) (CGraph.spiderEdges 1 legs)
    (hlts 1 legs (by omega))
    (hbounds2 1 legs (by omega))
    (hnoup 1 legs (by omega))]
  rw [hlen 1 legs]

/-- Hanging pendant vertices off a cycle adds one edge per pendant. -/
theorem E_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    (cyclePendant (m + 3) ks).E = m + 3 + ks.sum := by
  simp only [IsoGraph.cyclePendant, IsoGraph.E_mk, CGraph.cyclePendant]
  -- Helper: ofEdges_E_helper replicated locally
  have ofEdges_E_helper : ∀ {n : ℕ} {es : List (ℕ × ℕ)},
      (∀ p ∈ es, p.1 < n ∧ p.2 < n) →
      (∀ p ∈ es, p.1 ≠ p.2) →
      (∀ p ∈ es, (p.2, p.1) ∉ es) →
      es.Nodup →
      (CGraph.ofEdges n es).E = es.length := by
    intro n es hn hnooops hnorev hnodup
    induction es with
    | nil =>
      have : CGraph.ofEdges n [] = CGraph.empty n := by
        exact CGraph.ext' rfl (heq_of_eq (funext fun i => funext fun j =>
            by simp [CGraph.ofEdges, CGraph.empty]))
      rw [this, CGraph.E_empty, List.length_nil]
    | cons e es' ih =>
      unfold CGraph.E
      set ue : Fin n := ⟨e.1, (hn e (by simp)).1⟩
      set ve : Fin n := ⟨e.2, (hn e (by simp)).2⟩
      set edge_e : Sym2 (Fin n) := Sym2.mk (ue, ve)
      have he_not_in_es' : e ∉ es' := by
        intro h
        have hd := hnodup
        simp [List.nodup_cons] at hd
        exact hd.1 h
      have hrev_not_in_es' : (e.2, e.1) ∉ es' := by
        intro h
        have hmem : (e.2, e.1) ∈ e :: es' := by simp [h]
        exact absurd (hnorev (e.2, e.1) hmem) (by simp [List.mem_cons])
      have hdisjoint : edge_e ∉ (CGraph.ofEdges n es').toSimple.edgeFinset := by
        intro he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj,
            CGraph.ofEdges_adj_val] at he
        rcases he.2 with h | h
        · exact he_not_in_es' h
        · exact hrev_not_in_es' h
      have hedgeFinset_eq : (CGraph.ofEdges n (e :: es')).toSimple.edgeFinset =
          (insert edge_e (CGraph.ofEdges n es').toSimple.edgeFinset) := by
        ext x
        show x ∈ (CGraph.ofEdges n (e :: es')).toSimple.edgeFinset ↔
            x ∈ insert edge_e (CGraph.ofEdges n es').toSimple.edgeFinset
        have hdef : (CGraph.ofEdges n (e :: es')).V = Fin n := rfl
        change x ∈ (CGraph.ofEdges n (e :: es')).toSimple.edgeFinset ↔
            x ∈ insert edge_e (CGraph.ofEdges n es').toSimple.edgeFinset at *
        induction x using Sym2.ind with
        | h u v =>
          simp [SimpleGraph.mem_edgeFinset, Finset.mem_insert, SimpleGraph.mem_edgeSet,
            CGraph.toSimple_adj, CGraph.ofEdges_adj_val]
          dsimp only [CGraph.ofEdges, CGraph.ofRel] at u v
          simp only [edge_e]
          rw [Sym2.eq_iff]
          have heq1 : (u = ue ↔ ↑u = e.1) := by simp [ue, Fin.ext_iff]
          have heq2 : (v = ve ↔ ↑v = e.2) := by simp [ve, Fin.ext_iff]
          have heq3 : (u = ve ↔ ↑u = e.2) := by simp [ve, Fin.ext_iff]
          have heq4 : (v = ue ↔ ↑v = e.1) := by simp [ue, Fin.ext_iff]
          have heq5 : ((↑u, ↑v) = e ↔ ↑u = e.1 ∧ ↑v = e.2) := Prod.ext_iff
          have heq6 : ((↑v, ↑u) = e ↔ ↑v = e.1 ∧ ↑u = e.2) := Prod.ext_iff
          rw [heq5, heq6, heq1, heq2, heq3, heq4]
          have hnooops_e : e.1 ≠ e.2 := hnooops e (by simp)
          have hA_notC : (↑u = e.1 ∧ ↑v = e.2) → ¬(↑u = ↑v) := by
            intro ⟨ha, hb⟩ huv
            have huv' : (u : ℕ) = (v : ℕ) := congr_arg (fun x : Fin n => (x : ℕ)) huv
            exact hnooops_e (by rw [ha, hb] at huv'; exact huv')
          have hB_notC : (↑v = e.1 ∧ ↑u = e.2) → ¬(↑u = ↑v) := by
            intro ⟨ha, hb⟩ huv
            have huv' : (u : ℕ) = (v : ℕ) := congr_arg (fun x : Fin n => (x : ℕ)) huv
            exact hnooops_e (by rw [hb, ha] at huv'; exact huv'.symm)
          have hB_eq_B' : (↑u = e.2 ∧ ↑v = e.1) ↔ (↑v = e.1 ∧ ↑u = e.2) := and_comm
          have hAB_notC : (↑u = e.1 ∧ ↑v = e.2 ∨ ↑u = e.2 ∧ ↑v = e.1) → ¬(↑u = ↑v) := by
            rintro (hA | hB'')
            · exact hA_notC hA
            · exact hB_notC ⟨hB''.2, hB''.1⟩
          constructor
          · rintro ⟨hne, hmem⟩
            rcases hmem with hAD | hBD' | hF
            · rcases hAD with hA | hD
              · exact .inl (.inl hA)
              · exact .inr ⟨hne, .inl hD⟩
            · exact .inl (.inr (hB_eq_B'.mpr hBD'))
            · exact .inr ⟨hne, .inr hF⟩
          · rintro (hAB | ⟨hne, hDF⟩)
            · have hnotC := hAB_notC hAB
              exact ⟨by intro huv; exact hnotC (Fin.ext_iff.mpr huv),
                     Or.elim hAB (fun hA => Or.inl (Or.inl hA))
                       (fun hB'' => Or.inr (Or.inl (hB_eq_B'.mp hB'')))⟩
            · exact ⟨hne, Or.elim hDF (fun hD => Or.inl (Or.inr hD)) (fun hF => Or.inr (Or.inr hF))⟩
      rw [hedgeFinset_eq, Finset.card_insert_of_notMem hdisjoint]
      simp [List.length_cons]
      exact ih
        (fun p hp => ⟨(hn p (by simp [hp])).1, (hn p (by simp [hp])).2⟩)
        (fun p hp => hnooops p (by simp [hp]))
        (fun p hp => by
          have h := hnorev p (by simp [hp])
          exact fun hm => h (by simp [hm]))
        hnodup.tail
  -- pendantEdges length = sum
  have hpending_len : ∀ (v off : ℕ) (ks : List ℕ),
      (CGraph.pendantEdges v off ks).length = ks.sum := by
    intro v off ks
    induction ks generalizing v off with
    | nil => simp [CGraph.pendantEdges]
    | cons k rest ih =>
      simp [CGraph.pendantEdges, List.length_append, List.length_map, List.length_range]
      rw [ih (v + 1) (off + k)]
  -- cycleEdges length = n
  have hcycle_len : ∀ n, (CGraph.cycleEdges n).length = n := by
    intro n
    induction n with
    | zero => simp [CGraph.cycleEdges_zero]
    | succ n ih =>
      rw [CGraph.cycleEdges_succ]
      simp [List.length_append, List.length_map, List.length_range]
  -- Bounds for cycleEdges
  have hcycle_bound : ∀ p ∈ CGraph.cycleEdges (m + 3), p.1 < m + 3 ∧ p.2 < m + 3 := by
    intro p hp
    rw [CGraph.mem_cycleEdges] at hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega
  -- Bounds for pendantEdges
  have hpending_bound : ∀ p ∈ CGraph.pendantEdges 0 (m +
      3) ks, p.1 < m + 3 + ks.sum ∧ p.2 < m + 3 + ks.sum := by
    intro p hp
    have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 hp
    simp at this
    omega
  -- cycleEdges nodup
  have hcycle_nodup : List.Nodup (CGraph.cycleEdges (m + 3)) := by
    induction m + 3 with
    | zero => simp [CGraph.cycleEdges_zero]
    | succ n ih =>
      rw [CGraph.cycleEdges_succ]
      apply List.Nodup.append
      · exact List.Nodup.map (fun i j hij => by injection hij) List.nodup_range
      · exact List.nodup_singleton _
      · intro x hx
        simp [List.mem_map, List.mem_range] at hx
        rcases hx with ⟨i, hi, rfl, rfl⟩
        simp
  -- No loops in cycleEdges
  have hcycle_noloop : ∀ p ∈ CGraph.cycleEdges (m + 3), p.1 ≠ p.2 := by
    intro p hp
    rw [CGraph.mem_cycleEdges] at hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  -- Pendant edges have p.1 < p.2 (so no self loops, since p.1 ≥ 0 and p.2 ≥ m+3 > p.1... wait, p.1
  -- is the first component which is the "owner" vertex index)
  -- Actually from mem_pendantEdges_bound with v=0: p.1 < ks.length ≤ m+3, and p.2 ≥ m+3. So p.1 <
  -- p.2 always. Hence no loops.
  have hpending_noloop : ∀ p ∈ CGraph.pendantEdges 0 (m + 3) ks, p.1 ≠ p.2 := by
    intro p hp
    have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 hp
    simp at this
    omega
  -- Pendant edges: first component < second component (so no reverses of pendant edges within
  -- themselves)
  have hpending_forward : ∀ p ∈ CGraph.pendantEdges 0 (m + 3) ks, p.1 < p.2 := by
    intro p hp
    have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 hp
    omega
  -- No reverse of a pendant edge is in cycleEdges (pendant edges go to vertices ≥ m+3, cycle edges
  -- have both endpoints < m+3)
  have hpending_no_rev_in_cycle : ∀ p ∈ CGraph.pendantEdges 0 (m + 3) ks, (p.2,
      p.1) ∉ CGraph.cycleEdges (m + 3) := by
    intro p hp hrev
    have hc1 := (hcycle_bound _ hrev).1
    have hc2 := (hcycle_bound _ hrev).2
    have hpb := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 hp
    omega
  -- Reverse of cycle edge not in cycleEdges
  have hcycle_no_rev_in_cycle : ∀ p ∈ CGraph.cycleEdges (m + 3), (p.2, p.1) ∉ CGraph.cycleEdges (m
      + 3) := by
    intro p hp hmem
    rw [CGraph.mem_cycleEdges] at hp hmem
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hmem with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  -- Reverse of cycle edge not in pendantEdges (cycle edges have both endpoints < m+3; pendant edges
  -- have 2nd endpoint ≥ m+3)
  have hcycle_no_rev_in_pendant : ∀ p ∈ CGraph.cycleEdges (m + 3), (p.2,
      p.1) ∉ CGraph.pendantEdges 0 (m + 3) ks := by
    intro p hp hrev
    have hc := hcycle_bound _ hp
    have hpb := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.2 p.1 hrev
    omega
  -- Reverse of pendant edge not in pendantEdges (since pendant edges go forward)
  have hpendant_no_rev_in_pendant : ∀ p ∈ CGraph.pendantEdges 0 (m + 3) ks, (p.2,
      p.1) ∉ CGraph.pendantEdges 0 (m + 3) ks := by
    intro p hp hrev
    have hfwd := hpending_forward _ hp
    have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 hp
    simp at this
    have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.2 p.1 hrev
    simp at this
    omega
  -- pendantEdges is nodup
  have hpending_nodup : ∀ (v off : ℕ) (ks : List ℕ),
      List.Nodup (CGraph.pendantEdges v off ks) := by
    intro v off ks
    induction ks generalizing v off with
    | nil => simp [CGraph.pendantEdges]
    | cons k rest ih =>
      simp [CGraph.pendantEdges]
      apply List.Nodup.append
      · exact List.Nodup.map (fun i j hij => by injection hij with h1 h2; omega) List.nodup_range
      · exact ih (v + 1) (off + k)
      · intro x hxc hxp
        rcases List.mem_map.mp hxc with ⟨i, hi, rfl, rfl⟩
        have hbound := CGraph.mem_pendantEdges_bound (v + 1) (off + k) rest (v) (off + i) hxp
        omega
  -- cycleEdges and pendantEdges are disjoint
  have hdisjoint : Disjoint (CGraph.cycleEdges (m + 3)).toFinset (CGraph.pendantEdges 0 (m + 3)
      ks).toFinset := by
    rw [Finset.disjoint_left]
    intro p hp hpn
    have hc := hcycle_bound _ (by simpa using hp)
    have hpb := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 (by simpa using hpn)
    omega
  -- Nodup of the union
  have hunion_nodup : List.Nodup (CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m + 3)
      ks) := by
    apply List.Nodup.append hcycle_nodup (hpending_nodup 0 (m + 3) ks)
    intro p hpcy hppend
    exact Finset.disjoint_left.mp hdisjoint (List.mem_toFinset.mpr hpcy) (List.mem_toFinset.mpr
        hppend)
  -- No reverse in the union
  have hunion_norev : ∀ p ∈ CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m + 3) ks,
      (p.2, p.1) ∉ CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m + 3) ks := by
    intro p hp
    have hnotin_cycle : (p.2, p.1) ∉ CGraph.cycleEdges (m + 3) := by
      rcases List.mem_append.mp hp with h | h
      · exact hcycle_no_rev_in_cycle _ h
      · exact hpending_no_rev_in_cycle _ h
    have hnotin_pendant : (p.2, p.1) ∉ CGraph.pendantEdges 0 (m + 3) ks := by
      rcases List.mem_append.mp hp with h | h
      · exact hcycle_no_rev_in_pendant _ h
      · exact hpendant_no_rev_in_pendant _ h
    intro hmem
    rcases List.mem_append.mp hmem with h' | h'
    · exact hnotin_cycle h'
    · exact hnotin_pendant h'
  -- Bounds for union
  have hunion_bound : ∀ p ∈ CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m +
      3) ks, p.1 < m + 3 + ks.sum ∧ p.2 < m + 3 + ks.sum := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · have := hcycle_bound _ h
      exact ⟨by omega, by omega⟩
    · exact hpending_bound _ h
  -- No loops in union
  have hunion_noloop : ∀ p ∈ CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m +
      3) ks, p.1 ≠ p.2 := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hcycle_noloop _ h
    · exact hpending_noloop _ h
  -- Now apply ofEdges_E_helper
  rw [ofEdges_E_helper hunion_bound hunion_noloop hunion_norev hunion_nodup]
  rw [List.length_append, hcycle_len, hpending_len]

/-- The cycle keeps everything together and each pendant hangs off it. -/
theorem isConnected_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    IsConnected (cyclePendant (m + 3) ks) := by
  unfold IsoGraph.cyclePendant
  rw [IsoGraph.isConnected_mk]
  show CGraph.IsConnected _
  simp only [CGraph.IsConnected]
  haveI : Nonempty (CGraph.cyclePendant (m + 3) ks).V := by
    show Nonempty (Fin (m + 3 + ks.sum))
    exact ⟨0, by omega⟩
  apply SimpleGraph.Connected.mk
  · -- Preconnected: reachability from 0
    show SimpleGraph.Preconnected _
    -- All vertices are in Fin (m + 3 + ks.sum)
    --Cycle vertices: indices < m+3; Pendant vertices: indices ≥ m+3
    -- Pendant coverage: every index in [m+3, m+3+ks.sum) is a pendant vertex
    have hpend_cov : ∀ (ks : List ℕ) (v off : ℕ) (q : ℕ),
        off ≤ q → q < off + ks.sum →
        ∃ (p : ℕ), v ≤ p ∧ p < v + ks.length ∧ (p, q) ∈ CGraph.pendantEdges v off ks := by
      intro ks
      induction ks with
      | nil => intro v off q hq1 hq2; simp [List.sum] at hq2; omega
      | cons k ks ih =>
        simp only [List.sum_cons]
        intro v off q hq1 hq2
        by_cases hqk : q < off + k
        · exact ⟨v, le_refl v, by simp [List.length_cons], by
            simp [CGraph.pendantEdges, List.mem_append, List.mem_map, List.mem_range]
            exact Or.inl ⟨q - off, by omega, by omega⟩⟩
        · have hq1' : off + k ≤ q := by omega
          have hq2' : q < off + k + ks.sum := by omega
          obtain ⟨p', hp1', hp2', hp3'⟩ := ih (v + 1) (off + k) q hq1' hq2'
          exact ⟨p', by omega, by simp [List.length_cons]; omega, by
            simp [CGraph.pendantEdges]
            exact Or.inr hp3'⟩
    -- Pendant vertices are adjacent to some cycle vertex
    have hpend_adj : ∀ (q : ℕ) (hq2 : q < m + 3 + ks.sum), m + 3 ≤ q →
        ∃ (v : (CGraph.cyclePendant (m + 3) ks).V), v.val < m + 3 ∧
          (CGraph.cyclePendant (m + 3) ks).Adj v ⟨q, hq2⟩ := by
      intro q hq2 hq1
      obtain ⟨p, hp1, hp2, hp3⟩ := hpend_cov ks 0 (m + 3) q (by omega) hq2
      have hp_lt_m3 : p < m + 3 := by omega
      have hp_lt_N : p < m + 3 + ks.sum := by omega
      refine ⟨⟨p, hp_lt_N⟩, hp_lt_m3, ?_⟩
      have hne : (p : ℕ) ≠ q := by omega
      rw [CGraph.cyclePendant_adj_val]
      simp [hne]
      exact Or.inl (Or.inr hp3)
    have hindex_bound : ∀ (i : ℕ), i < m + 3 → i < m + 3 + ks.sum := fun i hi => by omega
    -- Cycle edges: (j, j+1) for j < m+2, as vertices of the graph
    let embed : Fin (m + 3) → (CGraph.cyclePendant (m + 3) ks).V := fun i => ⟨i.val, hindex_bound
        i.val i.isLt⟩
    let next : ∀ (j : Fin (m + 3)), j.val < m + 2 → Fin (m + 3) := fun j _ => ⟨j.val + 1, by omega⟩
    have hcycle_edge : ∀ (j : Fin (m + 3)) (hj : j.val < m + 2),
        (CGraph.cyclePendant (m + 3) ks).Adj (embed j) (embed (next j hj)) := by
      intro j hj
      rw [CGraph.cyclePendant_adj_val]
      simp only [embed, next]
      refine ⟨by omega, Or.inl ?_⟩
      apply List.mem_append_left
      rw [CGraph.mem_cycleEdges]
      exact Or.inl ⟨rfl, by omega⟩
    -- Reachability to all cycle vertices from 0
    have hcycle_reach : ∀ (i : Fin (m + 3)),
        (CGraph.cyclePendant (m + 3) ks).toSimple.Reachable
          (embed ⟨0, by omega⟩) (embed i) := by
      intro i
      have : ∀ (n : ℕ) (hn : n < m + 3),
          (CGraph.cyclePendant (m + 3) ks).toSimple.Reachable
            (embed ⟨0, by omega⟩) (embed ⟨n, hn⟩) := by
        intro n
        induction n with
        | zero => intro hn; rfl
        | succ j ih =>
          intro hj
          have hj' : j < m + 3 := by omega
          have hj'' : j < m + 2 := by omega
          exact (ih hj').trans (SimpleGraph.Adj.reachable (show (CGraph.cyclePendant (m + 3)
              ks).toSimple.Adj (embed ⟨j, hj'⟩) (embed (next ⟨j, hj'⟩
                  hj'')) by simpa using hcycle_edge ⟨j, hj'⟩ hj''))
      exact this i i.isLt
    -- Reachability to all pendant vertices from 0
    have hpend_reach : ∀ (q : ℕ) (hq2 : q < m + 3 + ks.sum), m + 3 ≤ q →
        (CGraph.cyclePendant (m + 3) ks).toSimple.Reachable
          (embed ⟨0, by omega⟩) (⟨q, hq2⟩ : (CGraph.cyclePendant (m + 3) ks).V) := by
      intro q hq2 hq1
      obtain ⟨v, hv_lt, havj⟩ := hpend_adj q hq2 hq1
      exact (hcycle_reach ⟨v.val, hv_lt⟩).trans (SimpleGraph.Adj.reachable (show
          (CGraph.cyclePendant (m + 3) ks).toSimple.Adj v ⟨q, hq2⟩ by simpa using havj))
    -- Reachability to all vertices from 0
    have hreach : ∀ (v : (CGraph.cyclePendant (m + 3) ks).V),
        (CGraph.cyclePendant (m + 3) ks).toSimple.Reachable (embed ⟨0, by omega⟩) v := by
      intro ⟨vi, hvi⟩
      by_cases hvi_lt : vi < m + 3
      · exact hcycle_reach ⟨vi, hvi_lt⟩
      · exact hpend_reach vi hvi (by omega)
    exact fun u v => (hreach u).symm.trans (hreach v)

theorem numComponents_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    (cyclePendant (m + 3)
        ks).numComponents = 1 := numComponents_eq_one_of_isConnected (isConnected_cyclePendant m ks
            h)

/-- The far end of any leg is a pendant. -/
theorem minDeg_spider (legs : List ℕ) (h : 0 < legs.sum) : minDeg (spider legs) = 1 := by
  induction legs with
  | nil => simp at h
  | cons k rest ih =>
    by_cases hk : k = 0
    · subst hk; rw [spider_zero_cons]; exact ih (by simp [List.sum_cons] at h; omega)
    · -- k > 0 case
      have hk0 : 0 < k := Nat.pos_of_ne_zero hk
      -- spider (k :: rest) = ofEdges (1 + k + rest.sum) (spiderEdges 1 (k :: rest))
      -- spiderEdges 1 (k :: rest) = legEdges 0 1 k ++ spiderEdges (1+k) rest
      -- Vertex k (index k) has degree 1 (pendant at end of first leg).
      -- Every vertex has degree ≥ 1.
      apply le_antisymm
      · -- minDeg ≤ 1: vertex ⟨k, _⟩ has degree ≤ 1
        simp [IsoGraph.minDeg, IsoGraph.spider, CGraph.minDeg]
        have hk_lt : k < 1 + (k :: rest).sum := by simp [List.sum_cons]; omega
        let v : (CGraph.spider (k :: rest)).V := ⟨k, hk_lt⟩
        have hdeg : (CGraph.spider (k :: rest)).toSimple.degree v ≤ 1 := by
          rw [← CGraph.card_nbrs_eq_degree]
          have hsub : (CGraph.spider (k :: rest)).nbrs v ⊆ {⟨k - 1, by omega⟩} := by
            intro w hw
            rw [CGraph.mem_nbrs, CGraph.spider_adj_val] at hw
            simp only [show v.val = k from rfl, CGraph.spiderEdges, List.mem_append] at hw
            rcases hw with ⟨hne, hor⟩
            -- (k, w.1) ∉ spiderEdges (1+k) rest and (w.1, k) ∉ spiderEdges (1+k) rest
            have hnot_spider : (k, w.1) ∉ CGraph.spiderEdges (1 + k) rest ∧ (w.1,
                k) ∉ CGraph.spiderEdges (1 + k) rest := by
              constructor <;> intro hmem
              · have := CGraph.mem_spiderEdges_bound (1 + k) rest k w.1 hmem
                omega
              · have := CGraph.mem_spiderEdges_bound (1 + k) rest w.1 k hmem
                omega
            rcases hor with hor | hor
            · -- (v,w) ∈ legEdges 0 1 k ∨ (v,w) ∈ spiderEdges (1+k) rest
              rcases hor with hle | hspider
              · rw [CGraph.mem_legEdges] at hle
                rcases hle with ⟨hv0, hw1, _⟩ | ⟨h1v, hwv, hlt⟩
                · exfalso; have hv : v.val = k := rfl; omega
                · exfalso; have hv : v.val = k := rfl; omega
              · exfalso; exact hnot_spider.1 hspider
            · -- (w,v) ∈ legEdges 0 1 k ∨ (w,v) ∈ spiderEdges (1+k) rest
              rcases hor with hle | hspider
              · rw [CGraph.mem_legEdges] at hle
                rcases hle with ⟨hw0, hv1, _⟩ | ⟨h1w, hvw, hlt'⟩
                · have hk1 : k = 1 := by
                    have : v.val = k := rfl
                    omega
                  subst hk1
                  let v2 : (CGraph.spider (1 :: rest)).V := ⟨0, by omega⟩
                  exact Finset.mem_singleton.mpr (Fin.ext hw0)
                · let v2 : (CGraph.spider (k :: rest)).V := ⟨k - 1, by omega⟩
                  have hwk : w.val = v2.val := by
                    simp [v2]; omega
                  exact Finset.mem_singleton.mpr (Fin.ext hwk)
              · exfalso; exact hnot_spider.2 hspider
          exact Finset.card_le_one.mpr (fun x hx y hy =>
              by rw [Finset.mem_singleton.mp (hsub hx), Finset.mem_singleton.mp (hsub hy)])
        exact le_trans (CGraph.minDeg_le_degree _ v) hdeg
      · -- 1 ≤ minDeg: every vertex has degree ≥ 1
        -- Off-general lemma: for off ≥ 1 and legs with legs.sum > 0,
        -- every vertex v of ofEdges (off + legs.sum) (spiderEdges off legs) with off ≤ v.val
        -- has degree ≥ 1.
        have h_off_gen : ∀ (off : ℕ) (legs : List ℕ), 1 ≤ off → 0 < legs.sum →
            ∀ v : (CGraph.ofEdges (off + legs.sum) (CGraph.spiderEdges off legs)).V,
            off ≤ v.val → 1 ≤ (CGraph.ofEdges (off + legs.sum) (CGraph.spiderEdges off
                legs)).toSimple.degree v := by
          intro off legs
          induction legs generalizing off with
          | nil =>
            intro _ hlegs_sum _ _; simp [List.sum_nil] at hlegs_sum
          | cons l rs ih =>
            intro h_off hlegs_sum v hv_off
            have hsum_eq : off + (l :: rs).sum = (off + l) + rs.sum := by simp [List.sum_cons]; ring
            let v'' : Fin ((off + l) + rs.sum) := Fin.cast hsum_eq v
            have hv_val : v.val = v''.val := rfl
            -- Degree casting lemma
            have hdeg_cast : ∀ {n m : ℕ} (e : n = m) (es : List (ℕ × ℕ))
                (hend : ∀ ep eq, (ep, eq) ∈ es → ep < n ∧ eq < n)
                (vend : ∀ ep eq, (ep, eq) ∈ es → ep < m ∧ eq < m)
                (u : Fin n) (u' : Fin m), u.val = u'.val →
                (CGraph.ofEdges n es).toSimple.degree u =
                (CGraph.ofEdges m es).toSimple.degree u' := by
              intro n m e es hend vend u u' hu_val; subst e; rw [Fin.ext hu_val]
            have spider_bound : ∀ ep eq, (ep, eq) ∈ CGraph.spiderEdges off (l :: rs) →
                ep < off + (l :: rs).sum ∧ eq < off + (l :: rs).sum := by
              intro ep eq hmem
              rcases CGraph.mem_spiderEdges_bound off (l :: rs) ep eq hmem with ⟨hp | ⟨_, hp2⟩,
                  hq1, hq2⟩
              · exact ⟨by omega, by omega⟩
              · exact ⟨by omega, by omega⟩
            have hdeg_eq : (CGraph.ofEdges (off + (l :: rs).sum) (CGraph.spiderEdges off (l ::
                rs))).toSimple.degree v =
                (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges off (l ::
                    rs))).toSimple.degree v'' := by
              exact hdeg_cast hsum_eq _
                (fun ep eq hmem => by
                  rcases spider_bound ep eq hmem with ⟨h1, h2⟩
                  rw [hsum_eq] at h1 h2 ⊢; exact ⟨h1, h2⟩)
                (fun ep eq hmem => by
                  rcases spider_bound ep eq hmem with ⟨h1, h2⟩
                  rw [hsum_eq] at h1 h2
                  exact ⟨by omega, by omega⟩)
                v v'' hv_val
            suffices h : 1 ≤ (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges off (l ::
                rs))).toSimple.degree v'' by
              linarith
            have hsplit : CGraph.spiderEdges off (l ::
                rs) = CGraph.legEdges 0 off l ++ CGraph.spiderEdges (off + l) rs := by
              simp [CGraph.spiderEdges]
            have handheld_edges : ∀ e : ℕ × ℕ, e ∈ CGraph.legEdges 0 off l → e.1 < off + l ∧ e.2 <
                off + l := by
              intro ⟨p, q⟩ hmem
              rw [CGraph.mem_legEdges] at hmem
              rcases hmem with ⟨rfl, rfl, hl0⟩ | ⟨h1p, rfl, hlt⟩ <;> constructor <;> omega
            by_cases hl : l = 0
            · subst hl
              simp only [List.sum_cons, zero_add] at hsum_eq ⊢
              -- spiderEdges off (0::rs) = spiderEdges off rs, and off+0+rs.sum = off+rs.sum
              have hspider : CGraph.spiderEdges off (0 :: rs) = CGraph.spiderEdges off rs := by
                simp [CGraph.spiderEdges, CGraph.legEdges]
              have hbdd : off + 0 + rs.sum = off + rs.sum := by omega
              have spider_bound_rs : ∀ ep eq, (ep, eq) ∈ CGraph.spiderEdges off rs →
                  ep < off + rs.sum ∧ eq < off + rs.sum := by
                intro ep eq hmem
                have := CGraph.mem_spiderEdges_bound off rs ep eq hmem
                omega
              have hv_rs : v.val < off + rs.sum := by
                have : (0 :: rs).sum = rs.sum := by simp
                omega
              let v' : (CGraph.ofEdges (off + rs.sum) (CGraph.spiderEdges off rs)).V := ⟨v.val,
                  hv_rs⟩
              have hdeg_eq' : (CGraph.ofEdges (off + (0 :: rs).sum) (CGraph.spiderEdges off (0 ::
                  rs))).toSimple.degree v =
                  (CGraph.ofEdges (off + rs.sum) (CGraph.spiderEdges off
                      rs)).toSimple.degree v' := by
                apply hdeg_cast
                · simp [List.sum_cons]
                · intro ep eq hmem
                  have := spider_bound ep eq (by rw [hspider] at hmem ⊢; exact hmem)
                  omega
                · exact spider_bound_rs
                · exact rfl
              have hdeg_eq'' : (CGraph.ofEdges (off + rs.sum) (CGraph.spiderEdges off
                  rs)).toSimple.degree v' =
                  (CGraph.ofEdges (off + 0 + rs.sum) (CGraph.spiderEdges off (0 ::
                      rs))).toSimple.degree v'' := by
                rw [← hdeg_eq', hdeg_eq]
              rw [← hdeg_eq'']
              exact ih off h_off (by simp at hlegs_sum; omega) v' hv_off
            · have hl0 : 0 < l := Nat.pos_of_ne_zero hl
              by_cases hvleg : v.val < off + l
              ·
                rw [SimpleGraph.degree, CGraph.neighborFinset_eq_nbrs]
                by_cases hv_off_eq : v.val = off
                ·
                  have hv''_zero : v''.val = off := by omega
                  have hedge : (0, off) ∈ CGraph.spiderEdges off (l :: rs) := by
                    rw [hsplit]
                    exact List.mem_append.mpr (Or.inl
                        (by rw [CGraph.mem_legEdges]; exact Or.inl ⟨rfl, rfl, hl0⟩))
                  have hmem : (⟨0, by omega⟩ : (CGraph.ofEdges ((off + l) + rs.sum)
                      (CGraph.spiderEdges off (l :: rs))).V) ∈ (CGraph.ofEdges ((off +
                          l) + rs.sum) (CGraph.spiderEdges off (l :: rs))).nbrs v'' := by
                    rw [CGraph.mem_nbrs, CGraph.ofEdges_adj_val]
                    simp [hv''_zero]
                    exact ⟨by omega, Or.inr hedge⟩
                  exact Finset.one_le_card.mpr ⟨_, hmem⟩
                ·
                  have hv_gt_off : off < v''.val := by omega
                  -- neighbor v''-1 via edge (v''-1, v'') in legEdges 0 off l
                  have hedge : ((v''.val - 1, v''.val) : ℕ × ℕ) ∈ CGraph.spiderEdges off (l ::
                      rs) := by
                    exact List.mem_append.mpr (Or.inl
                        (by rw [CGraph.mem_legEdges]; exact Or.inr ⟨by omega, by omega, by omega⟩))
                  have hmem : (⟨v''.val - 1, by omega⟩ : (CGraph.ofEdges ((off + l) + rs.sum)
                      (CGraph.spiderEdges off (l :: rs))).V) ∈ (CGraph.ofEdges ((off +
                          l) + rs.sum) (CGraph.spiderEdges off (l :: rs))).nbrs v'' := by
                    rw [CGraph.mem_nbrs, CGraph.ofEdges_adj_val]
                    simp
                    exact ⟨by omega, Or.inr hedge⟩
                  exact Finset.one_le_card.mpr ⟨_, hmem⟩
              ·
                push_neg at hvleg
                have hvtoff : off + l ≤ v''.val := by omega
                have hrs_pos : 0 < rs.sum := by omega
                have hvleg_not : ¬ (v''.val < off + l) := by omega
                have hv_not_adjl : ∀ w : Fin ((off + l) + rs.sum),
                    ¬ (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.legEdges 0 off
                        l)).Adj v'' w := by
                  intro w; rw [CGraph.ofEdges_adj_val]
                  intro hadj; obtain ⟨hne, hor⟩ := hadj
                  rcases hor with hor | hor
                  · have := handheld_edges _ hor |>.1; omega
                  · have := handheld_edges _ hor |>.2; omega
                have hw_not_adjl : ∀ w : Fin ((off + l) + rs.sum),
                    ¬ (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.legEdges 0 off
                        l)).Adj w v'' := by
                  intro w; rw [CGraph.ofEdges_adj_val]
                  intro hadj; obtain ⟨hne, hor⟩ := hadj
                  rcases hor with hor | hor
                  · have := handheld_edges _ hor |>.2; omega
                  · have := handheld_edges _ hor |>.1; omega
                have hneighbor_eq : ∀ w : Fin ((off + l) + rs.sum),
                    (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges off (l ::
                        rs))).Adj v'' w ↔
                    (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges (off + l)
                        rs)).Adj v'' w := by
                  intro w
                  rw [hsplit, CGraph.ofEdges_adj_val, CGraph.ofEdges_adj_val]
                  simp only [List.mem_append]
                  constructor
                  · intro ⟨hne, hor⟩
                    -- hor : ((v'',w) ∈ leg ∨ (v'',w) ∈ spider) ∨ ((w,v'') ∈ leg ∨ (w,v'') ∈ spider)
                    have : (↑v'', ↑w) ∈ CGraph.spiderEdges (off + l) rs ∨ (↑w,
                        ↑v'') ∈ CGraph.spiderEdges (off + l) rs := by
                      rcases hor with hor | hor
                      · rcases hor with hor | hor
                        · exfalso; have := handheld_edges _ hor |>.1; omega
                        · exact Or.inl hor
                      · rcases hor with hor | hor
                        · exfalso; have := handheld_edges _ hor |>.2; omega
                        · exact Or.inr hor
                    exact ⟨hne, this⟩
                  · intro ⟨hne, hor⟩
                    obtain h1 | h2 := hor
                    · exact ⟨hne, Or.inl (Or.inr h1)⟩
                    · exact ⟨hne, Or.inr (Or.inr h2)⟩
                have hdeg_local : (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges off (l
                    :: rs))).toSimple.degree v'' =
                    (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges (off + l)
                        rs)).toSimple.degree v'' := by
                  simp only [SimpleGraph.degree, CGraph.neighborFinset_eq_nbrs]
                  have : (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges off (l ::
                      rs))).nbrs v'' =
                         (CGraph.ofEdges ((off + l) + rs.sum) (CGraph.spiderEdges (off + l)
                             rs)).nbrs v'' := by
                    ext w; rw [CGraph.mem_nbrs, CGraph.mem_nbrs]; exact hneighbor_eq w
                  rw [this]
                rw [hdeg_local]
                exact ih (off + l) (by omega) hrs_pos v'' (by omega)
        -- Now prove the lower bound for spider (k :: rest)
        apply CGraph.le_minDeg_of_forall (⟨0, by omega⟩ : (CGraph.spider (k :: rest)).V)
        intro v
        by_cases hv0 : v.val = 0
        ·
          show 1 ≤ (CGraph.spider (k :: rest)).toSimple.degree v
          rw [SimpleGraph.degree, CGraph.neighborFinset_eq_nbrs]
          have hmem : ⟨1, by omega⟩ ∈ (CGraph.spider (k :: rest)).nbrs v := by
            rw [CGraph.mem_nbrs, CGraph.spider_adj_val]
            simp [hv0]
            left
            exact List.mem_append_left _ (by rw [CGraph.mem_legEdges]; exact Or.inl ⟨rfl, rfl, hk0⟩)
          exact Finset.one_le_card.mpr ⟨_, hmem⟩
        ·
          show 1 ≤ (CGraph.spider (k :: rest)).toSimple.degree v
          have hv1 : 1 ≤ v.val := Nat.pos_of_ne_zero hv0
          simp
          have := h_off_gen 1 (k :: rest) (by omega) (by omega) v hv1
          exact this

/-- A pendant vertex has degree one. -/
theorem minDeg_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) (h2 : 0 < ks.sum) :
    minDeg (cyclePendant (m + 3) ks) = 1 := by
  -- Key helper:pendant vertices (≥ m+3) have degree exactly 1
  -- Key helper 2: cycle vertices (< m+3) have degree ≥ 2
  -- Upper bound: vertex m+3 has degree 1, so minDeg ≤ 1
  -- Lower bound: all vertices have degree ≥ 1, so 1 ≤ minDeg
  set n := m + 3 with hn_def
  -- Helper: cycle edges only involve vertices < n
  have hcyc_bounds : ∀ a b : ℕ, (a, b) ∈ CGraph.cycleEdges n → a < n ∧ b < n := by
    intro a b hab
    rw [CGraph.mem_cycleEdges] at hab
    rcases hab with ⟨hlt, hlt2⟩ | ⟨heq, hb0⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  -- Helper: m+3 cannot be in any cycle edge (as either component)
  have hnot_in_cycle : ∀ q : ℕ, (n, q) ∉ CGraph.cycleEdges n ∧ (q, n) ∉ CGraph.cycleEdges n := by
    intro q
    exact ⟨fun h => by obtain ⟨ha, hb⟩ := hcyc_bounds n q h; omega,
           fun h => by obtain ⟨ha, hb⟩ := hcyc_bounds q n h; omega⟩
  -- Helper: pendant edge first component is < ks.length ≤ n
  have hpending_first_lt : ∀ p q : ℕ, (p, q) ∈ CGraph.pendantEdges 0 n ks → p < n := by
    intro p q hpq
    have := CGraph.mem_pendantEdges_bound 0 n ks p q hpq
    omega
  -- Helper: m+3 cannot be first component of any pendant edge
  have hnot_first_pendant : ∀ q : ℕ, (n, q) ∉ CGraph.pendantEdges 0 n ks := by
    intro q h
    have := hpending_first_lt n q h
    omega
  -- Helper: pendant vertices (≥ n) can only appear as second component of pendant edges
  -- For degree = 1 of vertex n: its only possible neighbor is via a pendant edge (n.owner, n)
  -- pendantEdges covers its stated range (second component)
  -- More general: for any v, off, ks, every q in [off, off + ks.sum) appears as second component
  have hpendant_exists : ∀ (v off : ℕ) (ks : List ℕ) (q : ℕ),
      off ≤ q → q < off + ks.sum →
      ∃ p : ℕ, (p, q) ∈ CGraph.pendantEdges v off ks := by
    clear h h2 hcyc_bounds hnot_in_cycle hpending_first_lt hnot_first_pendant hn_def
    suffices h : ∀ (ks : List ℕ), ∀ (v off : ℕ) (q : ℕ),
        off ≤ q → q < off + ks.sum → ∃ p, (p, q) ∈ CGraph.pendantEdges v off ks by
      exact fun v off ks q hle hlt => h ks v off q hle hlt
    intro ks
    induction ks with
    | nil => intro q hle hlt; show hle ≤ hlt → hlt < hle + [].sum → _; intro _ hlt'; rw
        [List.sum_nil] at hlt'; omega
    | cons k rest ih =>
      intro q hle hlt hk1 hk2
      have hk2' : hlt < hle + (k + rest.sum) := by
        rwa [List.sum_cons] at hk2
      by_cases hk3 : hlt < hle + k
      · refine ⟨q, ?_⟩
        rw [CGraph.pendantEdges]
        apply List.mem_append.mpr
        left
        exact List.mem_map.mpr ⟨hlt - hle, List.mem_range.mpr (by omega), by ext <;> omega⟩
      · push_neg at hk3
        have hlt'' : hlt < hle + k + rest.sum := by omega
        obtain ⟨p, hp⟩ := ih (q + 1) (hle + k) hlt (by omega) hlt''
        exact ⟨p, by simp [CGraph.pendantEdges]; exact Or.inr hp⟩
  -- Uniqueness: each pendant vertex (second component) appears in at most one pendant edge
  have hpendant_second_unique : ∀ (ks : List ℕ) (v off : ℕ) (p1 p2 q : ℕ),
      (p1, q) ∈ CGraph.pendantEdges v off ks →
      (p2, q) ∈ CGraph.pendantEdges v off ks → p1 = p2 := by
    intro ks
    induction ks with
    | nil =>
      intro v off p1 p2 q h1 h2; simp [CGraph.pendantEdges] at h1 h2
    | cons k rest ih =>
      intro v off p1 p2 q h1 h2
      simp [CGraph.pendantEdges, List.mem_append, List.mem_map, List.mem_range,
          Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨a1, ha1, hp1, hq1⟩ | h1'
      · rcases h2 with ⟨a2, ha2, hp2, hq2⟩ | h2'
        · subst hp1; subst hp2; rfl
        · have := CGraph.mem_pendantEdges_bound (v + 1) (off + k) rest p2 q h2'
          omega
      · have := CGraph.mem_pendantEdges_bound (v + 1) (off + k) rest p1 q h1'
        rcases h2 with ⟨a2, ha2, hp2, hq2⟩ | h2'
        · omega
        · exact ih (v + 1) (off + k) p1 p2 q h1' h2'
  have hm3lt : n < n + ks.sum := by omega
  let v : (CGraph.cyclePendant n ks).V := ⟨n, hm3lt⟩
  -- pendant vertex n has exactly one neighbor (its owner)
  -- Get the owner p of pendant vertex n
  obtain ⟨p, hp⟩ := hpendant_exists 0 n ks n (by omega) hm3lt
  -- p < n (first component of pendant edge)
  have hp_lt : p < n := hpending_first_lt p n hp
  -- The vertex ⟨p, by omega⟩ in cyclePendant n ks is adjacent to v
  let wp : (CGraph.cyclePendant n ks).V := ⟨p, by omega⟩
  -- Adjacency v ~ wp
  have hadj_vp : (CGraph.cyclePendant n ks).Adj v wp := by
    rw [CGraph.cyclePendant_adj_val]
    simp [v, wp]
    exact ⟨by omega, Or.inr (Or.inr hp)⟩
  -- No other vertex is adjacent to v
  have honly_neighbor : ∀ w : (CGraph.cyclePendant n ks).V,
      (CGraph.cyclePendant n ks).Adj v w → w = wp := by
    intro w hw
    rw [CGraph.cyclePendant_adj_val] at hw
    simp [v] at hw
    obtain ⟨hne, heir⟩ := hw
    -- heir : (n, w.1) ∈ cycleEdges n ++ pendantEdges 0 n ks ∨ (w.1, n) ∈ cycleEdges n ++
    -- pendantEdges 0 n ks
    rcases heir with heir | heir
    · -- (n, ↑w) in cycleEdges or pendantEdges
      rcases heir with heir2 | heir2
      · exact absurd (hcyc_bounds n w.1 heir2) (by omega)
      · exact False.elim (hnot_first_pendant _ heir2)
    · -- (↑w, n) in pendantEdges (or cycleEdges, but n not in cycle edges)
      rcases heir with heir2 | heir2
      · exact absurd (hcyc_bounds w.1 n heir2) (by omega)
      · have heq := hpendant_second_unique ks 0 n w.1 p n heir2 hp
        exact Fin.ext (by simp [wp, heq])
  -- degree(v) = 1
  have hnbrs_eq : CGraph.nbrs (CGraph.cyclePendant n ks) v = {wp} := by
    ext w; simp [Finset.mem_singleton]
    exact ⟨honly_neighbor w, fun hw => hw.symm ▸ hadj_vp⟩
  have hdeg_v : (CGraph.cyclePendant n ks).toSimple.degree v = 1 := by
    rw [SimpleGraph.degree]
    have hns : (CGraph.cyclePendant n ks).toSimple.neighborSet v = {wp} := by
      ext w; simp
      exact ⟨fun hw => honly_neighbor w hw, fun hw => hw.symm ▸ hadj_vp⟩
    simp [SimpleGraph.neighborFinset, hns, Finset.card_singleton]
  have hminDeg_le : (CGraph.cyclePendant n ks).minDeg ≤ 1 := by
    exact le_trans (CGraph.minDeg_le_degree _ _) hdeg_v.le
  -- All vertices have degree ≥ 1
  have hall_ge_one : ∀ w : (CGraph.cyclePendant n ks).V, 1 ≤ (CGraph.cyclePendant n
      ks).toSimple.degree w := by
    intro w
    set wf := w.1
    have hwlt := w.isLt
    have hexists : ∃ u, (CGraph.cyclePendant n ks).toSimple.Adj w u := by
      by_cases hwc : wf < n
      · -- cycle vertex
        by_cases hw1 : wf + 1 < n
        · let u : (CGraph.cyclePendant n ks).V := ⟨wf + 1, by omega⟩
          have hadj : (CGraph.cyclePendant n ks).Adj w u = true := by
            rw [CGraph.cyclePendant_adj_val]
            simp [u]
            have hmem : ((w.val, wf + 1)) ∈ CGraph.cycleEdges n := by
              rw [CGraph.mem_cycleEdges]
              exact Or.inl ⟨rfl, hw1⟩
            exact ⟨by omega, Or.inl (Or.inl hmem)⟩
          exact ⟨u, by rwa [CGraph.toSimple_adj]⟩
        · have hw1eq : wf + 1 = n := by omega
          let u : (CGraph.cyclePendant n ks).V := ⟨0, by omega⟩
          have hadj : (CGraph.cyclePendant n ks).Adj w u = true := by
            rw [CGraph.cyclePendant_adj_val]
            simp [u]
            have hmem : ((w.val, 0)) ∈ CGraph.cycleEdges n := by
              rw [CGraph.mem_cycleEdges]
              exact Or.inr ⟨hw1eq, rfl⟩
            have hne : (w ≠ ⟨0, by omega⟩) := by
              intro h; have : w.val = 0 := by simp [h]
              omega
            exact ⟨hne, Or.inl (Or.inl hmem)⟩
          exact ⟨u, by rwa [CGraph.toSimple_adj]⟩
      · -- pendant vertex
        push_neg at hwc
        have hwpending : n ≤ wf ∧ wf < n + ks.sum := ⟨hwc, hwlt⟩
        obtain ⟨p, hp⟩ := hpendant_exists 0 n ks wf hwpending.1 hwpending.2
        have hp_lt : p < n := hpending_first_lt p wf hp
        let u : (CGraph.cyclePendant n ks).V := ⟨p, by omega⟩
        have hadj : (CGraph.cyclePendant n ks).Adj w u = true := by
          rw [CGraph.cyclePendant_adj_val]
          simp [u]
          have hne : w.val ≠ p := ne_of_gt (by omega : p < w.val)
          exact ⟨hne, Or.inr (Or.inr hp)⟩
        exact ⟨u, by rwa [CGraph.toSimple_adj]⟩
    have hpos : 0 < (CGraph.cyclePendant n ks).toSimple.degree w := by
      rwa [SimpleGraph.degree_pos_iff_exists_adj]
    omega

  show IsoGraph.minDeg (cyclePendant n ks) = 1
  simp [IsoGraph.minDeg_mk, IsoGraph.cyclePendant]
  exact le_antisymm hminDeg_le (CGraph.le_minDeg_of_forall v hall_ge_one)

/-- The two centres are a vertex cover, and one vertex is not. -/
theorem coverNum_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).coverNum = 2 := by
  rw [coverNum_eq, V_doubleStar, indepNum_doubleStar]
  omega

/-- Only the two centres carry any edges, so the rest of a clique cover is singletons. -/
theorem cliqueCoverNum_doubleStar (m n : ℕ) :
    (doubleStar (m + 1) (n + 1)).cliqueCoverNum = m + n + 2 := by
  have hlow : m + n + 2 ≤ (doubleStar (m + 1) (n + 1)).cliqueCoverNum := by
    rw [← indepNum_doubleStar]
    exact indepNum_le_cliqueCoverNum _
  have h.high : (doubleStar (m + 1) (n + 1)).cliqueCoverNum ≤ m + n + 2 := by
    have hV : (doubleStar (m + 1) (n + 1)).V = m + n + 4 := by
      simp [IsoGraph.doubleStar, IsoGraph.V_mk, CGraph.card_doubleStar]; omega
    have hm := matchNum_doubleStar m n
    have h1 := cliqueCoverNum_le_V_sub_matchNum (doubleStar (m + 1) (n + 1))
    rw [hV, hm] at h1
    omega
  exact le_antisymm h.high hlow

/-- An odd cycle needs three colours, and the tail needs no more. -/
theorem chromNum_tadpole_odd (m k : ℕ) : (tadpole (2 * m + 3) k).chromNum = 3 := by
  rw [tadpole_def, chromNum_mk]
  rw [CGraph.chromNum_eq_iff]
  set G := CGraph.tadpole (2 * m + 3) k
  refine ⟨?_, ?_⟩
  · -- Colorable with 3 colors
    -- Coloring function: 0 ↦ 2, i (1 ≤ i < 2m+3) ↦ i%2, path vertices ↦ alternating 0,1
    let c : Fin (2 * m + 3 + k) → Fin 3 := fun i =>
      if hi : i.val < 2 * m + 3 then
        if hi0 : i.val = 0 then
          Fin.last 2
        else
          Fin.mk (i.val % 2) (by omega)
      else
        Fin.mk ((i.val - (2 * m + 3)) % 2) (by omega)
    refine ⟨c, ?_⟩
    have hc_ne_cycle : ∀ u v : Fin (2 * m + 3 + k),
        (u.val, v.val) ∈ CGraph.cycleEdges (2 * m + 3) → (c u).val ≠ (c v).val := by
      intro u v hmem
      simp only [c]
      rw [CGraph.mem_cycleEdges] at hmem
      rcases hmem with ⟨hv1, hu1⟩ | ⟨hu1, hv0⟩
      · simp only [hv1, hu1]
        split_ifs <;> simp <;> omega
      · simp only [hv0]
        have hu_val : (u : ℕ) = 2 * m + 2 := by omega
        simp [hu_val]
    have hc_ne_leg : ∀ u v : Fin (2 * m + 3 + k),
        (u.val, v.val) ∈ CGraph.legEdges 0 (2 * m + 3) k → (c u).val ≠ (c v).val := by
      intro u v hmem
      simp only [c]
      rw [CGraph.mem_legEdges] at hmem
      rcases hmem with ⟨hu0, hv_off, hkpos⟩ | ⟨hlop, hv_eq, hunil⟩
      · -- (u,v) = (0, 2*m+3), edge from cycle center to path start
        simp only [hu0, hv_off]
        split_ifs <;> simp <;> omega
      · -- (u,v) = (p, p+1) on the path, p ≥ 2*m+3
        simp only [hv_eq]
        split_ifs <;> simp <;> omega
    have hc_ne : ∀ u v : Fin (2 * m + 3 + k),
        (u ≠ v) → ((u.val, v.val) ∈ CGraph.cycleEdges (2 * m + 3) ++ CGraph.legEdges 0 (2 * m + 3)
            k ∨
          (v.val, u.val) ∈ CGraph.cycleEdges (2 * m + 3) ++ CGraph.legEdges 0 (2 * m + 3) k) →
        (c u).val ≠ (c v).val := by
      intro u v hne hmem
      rcases hmem with hmem | hmem
      · rcases List.mem_append.mp hmem with hmem | hmem
        · exact hc_ne_cycle u v hmem
        · exact hc_ne_leg u v hmem
      · rcases List.mem_append.mp hmem with hmem | hmem
        · exact fun h => (hc_ne_cycle v u hmem) (by rw [h])
        · exact fun h => (hc_ne_leg v u hmem) (by rw [h])
    intro u v huv
    rw [CGraph.toSimple_adj] at huv
    unfold G at huv
    rw [CGraph.tadpole_adj_val] at huv
    have hn := huv.1
    have hm := huv.2
    intro h
    exact (hc_ne u v (fun heq => hn (by rw [heq])) hm) (by rw [h])
  · -- Lower bound
    intro m_1 hm_1
    by_contra h
    push_neg at h
    have h2 : G.toSimple.Colorable 2 := by
      have : m_1 ≤ 2 := by omega
      exact hm_1.mono this
    have hbip : G.IsBipartite := (CGraph.isBipartite_iff_colorable G).mpr h2
    exact CGraph.not_isBipartite_ofEdges_of_odd_cycle
      (2 * m + 3 + k) (2 * m + 3) (CGraph.cycleEdges (2 * m + 3) ++ CGraph.legEdges 0 (2 * m + 3) k)
      (by omega) (by omega) (by omega)
      (fun p q h => Or.inl (List.mem_append_left _ h)) hbip

/-- An even cycle with pendants hung on it is bipartite and has an edge. -/
theorem chromNum_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t + 2) :
    (cyclePendant (2 * t + 2) ks).chromNum = 2 := by
  have hcgh : IsoGraph.chromNum (cyclePendant (2 * t + 2) ks) =
      (CGraph.cyclePendant (2 * t + 2) ks).chromNum := IsoGraph.chromNum_mk _
  rw [hcgh]
  -- Colorability (upper bound)
  have hc2 : (CGraph.cyclePendant (2 * t + 2) ks).toSimple.Colorable 2 := by
    refine ⟨fun i => ⟨CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks (i : Fin (2 * t + 2 +
        ks.sum)).1 % 2,
      Nat.mod_lt _ (by omega)⟩, ?_⟩
    intro x y hxy
    rw [CGraph.toSimple_adj] at hxy
    rw [CGraph.cyclePendant_adj_val] at hxy
    show ¬_ = _
    simp only [Fin.ext_iff]
    have key : ∀ p q : ℕ, (p, q) ∈ CGraph.cycleEdges (2 * t + 2) ++ CGraph.pendantEdges 0 (2 * t +
        2) ks →
        (CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks p
          + CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks q) % 2 = 1 := by
      intro p q hpq
      rw [List.mem_append] at hpq
      rcases hpq with hpq | hpq
      · rw [CGraph.mem_cycleEdges] at hpq
        rw [CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega),
          CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega)]
        omega
      · exact CGraph.pendantOwner_parity (2 * t + 2) 0 (2 * t + 2) ks p q (by omega) (by omega) hpq
    rcases hxy.2 with hm | hm
    · have hk := key x.1 y.1 hm
      intro heq
      have : (CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks x.1 +
        CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks y.1) % 2 = 0 := by omega
      omega
    · have hk := key y.1 x.1 hm
      intro heq; omega
  -- Edge (lower bound)
  have hmem : (0, 1) ∈ CGraph.cycleEdges (2 * t + 2) := by
    rw [CGraph.mem_cycleEdges]
    left; omega
  have hadj : (CGraph.cyclePendant (2 * t + 2) ks).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    rw [CGraph.cyclePendant_adj_val]
    simp [hmem]
  have hge : 2 ≤ (CGraph.cyclePendant (2 * t + 2) ks).chromNum :=
    CGraph.two_le_chromNum_of_adj hadj
  exact le_antisymm (CGraph.chromNum_le_iff_colorable.mpr hc2) hge

/-- Every vertex of a spider walks down its own leg to the centre. -/
theorem isConnected_spider (legs : List ℕ) : IsConnected (spider legs) := by
  -- Key lemma: reachability from 0 in spiderEdges off legs for off > 0
  have hreach_off : ∀ (ks : List ℕ) (off : ℕ) (hoff : 0 < off),
      ∀ (v : Fin (off + ks.sum)), (v.val = 0 ∨ off ≤ (v : ℕ)) →
        (CGraph.ofEdges (off + ks.sum) (CGraph.spiderEdges off ks)).toSimple.Reachable
          (⟨0, add_pos_of_pos_of_nonneg hoff (Nat.zero_le _)⟩ : Fin (off + ks.sum)) v := by
    intro ks
    induction ks using List.rec with
    | nil =>
      intro off hoff v hv
      simp at hv
      rcases hv with h | h
      · have heq : v = ⟨0, hoff⟩ := Fin.ext h
        rw [heq]
      · omega
    | cons k rest ih =>
      intro off hoff v hv
      rw [CGraph.spiderEdges]
      -- SpiderEdges off (k :: rest) has edges from legEdges 0 off k and spiderEdges (off+k) rest
      -- Case v.val = 0
      rcases hv with hv0 | hvge
      · have heq : v = ⟨0, add_pos_of_pos_of_nonneg hoff (Nat.zero_le _)⟩ := by
          exact Fin.ext hv0
        rw [heq]
      · -- off ≤ v.val
        -- If v.val < off + k, v is in the first leg. Reachable via leg edges.
        -- If v.val ≥ off + k, v is in the recursive spider (offset off+k). Use IH.
        by_cases hvlt : (v : ℕ) < off + k
        · -- v in first leg range: off ≤ v.val < off + k, so k > 0.
          have hsum' : (k :: rest).sum = k + rest.sum := List.sum_cons
          have hk0 : 0 < k := by omega
          -- Build path 0 → off → off+1 → ... → v using leg edges
          set t := (v : ℕ) - off with ht_def
          have ht_lt_k : t < k := by omega
          have hverb : off + k + rest.sum = off + (k :: rest).sum := by omega
          -- All vertices ⟨off + j, ...⟩ for j < k are in range
          have hsumk : k ≤ (k :: rest).sum := by simp [List.sum_cons]
          let offV : ∀ (j : ℕ), j < k → Fin (off + (k :: rest).sum) := fun j hj =>
            ⟨off + j, by omega⟩
          -- Edge (0, off) is in legEdges
          have hleg0 : (0, off) ∈ CGraph.legEdges 0 off k := by
            rw [CGraph.mem_legEdges]
            exact Or.inl ⟨rfl, rfl, hk0⟩
          -- Edge (off+j, off+j+1) ∈ legEdges for j+1 < k
          have hledge_succ : ∀ j, j + 1 < k →
              (off + j, off + (j + 1)) ∈ CGraph.legEdges 0 off k := by
            intro j hj
            rw [CGraph.mem_legEdges]
            exact Or.inr ⟨by omega, by omega, by omega⟩
          -- Hall: reachability from 0 to offV j hj
          have hall : ∀ (j : ℕ) (hj : j < k),
              (CGraph.ofEdges (off + (k :: rest).sum) (CGraph.legEdges 0 off k ++
                  CGraph.spiderEdges (off + k) rest)).toSimple.Reachable
                (⟨0, by omega⟩ : Fin (off + (k :: rest).sum)) (offV j hj) := by
            intro j hj
            induction j with
            | zero =>
              have hadj : (CGraph.ofEdges (off + (k :: rest).sum) (CGraph.legEdges 0 off k ++
                  CGraph.spiderEdges (off + k) rest)).Adj
                (⟨0, by omega⟩ : Fin (off + (k :: rest).sum)) (offV 0 hj) := by
                rw [CGraph.ofEdges_adj_val]
                show (0 : ℕ) ≠ off + 0 ∧ _
                exact ⟨by omega, Or.inl (List.mem_append_left _ hleg0)⟩
              obtain ⟨w⟩ := SimpleGraph.Reachable.refl _
              exact ⟨w.concat hadj⟩
            | succ i ih =>
              have hi_lt_k : i < k := by omega
              have ih' := ih hi_lt_k
              have hedge : ((off + i, off + (i + 1)) : (ℕ ×
                  ℕ)) ∈ CGraph.legEdges 0 off k := hledge_succ i (by omega)
              have hadj : (CGraph.ofEdges (off + (k :: rest).sum) (CGraph.legEdges 0 off k ++
                  CGraph.spiderEdges (off + k) rest)).Adj
                  (offV i hi_lt_k) (offV (i + 1) hj) := by
                rw [CGraph.ofEdges_adj_val]
                show (off + i : ℕ) ≠ off + (i + 1) ∧ _
                exact ⟨by omega, Or.inl (List.mem_append_left _ hedge)⟩
              obtain ⟨walk⟩ := ih'
              exact ⟨walk.concat hadj⟩
          -- v = offV t ht_lt_k
          have hv_eq : v = offV t ht_lt_k := by
            apply Fin.ext
            simp [offV, ht_def]
            omega
          rw [hv_eq]
          exact hall t ht_lt_k
        · -- v.val ≥ off + k, use IH with offset off+k
          have hverb : off + (k :: rest).sum = off + k + rest.sum := by
            simp [List.sum_cons]; omega
          have hfork : 0 < off + k := Nat.pos_of_ne_zero (by omega)
          have hvge2 : off + k ≤ (v : ℕ) := by omega
          -- Cast v to Fin (off + k + rest.sum)
          let v' : Fin (off + k + rest.sum) := ⟨(v : ℕ), by omega⟩
          have hv'_val : (v' : ℕ) = (v : ℕ) := rfl
          have hh := ih (off + k) hfork v' (Or.inr (by omega))
          -- Edge superset: spiderEdges (off+k) rest ⊆ legEdges 0 off k ++ spiderEdges (off+k) rest
          have edge_subset : ∀ e : ℕ × ℕ, e ∈ CGraph.spiderEdges (off + k) rest →
              e ∈ CGraph.legEdges 0 off k ++ CGraph.spiderEdges (off + k) rest :=
            fun e he => List.mem_append_right _ he
          -- Adjacency lifts
          have adj_lift : ∀ u w : Fin (off + k + rest.sum),
              (CGraph.ofEdges (off + k + rest.sum) (CGraph.spiderEdges (off + k) rest)).Adj u w →
              (CGraph.ofEdges (off + k + rest.sum) (CGraph.legEdges 0 off k ++ CGraph.spiderEdges
                  (off + k) rest)).Adj u w := by
            intro u w hadj
            rw [CGraph.ofEdges_adj_val] at hadj ⊢
            exact ⟨hadj.1, hadj.2.elim (fun h => Or.inl (edge_subset (u.val, w.val) h)) (fun h =>
                Or.inr (edge_subset (w.val, u.val) h))⟩
          have reach_lift : ∀ {u w : Fin (off + k + rest.sum)},
              (CGraph.ofEdges (off + k + rest.sum) (CGraph.spiderEdges (off + k)
                  rest)).toSimple.Reachable u w →
              (CGraph.ofEdges (off + k + rest.sum) (CGraph.legEdges 0 off k ++ CGraph.spiderEdges
                  (off + k) rest)).toSimple.Reachable u w := by
            intro u w hr
            have : (CGraph.ofEdges (off + k + rest.sum) (CGraph.spiderEdges (off + k)
                rest)).toSimple ≤
                   (CGraph.ofEdges (off + k + rest.sum) (CGraph.legEdges 0 off k ++
                       CGraph.spiderEdges (off + k) rest)).toSimple := by
              intro u v huv
              show (CGraph.ofEdges _ (CGraph.legEdges 0 off k ++ CGraph.spiderEdges (off + k)
                  rest)).toSimple.Adj u v
              rw [CGraph.toSimple_adj, CGraph.ofEdges_adj_val] at huv ⊢
              exact ⟨huv.1, huv.2.elim (fun he => Or.inl (edge_subset (u.val, v.val) he)) (fun he
                  => Or.inr (edge_subset (v.val, u.val) he))⟩
            exact hr.mono this
          have key := reach_lift hh
          let cast : Fin (off + k + rest.sum) → Fin (off + (k :: rest).sum) := Fin.cast hverb.symm
          have hcast_val : ∀ (x : Fin (off + k + rest.sum)), (cast x : ℕ) = (x : ℕ) := by
            intro x; simp [cast]
          have adj_cast : ∀ u w : Fin (off + k + rest.sum),
              (CGraph.ofEdges (off + k + rest.sum) (CGraph.legEdges 0 off k ++ CGraph.spiderEdges
                  (off + k) rest)).Adj u w →
              (CGraph.ofEdges (off + (k :: rest).sum) (CGraph.legEdges 0 off k ++
                  CGraph.spiderEdges (off + k) rest)).Adj (cast u) (cast w) := by
            intro u w hadj
            rw [CGraph.ofEdges_adj_val] at hadj ⊢
            exact ⟨hadj.1, hadj.2⟩
          have hreach_cast : ∀ {u w : Fin (off + k + rest.sum)},
              (CGraph.ofEdges (off + k + rest.sum) (CGraph.legEdges 0 off k ++ CGraph.spiderEdges
                  (off + k) rest)).toSimple.Reachable u w →
              (CGraph.ofEdges (off + (k :: rest).sum) (CGraph.legEdges 0 off k ++
                  CGraph.spiderEdges (off + k) rest)).toSimple.Reachable (cast u) (cast w) := by
            intro u w hr
            obtain ⟨walk⟩ := hr
            induction walk with
            | nil => exact SimpleGraph.Reachable.refl _
            | cons x' y' ih' =>
              rename_i u_ v_ w_
              have hxt_cgraph := adj_cast u_ v_ (by rwa [CGraph.toSimple_adj] at x')
              have hxt : (CGraph.ofEdges (off + (k :: rest).sum) (CGraph.legEdges 0 off k ++
                  CGraph.spiderEdges (off + k) rest)).toSimple.Adj (cast u_) (cast v_) := by
                rwa [CGraph.toSimple_adj]
              exact hxt.reachable.trans ih'
          have hcast0 : cast ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
            apply Fin.ext; simp [cast]
          have hcastv : cast v' = v := by
            apply Fin.ext; simp [cast, hv'_val]
          have step1 := hreach_cast key
          rw [hcastv] at step1
          exact step1
  unfold IsoGraph.spider
  rw [IsoGraph.isConnected_mk]
  show CGraph.IsConnected _
  simp only [CGraph.IsConnected]
  have hreach : ∀ (v : Fin (1 + legs.sum)),
      (CGraph.ofEdges (1 + legs.sum) (CGraph.spiderEdges 1 legs)).toSimple.Reachable
        (⟨0, add_pos_of_pos_of_nonneg Nat.one_pos (Nat.zero_le _)⟩ : Fin (1 + legs.sum)) v := by
    intro v
    exact hreach_off legs 1 Nat.one_pos v (by omega)
  haveI : Nonempty (CGraph.spider legs).V := by
    rw [CGraph.spider]
    show Nonempty (Fin (1 + legs.sum))
    exact ⟨0, by omega⟩
  apply SimpleGraph.Connected.mk
  · exact fun u v => (hreach u).symm.trans (hreach v)

theorem numComponents_spider (legs : List ℕ) : (spider legs).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_spider legs)

/-- A spider is a tree: connected, with `legs.sum` edges on `1 + legs.sum` vertices. -/
theorem isTree_spider (legs : List ℕ) : IsTree (spider legs) := by
  rw [IsoGraph.isTree_iff]
  refine ⟨isConnected_spider legs, ?_⟩
  rw [V_spider]
  suffices hE : (spider legs).E = legs.sum by omega
  show (CGraph.spider legs).E = legs.sum
  rw [CGraph.spider]
  have ofEdges_E_of_lt : ∀ (n : ℕ) (es : List (ℕ × ℕ)),
      (∀ p ∈ es, p.1 < p.2) →
      (∀ p ∈ es, p.2 < n) →
      List.Nodup es →
      (CGraph.ofEdges n es).E = es.length := by
    intro n es hlt hbound hnup
    induction es with
    | nil =>
      rw [CGraph.ofEdges_nil, CGraph.E_empty]; rfl
    | cons p es' ih =>
      have heq : CGraph.ofEdges n (p :: es') = CGraph.ofEdges n (es' ++ [p]) := by
        apply CGraph.ofEdges_congr n _ _ _
        intro x y hne
        simp [List.mem_cons, List.mem_append]
        tauto
      rw [heq]
      have hlt' : ∀ q ∈ es', q.1 < q.2 := fun q hq => hlt q (List.mem_cons_of_mem _ hq)
      have hfun : ∀ q ∈ p :: es', q.1 < n := fun q hq => lt_trans (hlt q hq) (hbound q hq)
      have hbound' : ∀ q ∈ es', q.2 < n := fun q hq => hbound q (List.mem_cons_of_mem _ hq)
      have hnup' : es'.Nodup := hnup.tail
      have ihm := ih hlt' hbound' hnup'
      have hp_mem : p ∈ p :: es' := List.mem_cons_self
      set ep : Sym2 (Fin n) := Sym2.mk (⟨p.1, hfun p hp_mem⟩, ⟨p.2, hbound p hp_mem⟩)
      have hnotin : ep ∉ (CGraph.ofEdges n es').toSimple.edgeFinset := by
        intro hmem
        simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple, CGraph.ofEdges, CGraph.ofRel] at hmem
        obtain ⟨hne, hm⟩ := hmem
        have hp12 : p.1 < p.2 := hlt p hp_mem
        have hpn : p ∉ es' := (List.nodup_cons.mp hnup).1
        rcases hm with h | h
        · exact hpn h
        · have := hlt' (p.2, p.1) h
          omega
      have hedgeFinset : (CGraph.ofEdges n (es' ++ [p])).toSimple.edgeFinset =
          (CGraph.ofEdges n es').toSimple.edgeFinset ∪ {ep} := by
        ext e
        simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple, CGraph.ofEdges, CGraph.ofRel,
          List.mem_append]
        induction e using Sym2.ind with
        | _ a b =>
          simp only [SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet]
          dsimp only [ep]
          rw [Sym2.eq_iff]
          simp only [Fin.ext_iff]
          have : ∀ (x : Fin n) (v : ℕ) (hv : v < n), (x = ⟨v, hv⟩ ↔ x.1 = v) := by
            intro x v hv; simp [Fin.ext_iff]
          rw [this a p.1 (hfun p hp_mem), this b p.2 (hbound p hp_mem),
              this a p.2 (hbound p hp_mem), this b p.1 (hfun p hp_mem)]
          set a' : ℕ := a.val
          set b' : ℕ := b.val
          rcases p with ⟨p1, p2⟩
          simp [Prod.mk.injEq]
          have hpnotin_es' : (p1, p2) ∉ es' := by
            intro h; exact (List.nodup_cons.mp hnup).1 h
          have hp12 : p1 < p2 := by simpa using hlt (p1, p2) hp_mem
          have hp21notin_es' : (p2, p1) ∉ es' := by
            intro h; have := hlt' (p2, p1) h; omega
          have hp12ne : p1 ≠ p2 := hp12.ne
          set A := (a', b') ∈ es'
          set B := a' = p1 ∧ b' = p2
          set C := (b', a') ∈ es'
          set D := b' = p1 ∧ a' = p2
          simp only [A, B, C, D] at *
          have hDflip : a' = p2 ∧ b' = p1 ↔ D := by constructor <;> intro h <;> exact ⟨h.2, h.1⟩
          rw [hDflip]
          rw [show b' = p1 ∧ a' = p2 ↔ D from Iff.rfl]
          have hNe_from_B : B → ¬a' = b' := by intro ⟨ha, hb⟩; omega
          have hNe_from_D : D → ¬a' = b' := by intro ⟨hb, ha⟩; omega
          set Ne := ¬a' = b'
          show Ne ∧ ((A ∨ B) ∨ C ∨ D) ↔ (B ∨ D) ∨ Ne ∧ (A ∨ C)
          constructor
          · intro h
            rcases h with ⟨Ne, hmem⟩
            rcases hmem with hAB | hCD
            · rcases hAB with hA | hB
              · exact Or.inr ⟨Ne, Or.inl hA⟩
              · exact Or.inl (Or.inl hB)
            · rcases hCD with hC | hD_val
              · exact Or.inr ⟨Ne, Or.inr hC⟩
              · exact Or.inl (Or.inr hD_val)
          · intro h
            rcases h with hBD | ⟨Ne, hAC⟩
            · rcases hBD with hB | hD_val
              · exact ⟨hNe_from_B hB, Or.inl (Or.inr hB)⟩
              · exact ⟨hNe_from_D hD_val, Or.inr (Or.inr hD_val)⟩
            · rcases hAC with hA | hC
              · exact ⟨Ne, Or.inl (Or.inl hA)⟩
              · exact ⟨Ne, Or.inr (Or.inl hC)⟩
      unfold CGraph.E at ihm ⊢
      rw [hedgeFinset, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnotin)]
      rw [Finset.card_singleton]
      rw [ihm]
      rfl
  have spider_spiderEdges_facts : ∀ (offs : ℕ) (hoffs : 1 ≤ offs) (ks : List ℕ),
      List.Nodup (CGraph.spiderEdges offs ks) ∧
      (∀ p ∈ CGraph.spiderEdges offs ks, p.1 < p.2) ∧
      (∀ p ∈ CGraph.spiderEdges offs ks, p.2 < offs + ks.sum) ∧
      List.length (CGraph.spiderEdges offs ks) = ks.sum := by
    intro offs _ks_h ks
    induction ks generalizing offs with
    | nil =>
      simp [CGraph.spiderEdges, List.sum_nil, List.length_nil]
    | cons k rest ih =>
      -- IH at offset offs+k for rest
      have hoffs_k : 1 ≤ offs + k := by omega
      obtain ⟨hnup', hlt', hbound', hlen'⟩ := ih (offs + k) hoffs_k
      -- spiderEdges offs (k :: rest) = legEdges 0 offs k ++ spiderEdges (offs + k) rest
      simp [CGraph.spiderEdges, List.sum_cons]
      -- legEdges 0 offs k properties
      have hleg_nodup : (CGraph.legEdges 0 offs k).Nodup := by
        induction k with
        | zero => simp [CGraph.legEdges_zero]
        | succ j ih' =>
          simp [CGraph.legEdges_succ]
          have : (List.range j).Nodup := List.nodup_range
          exact List.Nodup.map (fun x y h => by injection h with h1 h2; omega) this
      have hleg_lt : ∀ p ∈ CGraph.legEdges 0 offs k, p.1 < p.2 := by
        intro p hp
        rw [CGraph.mem_legEdges] at hp
        rcases hp with ⟨h1, h2, hk⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2]
        omega
      have hleg_bound : ∀ p ∈ CGraph.legEdges 0 offs k, p.2 < offs + k := by
        intro p hp
        rw [CGraph.mem_legEdges] at hp
        rcases hp with ⟨h1, h2, hk⟩ | ⟨h1, h2, h3⟩ <;> simp [h2] <;> omega
      have hleg_len : List.length (CGraph.legEdges 0 offs k) = k := by
        induction k with
        | zero => simp [CGraph.legEdges_zero]
        | succ j ih' => simp [CGraph.legEdges_succ, List.length_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Nodup
        apply List.Nodup.append hleg_nodup hnup'
        intro x hx_leg hx_spider
        have hq_lt := hleg_bound x hx_leg
        have ⟨_, hq_ge, _⟩ := CGraph.mem_spiderEdges_bound (offs + k) rest x.1 x.2 hx_spider
        omega
      · -- p.1 < p.2
        intro a b hp
        rcases hp with hp | hp
        · rcases hp with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩ <;> omega
        · exact hlt' _ hp
      · -- p.2 < offs + (k + rest.sum)
        intro a b hp
        rcases hp with hp | hp
        · rcases hp with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩ <;> omega
        · have := hbound' _ hp; omega
      · -- length
        rw [hleg_len, hlen']
  -- Now close the main goal
  have ⟨hnup, hlt, hbound, hlen⟩ := spider_spiderEdges_facts 1 (by omega) legs
  rw [ofEdges_E_of_lt _ _ hlt hbound hnup, hlen]

theorem girth_spider (legs : List ℕ) : (spider legs).girth = 0 := by
  rw [girth_eq_zero_iff]
  exact (isTree_spider legs).2

/-- The centre and the first vertex of any nonempty leg. -/
theorem cliqueNum_spider (legs : List ℕ) (h : 0 < legs.sum) : (spider legs).cliqueNum = 2 :=
  cliqueNum_of_isTree (h := isTree_spider legs) (by simp [V_spider]; omega)

theorem chromNum_spider (legs : List ℕ) (h : 0 < legs.sum) : (spider legs).chromNum = 2 := by
  simp only [IsoGraph.spider, IsoGraph.chromNum_mk, CGraph.chromNum]
  let SE := CGraph.spiderEdges
  -- Helper: for k > 0, (0,1) ∈ legEdges 0 1 k
  have hlist_start : ∀ k, 0 < k → ∃ L, (List.range k).map (· + 1) = 1 :: L := by
    intro k hk
    have : ∀ n, 0 < n → ∃ L, (List.range n).map (· + 1) = 1 :: L := by
      intro n hn
      induction n with
      | zero => contradiction
      | succ m ih =>
        cases m with
        | zero => exact ⟨[], by rfl⟩
        | succ p =>
          obtain ⟨L, hL⟩ := ih (by omega)
          exact ⟨L ++ [p + 1 + 1],
              by rw [List.range_succ, List.map_append, List.map_cons, hL]; simp⟩
    exact this k hk
  have hleg : ∀ k, 0 < k → (0, 1) ∈ CGraph.legEdges 0 1 k := by
    intro k hk
    show (0, 1) ∈ CGraph.pathEdges (0 :: (List.range k).map (· + 1))
    obtain ⟨L, hL⟩ := hlist_start k hk
    rw [hL, CGraph.pathEdges]
    exact List.mem_cons_self
  have hedge_first : ∀ (k : ℕ) (rest : List ℕ), 0 < k →
      (0, 1) ∈ CGraph.spiderEdges 1 (k :: rest) := by
    intro k rest hk
    rw [CGraph.spiderEdges]
    exact List.mem_append_left _ (hleg k hk)
  have hSE_zero_head : ∀ (rest : List ℕ), CGraph.spiderEdges 1 (0 ::
      rest) = CGraph.spiderEdges 1 rest := by
    intro rest
    simp [CGraph.spiderEdges, CGraph.legEdges]
  have hedge_all : (0, 1) ∈ CGraph.spiderEdges 1 legs := by
    have key : ∀ (ls : List ℕ), 0 < ls.sum → (0, 1) ∈ CGraph.spiderEdges 1 ls := by
      intro ls hls
      induction ls with
      | nil => simp at hls
      | cons k rest ih =>
        simp only [List.sum_cons] at hls
        by_cases hk : 0 < k
        · exact hedge_first k rest hk
        · push_neg at hk
          have hk0 : k = 0 := by omega
          rw [hk0] at hls
          simp at hls
          rw [hk0, hSE_zero_head]
          exact ih hls
    exact key legs h
  have htree : (CGraph.spider legs).toSimple.IsTree := isTree_spider legs
  have hchrom_le : (CGraph.spider legs).toSimple.chromaticNumber ≤ 2 :=
    htree.isBipartite.chromaticNumber_le
  have hchrom_ge : 2 ≤ (CGraph.spider legs).toSimple.chromaticNumber := by
    have hadj : (CGraph.spider legs).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      rw [CGraph.spider_adj_val]
      refine ⟨?_, Or.inl hedge_all⟩
      show ((⟨0, by omega⟩ : (CGraph.spider legs).V) : ℕ) ≠ ((⟨1, by omega⟩ : (CGraph.spider
          legs).V) : ℕ)
      simp
    exact SimpleGraph.two_le_chromaticNumber_of_adj hadj
  have hchrom_eq : (CGraph.spider
      legs).toSimple.chromaticNumber = 2 := le_antisymm hchrom_le hchrom_ge
  simp [hchrom_eq]

/-- Pendant, centre, centre, pendant. -/
theorem diameter_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).diameter = 3 := by
  simp only [IsoGraph.diameter]
  unfold doubleStar
  rw [Quotient.lift_mk]
  unfold CGraph.diameter
  set SG : SimpleGraph (CGraph.doubleStar (m + 1) (n + 1)).V :=
    (CGraph.doubleStar (m + 1) (n + 1)).toSimple
  let c0 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨0, by omega⟩
  let c1 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨1, by omega⟩
  have h_c0_val : c0.val = 0 := rfl
  have h_c1_val : c1.val = 1 := rfl
  have h_adj_val : ∀ x y : (CGraph.doubleStar (m + 1) (n + 1)).V,
      SG.Adj x y ↔
        (x.val ≠ y.val ∧
          ((x.val = 0 ∧ y.val = 1 ∨ x.val = 0 ∧ 2 ≤ y.val ∧ y.val < 2 + (m + 1) ∨
            x.val = 1 ∧ 2 + (m + 1) ≤ y.val ∧ y.val < 2 + (m + 1) + (n + 1)) ∨
           (y.val = 0 ∧ x.val = 1 ∨ y.val = 0 ∧ 2 ≤ x.val ∧ x.val < 2 + (m + 1) ∨
            y.val = 1 ∧ 2 + (m + 1) ≤ x.val ∧ x.val < 2 + (m + 1) + (n + 1)))) := by
    intro x y
    simp only [SG, CGraph.toSimple_adj]
    exact CGraph.doubleStar_adj_val (m+1) (n+1) x y
  have h_center_adj : SG.Adj c0 c1 := by
    rw [h_adj_val]
    rw [h_c0_val, h_c1_val]
    simp
  have h_adj_symm : ∀ x y : (CGraph.doubleStar (m + 1) (n + 1)).V, SG.Adj x y → SG.Adj y x :=
    fun x y h => SimpleGraph.Adj.symm h
  have hne_c0_c1 : c0 ≠ c1 := by
    intro h; have := congr_arg Fin.val h; simp at this
  -- Edge w-c0 when w.val < 2+(m+1) and w ≠ c0
  have h_adj_w_c0 : ∀ w, w ≠ c0 → w.val < 2 + (m + 1) → SG.Adj w c0 := by
    intro w hne hw
    rw [h_adj_val, h_c0_val]
    apply And.intro
    · exact fun h => hne (Fin.ext h)
    · right
      by_cases h1 : w.val = 1
      · exact Or.inl ⟨rfl, h1⟩
      · have hne0 : w.val ≠ 0 := fun h => hne (Fin.ext h)
        exact Or.inr (Or.inl ⟨rfl, Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne0))
            (Ne.symm h1), hw⟩)
  -- Edge c0-w when w.val < 2+(m+1) and w ≠ c0
  have h_adj_c0_w : ∀ w, w ≠ c0 → w.val < 2 + (m + 1) → SG.Adj c0 w :=
    fun w hne hw => h_adj_symm _ _ (h_adj_w_c0 w hne hw)
  -- Edge w-c1 when 2+(m+1) ≤ w.val
  have h_adj_w_c1 : ∀ w, 2 + (m + 1) ≤ w.val → SG.Adj w c1 := by
    intro w hw
    rw [h_adj_val, h_c1_val]
    exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨h_c1_val, hw, by exact w.2⟩))⟩
  -- Edge c1-w when 2+(m+1) ≤ w.val
  have h_adj_c1_w : ∀ w, 2 + (m + 1) ≤ w.val → SG.Adj c1 w :=
    fun w hw => h_adj_symm _ _ (h_adj_w_c1 w hw)
  -- Walk from w to c0, length ≤ 1
  let walkToCenter0 : ∀ w, w.val < 2 + (m + 1) → SG.Walk w c0 := by
    intro w hw
    by_cases h0 : w = c0
    · subst h0; exact SimpleGraph.Walk.nil
    · exact (SimpleGraph.Walk.cons (h_adj_w_c0 w h0 hw) SimpleGraph.Walk.nil)
  have walkToCenter0_len : ∀ w hw, (walkToCenter0 w hw).length ≤ 1 := by
    intro w hw
    by_cases h0 : w = c0
    · subst h0; simp [walkToCenter0]
    · simp [walkToCenter0, h0]
  -- Walk from c0 to w, length ≤ 1
  let walkFromCenter0 : ∀ w, w.val < 2 + (m + 1) → SG.Walk c0 w := by
    intro w hw
    by_cases h0 : w = c0
    · subst h0; exact SimpleGraph.Walk.nil
    · exact (SimpleGraph.Walk.cons (h_adj_c0_w w h0 hw) SimpleGraph.Walk.nil)
  have walkFromCenter0_len : ∀ w hw, (walkFromCenter0 w hw).length ≤ 1 := by
    intro w hw
    by_cases h0 : w = c0
    · subst h0; simp [walkFromCenter0]
    · simp [walkFromCenter0, h0]
  -- Walk from w to c1, length ≤ 1
  let walkToCenter1 : ∀ w, 2 + (m + 1) ≤ w.val → SG.Walk w c1 := by
    intro w hw
    exact (SimpleGraph.Walk.cons (h_adj_w_c1 w hw) SimpleGraph.Walk.nil)
  have walkToCenter1_len : ∀ w hw, (walkToCenter1 w hw).length = 1 := by
    intro w hw; rfl
  -- Walk from c1 to w, length ≤ 1
  let walkFromCenter1 : ∀ w, 2 + (m + 1) ≤ w.val → SG.Walk c1 w := by
    intro w hw
    exact (SimpleGraph.Walk.cons (h_adj_c1_w w hw) SimpleGraph.Walk.nil)
  have walkFromCenter1_len : ∀ w hw, (walkFromCenter1 w hw).length = 1 := by
    intro w hw; rfl
  -- Walk c0 → c1, length 1
  let walk0to1 : SG.Walk c0 c1 := SimpleGraph.Walk.cons h_center_adj SimpleGraph.Walk.nil
  have walk0to1_len : walk0to1.length = 1 := by rfl
  -- Walk c1 → c0, length 1
  let walk1to0 : SG.Walk c1 c0 := SimpleGraph.Walk.cons (h_adj_symm _ _
      h_center_adj) SimpleGraph.Walk.nil
  have walk1to0_len : walk1to0.length = 1 := by rfl
  -- Upper bound
  have h_walk_to_c0_len : ∀ w hw, (walkToCenter0 w hw).length ≤ 1 := walkToCenter0_len
  have h_walk_from_c0_len : ∀ w hw, (walkFromCenter0 w hw).length ≤ 1 := walkFromCenter0_len
  have h_walk_to_c1_len : ∀ w hw, (walkToCenter1 w hw).length = 1 := walkToCenter1_len
  have h_walk_from_c1_len : ∀ w hw, (walkFromCenter1 w hw).length = 1 := walkFromCenter1_len
  have h_walk_0to1_len : walk0to1.length = 1 := walk0to1_len
  have h_walk_1to0_len : walk1to0.length = 1 := walk1to0_len
  -- Build concrete walks and bound their lengths
  
  let walkuC0 : ∀ w hw, SG.Walk w c0 := fun w hw => walkToCenter0 w hw
  have walkuC0_len : ∀ w hw, (walkuC0 w hw).length ≤ 1 := fun w hw => walkToCenter0_len w hw
  let walkuC1 : ∀ w hw, SG.Walk w c1 := fun w hw => walkToCenter1 w hw
  have walkuC1_len : ∀ w hw, (walkuC1 w hw).length = 1 := fun w hw => walkToCenter1_len w hw
  have h_edist_le_three : ∀ u v : (CGraph.doubleStar (m + 1) (n + 1)).V, SG.edist u v ≤ 3 := by
    intro u v
    by_cases hu0 : u.val < 2 + (m + 1)
    · by_cases hv0 : v.val < 2 + (m + 1)
      · exact ((walkToCenter0 u hu0).append (walkFromCenter0 v hv0)) |>.edist_le.trans
          (by rw [SimpleGraph.Walk.length_append]; exact_mod_cast
            (by have := walkToCenter0_len u hu0; have := walkFromCenter0_len v hv0; omega))
      · let hvhw : 2 + (m + 1) ≤ v.val := Nat.le_of_not_lt hv0
        let hwalk2 : SG.Walk c0 v := walk0to1.append (walkFromCenter1 v hvhw)
        have hlen2 : hwalk2.length = 2 := by
          dsimp only [hwalk2, walk0to1, walkFromCenter1]
          rw [SimpleGraph.Walk.length_append, walk0to1_len, walkFromCenter1_len v hvhw]
        exact ((walkToCenter0 u hu0).append hwalk2) |>.edist_le.trans
          (by rw [SimpleGraph.Walk.length_append, hlen2]; exact_mod_cast
            (by have := walkToCenter0_len u hu0; omega))
    · by_cases hv0 : v.val < 2 + (m + 1)
      · let hwalk2 : SG.Walk c1 v := walk1to0.append (walkFromCenter0 v hv0)
        have hlen2 : hwalk2.length ≤ 2 := by
          dsimp only [hwalk2, walk1to0, walkFromCenter0]
          rw [SimpleGraph.Walk.length_append, walk1to0_len]
          exact Nat.add_le_add_left (walkFromCenter0_len v hv0) 1
        exact ((walkToCenter1 u (Nat.le_of_not_lt hu0)).append hwalk2) |>.edist_le.trans
          (by rw [SimpleGraph.Walk.length_append]; exact_mod_cast
            (by have := walkToCenter1_len u (Nat.le_of_not_lt hu0); omega))
      · exact ((walkToCenter1 u (Nat.le_of_not_lt hu0)).append (walkFromCenter1 v (Nat.le_of_not_lt
          hv0))) |>.edist_le.trans
          (by rw [SimpleGraph.Walk.length_append]; exact_mod_cast
            (by
              have := walkToCenter1_len u (Nat.le_of_not_lt hu0)
              have := walkFromCenter1_len v (Nat.le_of_not_lt hv0)
              omega))
  -- Lower bound
  set u : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨2, by omega⟩
  set v : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨m + 3, by omega⟩
  have h_ne : u ≠ v := by
    intro h; have := congr_arg Fin.val h; simp [u, v] at this
  have h_not_adj : ¬SG.Adj u v := by
    rw [h_adj_val]
    simp [u, v]
  have hu_val : u.val = 2 := rfl
  have hc0_val' : c0.val = 0 := rfl
  -- Neighbors of u: only c0
  have h_u_neighbors : ∀ p, SG.Adj u p → p = c0 := by
    intro p hp
    rw [h_adj_val] at hp
    simp [hu_val] at hp
    obtain ⟨hne, hdisj⟩ := hp
    exact Fin.ext (by simp [hc0_val'] at hdisj ⊢; omega)
  have hv_val : v.val = m + 3 := rfl
  -- Neighbors of v: only c1
  have h_v_neighbors : ∀ p, SG.Adj p v → p = c1 := by
    intro p hp
    rw [h_adj_val] at hp
    rw [hv_val] at hp
    obtain ⟨hne, hdisj⟩ := hp
    have hp1 : p.val = 1 := by
      rcases hdisj with h | h | h | h | h | h <;> try omega
    exact Fin.ext hp1
  -- No walk of length 2 from u to v
  have h_no_walk2 : ∀ w : SG.Walk u v, w.length = 2 → False := by
    intro w hw
    have hadj1 : SG.Adj u (w.getVert (1 : ℕ)) := by
      have h1 := w.adj_getVert_succ (i := 0) (by omega : (0 : ℕ) < w.length)
      rw [w.getVert_zero] at h1; exact h1
    have hadj2 : SG.Adj (w.getVert (1 : ℕ)) v := by
      have hvert2 : w.getVert w.length = v := w.getVert_length
      rw [hw] at hvert2
      have h1 := w.adj_getVert_succ (i := 1) (by omega : (1 : ℕ) < w.length)
      rw [hvert2] at h1; exact h1
    have hp0 := h_u_neighbors _ hadj1
    have hp1 := h_v_neighbors _ hadj2
    exact hne_c0_c1 (hp0.symm.trans hp1)
  -- No walk of length < 3 from u to v
  have h_no_walk_lt_3 : ∀ w : SG.Walk u v, ¬(w.length < 3) := by
    intro w hlt
    have h012 : w.length = 0 ∨ w.length = 1 ∨ w.length = 2 := by omega
    rcases h012 with h | h | h
    · exfalso
      have huv : u = v := by
        have h1 := w.getVert_zero
        have h2 := w.getVert_length
        rw [h] at h2; exact h1.symm.trans h2
      exact h_ne huv
    · exfalso; exact h_not_adj (SimpleGraph.Walk.adj_of_length_eq_one h)
    · exact h_no_walk2 w h
  have h_walks_ge_3 : ∀ w : SG.Walk u v, 3 ≤ w.length := fun w => not_lt.mp (h_no_walk_lt_3 w)
  -- Reachability: u → c0 → c1 → v
  have h_reach : SG.Reachable u v := by
    exact ((walkToCenter0 u (by simp [u])).append
      (walk0to1.append (walkFromCenter1 v (by simp [v]; omega)))).reachable
  have h_edist_ge_three : 3 ≤ SG.edist u v := by
    rw [SimpleGraph.edist]
    apply le_csInf
    · exact ⟨_, ⟨h_reach.some, rfl⟩⟩
    · rintro _ ⟨w, rfl⟩
      show (3 : ℕ∞) ≤ ↑w.length
      exact_mod_cast h_walks_ge_3 w
  have h_3_le_ediam : 3 ≤ SG.ediam := h_edist_ge_three.trans SimpleGraph.edist_le_ediam
  have h_ediam_le_three : SG.ediam ≤ 3 := by
    apply SimpleGraph.ediam_le_of_edist_le
    intro x y
    exact_mod_cast h_edist_le_three x y
  have h_ediam_eq_three : SG.ediam = 3 := le_antisymm h_ediam_le_three h_3_le_ediam
  change SG.diam = 3
  rw [SimpleGraph.diam, h_ediam_eq_three]
  rfl

/-- Either centre reaches everything in two steps. -/
theorem radius_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).radius = 2 := by
  rw [IsoGraph.doubleStar_def, radius_mk]
  -- Lower bound: 2 ≤ radius, from diameter = 3 and diameter ≤ 2 * radius
  have hdia : (CGraph.doubleStar (m + 1) (n + 1)).diameter = 3 := by
    have := diameter_doubleStar m n
    simp [IsoGraph.doubleStar_def, diameter_mk] at this
    exact this
  have hlow : 2 ≤ (CGraph.doubleStar (m + 1) (n + 1)).radius := by
    have := CGraph.diameter_le_two_mul_radius (CGraph.doubleStar (m + 1) (n + 1))
    simp [hdia] at this
    omega
  -- Upper bound: radius ≤ 2, from eccent(0) ≤ 2
  set v0 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨0, by omega⟩
  have hecc0 : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.eccent v0 ≤ 2 := by
    rw [SimpleGraph.eccent_le_iff]
    intro u
    have hlk : u.val < 2 + (m + 1) + (n + 1) := u.isLt
    -- It suffices to show v0 = u or adj v0 u or ∃ w, adj v0 w ∧ adj w u
    suffices h : v0 = u ∨ (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj v0 u ∨
      ∃ w, (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj v0 w ∧
        (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj w u by
      rcases h with rfl | hadj | ⟨w, h1, h2⟩
      · simp
      · rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj]; norm_num
      · exact le_trans (SimpleGraph.edist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
          SimpleGraph.Walk.nil))) (by simp)
    by_cases h0 : u.val = 0
    · left; exact Fin.ext (by simp [v0]; omega)
    · by_cases h1 : u.val = 1
      · right; left
        simp [v0, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
        omega
      · by_cases h2 : u.val < 2 + (m + 1)
        · right; left
          simp [v0, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
          omega
        · right; right
          refine ⟨⟨1, by omega⟩, ?_, ?_⟩
          · simp [v0, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
          · simp [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
            omega
  have hup : (CGraph.doubleStar (m + 1) (n + 1)).radius ≤ 2 := by
    rw [CGraph.radius]
    apply ENat.toNat_le_of_le_coe
    exact le_trans (SimpleGraph.radius_le_eccent (u := v0)) hecc0
  exact le_antisymm hup hlow

/-- A clique on three or more vertices already has more edges than a tree may. -/
theorem not_isAcyclic_lollipop (m k : ℕ) : ¬ IsAcyclic (lollipop (m + 3) k) := by
  intro hac
  have htree : IsTree (lollipop (m + 3) k) :=
    (isTree_iff_isConnected_and_isAcyclic _).mpr ⟨isConnected_lollipop (m + 2) k, hac⟩
  have h := ((isTree_iff _).mp htree).2
  have hE : (lollipop (m + 3) k).E = (m + 3).choose 2 + k := E_lollipop (m + 2) k
  have hch : m + 3 ≤ (m + 3).choose 2 := by
    have hc : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
      rw [Nat.choose_two_right]; simp
    rw [hc, Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  rw [hE, V_lollipop] at h
  omega

/-- Hanging pendants off a cycle leaves the edge and vertex counts equal. -/
theorem not_isAcyclic_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    ¬ IsAcyclic (cyclePendant (m + 3) ks) := by
  intro hac
  have htree : IsTree (cyclePendant (m + 3) ks) :=
    (isTree_iff_isConnected_and_isAcyclic _).mpr ⟨isConnected_cyclePendant m ks h, hac⟩
  have h2 := (isTree_iff _).mp htree
  rw [E_cyclePendant m ks h, V_cyclePendant] at h2
  omega

/-- Every path the same parity means two colours, once each path is genuinely subdivided. -/
theorem chromNum_thetaGraph_of_parity {xs : List ℕ} (b : ℕ) (hne : xs ≠ [])
    (h0 : ∀ k ∈ xs, 0 < k) (h : ∀ k ∈ xs, (k + b) % 2 = 1) : (thetaGraph xs).chromNum = 2 := by
  refine chromNum_eq_two_iff.mpr ⟨isBipartite_thetaGraph_of_parity b h, ?_⟩
  have hlen : 0 < xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => simp
  rw [E_thetaGraph xs h0]
  omega

/-- All the paths odd is the `b = 0` case, and odd paths are automatically subdivided. -/
theorem chromNum_thetaGraph_odd {xs : List ℕ} (hne : xs ≠ []) (h : ∀ k ∈ xs, k % 2 = 1) :
    (thetaGraph xs).chromNum = 2 :=
  chromNum_thetaGraph_of_parity 0 hne (fun k hk ↦ by have := h k hk; omega) (by simpa using h)

/-- All the paths even is the `b = 1` case, and there positivity has to be asked for. -/
theorem chromNum_thetaGraph_even {xs : List ℕ} (hne : xs ≠ []) (h0 : ∀ k ∈ xs, 0 < k)
    (h : ∀ k ∈ xs, k % 2 = 0) : (thetaGraph xs).chromNum = 2 :=
  chromNum_thetaGraph_of_parity 1 hne h0 (fun k hk ↦ by have := h k hk; omega)

/-- A spider is a tree, so it has no cycle. -/
@[simp] theorem isAcyclic_spider (legs : List ℕ) : IsAcyclic (spider legs) :=
  ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_spider legs)).2

/-- A double star is a tree, so it has no cycle. -/
@[simp] theorem isAcyclic_doubleStar (m n : ℕ) : IsAcyclic (doubleStar m n) :=
  ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_doubleStar m n)).2

/-- Covering the triangular graph by cliques is colouring the Kneser graph on the same pairs. -/
theorem cliqueCoverNum_triangular (n : ℕ) :
    (triangular n).cliqueCoverNum = (kneser n 2).chromNum := by
  rw [cliqueCoverNum_eq, compl_triangular]

/-- Lovász' bound for `K(n, 2)` transported through the complement. -/
theorem cliqueCoverNum_triangular_le (n : ℕ) :
    (triangular (n + 4)).cliqueCoverNum ≤ n + 2 := by
  have h := chromNum_kneser_le (n + 4) 2 (by norm_num)
  rw [cliqueCoverNum_triangular]
  omega

/-- `L(K₅)` is covered by three cliques, since its complement is the Petersen graph. -/
theorem cliqueCoverNum_triangular_five : (triangular 5).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_eq, ← compl_petersen, compl_compl, chromNum_petersen]

/-- **Paley graphs are class two.**  They are regular of odd order, so `Δ` colours leave an edge
uncoloured. -/
theorem maxDeg_lt_edgeChromNum_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (h5 : 5 ≤ q) : maxDeg (paley q) < (paley q).edgeChromNum := by
  refine maxDeg_lt_edgeChromNum_of_isRegularWith_odd (isRegularWith_paley q hq) (by omega) ?_
  rw [V_paley]
  omega

/-- Spelling the previous bound out: `χ'(Paley q) ≥ (q + 1) / 2`. -/
theorem edgeChromNum_paley_ge (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (h5 : 5 ≤ q) :
    (q + 1) / 2 ≤ (paley q).edgeChromNum := by
  have h := maxDeg_lt_edgeChromNum_paley q hq h5
  rw [maxDeg_paley q hq] at h
  omega

/-- **Rook graphs of odd order are class two.**  `R(2m+3, 2n+3)` is regular on an odd number of
vertices. -/
theorem edgeChromNum_rook_odd_ge (m n : ℕ) :
    2 * m + 2 * n + 5 ≤ (rook (2 * m + 3) (2 * n + 3)).edgeChromNum := by
  have hodd : (rook (2 * m + 3) (2 * n + 3)).V % 2 = 1 := by
    rw [V_rook, Nat.mul_mod, show (2 * m + 3) % 2 = 1 by omega, show (2 * n + 3) % 2 = 1 by omega]
  have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd
    (isRegularWith_rook (2 * m + 3) (2 * n + 3)) (by omega) hodd
  have hd : maxDeg (rook (2 * m + 3) (2 * n + 3)) = 2 * m + 2 * n + 4 := by
    have hr := maxDeg_rook (2 * m + 2) (2 * n + 2)
    rw [show 2 * m + 2 + 1 = 2 * m + 3 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring] at hr
    omega
  rw [hd] at h
  omega

/-- **Balanced complete multipartite graphs of odd order are class two.** -/
theorem edgeChromNum_completeMultipartite_replicate_ge {m d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hodd : m * d % 2 = 1) :
    (m - 1) * d + 1 ≤ (completeMultipartite (List.replicate m d)).edgeChromNum := by
  have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd
    (isRegularWith_completeMultipartite_replicate m d)
    (Nat.mul_pos (by omega) hd)
    (by rw [V_completeMultipartite_replicate]; exact hodd)
  rw [maxDeg_completeMultipartite_replicate (by omega) hd] at h
  omega

/-- `α(Paley 13) ≤ 3` leaves at least ten vertices for the cover. -/
theorem ten_le_coverNum_paley_thirteen : 10 ≤ (paley 13).coverNum := by
  have h := coverNum_add_indepNum (paley 13)
  have h2 := indepNum_paley_thirteen_le
  rw [V_paley] at h
  omega

/-- `α(Paley 17) ≤ 4` leaves at least thirteen vertices for the cover. -/
theorem thirteen_le_coverNum_paley_seventeen : 13 ≤ (paley 17).coverNum := by
  have h := coverNum_add_indepNum (paley 17)
  have h2 := indepNum_paley_seventeen_le
  rw [V_paley] at h
  omega

/-- **Triangular graphs of odd order are class two.**  `L(Kₙ)` is `(2n - 4)`-regular on
`C(n, 2)` vertices, so an odd binomial coefficient forces an extra edge colour. -/
theorem maxDeg_lt_edgeChromNum_triangular {n : ℕ} (hn : 3 ≤ n) (hodd : n.choose 2 % 2 = 1) :
    maxDeg (triangular n) < (triangular n).edgeChromNum := by
  refine maxDeg_lt_edgeChromNum_of_isRegularWith_odd (isRegularWith_triangular n) (by omega) ?_
  rw [V_triangular]
  exact hodd

/-- The same bound with the maximum degree evaluated. -/
theorem edgeChromNum_triangular_ge (n : ℕ) (hodd : (n + 4).choose 2 % 2 = 1) :
    2 * n + 5 ≤ (triangular (n + 4)).edgeChromNum := by
  have h := maxDeg_lt_edgeChromNum_triangular (n := n + 4) (by omega) hodd
  have hd : maxDeg (triangular (n + 4)) = 2 * n + 4 := by
    have hr := maxDeg_triangular (n + 2)
    rw [show n + 2 + 2 = n + 4 by ring] at hr
    omega
  omega

/-- `T(6)` is `8`-regular on `15` vertices. -/
theorem edgeChromNum_triangular_six_ge : 9 ≤ (triangular 6).edgeChromNum := by
  have h := edgeChromNum_triangular_ge 2 (by decide)
  norm_num at h
  exact h

/-- `T(7)` is `10`-regular on `21` vertices. -/
theorem edgeChromNum_triangular_seven_ge : 11 ≤ (triangular 7).edgeChromNum := by
  have h := edgeChromNum_triangular_ge 3 (by decide)
  norm_num at h
  exact h

end IsoGraph
