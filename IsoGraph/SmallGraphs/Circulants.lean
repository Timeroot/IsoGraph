import IsoGraph.SmallGraphs.Families

/-!
# Circulants, Kneser and Johnson graphs

Circulants, Kneser and Johnson graphs: their invariants, and what vertex transitivity and the
diameter give for them.
-/

namespace IsoGraph

/-! ### Invariants of the circulant graphs

Every circulant graph is vertex transitive, and a great deal follows from that alone: it is
regular, its radius equals its diameter, and the clique–coclique bound `α · ω ≤ |V|` applies.
The complement of a circulant is again vertex transitive. -/

theorem exists_degSequence_replicate_circulant (n : ℕ) (S : List ℕ) :
    ∃ k, degSequence (circulant n S) = List.replicate n k := by
  have h := exists_degSequence_replicate_of_isVertexTransitive (isVertexTransitive_circulant n S)
  rwa [V_circulant] at h

theorem exists_isRegularWith_circulant (n : ℕ) (S : List ℕ) :
    ∃ k, (circulant n S).IsRegularWith k :=
  exists_isRegularWith_of_isVertexTransitive (isVertexTransitive_circulant n S)

/-- A circulant graph is regular, so its vertex and edge counts pin down its degree sequence. -/
theorem degSequence_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : degSequence (circulant n S) = List.replicate n k := by
  have h := degSequence_of_isVertexTransitive (k := k) (isVertexTransitive_circulant n S)
    (by rwa [V_circulant]) (by rwa [V_circulant])
  rwa [V_circulant] at h

@[simp] theorem maxDeg_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : maxDeg (circulant n S) = k :=
  maxDeg_eq_of_degSequence_replicate hn (degSequence_circulant hn hk)

@[simp] theorem minDeg_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : minDeg (circulant n S) = k :=
  minDeg_eq_of_degSequence_replicate hn (degSequence_circulant hn hk)

@[simp] theorem radius_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).radius = (circulant n S).diameter :=
  radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_circulant n S)

theorem indepNum_mul_cliqueNum_le_V_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).indepNum * (circulant n S).cliqueNum ≤ n := by
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_circulant n S)
  rwa [V_circulant] at h

theorem two_mul_indepNum_le_V_circulant {n : ℕ} {S : List ℕ} (hE : 0 < (circulant n S).E) :
    2 * (circulant n S).indepNum ≤ n := by
  have h := two_mul_indepNum_le_V (isVertexTransitive_circulant n S) hE
  rwa [V_circulant] at h

@[simp] theorem isVertexTransitive_compl_circulant (n : ℕ) (S : List ℕ) :
    IsVertexTransitive (circulant n S)ᶜ :=
  (isVertexTransitive_circulant n S).compl

theorem coverNum_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).coverNum = n - (circulant n S).indepNum := by
  have h := (circulant n S).coverNum_add_indepNum
  rw [V_circulant] at h
  omega

/-- **The matching number of a rook's graph**: `ν(Kₘ □ Kₙ) = ⌊mn/2⌋`.  The board already carries
a boustrophedon Hamiltonian path as a grid, and every grid edge is a rook edge, so
`le_indepNum_lineGraph_board` supplies the matching. -/
theorem matchNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).matchNum = (m + 1) * (n + 1) / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (rook (m + 1) (n + 1)).two_mul_matchNum_le_V
    rw [V_rook] at h
    omega
  · rw [matchNum_eq, rook, complete, complete, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    refine CGraph.le_indepNum_lineGraph_board _ (fun p ↦ p) (fun _ _ h ↦ h) ?_
    intro p q h
    rw [CGraph.cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, CGraph.complete_adj, ne_eq]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by simp only [Fin.ext_iff]; omega⟩
    · exact Or.inr ⟨by simp only [Fin.ext_iff]; omega, h1⟩

/-! ### Blocks of consecutive elements

The extremal pairs for the Johnson diameter are two blocks of `k` consecutive elements at a
prescribed offset; three lemmas about blocks are all the argument needs of them. -/

/-- The block `{a, a + 1, …, a + m - 1}` of `Fin n`. -/
private def finBlock (n a m : ℕ) (h : a + m ≤ n) : Finset (Fin n) :=
  Finset.image (fun i : Fin m ↦ (⟨a + i.val, by omega⟩ : Fin n)) Finset.univ

private theorem mem_finBlock {n a m : ℕ} (h : a + m ≤ n) (x : Fin n) :
    x ∈ finBlock n a m h ↔ a ≤ x.val ∧ x.val < a + m := by
  simp only [finBlock, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt a⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x.val - a, by omega⟩, Fin.ext (by show a + (x.val - a) = x.val; omega)⟩

private theorem card_finBlock {n a m : ℕ} (h : a + m ≤ n) : (finBlock n a m h).card = m := by
  rw [finBlock, Finset.card_image_of_injective _ fun i j hij ↦
    Fin.ext (by simpa [Fin.ext_iff] using hij), Finset.card_univ, Fintype.card_fin]

/-- Two blocks of length `k` at offset `d ≤ k` meet in exactly `k - d` points. -/
private theorem card_inter_finBlock {n k d : ℕ} (h0 : 0 + k ≤ n) (h : d + k ≤ n) (hdk : d ≤ k) :
    (finBlock n 0 k h0 ∩ finBlock n d k h).card = k - d := by
  have hinter : finBlock n 0 k h0 ∩ finBlock n d k h = finBlock n d (k - d) (by omega) := by
    ext x
    simp only [Finset.mem_inter, mem_finBlock]
    omega
  rw [hinter, card_finBlock]

/-- **The swap bound**: replacing an element of `s \ t` by one of `t \ s` moves `s` one edge
closer to `t` in `J(n, k)`, so `s` and `t` are at distance at most `|s \ t|`. -/
private theorem edist_johnson_le {n k : ℕ} : ∀ (d : ℕ) (s t : Finset (Fin n))
    (hs : s.card = k) (ht : t.card = k), (s \ t).card ≤ d →
      (CGraph.johnson n k).toSimple.edist ⟨s, hs⟩ ⟨t, ht⟩ ≤ (d : ℕ∞) := by
  classical
  intro d
  induction d with
  | zero =>
    intro s t hs ht hd
    have hst : s = t := Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 (Nat.le_zero.1 hd)))
      (by rw [hs, ht])
    subst hst
    simp
  | succ d ih =>
    intro s t hs ht hd
    rcases Finset.eq_empty_or_nonempty (s \ t) with hst | ⟨a, ha⟩
    · exact le_trans (ih s t hs ht (by simp [hst])) (by exact_mod_cast Nat.le_succ d)
    rw [Finset.mem_sdiff] at ha
    obtain ⟨b, hb⟩ : (t \ s).Nonempty := by
      rw [← Finset.card_pos, ← Finset.card_sdiff_comm (hs.trans ht.symm)]
      exact Finset.card_pos.2 ⟨a, Finset.mem_sdiff.2 ha⟩
    rw [Finset.mem_sdiff] at hb
    -- `s` with `a` swapped for `b`
    set w : Finset (Fin n) := insert b (s.erase a) with hw
    have hbw : b ∉ s.erase a := fun h ↦ hb.2 (Finset.mem_of_mem_erase h)
    have hwcard : w.card = k := by
      rw [hw, Finset.card_insert_of_notMem hbw, Finset.card_erase_of_mem ha.1, hs]
      have : 0 < k := hs ▸ Finset.card_pos.2 ⟨a, ha.1⟩
      omega
    have hinter : s ∩ w = s.erase a := by
      ext x
      simp only [hw, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hx, rfl | hx2⟩
        · exact absurd hx hb.2
        · exact hx2
      · rintro ⟨hxa, hxs⟩
        exact ⟨hxs, Or.inr ⟨hxa, hxs⟩⟩
    have hne : (⟨s, hs⟩ : (CGraph.johnson n k).V) ≠ ⟨w, hwcard⟩ := fun h ↦
      hb.2 (by rw [show s = w from congrArg Subtype.val h]; exact Finset.mem_insert_self _ _)
    have hadj : (CGraph.johnson n k).toSimple.Adj ⟨s, hs⟩ ⟨w, hwcard⟩ := by
      simp only [CGraph.toSimple_adj, CGraph.johnson_adj, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      exact ⟨hne, by rw [hinter, Finset.card_erase_of_mem ha.1, hs]⟩
    -- the swap removed `a` from the difference and added nothing
    have hstep : (w \ t).card ≤ d := by
      have hsub : w \ t ⊆ (s \ t).erase a := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_erase, Finset.mem_sdiff]
        rcases Finset.mem_insert.1 hx.1 with rfl | hx1
        · exact absurd hb.1 hx.2
        · exact ⟨(Finset.mem_erase.1 hx1).1, (Finset.mem_erase.1 hx1).2, hx.2⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_sdiff.2 ha)] at hcard
      omega
    calc (CGraph.johnson n k).toSimple.edist ⟨s, hs⟩ ⟨t, ht⟩
        ≤ (CGraph.johnson n k).toSimple.edist ⟨s, hs⟩ ⟨w, hwcard⟩
            + (CGraph.johnson n k).toSimple.edist ⟨w, hwcard⟩ ⟨t, ht⟩ :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + (d : ℕ∞) :=
          add_le_add ((SimpleGraph.edist_le (SimpleGraph.Adj.toWalk hadj)).trans (by simp))
            (ih w t hwcard ht hstep)
      _ = ((d + 1 : ℕ) : ℕ∞) := by push_cast; ring


/-- Two `k`-sets differing in `d` elements are at distance `d`, and `d ≤ min k (n - k)`. -/
theorem diameter_johnson {n k : ℕ} (hk : k ≤ n) :
    (johnson n k).diameter = min k (n - k) := by
  have : (johnson n k : IsoGraph) = Quotient.mk _ (CGraph.johnson n k) := rfl
  rw [this, diameter_mk]
  simp [CGraph.diameter, SimpleGraph.diam]
  set G := (CGraph.johnson n k).toSimple
  have adj_char : ∀ s t : (CGraph.johnson n k).V, G.Adj s t ↔ s ≠ t ∧ (s.val ∩ t.val).card = k - 1
    := by
    simp [G, CGraph.johnson_adj]
  -- Step 1: the distance is at most the number of elements that have to be swapped in.
  have edist_le_k_inter : ∀ s t : (CGraph.johnson n k).V, G.edist s t ≤ (k - (s.val ∩ t.val).card :
    ℕ∞) := by
    intro s t
    have hsd : (s.val \ t.val).card = k - (s.val ∩ t.val).card := by
      rw [Finset.card_sdiff, s.property, Finset.inter_comm]
    rw [← ENat.natCast_sub, ← hsd]
    exact edist_johnson_le _ s.1 t.1 s.2 t.2 le_rfl
  -- Step 2: the distance is at least that, because `|u \ t|` drops by at most one along an edge.
  have inter_le_k_sub_edist : ∀ s t : (CGraph.johnson n k).V, (k : ℕ∞) - ↑(s.val ∩ t.val).card ≤
    G.edist s t := by
    intro s t
    set phi : (CGraph.johnson n k).V → ℕ := fun u => (u.val \ t.val).card
    have card_uv : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (u.val \ v.val).card = 1 := by
      intro u v huv
      have huv' := adj_char u v |>.mp huv
      have h1 : (u.val ∩ v.val).card = k - 1 := huv'.2
      by_cases hk0 : k = 0
      · exfalso
        apply huv'.1
        have hu : u.val = ∅ := Finset.card_eq_zero.mp (by rw [u.property, hk0])
        have hv : v.val = ∅ := Finset.card_eq_zero.mp (by rw [v.property, hk0])
        exact Subtype.ext (by rw [hu, hv])
      · have h2 : (u.val \ v.val).card = k - (k - 1) := by
          rw [Finset.card_sdiff, u.property, ← h1, Finset.inter_comm]
        omega
    have phi_adj : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → phi u ≤ phi v + 1 := by
      intro u v huv
      -- every element of `u \ t` lies in `v \ t` or in the single-element set `u \ v`
      have hunion : (u.val \ t.val) ⊆ (v.val \ t.val) ∪ (u.val \ v.val) := by
        intro x hx
        simp [Finset.mem_sdiff] at hx ⊢
        by_cases hxv : x ∈ v.val
        · exact Or.inl ⟨hxv, hx.2⟩
        · exact Or.inr ⟨hx.1, hxv⟩
      have hcard_union : (u.val \ t.val).card ≤ (v.val \ t.val).card + (u.val \ v.val).card :=
        le_trans (Finset.card_le_card hunion) (Finset.card_union_le _ _)
      rw [card_uv u v huv] at hcard_union
      exact hcard_union
    -- `phi` is `1`-Lipschitz and vanishes at `t`, so `phi s` steps are needed to reach `t`
    have hphi_s : phi s = k - (s.val ∩ t.val).card := by
      simp only [phi]
      rw [Finset.card_sdiff, s.property, Finset.inter_comm]
    have ht0 : phi t = 0 := by simp [phi]
    have hlip := SimpleGraph.sub_le_edist_of_adj_le_succ phi_adj s t
    rwa [hphi_s, ht0, ENat.natCast_sub, Nat.cast_zero, tsub_zero] at hlip
  -- Step 3: so the distance is exactly `k - |s ∩ t|`.
  have edist_eq : ∀ s t : (CGraph.johnson n k).V, G.edist s t = (k : ℕ∞) - ↑(s.val ∩ t.val).card :=
    fun s t ↦ le_antisymm (edist_le_k_inter s t) (inter_le_k_sub_edist s t)
  have hmin_coe : min (↑k) (↑(n - k) : ℕ∞) = ↑(min k (n - k)) := by
    by_cases h : k ≤ n - k
    · rw [min_eq_left (mod_cast h), min_eq_left (mod_cast h)]
    · rw [min_eq_right (mod_cast le_of_not_ge h), min_eq_right (mod_cast le_of_not_ge h)]
  -- Step 4: `|s ∩ t| ≥ 2k - n`, so no pair is further apart than `min k (n - k)` …
  have upper : ∀ s t : (CGraph.johnson n k).V, G.edist s t ≤ (min (↑k) (↑(n - k) : ℕ∞)) := by
    intro s t
    rw [edist_eq s t]
    apply le_min
    · rw [← ENat.natCast_sub]
      exact Nat.cast_le.mpr (Nat.sub_le _ _)
    · have hunion : (s.val ∪ t.val).card + (s.val ∩ t.val).card = 2 * k := by
        rw [Finset.card_union_add_card_inter, s.property, t.property]; ring
      have hunion_le_n : (s.val ∪ t.val).card ≤ n :=
        le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
      have hle : k - (s.val ∩ t.val).card ≤ n - k := by omega
      rw [ENat.natCast_sub]
      exact Nat.cast_le.mpr hle
  -- … and two blocks of `k` consecutive elements offset by `min k (n - k)` are that far apart.
  have edist_le_ediam_aux : min (↑k) (↑(n - k) : ℕ∞) ≤ G.ediam := by
    have h0 : 0 + k ≤ n := by omega
    have hdn : min k (n - k) + k ≤ n := by omega
    let s : (CGraph.johnson n k).V := ⟨finBlock n 0 k h0, card_finBlock h0⟩
    let t : (CGraph.johnson n k).V := ⟨finBlock n (min k (n - k)) k hdn, card_finBlock hdn⟩
    have hst : G.edist s t = ((min k (n - k) : ℕ) : ℕ∞) := by
      rw [edist_eq s t, show (s.val ∩ t.val).card = k - min k (n - k) from
        card_inter_finBlock h0 hdn (min_le_left _ _), ← ENat.natCast_sub]
      congr 1
      omega
    rw [hmin_coe, ← hst]
    exact SimpleGraph.edist_le_ediam
  rw [le_antisymm (SimpleGraph.ediam_le_of_edist_le upper) edist_le_ediam_aux, hmin_coe,
    ENat.toNat_natCast]

/-- Johnson graphs are connected: any two `k`-sets are a finite number of swaps apart. -/
theorem isConnected_johnson {n k : ℕ} (hk : k ≤ n) : IsConnected (johnson n k) := by
  change IsConnected ⟦CGraph.johnson n k⟧
  rw [IsoGraph.isConnected_mk]
  classical
  obtain ⟨s₀, -, hs₀⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (by simpa using hk)
  exact { preconnected := fun ⟨u, hu⟩ ⟨v, hv⟩ ↦
            SimpleGraph.reachable_of_edist_ne_top
              (ne_top_of_le_ne_top (ENat.natCast_ne_top _) (edist_johnson_le _ u v hu hv le_rfl)),
          nonempty := ⟨⟨s₀, hs₀⟩⟩ }

/-- The `2 × n` grid has four corners of degree two and `2n - 4` interior vertices of degree
three. -/
theorem degSequence_ladder (n : ℕ) :
    degSequence (ladder (n + 2)) = List.replicate 4 2 ++ List.replicate (2 * n) 3 := by
  unfold ladder
  rw [degSequence_eq_sort]
  rw [degMultiset_cartesianProduct, degMultiset_path, degMultiset_complete]
  simp only [Multiset.bind, Multiset.map_replicate]
  simp (config := { decide := true }) only [show (2 : ℕ) - 1 = 1 from rfl]
  -- Compute map over cons/replicate
  have h1 : Multiset.map (fun x => Multiset.replicate 2 (x + 1)) (1 ::ₘ 1 ::ₘ Multiset.replicate n
    2) =
    Multiset.replicate 2 2 ::ₘ Multiset.replicate 2 2 ::ₘ Multiset.replicate n (Multiset.replicate 2
      3) := by
    simp [Multiset.map_cons, Multiset.map_replicate]
  rw [h1]
  -- Compute join
  simp only [Multiset.join]
  simp (config := { decide := true }) [
    Multiset.sum_replicate]
  -- Step: n • replicate 2 3 = replicate (2 * n) 3
  have hrep : ∀ (m : ℕ) (a : ℕ), m • Multiset.replicate 2 a = Multiset.replicate (2 * m) a := by
    intro m a
    induction m with
    | zero => simp
    | succ p ih =>
      have : 2 * (p + 1) = 2 * p + 2 := by omega
      rw [this]
      rw [succ_nsmul, ih, Multiset.replicate_add]
  -- Now handle the main sort goal
  have h3 : (3 ::ₘ ({3} : Multiset ℕ)) = Multiset.replicate 2 3 := by rfl
  rw [h3, hrep]
  exact sort_eq_of_pairwise
    (by simp [List.pairwise_replicate, List.mem_replicate]) rfl

/-! ### Consequences of the Johnson graph's connectivity and diameter -/

@[simp] theorem numComponents_johnson {n k : ℕ} (hk : k ≤ n) : (johnson n k).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_johnson hk)

@[simp] theorem isConnected_compl_kneser_two (n : ℕ) : IsConnected (kneser (n + 2) 2)ᶜ := by
  rw [← triangular_eq_compl_kneser]
  exact isConnected_johnson (by omega)

/-- The Johnson graph `J(n, 1)` is the complete graph `Kₙ`, so its diameter is one. -/
example (n : ℕ) : (johnson (n + 2) 1).diameter = 1 := by
  rw [diameter_johnson (by omega)]
  omega

/-! ### The `2 × n` grid, from its degree sequence -/

theorem two_mul_E_ladder (n : ℕ) : 2 * (ladder (n + 2)).E = 8 + 6 * n := by
  have h := sum_degSequence (ladder (n + 2))
  rw [degSequence_ladder, List.sum_append, List.sum_replicate, List.sum_replicate,
    smul_eq_mul, smul_eq_mul] at h
  omega

/-- Consecutive rim vertices of a wheel are adjacent. -/
private theorem wheel_rim_adj {m : ℕ} (u v : ℕ) (hu : u < m) (hv : v < m) (h : u + 1 = v) :
    (CGraph.wheel m).Adj (Sum.inr ⟨u, hu⟩) (Sum.inr ⟨v, hv⟩) = true := by
  show (CGraph.complete 1 ∇g CGraph.cycle m).Adj (Sum.inr ⟨u, hu⟩) (Sum.inr ⟨v, hv⟩) = true
  rw [CGraph.join_adj_inr_inr, CGraph.cycle_adj_val]
  exact ⟨by simp only []; omega, Or.inl (by simp only []; rw [h, Nat.mod_eq_of_lt hv])⟩

/-- **A wheel has a near-perfect matching.**  When the rim `Cₙ₊₃` is even it matches itself
perfectly; when it is odd, one rim vertex is left over and a spoke to the hub takes care of
it. -/
theorem matchNum_wheel (n : ℕ) : (wheel (n + 3)).matchNum = (n + 4) / 2 := by
  refine le_antisymm ?_ ?_
  · have h1 := (wheel (n + 3)).two_mul_matchNum_le_V
    rw [V_wheel] at h1
    omega
  · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · -- `n = 2k`: the rim has odd length `2k + 3`, so pair `2j+1` with `2j+2` along it and
      -- spend one spoke on the leftover rim vertex `0`.
      rw [show (wheel (2 * k + 3) : IsoGraph) = ⟦CGraph.wheel (2 * k + 3)⟧ from rfl, matchNum_mk,
        show (2 * k + 4) / 2 = Fintype.card (Unit ⊕ Fin (k + 1)) by simp; omega]
      refine CGraph.card_le_matchNum
        (Sum.elim (fun _ ↦ Sum.inl ⟨0, by omega⟩)
          fun j : Fin (k + 1) ↦ Sum.inr ⟨2 * j + 1, by have := j.isLt; omega⟩)
        (Sum.elim (fun _ ↦ Sum.inr ⟨0, by omega⟩)
          fun j : Fin (k + 1) ↦ Sum.inr ⟨2 * j + 2, by have := j.isLt; omega⟩) ?_ ?_
      · rintro (_ | j)
        · exact CGraph.join_adj_inl_inr _ _ _ _
        · exact wheel_rim_adj _ _ _ _ rfl
      · rintro (⟨⟩ | i) (⟨⟩ | j) hij
        · exact absurd rfl hij
        · have hj := j.isLt
          exact ⟨by simp, by simp, CGraph.inr_mk_ne_inr_mk _ _ (by omega),
            CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩
        · have hi := i.isLt
          exact ⟨by simp, CGraph.inr_mk_ne_inr_mk _ _ (by omega), by simp,
            CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩
        · have hne : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (by rw [Fin.ext h])
          exact ⟨CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega),
            CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩
    · -- `n = 2k + 1`: the rim has even length `2k + 4` and a perfect matching of its own.
      rw [show (wheel (2 * k + 1 + 3) : IsoGraph) = ⟦CGraph.wheel (2 * k + 4)⟧ from rfl,
        matchNum_mk, show (2 * k + 1 + 4) / 2 = Fintype.card (Fin (k + 2)) by simp; omega]
      refine CGraph.card_le_matchNum
        (fun j : Fin (k + 2) ↦ Sum.inr ⟨2 * j, by have := j.isLt; omega⟩)
        (fun j : Fin (k + 2) ↦ Sum.inr ⟨2 * j + 1, by have := j.isLt; omega⟩)
        (fun _ ↦ wheel_rim_adj _ _ _ _ rfl) ?_
      intro i j hij
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (by rw [Fin.ext h])
      exact ⟨CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega),
        CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩

@[simp] theorem radius_strongProduct_hypercube (m n : ℕ) :
    (hypercube m ⊠g hypercube n).radius = max m n := by
  rw [radius_strongProduct (isConnected_hypercube m) (isConnected_hypercube n), radius_hypercube,
    radius_hypercube]

@[simp] theorem diameter_strongProduct_hypercube (m n : ℕ) :
    (hypercube m ⊠g hypercube n).diameter = max m n := by
  rw [diameter_strongProduct (isConnected_hypercube m) (isConnected_hypercube n),
    diameter_hypercube, diameter_hypercube]

/-- A near-perfect matching leaves at most one vertex over, so the wheel is covered by that many
cliques. -/
theorem cliqueCoverNum_wheel_le (n : ℕ) :
    (wheel (n + 3)).cliqueCoverNum ≤ (n + 5) / 2 := by
  have h := cliqueCoverNum_le_V_sub_matchNum (wheel (n + 3))
  rw [V_wheel, matchNum_wheel] at h
  omega

@[simp] theorem isVertexTransitive_johnson (n k : ℕ) : IsVertexTransitive (johnson n k) :=
  CGraph.isVertexTransitive_johnson n k

/-! ### Invariants of the Johnson graphs from vertex transitivity -/

/-- The radius of a Johnson graph equals its diameter, `min k (n - k)`. -/
@[simp] theorem radius_johnson {n k : ℕ} (hk : k ≤ n) : (johnson n k).radius = min k (n - k) := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_johnson n k),
    diameter_johnson hk]

/-- The clique–coclique bound for a Johnson graph. -/
theorem indepNum_mul_cliqueNum_le_johnson (n k : ℕ) :
    (johnson n k).indepNum * (johnson n k).cliqueNum ≤ n.choose k := by
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_johnson n k)
  rwa [V_johnson] at h

/-- A vertex-transitive graph with an edge has an independent set on at most half its vertices. -/
theorem two_mul_indepNum_le_johnson {n k : ℕ} (hE : 0 < (johnson n k).E) :
    2 * (johnson n k).indepNum ≤ n.choose k := by
  have h := two_mul_indepNum_le_V (isVertexTransitive_johnson n k) hE
  rwa [V_johnson] at h

theorem coverNum_johnson (n k : ℕ) :
    (johnson n k).coverNum = n.choose k - (johnson n k).indepNum := by
  rw [coverNum_eq, V_johnson]

@[simp] theorem not_isVertexTransitive_star (n : ℕ) : ¬ IsVertexTransitive (star (n + 2)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 2 = n + 1 + 1 from rfl, minDeg_star, maxDeg_star]
  omega

/-- The hub of a wheel on five or more vertices has degree larger than three. -/
@[simp] theorem not_isVertexTransitive_wheel (n : ℕ) :
    ¬ IsVertexTransitive (wheel (n + 4)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 4 = n + 1 + 3 from rfl, minDeg_wheel, maxDeg_wheel]
  omega

/-- The hub of a fan on five or more vertices has degree larger than two. -/
@[simp] theorem not_isVertexTransitive_fan (n : ℕ) : ¬ IsVertexTransitive (fan (n + 3)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 3 = n + 1 + 2 from rfl, minDeg_fan, show n + 1 + 2 = n + 3 from rfl, maxDeg_fan]
  omega

/-- The spine of a book with two or more pages has degree larger than two. -/
@[simp] theorem not_isVertexTransitive_book (n : ℕ) : ¬ IsVertexTransitive (book (n + 2)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 2 = n + 1 + 1 from rfl, minDeg_book, maxDeg_book]
  omega

/-- The four corners of a ladder have degree two, the rest three. -/
@[simp] theorem not_isVertexTransitive_ladder (n : ℕ) :
    ¬ IsVertexTransitive (ladder (n + 3)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 3 = n + 1 + 2 from rfl, minDeg_ladder, show n + 1 + 2 = n + 3 from rfl,
    maxDeg_ladder]
  omega

/-! ### Regularity of the ladder and of the wheel's rim -/

/-- A ladder is not regular for three or more rungs; the two small ones are `K₂` and `C₄`. -/
@[simp] theorem isRegularWith_ladder_two : (ladder 2).IsRegularWith 2 := by
  rw [ladder_two]
  exact isRegularWith_cycle 1

@[simp] theorem isVertexTransitive_ladder_two : IsVertexTransitive (ladder 2) := by
  rw [ladder_two]
  exact isVertexTransitive_cycle 4

@[simp] theorem isVertexTransitive_ladder_one : IsVertexTransitive (ladder 1) := by
  rw [ladder_one]
  exact isVertexTransitive_complete 2

/-- **The handshake lemma for a circulant**: `2|E| = n · δ`, with no need to count the
connection set. -/
theorem two_mul_E_circulant (n : ℕ) (S : List ℕ) (hn : 0 < n) :
    2 * (circulant n S).E = n * (circulant n S).minDeg := by
  have h := two_mul_E_of_isVertexTransitive (G := circulant n S) (by simpa using hn)
    (isVertexTransitive_circulant n S)
  rwa [V_circulant] at h

/-- A circulant on an odd number of vertices has even degree. -/
theorem even_minDeg_circulant_of_odd {n : ℕ} (S : List ℕ) (hodd : n % 2 = 1) :
    (circulant n S).minDeg % 2 = 0 := by
  refine even_minDeg_of_isVertexTransitive_of_odd (G := circulant n S) (by simp; omega)
    (isVertexTransitive_circulant n S) ?_
  rwa [V_circulant]

/-- A dominating set in `T(n) = L(Kₙ)` is an edge dominating set of `Kₙ`, so it must cover all
but one vertex; a near-perfect matching does it. -/
theorem domNum_triangular (n : ℕ) : (triangular (n + 2)).domNum = (n + 2) / 2 := by
  simp only [triangular, IsoGraph.johnson, IsoGraph.domNum_mk]
  classical
  -- two pairs are adjacent exactly when they are distinct and meet
  have hadj : ∀ u v : (CGraph.johnson (n + 2) 2).V,
      (CGraph.johnson (n + 2) 2).Adj u v = true ↔ u ≠ v ∧ (u.1 ∩ v.1).card = 1 := by
    intro u v
    simp [CGraph.johnson_adj]
  -- a set of `m` pairs covers at most `2m` points
  have hcov : ∀ s : Finset (CGraph.johnson (n + 2) 2).V,
      (s.biUnion fun u ↦ u.1).card ≤ 2 * s.card := fun s ↦
    calc (s.biUnion fun u ↦ u.1).card ≤ ∑ u ∈ s, u.1.card := Finset.card_biUnion_le
      _ = 2 * s.card := by rw [Finset.sum_congr rfl fun u _ ↦ u.2]; simp [mul_comm]
  refine le_antisymm ?_ ?_
  · -- an independent set is a matching, so it has at most `⌊n/2⌋` pairs, and it dominates
    refine le_trans (CGraph.domNum_le_indepNum _) (CGraph.indepNum_le_of_forall_card_le ?_)
    intro S hS
    have hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint u.1 v.1 := by
      intro u hu v hv huv
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hne
      exact hS hu hv huv ((hadj u v).2 ⟨huv, CGraph.card_inter_eq_one_of_ne u v huv hne⟩)
    have hcard : (S.biUnion fun u ↦ u.1).card = 2 * S.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl fun u _ ↦ u.2]
      simp [mul_comm]
    have hle : (S.biUnion fun u ↦ u.1).card ≤ n + 2 := by
      simpa using Finset.card_le_card (Finset.subset_univ (S.biUnion fun u ↦ u.1))
    omega
  · -- a dominating set covering fewer than `n + 1` points misses a pair entirely
    obtain ⟨D, hDcard, hD⟩ := (CGraph.johnson (n + 2) 2).exists_isDominatingSet_domNum
    refine hDcard ▸ ?_
    by_contra hlt
    push Not at hlt
    have h2 := hcov D
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ Finset.univ \ D.biUnion fun u ↦ u.1,
        ∃ b ∈ Finset.univ \ D.biUnion fun u ↦ u.1, a ≠ b :=
      Finset.one_lt_card.mp (by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        omega)
    have hnot : ∀ x ∈ Finset.univ \ D.biUnion fun u ↦ u.1, ∀ u ∈ D, x ∉ u.1 :=
      fun x hx u hu hxu ↦ (Finset.mem_sdiff.1 hx).2 (Finset.mem_biUnion.2 ⟨u, hu, hxu⟩)
    rcases hD ⟨{a, b}, Finset.card_pair hab⟩ with hv | ⟨u, hu, huv⟩
    · exact hnot a ha _ hv (Finset.mem_insert_self _ _)
    · obtain ⟨x, hx⟩ := Finset.card_pos.1 (by
        rw [((hadj u _).1 huv).2]; omega :
        0 < (u.1 ∩ ({a, b} : Finset (Fin (n + 2)))).card)
      rw [Finset.mem_inter] at hx
      rcases Finset.mem_insert.1 hx.2 with rfl | hx2
      · exact hnot x ha u hu hx.1
      · rw [Finset.mem_singleton] at hx2
        subst hx2
        exact hnot x hb u hu hx.1

@[simp] theorem domNum_johnson_two (n : ℕ) : (johnson (n + 2) 2).domNum = (n + 2) / 2 :=
  domNum_triangular n

/-- **A prism over a cycle of length at least four has girth four**, the odd case included:
the square faces are the shortest cycles. -/
@[simp] theorem girth_prism (n : ℕ) : (prism (n + 4)).girth = 4 := by
  refine girth_cartesianProduct_of_cliqueNum_le_two ?_ (by simp) (by rw [cliqueNum_cycle]) (by simp)
  rw [show n + 4 = n + 1 + 3 by ring, E_cycle]
  omega

/-- **A grid has girth four.** -/
@[simp] theorem girth_grid (m n : ℕ) :
    (path (m + 2) □g path (n + 2)).girth = 4 :=
  girth_cartesianProduct (by simp) (by simp) (isBipartite_path (m + 2)) (isBipartite_path (n + 2))

/-- The Johnson graph has a triangle, so a clique of size three. -/
theorem three_le_cliqueNum_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    3 ≤ (johnson n k).cliqueNum :=
  girth_eq_three_iff.1 (girth_johnson hk h)

theorem three_le_chromNum_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    3 ≤ (johnson n k).chromNum :=
  (three_le_cliqueNum_johnson hk h).trans (cliqueNum_le_chromNum _)

theorem not_isAcyclic_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    ¬ IsAcyclic (johnson n k) :=
  not_isAcyclic_of_girth_pos (by rw [girth_johnson hk h]; omega)

theorem not_isTree_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) : ¬ IsTree (johnson n k) :=
  not_isTree_of_girth_pos (by rw [girth_johnson hk h]; omega)

/-- **Four codewords dominate the four-cube**: the sphere-covering bound needs at least four,
and four suffice. -/
theorem domNum_hypercube_four : (hypercube 4).domNum = 4 := by
  apply Nat.le_antisymm
  · -- Upper bound: exhibit a dominating set of size 4
    let c0 : (CGraph.hypercube 4).V := fun _ => false
    let c1 : (CGraph.hypercube 4).V := fun i => (i = 3)
    let c2 : (CGraph.hypercube 4).V := fun i => (i ≠ 3)
    let c3 : (CGraph.hypercube 4).V := fun _ => true
    let S : Finset (CGraph.hypercube 4).V :=
      (insert c0 (insert c1 (insert c2 (singleton c3))))
    have hdom : (CGraph.hypercube 4).IsDominatingSet S := by
      intro v
      revert v
      decide
    have hcard : S.card = 4 := by decide
    show CGraph.domNum (CGraph.hypercube 4) ≤ 4
    exact le_trans (CGraph.domNum_le_card_of_isDominatingSet hdom) hcard.le
  · -- Lower bound: 16 ≤ domNum * 5
    show 4 ≤ (hypercube 4).domNum
    simp only [hypercube, domNum_mk]
    have hcard : FinEnum.card (CGraph.hypercube 4).V = 16 := by decide
    have hdeg : CGraph.maxDeg (CGraph.hypercube 4) ≤ 4 := by
      apply CGraph.maxDeg_le_of_forall
      intro v
      show (CGraph.hypercube 4).toSimple.degree v ≤ 4
      revert v; native_decide
    have hbound : 16 ≤ CGraph.domNum (CGraph.hypercube 4) *
        (CGraph.maxDeg (CGraph.hypercube 4) + 1) := by
      rw [← hcard]
      apply CGraph.card_le_domNum_mul_maxDeg_add_one
    nlinarith

theorem three_le_cliqueNum_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    3 ≤ (kneser n k).cliqueNum :=
  girth_eq_three_iff.1 (girth_kneser hk h)

theorem three_le_chromNum_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    3 ≤ (kneser n k).chromNum :=
  (three_le_cliqueNum_kneser hk h).trans (cliqueNum_le_chromNum _)

theorem not_isAcyclic_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    ¬ IsAcyclic (kneser n k) :=
  not_isAcyclic_of_girth_pos (by rw [girth_kneser hk h]; omega)

theorem not_isTree_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) : ¬ IsTree (kneser n k) :=
  not_isTree_of_girth_pos (by rw [girth_kneser hk h]; omega)

/-! ### Which named families are trees -/

@[simp] theorem not_isTree_book (n : ℕ) : ¬ IsTree (book (n + 1)) :=
  not_isTree_of_girth_pos (by rw [girth_book]; omega)

@[simp] theorem not_isTree_cocktailParty (n : ℕ) : ¬ IsTree (cocktailParty (n + 3)) :=
  not_isTree_of_girth_pos (by rw [girth_cocktailParty]; omega)

@[simp] theorem not_isTree_triangular (n : ℕ) : ¬ IsTree (triangular (n + 4)) :=
  not_isTree_of_girth_pos (by rw [girth_triangular]; omega)

theorem not_isTree_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : 3 ≤ max m n) :
    ¬ IsTree (rook m n) :=
  not_isTree_of_girth_pos (by rw [girth_rook hm hn h]; omega)

@[simp] theorem not_isTree_completeMultipartite_replicate (m d : ℕ) :
    ¬ IsTree (completeMultipartite (List.replicate (m + 3) (d + 1))) :=
  not_isTree_of_girth_pos (by rw [girth_completeMultipartite_replicate]; omega)

theorem not_isTree_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    ¬ IsTree (paley q) :=
  not_isTree_of_girth_pos (by rw [girth_paley q hq hq9]; omega)

@[simp] theorem isAcyclic_star (n : ℕ) : IsAcyclic (star n) :=
  ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_star n)).2

/-! ### Circulants -/

/-- The edge count of a circulant, from its regularity. -/
theorem E_circulant (n : ℕ) (S : List ℕ) (hn : 0 < n) :
    (circulant n S).E = n * (circulant n S).minDeg / 2 := by
  rw [← two_mul_E_circulant n S hn]
  omega

theorem diameter_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).diameter = (circulant n S).radius := (radius_circulant n S).symm

/-! ### Balanced complete multipartite graphs -/

/-- A balanced complete multipartite graph is regular: every vertex misses exactly its own
part. -/
@[simp] theorem isRegularWith_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m d)).IsRegularWith ((m - 1) * d) := by
  rw [completeMultipartite_replicate]
  simpa using (isRegularWith_complete m).lexProduct (isRegularWith_empty d)

@[simp] theorem isVertexTransitive_completeMultipartite_replicate (m d : ℕ) :
    IsVertexTransitive (completeMultipartite (List.replicate m d)) := by
  rw [completeMultipartite_replicate]
  exact (isVertexTransitive_complete m).lexProduct (isVertexTransitive_empty d)

/-! ### Domination in Kneser graphs -/

/-- **Three pairs dominate a Kneser graph on at least five points**: `{0,1}`, `{1,2}` and
`{0,2}` between them meet or miss every pair, and no two pairs can do the same, because two
pairs use up at most four of the `n ≥ 5` points and a third pair can be built to meet both. -/
theorem domNum_kneser_two (n : ℕ) : (kneser (n + 5) 2).domNum = 3 := by
  have h01 : (0 : Fin (n + 5)) ≠ 1 := by
    intro h; have := Fin.ext_iff.mp h; simp at this
  have h02 : (0 : Fin (n + 5)) ≠ 2 := by
    intro h; have := Fin.ext_iff.mp h; simp [Nat.mod_eq_of_lt (by omega : 2 < n + 5)] at this
  have h12 : (1 : Fin (n + 5)) ≠ 2 := by
    intro h; have := Fin.ext_iff.mp h; simp [Nat.mod_eq_of_lt (by omega : 2 < n + 5)] at this
  -- two pairs differ as soon as one contains a point the other misses
  have vne : ∀ (p q : (CGraph.kneser (n + 5) 2).V) (y : Fin (n + 5)), y ∈ p.1 → y ∉ q.1 →
      p ≠ q := fun p q y hyp hyq h ↦ hyq (h ▸ hyp)
  -- Every pair either *is* one of `{0,1}`, `{1,2}`, `{0,2}` or misses one of them.
  have key_dom : ∀ t : Finset (Fin (n + 5)), t.card = 2 →
      t = {0, 1} ∨ t = {1, 2} ∨ t = {0, 2} ∨
        t ∩ {0, 1} = ∅ ∨ t ∩ {1, 2} = ∅ ∨ t ∩ {0, 2} = ∅ := by
    intro t ht
    -- a pair containing `a` and `b` *is* `{a, b}` …
    have pair : ∀ a b : Fin (n + 5), a ≠ b → a ∈ t → b ∈ t → t = {a, b} := fun a b hab ha hb ↦
      (Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff, ha, hb])
        (by rw [ht, Finset.card_pair hab])).symm
    -- … and one containing neither misses `{a, b}` altogether
    have miss : ∀ a b : Fin (n + 5), a ∉ t → b ∉ t → t ∩ {a, b} = ∅ := by
      intro a b ha hb
      simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, Finset.mem_insert,
        Finset.mem_singleton, not_and]
      rintro x hx (rfl | rfl)
      · exact ha hx
      · exact hb hx
    by_cases hm0 : (0 : Fin (n + 5)) ∈ t <;> by_cases hm1 : (1 : Fin (n + 5)) ∈ t <;>
        by_cases hm2 : (2 : Fin (n + 5)) ∈ t
    · -- `t` would have three elements
      have hsub : ({0, 1, 2} : Finset (Fin (n + 5))) ⊆ t := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hc := Finset.card_le_card hsub
      rw [ht, show ({0, 1, 2} : Finset (Fin (n + 5))).card = 3 by
        simp [Finset.card_insert_of_notMem, h01, h02, h12]] at hc
      omega
    · exact Or.inl (pair 0 1 h01 hm0 hm1)
    · exact Or.inr (Or.inr (Or.inl (pair 0 2 h02 hm0 hm2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (miss 1 2 hm1 hm2)))))
    · exact Or.inr (Or.inl (pair 1 2 h12 hm1 hm2))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (miss 0 2 hm0 hm2)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (miss 0 1 hm0 hm1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (miss 0 1 hm0 hm1))))
  rw [kneser, IsoGraph.domNum_mk]
  -- Upper bound: the three pairs above dominate.
  have hupp : (CGraph.kneser (n + 5) 2).domNum ≤ 3 := by
    let v01 : (CGraph.kneser (n + 5) 2).V := ⟨{0, 1}, Finset.card_pair h01⟩
    let v12 : (CGraph.kneser (n + 5) 2).V := ⟨{1, 2}, Finset.card_pair h12⟩
    let v02 : (CGraph.kneser (n + 5) 2).V := ⟨{0, 2}, Finset.card_pair h02⟩
    have hne01_12 : v01 ≠ v12 := vne _ _ 0 (by simp [v01]) (by simp [v12, h01, h02])
    have hne01_02 : v01 ≠ v02 := vne _ _ 1 (by simp [v01]) (by simp [v02, h01.symm, h12])
    have hne12_02 : v12 ≠ v02 := vne _ _ 1 (by simp [v12]) (by simp [v02, h01.symm, h12])
    have hcard_s : ({v01, v12, v02} : Finset (CGraph.kneser (n + 5) 2).V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne01_12, hne01_02]),
        Finset.card_insert_of_notMem (by simp [hne12_02]), Finset.card_singleton]
    refine hcard_s ▸ CGraph.domNum_le_card_of_isDominatingSet ?_
    rintro ⟨t, ht⟩
    by_cases hmem : (⟨t, ht⟩ : (CGraph.kneser (n + 5) 2).V) ∈ ({v01, v12, v02} : Finset _)
    · exact Or.inl hmem
    right
    -- a member of the dominating set disjoint from `t` is adjacent to it
    have dom_of : ∀ w : (CGraph.kneser (n + 5) 2).V, w ∈ ({v01, v12, v02} : Finset _) →
        t ∩ w.1 = ∅ → ∃ w' ∈ ({v01, v12, v02} : Finset _),
          (CGraph.kneser (n + 5) 2).Adj w' ⟨t, ht⟩ := by
      intro w hw hint
      refine ⟨w, hw, ?_⟩
      rw [CGraph.kneser_adj]
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
      exact ⟨fun h ↦ hmem (h ▸ hw), by rw [Finset.inter_comm]; exact hint⟩
    have hv01 : v01 ∈ ({v01, v12, v02} : Finset _) := by simp
    have hv12 : v12 ∈ ({v01, v12, v02} : Finset _) := by simp
    have hv02 : v02 ∈ ({v01, v12, v02} : Finset _) := by simp
    rcases key_dom t ht with h | h | h | h | h | h
    · exact absurd ((show (⟨t, ht⟩ : (CGraph.kneser (n + 5) 2).V) = v01 from Subtype.ext h) ▸ hv01)
        hmem
    · exact absurd ((show (⟨t, ht⟩ : (CGraph.kneser (n + 5) 2).V) = v12 from Subtype.ext h) ▸ hv12)
        hmem
    · exact absurd ((show (⟨t, ht⟩ : (CGraph.kneser (n + 5) 2).V) = v02 from Subtype.ext h) ▸ hv02)
        hmem
    · exact dom_of v01 hv01 h
    · exact dom_of v12 hv12 h
    · exact dom_of v02 hv02 h
  -- Lower bound: no two pairs dominate, since some third pair meets both.
  have hlow : 2 < (CGraph.kneser (n + 5) 2).domNum := by
    refine CGraph.two_lt_domNum _ ?_ ?_
    · rw [CGraph.card_kneser]
      calc 2 ≤ Nat.choose 5 2 := by decide
        _ ≤ (n + 5).choose 2 := Nat.choose_le_choose 2 (by omega)
    intro u v
    -- two vertices use up at most four points, so some point `x` lies outside both
    obtain ⟨x, hx⟩ : ∃ x : Fin (n + 5), x ∉ u.1 ∪ v.1 := by
      by_contra hall
      push Not at hall
      have h1 := Finset.card_le_card (fun y _ ↦ hall y :
        (Finset.univ : Finset (Fin (n + 5))) ⊆ u.1 ∪ v.1)
      have h2 := Finset.card_union_le u.1 v.1
      rw [Finset.card_univ, Fintype.card_fin] at h1
      rw [u.2, v.2] at h2
      omega
    have hxu : x ∉ u.1 := fun h ↦ hx (Finset.mem_union_left _ h)
    have hxv : x ∉ v.1 := fun h ↦ hx (Finset.mem_union_right _ h)
    have nadj : ∀ (p q : (CGraph.kneser (n + 5) 2).V) (y : Fin (n + 5)), y ∈ p.1 → y ∈ q.1 →
        (CGraph.kneser (n + 5) 2).Adj p q = false := by
      intro p q y hyp hyq
      rw [CGraph.kneser_adj, Bool.and_eq_false_iff]
      exact Or.inr (by
        simp only [decide_eq_false_iff_not]
        exact fun h ↦ Finset.notMem_empty y (h ▸ Finset.mem_inter.mpr ⟨hyp, hyq⟩))
    by_cases hint : (u.1 ∩ v.1).Nonempty
    · -- `u` and `v` share a point: pair it with `x`
      obtain ⟨a, ha⟩ := hint
      rw [Finset.mem_inter] at ha
      have hax : a ≠ x := fun h ↦ hxu (h ▸ ha.1)
      exact ⟨⟨{a, x}, Finset.card_pair hax⟩, vne _ _ x (by simp) hxu, vne _ _ x (by simp) hxv,
        nadj _ _ a ha.1 (by simp), nadj _ _ a ha.2 (by simp)⟩
    · -- `u` and `v` are disjoint: take one point from each
      rw [Finset.not_nonempty_iff_eq_empty] at hint
      obtain ⟨a, ha⟩ : u.1.Nonempty := Finset.card_pos.mp (by rw [u.2]; omega)
      obtain ⟨b, hb⟩ : v.1.Nonempty := Finset.card_pos.mp (by rw [v.2]; omega)
      have hbu : b ∉ u.1 := fun h ↦ Finset.notMem_empty b (hint ▸ Finset.mem_inter.mpr ⟨h, hb⟩)
      have hav : a ∉ v.1 := fun h ↦ Finset.notMem_empty a (hint ▸ Finset.mem_inter.mpr ⟨ha, h⟩)
      have hab : a ≠ b := fun h ↦ hav (h ▸ hb)
      exact ⟨⟨{a, b}, Finset.card_pair hab⟩, vne _ _ b (by simp) hbu, vne _ _ a (by simp) hav,
        nadj _ _ a ha (by simp), nadj _ _ b hb (by simp)⟩
  omega

/-- Consecutive spine vertices of a fan are adjacent. -/
private theorem fan_spine_adj {m : ℕ} (u v : ℕ) (hu : u < m) (hv : v < m) (h : u + 1 = v) :
    (CGraph.complete 1 ∇g CGraph.path m).Adj (Sum.inr ⟨u, hu⟩) (Sum.inr ⟨v, hv⟩) = true := by
  rw [CGraph.join_adj_inr_inr, CGraph.path_adj_val]
  exact ⟨by simp only []; omega, Or.inl (by simp only []; omega)⟩

/-- **A fan has a near-perfect matching**, by the same argument as the wheel: the spine matches
itself, and a spoke to the hub mops up the leftover end vertex when the spine is odd. -/
@[simp] theorem matchNum_fan (n : ℕ) : (fan (n + 1)).matchNum = (n + 2) / 2 := by
  refine le_antisymm ?_ ?_
  · have h1 := (fan (n + 1)).two_mul_matchNum_le_V
    rw [V_fan] at h1
    omega
  · rw [fan_eq_join, IsoGraph.complete, IsoGraph.path, join_mk, matchNum_mk]
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · -- `n = 2k`: the spine `P₂ₖ₊₁` has odd order, so match `1—2, 3—4, …` along it and spend a
      -- spoke on the leftover end vertex `0`.
      rw [show (2 * k + 2) / 2 = Fintype.card (Unit ⊕ Fin k) by simp; omega]
      refine CGraph.card_le_matchNum
        (Sum.elim (fun _ ↦ Sum.inl ⟨0, by omega⟩)
          fun j : Fin k ↦ Sum.inr ⟨2 * j + 1, by have := j.isLt; omega⟩)
        (Sum.elim (fun _ ↦ Sum.inr ⟨0, by omega⟩)
          fun j : Fin k ↦ Sum.inr ⟨2 * j + 2, by have := j.isLt; omega⟩) ?_ ?_
      · rintro (_ | j)
        · exact CGraph.join_adj_inl_inr _ _ _ _
        · exact fan_spine_adj _ _ _ _ rfl
      · rintro (⟨⟩ | i) (⟨⟩ | j) hij
        · exact absurd rfl hij
        · have hj := j.isLt
          exact ⟨by simp, by simp, CGraph.inr_mk_ne_inr_mk _ _ (by omega),
            CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩
        · have hi := i.isLt
          exact ⟨by simp, CGraph.inr_mk_ne_inr_mk _ _ (by omega), by simp,
            CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩
        · have hne : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (by rw [Fin.ext h])
          exact ⟨CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega),
            CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩
    · -- `n = 2k + 1`: the spine `P₂ₖ₊₂` has even order and matches itself perfectly.
      rw [show (2 * k + 1 + 2) / 2 = Fintype.card (Fin (k + 1)) by simp; omega]
      refine CGraph.card_le_matchNum
        (fun j : Fin (k + 1) ↦ Sum.inr ⟨2 * j, by have := j.isLt; omega⟩)
        (fun j : Fin (k + 1) ↦ Sum.inr ⟨2 * j + 1, by have := j.isLt; omega⟩)
        (fun _ ↦ fan_spine_adj _ _ _ _ rfl) ?_
      intro i j hij
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (by rw [Fin.ext h])
      exact ⟨CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega),
        CGraph.inr_mk_ne_inr_mk _ _ (by omega), CGraph.inr_mk_ne_inr_mk _ _ (by omega)⟩

/-- **A book with at least two pages has matching number two**: one spine vertex pairs
with one page vertex and the other spine vertex with another. -/
theorem matchNum_book (n : ℕ) : (book (n + 2)).matchNum = 2 := by
  refine le_antisymm ?_ ?_
  · calc (book (n + 2)).matchNum ≤ (book (n + 2)).coverNum := matchNum_le_coverNum _
      _ = 2 := by
          rw [book_eq_join]
          simp [coverNum_join, coverNum_complete, coverNum_empty, V_complete, V_empty]
          omega
  · rw [book_eq_join, IsoGraph.complete, IsoGraph.empty, join_mk, matchNum_mk]
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun i : Fin 2 ↦ Sum.inl i)
      (fun i : Fin 2 ↦ Sum.inr ⟨i.val, by have := i.isLt; omega⟩) ?_ ?_)
    · intro i
      exact CGraph.join_adj_inl_inr _ _ _ _
    · intro i j hij
      refine ⟨fun h ↦ hij (Sum.inl.inj h), fun h ↦ Sum.inl_ne_inr h,
        fun h ↦ Sum.inl_ne_inr h.symm, ?_⟩
      exact CGraph.inr_mk_ne_inr_mk _ _ (fun h ↦ hij (Fin.ext h))

/-- **The Johnson graph `J(2m+3, 2)` needs `2m + 3` colours**: its chromatic number is the edge
chromatic number of the complete graph `K_{2m+3}`, which is class two. -/
@[simp] theorem chromNum_johnson_two_odd (m : ℕ) :
    (johnson (2 * m + 3) 2).chromNum = 2 * m + 3 := by
  rw [chromNum_johnson_two, edgeChromNum_complete_odd]

/-- **The triangular graph `T(2m+3)` needs `2m + 3` colours.** -/
@[simp] theorem chromNum_triangular_odd (m : ℕ) :
    (triangular (2 * m + 3)).chromNum = 2 * m + 3 := by
  rw [← lineGraph_complete_eq_triangular, lineGraph_complete, chromNum_johnson_two_odd]

/-- **The Kneser graph `K(2m+3, 2)` has clique cover number `2m + 3`**, its complement being the
triangular graph. -/
@[simp] theorem cliqueCoverNum_kneser_two_odd (m : ℕ) :
    (kneser (2 * m + 3) 2).cliqueCoverNum = 2 * m + 3 := by
  rw [cliqueCoverNum_eq, ← triangular_eq_compl_kneser, chromNum_triangular_odd]

/-- **The triangular graph `T(n)` has clique number `n - 1`** for `n ≥ 4`: the largest clique is
the star of all pairs through a fixed point. -/
@[simp] theorem cliqueNum_triangular (n : ℕ) : (triangular (n + 4)).cliqueNum = n + 3 := by
  rw [← lineGraph_complete_eq_triangular,
    cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_complete]; omega), maxDeg_complete]
  omega

/-- **The Johnson graph `J(n, 2)` has clique number `n - 1`** for `n ≥ 4`. -/
@[simp] theorem cliqueNum_johnson_two (n : ℕ) : (johnson (n + 4) 2).cliqueNum = n + 3 := by
  rw [← lineGraph_complete, cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_complete]; omega),
    maxDeg_complete]
  omega

/-- **Erdős--Ko--Rado for pairs**: the largest intersecting family of pairs from `n ≥ 4` points is
a star, of size `n - 1`, so the Kneser graph `K(n, 2)` has independence number `n - 1`. -/
@[simp] theorem indepNum_kneser_two (n : ℕ) : (kneser (n + 4) 2).indepNum = n + 3 := by
  rw [← cliqueNum_compl, ← triangular_eq_compl_kneser, cliqueNum_triangular]

/-- **The line graph of the Petersen graph has clique number three.** -/
@[simp] theorem cliqueNum_lineGraph_petersen : (lineGraph petersen).cliqueNum = 3 := by
  rw [cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_petersen]), maxDeg_petersen]

/-- **The line graph of a hypercube `Q_{n+3}` has clique number `n + 3`.** -/
@[simp] theorem cliqueNum_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 3))).cliqueNum = n + 3 := by
  rw [cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_hypercube]; omega), maxDeg_hypercube]

/-- **A Paley graph on at least nine points is not bipartite.** -/
theorem not_isBipartite_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    ¬ IsBipartite (paley q) :=
  not_isBipartite_of_girth_eq_three (girth_paley q hq hq9)

/-- **A complete multipartite graph with at least three parts has a cycle.** -/
@[simp] theorem not_isAcyclic_completeMultipartite_replicate (m d : ℕ) :
    ¬ IsAcyclic (completeMultipartite (List.replicate (m + 3) (d + 1))) :=
  not_isAcyclic_of_girth_pos (by rw [girth_completeMultipartite_replicate]; omega)

/-- **The Kneser graph `K(n, 2)` has vertex cover number `C(n, 2) - (n - 1)`**, by Gallai's
identity and the Erdős--Ko--Rado value of its independence number. -/
@[simp] theorem coverNum_kneser_two (n : ℕ) :
    (kneser (n + 4) 2).coverNum = (n + 4).choose 2 - (n + 3) := by
  have h := coverNum_add_indepNum (kneser (n + 4) 2)
  rw [indepNum_kneser_two, V_kneser] at h
  omega

/-- **The triangular graph `T(n)` needs at least `n - 1` colours**, its clique number. -/
theorem le_chromNum_triangular (n : ℕ) : n + 3 ≤ (triangular (n + 4)).chromNum := by
  rw [← cliqueNum_triangular n]
  exact cliqueNum_le_chromNum _

/-- **The Johnson graph `J(n, 2)` needs at least `n - 1` colours.** -/
theorem le_chromNum_johnson_two (n : ℕ) : n + 3 ≤ (johnson (n + 4) 2).chromNum := by
  rw [← cliqueNum_johnson_two n]
  exact cliqueNum_le_chromNum _

end IsoGraph
