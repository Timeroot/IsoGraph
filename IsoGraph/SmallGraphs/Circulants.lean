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

/-- Two `k`-sets differing in `d` elements are at distance `d`, and `d ≤ min k (n - k)`. -/
theorem diameter_johnson {n k : ℕ} (hk : k ≤ n) :
    (johnson n k).diameter = min k (n - k) := by
  -- johnson here is IsoGraph.johnson = ⟦CGraph.johnson n k⟧
  -- We need to work with CGraph.johnson n k
  have : (johnson n k : IsoGraph) = Quotient.mk _ (CGraph.johnson n k) := rfl
  rw [this, diameter_mk]
  simp [CGraph.diameter, SimpleGraph.diam]
  set G := (CGraph.johnson n k).toSimple
  -- Adjacency in G
  have adj_char : ∀ s t : (CGraph.johnson n k).V, G.Adj s t ↔ s ≠ t ∧ (s.val ∩ t.val).card = k - 1
    := by
    simp [G, CGraph.johnson_adj]
  -- Key: edist(s, t) = k - |s ∩ t|.card
  -- Step 1: Upper bound on edist via swap path
  have edist_le_k_inter : ∀ s t : (CGraph.johnson n k).V, G.edist s t ≤ (k - (s.val ∩ t.val).card :
    ℕ∞) := by
    -- Bound edist by |s \ t| = k - |s ∩ t|
    -- Induction: if s = t, edist = 0. If s ≠ t, swap one element to get closer.
    have key : ∀ d : ℕ, ∀ s t : (CGraph.johnson n k).V, k - (s.val ∩ t.val).card = d → G.edist s t ≤
      (d : ℕ∞) := by
      intro d
      induction d with
      | zero =>
        intro s t h0
        have hcard_le : (s.val ∩ t.val).card ≤ k := by
          exact le_trans (Finset.card_le_card Finset.inter_subset_left) s.property.le
        have hcard_inter : (s.val ∩ t.val).card = k := by omega
        have hsub_s : s.val ⊆ t.val := by
          have hel : (s.val ∩ t.val) = s.val :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left
              (by show (s.val).card ≤ (s.val ∩ t.val).card; rw [hcard_inter]; exact s.property.le)
          exact Finset.inter_eq_left.mp hel
        have hsub_t : t.val ⊆ s.val := by
          have hcard_inter' : (t.val ∩ s.val).card = k := by
            rw [Finset.inter_comm]
            exact hcard_inter
          have hel : (t.val ∩ s.val) = t.val :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left
              (by show (t.val).card ≤ (t.val ∩ s.val).card; rw [hcard_inter']; exact t.property.le)
          exact Finset.inter_eq_left.mp hel
        have : s.val = t.val := Finset.Subset.antisymm hsub_s hsub_t
        simp [Subtype.ext this, SimpleGraph.edist_self]
      | succ d ih =>
        intro s t hd
        have hcard_inter : (s.val ∩ t.val).card = k - (d + 1) := by omega
        have hcard_st : (s.val \ t.val).card = d + 1 := by
          rw [Finset.card_sdiff, s.property, Finset.inter_comm, hcard_inter]
          omega
        have hcard_ts : (t.val \ s.val).card = d + 1 := by
          rw [Finset.card_sdiff, t.property, hcard_inter]
          omega
        have hk1 : 1 ≤ k := by omega
        obtain ⟨a, ha_s, ha_t⟩ : ∃ a, a ∈ s.val ∧ a ∉ t.val := by
          obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (s.val \ t.val).card)
          exact ⟨a, Finset.mem_sdiff.mp ha |>.1, Finset.mem_sdiff.mp ha |>.2⟩
        obtain ⟨b, hb_t, hb_s⟩ : ∃ b, b ∈ t.val ∧ b ∉ s.val := by
          obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (t.val \ s.val).card)
          exact ⟨b, Finset.mem_sdiff.mp hb |>.1, Finset.mem_sdiff.mp hb |>.2⟩
        let s'_val : Finset (Fin n) := (s.val \ {a}) ∪ {b}
        have hs'_card : s'_val.card = k := by
          have hdisj : Disjoint (s.val \ {a}) {b} := by
            rw [Finset.disjoint_singleton_right]
            exact fun h => hb_s (Finset.mem_sdiff.mp h |>.1)
          have hcard_sa : (s.val ∩ {a}).card = 1 := by
            rw [Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr ha_s)]
            exact Finset.card_singleton a
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff]
          rw
            [show ({a} ∩ s.val).card = (s.val ∩ {a}).card by rw [Finset.inter_comm],
              hcard_sa, Finset.card_singleton, s.property]
          omega
        let s' : (CGraph.johnson n k).V := ⟨s'_val, hs'_card⟩
        have hab : a ≠ b := by intro h; exact ha_t (h ▸ hb_t)
        have ha_not_in_s' : a ∉ s'_val := by
          simp [s'_val, Finset.mem_sdiff, Finset.mem_singleton]
          tauto
        have hne : s ≠ s' := by
          intro heq
          apply ha_not_in_s'
          have heq2 : s.val = s'_val := Subtype.ext_iff.mp heq
          rw [← heq2]
          exact ha_s
        have hinter_ss' : (s.val ∩ s'_val).card = k - 1 := by
          have hex : s.val ∩ s'_val = s.val \ {a} := by
            ext x
            simp [s'_val, Finset.mem_sdiff, Finset.mem_singleton]
            by_cases hx : x = a
            · subst hx; simp [hab]
            · simp [hx]; exact fun _ => Or.inr ‹_›
          have hcard_sa : (s.val ∩ {a}).card = 1 := by
            rw [Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr ha_s)]
            exact Finset.card_singleton a
          rw [hex, Finset.card_sdiff]
          rw
            [show ({a} ∩ s.val).card = (s.val ∩ {a}).card by rw [Finset.inter_comm],
              hcard_sa, s.property]
        have hadj : G.Adj s s' := by
          rw [adj_char]
          exact ⟨hne, hinter_ss'⟩
        have hinter_s't : (s'_val ∩ t.val).card = (s.val ∩ t.val).card + 1 := by
          have hex : s'_val ∩ t.val = (s.val ∩ t.val) ∪ {b} := by
            ext x
            simp [s'_val, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_inter]
            by_cases hx : x = b
            · subst hx; simp [hb_t]
            · simp [hx]
              exact fun hxt _ hxa => ha_t (hxa ▸ hxt)
          rw [hex]
          have hdisj2 : Disjoint (s.val ∩ t.val) {b} := by
            rw [Finset.disjoint_singleton_right]
            intro h; exact hb_s (Finset.mem_of_mem_inter_left h)
          rw [Finset.card_union_of_disjoint hdisj2, Finset.card_singleton]
        have hid : k - (s'_val ∩ t.val).card = d := by
          rw [hinter_s't, hcard_inter]
          omega
        have hedist_s't : G.edist s' t ≤ ↑d := ih s' t hid
        have hedist_ss' : G.edist s s' ≤ 1 := by
          let hwalk : G.Walk s s' := SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.nil : G.Walk s'
            s')
          have h1 : G.edist s s' ≤ ↑hwalk.length := SimpleGraph.Walk.edist_le hwalk
          simp [hwalk] at h1
          exact h1
        have htri : G.edist s t ≤ G.edist s s' + G.edist s' t :=
          @SimpleGraph.edist_triangle _ G _ _ _
        calc G.edist s t
            ≤ G.edist s s' + G.edist s' t := htri
          _ ≤ (1 : ℕ∞) + ↑d := add_le_add hedist_ss' hedist_s't
          _ = ↑(d + 1) := by push_cast; ring
    intro s t
    exact key _ _ _ rfl
  -- Step 2: Lower bound on edist via potential
  -- Goal: (k : ℕ∞) - ↑|s∩t|.card ≤ edist s t
  have inter_le_k_sub_edist : ∀ s t : (CGraph.johnson n k).V, (k : ℕ∞) - ↑(s.val ∩ t.val).card ≤
    G.edist s t := by
    intro s t
    -- Potential φ(u) = |u \ t|.card. For adjacent u,v, φ(u) ≤ φ(v) + 1.
    -- Hence for any walk of length L from s to t: φ(s) ≤ L.
    -- So φ(s) ≤ edist s t = sInf of walk lengths.
    set phi : (CGraph.johnson n k).V → ℕ := fun u => (u.val \ t.val).card
    have card_uv : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (u.val \ v.val).card = 1 := by
      intro u v huv
      have huv' := adj_char u v |>.mp huv
      have h1 : (u.val ∩ v.val).card = k - 1 := huv'.2
      by_cases hk0 : k = 0
      · exfalso; apply huv'.1
        have hu : u.val = ∅ := by
          have := Finset.card_eq_zero.mp (by rw [u.property, hk0])
          exact this
        have hv : v.val = ∅ := by
          have := Finset.card_eq_zero.mp (by rw [v.property, hk0])
          exact this
        exact Subtype.ext (by simp [‹u.val = ∅›, ‹v.val = ∅›])
      · have h2 : (u.val \ v.val).card = k - (k - 1) := by
          rw [Finset.card_sdiff, u.property, ← h1, Finset.inter_comm]
        omega
    have card_vu : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (v.val \ u.val).card = 1 := by
      intro u v huv
      have huv2 : G.Adj v u := by
        rw [adj_char] at huv ⊢
        exact ⟨huv.1.symm, by rw [Finset.inter_comm]; exact huv.2⟩
      exact card_uv v u huv2
    have phi_adj : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (phi u : ℕ∞) ≤ (phi v : ℕ∞) + 1 := by
      intro u v huv
      -- |u\t| = |(u\v) \ t| + |(u∩v)\t|  (disjoint union)
      -- |v\t| = |(v\u) \ t| + |(v∩u)\t| = |(v\u) \ t| + |(u∩v)\t|
      -- So |u\t| ≤ |(u\v)\t| + |(u∩v)\t| ≤ 1 + |(u∩v)\t| ≤ |v\t| + 1
      have hle : (u.val \ t.val).card ≤ (v.val \ t.val).card + 1 := by
        have hunion : (u.val \ t.val) ⊆ (v.val \ t.val) ∪ (u.val \ v.val) := by
          intro x hx
          simp [Finset.mem_sdiff] at hx ⊢
          by_cases hxv : x ∈ v.val
          · exact Or.inl ⟨hxv, hx.2⟩
          · exact Or.inr ⟨hx.1, hxv⟩
        have hcard_union : (u.val \ t.val).card ≤ (v.val \ t.val).card + (u.val \ v.val).card := by
          exact Finset.card_le_card hunion |> (fun h => le_trans h (Finset.card_union_le _ _))
        linarith [card_uv u v huv]
      exact mod_cast hle
    -- Generalize over target
    have phi_walk_le_gen : ∀ (u v : (CGraph.johnson n k).V) (p : G.Walk u v), (phi u : ℕ∞) ≤ (phi v
      : ℕ∞) + ↑p.length := by
      intro u v p
      induction p with
      | nil => simp [phi]
      | cons h p' ih =>
        rename_i u1 u2 u3
        have step := phi_adj u1 u2 h
        have hlen : (SimpleGraph.Walk.cons h p').length = p'.length + 1 := by
          rfl
        rw [hlen]
        have hphi32 : (phi u2 : ℕ∞) ≤ (phi u3 : ℕ∞) + ↑p'.length := by
          rw [← ENat.coe_add]; exact_mod_cast ih
        have heq : (↑(p'.length + 1) : ℕ∞) = ↑p'.length + 1 := by
          rw [ENat.coe_add, ENat.coe_one]
        rw [heq]
        calc (phi u1 : ℕ∞) ≤ (phi u2 : ℕ∞) + 1 := step
          _ ≤ ((phi u3 : ℕ∞) + ↑p'.length) + 1 := by
            have h2 := add_le_add_left hphi32 1
            rw [add_comm] at h2 ⊢; exact h2
          _ = (phi u3 : ℕ∞) + (↑p'.length + 1) := by rw [add_assoc]
    have phi_walk_le : ∀ (u : (CGraph.johnson n k).V) (p : G.Walk u t), (phi u : ℕ∞) ≤ ↑p.length :=
      by
      intro u p
      have := phi_walk_le_gen u t p
      simp [phi] at this
      exact_mod_cast this
    have hphi_s : phi s = k - (s.val ∩ t.val).card := by
      simp only [phi]
      rw [Finset.card_sdiff, s.property, Finset.inter_comm]
    have hc_le_k : (s.val ∩ t.val).card ≤ k :=
        le_trans (Finset.card_le_card Finset.inter_subset_left) s.property.le
    have hcast : ((k - (s.val ∩ t.val).card : ℕ) : ℕ∞) = (k : ℕ∞) - ↑(s.val ∩ t.val).card := by
      set c := (s.val ∩ t.val).card
      have hsum : (k : ℕ∞) = ↑(k - c) + ↑c := by
        calc (k : ℕ∞) = ↑((k - c) + c) := by rw [Nat.sub_add_cancel hc_le_k]
        _ = ↑(k - c) + ↑c := ENat.coe_add _ _
      rw [hsum]
      have key : ∀ (a b : ℕ), ((a : ℕ∞) + (b : ℕ∞)) - (b : ℕ∞) = (a : ℕ∞) := by
        intro a b
        -- In ℕ∞ = WithTop ℕ, coe commutes with + and - (truncated)
        have h1 : ((a : ℕ∞) + (b : ℕ∞) : ℕ∞) = (↑(a + b) : ℕ∞) := by
          rw [← ENat.coe_add]
        have coe_tsub : ∀ (x y : ℕ), y ≤ x → ((x : ℕ∞) - (y : ℕ∞) : ℕ∞) = (↑(x - y) : ℕ∞) := by
          intro x y hxy
          rfl
        have h2 : ((a : ℕ∞) + (b : ℕ∞) - (b : ℕ∞) : ℕ∞) = (a : ℕ∞) := by
          rw [← ENat.coe_add, coe_tsub (a + b) b (by omega), Nat.add_sub_cancel_right]
        exact h2
      exact (key _ _).symm
    rw [← hcast, ← hphi_s]
    rw [SimpleGraph.edist_eq_sInf]
    apply le_sInf
    rintro _ ⟨w, rfl⟩
    exact phi_walk_le _ w
  -- Step 3: edist(s,t) = k - |s∩t|.card (in ℕ∞)
  have edist_eq : ∀ s t : (CGraph.johnson n k).V, G.edist s t = (k : ℕ∞) - ↑(s.val ∩ t.val).card :=
    by
    intro s t
    exact le_antisymm (edist_le_k_inter s t) (inter_le_k_sub_edist s t)
  -- Step 4: ediam = max_{s,t} (k - |s∩t|.card)
  -- Helper: rewrite ℕ∞ subtraction
  have hsub_nk : (n : ℕ∞) - ↑k = ↑(n - k) := by rw [ENat.coe_sub]
  -- Upper bound on edist
  have upper : ∀ s t : (CGraph.johnson n k).V, G.edist s t ≤ (min (↑k) (↑(n - k) : ℕ∞)) := by
    intro s t
    rw [edist_eq s t]
    apply le_min
    · rw [← ENat.coe_sub]
      exact Nat.cast_le.mpr (Nat.sub_le _ _)
    · have hunion : (s.val ∪ t.val).card + (s.val ∩ t.val).card = 2 * k := by
        rw [Finset.card_union_add_card_inter, s.property, t.property]; ring
      have hunion_le_n : (s.val ∪ t.val).card ≤ n := by
        exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
      have hcard_ge : (s.val ∩ t.val).card ≥ 2 * k - n := by omega
      have hle : k - (s.val ∩ t.val).card ≤ n - k := by omega
      rw [ENat.coe_sub]
      exact Nat.cast_le.mpr hle
  -- Lower bound: exhibit s,t with edist = min (↑k) (↑(n-k))
  have edist_le_ediam_aux : min (↑k) (↑(n - k) : ℕ∞) ≤ G.ediam := by
    by_cases hk2 : 2 * k ≤ n
    · -- Disjoint s, t: edist = k = min
      let s_val : Finset (Fin n) := Finset.image (fun i : Fin k => Fin.castLE hk i) (Finset.univ :
        Finset (Fin k))
      let t_val : Finset (Fin n) := Finset.image (fun i : Fin k => ⟨(i : ℕ) + k, by omega⟩ : Fin k →
        Fin n) (Finset.univ : Finset (Fin k))
      have hs_card : s_val.card = k := by
        rw [Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
        simp
      have ht_card : t_val.card = k := by
        rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext
          (by simp [Fin.ext_iff] at h; omega))]
        simp
      let s : (CGraph.johnson n k).V := ⟨s_val, hs_card⟩
      let t : (CGraph.johnson n k).V := ⟨t_val, ht_card⟩
      have hint_empty : s_val ∩ t_val = ∅ := by
        have : ∀ x, x ∉ s_val ∩ t_val := by
          intro x hx
          simp [s_val, t_val, Finset.mem_inter, Finset.mem_image] at hx
          obtain ⟨i, hi⟩ := hx.1
          obtain ⟨j, hj⟩ := hx.2
          simp [Fin.ext_iff] at hi hj
          omega
        exact Finset.not_nonempty_iff_eq_empty.mp (by intro h; obtain ⟨x, hx⟩ := h; exact this x hx)
      have hedist : G.edist s t = (k : ℕ∞) := by
        rw [edist_eq s t, hint_empty, Finset.card_empty, Nat.cast_zero]
        simp
      have hmin : min (↑k) (↑(n - k) : ℕ∞) = (k : ℕ∞) := by
        rw [min_eq_left]
        exact_mod_cast Nat.le_sub_of_add_le (by omega)
      rw [hmin]
      exact hedist.symm ▸ SimpleGraph.edist_le_ediam
    · -- 2k > n: min = n-k
      have h2kn : n < 2 * k := lt_of_not_ge hk2
      have hnk_lt_k : n - k < k := by omega
      let s_val : Finset (Fin n) := Finset.image (fun i : Fin k => Fin.castLE hk i) (Finset.univ :
        Finset (Fin k))
      let t_val : Finset (Fin n) := Finset.image (fun i : Fin k => ⟨(i : ℕ) + (n - k), by omega⟩ :
        Fin k → Fin n) (Finset.univ : Finset (Fin k))
      have hs_card : s_val.card = k := by
        rw [Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
        simp
      have ht_card : t_val.card = k := by
        rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext
          (by simp [Fin.ext_iff] at h; omega))]
        simp
      let s : (CGraph.johnson n k).V := ⟨s_val, hs_card⟩
      let t : (CGraph.johnson n k).V := ⟨t_val, ht_card⟩
      have hint_card : (s_val ∩ t_val).card = 2 * k - n := by
        -- s_val = image of Fin.castLE hk over Fin k, i.e. {0,...,k-1} in Fin n
        -- t_val = image of shift by (n-k), i.e. {n-k,...,n-1} in Fin n
        -- Their intersection = elements of Fin n with value in [n-k, k), size = 2k-n
        -- This set is in bijection with Fin (2*k-n) via i ↦ ⟨n-k + i, by omega⟩
        have hinj : Function.Injective (fun (i : Fin (2 * k - n)) =>
          ⟨(n - k) + i.val, by omega⟩ : Fin (2 * k - n) → Fin n) := by
          intro i j h
          simp [Fin.ext_iff] at h ⊢; exact h
        -- Key lemma: x ∈ s_val ↔ x.val < k, and x ∈ t_val ↔ n-k ≤ x.val
        have hs_mem : ∀ x : Fin n, x ∈ s_val ↔ x.val < k := by
          intro x
          simp only [s_val, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi⟩
            have : x.val = i.val := by
              have := congr_arg Fin.val hi; simp [Fin.castLE] at this; exact this.symm
            rw [this]; exact i.is_lt
          · intro hx
            exact ⟨⟨x.val, hx⟩, Fin.ext (by simp)⟩
        have ht_mem : ∀ x : Fin n, x ∈ t_val ↔ n - k ≤ x.val := by
          intro x
          simp only [t_val, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj⟩
            have hval : x.val = j.val + (n - k) := by
              have := congr_arg Fin.val hj; simp at this ⊢; exact
                this.symm
            rw [hval]; exact Nat.le_add_left _ _
          · intro hx
            exact ⟨⟨x.val - (n - k), by omega⟩, Fin.ext (by simp [Nat.sub_add_cancel hx])⟩
        -- Now: s_val ∩ t_val = {x : Fin n | n-k ≤ x.val ∧ x.val < k}
        -- This equals the image of Fin (2k-n) under i ↦ ⟨n-k + i, by omega⟩
        have hint_eq : s_val ∩ t_val = Finset.image (fun (i : Fin (2 * k - n)) =>
          ⟨(n - k) + i.val, by omega⟩ : Fin (2 * k - n) → Fin n) Finset.univ := by
          ext x
          simp [Finset.mem_inter, hs_mem, ht_mem, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · intro h
            have h1 : n - k ≤ x.val := by omega
            exact ⟨⟨x.val - (n - k), by omega⟩, Fin.ext (by simp [Nat.add_sub_of_le h1])⟩
          · rintro ⟨i, hi⟩
            subst hi
            have : (⟨n - k + i.val, by omega⟩ : Fin n).val = n - k + i.val := by simp
            rw [this]
            exact ⟨by omega, by omega⟩
        rw [hint_eq, Finset.card_image_of_injective _ hinj, Finset.card_univ]
        simp
      have hedist : G.edist s t = (↑(n - k) : ℕ∞) := by
        rw [edist_eq s t, hint_card]
        show (↑k : ℕ∞) - ↑(2 * k - n) = ↑(n - k)
        haveI : 2 * k - n ≤ k := by omega
        rw [← ENat.coe_sub k (2 * k - n)]
        congr 1; omega
      have hmin : min (↑k) (↑(n - k) : ℕ∞) = (↑(n - k) : ℕ∞) := by
        rw [min_eq_right]
        exact_mod_cast Nat.sub_le_of_le_add (by omega)
      rw [hmin]
      exact hedist.symm ▸ SimpleGraph.edist_le_ediam
  have ediam_eq_nn : G.ediam = min (↑k) (↑(n - k) : ℕ∞) :=
    le_antisymm (SimpleGraph.ediam_le_of_edist_le upper) edist_le_ediam_aux
  -- Step 5: conclude
  rw [ediam_eq_nn]
  have hmin_coe : min (↑k) (↑(n - k) : ℕ∞) = ↑(min k (n - k)) := by
    by_cases h : k ≤ n - k
    · rw [min_eq_left (mod_cast h), min_eq_left (mod_cast h)]
    · rw [min_eq_right (mod_cast le_of_not_ge h), min_eq_right (mod_cast le_of_not_ge h)]
  rw [hmin_coe, ENat.toNat_coe]

/-- Johnson graphs are connected: swap the elements of two `k`-sets one at a time. -/
theorem isConnected_johnson {n k : ℕ} (hk : k ≤ n) : IsConnected (johnson n k) := by
  change IsConnected ⟦CGraph.johnson n k⟧
  rw [IsoGraph.isConnected_mk]
  -- Goal: (johnson n k).IsConnected, i.e., (johnson n k).toSimple.Connected
  unfold CGraph.IsConnected
  have hne : Nonempty (CGraph.johnson n k).V := by
    by_cases hkn : k = n
    · subst hkn
      exact ⟨⟨Finset.univ, by simp⟩⟩
    · exact ⟨⟨Finset.Iio ⟨k, lt_of_le_of_ne hk hkn⟩, by simp⟩⟩
  apply SimpleGraph.Connected.mk
  · -- Preconnected: any two vertices reachable
    let johnsonC : CGraph := CGraph.johnson n k
    have reachability : ∀ d : ℕ, ∀ (s t : Finset (Fin n)) (hs : s.card = k) (ht : t.card = k),
        (s \ t).card = d → johnsonC.toSimple.Reachable ⟨s, hs⟩ ⟨t, ht⟩ := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro s t hs ht hdval
        by_cases hst : s = t
        · exact hst ▸ SimpleGraph.Reachable.refl _
        · -- s ≠ t, so (s \ t) is nonempty
          have hd_pos : 0 < (s \ t).card := by
            by_contra h
            have h0 : (s \ t).card = 0 := by omega
            have hsub : s ⊆ t := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h0)
            exact hst (Finset.eq_of_subset_of_card_le hsub (by simp [hs, ht]))
          -- Pick a ∈ s \ t
          obtain ⟨a, has, hat⟩ : ∃ a ∈ s, a ∉ t := by
            obtain ⟨x, hx⟩ := Finset.card_pos.mp hd_pos
            exact ⟨x, Finset.mem_sdiff.mp hx |>.1, Finset.mem_sdiff.mp hx |>.2⟩
          -- Pick b ∈ t \ s
          have hne2 : (t \ s).Nonempty := by
            by_contra h
            have hempty : t \ s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
            have hsub2 : t ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp hempty
            have := Finset.eq_of_subset_of_card_le hsub2 (by simp [ht, hs])
            exact hst this.symm
          obtain ⟨b, hbt, hbs⟩ : ∃ b ∈ t, b ∉ s := by
            obtain ⟨x, hx⟩ := hne2
            exact ⟨x, Finset.mem_sdiff.mp hx |>.1, Finset.mem_sdiff.mp hx |>.2⟩
          -- Construct s'val = insert b (erase s a)
          let s'val : Finset (Fin n) := s.erase a ∪ {b}
          have hb_not_in_erase : b ∉ s.erase a := by intro h; exact hbs (Finset.mem_of_mem_erase h)
          have hs'card : s'val.card = k := by
            have hdisj : Disjoint (s.erase a) {b} := by
              rw [Finset.disjoint_singleton_right]
              exact hb_not_in_erase
            have := Finset.card_union_of_disjoint hdisj
            rw [this, Finset.card_erase_of_mem has, Finset.card_singleton, hs]
            have : 0 < k := hs ▸ Finset.card_pos.mpr ⟨a, has⟩
            omega
          let s' : johnsonC.V := ⟨s'val, hs'card⟩
          have hab : a ≠ b := by intro h; exact hbs (h.symm ▸ has)
          -- Show s' ≠ s (for adjacency)
          have hs'_ne_s : (⟨s, hs⟩ : johnsonC.V) ≠ s' := by
            intro h
            have hval : s = s'val := Subtype.ext_iff.mp h
            have : b ∈ s := by
              rw [hval]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            exact hbs this
          -- Show |s'val ∩ s| = k - 1
          have hinter : (s'val ∩ s).card = k - 1 := by
            have hessa : s'val ∩ s = s.erase a := by
              ext x
              simp [s'val]
              by_cases hx : x = a <;> by_cases hx2 : x = b <;> simp [hx, hx2, hab]
              tauto
            rw [hessa, Finset.card_erase_of_mem has, hs]
          -- Show s' is adjacent to s
          have hadj_adj : johnsonC.Adj ⟨s, hs⟩ s' := by
            show johnsonC.Adj ⟨s, hs⟩ s'
            simp only [johnsonC, CGraph.johnson_adj]
            have hne' : (⟨s, hs⟩ : johnsonC.V) ≠ s' := hs'_ne_s
            have hcard' : (s ∩ s'.val).card = k - 1 := by rw [Finset.inter_comm]; exact hinter
            simp [hne', hcard']
          -- Show (s'val \ t).card < d
          have hcard_lt : (s'val \ t).card < d := by
            have hsub : s'val \ t ⊆ (s \ t) \ {a} := by
              intro x hx
              simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx ⊢
              have hx1 : x ∈ s := by
                dsimp [s'val] at hx
                rcases Finset.mem_union.mp hx.1 with hx1 | hx1
                · exact Finset.mem_of_mem_erase hx1
                · have hxb : x = b := Finset.mem_singleton.mp hx1
                  exact False.elim ((hxb ▸ hx.2) hbt)
              have hxa : x ≠ a := by
                by_contra hx_eq_a
                rw [hx_eq_a] at hx
                have : a ∈ s'val := hx.1
                simp [s'val, Finset.mem_erase] at this
                exact hab this
              exact ⟨⟨hx1, hx.2⟩, hxa⟩
            have hcard_erase : ((s \ t) \ {a}).card = (s \ t).card - 1 := by
              have ha_mem : a ∈ s \ t := Finset.mem_sdiff.mpr ⟨has, hat⟩
              rw [show (s \ t) \ {a} = (s \ t).erase a from by
                ext x; simp [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
                tauto]
              exact Finset.card_erase_of_mem ha_mem
            have : (s'val \ t).card ≤ (s \ t).card - 1 := by
              exact le_trans (Finset.card_le_card hsub) hcard_erase.le
            omega
          -- Use IH for s', t
          have hired : johnsonC.toSimple.Reachable s' ⟨t, ht⟩ :=
            ih _ hcard_lt _ _ hs'card ht rfl
          -- Compose: s → s' → t
          have hreach_edge : johnsonC.toSimple.Reachable ⟨s, hs⟩ s' :=
            (SimpleGraph.Adj.reachable
              (show johnsonC.toSimple.Adj _ _ from by
                simpa [johnsonC, CGraph.toSimple_adj] using hadj_adj))
          exact hreach_edge.trans hired
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact reachability _ _ _ hu hv rfl

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
  apply List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (Multiset.pairwise_sort _ (fun x1 x2 => x1 ≤ x2))
    (by simp [List.pairwise_cons, List.pairwise_replicate, List.mem_replicate])
    (by
      have hms : ∀ (m : Multiset ℕ), Multiset.ofList (Multiset.sort m (· ≤ ·)) = m := by
        intro m; exact Multiset.sort_eq _ _
      have htarget : (2 ::ₘ 2 ::ₘ 2 ::ₘ 2 ::ₘ Multiset.replicate (2 * n) 3 : Multiset ℕ) =
          ((2 :: 2 :: 2 :: 2 :: List.replicate (2 * n) 3) : Multiset ℕ) := by rfl
      exact Multiset.coe_eq_coe.mp (hms _ ▸ htarget))

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
  -- goal: (CGraph.johnson (n + 2) 2).domNum = (n + 2) / 2
  apply le_antisymm
  · -- Upper bound: domNum ≤ indepNum ≤ (n+2)/2
    have h1 : (CGraph.johnson (n + 2) (2 : ℕ)).domNum ≤ (CGraph.johnson (n + 2) (2 : ℕ)).indepNum :=
      CGraph.domNum_le_indepNum _
    have h2 : (CGraph.johnson (n + 2) (2 : ℕ)).indepNum ≤ (n + 2) / 2 := by
      unfold CGraph.indepNum
      simp only [SimpleGraph.indepNum]
      apply csSup_le
      · -- nonempty
        exact ⟨0, ⟨∅, SimpleGraph.IsNIndepSet.mk (by simp [SimpleGraph.IsIndepSet]) rfl⟩⟩
      · -- upper bound
        intro b hb
        obtain ⟨S, hS_indep, rfl⟩ := hb
        -- Each pair of distinct vertices in S is disjoint (as Finsets)
        have hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint u.1 v.1 := by
          intro u hu v hv huv
          by_contra hndisj
          have hadj : (CGraph.johnson (n + 2) (2 : ℕ)).Adj u v := by
            simp [CGraph.johnson_adj, huv, beq_iff_eq]
            have hnd := Finset.not_disjoint_iff.mp hndisj
            exact CGraph.card_inter_eq_one_of_ne u v huv
              (by
                intro h
                obtain ⟨x, hxu, hxv⟩ := hnd
                exact absurd (h ▸ Finset.mem_inter_of_mem hxu hxv) (by simp))
          exact absurd hadj (hS_indep hu hv huv)
        have hcard2 : ∀ u ∈ S, u.1.card = 2 := fun u hu => u.2
        have hcard_biUnion : (S.biUnion (fun u => u.1)).card = ∑ u ∈ S, u.1.card :=
          Finset.card_biUnion (fun u hu v hv huv => hdisj u hu v hv huv)
        have hcard_sum : ∑ u ∈ S, u.1.card = 2 * S.card := by
          rw [Finset.sum_congr rfl hcard2]
          simp [Finset.sum_const, mul_comm]
        have hle : 2 * S.card ≤ (n + 2) := by
          have : (S.biUnion (fun u => u.1)).card = 2 * S.card := by rw [hcard_biUnion, hcard_sum]
          have hsub : S.biUnion (fun u => u.1) ⊆ Finset.univ := Finset.subset_univ _
          have := Finset.card_le_card hsub
          simp [Finset.card_univ, Fintype.card_fin] at this
          linarith
        omega
    omega
  · -- Lower bound
    have hlower : ∀ s : Finset (CGraph.johnson (n + 2) (2 : ℕ)).V,
        (CGraph.johnson (n + 2) (2 : ℕ)).IsDominatingSet s → (n + 2) / 2 ≤ s.card := by
      intro s hsdom
      by_contra hcard
      push_neg at hcard
      set covered := Finset.biUnion s (fun u => u.1) with hcovered_def
      have hcovered_size : covered.card ≤ 2 * s.card := by
        have : ∀ u ∈ s, u.1.card = 2 := fun u hu => u.2
        calc covered.card = (s.biUnion (fun u => u.1)).card := congr_arg Finset.card hcovered_def
          _ ≤ ∑ u ∈ s, u.1.card := Finset.card_biUnion_le
          _ = ∑ _ ∈ s, 2 := Finset.sum_congr rfl this
          _ = 2 * s.card := by simp [mul_comm]
      have h2le : 2 * s.card ≤ n := by omega
      have huncovered : (Finset.univ \ covered).card ≥ 2 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ Finset.univ \ covered, ∃ b ∈ Finset.univ \ covered, a ≠ b
        := by
        exact Finset.one_lt_card.mp huncovered
      let v : (CGraph.johnson (n + 2) (2 : ℕ)).V := ⟨{a, b}, Finset.card_pair hab⟩
      have hv_notin : v ∉ s := by
        intro hv
        have : a ∈ covered := hcovered_def ▸ Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_self _
          _⟩
        exact Finset.mem_sdiff.mp ha |>.2 this
      have ha_notin : ∀ u ∈ s, a ∉ u.1 := by
        intro u hu hua
        exact Finset.mem_sdiff.mp ha |>.2 (hcovered_def ▸ Finset.mem_biUnion.mpr ⟨u, hu, hua⟩)
      have hb_notin : ∀ u ∈ s, b ∉ u.1 := by
        intro u hu hub
        exact Finset.mem_sdiff.mp hb |>.2 (hcovered_def ▸ Finset.mem_biUnion.mpr ⟨u, hu, hub⟩)
      have hv_inter_empty : ∀ u ∈ s, (u.1 ∩ v.1) = ∅ := by
        intro u hu
        have hv1 : v.1 = {a, b} := rfl
        have : ∀ x, x ∈ u.1 ∩ v.1 → False := by
          intro x hx
          simp [hv1, Finset.mem_inter] at hx
          rcases hx.2 with rfl | rfl
          · exact ha_notin u hu hx.1
          · exact hb_notin u hu hx.1
        exact Finset.not_nonempty_iff_eq_empty.mp (by rintro ⟨x, hx⟩; exact this x hx)
      have huv_ne : ∀ u ∈ s, u ≠ v := by
        intro u hu huv_eq
        have := congrArg Subtype.val huv_eq
        simp [v] at this
        have ha_in_u : a ∈ u.1 := by rw [this]; simp
        exact Finset.mem_sdiff.mp ha |>.2 (hcovered_def ▸ Finset.mem_biUnion.mpr ⟨u, hu, ha_in_u⟩)
      have hv_not_adj : ∀ u ∈ s, ¬(CGraph.johnson (n + 2) (2 : ℕ)).Adj u v := by
        intro u hu
        simp [CGraph.johnson_adj, huv_ne u hu, hv_inter_empty u hu]
      have hv_not_dom : ¬(v ∈ s ∨ ∃ u ∈ s, (CGraph.johnson (n + 2) (2 : ℕ)).Adj u v) := by
        intro h
        rcases h with hv | ⟨u, hu, hadj⟩
        · exact hv_notin hv
        · exact absurd hadj (hv_not_adj u hu)
      exact hv_not_dom (hsdom v)
    apply le_csInf
    · exact ⟨Fintype.card _, ⟨Finset.univ, rfl, CGraph.isDominatingSet_univ _⟩⟩
    · intro a ⟨s, hs, hsdom⟩; rw [← hs]; exact hlower s hsdom

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
      push_neg at hall
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

/-- **A balanced complete multipartite graph with at least two parts has a near-perfect
matching.** -/
theorem matchNum_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 1))).matchNum
      = (m + 2) * (d + 1) / 2 := by
  apply le_antisymm
  · have h1 := two_mul_matchNum_le_V (completeMultipartite (List.replicate (m + 2) (d + 1)))
    rw [V_completeMultipartite, List.sum_replicate] at h1
    simp at h1
    omega
  · -- Number the vertices round robin: `j` sits in part `j % k`, slot `j / k`.  Consecutive
    -- numbers land in different parts, so the pairs `{2t, 2t + 1}` are disjoint edges.
    set k := m + 2 with hk
    set s := d + 1 with hs
    set H : CGraph := CGraph.completeMultipartite (List.replicate k s) with hH
    rw [show (completeMultipartite (List.replicate k s) : IsoGraph) = ⟦H⟧ from rfl, matchNum_mk]
    have hlen : (List.replicate k s).length = k := List.length_replicate
    have hget : ∀ (i : Fin k), (List.replicate k s).get ⟨i, by rw [hlen]; exact i.2⟩ = s := by
      intro i; simp [List.getElem_replicate]
    let vertex : Fin k → Fin s → H.V := fun i a =>
      ⟨⟨i, by rw [hlen]; exact i.2⟩, Fin.cast (hget i).symm a⟩
    have hadj : ∀ (i j : Fin k) (a b : Fin s), H.Adj (vertex i a) (vertex j b) ↔ i ≠ j := by
      intro i j a b
      simp [vertex, H, CGraph.completeMultipartite_adj]
      simp [Fin.ext_iff]
    let f : Fin (k * s) → H.V := fun ⟨j, hj⟩ =>
      vertex ⟨j % k, Nat.mod_lt _ (by omega : 0 < k)⟩ ⟨j / k, Nat.div_lt_of_lt_mul hj⟩
    have hf_fst_val : ∀ j : Fin (k * s), (f j).1.val = j.val % k := by
      intro j; simp [f, vertex]
    have hf_snd_val : ∀ j : Fin (k * s), (f j).2.val = j.val / k := by
      intro j; simp [f, vertex]
    have hf_inj : Function.Injective f := by
      intro j1 j2 hfeq
      have hmod : j1.val % k = j2.val % k := by
        have h1 := congr_arg (fun v : H.V => v.1.val) hfeq
        simp only [hf_fst_val] at h1
        exact h1
      have hdiv : j1.val / k = j2.val / k := by
        have h2 := congr_arg (fun v : H.V => v.2.val) hfeq
        simp only [hf_snd_val] at h2
        exact h2
      refine Fin.ext ?_
      have h1' := Nat.div_add_mod j1.val k
      have h2' := Nat.div_add_mod j2.val k
      rw [hmod, hdiv] at h1'
      linarith [h2']
    have hbound : ∀ t : Fin (k * s / 2), 2 * (t : ℕ) + 1 < k * s := by
      intro t
      have ht : (t : ℕ) < k * s / 2 := t.2
      have := Nat.div_add_mod (k * s) 2
      omega
    have hbound' : ∀ t : Fin (k * s / 2), 2 * (t : ℕ) < k * s := fun t ↦ by
      have := hbound t; omega
    refine le_trans (le_of_eq (by simp)) (CGraph.card_le_matchNum
      (fun t : Fin (k * s / 2) ↦ f ⟨2 * (t : ℕ), hbound' t⟩)
      (fun t : Fin (k * s / 2) ↦ f ⟨2 * (t : ℕ) + 1, hbound t⟩) ?_ ?_)
    · -- `2t` and `2t + 1` are different mod `k ≥ 2`, so they lie in different parts.
      have hpart : ∀ x y : Fin (k * s), x.val % k ≠ y.val % k → H.Adj (f x) (f y) := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hne
        simp only [f]
        rw [hadj]
        exact fun h ↦ hne (congrArg Fin.val h)
      intro t
      refine hpart ⟨2 * (t : ℕ), hbound' t⟩ ⟨2 * (t : ℕ) + 1, hbound t⟩ ?_
      dsimp only
      intro heq
      have := Nat.modEq_iff_dvd.mp (Nat.ModEq.symm heq)
      simp at this
      exact absurd (Int.le_of_dvd (by omega : (0 : ℤ) < 1) this) (by omega)
    · intro t t' htt'
      have hfval : ∀ x y : Fin (k * s), f x = f y → (x : ℕ) = (y : ℕ) :=
        fun x y he ↦ congrArg Fin.val (hf_inj he)
      have hne : ∀ (x y : ℕ) (hx : x < k * s) (hy : y < k * s), x ≠ y →
          f ⟨x, hx⟩ ≠ f ⟨y, hy⟩ :=
        fun x y hx hy hxy he ↦ hxy (hfval ⟨x, hx⟩ ⟨y, hy⟩ he)
      have ht : (t : ℕ) ≠ (t' : ℕ) := fun hval ↦ htt' (Fin.ext hval)
      exact ⟨hne _ _ (hbound' t) (hbound' t') (by omega),
        hne _ _ (hbound' t) (hbound t') (by omega),
        hne _ _ (hbound t) (hbound' t') (by omega),
        hne _ _ (hbound t) (hbound t') (by omega)⟩

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
