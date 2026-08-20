import IsoGraph.SmallGraphs.Equalities

/-!
# Order, size and degrees of the named graphs

Order, size and degrees of the named graphs and the parametrised families.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

@[simp] theorem E_path (n : ℕ) : (path (n + 1)).E = n := by
  unfold CGraph.E
  have h1 : (path (n + 1)).toSimple.edgeFinset.card = ((path (n + 1)).toSimple.edgeSet).ncard := by
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
  rw [h1, path_toSimple]
  -- Goal: (pathGraph (n+1)).edgeSet.ncard = n
  -- Use: edgeSet.ncard = edgeFinset.card, and compute edgeFinset.card for pathGraph
  haveI : DecidableRel (SimpleGraph.pathGraph (n + 1)).Adj :=
    fun i j => decidable_of_iff _ (SimpleGraph.pathGraph_adj).symm
  have h2 : (SimpleGraph.pathGraph (n + 1)).edgeSet.ncard =
    (SimpleGraph.pathGraph (n + 1)).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
  have htree : (SimpleGraph.pathGraph (n + 1)).IsTree := by
    exact {
      isConnected := SimpleGraph.pathGraph_connected n
      IsAcyclic := by
        have := isAcyclic_path (n + 1)
        simpa [CGraph.IsAcyclic, path_toSimple] using this
    }
  have h3 := SimpleGraph.IsTree.card_edgeFinset htree
  have h4 : (SimpleGraph.pathGraph (n + 1)).edgeFinset.card = n := by
    simp [Fintype.card_fin] at h3; omega
  exact h2.trans h4

/-! ### Bipartite and multipartite graphs -/

@[simp] theorem E_bipartite (m n : ℕ) : (bipartite m n).E = m * n := by
  let G := complete m ⊕g complete n
  have h1 := E_compl (G := G)
  have h2 := E_disjUnion (G := complete m) (H := complete n)
  have h3 := E_complete m
  have h4 := E_complete n
  rw [h3, h4] at h2
  rw [h2] at h1
  rw [card_disjUnion, card_complete, card_complete] at h1
  -- bipartite m n = Gᶜ
  have hbip : bipartite m n = Gᶜ := rfl
  rw [hbip]
  have hdiv (k : ℕ) : 2 ∣ k * (k - 1) := by
    rcases k with _ | _ | k <;> simp [Nat.mul_succ, parity_simps]
    exact even_iff_two_dvd.mp (by simp [parity_simps])
  have h2' : 2 * (Nat.choose (m + n) 2) = (m + n) * (m + n - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (hdiv _)]
  have h3' : 2 * (Nat.choose m 2) = m * (m - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (hdiv _)]
  have h4' : 2 * (Nat.choose n 2) = n * (n - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (hdiv _)]
  have h1' : 2 * Gᶜ.E + 2 * m.choose 2 + 2 * n.choose 2 = 2 * (m + n).choose 2 := by
    linarith
  rw [h2', h3', h4'] at h1'
  generalize Gᶜ.E = e at h1'
  clear h1 h2 h3 h4 h2' h3' h4' hbip hdiv G
  have hgoal : e = m * n := by
    rcases m with _ | m <;> rcases n with _ | n
    · simp at h1'; omega
    · simp at h1'; omega
    · simp at h1'; omega
    · simp [Nat.succ_mul] at h1'
      have h1'' : e + e + (m * m + m) + (n * n + n) = (m + 1 + (n + 1)) * (m + 1 + n) := h1'
      have : 2 * e = 2 * ((m + 1) * (n + 1)) := by
        ring_nf at h1''
        clear h1'
        have he : e = m * n + m + n + 1 := by omega
        rw [he]; ring
      omega
  exact hgoal

@[simp] theorem card_completeMultipartite (ds : List ℕ) :
    FinEnum.card (completeMultipartite ds).V = ds.sum := by
  simp only [completeMultipartite, card_compl, card_sigmaUnion, card_complete]
  rw [Finset.sum_univ_inst_eq _ (Fin.fintype ds.length), ← Fin.sum_ofFn, List.ofFn_get]

@[simp] theorem card_star (n : ℕ) : FinEnum.card (star n).V = 1 + n := by
  simp [star]

@[simp] theorem E_star (n : ℕ) : (star n).E = n := by
  simp [star, E_bipartite]

@[simp] theorem card_hypercube (n : ℕ) : FinEnum.card (hypercube n).V = 2 ^ n := by
  simp [hypercube, FinEnum.card_fun]

/-! ### Kneser, line and Mycielskian -/

@[simp] theorem card_kneser (n k : ℕ) : FinEnum.card (kneser n k).V = n.choose k := by
  show FinEnum.card {s : Finset (Fin n) // s.card = k} = n.choose k
  rw [FinEnum.card_eq_fintypeCard', Fintype.card_finset_len, Fintype.card_fin]

/-- The Petersen graph, as `K(5,2)`. -/
theorem card_petersen : FinEnum.card (kneser 5 2).V = 10 := by
  rw [card_kneser]; rfl

end

section
open Fintype
variable {m n : ℕ}

/-! ### Rook's graphs -/

theorem rook_adj (p q : (rook m n).V) :
    (rook m n).Adj p q
      = ((decide (p.1 = q.1) && decide (p.2 ≠ q.2)) ||
          (decide (p.1 ≠ q.1) && decide (p.2 = q.2))) := by
  simp [rook, cartesianProduct_adj]

theorem mem_nbrs_rook (p q : (rook m n).V) :
    q ∈ (rook m n).nbrs p ↔ (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.1 ≠ q.1 ∧ p.2 = q.2) := by
  rw [mem_nbrs, rook_adj]
  simp

/-- The neighbours of a square are the rest of its row together with the rest of its column. -/
theorem nbrs_rook (p : (rook m n).V) :
    (rook m n).nbrs p
      = (({p.1} : Finset (complete m).V) ×ˢ ({p.2} : Finset (complete n).V)ᶜ) ∪
          (({p.1} : Finset (complete m).V)ᶜ ×ˢ ({p.2} : Finset (complete n).V)) := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun q ↦ ?_
  obtain ⟨x, y⟩ := q
  rw [mem_nbrs_rook p (x, y)]
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_compl, Finset.mem_singleton]
  tauto

theorem card_nbrs_rook (p : (rook m n).V) :
    ((rook m n).nbrs p).card = (n - 1) + (m - 1) := by
  rw [nbrs_rook, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product]
  · simp [Finset.card_compl]
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_singleton] at h1 h2
    exact h2.1 h1.1

/-- Neighbours common to two squares in the same row: the rest of that row. -/
theorem nbrs_inter_rook_row (a : (complete m).V) (b d : (complete n).V) (h : b ≠ d) :
    (rook m n).nbrs (a, b) ∩ (rook m n).nbrs (a, d)
      = ({a} : Finset (complete m).V) ×ˢ ({b, d} : Finset (complete n).V)ᶜ := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun r ↦ ?_
  obtain ⟨x, y⟩ := r
  rw [Finset.mem_inter, mem_nbrs_rook (a, b) (x, y), mem_nbrs_rook (a, d) (x, y)]
  simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert,
    not_or]
  grind

/-- Neighbours common to two squares in the same column: the rest of that column. -/
theorem nbrs_inter_rook_col (a c : (complete m).V) (b : (complete n).V) (h : a ≠ c) :
    (rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, b)
      = ({a, c} : Finset (complete m).V)ᶜ ×ˢ ({b} : Finset (complete n).V) := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun r ↦ ?_
  obtain ⟨x, y⟩ := r
  rw [Finset.mem_inter, mem_nbrs_rook (a, b) (x, y), mem_nbrs_rook (c, b) (x, y)]
  simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert,
    not_or]
  grind

/-- Neighbours common to two squares in different rows *and* different columns: the two remaining
corners of the rectangle they span. -/
theorem nbrs_inter_rook_diag (a c : (complete m).V) (b d : (complete n).V) (h1 : a ≠ c)
    (h2 : b ≠ d) :
    (rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, d)
      = ({(a, d), (c, b)} : Finset ((complete m).V × (complete n).V)) := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun r ↦ ?_
  obtain ⟨x, y⟩ := r
  rw [Finset.mem_inter, mem_nbrs_rook (a, b) (x, y), mem_nbrs_rook (c, d) (x, y)]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  grind

theorem card_nbrs_inter_rook_row (a : (complete m).V) (b d : (complete n).V) (h : b ≠ d) :
    ((rook m n).nbrs (a, b) ∩ (rook m n).nbrs (a, d)).card = n - 2 := by
  rw [nbrs_inter_rook_row a b d h, Finset.card_product, Finset.card_compl,
    Finset.card_singleton, Finset.card_pair h, ← FinEnum.card_eq_fintypeCard, card_complete,
    one_mul]

theorem card_nbrs_inter_rook_col (a c : (complete m).V) (b : (complete n).V) (h : a ≠ c) :
    ((rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, b)).card = m - 2 := by
  rw [nbrs_inter_rook_col a c b h, Finset.card_product, Finset.card_compl,
    Finset.card_singleton, Finset.card_pair h, ← FinEnum.card_eq_fintypeCard, card_complete,
    mul_one]

theorem card_nbrs_inter_rook_diag (a c : (complete m).V) (b d : (complete n).V) (h1 : a ≠ c)
    (h2 : b ≠ d) : ((rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, d)).card = 2 := by
  rw [nbrs_inter_rook_diag a c b d h1 h2, Finset.card_pair fun hc ↦ h1 (congrArg Prod.fst hc)]

/-- For `k ≥ 1` the neighbours of `s` in `kneser n k` are exactly the vertices disjoint from `s`:
the `s ≠ t` conjunct in the definition is redundant, since a nonempty set meets itself. -/
theorem nbrs_kneser {k : ℕ} (hk : 1 ≤ k) (s : (kneser n k).V) :
    (kneser n k).nbrs s
      = Finset.univ.filter fun u : {u : Finset (Fin n) // u.card = k} ↦ u.1 ∩ s.1 = ∅ := by
  refine Finset.ext (α := {u : Finset (Fin n) // u.card = k}) fun u ↦ ?_
  rw [mem_nbrs]
  simp only [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Finset.inter_comm]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun hst ↦ ?_, h⟩⟩
  rw [← hst, Finset.inter_self] at h
  have hs := s.2
  rw [h, Finset.card_empty] at hs
  omega

/-- **Kneser graphs are regular of degree `(n - k).choose k`.** -/
theorem card_nbrs_kneser {k : ℕ} (hk : 1 ≤ k) (s : (kneser n k).V) :
    ((kneser n k).nbrs s).card = (n - k).choose k := by
  rw [nbrs_kneser hk, card_filter_kneser_disjoint, s.2]

theorem nbrs_inter_kneser {k : ℕ} (hk : 1 ≤ k) (s t : (kneser n k).V) :
    (kneser n k).nbrs s ∩ (kneser n k).nbrs t
      = Finset.univ.filter fun u : {u : Finset (Fin n) // u.card = k} ↦
          u.1 ∩ (s.1 ∪ t.1) = ∅ := by
  rw [nbrs_kneser hk, nbrs_kneser hk]
  refine Finset.ext (α := {u : Finset (Fin n) // u.card = k}) fun u ↦ ?_
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.inter_union_distrib_left, Finset.union_eq_empty]

/-- Two `k`-sets meeting in `i` points have `(n - (2k - i)).choose k` common neighbours: the
`k`-sets avoiding their union.  In particular adjacent — i.e. disjoint — vertices have
`(n - 2k).choose k`. -/
theorem card_nbrs_inter_kneser {k : ℕ} (hk : 1 ≤ k) (s t : (kneser n k).V) :
    ((kneser n k).nbrs s ∩ (kneser n k).nbrs t).card
      = (n - (2 * k - (s.1 ∩ t.1).card)).choose k := by
  rw [nbrs_inter_kneser hk, card_filter_kneser_disjoint]
  congr 2
  have := Finset.card_union_add_card_inter s.1 t.1
  rw [s.2, t.2] at this
  omega

/-- Two distinct `2`-subsets that are not disjoint meet in exactly one point. -/
theorem card_inter_eq_one_of_ne (s t : (kneser n 2).V) (hne : s ≠ t) (hd : s.1 ∩ t.1 ≠ ∅) :
    (s.1 ∩ t.1).card = 1 := by
  have hle : (s.1 ∩ t.1).card ≤ 2 := by
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := s.1) (s₂ := t.1))
    rwa [s.2] at this
  have hpos : 0 < (s.1 ∩ t.1).card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hd)
  rcases Nat.lt_or_ge (s.1 ∩ t.1).card 2 with h | h
  · omega
  · refine absurd (Subtype.ext ?_) hne
    have h1 : s.1 ∩ t.1 = s.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [s.2]; exact h)
    have h2 : s.1 ∩ t.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [t.2]; exact h)
    rw [← h1, h2]

/-! ### Complete bipartite graphs -/

theorem nbrs_bipartite_inl (m n : ℕ) (a : (complete m).V) :
    (bipartite m n).nbrs (Sum.inl a) = Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
  refine Finset.ext (α := (complete m).V ⊕ (complete n).V) fun x ↦ ?_
  cases x with
  | inl b => rw [mem_nbrs]; simp
  | inr b => rw [mem_nbrs]; simp

theorem nbrs_bipartite_inr (m n : ℕ) (b : (complete n).V) :
    (bipartite m n).nbrs (Sum.inr b) = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  refine Finset.ext (α := (complete m).V ⊕ (complete n).V) fun x ↦ ?_
  cases x with
  | inl c => rw [mem_nbrs]; simp
  | inr d => rw [mem_nbrs]; simp

/-! ### Complete multipartite graphs

`completeMultipartite ds` is the complement of a disjoint union of complete graphs, so two
vertices are adjacent exactly when they lie in different parts.  Once that is said, every count
the strong-regularity definition asks for is a sum of part sizes over a complement, and for equal
parts those sums are products. -/

/-- Two vertices of a complete multipartite graph are adjacent exactly when they lie in different
parts. -/
theorem completeMultipartite_adj (ds : List ℕ)
    (x y : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).Adj x y = decide (x.1 ≠ y.1) := by
  show ((sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i))ᶜ).Adj x y = _
  rw [compl_adj]
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  by_cases h : i = j
  · subst h
    rw [sigmaUnion_adj_mk, complete_adj]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  · rw [sigmaUnion_adj_ne _ _ _ _ _ h]
    have hne : (⟨i, a⟩ : Σ i : Fin ds.length, (complete (ds.get i)).V) ≠ ⟨j, b⟩ :=
      fun hh ↦ h (congrArg Sigma.fst hh)
    simp [hne, h]

/-- The neighbourhood of `x` is everything outside `x`'s own part. -/
theorem nbrs_completeMultipartite (ds : List ℕ)
    (x : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).nbrs x
      = Finset.univ.filter (fun z : Σ i : Fin ds.length, (complete (ds.get i)).V ↦
          z.1 ∉ ({x.1} : Finset (Fin ds.length))) := by
  refine Finset.ext (α := Σ i : Fin ds.length, (complete (ds.get i)).V) fun z ↦ ?_
  rw [mem_nbrs, completeMultipartite_adj]
  simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ne_comm

/-- Two vertices see in common everything outside both of their parts. -/
theorem nbrs_inter_completeMultipartite (ds : List ℕ)
    (x y : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).nbrs x ∩ (completeMultipartite ds).nbrs y
      = Finset.univ.filter (fun z : Σ i : Fin ds.length, (complete (ds.get i)).V ↦
          z.1 ∉ ({x.1, y.1} : Finset (Fin ds.length))) := by
  rw [nbrs_completeMultipartite, nbrs_completeMultipartite]
  refine Finset.ext (α := Σ i : Fin ds.length, (complete (ds.get i)).V) fun z ↦ ?_
  simp

end

section
open Fintype
variable {m n : ℕ}
variable {F : Type} [Field F] [FinEnum F]

@[simp] theorem card_paleyField : FinEnum.card (paleyField F).V = Fintype.card F :=
  FinEnum.card_eq_fintypeCard

theorem nbrs_paleyField (hq : Fintype.card F % 4 = 1) (x : F) :
    (paleyField F).nbrs x = Finset.univ.filter fun y : F ↦ quadraticChar F (y - x) = 1 := by
  refine Finset.ext (α := F) fun y ↦ ?_
  rw [mem_nbrs, paleyField_adj hq]
  simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]

theorem nbrs_inter_paleyField (hq : Fintype.card F % 4 = 1) (x y : F) :
    (paleyField F).nbrs x ∩ (paleyField F).nbrs y
      = Finset.univ.filter fun z : F ↦
          quadraticChar F (z - x) = 1 ∧ quadraticChar F (z - y) = 1 := by
  refine Finset.ext (α := F) fun z ↦ ?_
  rw [Finset.mem_inter, mem_nbrs, mem_nbrs, paleyField_adj hq, paleyField_adj hq]
  simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Translation by `x` matches the neighbours of `x` with the nonzero squares. -/
theorem card_nbrs_paleyField (hq : Fintype.card F % 4 = 1) (x : F) :
    ((paleyField F).nbrs x).card = (Fintype.card F - 1) / 2 := by
  have hb : (Finset.univ.filter fun y : F ↦ quadraticChar F (y - x) = 1).card
      = (Finset.univ.filter fun u : F ↦ quadraticChar F u = 1).card := by
    refine Finset.card_bij (fun y _ ↦ y - x) ?_ (fun a _ b _ h ↦ sub_left_inj.mp h) ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact ⟨u + x, by simpa using hu, by ring⟩
  have := card_quadraticChar_eq_one hq
  rw [nbrs_paleyField hq, hb]
  omega

theorem card_nbrs_inter_paleyField (hq : Fintype.card F % 4 = 1) {x y : F} (hxy : x ≠ y) :
    (((paleyField F).nbrs x ∩ (paleyField F).nbrs y).card : ℤ) * 4
      = Fintype.card F - 3 - 2 * quadraticChar F (y - x) := by
  have hb : (Finset.univ.filter fun z : F ↦
        quadraticChar F (z - x) = 1 ∧ quadraticChar F (z - y) = 1).card
      = (Finset.univ.filter fun u : F ↦
          quadraticChar F u = 1 ∧ quadraticChar F (u - (y - x)) = 1).card := by
    refine Finset.card_bij (fun z _ ↦ z - x) ?_ (fun a _ b _ h ↦ sub_left_inj.mp h) ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact ⟨hz.1, by rw [show z - x - (y - x) = z - y by ring]; exact hz.2⟩
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨u + x, ⟨by simpa using hu.1, ?_⟩, by ring⟩
      rw [show u + x - y = u - (y - x) by ring]
      exact hu.2
  have ha : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  rw [nbrs_inter_paleyField hq, hb, mul_comm]
  exact card_common_quadraticChar hq ha

end

section
open Fintype
variable (G : CGraph)

@[simp] theorem bipartiteCongr_inl (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (a : Fin n) :
    bipartiteCongr n σ τ (.inl a) = .inl (σ a) := rfl

@[simp] theorem bipartiteCongr_inr (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (b : Fin n) :
    bipartiteCongr n σ τ (.inr b) = .inr (τ b) := rfl

@[simp] theorem bipartiteSwap_inl (n : ℕ) (a : Fin n) : bipartiteSwap n (.inl a) = .inr a := rfl

@[simp] theorem bipartiteSwap_inr (n : ℕ) (b : Fin n) : bipartiteSwap n (.inr b) = .inl b := rfl

@[simp] theorem starAut_inl (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : Fin 1) :
    starAut n σ (.inl a) = .inl a := rfl

@[simp] theorem starAut_inr (n : ℕ) (σ : Equiv.Perm (Fin n)) (b : Fin n) :
    starAut n σ (.inr b) = .inr (σ b) := rfl

/-- Every arc of `K_{m,n}` crosses between the two sides. -/
theorem bipartite_arc (m n : ℕ) (x y : (bipartite m n).V) (h : (bipartite m n).Adj x y) :
    (∃ a b, x = .inl a ∧ y = .inr b) ∨ (∃ a b, x = .inr b ∧ y = .inl a) := by
  rcases x with a | b <;> rcases y with c | d
  · simp at h
  · exact Or.inl ⟨a, d, rfl, rfl⟩
  · exact Or.inr ⟨c, b, rfl, rfl⟩
  · simp at h

end

/-- Any sum over the vertices of a function of the degree is a sum over the degree sequence. -/
theorem sum_degSequence_map (G : CGraph) (f : ℕ → ℕ) :
    (G.degSequence.map f).sum = ∑ v : G.V, f (G.toSimple.degree v) := by
  have h : ((G.degSequence : List ℕ) : Multiset ℕ)
      = Finset.univ.val.map fun v ↦ G.toSimple.degree v := Multiset.sort_eq _ _
  have h2 : (G.degSequence.map f).sum = (((G.degSequence : List ℕ) : Multiset ℕ).map f).sum := rfl
  rw [h2, h, Multiset.map_map]
  rfl

/-- The line graph's edge count, phrased so that it only mentions the degree sequence. -/
@[toIsoGraph E_lineGraph]
theorem E_lineGraph_eq_sum_degSequence (G : CGraph) :
    (lineGraph G).E = (G.degSequence.map fun d ↦ d.choose 2).sum := by
  rw [sum_degSequence_map, E_lineGraph]

theorem degSequence_of_card_nbrs (G : CGraph) {k : ℕ} (h : ∀ v, (G.nbrs v).card = k) :
    G.degSequence = List.replicate (FinEnum.card G.V) k :=
  degSequence_of_regular G (isRegularOfDegree_of_card_nbrs G h)

section
variable {G H : CGraph}

/-! ### Degree sequences of the four products -/

theorem degSequence_cartesianProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (G □g H).degSequence
      = List.replicate (FinEnum.card G.V * FinEnum.card H.V) (k + l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_cartesianProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_cartesianProduct]

theorem degSequence_tensorProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (G ⊗g H).degSequence
      = List.replicate (FinEnum.card G.V * FinEnum.card H.V) (k * l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_tensorProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_tensorProduct]

theorem degSequence_lexProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (G ·g H).degSequence
      = List.replicate (FinEnum.card G.V * FinEnum.card H.V) (k * FinEnum.card H.V + l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_lexProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_lexProduct]

theorem degSequence_strongProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (G ⊠g H).degSequence
      = List.replicate (FinEnum.card G.V * FinEnum.card H.V) ((k + 1) * (l + 1) - 1) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_strongProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_strongProduct]

/-- An automorphism cannot change a degree, so a vertex-transitive graph is regular. -/
theorem degree_eq_of_isVertexTransitive {G : CGraph} (h : G.IsVertexTransitive) (u v : G.V) :
    G.toSimple.degree u = G.toSimple.degree v := by
  obtain ⟨σ, hσ⟩ := h u v
  rw [← hσ]
  exact (SimpleGraph.Iso.degree_eq σ.toSimpleIso u).symm

@[toIsoGraph]
theorem exists_degSequence_replicate_of_isVertexTransitive {G : CGraph}
    (h : G.IsVertexTransitive) : ∃ k, G.degSequence = List.replicate (FinEnum.card G.V) k := by
  cases isEmpty_or_nonempty G.V with
  | inl hE =>
    refine ⟨0, ?_⟩
    have hcard : FinEnum.card G.V = 0 := FinEnum.card_eq_zero_iff.2 hE
    have hnil : G.degSequence = [] :=
      List.eq_nil_of_length_eq_zero (by rw [length_degSequence, hcard])
    rw [hnil, hcard]
    rfl
  | inr hN =>
    obtain ⟨v₀⟩ := hN
    exact ⟨G.toSimple.degree v₀,
      degSequence_of_regular G fun v ↦ degree_eq_of_isVertexTransitive h v v₀⟩

/-! ### Joins have diameter at most two -/

/-- A graph with fewer than `V choose 2` edges has a non-adjacent pair: if every two distinct
vertices were adjacent it would be regular of degree `V - 1`, and the handshake lemma would make
the edge count exactly `V choose 2`. -/
theorem exists_not_adj_of_E_lt (G : CGraph) (h : G.E < (FinEnum.card G.V).choose 2) :
    ∃ u v : G.V, u ≠ v ∧ G.Adj u v = false := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ u v : G.V, u ≠ v → G.Adj u v = true := by
    intro u v huv
    simpa using hcon u v huv
  have hnbrs : ∀ u : G.V, (G.nbrs u).card = FinEnum.card G.V - 1 := by
    intro u
    have hu : G.nbrs u = Finset.univ.erase u := by
      ext w
      simp only [mem_nbrs, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro hw rfl
        rw [adj_self] at hw
        exact Bool.noConfusion hw
      · intro hw
        exact hall u w (Ne.symm hw)
    rw [hu, Finset.card_erase_of_mem (Finset.mem_univ u), FinEnum.card_univ]
  have h2 : 2 * G.E = FinEnum.card G.V * (FinEnum.card G.V - 1) := by
    rw [← sum_degSequence, degSequence_of_card_nbrs G hnbrs, List.sum_replicate, smul_eq_mul]
  rw [Nat.choose_two_right] at h
  set m := FinEnum.card G.V * (FinEnum.card G.V - 1) with hm
  omega

/-- In a join, two vertices on the same side have a common neighbour on the other side, and two
vertices on opposite sides are adjacent. -/
theorem two_step_join (G H : CGraph) [Nonempty G.V]
    [Nonempty H.V] (u v : (G ∇g H).V) (huv : u ≠ v) :
    (G ∇g H).toSimple.Adj u v ∨ ∃ w, (G ∇g H).toSimple.Adj u w ∧ (G ∇g H).toSimple.Adj w v := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  rcases u with a | b <;> rcases v with c | d
  · exact Or.inr ⟨Sum.inr b₀, by simp, by simp⟩
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inr ⟨Sum.inl a₀, by simp, by simp⟩

/-! ### Turán's theorem -/

/-- **Turán's theorem**: a graph whose clique number is at most `r` has `2r·|E| ≤ (r - 1)·|V|²`
edges. -/
@[toIsoGraph]
theorem two_mul_mul_E_le (G : CGraph) {r : ℕ} (hr : 0 < r) (h : G.cliqueNum ≤ r) :
    2 * r * G.E ≤ (r - 1) * (FinEnum.card G.V) ^ 2 := by
  rw [FinEnum.card_eq_fintypeCard']
  exact mul_card_edgeFinset_le_of_cliqueFree hr
    (cliqueFree_iff_cliqueNum_lt.2 (Nat.lt_succ_of_le h))

/-- **Mantel's theorem**: a triangle-free graph has at most `|V|²/4` edges. -/
theorem four_mul_E_le_card_sq (G : CGraph) (h : G.cliqueNum ≤ 2) :
    4 * G.E ≤ (FinEnum.card G.V) ^ 2 := by
  have := G.two_mul_mul_E_le (r := 2) (by omega) h
  omega

/-- **`|E| ≤ τ·Δ`**: each of the `τ` cover vertices takes care of at most `Δ` edges. -/
@[toIsoGraph]
theorem E_le_coverNum_mul_maxDeg (G : CGraph) : G.E ≤ G.coverNum * G.maxDeg := by
  classical
  exact card_edgeFinset_le_vertexCoverNum_mul_maxDegree G.toSimple

theorem E_pos_of_adj {G : CGraph} {a b : G.V} (h : G.toSimple.Adj a b) : 0 < G.E :=
  Finset.card_pos.2 ⟨s(a, b), SimpleGraph.mem_edgeFinset.2 h⟩

/-- Choosing, in every component, one vertex to be the root, and sending every other vertex to the
edge joining it to a neighbour closer to that root, embeds `V` minus the roots into `E`:
`|V| ≤ |E| + c(G)`. -/
@[toIsoGraph V_le_E_add_numComponents]
theorem card_le_E_add_numComponents (G : CGraph) :
    FinEnum.card G.V ≤ G.E + G.numComponents := by
  classical
  rcases isEmpty_or_nonempty G.V with hV | hV
  · simp [FinEnum.card_eq_zero_iff.2 hV]
  choose r hr using G.surjective_connectedComponentMk
  set root : G.V → G.V := fun v ↦ r (G.toSimple.connectedComponentMk v) with hroot
  have hreach : ∀ v, G.toSimple.Reachable v (root v) := by
    intro v
    apply SimpleGraph.ConnectedComponent.exact
    rw [hroot]
    exact (hr _).symm
  have hrootroot : ∀ c, root (r c) = r c := fun c ↦ by rw [hroot]; simp only [hr]
  -- the roots form a set of size `c(G)`
  have hinj : Function.Injective r := fun c d h ↦ by rw [← hr c, ← hr d, h]
  have himg : Finset.univ.filter (fun v ↦ v = root v) = Finset.univ.image r := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact fun h ↦ ⟨G.toSimple.connectedComponentMk v, h.symm⟩
    · rintro ⟨c, rfl⟩
      exact (hrootroot c).symm
  have hroots : (Finset.univ.filter (fun v ↦ v = root v)).card = G.numComponents := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, numComponents,
      Fintype.card_eq_nat_card]
  -- and every other vertex picks out an edge, injectively
  choose! u hu1 hu2 using fun v (hv : v ≠ root v) ↦ G.exists_adj_dist_lt (hreach v) hv
  have hne : ∀ {v w : G.V}, G.toSimple.Adj v w → root v = root w := fun {v w} h ↦ by
    rw [hroot]
    simp only
    rw [SimpleGraph.ConnectedComponent.sound h.reachable]
  have hmaps : ∀ v ∈ Finset.univ.filter (fun v ↦ ¬ v = root v),
      s(v, u v) ∈ G.toSimple.edgeFinset := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simpa using hu1 v hv
  have hinjOn : Set.InjOn (fun v ↦ s(v, u v))
      (Finset.univ.filter (fun v ↦ ¬ v = root v) : Finset G.V) := by
    intro v hv w hw h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have hrw : root v = root w := hne (h2 ▸ hu1 v hv)
      have d1 := hu2 v hv
      have d2 := hu2 w hw
      rw [← h1] at d2
      rw [h2, hrw] at d1
      omega
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G.V)) (p := fun v ↦ v = root v)
  have hle : (Finset.univ.filter (fun v ↦ ¬ v = root v)).card ≤ G.E :=
    Finset.card_le_card_of_injOn _ hmaps hinjOn
  rw [FinEnum.card_univ] at hcards
  omega

/-- A connected graph has at least `|V| - 1` edges. -/
theorem card_le_E_add_one_of_isConnected (G : CGraph) (h : G.IsConnected) :
    FinEnum.card G.V ≤ G.E + 1 := by
  have := G.card_le_E_add_numComponents
  rw [(numComponents_eq_one_iff G).2 h] at this
  exact this

/-- Each edge can merge at most two components, so a graph with few edges has many components. -/
theorem card_sub_E_le_numComponents (G : CGraph) :
    FinEnum.card G.V - G.E ≤ G.numComponents := by
  have := G.card_le_E_add_numComponents
  omega

/-- More components than vertices is impossible, so a graph with fewer components than vertices
has an edge. -/
theorem E_pos_of_numComponents_lt_card (G : CGraph) (h : G.numComponents < FinEnum.card G.V) :
    0 < G.E := by
  have := G.card_le_E_add_numComponents
  omega

/-! ### Matchings versus independent sets -/

/-- Every edge of `G` has an endpoint outside a given independent set. -/
theorem one_le_card_sdiff_of_isIndepSet (G : CGraph) {I : Finset G.V}
    (hI : G.toSimple.IsIndepSet (I : Set G.V)) (e : (lineGraph G).V) :
    1 ≤ (e.1.toFinset \ I).card := by
  classical
  revert e
  refine lineGraph_vertex_cases fun u v huv ↦ ?_
  have hadj : G.toSimple.Adj u v := huv
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  by_cases hu : u ∈ I
  · exact ⟨v, Finset.mem_sdiff.2 ⟨by simp, fun hv ↦
      hI (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hadj.ne hadj⟩⟩
  · exact ⟨u, Finset.mem_sdiff.2 ⟨by simp, hu⟩⟩

/-- **No short cycle in `Cₙ`.**  A closed chain of fewer than `n` distinct vertices misses one,
and rotating that vertex to the top turns the chain into a cycle in the acyclic `path n`. -/
theorem cycle_no_short_cycleList {N : ℕ} (hN : 3 ≤ N) (u : (cycle N).V) (vs : List (cycle N).V)
    (h2 : 2 ≤ vs.length) (hlt : vs.length + 1 < N) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun a b ↦ (cycle N).Adj a b) (u :: vs))
    (hcl : (cycle N).Adj (vs.getLastD u) u) : False := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : Fin N, x ∉ u :: vs := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin N)) ⊆ (u :: vs).toFinset :=
      fun a _ ↦ List.mem_toFinset.2 (hcon a)
    have h1 := Finset.card_le_card hsub
    have h2' : (u :: vs).toFinset.card ≤ (u :: vs).length := List.toFinset_card_le _
    simp only [Finset.card_univ, Fintype.card_fin, List.length_cons] at h1 h2'
    omega
  have hmem : ∀ a ∈ u :: vs, a ≠ x := fun a ha hax ↦ hx (hax ▸ ha)
  refine absurd (isAcyclic_path N) ?_
  refine not_isAcyclic_of_cycleList (G := path N) (cycRot x u) (vs.map (cycRot x)) ?_ ?_ ?_ ?_
  · simpa using h2
  · rw [show cycRot x u :: vs.map (cycRot x) = (u :: vs).map (cycRot x) from rfl]
    exact hnd.map (cycRot_injective x)
  · rw [show cycRot x u :: vs.map (cycRot x) = (u :: vs).map (cycRot x) from rfl]
    refine (List.isChain_map (cycRot x)).2 ?_
    exact hch.imp_of_mem_imp fun a b ha hb hab ↦
      path_adj_cycRot hN (hmem a ha) (hmem b hb) hab
  · rw [getLastD_map]
    exact path_adj_cycRot hN (hmem _ List.getLastD_mem_cons) (hmem u (by simp)) hcl

/-- **Every vertex of a cycle list has two distinct neighbours in the list**: its predecessor and
its successor around the closed chain. -/
theorem cycleList_two_nbrs {G : CGraph} {u : G.V} {vs : List G.V}
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u)
    {x : G.V} (hx : x ∈ u :: vs) :
    ∃ a b, a ∈ u :: vs ∧ b ∈ u :: vs ∧ a ≠ b ∧ G.Adj x a = true ∧ G.Adj x b = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hn : (u :: vs).length = vs.length + 1 := List.length_cons ..
  have hi' : i < vs.length + 1 := by omega
  have hlast : (u :: vs)[vs.length]'(by simp) = vs.getLastD u := (getLastD_eq_getElem vs u).symm
  have hhead : (u :: vs)[0]'(by simp) = u := rfl
  have hsucc : ∀ j : ℕ, ∀ _ : j < vs.length + 1,
      G.Adj ((u :: vs)[j]'(by omega)) ((u :: vs)[if j + 1 = vs.length + 1 then 0 else j + 1]'
        (by split_ifs <;> omega)) = true := by
    intro j hj
    by_cases hje : j + 1 = vs.length + 1
    · have e1 : (u :: vs)[j]'(by omega) = vs.getLastD u :=
        (getElem_congr_idx (u :: vs) (show j = vs.length from by omega) (by omega)).trans hlast
      have e2 : (u :: vs)[if j + 1 = vs.length + 1 then 0 else j + 1]'
          (by split_ifs; omega) = u :=
        (getElem_congr_idx (u :: vs)
          (show (if j + 1 = vs.length + 1 then 0 else j + 1) = 0 from if_pos hje)
          (by split_ifs; omega)).trans hhead
      rw [e1, e2]
      exact hcl
    · have e2 : (u :: vs)[if j + 1 = vs.length + 1 then 0 else j + 1]'
          (by split_ifs; omega) = (u :: vs)[j + 1]'(by omega) :=
        getElem_congr_idx (u :: vs) (if_neg hje) (by split_ifs; omega)
      rw [e2]
      exact List.isChain_iff_getElem.1 hch j (by omega)
  refine ⟨(u :: vs)[if i + 1 = vs.length + 1 then 0 else i + 1]'(by split_ifs <;> omega),
    (u :: vs)[if i = 0 then vs.length else i - 1]'(by split_ifs <;> omega),
    List.getElem_mem _, List.getElem_mem _, ?_, hsucc i hi', ?_⟩
  · intro heq
    have := (List.Nodup.getElem_inj_iff hnd).1 heq
    split_ifs at this <;> omega
  · have hprev := hsucc (if i = 0 then vs.length else i - 1) (by split_ifs <;> omega)
    have e3 : (u :: vs)[if (if i = 0 then vs.length else i - 1) + 1 = vs.length + 1 then 0
          else (if i = 0 then vs.length else i - 1) + 1]'(by split_ifs <;> omega)
        = (u :: vs)[i]'(by omega) :=
      getElem_congr_idx (u :: vs) (by split_ifs <;> omega) (by split_ifs <;> omega)
    rw [e3] at hprev
    rw [G.symm]
    exact hprev

/-- A closed nodup chain of a graph `H` whose vertices carry distinct labels below `M`, with
adjacent vertices carrying adjacent labels, is impossible when the chain is shorter than `M`:
it would be a short cycle in `cycle M`. -/
theorem no_short_cycleList_of_labels {H : CGraph} {M : ℕ} (hM : 3 ≤ M) (gv : H.V → ℕ)
    (u : H.V) (vs : List H.V) (hbd : ∀ a ∈ u :: vs, gv a < M)
    (hginj : ∀ a ∈ u :: vs, ∀ b ∈ u :: vs, gv a = gv b → a = b)
    (hgadj : ∀ a ∈ u :: vs, ∀ b ∈ u :: vs, H.Adj a b = true →
      ∀ (ha : gv a < M) (hb : gv b < M), (cycle M).Adj ⟨gv a, ha⟩ ⟨gv b, hb⟩ = true)
    (h2 : 2 ≤ vs.length) (hlt : vs.length + 1 < M) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ H.Adj x y) (u :: vs)) (hcl : H.Adj (vs.getLastD u) u) :
    False := by
  obtain ⟨g, hgval⟩ : ∃ g : H.V → (cycle M).V, ∀ a ∈ u :: vs, (g a).1 = gv a :=
    ⟨fun v ↦ ⟨min (gv v) (M - 1), by omega⟩,
      fun a ha ↦ show min (gv a) (M - 1) = gv a from by have := hbd a ha; omega⟩
  have hmap : ∀ a, a ∈ u :: vs → ∀ b, b ∈ u :: vs → H.Adj a b = true →
      (cycle M).Adj (g a) (g b) = true := by
    intro a ha b hb hab
    have ea : g a = ⟨gv a, hbd a ha⟩ := Fin.ext (hgval a ha)
    have eb : g b = ⟨gv b, hbd b hb⟩ := Fin.ext (hgval b hb)
    rw [ea, eb]
    exact hgadj a ha b hb hab _ _
  have hlastmem : vs.getLastD u ∈ u :: vs := List.getLastD_mem_cons
  refine cycle_no_short_cycleList hM (g u) (vs.map g) (by simpa using h2) (by simpa using hlt)
    ?_ ?_ ?_
  · rw [show g u :: vs.map g = (u :: vs).map g from rfl]
    refine hnd.map_on fun a ha b hb hab ↦ ?_
    exact hginj a ha b hb ((hgval a ha).symm.trans ((congrArg Fin.val hab).trans (hgval b hb)))
  · rw [show g u :: vs.map g = (u :: vs).map g from rfl]
    exact (List.isChain_map g).2 (hch.imp_of_mem_imp fun a b ha hb hab ↦ hmap a ha b hb hab)
  · rw [getLastD_map]
    exact hmap _ hlastmem u (by simp) hcl

/-- A proper colouring of the line graph *is* an edge colouring: read it back as a symmetric
function on ordered pairs, with a fixed junk value off the edges.  This is the converse of
`chromNum_lineGraph_le_of_edgeColouring`, and it needs a colour to spare for the junk. -/
theorem exists_edgeColouring {G : CGraph} {k : ℕ}
    (h : (lineGraph G).chromNum ≤ k) (j : Fin k) :
    ∃ c : G.V → G.V → Fin k, (∀ x y, c x y = c y x) ∧
      ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w := by
  obtain ⟨col⟩ := chromNum_le_iff_colorable.1 h
  refine ⟨fun x y ↦ if hxy : s(x, y) ∈ G.toSimple.edgeSet then col ⟨s(x, y), hxy⟩ else j, ?_, ?_⟩
  · intro x y
    simp only [Sym2.eq_swap]
  · intro u v w huv huw hvw
    have hev : s(u, v) ∈ G.toSimple.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, toSimple_adj]; exact huv
    have hew : s(u, w) ∈ G.toSimple.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, toSimple_adj]; exact huw
    beta_reduce
    rw [dif_pos hev, dif_pos hew]
    refine col.valid ?_
    have hne : (⟨s(u, v), hev⟩ : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) ≠ ⟨s(u, w), hew⟩ := by
      intro hh
      exact hvw ((Sym2.congr_right).1 (Subtype.ext_iff.1 hh))
    show (lineGraph G).Adj _ _ = true
    rw [lineGraph_adj]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hne, u, by simp, by simp⟩

end

end CGraph

namespace IsoGraph

/-! ### Edge counts

`V_*` reads the vertex count of every family off its `CGraph` counterpart; these do the same for
the edge count.  The operations all follow the same script: push the quotient through with
`mk_canonicalize`, replace the constructor by its `CGraph` form, and apply the `CGraph` lemma. -/

@[simp] theorem E_empty (n : ℕ) : (empty n).E = 0 := CGraph.E_empty n

@[simp] theorem E_complete (n : ℕ) : (complete n).E = n.choose 2 := CGraph.E_complete n

@[simp] theorem E_path (n : ℕ) : (path (n + 1)).E = n := CGraph.E_path n

@[simp] theorem E_cycle (n : ℕ) : (cycle (n + 3)).E = n + 3 := CGraph.E_cycle n

/-! ### Connectivity and triangles in the strong and lexicographic products -/

@[simp] theorem E_complete_pos (n : ℕ) : 0 < (complete (n + 2)).E := by
  rw [E_complete]
  exact Nat.choose_pos (by omega)

/-! ### Degree sequences -/

@[simp] theorem degSequence_empty (n : ℕ) : degSequence (empty n) = List.replicate n 0 :=
  CGraph.degSequence_empty n

@[simp] theorem degSequence_complete (n : ℕ) :
    degSequence (complete n) = List.replicate n (n - 1) := CGraph.degSequence_complete n

/-! ### Regular families beyond the strongly regular ones -/

/-- The handshake lemma for any graph whose degree sequence is constant. -/
theorem two_mul_E_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : 2 * G.E = n * k := by
  rw [← sum_degSequence, h, List.sum_replicate, smul_eq_mul]

/-! ### Degree sequences of the products

A product of regular graphs is regular, and on the quotient "regular of degree `k`" is exactly
"the degree sequence is `List.replicate _ k`". -/

private theorem card_eq_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : n = G.V := by
  rw [← length_degSequence, h, List.length_replicate]

theorem degSequence_cartesianProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G □g H) = List.replicate (m * n) (k + l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_cartesianProduct hG hH

theorem degSequence_tensorProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G ⊗g H) = List.replicate (m * n) (k * l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_tensorProduct hG hH

theorem degSequence_lexProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G ·g H) = List.replicate (m * n) (k * n + l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_lexProduct hG hH

theorem degSequence_strongProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G ⊠g H) = List.replicate (m * n) ((k + 1) * (l + 1) - 1) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_strongProduct hG hH

/-! ### Vertex-transitive graphs are regular -/

/-- A vertex-transitive graph is regular, so the vertex and edge counts already pin down its
degree sequence. -/
theorem degSequence_of_isVertexTransitive {G : IsoGraph} {k : ℕ} (h : IsVertexTransitive G)
    (hV : 0 < G.V) (hk : G.V * k = 2 * G.E) : degSequence G = List.replicate G.V k := by
  obtain ⟨k', hk'⟩ := exists_degSequence_replicate_of_isVertexTransitive h
  have h2 := two_mul_E_of_degSequence_replicate hk'
  have : k = k' := Nat.eq_of_mul_eq_mul_left hV (hk.trans h2)
  rwa [this]

@[simp] theorem degSequence_cycle (n : ℕ) :
    degSequence (cycle (n + 3)) = List.replicate (n + 3) 2 := by
  have h := degSequence_of_isVertexTransitive (k := 2) (isVertexTransitive_cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle, E_cycle]; omega)
  rwa [V_cycle] at h

/-! ### Distinguishing graphs

Because `IsoGraph` is the quotient of `CGraph` by isomorphism, `G ≠ H` *is* the assertion that
`G` and `H` are non-isomorphic. Every invariant therefore doubles as a tool for proving
non-isomorphism: if it takes different values on the two graphs, they are different. -/

theorem ne_of_V_ne {G H : IsoGraph} (h : G.V ≠ H.V) : G ≠ H := ne_of_apply_ne V h

theorem ne_of_E_ne {G H : IsoGraph} (h : G.E ≠ H.E) : G ≠ H := ne_of_apply_ne E h

theorem ne_of_degSequence_ne {G H : IsoGraph} (h : degSequence G ≠ degSequence H) : G ≠ H :=
  ne_of_apply_ne degSequence h

private theorem replicate_ne {k a b : ℕ} (hk : 0 < k) (hab : a ≠ b) :
    List.replicate k a ≠ List.replicate k b := fun h ↦
  hab (List.eq_of_mem_replicate (h ▸ List.mem_replicate.2 ⟨hk.ne', rfl⟩))

/-- Two regular graphs on the same (positive) number of vertices but of different degree are
non-isomorphic. -/
theorem ne_of_degree_ne {G H : IsoGraph} {n k l : ℕ} (hG : degSequence G = List.replicate n k)
    (hH : degSequence H = List.replicate n l) (hn : 0 < n) (hkl : k ≠ l) : G ≠ H :=
  ne_of_degSequence_ne (by rw [hG, hH]; exact replicate_ne hn hkl)

/-! ### Degree multisets

`degSequence` is a sorted list, which makes it awkward to combine: the degree sequence of a
disjoint union is a *merge* of the two sequences, not a concatenation.  The underlying multiset
`degMultiset` has no such problem, and since `degSequence` is literally its `sort`
(`coe_degSequence`) nothing is lost by working with it. -/

@[simp] theorem card_degMultiset (G : IsoGraph) : Multiset.card (degMultiset G) = G.V := by
  rw [← coe_degSequence, Multiset.coe_card, length_degSequence]

/-- The handshake lemma, for the degree multiset. -/
theorem sum_degMultiset (G : IsoGraph) : (degMultiset G).sum = 2 * G.E := by
  rw [← coe_degSequence, Multiset.sum_coe, sum_degSequence]

theorem ne_of_degMultiset_ne {G H : IsoGraph} (h : degMultiset G ≠ degMultiset H) : G ≠ H :=
  ne_of_apply_ne degMultiset h

/-- Reading a degree multiset off a constant degree sequence. -/
theorem degMultiset_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : degMultiset G = Multiset.replicate n k := by
  rw [← coe_degSequence, h, Multiset.coe_replicate]

/-! ### Degree multisets of the named graphs -/

@[simp] theorem degMultiset_empty (n : ℕ) : degMultiset (empty n) = Multiset.replicate n 0 :=
  degMultiset_of_degSequence (degSequence_empty n)

@[simp] theorem degMultiset_complete (n : ℕ) :
    degMultiset (complete n) = Multiset.replicate n (n - 1) :=
  degMultiset_of_degSequence (degSequence_complete n)

@[simp] theorem degMultiset_cycle (n : ℕ) :
    degMultiset (cycle (n + 3)) = Multiset.replicate (n + 3) 2 :=
  degMultiset_of_degSequence (degSequence_cycle n)

/-! ### The degrees of a path

The path is the first named graph whose degrees are not all equal, so it is the first whose degree
multiset needs `degMultiset_path` rather than the strong-regularity machinery.  Sorting the
resulting multiset is easy enough that the degree *sequence* comes out too. -/

@[simp] theorem degMultiset_path (n : ℕ) :
    degMultiset (path (n + 2)) = 1 ::ₘ 1 ::ₘ Multiset.replicate n 2 := by
  rw [degMultiset_path_eq]
  set g : ℕ → ℕ := fun k ↦ (if k + 1 < n + 2 then 1 else 0) + (if 0 < k then 1 else 0) with hg
  have hmid : ∀ m, m ≤ n → (Multiset.range (m + 1)).map g = 1 ::ₘ Multiset.replicate m 2 := by
    intro m
    induction m with
    | zero => intro _; simp [hg]
    | succ p ih =>
      intro hp
      have hgp : g (p + 1) = 2 := by simp only [hg]; split_ifs <;> omega
      rw [Multiset.range_succ, Multiset.map_cons, ih (by omega), hgp, Multiset.cons_swap,
        ← Multiset.replicate_succ]
  have hgn : g (n + 1) = 1 := by simp only [hg]; split_ifs <;> omega
  rw [Multiset.range_succ, Multiset.map_cons, hmid n le_rfl, hgn]

/-- Sorting a multiset whose sorted form we can guess. -/
theorem sort_eq_of_pairwise {s : Multiset ℕ} {l : List ℕ} (hl : l.Pairwise (· ≤ ·))
    (h : (l : Multiset ℕ) = s) : s.sort (· ≤ ·) = l :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba ↦ le_antisymm hab hba)
    (Multiset.pairwise_sort s (· ≤ ·)) hl
    (Multiset.coe_eq_coe.mp (by rw [Multiset.sort_eq, h]))

@[simp] theorem degSequence_path (n : ℕ) :
    degSequence (path (n + 2)) = 1 :: 1 :: List.replicate n 2 := by
  rw [degSequence_eq_sort]
  refine sort_eq_of_pairwise ?_ ?_
  · simp [List.pairwise_cons, List.mem_replicate]
  · rw [degMultiset_path]
    rfl

/-! ### The named graphs -/

@[simp] theorem maxDeg_empty (n : ℕ) : maxDeg (empty n) = 0 :=
  Nat.le_zero.1 (maxDeg_le_of_degMultiset fun d hd ↦ by
    rw [degMultiset_empty] at hd
    exact le_of_eq (Multiset.eq_of_mem_replicate hd))

@[simp] theorem minDeg_empty (n : ℕ) : minDeg (empty n) = 0 :=
  Nat.le_zero.1 (le_trans (minDeg_le_maxDeg _) (le_of_eq (maxDeg_empty n)))

@[simp] theorem maxDeg_complete (n : ℕ) : maxDeg (complete n) = n - 1 := by
  cases n with
  | zero =>
    refine Nat.le_zero.1 (maxDeg_le_of_degMultiset fun d hd ↦ ?_)
    rw [degMultiset_complete] at hd
    exact le_of_eq (Multiset.eq_of_mem_replicate hd)
  | succ m => exact maxDeg_of_degMultiset_replicate (n := m + 1) (Nat.succ_pos m) (by simp)

@[simp] theorem minDeg_complete (n : ℕ) : minDeg (complete n) = n - 1 := by
  cases n with
  | zero => exact Nat.le_zero.1 (le_trans (minDeg_le_maxDeg _) (by simp))
  | succ m => exact minDeg_of_degMultiset_replicate (n := m + 1) (Nat.succ_pos m) (by simp)

@[simp] theorem maxDeg_cycle (n : ℕ) : maxDeg (cycle (n + 3)) = 2 :=
  maxDeg_of_degMultiset_replicate (n := n + 3) (by omega) (by simp)

@[simp] theorem minDeg_cycle (n : ℕ) : minDeg (cycle (n + 3)) = 2 :=
  minDeg_of_degMultiset_replicate (n := n + 3) (by omega) (by simp)

@[simp] theorem maxDeg_path (n : ℕ) : maxDeg (path (n + 3)) = 2 := by
  refine maxDeg_eq_of_degMultiset ?_ fun d hd ↦ ?_
  · rw [show n + 3 = (n + 1) + 2 from rfl, degMultiset_path]
    simp
  · rw [show n + 3 = (n + 1) + 2 from rfl, degMultiset_path] at hd
    rcases Multiset.mem_cons.1 hd with h | h
    · omega
    rcases Multiset.mem_cons.1 h with h | h
    · omega
    · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem minDeg_path (n : ℕ) : minDeg (path (n + 2)) = 1 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_path] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  rcases Multiset.mem_cons.1 h with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

/-! ### Turán's theorem -/

/-- **Mantel's theorem**: `4·|E| ≤ |V|²` for a triangle-free graph. -/
theorem four_mul_E_le_V_sq (G : IsoGraph) (h : G.cliqueNum ≤ 2) : 4 * G.E ≤ G.V ^ 2 := by
  have := G.two_mul_mul_E_le (r := 2) (by omega) h
  omega

/-! ### The domination number -/

/-- With Gallai's identity, the degree bound reads `τ ≥ |V|·Δ/(Δ+1) - ...`; more usefully it
bounds the independence number from below, since `γ ≤ α`. -/
theorem V_le_indepNum_mul_maxDeg_add_one (G : IsoGraph) : G.V ≤ G.indepNum * (G.maxDeg + 1) :=
  le_trans G.V_le_domNum_mul_maxDeg_add_one
    (Nat.mul_le_mul_right _ G.domNum_le_indepNum)

/-! ### The handshaking lemma -/

/-- A graph all of whose degrees are odd has evenly many vertices. -/
theorem even_V_of_forall_odd_mem_degSequence (G : IsoGraph)
    (h : ∀ d ∈ degSequence G, Odd d) : Even G.V := by
  have hc := G.even_countP_odd_degSequence
  rwa [List.countP_eq_length.2 (fun d hd ↦ by simpa using h d hd), length_degSequence] at hc

/-- **An odd-regular graph has evenly many vertices.** -/
theorem even_V_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hk : Odd k)
    (h : degSequence G = List.replicate n k) : Even G.V :=
  G.even_V_of_forall_odd_mem_degSequence fun d hd ↦ by
    rw [h, List.mem_replicate] at hd
    exact hd.2 ▸ hk

/-- On an odd number of vertices, some degree is even. -/
theorem exists_even_mem_degSequence_of_odd_V (G : IsoGraph) (h : Odd G.V) :
    ∃ d ∈ degSequence G, Even d := by
  by_contra hc
  push_neg at hc
  exact Nat.not_even_iff_odd.2 h (G.even_V_of_forall_odd_mem_degSequence
    fun d hd ↦ Nat.not_even_iff_odd.1 (hc d hd))

/-! ### Vertices, edges and components -/

theorem V_le_E_add_one_of_isConnected {G : IsoGraph} (h : G.IsConnected) : G.V ≤ G.E + 1 := by
  have := G.V_le_E_add_numComponents
  rw [numComponents_eq_one_of_isConnected h] at this
  exact this

theorem V_sub_E_le_numComponents (G : IsoGraph) : G.V - G.E ≤ G.numComponents := by
  have := G.V_le_E_add_numComponents
  omega

theorem E_pos_of_numComponents_lt_V {G : IsoGraph} (h : G.numComponents < G.V) : 0 < G.E := by
  have := G.V_le_E_add_numComponents
  omega

/-- `c(G) = |V|` forces `E = 0`, and this recovers it quantitatively: each edge kills at most one
component. -/
theorem V_sub_numComponents_le_E (G : IsoGraph) : G.V - G.numComponents ≤ G.E := by
  have := G.V_le_E_add_numComponents
  omega

/-! ### Independence numbers of the graph products -/

/-- `α(G × H)` is also at least `|V(G)| · α(H)`, by symmetry. -/
theorem V_mul_indepNum_le_indepNum_tensorProduct (G H : IsoGraph) :
    G.V * H.indepNum ≤ (G ⊗g H).indepNum := by
  rw [tensorProduct_comm, mul_comm]
  exact indepNum_mul_V_le_indepNum_tensorProduct H G

/-- Fibrewise counting from below: `|V(G)|·τ(H) ≤ τ(G □ H)`. -/
theorem V_mul_coverNum_le_coverNum_cartesianProduct (G H : IsoGraph) :
    G.V * H.coverNum ≤ (G □g H).coverNum := by
  have h1 : G.V * H.coverNum = G.V * H.V - G.V * H.indepNum := by
    rw [coverNum_eq, Nat.mul_sub]
  have h2 := indepNum_cartesianProduct_le G H
  have h3 := (G □g H).coverNum_add_indepNum
  rw [V_cartesianProduct] at h3
  have h4 : G.V * H.indepNum ≤ G.V * H.V :=
    Nat.mul_le_mul_left _ (by have := H.coverNum_add_indepNum; omega)
  omega

/-- The strong product contains the cartesian one, and both have the same vertex set, so the
lower bound survives: `|V(G)|·τ(H) ≤ τ(G ⊠ H)`. -/
theorem V_mul_coverNum_le_coverNum_strongProduct (G H : IsoGraph) :
    G.V * H.coverNum ≤ (G ⊠g H).coverNum := by
  have h1 : G.V * H.coverNum = G.V * H.V - G.V * H.indepNum := by
    rw [coverNum_eq, Nat.mul_sub]
  have h2 := indepNum_strongProduct_le G H
  have h3 := (G ⊠g H).coverNum_add_indepNum
  rw [V_strongProduct] at h3
  have h4 : G.V * H.indepNum ≤ G.V * H.V :=
    Nat.mul_le_mul_left _ (by have := H.coverNum_add_indepNum; omega)
  omega

/-- **Nordhaus–Gaddum, lower bound**: `|V| - 1 ≤ τ(G) + τGᶜ`, dual to `α + ω ≤ |V| + 1`. -/
theorem V_sub_one_le_coverNum_add_coverNum_compl (G : IsoGraph) :
    G.V - 1 ≤ G.coverNum + Gᶜ.coverNum := by
  have h1 := G.coverNum_add_coverNum_compl_add_indepNum_add_cliqueNum
  have h2 := G.cliqueNum_add_indepNum_le_V_add_one
  omega

/-! ### The edge chromatic number

The chromatic index `χ'(G)` is the chromatic number of the line graph — that is its definition,
in `Invariants/Derived.lean` — so `edgeChromNum_eq` turns every statement below into one about
`chromNum` of `lineGraph`. -/

/-- Every edge colouring uses at least `Δ` colours, since the edges at a vertex of maximum
degree pairwise conflict. -/
theorem maxDeg_le_edgeChromNum (G : IsoGraph) : G.maxDeg ≤ G.edgeChromNum := by
  rw [edgeChromNum_eq]
  exact le_trans G.maxDeg_le_cliqueNum_lineGraph (cliqueNum_le_chromNum _)

/-- Each vertex of `L(G)` dominates at most `2Δ - 1` vertices including itself. -/
theorem E_le_domNum_lineGraph_mul (G : IsoGraph) (hd : 1 ≤ G.maxDeg) :
    G.E ≤ (lineGraph G).domNum * (2 * G.maxDeg) := by
  have h := V_le_domNum_mul_maxDeg_add_one (lineGraph G)
  have h2 := maxDeg_lineGraph_le G
  rw [V_lineGraph] at h
  exact h.trans (Nat.mul_le_mul_left _ (by omega))

theorem E_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 3) □g cycle (n + 3)).E = 2 * ((m + 3) * (n + 3)) := by
  rw [E_cartesianProduct, E_cycle, E_cycle, V_cycle, V_cycle]
  ring

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

theorem E_strongProduct_complete (m n : ℕ) :
    (complete m ⊠g complete n).E
      = m * n.choose 2 + n * m.choose 2 + 2 * m.choose 2 * n.choose 2 := by
  rw [E_strongProduct, E_complete, E_complete, V_complete, V_complete]

theorem E_lexProduct_complete (m n : ℕ) :
    (complete m ·g complete n).E = n * n * m.choose 2 + m * n.choose 2 := by
  rw [E_lexProduct, E_complete, E_complete, V_complete, V_complete]

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

/-! ### The disjoint union of two cycles -/

@[simp] theorem minDeg_disjUnion_cycle (m n : ℕ) :
    minDeg (cycle (m + 3) ⊕g cycle (n + 3)) = 2 := by
  have h := minDeg_disjUnion (G := cycle (m + 3)) (H := cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, minDeg_cycle] at h
  omega

/-! ### The disjoint union of two paths -/

@[simp] theorem minDeg_disjUnion_path (m n : ℕ) :
    minDeg (path (m + 2) ⊕g path (n + 2)) = 1 := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := path (n + 2))
    (by rw [V_path]; omega) (by rw [V_path]; omega)
  rw [minDeg_path, minDeg_path] at h
  omega

/-! ### The disjoint union of two complete graphs -/

@[simp] theorem minDeg_disjUnion_complete (m n : ℕ) :
    minDeg (complete (m + 1) ⊕g complete (n + 1)) = min m n := by
  have h := minDeg_disjUnion (G := complete (m + 1)) (H := complete (n + 1))
    (by rw [V_complete]; omega) (by rw [V_complete]; omega)
  rw [minDeg_complete, minDeg_complete] at h
  omega

theorem maxDeg_cartesianProduct_complete_cycle (m n : ℕ) :
    maxDeg (complete (m + 1) □g cycle (n + 3)) = m + 2 := by
  have h := maxDeg_cartesianProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_complete, maxDeg_cycle] at h
  omega

theorem minDeg_cartesianProduct_complete_cycle (m n : ℕ) :
    minDeg (complete (m + 1) □g cycle (n + 3)) = m + 2 := by
  have h := minDeg_cartesianProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_complete, minDeg_cycle] at h
  omega

theorem maxDeg_cartesianProduct_complete_path (m n : ℕ) :
    maxDeg (complete (m + 1) □g path (n + 3)) = m + 2 := by
  have h := maxDeg_cartesianProduct (G := complete (m + 1)) (H := path (n + 3))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [maxDeg_complete, maxDeg_path] at h
  omega

theorem minDeg_cartesianProduct_complete_path (m n : ℕ) :
    minDeg (complete (m + 1) □g path (n + 2)) = m + 1 := by
  have h := minDeg_cartesianProduct (G := complete (m + 1)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [minDeg_complete, minDeg_path] at h
  omega

theorem maxDeg_strongProduct_complete_cycle (m n : ℕ) :
    maxDeg (complete (m + 1) ⊠g cycle (n + 3)) = 3 * m + 2 := by
  have h := maxDeg_strongProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_complete, maxDeg_cycle] at h
  omega

theorem minDeg_strongProduct_complete_cycle (m n : ℕ) :
    minDeg (complete (m + 1) ⊠g cycle (n + 3)) = 3 * m + 2 := by
  have h := minDeg_strongProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_complete, minDeg_cycle] at h
  omega

theorem maxDeg_lexProduct_complete_cycle (m n : ℕ) :
    maxDeg (complete (m + 1) ·g cycle (n + 3)) = m * (n + 3) + 2 := by
  have h := maxDeg_lexProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_complete, maxDeg_cycle, V_cycle] at h
  simpa using h

theorem minDeg_lexProduct_complete_cycle (m n : ℕ) :
    minDeg (complete (m + 1) ·g cycle (n + 3)) = m * (n + 3) + 2 := by
  have h := minDeg_lexProduct (G := complete (m + 1)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_complete, minDeg_cycle, V_cycle] at h
  simpa using h

theorem maxDeg_strongProduct_complete_path (m n : ℕ) :
    maxDeg (complete (m + 1) ⊠g path (n + 3)) = 3 * m + 2 := by
  have h := maxDeg_strongProduct (G := complete (m + 1)) (H := path (n + 3))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [maxDeg_complete, maxDeg_path] at h
  omega

theorem minDeg_strongProduct_complete_path (m n : ℕ) :
    minDeg (complete (m + 1) ⊠g path (n + 2)) = 2 * m + 1 := by
  have h := minDeg_strongProduct (G := complete (m + 1)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [minDeg_complete, minDeg_path] at h
  omega

theorem maxDeg_lexProduct_complete_path (m n : ℕ) :
    maxDeg (complete (m + 1) ·g path (n + 3)) = m * (n + 3) + 2 := by
  have h := maxDeg_lexProduct (G := complete (m + 1)) (H := path (n + 3))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [maxDeg_complete, maxDeg_path, V_path] at h
  simpa using h

theorem minDeg_lexProduct_complete_path (m n : ℕ) :
    minDeg (complete (m + 1) ·g path (n + 2)) = m * (n + 2) + 1 := by
  have h := minDeg_lexProduct (G := complete (m + 1)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [minDeg_complete, minDeg_path, V_path] at h
  simpa using h

/-! ### The join of a path with a cycle -/

theorem maxDeg_join_path_cycle (m n : ℕ) :
    maxDeg (path (m + 3) ∇g cycle (n + 3)) = max (n + 5) (m + 5) := by
  have h := maxDeg_join (G := path (m + 3)) (H := cycle (n + 3))
    (by rw [V_path]; omega) (by rw [V_cycle]; omega)
  rw [maxDeg_path, maxDeg_cycle, V_path, V_cycle] at h
  rw [h]
  omega

theorem minDeg_join_path_cycle (m n : ℕ) :
    minDeg (path (m + 2) ∇g cycle (n + 3)) = min (n + 4) (m + 4) := by
  have h := minDeg_join (G := path (m + 2)) (H := cycle (n + 3))
    (by rw [V_path]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_path, minDeg_cycle, V_path, V_cycle] at h
  rw [h]
  omega

/-! ### The Mycielskian of a cycle -/

theorem E_mycielskian_cycle (m : ℕ) : (mycielskian (cycle (m + 3))).E = 4 * (m + 3) := by
  rw [E_mycielskian, E_cycle, V_cycle]
  omega

theorem maxDeg_mycielskian_cycle (m : ℕ) :
    maxDeg (mycielskian (cycle (m + 3))) = max 4 (m + 3) := by
  have h := maxDeg_mycielskian (cycle (m + 3))
  rw [maxDeg_cycle, V_cycle] at h
  omega

theorem minDeg_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 3))).minDeg = min 3 (m + 3) := by
  have h := minDeg_mycielskian (cycle (m + 3)) (by rw [V_cycle]; omega)
  rw [minDeg_cycle, V_cycle] at h
  omega

/-! ### The Mycielskian of a path -/

theorem E_mycielskian_path (m : ℕ) : (mycielskian (path (m + 1))).E = 4 * m + 1 := by
  rw [E_mycielskian, E_path, V_path]
  omega

theorem maxDeg_mycielskian_path (m : ℕ) :
    maxDeg (mycielskian (path (m + 3))) = max 4 (m + 3) := by
  have h := maxDeg_mycielskian (path (m + 3))
  rw [maxDeg_path, V_path] at h
  omega

theorem minDeg_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 2))).minDeg = min 2 (m + 2) := by
  have h := minDeg_mycielskian (path (m + 2)) (by rw [V_path]; omega)
  rw [minDeg_path, V_path] at h
  omega

theorem maxDeg_mycielskian_complete (m : ℕ) :
    maxDeg (mycielskian (complete m)) = max (2 * (m - 1)) m := by
  have h := maxDeg_mycielskian (complete m)
  rw [maxDeg_complete, V_complete] at h
  omega

theorem minDeg_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 1))).minDeg = min (2 * m) (m + 1) := by
  have h := minDeg_mycielskian (complete (m + 1)) (by rw [V_complete]; omega)
  rw [minDeg_complete, V_complete] at h
  omega

theorem maxDeg_join_path_complete (m n : ℕ) :
    maxDeg (path (m + 3) ∇g complete (n + 1)) = max (n + 3) (m + 3 + n) := by
  have h := maxDeg_join (G := path (m + 3)) (H := complete (n + 1))
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [maxDeg_path, maxDeg_complete, V_path, V_complete] at h
  omega

theorem minDeg_join_path_complete (m n : ℕ) :
    minDeg (path (m + 2) ∇g complete (n + 1)) = min (n + 2) (m + 2 + n) := by
  have h := minDeg_join (G := path (m + 2)) (H := complete (n + 1))
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [minDeg_path, minDeg_complete, V_path, V_complete] at h
  omega

theorem maxDeg_join_cycle_complete (m n : ℕ) :
    maxDeg (cycle (m + 3) ∇g complete (n + 1)) = max (n + 3) (m + 3 + n) := by
  have h := maxDeg_join (G := cycle (m + 3)) (H := complete (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_complete]; omega)
  rw [maxDeg_cycle, maxDeg_complete, V_cycle, V_complete] at h
  omega

theorem minDeg_join_cycle_complete (m n : ℕ) :
    minDeg (cycle (m + 3) ∇g complete (n + 1)) = min (n + 3) (m + 3 + n) := by
  have h := minDeg_join (G := cycle (m + 3)) (H := complete (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_complete]; omega)
  rw [minDeg_cycle, minDeg_complete, V_cycle, V_complete] at h
  omega

theorem minDeg_disjUnion_path_cycle (m n : ℕ) :
    minDeg (path (m + 2) ⊕g cycle (n + 3)) = 1 := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := cycle (n + 3))
    (by rw [V_path]; omega) (by rw [V_cycle]; omega)
  rw [minDeg_path, minDeg_cycle] at h
  omega

theorem minDeg_disjUnion_path_complete (m n : ℕ) :
    minDeg (path (m + 2) ⊕g complete (n + 1)) = min 1 n := by
  have h := minDeg_disjUnion (G := path (m + 2)) (H := complete (n + 1))
    (by rw [V_path]; omega) (by rw [V_complete]; omega)
  rw [minDeg_path, minDeg_complete] at h
  omega

theorem minDeg_disjUnion_cycle_complete (m n : ℕ) :
    minDeg (cycle (m + 3) ⊕g complete (n + 1)) = min 2 n := by
  have h := minDeg_disjUnion (G := cycle (m + 3)) (H := complete (n + 1))
    (by rw [V_cycle]; omega) (by rw [V_complete]; omega)
  rw [minDeg_cycle, minDeg_complete] at h
  omega

/-! ### Edge positivity from connectivity -/

theorem E_pos_of_isConnected {G : IsoGraph} (h : IsConnected G) (hV : 2 ≤ G.V) : 0 < G.E :=
  E_pos_of_numComponents_lt_V (by rw [numComponents_eq_one_of_isConnected h]; omega)

end IsoGraph
