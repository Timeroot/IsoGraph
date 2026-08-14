import IsoGraph.Values.Identities.Concrete

/-!
# Extremal bounds, domination, and counting

The classical inequalities, at the `CGraph` level: greedy colouring and Nordhaus–Gaddum, Turán's
theorem, the Ramsey number `R(3, 3)`, Gallai's identity between the covering and independence
numbers, and the clique–coclique bound for vertex-transitive graphs.

Then the invariants that are defined by an optimisation and so need a witness in both directions —
the vertex cover number, the domination number, the radius — and the ones that are defined by a
count: cliques, independent sets, and connected components.
-/

set_option autoImplicit false

namespace CGraph

variable {G H : CGraph}

/-! ### Two graphs of girth five -/

/-- **The five-cycle has girth five.** -/
@[toIsoGraph]
theorem girth_cycle_five : (cycle 5).girth = 5 := by
  refine le_antisymm ?_ (five_le_girth (by decide) (by decide) (not_isAcyclic_cycle 2))
  exact girth_le_five_of_pentagon (a := (0 : Fin 5)) (b := (1 : Fin 5)) (c := (2 : Fin 5))
    (d := (3 : Fin 5)) (e := (4 : Fin 5))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))

/-- **The Petersen graph has girth five**: it is strongly regular with `ℓ = 0` and `μ = 1`, so it
has neither a triangle nor a square, and its outer five-cycle realises the bound. -/
theorem girth_kneser_five_two : (kneser 5 2).girth = 5 := by
  have hpent := girth_le_five_of_pentagon (G := kneser 5 2)
    (a := (⟨{0, 1}, by decide⟩ : {s : Finset (Fin 5) // s.card = 2}))
    (b := ⟨{2, 3}, by decide⟩) (c := ⟨{4, 0}, by decide⟩)
    (d := ⟨{1, 2}, by decide⟩) (e := ⟨{3, 4}, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide))
  have hnac := not_isAcyclic_of_pentagon (G := kneser 5 2)
    (a := (⟨{0, 1}, by decide⟩ : {s : Finset (Fin 5) // s.card = 2}))
    (b := ⟨{2, 3}, by decide⟩) (c := ⟨{4, 0}, by decide⟩)
    (d := ⟨{1, 2}, by decide⟩) (e := ⟨{3, 4}, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide))
  exact le_antisymm hpent ((isSRGWith_kneser_two 5).five_le_girth hnac)

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

/-! ### Maximum and minimum degree -/

/-! ### Basic API -/

theorem degree_le_maxDeg (G : CGraph) (v : G.V) : G.toSimple.degree v ≤ G.maxDeg :=
  SimpleGraph.degree_le_maxDegree _ v

theorem minDeg_le_degree (G : CGraph) (v : G.V) : G.minDeg ≤ G.toSimple.degree v :=
  SimpleGraph.minDegree_le_degree _ v

/-- **Arc-transitive graphs with no isolated vertex are vertex-transitive.**  Given `u` and `v`,
pick any neighbours `u'` and `v'` and carry the arc `u → u'` to the arc `v → v'`.  Phrased with
`0 < δ` rather than "no isolated vertices" so that it transfers to `IsoGraph`. -/
@[toIsoGraph IsArcTransitive.isVertexTransitive]
theorem isVertexTransitive_of_isArcTransitive_of_minDeg_pos {G : CGraph} (h : G.IsArcTransitive)
    (hδ : 0 < G.minDeg) : G.IsVertexTransitive := by
  refine isVertexTransitive_of_isArcTransitive G (fun u ↦ ?_) h
  have hd : 0 < G.toSimple.degree u := lt_of_lt_of_le hδ (minDeg_le_degree G u)
  obtain ⟨v, hv⟩ := (SimpleGraph.degree_pos_iff_exists_adj G.toSimple u).1 hd
  exact ⟨v, hv⟩

theorem maxDeg_le_of_forall {G : CGraph} {k : ℕ} (h : ∀ v, G.toSimple.degree v ≤ k) :
    G.maxDeg ≤ k :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ k h

theorem le_minDeg_of_forall {G : CGraph} {k : ℕ} (v₀ : G.V)
    (h : ∀ v, k ≤ G.toSimple.degree v) : k ≤ G.minDeg :=
  haveI : Nonempty G.V := ⟨v₀⟩
  SimpleGraph.le_minDegree_of_forall_le_degree _ k h

theorem exists_degree_eq_maxDeg (G : CGraph) (v₀ : G.V) :
    ∃ v : G.V, G.toSimple.degree v = G.maxDeg := by
  haveI : Nonempty G.V := ⟨v₀⟩
  obtain ⟨v, hv⟩ := SimpleGraph.exists_maximal_degree_vertex G.toSimple
  exact ⟨v, hv.symm⟩

theorem exists_degree_eq_minDeg (G : CGraph) (v₀ : G.V) :
    ∃ v : G.V, G.toSimple.degree v = G.minDeg := by
  haveI : Nonempty G.V := ⟨v₀⟩
  obtain ⟨v, hv⟩ := SimpleGraph.exists_minimal_degree_vertex G.toSimple
  exact ⟨v, hv.symm⟩

@[toIsoGraph]
theorem minDeg_le_maxDeg (G : CGraph) : G.minDeg ≤ G.maxDeg :=
  SimpleGraph.minDegree_le_maxDegree _

@[toIsoGraph maxDeg_lt_V]
theorem maxDeg_lt_card {G : CGraph} [Nonempty G.V] : G.maxDeg < Fintype.card G.V :=
  SimpleGraph.maxDegree_lt_card_verts _

theorem mem_degMultiset {G : CGraph} {d : ℕ} :
    d ∈ G.degMultiset ↔ ∃ v : G.V, G.toSimple.degree v = d := by
  unfold degMultiset
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, Finset.mem_univ_val v, hv⟩

/-- **A bound on every entry of the degree multiset bounds the maximum degree.** -/
@[toIsoGraph]
theorem maxDeg_le_of_degMultiset {G : CGraph} {k : ℕ} (h : ∀ d ∈ G.degMultiset, d ≤ k) :
    G.maxDeg ≤ k :=
  maxDeg_le_of_forall fun v ↦ h _ (mem_degMultiset.2 ⟨v, rfl⟩)

/-- The maximum degree is the largest entry of the degree multiset. -/
@[toIsoGraph]
theorem maxDeg_eq_sup (G : CGraph) : G.maxDeg = G.degMultiset.sup := by
  refine le_antisymm ?_ (Multiset.sup_le.2 fun d hd ↦ ?_)
  · rcases isEmpty_or_nonempty G.V with h | h
    · rw [maxDeg, SimpleGraph.maxDegree_of_isEmpty]
      exact Nat.zero_le _
    · obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg h.some
      exact hv ▸ Multiset.le_sup (mem_degMultiset.2 ⟨v, rfl⟩)
  · obtain ⟨v, hv⟩ := mem_degMultiset.1 hd
    exact hv ▸ G.degree_le_maxDeg v

@[toIsoGraph]
theorem maxDeg_eq_of_degMultiset {G : CGraph} {k : ℕ} (hmem : k ∈ G.degMultiset)
    (hle : ∀ d ∈ G.degMultiset, d ≤ k) : G.maxDeg = k := by
  obtain ⟨v, hv⟩ := mem_degMultiset.1 hmem
  exact le_antisymm (maxDeg_le_of_forall fun w ↦ hle _ (mem_degMultiset.2 ⟨w, rfl⟩))
    (hv ▸ G.degree_le_maxDeg v)

@[toIsoGraph]
theorem minDeg_eq_of_degMultiset {G : CGraph} {k : ℕ} (hmem : k ∈ G.degMultiset)
    (hle : ∀ d ∈ G.degMultiset, k ≤ d) : G.minDeg = k := by
  obtain ⟨v, hv⟩ := mem_degMultiset.1 hmem
  exact le_antisymm (hv ▸ G.minDeg_le_degree v)
    (le_minDeg_of_forall v fun w ↦ hle _ (mem_degMultiset.2 ⟨w, rfl⟩))

/-- Half the handshake lemma: the degree sum is squeezed between `|V|·δ` and `|V|·Δ`. -/
@[toIsoGraph V_mul_minDeg_le]
theorem card_mul_minDeg_le (G : CGraph) : Fintype.card G.V * G.minDeg ≤ 2 * G.E := by
  calc Fintype.card G.V * G.minDeg = ∑ _v : G.V, G.minDeg := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ v : G.V, G.toSimple.degree v := Finset.sum_le_sum fun v _ ↦ G.minDeg_le_degree v
    _ = 2 * G.E := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple

@[toIsoGraph two_mul_E_le_V_mul_maxDeg]
theorem two_mul_E_le_card_mul_maxDeg (G : CGraph) : 2 * G.E ≤ Fintype.card G.V * G.maxDeg := by
  calc 2 * G.E = ∑ v : G.V, G.toSimple.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple).symm
    _ ≤ ∑ _v : G.V, G.maxDeg := Finset.sum_le_sum fun v _ ↦ G.degree_le_maxDeg v
    _ = Fintype.card G.V * G.maxDeg := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- One vertex's degree is at most the whole degree sum, so `Δ ≤ 2|E|`; in particular a graph
with no edges has no vertex of positive degree. -/
@[toIsoGraph]
theorem maxDeg_le_two_mul_E {G : CGraph} [Nonempty G.V] : G.maxDeg ≤ 2 * G.E := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  calc G.maxDeg = G.toSimple.degree v := hv.symm
    _ ≤ ∑ u : G.V, G.toSimple.degree u :=
        Finset.single_le_sum (f := fun u : G.V ↦ G.toSimple.degree u)
          (fun u _ ↦ Nat.zero_le _) (Finset.mem_univ v)
    _ = 2 * G.E := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple

/-! ### The disjoint union, the join and the complement -/

@[toIsoGraph]
theorem maxDeg_disjUnion (G H : CGraph) :
    (disjUnion G H).maxDeg = max G.maxDeg H.maxDeg := by
  refine le_antisymm (maxDeg_le_of_forall ?_) (max_le ?_ ?_)
  · rintro (a | b)
    · rw [degree_disjUnion_inl]; exact le_max_of_le_left (G.degree_le_maxDeg a)
    · rw [degree_disjUnion_inr]; exact le_max_of_le_right (H.degree_le_maxDeg b)
  · refine maxDeg_le_of_forall fun a ↦ ?_
    rw [← degree_disjUnion_inl G H a]
    exact degree_le_maxDeg _ _
  · refine maxDeg_le_of_forall fun b ↦ ?_
    rw [← degree_disjUnion_inr G H b]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_disjUnion {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (disjUnion G H).minDeg = min G.minDeg H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  refine le_antisymm (le_min ?_ ?_) (le_minDeg_of_forall (Sum.inl a₀) ?_)
  · rw [← ha, ← degree_disjUnion_inl G H a]
    exact minDeg_le_degree _ _
  · rw [← hb, ← degree_disjUnion_inr G H b]
    exact minDeg_le_degree _ _
  · rintro (a | b)
    · rw [degree_disjUnion_inl]; exact le_trans (min_le_left _ _) (G.minDeg_le_degree a)
    · rw [degree_disjUnion_inr]; exact le_trans (min_le_right _ _) (H.minDeg_le_degree b)

@[toIsoGraph]
theorem maxDeg_join {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (join G H).maxDeg
      = max (G.maxDeg + Fintype.card H.V) (Fintype.card G.V + H.maxDeg) := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  refine le_antisymm (maxDeg_le_of_forall ?_) (max_le ?_ ?_)
  · rintro (a' | b')
    · rw [degree_join_inl]
      exact le_max_of_le_left (Nat.add_le_add_right (G.degree_le_maxDeg a') _)
    · rw [degree_join_inr]
      exact le_max_of_le_right (Nat.add_le_add_left (H.degree_le_maxDeg b') _)
  · rw [← ha, ← degree_join_inl G H a]
    exact degree_le_maxDeg _ _
  · rw [← hb, ← degree_join_inr G H b]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_join {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (join G H).minDeg
      = min (G.minDeg + Fintype.card H.V) (Fintype.card G.V + H.minDeg) := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  refine le_antisymm (le_min ?_ ?_) (le_minDeg_of_forall (Sum.inl a₀) ?_)
  · rw [← ha, ← degree_join_inl G H a]
    exact minDeg_le_degree _ _
  · rw [← hb, ← degree_join_inr G H b]
    exact minDeg_le_degree _ _
  · rintro (a' | b')
    · rw [degree_join_inl]
      exact le_trans (min_le_left _ _) (Nat.add_le_add_right (G.minDeg_le_degree a') _)
    · rw [degree_join_inr]
      exact le_trans (min_le_right _ _) (Nat.add_le_add_left (H.minDeg_le_degree b') _)

/-- **Complementation swaps the two extreme degrees.** -/
@[toIsoGraph]
theorem maxDeg_compl {G : CGraph} [Nonempty G.V] :
    Gᶜ.maxDeg = Fintype.card G.V - 1 - G.minDeg := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  obtain ⟨v, hv⟩ := G.exists_degree_eq_minDeg v₀
  refine le_antisymm (maxDeg_le_of_forall fun w ↦ ?_) ?_
  · rw [degree_compl]
    exact Nat.sub_le_sub_left (G.minDeg_le_degree w) _
  · rw [← hv, ← degree_compl]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_compl {G : CGraph} [Nonempty G.V] :
    Gᶜ.minDeg = Fintype.card G.V - 1 - G.maxDeg := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  refine le_antisymm ?_ (le_minDeg_of_forall v₀ fun w ↦ ?_)
  · rw [← hv, ← degree_compl]
    exact minDeg_le_degree _ _
  · rw [degree_compl]
    exact Nat.sub_le_sub_left (G.degree_le_maxDeg w) _

/-! ### The four products -/

@[toIsoGraph]
theorem maxDeg_cartesianProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (cartesianProduct G H).maxDeg = G.maxDeg + H.maxDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_cartesianProduct G H ((a, b) : (cartesianProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_cartesianProduct]
    exact Nat.add_le_add (G.degree_le_maxDeg _) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_cartesianProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (cartesianProduct G H).minDeg = G.minDeg + H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_cartesianProduct G H ((a, b) : (cartesianProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (cartesianProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_cartesianProduct]
    exact Nat.add_le_add (G.minDeg_le_degree _) (H.minDeg_le_degree _)

@[toIsoGraph]
theorem maxDeg_tensorProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (tensorProduct G H).maxDeg = G.maxDeg * H.maxDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_tensorProduct G H ((a, b) : (tensorProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_tensorProduct]
    exact Nat.mul_le_mul (G.degree_le_maxDeg _) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_tensorProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (tensorProduct G H).minDeg = G.minDeg * H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_tensorProduct G H ((a, b) : (tensorProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (tensorProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_tensorProduct]
    exact Nat.mul_le_mul (G.minDeg_le_degree _) (H.minDeg_le_degree _)

@[toIsoGraph]
theorem maxDeg_lexProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (lexProduct G H).maxDeg = G.maxDeg * Fintype.card H.V + H.maxDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_lexProduct G H ((a, b) : (lexProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_lexProduct]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (G.degree_le_maxDeg _)) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_lexProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (lexProduct G H).minDeg = G.minDeg * Fintype.card H.V + H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_lexProduct G H ((a, b) : (lexProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (lexProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_lexProduct]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (G.minDeg_le_degree _)) (H.minDeg_le_degree _)

@[toIsoGraph]
theorem maxDeg_strongProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (strongProduct G H).maxDeg = (G.maxDeg + 1) * (H.maxDeg + 1) - 1 := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_strongProduct G H ((a, b) : (strongProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_strongProduct]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul (Nat.add_le_add_right (G.degree_le_maxDeg _) _)
      (Nat.add_le_add_right (H.degree_le_maxDeg _) _)) 1
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_strongProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (strongProduct G H).minDeg = (G.minDeg + 1) * (H.minDeg + 1) - 1 := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_strongProduct G H ((a, b) : (strongProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (strongProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_strongProduct]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul (Nat.add_le_add_right (G.minDeg_le_degree _) _)
      (Nat.add_le_add_right (H.minDeg_le_degree _) _)) 1

/-! ### Greedy colouring and Nordhaus–Gaddum -/

section Greedy

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

end Greedy

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

/-- Independence version of the greedy bound: `|V| ≤ (Δ + 1)·α`. -/
@[toIsoGraph V_le_maxDeg_add_one_mul_indepNum]
theorem card_le_maxDeg_add_one_mul_indepNum (G : CGraph) :
    Fintype.card G.V ≤ (G.maxDeg + 1) * G.indepNum :=
  le_trans G.card_le_chromNum_mul_indepNum
    (Nat.mul_le_mul_right _ G.chromNum_le_maxDeg_add_one)

/-! ### Colouring around a maximum independent set -/

/-- Colour a maximum independent set with a single colour and every other vertex with its own:
`χ ≤ |V| - α + 1`. -/
@[toIsoGraph chromNum_le_V_sub_indepNum_add_one]
theorem chromNum_le_card_sub_indepNum_add_one (G : CGraph) :
    G.chromNum ≤ Fintype.card G.V - G.indepNum + 1 := by
  classical
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcard' : s.card = G.indepNum := hcard
  have hcompl : Fintype.card {v : G.V // v ∉ s} = Fintype.card G.V - G.indepNum := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hcard']
  obtain ⟨e⟩ : Nonempty ({v : G.V // v ∉ s} ≃ Fin (Fintype.card G.V - G.indepNum)) :=
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
    G.chromNum + G.indepNum ≤ Fintype.card G.V + 1 := by
  have h := G.chromNum_le_card_sub_indepNum_add_one
  have h2 : G.indepNum ≤ Fintype.card G.V := by
    obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
    have hcard' : G.indepNum = s.card := hcard.symm
    rw [hcard', ← Finset.card_univ]
    exact Finset.card_le_univ s
  omega

section NordhausGaddum

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

end NordhausGaddum

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
    G.chromNum + Gᶜ.chromNum ≤ Fintype.card G.V + 1 := by
  have h := chromOn_add_chromOn_compl_le G.toSimple (Finset.univ : Finset G.V)
  rw [Finset.card_univ] at h
  rwa [G.chromNum_eq_chromOn_univ, show Gᶜ.chromNum = chromOn G.toSimpleᶜ Finset.univ from
    by rw [Gᶜ.chromNum_eq_chromOn_univ, compl_toSimple]]

section Turan

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Being `n`-clique-free is the same as having clique number below `n`. -/
private theorem cliqueFree_iff_cliqueNum_lt {S : SimpleGraph X} {n : ℕ} :
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
private theorem mul_card_edgeFinset_le_of_cliqueFree {S : SimpleGraph X} [DecidableRel S.Adj]
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

end Turan

/-! ### Turán's theorem -/

/-- **Turán's theorem**: a graph whose clique number is at most `r` has `2r·|E| ≤ (r - 1)·|V|²`
edges. -/
@[toIsoGraph]
theorem two_mul_mul_E_le (G : CGraph) {r : ℕ} (hr : 0 < r) (h : G.cliqueNum ≤ r) :
    2 * r * G.E ≤ (r - 1) * (Fintype.card G.V) ^ 2 :=
  mul_card_edgeFinset_le_of_cliqueFree hr
    (cliqueFree_iff_cliqueNum_lt.2 (Nat.lt_succ_of_le h))

/-- **Mantel's theorem**: a triangle-free graph has at most `|V|²/4` edges. -/
theorem four_mul_E_le_card_sq (G : CGraph) (h : G.cliqueNum ≤ 2) :
    4 * G.E ≤ (Fintype.card G.V) ^ 2 := by
  have := G.two_mul_mul_E_le (r := 2) (by omega) h
  omega

/-- **A bipartite graph is triangle-free**, hence has clique number at most two. -/
@[toIsoGraph]
theorem cliqueNum_le_two_of_isBipartite {G : CGraph} (hb : G.IsBipartite) : G.cliqueNum ≤ 2 := by
  classical
  by_contra hcon
  obtain ⟨s, hs⟩ := G.toSimple.exists_isNClique_cliqueNum
  obtain ⟨t, hts, htc⟩ :=
    Finset.exists_subset_card_eq (n := 3)
      (show 3 ≤ s.card by rw [hs.card_eq]; exact Nat.not_le.1 hcon)
  have hcl : G.toSimple.IsNClique 3 t := ⟨hs.isClique.subset (by exact_mod_cast hts), htc⟩
  obtain ⟨x, y, z, -, -, -, rfl⟩ := Finset.card_eq_three.1 htc
  rw [SimpleGraph.is3Clique_triple_iff] at hcl
  exact not_isBipartite_of_triangle ((toSimple_adj _ _ _).1 hcl.1)
    ((toSimple_adj _ _ _).1 hcl.2.1) ((toSimple_adj _ _ _).1 hcl.2.2) hb

/-- Contrapositive of Mantel: a graph with more than `|V|²/4` edges has a triangle. -/
theorem three_le_cliqueNum_of_card_sq_lt (G : CGraph)
    (h : (Fintype.card G.V) ^ 2 < 4 * G.E) : 3 ≤ G.cliqueNum := by
  by_contra hcon
  exact absurd (G.four_mul_E_le_card_sq (by omega)) (by omega)

section Ramsey

variable {X : Type} [Fintype X] [DecidableEq X]

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

end Ramsey

/-! ### The Ramsey number `R(3, 3)` -/

/-- **`R(3, 3) ≤ 6`**: any graph on at least six vertices has three mutually adjacent vertices or
three mutually non-adjacent ones. -/
@[toIsoGraph]
theorem three_le_cliqueNum_or_three_le_indepNum (G : CGraph) (h : 6 ≤ Fintype.card G.V) :
    3 ≤ G.cliqueNum ∨ 3 ≤ G.indepNum := by
  classical
  have := three_le_cliqueNum_or_compl G.toSimple h
  rwa [SimpleGraph.cliqueNum_compl] at this

/-- Triangle-free form: a triangle-free graph on six or more vertices has three pairwise
non-adjacent vertices. -/
@[toIsoGraph]
theorem three_le_indepNum_of_cliqueNum_le_two (G : CGraph) (h : 6 ≤ Fintype.card G.V)
    (hcl : G.cliqueNum ≤ 2) : 3 ≤ G.indepNum := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · omega
  · exact h'

/-! ### Ramsey numbers in general -/

/-- **Ramsey's theorem**, `R(s, t) ≤ C(s + t, s)`: a graph on at least `C(s + t, s)` vertices has
a clique on `s` vertices or an independent set on `t` vertices. -/
@[toIsoGraph]
theorem le_cliqueNum_or_le_indepNum (G : CGraph) {s t : ℕ}
    (h : (s + t).choose s ≤ Fintype.card G.V) : s ≤ G.cliqueNum ∨ t ≤ G.indepNum := by
  classical
  rcases exists_clique_or_clique_compl G.toSimple s t Finset.univ
      (by rwa [Finset.card_univ]) with ⟨c, -, hcl, hcard⟩ | ⟨c, -, hcl, hcard⟩
  · exact Or.inl (hcard ▸ hcl.card_le_cliqueNum)
  · refine Or.inr ?_
    have := hcl.card_le_cliqueNum
    rw [hcard, SimpleGraph.cliqueNum_compl] at this
    exact this

section Gallai

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
private theorem card_edgeFinset_le_vertexCoverNum_mul_maxDegree (S : SimpleGraph X)
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

end Gallai

/-! ### The vertex cover number -/

/-- **Gallai's identity**: a set of vertices is a vertex cover exactly when its complement is
independent, so `τ(G) + α(G) = |V|`. -/
@[toIsoGraph]
theorem coverNum_add_indepNum (G : CGraph) :
    G.coverNum + G.indepNum = Fintype.card G.V := by
  classical
  exact vertexCoverNum_toNat_add_indepNum G.toSimple

/-- **`|E| ≤ τ·Δ`**: each of the `τ` cover vertices takes care of at most `Δ` edges. -/
@[toIsoGraph]
theorem E_le_coverNum_mul_maxDeg (G : CGraph) : G.E ≤ G.coverNum * G.maxDeg := by
  classical
  exact card_edgeFinset_le_vertexCoverNum_mul_maxDegree G.toSimple

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
    G.indepNum < Fintype.card G.V := by
  classical
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos h
  obtain ⟨s, hs⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcards : s.card = G.indepNum := hs.card_eq
  have hle : G.indepNum ≤ Fintype.card G.V := by
    rw [← hcards, ← Finset.card_univ]
    exact Finset.card_le_univ s
  rcases Nat.lt_or_ge G.indepNum (Fintype.card G.V) with h' | h'
  · exact h'
  · exfalso
    have huniv : s = Finset.univ := Finset.eq_univ_of_card s (by rw [hcards]; omega)
    have hmem : ∀ x : G.V, x ∈ (s : Set G.V) := by
      intro x
      rw [huniv]
      simp
    exact hs.isIndepSet (hmem a) (hmem b) ((toSimple_adj _ _ _).2 hab).ne
      ((toSimple_adj _ _ _).2 hab)

section CliqueCoclique

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

end CliqueCoclique

/-! ### The clique–coclique bound -/

/-- **The clique–coclique bound**: in a vertex-transitive graph, `α · ω ≤ |V|`.

The proof is a double count of the pairs `(σ, c)` with `σ` an automorphism, `c` a vertex of a
fixed maximum clique `C`, and `σ c` in a fixed maximum independent set `S`.  For each `σ` there
is at most one such `c`, since `σ C` is a clique and `S` is independent; on the other hand each
of the `|C| · |S|` pairs `(c, v)` is realised by exactly `|Aut G| / |V|` automorphisms, because
the action is transitive. -/
@[toIsoGraph indepNum_mul_cliqueNum_le_V]
theorem indepNum_mul_cliqueNum_le_card (G : CGraph) (hvt : G.IsVertexTransitive) :
    G.indepNum * G.cliqueNum ≤ Fintype.card G.V := by
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
  have hcard : Γ.card = Fintype.card G.V * m := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := fun σ : Equiv.Perm G.V ↦ σ c₀) (s := Γ) (t := Finset.univ)
      (fun x _ ↦ Finset.mem_univ _)
    rw [this]
    rw [Finset.sum_congr rfl fun v _ ↦ hfib c₀ v, Finset.sum_const, Finset.card_univ,
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
  have hfinal : S.card * C.card * m ≤ Fintype.card G.V * m := by
    calc S.card * C.card * m = C.card * (S.card * m) := by ring
      _ = N := hlower.symm
      _ ≤ Γ.card := hupper
      _ = Fintype.card G.V * m := hcard
  have := Nat.le_of_mul_le_mul_right hfinal hmpos
  rwa [hScard, hCcard] at this

/-- A graph with `α · ω > |V|` cannot be vertex-transitive. -/
theorem not_isVertexTransitive_of_card_lt (G : CGraph)
    (h : Fintype.card G.V < G.indepNum * G.cliqueNum) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.indepNum_mul_cliqueNum_le_card hvt) (by omega)

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
theorem domNum_le_card (G : CGraph) : G.domNum ≤ Fintype.card G.V := by
  have := domNum_le_card_of_isDominatingSet (isDominatingSet_univ G)
  rwa [Finset.card_univ] at this

@[simp, toIsoGraph]
theorem domNum_eq_zero_iff (G : CGraph) :
    G.domNum = 0 ↔ Fintype.card G.V = 0 := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
    rw [h, Finset.card_eq_zero] at hcard
    subst hcard
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun v ↦ ?_⟩
    rcases hs v with hv | ⟨u, hu, -⟩
    · simp at hv
    · simp at hu
  · intro h
    have := G.domNum_le_card
    omega

@[toIsoGraph]
theorem domNum_pos (G : CGraph) (h : 0 < Fintype.card G.V) : 0 < G.domNum := by
  have := (G.domNum_eq_zero_iff).not.2 (by omega : ¬ Fintype.card G.V = 0)
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
  have h2 : 0 < Fintype.card G.V := Fintype.card_pos_iff.2 ⟨v⟩
  have := G.domNum_pos h2
  omega

/-- **The degree bound** `|V| ≤ γ·(Δ + 1)`: each vertex of a dominating set covers itself and at
most `Δ` neighbours. -/
@[toIsoGraph V_le_domNum_mul_maxDeg_add_one]
theorem card_le_domNum_mul_maxDeg_add_one (G : CGraph) :
    Fintype.card G.V ≤ G.domNum * (G.maxDeg + 1) := by
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
  rw [Finset.card_univ] at h1
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
theorem domNum_add_maxDeg_le_card (G : CGraph) : G.domNum + G.maxDeg ≤ Fintype.card G.V := by
  classical
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : Fintype.card G.V = 0 := Fintype.card_eq_zero
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
  have hcardT : T.card = Fintype.card G.V - G.maxDeg := by
    rw [hT, Finset.card_univ_diff, SimpleGraph.card_neighborFinset_eq_degree, hv]
  have h1 := domNum_le_card_of_isDominatingSet hdom
  have h2 : G.maxDeg < Fintype.card G.V := @maxDeg_lt_card G ⟨v₀⟩
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
    rw [huniv, Finset.card_univ, card_empty] at hcard
    omega

@[toIsoGraph]
theorem domNum_complete (n : ℕ) : (complete (n + 1)).domNum = 1 :=
  domNum_eq_one_of_universal (v := (0 : Fin (n + 1))) fun u hu ↦ by
    simpa using Ne.symm hu

@[toIsoGraph]
theorem domNum_star (n : ℕ) : (star n).domNum = 1 := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  refine domNum_eq_one_of_universal (v := (Sum.inl 0 : Fin 1 ⊕ Fin n)) fun u hu ↦ ?_
  match u with
  | Sum.inl a => exact absurd (congrArg Sum.inl (Subsingleton.elim a (0 : Fin 1))) hu
  | Sum.inr b => exact bipartite_adj_inl_inr 1 n 0 b

/-! ### The radius -/

/-- The most central vertex is no further from the rest than the least central one. -/
@[toIsoGraph]
theorem radius_le_diameter (G : CGraph) : G.radius ≤ G.diameter := by
  by_cases hc : G.toSimple.Connected
  · haveI : Nonempty G.V := hc.nonempty
    have hd : G.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hc
    exact ENat.toNat_le_toNat SimpleGraph.radius_le_ediam hd
  · have h : G.toSimple.radius = ⊤ := SimpleGraph.radius_eq_top_of_not_connected hc
    simp [radius, h]

/-- Walking through a central vertex crosses the graph in at most `2r` steps. -/
@[toIsoGraph]
theorem diameter_le_two_mul_radius (G : CGraph) : G.diameter ≤ 2 * G.radius := by
  by_cases hc : G.toSimple.Connected
  · haveI : Nonempty G.V := hc.nonempty
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 (SimpleGraph.radius_ne_top_iff.2 hc)
    have h := SimpleGraph.ediam_le_two_mul_radius (G := G.toSimple)
    rw [← hr] at h
    have h2 : G.toSimple.ediam ≤ ((2 * r : ℕ) : ℕ∞) := by
      rwa [Nat.cast_mul, Nat.cast_ofNat]
    have h3 := ENat.toNat_le_toNat h2 (ENat.coe_ne_top _)
    simpa [radius, ← hr] using h3
  · have h : G.toSimple.diam = 0 := SimpleGraph.diam_eq_zero_of_not_connected hc
    simp [diameter, h]

@[toIsoGraph]
theorem radius_pos (G : CGraph) (hc : G.IsConnected) (hV : 1 < Fintype.card G.V) :
    0 < G.radius := by
  haveI : Nonempty G.V := hc.nonempty
  haveI : Nontrivial G.V := Fintype.one_lt_card_iff_nontrivial.1 hV
  have h0 : G.toSimple.radius ≠ 0 := SimpleGraph.radius_ne_zero_of_nontrivial
  have ht : G.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hc
  have : G.radius ≠ 0 := by
    simp only [radius, ne_eq, ENat.toNat_eq_zero]
    tauto
  omega

/-- A vertex adjacent to everything else is at distance one from the rest, so it makes the
radius `1` — provided there is something else. -/
theorem radius_eq_one_of_universal {v : G.V} (h : ∀ u, u ≠ v → G.Adj v u)
    (hV : 1 < Fintype.card G.V) : G.radius = 1 := by
  haveI : Nontrivial G.V := Fintype.one_lt_card_iff_nontrivial.1 hV
  have hle : G.toSimple.eccent v ≤ 1 :=
    (SimpleGraph.eccent_le_one_iff v).2 fun u hu ↦ (toSimple_adj _ _ _).2 (h u (Ne.symm hu))
  have h1 : G.toSimple.radius ≤ 1 := le_trans SimpleGraph.radius_le_eccent hle
  have h0 : G.toSimple.radius ≠ 0 := SimpleGraph.radius_ne_zero_of_nontrivial
  have : G.toSimple.radius = 1 := le_antisymm h1 (ENat.one_le_iff_ne_zero.2 h0)
  simp [radius, this]

/-- Conversely, radius `1` produces a vertex adjacent to everything else. -/
theorem exists_universal_of_radius_eq_one (G : CGraph) (h : G.radius = 1) :
    ∃ v : G.V, ∀ u, u ≠ v → G.Adj v u := by
  have hne : G.toSimple.radius ≠ ⊤ := by
    intro htop
    rw [radius, htop] at h
    simp at h
  haveI : Nonempty G.V := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hne SimpleGraph.radius_eq_top_of_isEmpty
  obtain ⟨v, hv⟩ := SimpleGraph.exists_eccent_eq_radius (G := G.toSimple)
  refine ⟨v, fun u hu ↦ ?_⟩
  have h1 : G.toSimple.radius = 1 := by
    rw [radius] at h
    rcases ENat.ne_top_iff_exists.1 hne with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [ENat.toNat_coe] at h
    rw [h]
    rfl
  have : G.toSimple.eccent v ≤ 1 := by rw [hv, h1]
  exact (toSimple_adj _ _ _).1 ((SimpleGraph.eccent_le_one_iff v).1 this u (Ne.symm hu))

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
    (join (complete 1) G).domNum = 1 := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  haveI : Subsingleton ((complete 1)ᶜ).V := inferInstanceAs (Subsingleton (Fin 1))
  refine domNum_eq_one_of_universal
    (v := (Sum.inl (0 : Fin 1) : (join (complete 1) G).V)) fun u hu ↦ ?_
  rcases u with a | b
  · exact absurd (congrArg Sum.inl (Subsingleton.elim a (0 : Fin 1))) hu
  · exact join_adj_inl_inr (complete 1) G _ b

@[toIsoGraph]
theorem domNum_wheel (n : ℕ) : (wheel n).domNum = 1 := domNum_join_complete_one (cycle n)

/-- **Radius one and domination number one are the same condition** on a graph with at least two
vertices: both say that some vertex sees the whole graph. -/
@[toIsoGraph]
theorem radius_eq_one_iff_domNum_eq_one (G : CGraph) (hV : 1 < Fintype.card G.V) :
    G.radius = 1 ↔ G.domNum = 1 := by
  rw [domNum_eq_one_iff]
  exact ⟨G.exists_universal_of_radius_eq_one, fun ⟨_, hv⟩ ↦ radius_eq_one_of_universal hv hV⟩

/-- **A vertex-transitive graph has radius equal to its diameter**: every vertex is as central as
every other, so the least and the greatest eccentricity agree. -/
@[toIsoGraph]
theorem radius_eq_diameter_of_isVertexTransitive (G : CGraph) (h : G.IsVertexTransitive) :
    G.radius = G.diameter := by
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : G.toSimple.radius = ⊤ := SimpleGraph.radius_eq_top_of_isEmpty
    have h2 : G.toSimple.diam = 0 := by
      rw [SimpleGraph.diam_eq_zero]
      exact Or.inr (by infer_instance)
    simp [radius, diameter, h1, h2]
  · have key : G.toSimple.radius = G.toSimple.ediam := by
      rw [SimpleGraph.radius_eq_ediam_iff]
      refine ⟨G.toSimple.eccent Classical.ofNonempty, fun u ↦ ?_⟩
      obtain ⟨σ, hσ⟩ := h Classical.ofNonempty u
      rw [← hσ]
      exact (SimpleGraph.Iso.eccent_eq (CGraph.Iso.toSimpleIso σ) _).symm
    simp [radius, diameter, SimpleGraph.diam, key]

/-! ### Counting cliques

`cliqueCount n` counts the `n`-element cliques.  The first three values are forced — there is
one empty clique, `|V|` singletons and one clique per edge — and after that the count is tied to
the clique number: it vanishes exactly when `n` exceeds `ω(G)`. -/

@[simp, toIsoGraph] theorem cliqueCount_zero (G : CGraph) : G.cliqueCount 0 = 1 := by
  have h : G.toSimple.cliqueSet 0 = {∅} := by
    ext s
    simp
  rw [cliqueCount, h, Set.ncard_singleton]

@[simp, toIsoGraph] theorem cliqueCount_one (G : CGraph) : G.cliqueCount 1 = Fintype.card G.V := by
  have h : G.toSimple.cliqueSet 1 = (fun a : G.V ↦ ({a} : Finset G.V)) '' Set.univ := by
    ext s
    simp [eq_comm]
  rw [cliqueCount, h, Set.ncard_image_of_injective _ Finset.singleton_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The `2`-cliques are exactly the edges. -/
@[simp] theorem cliqueCount_two (G : CGraph) : G.cliqueCount 2 = G.E := by
  have h : G.toSimple.cliqueSet 2 = Sym2.toFinset '' G.toSimple.edgeSet := by
    ext s
    simp only [SimpleGraph.mem_cliqueSet_iff, Set.mem_image]
    constructor
    · rintro ⟨hcl, hcard⟩
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
      refine ⟨s(a, b), ?_, by rw [Sym2.toFinset_mk_eq]⟩
      exact hcl (by simp) (by simp) hab
    · rintro ⟨e, he, rfl⟩
      induction e with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        rw [Sym2.toFinset_mk_eq]
        refine ⟨?_, Finset.card_pair he.ne⟩
        simpa using SimpleGraph.isClique_pair.2 (fun _ ↦ he)
  have hinj : Set.InjOn Sym2.toFinset G.toSimple.edgeSet := by
    intro e₁ he₁ e₂ he₂ heq
    induction e₁ with
    | _ a b =>
      induction e₂ with
      | _ c d =>
        rw [SimpleGraph.mem_edgeSet] at he₁
        have ha : a ∈ Sym2.toFinset s(c, d) := by rw [← heq, Sym2.toFinset_mk_eq]; simp
        have hb : b ∈ Sym2.toFinset s(c, d) := by rw [← heq, Sym2.toFinset_mk_eq]; simp
        exact Sym2.eq_of_ne_mem he₁.ne (by simp) (by simp)
          (Sym2.mem_toFinset.1 ha) (Sym2.mem_toFinset.1 hb)
  rw [cliqueCount, h, hinj.ncard_image, E, SimpleGraph.edgeFinset,
    ← Set.ncard_eq_toFinset_card']

@[toIsoGraph]
theorem cliqueCount_eq_zero_iff (G : CGraph) (n : ℕ) : G.cliqueCount n = 0 ↔ G.cliqueNum < n := by
  rw [cliqueCount, Set.ncard_eq_zero (Set.toFinite _), SimpleGraph.cliqueSet_eq_empty_iff,
    cliqueFree_iff_cliqueNum_lt]
  rfl

@[toIsoGraph]
theorem cliqueCount_pos_iff (G : CGraph) (n : ℕ) : 0 < G.cliqueCount n ↔ n ≤ G.cliqueNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, cliqueCount_eq_zero_iff]
  omega

theorem cliqueCount_eq_zero_of_cliqueNum_lt {G : CGraph} {n : ℕ} (h : G.cliqueNum < n) :
    G.cliqueCount n = 0 :=
  (cliqueCount_eq_zero_iff G n).2 h

@[toIsoGraph]
theorem cliqueCount_le_choose (G : CGraph) (n : ℕ) :
    G.cliqueCount n ≤ (Fintype.card G.V).choose n := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset]
  exact SimpleGraph.card_cliqueFinset_le

theorem cliqueCount_eq_zero_of_card_lt {G : CGraph} {n : ℕ} (h : Fintype.card G.V < n) :
    G.cliqueCount n = 0 :=
  Nat.le_zero.1 ((cliqueCount_le_choose G n).trans (Nat.choose_eq_zero_of_lt h).le)

/-- A graph has a triangle exactly when its girth is three, so the triangle count vanishes
exactly when the girth is anything else. -/
@[toIsoGraph]
theorem cliqueCount_three_eq_zero_iff (G : CGraph) : G.cliqueCount 3 = 0 ↔ G.girth ≠ 3 := by
  rw [cliqueCount_eq_zero_iff, ne_eq, girth_eq_three_iff]
  omega

theorem cliqueCount_two_eq_zero_iff (G : CGraph) : G.cliqueCount 2 = 0 ↔ G.E = 0 := by
  classical
  rw [cliqueCount_two]

/-- A graph needs `n` colours before it can have an `n`-clique. -/
theorem cliqueCount_eq_zero_of_chromNum_lt {G : CGraph} {n : ℕ} (h : G.chromNum < n) :
    G.cliqueCount n = 0 :=
  cliqueCount_eq_zero_of_cliqueNum_lt (lt_of_le_of_lt (cliqueNum_le_chromNum G) h)

/-- Bipartite graphs are triangle-free. -/
@[toIsoGraph]
theorem cliqueCount_three_eq_zero_of_isBipartite {G : CGraph} (h : G.IsBipartite) :
    G.cliqueCount 3 = 0 :=
  cliqueCount_eq_zero_of_chromNum_lt
    (lt_of_le_of_lt (isBipartite_iff_chromNum_le_two.1 h) (by omega))

/-- Every subset of the complete graph is a clique, so the count is a binomial coefficient. -/
@[simp, toIsoGraph]
theorem cliqueCount_complete (m n : ℕ) :
    (complete m).cliqueCount n = m.choose n := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset]
  have h : (complete m).toSimple.cliqueFinset n = Finset.univ.powersetCard n := by
    ext s
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, Finset.mem_powersetCard,
      complete_toSimple]
    simp [SimpleGraph.IsClique, Set.Pairwise]
  rw [h, Finset.card_powersetCard, Finset.card_univ, card_complete]

@[simp, toIsoGraph] theorem cliqueCount_empty (m n : ℕ) : (empty m).cliqueCount (n + 2) = 0 := by
  refine cliqueCount_eq_zero_of_cliqueNum_lt ?_
  rw [cliqueNum_empty]
  omega

/-! ### Counting independent sets

Independent sets are cliques of the complement, so the whole clique-count API transfers: each
fact below is its clique-count counterpart read through `compl`. -/

@[simp] theorem cliqueCount_compl (G : CGraph) (n : ℕ) :
    Gᶜ.cliqueCount n = G.indepCount n := by
  rw [cliqueCount, indepCount]
  congr 1
  ext s
  simp [compl_toSimple]

@[simp] theorem indepCount_compl (G : CGraph) (n : ℕ) :
    Gᶜ.indepCount n = G.cliqueCount n := by
  rw [← cliqueCount_compl Gᶜ, compl_compl]

@[simp, toIsoGraph] theorem indepCount_zero (G : CGraph) : G.indepCount 0 = 1 := by
  classical
  rw [← cliqueCount_compl]
  exact cliqueCount_zero _

@[simp, toIsoGraph] theorem indepCount_one (G : CGraph) : G.indepCount 1 = Fintype.card G.V := by
  classical
  rw [← cliqueCount_compl, cliqueCount_one, card_compl]

@[toIsoGraph]
theorem indepCount_eq_zero_iff (G : CGraph) (n : ℕ) :
    G.indepCount n = 0 ↔ G.indepNum < n := by
  classical
  rw [← cliqueCount_compl, cliqueCount_eq_zero_iff, cliqueNum_compl]

@[toIsoGraph]
theorem indepCount_pos_iff (G : CGraph) (n : ℕ) : 0 < G.indepCount n ↔ n ≤ G.indepNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, indepCount_eq_zero_iff]
  omega

theorem indepCount_eq_zero_of_indepNum_lt {G : CGraph} {n : ℕ} (h : G.indepNum < n) :
    G.indepCount n = 0 :=
  (indepCount_eq_zero_iff G n).2 h

@[toIsoGraph]
theorem indepCount_le_choose (G : CGraph) (n : ℕ) :
    G.indepCount n ≤ (Fintype.card G.V).choose n := by
  classical
  rw [← cliqueCount_compl]
  have h := cliqueCount_le_choose Gᶜ n
  rwa [card_compl] at h

theorem indepCount_eq_zero_of_card_lt {G : CGraph} {n : ℕ} (h : Fintype.card G.V < n) :
    G.indepCount n = 0 :=
  Nat.le_zero.1 ((indepCount_le_choose G n).trans (Nat.choose_eq_zero_of_lt h).le)

/-- The independent pairs are exactly the non-edges. -/
@[toIsoGraph]
theorem indepCount_two_add_E (G : CGraph) :
    G.indepCount 2 + G.E = (Fintype.card G.V).choose 2 := by
  rw [← cliqueCount_compl, cliqueCount_two]
  exact E_compl G

/-- Every set of vertices of the empty graph is independent. -/
@[simp, toIsoGraph] theorem indepCount_empty (m n : ℕ) : (empty m).indepCount n = m.choose n := by
  rw [← cliqueCount_compl]
  exact cliqueCount_complete m n

@[simp, toIsoGraph]
theorem indepCount_complete (m n : ℕ) :
    (complete m).indepCount (n + 2) = 0 := by
  rw [← cliqueCount_compl, show (complete m)ᶜ = empty m from compl_compl (empty m)]
  exact cliqueCount_empty m n

/-! ### Counting cliques in a disjoint union -/

/-- A clique of a disjoint union that has at least one vertex lies wholly on one of the two
sides, because no edge crosses between them. -/
theorem isNClique_disjUnion_iff {n : ℕ} {s : Finset (disjUnion G H).V} :
    (disjUnion G H).toSimple.IsNClique (n + 1) s ↔
      (∃ t : Finset G.V, G.toSimple.IsNClique (n + 1) t ∧
          s = t.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (∃ t : Finset H.V, H.toSimple.IsNClique (n + 1) t ∧
          s = t.map ⟨Sum.inr, Sum.inr_injective⟩) := by
  constructor
  · rintro ⟨hcl, hcard⟩
    obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    match x, hx with
    | .inl a, ha =>
      have hsub : s ⊆ Finset.univ.map
          (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (disjUnion G H).V) := by
        intro y hy
        match y, hy with
        | .inl b, _ => simp
        | .inr d, hd =>
          exact absurd (hcl (by simpa using ha) (by simpa using hd) (by simp))
            (by simp [CGraph.toSimple_adj])
      obtain ⟨t, -, rfl⟩ := Finset.subset_map_iff.1 hsub
      refine Or.inl ⟨t, ⟨?_, by simpa using hcard⟩, rfl⟩
      intro b hb c hc hbc
      have hb' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hb))
      have hc' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hc))
      have := hcl hb' hc' (Sum.inl_injective.ne hbc)
      simpa [CGraph.toSimple_adj] using this
    | .inr b, hb =>
      have hsub : s ⊆ Finset.univ.map
          (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (disjUnion G H).V) := by
        intro y hy
        match y, hy with
        | .inr d, _ => simp
        | .inl a, ha =>
          exact absurd (hcl (by simpa using ha) (by simpa using hb) (by simp))
            (by simp [CGraph.toSimple_adj])
      obtain ⟨t, -, rfl⟩ := Finset.subset_map_iff.1 hsub
      refine Or.inr ⟨t, ⟨?_, by simpa using hcard⟩, rfl⟩
      intro c hc d hd hcd
      have hc' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hc))
      have hd' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hd))
      have := hcl hc' hd' (Sum.inr_injective.ne hcd)
      simpa [CGraph.toSimple_adj] using this
  · rintro (⟨t, ⟨hcl, hcard⟩, rfl⟩ | ⟨t, ⟨hcl, hcard⟩, rfl⟩)
    · refine ⟨?_, by simpa using hcard⟩
      rintro _ hx _ hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have : a ≠ b := fun h ↦ hxy (by rw [h])
      simpa [CGraph.toSimple_adj] using hcl ha hb this
    · refine ⟨?_, by simpa using hcard⟩
      rintro _ hx _ hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have : a ≠ b := fun h ↦ hxy (by rw [h])
      simpa [CGraph.toSimple_adj] using hcl ha hb this

/-- Cliques never cross between the two sides, so from size one on the counts simply add. -/
@[toIsoGraph simp]
theorem cliqueCount_disjUnion (G H : CGraph) (n : ℕ) :
    (disjUnion G H).cliqueCount (n + 1) = G.cliqueCount (n + 1) + H.cliqueCount (n + 1) := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset, cliqueCount_eq_card_cliqueFinset,
    cliqueCount_eq_card_cliqueFinset]
  set fl : Finset G.V ↪ Finset (disjUnion G H).V :=
    ⟨Finset.map ⟨Sum.inl, Sum.inl_injective⟩, Finset.map_injective _⟩ with hfl
  set fr : Finset H.V ↪ Finset (disjUnion G H).V :=
    ⟨Finset.map ⟨Sum.inr, Sum.inr_injective⟩, Finset.map_injective _⟩ with hfr
  have hset : (disjUnion G H).toSimple.cliqueFinset (n + 1)
      = (G.toSimple.cliqueFinset (n + 1)).map fl
        ∪ (H.toSimple.cliqueFinset (n + 1)).map fr := by
    ext s
    simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_cliqueFinset_iff, hfl, hfr,
      Function.Embedding.coeFn_mk]
    rw [isNClique_disjUnion_iff]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact Or.inl ⟨t, ht, rfl⟩
      · exact Or.inr ⟨t, ht, rfl⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact Or.inl ⟨t, ht, rfl⟩
      · exact Or.inr ⟨t, ht, rfl⟩
  have hdisj : Disjoint ((G.toSimple.cliqueFinset (n + 1)).map fl)
      ((H.toSimple.cliqueFinset (n + 1)).map fr) := by
    rw [Finset.disjoint_left]
    rintro s hs hs'
    simp only [Finset.mem_map, SimpleGraph.mem_cliqueFinset_iff, hfl, hfr,
      Function.Embedding.coeFn_mk] at hs hs'
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨u, -, hu⟩ := hs'
    obtain ⟨a, ha⟩ : t.Nonempty := Finset.card_pos.1 (by rw [ht.card_eq]; omega)
    have : (Sum.inl a : (disjUnion G H).V) ∈ u.map ⟨Sum.inr, Sum.inr_injective⟩ := by
      rw [hu]; simpa using ha
    simp at this
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

/-- Dually, independent sets never cross a join. -/
theorem indepCount_join (G H : CGraph) (n : ℕ) :
    (join G H).indepCount (n + 1) = G.indepCount (n + 1) + H.indepCount (n + 1) := by
  classical
  rw [join, indepCount_compl, cliqueCount_disjUnion, cliqueCount_compl, cliqueCount_compl]

/-- An independent set of `K_{m,n}` is a set of vertices on one side. -/
@[simp, toIsoGraph] theorem indepCount_bipartite (m n k : ℕ) :
    (bipartite m n).indepCount (k + 1) = m.choose (k + 1) + n.choose (k + 1) := by
  classical
  rw [bipartite, indepCount_compl, cliqueCount_disjUnion, cliqueCount_complete,
    cliqueCount_complete]

/-! ### Counting connected components -/

@[toIsoGraph]
theorem numComponents_eq_zero_iff (G : CGraph) :
    G.numComponents = 0 ↔ Fintype.card G.V = 0 := by
  rw [numComponents, Nat.card_eq_zero, Fintype.card_eq_zero_iff]
  simp only [or_iff_left (not_infinite_iff_finite.2 inferInstance)]
  exact ⟨fun h ↦ ⟨fun v ↦ h.false (G.toSimple.connectedComponentMk v)⟩, fun _ ↦ inferInstance⟩

@[toIsoGraph]
theorem numComponents_pos_iff (G : CGraph) : 0 < G.numComponents ↔ 0 < Fintype.card G.V := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, ne_eq, ne_eq, numComponents_eq_zero_iff]

/-- A graph is connected exactly when it has one component. -/
@[toIsoGraph]
theorem numComponents_eq_one_iff (G : CGraph) : G.numComponents = 1 ↔ G.IsConnected := by
  rw [numComponents, Nat.card_eq_one_iff_unique, IsConnected, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨hsub, hne⟩
    refine ⟨fun u v ↦ SimpleGraph.ConnectedComponent.exact (hsub.elim _ _), ?_⟩
    obtain ⟨c⟩ := hne
    exact SimpleGraph.ConnectedComponent.ind (β := fun _ ↦ Nonempty G.V) (fun v ↦ ⟨v⟩) c
  · rintro ⟨hpre, hne⟩
    exact ⟨hpre.subsingleton_connectedComponent, inferInstance⟩

/-- Each component contains at least one vertex. -/
@[toIsoGraph numComponents_le_V]
theorem numComponents_le_card (G : CGraph) : G.numComponents ≤ Fintype.card G.V := by
  rw [numComponents, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ (Quot.mk_surjective)

@[simp, toIsoGraph] theorem numComponents_empty (n : ℕ) : (empty n).numComponents = n := by
  rw [numComponents, empty_toSimple]
  have : Function.Bijective ((⊥ : SimpleGraph (Fin n)).connectedComponentMk) := by
    refine ⟨fun u v h ↦ ?_, Quot.mk_surjective⟩
    exact SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.exact h)
  rw [← Nat.card_eq_of_bijective _ this, Nat.card_eq_fintype_card, Fintype.card_fin]

@[simp, toIsoGraph] theorem numComponents_complete (n : ℕ) : (complete (n + 1)).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_complete n)

/-! ### The components of a disjoint union -/

/-- The inclusion of the left factor of a disjoint union, as a graph homomorphism. -/
def disjUnionInl (G H : CGraph) : G.toSimple →g (disjUnion G H).toSimple where
  toFun := Sum.inl
  map_rel' {a b} h := by simpa [CGraph.toSimple_adj] using h

/-- The inclusion of the right factor of a disjoint union, as a graph homomorphism. -/
def disjUnionInr (G H : CGraph) : H.toSimple →g (disjUnion G H).toSimple where
  toFun := Sum.inr
  map_rel' {a b} h := by simpa [CGraph.toSimple_adj] using h

/-- Send a vertex of a disjoint union to its component on whichever side it lives. -/
private def duSplit (G H : CGraph) :
    (disjUnion G H).V → G.toSimple.ConnectedComponent ⊕ H.toSimple.ConnectedComponent :=
  Sum.map G.toSimple.connectedComponentMk H.toSimple.connectedComponentMk

private theorem duSplit_eq_of_adj {u v : (disjUnion G H).V}
    (h : (disjUnion G H).toSimple.Adj u v) : duSplit G H u = duSplit G H v := by
  match u, v with
  | Sum.inl a, Sum.inl c =>
    have : G.toSimple.Adj a c := by simpa [CGraph.toSimple_adj] using h
    simp [duSplit, SimpleGraph.ConnectedComponent.eq, this.reachable]
  | Sum.inl a, Sum.inr d => exact absurd h (by simp [CGraph.toSimple_adj])
  | Sum.inr c, Sum.inl b => exact absurd h (by simp [CGraph.toSimple_adj])
  | Sum.inr c, Sum.inr d =>
    have : H.toSimple.Adj c d := by simpa [CGraph.toSimple_adj] using h
    simp [duSplit, SimpleGraph.ConnectedComponent.eq, this.reachable]

private theorem duSplit_eq_of_reachable {u v : (disjUnion G H).V}
    (h : (disjUnion G H).toSimple.Reachable u v) : duSplit G H u = duSplit G H v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (duSplit_eq_of_adj hadj).trans ih

/-- **The components of a disjoint union are those of the two factors.** -/
def disjUnionComponentEquiv (G H : CGraph) :
    (disjUnion G H).toSimple.ConnectedComponent ≃
      G.toSimple.ConnectedComponent ⊕ H.toSimple.ConnectedComponent where
  toFun := SimpleGraph.ConnectedComponent.lift (duSplit G H)
    (fun _ _ p _ ↦ duSplit_eq_of_reachable ⟨p⟩)
  invFun := Sum.elim (SimpleGraph.ConnectedComponent.map (disjUnionInl G H))
    (SimpleGraph.ConnectedComponent.map (disjUnionInr G H))
  left_inv := by
    refine SimpleGraph.ConnectedComponent.ind (fun v ↦ ?_)
    match v with
    | Sum.inl a => rfl
    | Sum.inr b => rfl
  right_inv := by
    rintro (c | c)
    · induction c using SimpleGraph.ConnectedComponent.ind with | _ a => rfl
    · induction c using SimpleGraph.ConnectedComponent.ind with | _ b => rfl

@[simp, toIsoGraph] theorem numComponents_disjUnion (G H : CGraph) :
    (disjUnion G H).numComponents = G.numComponents + H.numComponents := by
  rw [numComponents, numComponents, numComponents,
    Nat.card_congr (disjUnionComponentEquiv G H), Nat.card_sum]

/-- **At most one of a graph and its complement is disconnected.** -/
@[toIsoGraph]
theorem numComponents_compl_eq_one (G : CGraph) (h : 2 ≤ G.numComponents) :
    Gᶜ.numComponents = 1 := by
  have hne : Nonempty G.V := Fintype.card_pos_iff.1
    ((numComponents_pos_iff G).1 (by omega))
  rw [numComponents_eq_one_iff]
  refine G.isConnected_compl_of_not_preconnected (fun hpre ↦ ?_)
  have : Subsingleton G.toSimple.ConnectedComponent := hpre.subsingleton_connectedComponent
  have : G.numComponents = 1 := by
    rw [numComponents]
    exact Nat.card_eq_one_iff_unique.2 ⟨this, inferInstance⟩
  omega

/-! ### Components versus the other invariants -/

theorem surjective_connectedComponentMk (G : CGraph) :
    Function.Surjective G.toSimple.connectedComponentMk :=
  fun c ↦ Quot.exists_rep c

/-- One vertex from each component is an independent set, so there are at most `α(G)` components. -/
@[toIsoGraph]
theorem numComponents_le_indepNum (G : CGraph) : G.numComponents ≤ G.indepNum := by
  classical
  choose f hout using G.surjective_connectedComponentMk
  have hinj : Function.Injective f := fun c d h ↦ by rw [← hout c, ← hout d, h]
  set s : Finset G.V := Finset.univ.image f with hs
  have hcard : s.card = G.numComponents := by
    rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, numComponents,
      Fintype.card_eq_nat_card]
  have hindep : G.toSimple.IsIndepSet s := by
    intro x hx y hy hxy hadj
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    refine hxy ?_
    have : c = d := by
      rw [← hout c, ← hout d]
      exact SimpleGraph.ConnectedComponent.sound hadj.reachable
    rw [this]
  calc G.numComponents = s.card := hcard.symm
    _ ≤ G.indepNum := hindep.card_le_indepNum

/-- A dominating set must meet every component, so there are at most `γ(G)` components. -/
@[toIsoGraph]
theorem numComponents_le_domNum (G : CGraph) : G.numComponents ≤ G.domNum := by
  classical
  obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
  have hsurj : Function.Surjective
      (fun v : {x : G.V // x ∈ s} ↦ G.toSimple.connectedComponentMk v.1) := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      rcases hs v with hv | ⟨u, hu, hadj⟩
      · exact ⟨⟨v, hv⟩, rfl⟩
      · exact ⟨⟨u, hu⟩, SimpleGraph.ConnectedComponent.sound
          (SimpleGraph.Adj.reachable (G.toSimple_adj u v |>.2 hadj))⟩
  rw [numComponents]
  calc Nat.card G.toSimple.ConnectedComponent
      ≤ Nat.card {x : G.V // x ∈ s} := Nat.card_le_card_of_surjective _ hsurj
    _ = s.card := Nat.card_eq_finsetCard s
    _ = G.domNum := hcard

/-- The join of two nonempty graphs is connected, hence has one component. -/
theorem numComponents_join (G H : CGraph)
    (hG : 0 < Fintype.card G.V) (hH : 0 < Fintype.card H.V) :
    (join G H).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_join G H hG hH)

theorem E_pos_of_adj {G : CGraph} {a b : G.V} (h : G.toSimple.Adj a b) : 0 < G.E :=
  Finset.card_pos.2 ⟨s(a, b), SimpleGraph.mem_edgeFinset.2 h⟩

/-- A graph has as many components as vertices exactly when it has no edges. -/
@[toIsoGraph numComponents_eq_V_iff]
theorem numComponents_eq_card_iff (G : CGraph) :
    G.numComponents = Fintype.card G.V ↔ G.E = 0 := by
  classical
  constructor
  · intro h
    by_contra hE
    obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos (Nat.pos_of_ne_zero hE)
    have hadj : G.toSimple.Adj a b := hab
    have hnotinj : ¬ Function.Injective G.toSimple.connectedComponentMk := fun hinj ↦
      hadj.ne (hinj (SimpleGraph.ConnectedComponent.sound hadj.reachable))
    have hlt := Fintype.card_lt_of_surjective_not_injective _ G.surjective_connectedComponentMk
      hnotinj
    rw [Fintype.card_eq_nat_card] at hlt
    rw [numComponents] at h
    omega
  · intro h
    have hbot : G.toSimple = ⊥ := by
      ext a b
      simp only [SimpleGraph.bot_adj, iff_false]
      intro hadj
      have := E_pos_of_adj hadj
      omega
    have hinj : Function.Injective G.toSimple.connectedComponentMk := by
      intro u v huv
      have hr : G.toSimple.Reachable u v := SimpleGraph.ConnectedComponent.exact huv
      rw [hbot] at hr
      exact SimpleGraph.reachable_bot.1 hr
    rw [numComponents,
      ← Nat.card_eq_of_bijective _ ⟨hinj, G.surjective_connectedComponentMk⟩,
      Nat.card_eq_fintype_card]

theorem numComponents_lt_card_of_E_pos (G : CGraph) (h : 0 < G.E) :
    G.numComponents < Fintype.card G.V := by
  have hle := G.numComponents_le_card
  have := (G.numComponents_eq_card_iff).not.2 (by omega : ¬ G.E = 0)
  omega

/-! ### Components of a Cartesian product -/

/-- Reachability in a box product is reachability in both factors, so the components of a box
product are the pairs of components. -/
private theorem card_connectedComponent_boxProd {α β : Type*} (S : SimpleGraph α)
    (T : SimpleGraph β) :
    Nat.card (S.boxProd T).ConnectedComponent
      = Nat.card S.ConnectedComponent * Nat.card T.ConnectedComponent := by
  set φ : (S.boxProd T).ConnectedComponent → S.ConnectedComponent × T.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift
      (fun p ↦ (S.connectedComponentMk p.1, T.connectedComponentMk p.2))
      (fun p q w _ ↦ by
        obtain ⟨h1, h2⟩ := SimpleGraph.reachable_boxProd.1 ⟨w⟩
        exact Prod.ext (SimpleGraph.ConnectedComponent.sound h1)
          (SimpleGraph.ConnectedComponent.sound h2)) with hφ
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y
      induction x using SimpleGraph.ConnectedComponent.ind with | _ p =>
      induction y using SimpleGraph.ConnectedComponent.ind with | _ q =>
      intro h
      have h1 : S.connectedComponentMk p.1 = S.connectedComponentMk q.1 := congrArg Prod.fst h
      have h2 : T.connectedComponentMk p.2 = T.connectedComponentMk q.2 := congrArg Prod.snd h
      exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.reachable_boxProd.2
        ⟨SimpleGraph.ConnectedComponent.exact h1, SimpleGraph.ConnectedComponent.exact h2⟩)
    · rintro ⟨c, d⟩
      obtain ⟨a, rfl⟩ := Quot.exists_rep c
      obtain ⟨b, rfl⟩ := Quot.exists_rep d
      exact ⟨(S.boxProd T).connectedComponentMk (a, b), rfl⟩
  rw [Nat.card_eq_of_bijective φ hbij, Nat.card_prod]

/-- **The components of a Cartesian product are the pairs of components.** -/
theorem numComponents_cartesianProduct (G H : CGraph) :
    (cartesianProduct G H).numComponents = G.numComponents * H.numComponents := by
  rw [numComponents, numComponents, numComponents, toSimple_cartesianProduct]
  exact card_connectedComponent_boxProd _ _

/-! ### A minimum-degree condition for connectedness -/

/-- **A graph with `2δ(G) + 1 ≥ |V|` is connected**: two nonadjacent vertices have too many
neighbours between them to avoid sharing one. -/
@[toIsoGraph isConnected_of_V_le_two_mul_minDeg]
theorem isConnected_of_card_le_two_mul_minDeg (G : CGraph) [Nonempty G.V]
    (h : Fintype.card G.V ≤ 2 * G.minDeg + 1) : G.IsConnected := by
  classical
  rw [IsConnected, SimpleGraph.connected_iff]
  refine ⟨fun u v ↦ ?_, inferInstance⟩
  by_cases huv : u = v
  · exact huv ▸ SimpleGraph.Reachable.refl u
  by_cases hadj : G.toSimple.Adj u v
  · exact hadj.reachable
  -- neither neighbourhood contains `u` or `v`
  set T : Finset G.V := (Finset.univ.erase u).erase v with hT
  have hu : G.toSimple.neighborFinset u ⊆ T := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact Finset.mem_erase.2 ⟨fun hwv ↦ hadj (hwv ▸ hw),
      Finset.mem_erase.2 ⟨fun hwu ↦ (hwu ▸ hw).ne rfl, Finset.mem_univ w⟩⟩
  have hv : G.toSimple.neighborFinset v ⊆ T := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact Finset.mem_erase.2 ⟨fun hwv ↦ (hwv ▸ hw).ne rfl,
      Finset.mem_erase.2 ⟨fun hwu ↦ hadj (hwu ▸ hw).symm, Finset.mem_univ w⟩⟩
  have hTcard : T.card = Fintype.card G.V - 2 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨fun h' ↦ huv h'.symm, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
    omega
  have hdu : G.minDeg ≤ (G.toSimple.neighborFinset u).card := G.minDeg_le_degree u
  have hdv : G.minDeg ≤ (G.toSimple.neighborFinset v).card := G.minDeg_le_degree v
  have hunion : (G.toSimple.neighborFinset u ∪ G.toSimple.neighborFinset v).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset hu hv)
  have hinter := Finset.card_union_add_card_inter
    (G.toSimple.neighborFinset u) (G.toSimple.neighborFinset v)
  have hcard2 : 2 ≤ Fintype.card G.V := by
    have hle : ({u, v} : Finset G.V).card ≤ Fintype.card G.V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rwa [Finset.card_pair huv] at hle
  have hpos : 0 < (G.toSimple.neighborFinset u ∩ G.toSimple.neighborFinset v).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
  exact hw.1.reachable.trans hw.2.reachable.symm

theorem numComponents_eq_one_of_card_le_two_mul_minDeg (G : CGraph) [Nonempty G.V]
    (h : Fintype.card G.V ≤ 2 * G.minDeg + 1) : G.numComponents = 1 :=
  (numComponents_eq_one_iff G).2 (G.isConnected_of_card_le_two_mul_minDeg h)

/-! ### Counting automorphisms -/

/-- Every permutation is an automorphism of the edgeless graph. -/
def _root_.SimpleGraph.autBotEquiv (α : Type*) :
    ((⊥ : SimpleGraph α) ≃g (⊥ : SimpleGraph α)) ≃ Equiv.Perm α where
  toFun a := a.toEquiv
  invFun e := ⟨e, by simp⟩
  left_inv a := by ext v; rfl
  right_inv e := by ext v; rfl

/-- Every permutation is an automorphism of the complete graph. -/
def _root_.SimpleGraph.autTopEquiv (α : Type*) :
    ((⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph α)) ≃ Equiv.Perm α where
  toFun a := a.toEquiv
  invFun e := ⟨e, by simp [e.injective.ne_iff]⟩
  left_inv a := by ext v; rfl
  right_inv e := by ext v; rfl

/-- Complementation does not change the automorphism group. -/
def _root_.SimpleGraph.autComplEquiv {α : Type*} (S : SimpleGraph α) : (S ≃g S) ≃ (Sᶜ ≃g Sᶜ) where
  toFun a := ⟨a.toEquiv, by
    intro x y
    simp only [SimpleGraph.compl_adj, ne_eq, a.toEquiv.injective.ne_iff]
    exact and_congr_right fun _ ↦ not_congr a.map_rel_iff⟩
  invFun b := ⟨b.toEquiv, by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · have hne : ¬ (b x = b y) := fun hh ↦ hxy (b.toEquiv.injective hh)
      have h := b.map_rel_iff (a := x) (b := y)
      rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at h
      constructor
      · intro hadj
        by_contra hc
        exact (h.2 ⟨hxy, hc⟩).2 hadj
      · intro hadj
        by_contra hc
        exact (h.1 ⟨hne, hc⟩).2 hadj⟩
  left_inv a := by ext v; rfl
  right_inv b := by ext v; rfl

@[toIsoGraph]
theorem autCount_pos (G : CGraph) : 0 < G.autCount := Nat.card_pos

/-- An automorphism is in particular a permutation of the vertices. -/
@[toIsoGraph]
theorem autCount_le_factorial (G : CGraph) : G.autCount ≤ Nat.factorial (Fintype.card G.V) := by
  classical
  calc G.autCount ≤ Nat.card (G.V ≃ G.V) :=
        Nat.card_le_card_of_injective (fun a : G.toSimple ≃g G.toSimple ↦ a.toEquiv)
          (fun _ _ h ↦ by ext v; exact congrArg (fun e : G.V ≃ G.V ↦ e v) h)
    _ = Nat.factorial (Fintype.card G.V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- **A graph and its complement have the same automorphisms.** -/
@[simp] theorem autCount_compl (G : CGraph) :
    Gᶜ.autCount = G.autCount := by
  rw [autCount, autCount, compl_toSimple]
  exact (Nat.card_congr (SimpleGraph.autComplEquiv G.toSimple)).symm

@[simp, toIsoGraph] theorem autCount_empty (n : ℕ) : (empty n).autCount = Nat.factorial n := by
  classical
  rw [autCount, empty_toSimple, Nat.card_congr (SimpleGraph.autBotEquiv (Fin n)),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

@[simp, toIsoGraph]
theorem autCount_complete (n : ℕ) :
    (complete n).autCount = Nat.factorial n := by
  classical
  rw [autCount, complete_toSimple, Nat.card_congr (SimpleGraph.autTopEquiv (Fin n)),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- A ray of a star has only one neighbour, so a vertex of `K_{1,n}` with two distinct neighbours
is the centre. -/
theorem exists_eq_inl_of_two_neighbours {n : ℕ} {x u v : (bipartite 1 n).V} (huv : u ≠ v)
    (hu : (bipartite 1 n).Adj x u = true) (hv : (bipartite 1 n).Adj x v = true) :
    ∃ a, x = Sum.inl a := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  rcases x with a | b
  · exact ⟨a, rfl⟩
  · exfalso
    apply huv
    rcases u with c | d
    · rcases v with c' | d'
      · rw [Subsingleton.elim c c']
      · simp at hv
    · simp at hu

/-- **Every automorphism of a star with at least two rays fixes the centre**, since the centre is
the only vertex with two distinct neighbours. -/
theorem aut_apply_inl {n : ℕ} (f : bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2))
    (a : (complete 1).V) : f (.inl a) = .inl a := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  obtain ⟨u, v, huv⟩ :=
    Fintype.exists_pair_of_one_lt_card (α := (complete (n + 2)).V) (by simp)
  have hne : (Sum.inr u : (bipartite 1 (n + 2)).V) ≠ Sum.inr v := fun h ↦ huv (Sum.inr.inj h)
  obtain ⟨a', ha'⟩ := exists_eq_inl_of_two_neighbours
    (x := f (.inl a)) (u := f (Sum.inr u)) (v := f (Sum.inr v))
    (fun h ↦ hne (f.injective h)) (by rw [f.adj_eq]; simp) (by rw [f.adj_eq]; simp)
  rw [ha', Subsingleton.elim a' a]

/-- With the centre fixed, an automorphism of a star with at least two rays is nothing but a
permutation of the rays. -/
theorem exists_perm_of_aut {n : ℕ} (f : bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2)) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), f = starAut (n + 2) σ := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  have hex : ∀ b : (complete (n + 2)).V, ∃ r, f (.inr b) = Sum.inr r := by
    intro b
    rcases hb : f (.inr b) with a | r
    · exact absurd (f.injective (hb.trans (aut_apply_inl f a).symm)) (by simp)
    · exact ⟨r, rfl⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro b c h
    have hbc : f (.inr b) = f (.inr c) := by rw [hg b, hg c, h]
    exact Sum.inr.inj (f.injective hbc)
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj), ?_⟩
  ext x
  rcases x with a | b
  · rw [aut_apply_inl f a, starAut_inl]
  · rw [hg b, starAut_inr]
    rfl

/-- **The star `K_{1,n}` has exactly `n!` automorphisms** once it has at least two rays: every
automorphism fixes the centre, and what is left is an arbitrary permutation of the rays.  This is
the upper bound matching `IsoGraph.factorial_le_autCount_star`; the two smaller stars are
exceptions, `star 0 = K₁` has one automorphism and `star 1 = K₂` has two. -/
@[toIsoGraph]
theorem autCount_star (n : ℕ) : (star (n + 2)).autCount = (n + 2).factorial := by
  have hb : Function.Bijective (starAut (n + 2)) := by
    constructor
    · intro σ τ h
      refine Equiv.ext fun b ↦ ?_
      have h1 : (Sum.inr (σ b) : (bipartite 1 (n + 2)).V) = Sum.inr (τ b) :=
        congrArg (fun e : bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2) ↦ e (.inr b)) h
      exact Sum.inr.inj h1
    · intro f
      obtain ⟨σ, hσ⟩ := exists_perm_of_aut f
      exact ⟨σ, hσ.symm⟩
  have hcard : Nat.card (Equiv.Perm (Fin (n + 2)))
      = Nat.card (bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2)) :=
    Nat.card_eq_of_bijective _ hb
  have hperm : Nat.card (Equiv.Perm (Fin (n + 2))) = (n + 2).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  show Nat.card (bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2)) = (n + 2).factorial
  rw [← hcard, hperm]

/-! ### The automorphism count of a complete bipartite graph

`K_{m,n}` with `m ≠ n` is the star argument with the asymmetry moved from one vertex to one side.
A vertex of the `m`-side has `n` neighbours and a vertex of the `n`-side has `m`, so as soon as the
two sides have different sizes no automorphism can exchange them, and the group is `Sₘ × Sₙ`.  When
`m = n` the swap is available and the count doubles, which is why the hypothesis cannot be dropped.
-/

/-- Permuting the two sides of `K_{m,n}` separately.  This is `bipartiteCongr` without the
requirement that the two sides have the same size. -/
def bipartiteAut (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    bipartite m n ≃cg bipartite m n :=
  autoOfPerm (G := bipartite m n) (Equiv.sumCongr σ τ) fun x y ↦ by
    show (bipartite m n).Adj (Sum.map σ τ x) (Sum.map σ τ y) = _
    rcases x with a | b <;> rcases y with c | d <;> simp

@[simp] theorem bipartiteAut_inl (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (a : Fin m) : bipartiteAut m n σ τ (.inl a) = .inl (σ a) := rfl

@[simp] theorem bipartiteAut_inr (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (b : Fin n) : bipartiteAut m n σ τ (.inr b) = .inr (τ b) := rfl

theorem card_nbrs_bipartite_inl (m n : ℕ) (a : (complete m).V) :
    ((bipartite m n).nbrs (Sum.inl a)).card = n := by
  rw [nbrs_bipartite_inl, Finset.card_map, Finset.card_univ, card_complete]

theorem card_nbrs_bipartite_inr (m n : ℕ) (b : (complete n).V) :
    ((bipartite m n).nbrs (Sum.inr b)).card = m := by
  rw [nbrs_bipartite_inr, Finset.card_map, Finset.card_univ, card_complete]

/-- An automorphism cannot change the number of neighbours of a vertex. -/
theorem card_nbrs_aut {G : CGraph} (f : G ≃cg G) (x : G.V) :
    (G.nbrs (f x)).card = (G.nbrs x).card := by
  rw [card_nbrs_eq_degree, card_nbrs_eq_degree]
  exact SimpleGraph.Iso.degree_eq f.toSimpleIso x

/-- **The two sides of `K_{m,n}` cannot be exchanged when `m ≠ n`**, since they are told apart by
the degree of their vertices. -/
theorem bipartite_aut_inl {m n : ℕ} (hmn : m ≠ n) (f : bipartite m n ≃cg bipartite m n)
    (a : (complete m).V) : ∃ a', f (Sum.inl a) = Sum.inl a' := by
  rcases h : f (Sum.inl a) with a' | b'
  · exact ⟨a', rfl⟩
  · exfalso
    have h1 := card_nbrs_aut f (Sum.inl a)
    rw [h, card_nbrs_bipartite_inr, card_nbrs_bipartite_inl] at h1
    exact hmn h1

theorem bipartite_aut_inr {m n : ℕ} (hmn : m ≠ n) (f : bipartite m n ≃cg bipartite m n)
    (b : (complete n).V) : ∃ b', f (Sum.inr b) = Sum.inr b' := by
  rcases h : f (Sum.inr b) with a' | b'
  · exfalso
    have h1 := card_nbrs_aut f (Sum.inr b)
    rw [h, card_nbrs_bipartite_inl, card_nbrs_bipartite_inr] at h1
    exact hmn h1.symm
  · exact ⟨b', rfl⟩

/-- With the sides preserved, an automorphism of `K_{m,n}` is a pair of permutations. -/
theorem exists_perm_of_aut_bipartite {m n : ℕ} (hmn : m ≠ n)
    (f : bipartite m n ≃cg bipartite m n) :
    ∃ (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)), f = bipartiteAut m n σ τ := by
  choose g hg using bipartite_aut_inl hmn f
  choose h hh using bipartite_aut_inr hmn f
  have hginj : Function.Injective g := by
    intro a b hab
    have hab' : f (Sum.inl a) = f (Sum.inl b) := by rw [hg a, hg b, hab]
    exact Sum.inl.inj (f.injective hab')
  have hhinj : Function.Injective h := by
    intro a b hab
    have hab' : f (Sum.inr a) = f (Sum.inr b) := by rw [hh a, hh b, hab]
    exact Sum.inr.inj (f.injective hab')
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj),
    Equiv.ofBijective h (Finite.injective_iff_bijective.1 hhinj), ?_⟩
  ext x
  rcases x with a | b
  · rw [hg a, bipartiteAut_inl]
    rfl
  · rw [hh b, bipartiteAut_inr]
    rfl

/-- **The complete bipartite graph `K_{m,n}` has exactly `m! · n!` automorphisms when `m ≠ n`**:
the sides are told apart by degree, so each is permuted within itself.  This is the upper bound
matching `IsoGraph.factorial_mul_factorial_le_autCount_bipartite`, and it generalises
`autCount_star`, whose `n ≥ 2` hypothesis becomes `1 ≠ n`.  For `m = n` the true count is
`2 · (n!)²`, by `bipartiteSwap`. -/
@[toIsoGraph]
theorem autCount_bipartite {m n : ℕ} (hmn : m ≠ n) :
    (bipartite m n).autCount = m.factorial * n.factorial := by
  have hb : Function.Bijective
      (fun p : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) ↦ bipartiteAut m n p.1 p.2) := by
    constructor
    · rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ hst
      have h1 : ∀ a, (Sum.inl (σ a) : (bipartite m n).V) = Sum.inl (σ' a) := fun a ↦
        congrArg (fun e : bipartite m n ≃cg bipartite m n ↦ e (.inl a)) hst
      have h2 : ∀ b, (Sum.inr (τ b) : (bipartite m n).V) = Sum.inr (τ' b) := fun b ↦
        congrArg (fun e : bipartite m n ≃cg bipartite m n ↦ e (.inr b)) hst
      have e1 : σ = σ' := Equiv.ext fun a ↦ Sum.inl.inj (h1 a)
      have e2 : τ = τ' := Equiv.ext fun b ↦ Sum.inr.inj (h2 b)
      rw [e1, e2]
    · intro f
      obtain ⟨σ, τ, hσ⟩ := exists_perm_of_aut_bipartite hmn f
      exact ⟨(σ, τ), hσ.symm⟩
  have hcard := Nat.card_eq_of_bijective _ hb
  have hperm : Nat.card (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))
      = m.factorial * n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fin]
  show Nat.card (bipartite m n ≃cg bipartite m n) = m.factorial * n.factorial
  rw [← hcard, hperm]

/-! ### The automorphism count of `K_{n,n}`

When the two sides have the same size the degree argument no longer separates them, but being on
the same side is still first-order: two distinct vertices are on the same side exactly when they
are non-adjacent.  So an automorphism either preserves both sides or exchanges them, and the count
doubles.
-/

/-- Permuting the two sides of `K_{n,n}` and then exchanging them. -/
def bipartiteSwapAut (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : bipartite n n ≃cg bipartite n n :=
  (bipartiteAut n n σ τ).trans (bipartiteSwap n)

@[simp] theorem bipartiteSwapAut_inl (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (a : Fin n) :
    bipartiteSwapAut n σ τ (.inl a) = .inr (σ a) := rfl

@[simp] theorem bipartiteSwapAut_inr (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (b : Fin n) :
    bipartiteSwapAut n σ τ (.inr b) = .inl (τ b) := rfl

/-- If one left vertex of `K_{n,n}` goes left then they all do: two left vertices are
non-adjacent, and a left and a right vertex are adjacent. -/
theorem bipartite_self_inl_inl {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a a' c : (complete n).V} (h : f (Sum.inl a) = Sum.inl c) :
    ∃ c', f (Sum.inl a') = Sum.inl c' := by
  rcases ha : f (Sum.inl a') with c' | d'
  · exact ⟨c', rfl⟩
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inl a')) = true := by
      rw [h, ha]; simp
    rw [f.adj_eq] at hadj
    simp at hadj

/-- If one left vertex of `K_{n,n}` goes right then they all do. -/
theorem bipartite_self_inl_inr {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a a' d : (complete n).V} (h : f (Sum.inl a) = Sum.inr d) :
    ∃ d', f (Sum.inl a') = Sum.inr d' := by
  rcases ha : f (Sum.inl a') with c' | d'
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inl a')) = true := by
      rw [h, ha]; simp
    rw [f.adj_eq] at hadj
    simp at hadj
  · exact ⟨d', rfl⟩

theorem bipartite_self_inr_of_inl {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a c : (complete n).V} (h : f (Sum.inl a) = Sum.inl c) (b : (complete n).V) :
    ∃ d, f (Sum.inr b) = Sum.inr d := by
  rcases hb : f (Sum.inr b) with c' | d'
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inr b)) = true := by
      rw [f.adj_eq]; simp
    rw [h, hb] at hadj
    simp at hadj
  · exact ⟨d', rfl⟩

theorem bipartite_self_inl_of_inr {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a d : (complete n).V} (h : f (Sum.inl a) = Sum.inr d) (b : (complete n).V) :
    ∃ c, f (Sum.inr b) = Sum.inl c := by
  rcases hb : f (Sum.inr b) with c' | d'
  · exact ⟨c', rfl⟩
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inr b)) = true := by
      rw [f.adj_eq]; simp
    rw [h, hb] at hadj
    simp at hadj

/-- **Every automorphism of `K_{n,n}` is a pair of permutations of the two sides, possibly
followed by exchanging them.** -/
theorem exists_perm_of_aut_bipartite_self {n : ℕ}
    (f : bipartite (n + 1) (n + 1) ≃cg bipartite (n + 1) (n + 1)) :
    ∃ σ τ : Equiv.Perm (Fin (n + 1)),
      f = bipartiteAut (n + 1) (n + 1) σ τ ∨ f = bipartiteSwapAut (n + 1) σ τ := by
  rcases h0 : f (Sum.inl ⟨0, Nat.succ_pos n⟩) with c | d
  · have hl : ∀ a, ∃ c', f (Sum.inl a) = Sum.inl c' := fun a ↦ bipartite_self_inl_inl f h0
    have hr : ∀ b, ∃ d', f (Sum.inr b) = Sum.inr d' := bipartite_self_inr_of_inl f h0
    choose g hg using hl
    choose k hk using hr
    have hginj : Function.Injective g := by
      intro a b hab
      have hab' : f (Sum.inl a) = f (Sum.inl b) := by rw [hg a, hg b, hab]
      exact Sum.inl.inj (f.injective hab')
    have hkinj : Function.Injective k := by
      intro a b hab
      have hab' : f (Sum.inr a) = f (Sum.inr b) := by rw [hk a, hk b, hab]
      exact Sum.inr.inj (f.injective hab')
    refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj),
      Equiv.ofBijective k (Finite.injective_iff_bijective.1 hkinj), Or.inl ?_⟩
    ext x
    rcases x with a | b
    · rw [hg a, bipartiteAut_inl]
      rfl
    · rw [hk b, bipartiteAut_inr]
      rfl
  · have hl : ∀ a, ∃ d', f (Sum.inl a) = Sum.inr d' := fun a ↦ bipartite_self_inl_inr f h0
    have hr : ∀ b, ∃ c', f (Sum.inr b) = Sum.inl c' := bipartite_self_inl_of_inr f h0
    choose g hg using hl
    choose k hk using hr
    have hginj : Function.Injective g := by
      intro a b hab
      have hab' : f (Sum.inl a) = f (Sum.inl b) := by rw [hg a, hg b, hab]
      exact Sum.inl.inj (f.injective hab')
    have hkinj : Function.Injective k := by
      intro a b hab
      have hab' : f (Sum.inr a) = f (Sum.inr b) := by rw [hk a, hk b, hab]
      exact Sum.inr.inj (f.injective hab')
    refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj),
      Equiv.ofBijective k (Finite.injective_iff_bijective.1 hkinj), Or.inr ?_⟩
    ext x
    rcases x with a | b
    · rw [hg a, bipartiteSwapAut_inl]
      rfl
    · rw [hk b, bipartiteSwapAut_inr]
      rfl

/-- An automorphism of `K_{n,n}` packaged as a `Bool` — whether the sides are exchanged — together
with a permutation of each side. -/
def bipartiteSelfAut (n : ℕ) (p : Bool × Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :
    bipartite n n ≃cg bipartite n n :=
  if p.1 then bipartiteSwapAut n p.2.1 p.2.2 else bipartiteAut n n p.2.1 p.2.2

theorem bipartiteSelfAut_injective (n : ℕ) : Function.Injective (bipartiteSelfAut (n + 1)) := by
  rintro ⟨s, σ, τ⟩ ⟨s', σ', τ'⟩ h
  have key : ∀ x : (bipartite (n + 1) (n + 1)).V,
      bipartiteSelfAut (n + 1) (s, σ, τ) x = bipartiteSelfAut (n + 1) (s', σ', τ') x := fun x ↦
    congrArg (fun e : bipartite (n + 1) (n + 1) ≃cg bipartite (n + 1) (n + 1) ↦ e x) h
  have hs : s = s' := by
    cases s <;> cases s' <;>
      first
        | rfl
        | exact absurd (key (Sum.inl ⟨0, Nat.succ_pos n⟩)) (by simp [bipartiteSelfAut])
  subst hs
  have hσ : σ = σ' := by
    refine Equiv.ext fun a ↦ ?_
    have hx := key (Sum.inl a)
    cases s with
    | false =>
      have h2 : (Sum.inl (σ a) : (bipartite (n + 1) (n + 1)).V) = Sum.inl (σ' a) := hx
      exact Sum.inl.inj h2
    | true =>
      have h2 : (Sum.inr (σ a) : (bipartite (n + 1) (n + 1)).V) = Sum.inr (σ' a) := hx
      exact Sum.inr.inj h2
  have hτ : τ = τ' := by
    refine Equiv.ext fun b ↦ ?_
    have hx := key (Sum.inr b)
    cases s with
    | false =>
      have h2 : (Sum.inr (τ b) : (bipartite (n + 1) (n + 1)).V) = Sum.inr (τ' b) := hx
      exact Sum.inr.inj h2
    | true =>
      have h2 : (Sum.inl (τ b) : (bipartite (n + 1) (n + 1)).V) = Sum.inl (τ' b) := hx
      exact Sum.inl.inj h2
  rw [hσ, hτ]

theorem bipartiteSelfAut_surjective (n : ℕ) : Function.Surjective (bipartiteSelfAut (n + 1)) := by
  intro f
  obtain ⟨σ, τ, hf | hf⟩ := exists_perm_of_aut_bipartite_self f
  · exact ⟨(false, σ, τ), hf.symm⟩
  · exact ⟨(true, σ, τ), hf.symm⟩

/-- **`K_{n,n}` has exactly `2 · (n!)²` automorphisms**: each side may be permuted freely, and the
two sides may be exchanged.  This is the case `autCount_bipartite` has to exclude. -/
@[toIsoGraph]
theorem autCount_bipartite_self (n : ℕ) :
    (bipartite (n + 1) (n + 1)).autCount = 2 * ((n + 1).factorial * (n + 1).factorial) := by
  have hb : Function.Bijective (bipartiteSelfAut (n + 1)) :=
    ⟨bipartiteSelfAut_injective n, bipartiteSelfAut_surjective n⟩
  have hcard := Nat.card_eq_of_bijective _ hb
  have hprod : Nat.card (Bool × Equiv.Perm (Fin (n + 1)) × Equiv.Perm (Fin (n + 1)))
      = 2 * ((n + 1).factorial * (n + 1).factorial) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_perm, Fintype.card_fin]
  show Nat.card (bipartite (n + 1) (n + 1) ≃cg bipartite (n + 1) (n + 1))
    = 2 * ((n + 1).factorial * (n + 1).factorial)
  rw [← hcard, hprod]

end CGraph
