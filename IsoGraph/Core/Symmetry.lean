import IsoGraph.Core.Structure

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Automorphisms, transitivity and regularity

Automorphisms, vertex- and arc-transitivity, regularity and self-complementarity, both for the core
constructions and as general theory: a vertex-transitive graph is regular, a transitive graph's
order divides its automorphism count, and the clique–coclique bound.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

/-- The complement of a strongly regular graph is strongly regular, with the parameters Mathlib
computes for `SimpleGraph`s. -/
@[toIsoGraph IsSRGWith.compl]
theorem isSRGWith_compl {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsSRGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) :=
  SimpleGraph.Iso.isSRGWith_of_iso (G := G.toSimpleᶜ) (G' := Gᶜ.toSimple)
    ⟨Equiv.refl G.V, by simp; intro a b _; rfl⟩ (SimpleGraph.IsSRGWith.compl h)

end

section
open Fintype
variable (G : CGraph)

/-- To see that `ofRel V r` is vertex-transitive it is enough to move `u` to `v` by a permutation
preserving the symmetrisation of `r`. -/
theorem isVertexTransitive_ofRel (V : Type) [FinEnum V] (r : V → V → Bool)
    (h : ∀ u v : V, ∃ σ : Equiv.Perm V,
      (∀ x y, (r (σ x) (σ y) || r (σ y) (σ x)) = (r x y || r y x)) ∧ σ u = v) :
    (ofRel V r).IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ, huv⟩ := h u v
  refine ⟨autoOfPerm (G := ofRel V r) σ fun x y ↦ ?_, huv⟩
  show (decide (σ x ≠ σ y) && (r (σ x) (σ y) || r (σ y) (σ x))) =
    (decide (x ≠ y) && (r x y || r y x))
  rw [hσ x y]
  simp

/-- To see that `ofRel V r` is arc-transitive it is enough to match up any two pairs of distinct,
symmetrically-related points. -/
theorem isArcTransitive_ofRel (V : Type) [FinEnum V] (r : V → V → Bool)
    (h : ∀ u v u' v' : V, u ≠ v → u' ≠ v' → (r u v || r v u) → (r u' v' || r v' u') →
      ∃ σ : Equiv.Perm V, (∀ x y, (r (σ x) (σ y) || r (σ y) (σ x)) = (r x y || r y x)) ∧
        σ u = u' ∧ σ v = v') :
    (ofRel V r).IsArcTransitive := by
  intro u v u' v' huv hu'v'
  simp only [ofRel_adj, Bool.and_eq_true, decide_eq_true_eq] at huv hu'v'
  obtain ⟨σ, hσ, h₁, h₂⟩ := h u v u' v' huv.1 hu'v'.1 huv.2 hu'v'.2
  refine ⟨autoOfPerm (G := ofRel V r) σ fun x y ↦ ?_, h₁, h₂⟩
  show (decide (σ x ≠ σ y) && (r (σ x) (σ y) || r (σ y) (σ x))) =
    (decide (x ≠ y) && (r x y || r y x))
  rw [hσ x y]
  simp

/-- Arc-transitivity is the stronger property: it implies vertex-transitivity as soon as there
are no isolated vertices.  (The hypothesis is needed: `empty n` is arc-transitive for want of any
arcs at all, but not vertex-transitive for `n ≥ 2`.) -/
theorem isVertexTransitive_of_isArcTransitive
    (hne : ∀ u : G.V, ∃ v, G.Adj u v) (h : G.IsArcTransitive) : G.IsVertexTransitive := by
  intro u v
  obtain ⟨u', hu⟩ := hne u
  obtain ⟨v', hv⟩ := hne v
  obtain ⟨σ, h₁, -⟩ := h u u' v v' hu hv
  exact ⟨σ, h₁⟩

/-- The complement has the same automorphisms, so it is vertex-transitive whenever `G` is. -/
@[toIsoGraph IsVertexTransitive.compl]
theorem isVertexTransitive_compl (h : G.IsVertexTransitive) :
    Gᶜ.IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ⟩ := h u v
  refine ⟨autoOfPerm (G := Gᶜ) σ.toEquiv fun x y ↦ ?_, hσ⟩
  show (decide (σ x ≠ σ y) && !G.Adj (σ x) (σ y)) = (decide (x ≠ y) && !G.Adj x y)
  rw [σ.adj_eq]
  simp [(RelIso.injective σ).eq_iff]

theorem isVertexTransitive_empty (n : ℕ) : (empty n).IsVertexTransitive := by
  rw [empty_eq_ofRel]
  exact isVertexTransitive_ofRel _ _ fun u v ↦ ⟨Equiv.swap u v, fun _ _ ↦ rfl, by simp⟩

/-- Vacuously: `empty n` has no arcs to move around. -/
theorem isArcTransitive_empty (n : ℕ) : (empty n).IsArcTransitive := by
  intro u v u' v' huv _
  simp at huv

theorem isVertexTransitive_complete (n : ℕ) : (complete n).IsVertexTransitive := by
  rw [complete_eq_ofRel]
  exact isVertexTransitive_ofRel _ _ fun u v ↦ ⟨Equiv.swap u v, fun _ _ ↦ rfl, by simp⟩

theorem isArcTransitive_complete (n : ℕ) : (complete n).IsArcTransitive := by
  rw [complete_eq_ofRel]
  refine isArcTransitive_ofRel _ _ fun u v u' v' huv hu'v' _ _ ↦ ?_
  obtain ⟨σ, h₁, h₂⟩ := exists_perm_apply_apply huv hu'v'
  exact ⟨σ, fun _ _ ↦ rfl, h₁, h₂⟩

/-! ### Cycles

The successor relation `(i + 1) % n = j` defining `cycle n` is the group-theoretic successor on
`Fin n`, so the rotations `x ↦ x + d` preserve it and the reflections `x ↦ c - x` reverse it —
and reversing it is enough, since `ofRel` symmetrises.  Together they act transitively on arcs:
rotations match up two arcs that run the same way round, reflections two that run oppositely. -/

private theorem cycle_rel (n : ℕ) [NeZero n] (x y : Fin n) :
    ((x.1 + 1) % n == y.1) = decide (x + 1 = y) := by
  rw [show ((x + 1 : Fin n)) = ⟨(x.1 + 1) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩ from ?_]
  · simp [Fin.ext_iff]
    rfl
  · apply Fin.ext
    simp [Fin.add_def, Nat.add_mod_mod]

private theorem cycle_trans_iff {n : ℕ} [NeZero n] (d x y : Fin n) :
    (x + d + 1 = y + d) ↔ (x + 1 = y) := by
  rw [add_right_comm, add_left_inj]

private theorem cycle_refl_iff {n : ℕ} [NeZero n] (c a b : Fin n) :
    (c - a + 1 = c - b) ↔ (b + 1 = a) := by
  constructor
  · intro h
    have h2 : c - a = c - (b + 1) := by rw [sub_add_eq_sub_sub, ← h]; simp
    exact (sub_right_injective h2).symm
  · rintro rfl
    rw [sub_add_eq_sub_sub, sub_add_cancel]

theorem isVertexTransitive_cycle (n : ℕ) : (cycle n).IsVertexTransitive := by
  match n with
  | 0 => intro u _; exact (u : Fin 0).elim0
  | (m + 1) =>
    rw [cycle]
    refine isVertexTransitive_ofRel _ _ fun u v ↦
      ⟨Equiv.addRight (v - u), fun x y ↦ ?_, by simp⟩
    simp only [Equiv.coe_addRight, cycle_rel, cycle_trans_iff]

theorem isArcTransitive_cycle (n : ℕ) : (cycle n).IsArcTransitive := by
  match n with
  | 0 => intro u _ _ _ _ _; exact (u : Fin 0).elim0
  | (m + 1) =>
    rw [cycle]
    refine isArcTransitive_ofRel _ _ fun u v u' v' _ _ h h' ↦ ?_
    have htrans (d : Fin (m + 1)) (x y : Fin (m + 1)) :
        ((((x + d).1 + 1) % (m + 1) == (y + d).1) || (((y + d).1 + 1) % (m + 1) == (x + d).1)) =
          ((((x.1 + 1) % (m + 1)) == y.1) || (((y.1 + 1) % (m + 1)) == x.1)) := by
      simp only [cycle_rel, cycle_trans_iff]
    have hrefl (c : Fin (m + 1)) (x y : Fin (m + 1)) :
        ((((c - x).1 + 1) % (m + 1) == (c - y).1) || (((c - y).1 + 1) % (m + 1) == (c - x).1)) =
          ((((x.1 + 1) % (m + 1)) == y.1) || (((y.1 + 1) % (m + 1)) == x.1)) := by
      simp only [cycle_rel, cycle_refl_iff, Bool.or_comm]
    simp only [cycle_rel, Bool.or_eq_true, decide_eq_true_eq] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · refine ⟨Equiv.addRight (u' - u), fun x y ↦ by
        simpa only [Equiv.coe_addRight] using htrans (u' - u) x y, by simp, ?_⟩
      simp only [Equiv.coe_addRight, ← h]
      rw [add_right_comm, add_comm u (u' - u), sub_add_cancel]
      exact h'
    · refine ⟨Equiv.subLeft (u' + u), fun x y ↦ by
        simpa only [Equiv.subLeft_apply] using hrefl (u' + u) x y, ?_, ?_⟩
      · rw [Equiv.subLeft_apply, add_sub_cancel_right]
      · rw [Equiv.subLeft_apply, ← h, sub_add_eq_sub_sub, add_sub_cancel_right, ← h',
          add_sub_cancel_right]
    · refine ⟨Equiv.subLeft (u' + u), fun x y ↦ by
        simpa only [Equiv.subLeft_apply] using hrefl (u' + u) x y, ?_, ?_⟩
      · rw [Equiv.subLeft_apply, add_sub_cancel_right]
      · rw [Equiv.subLeft_apply, ← h, add_comm v 1, ← add_assoc, add_sub_cancel_right, h']
    · refine ⟨Equiv.addRight (u' - u), fun x y ↦ by
        simpa only [Equiv.coe_addRight] using htrans (u' - u) x y, by simp, ?_⟩
      subst h
      subst h'
      rw [Equiv.coe_addRight, add_sub_add_right_eq_sub]
      simp

/-! ### Products

An automorphism of each factor gives an automorphism of any of the four products, acting
coordinatewise. -/

theorem isVertexTransitive_cartesianProduct (H : CGraph)
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (G □g H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := G □g H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (G □g H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [cartesianProduct_adj, σ.adj_eq, τ.adj_eq, (RelIso.injective σ).eq_iff,
    (RelIso.injective τ).eq_iff]

theorem isVertexTransitive_tensorProduct (H : CGraph)
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (G ⊗g H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := G ⊗g H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (G ⊗g H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [tensorProduct_adj, σ.adj_eq, τ.adj_eq]

theorem isVertexTransitive_strongProduct (H : CGraph)
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (G ⊠g H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := G ⊠g H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (G ⊠g H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [strongProduct_adj, σ.adj_eq, τ.adj_eq, (RelIso.injective σ).eq_iff,
    (RelIso.injective τ).eq_iff, ne_eq, Prod.ext_iff]

theorem isVertexTransitive_lexProduct (H : CGraph)
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (G ·g H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := G ·g H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (G ·g H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [lexProduct_adj, σ.adj_eq, τ.adj_eq, (RelIso.injective σ).eq_iff]

end

/-- Strongly regular graphs are regular, so their degree sequence is constant. -/
@[toIsoGraph]
theorem IsSRGWith.degSequence {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) :
    G.degSequence = List.replicate n k := by
  rw [degSequence_of_regular G h.regular, FinEnum.card_eq_fintypeCard', h.card]

section
variable {G H : CGraph}

/-! ### Strongly regular graphs of diameter two -/

/-- In a strongly regular graph with `μ > 0`, any two distinct non-adjacent vertices have a
common neighbour — that is what `μ` counts. -/
theorem IsSRGWith.exists_common_neighbor {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hμ : 0 < μ) {u v : G.V} (hne : u ≠ v) (hadj : ¬ G.toSimple.Adj u v) :
    ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v := by
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have hcard : 0 < Fintype.card (G.toSimple.commonNeighbors u v) := by
    rw [h'.of_not_adj hne hadj]; exact hμ
  obtain ⟨w, hw⟩ := Fintype.card_pos_iff.1 hcard
  exact ⟨w, hw.1, hw.2.symm⟩

/-- A strongly regular graph that is not complete has a non-adjacent pair. -/
theorem IsSRGWith.exists_not_adj {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hk : k + 1 < n) : ∃ u v : G.V, u ≠ v ∧ ¬ G.toSimple.Adj u v := by
  classical
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have hn : FinEnum.card G.V = n := FinEnum.card_eq_fintypeCard'.trans h'.card
  obtain ⟨u⟩ := FinEnum.card_pos_iff.1 (show 0 < FinEnum.card G.V by omega)
  by_contra hcon
  push Not at hcon
  have hnbrs : G.nbrs u = Finset.univ.erase u := by
    ext w
    simp only [mem_nbrs, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hw
      rintro rfl
      rw [adj_self] at hw
      exact Bool.noConfusion hw
    · intro hw
      exact hcon u w (Ne.symm hw)
  have hcard : (G.nbrs u).card = k := by rw [card_nbrs_eq_degree, h'.regular u]
  rw [hnbrs, Finset.card_erase_of_mem (Finset.mem_univ u), FinEnum.card_univ, hn] at hcard
  omega

/-- **A strongly regular graph with `μ > 0` is connected**: any two non-adjacent vertices are
joined by a path of length two. -/
@[toIsoGraph]
theorem IsSRGWith.isConnected {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) (hμ : 0 < μ)
    (hn : 0 < n) : G.IsConnected := by
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have : Nonempty G.V := Fintype.card_pos_iff.1 (by rw [h'.card]; exact hn)
  refine SimpleGraph.connected_of_ediam_ne_top (ne_top_of_le_ne_top (by simp) (G.ediam_le_two ?_))
  intro u v huv
  by_cases hadj : G.toSimple.Adj u v
  · exact Or.inl hadj
  · exact Or.inr (h.exists_common_neighbor hμ huv hadj)

/-- **A strongly regular graph with `μ > 0` that is not complete has diameter two.** -/
@[toIsoGraph]
theorem IsSRGWith.diameter_eq_two {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hμ : 0 < μ) (hk : k + 1 < n) : G.diameter = 2 := by
  obtain ⟨u, v, hne, hadj⟩ := h.exists_not_adj hk
  refine G.diameter_eq_two (fun a b hab ↦ ?_) hne hadj
  by_cases hab2 : G.toSimple.Adj a b
  · exact Or.inl hab2
  · exact Or.inr (h.exists_common_neighbor hμ hab hab2)

/-! ### Girth five from strong regularity -/

/-- **A strongly regular graph with `ℓ = 0` and `μ = 1` has girth at least five**: `ℓ = 0` rules
out triangles and `μ = 1` rules out squares, since the two opposite corners of a square would
share two neighbours. -/
theorem IsSRGWith.five_le_girth {G : CGraph} {n k : ℕ} (h : G.IsSRGWith n k 0 1)
    (hnac : ¬ G.IsAcyclic) : 5 ≤ G.girth := by
  have h' : G.toSimple.IsSRGWith n k 0 1 := h
  refine _root_.CGraph.five_le_girth (fun x y z h1 h2 h3 ↦ ?_) (fun x y z t h1 h2 h3 h4 ↦ ?_) hnac
  · have hzx : G.toSimple.Adj z x := (toSimple_adj _ _ _).2 h3
    have hemp := h'.of_adj z x hzx
    rw [Fintype.card_eq_zero_iff] at hemp
    exact hemp.false ⟨y, ((toSimple_adj _ _ _).2 h2).symm, (toSimple_adj _ _ _).2 h1⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨hxz, hyt⟩ := hcon
    have hy : y ∈ G.toSimple.commonNeighbors x z :=
      ⟨(toSimple_adj _ _ _).2 h1, ((toSimple_adj _ _ _).2 h2).symm⟩
    have ht : t ∈ G.toSimple.commonNeighbors x z :=
      ⟨((toSimple_adj _ _ _).2 h4).symm, (toSimple_adj _ _ _).2 h3⟩
    by_cases hadj : G.toSimple.Adj x z
    · have hemp := h'.of_adj x z hadj
      rw [Fintype.card_eq_zero_iff] at hemp
      exact hemp.false ⟨y, hy⟩
    · have hcard := h'.of_not_adj hxz hadj
      have h2card : 1 < Fintype.card (G.toSimple.commonNeighbors x z) :=
        Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨y, hy⟩, ⟨t, ht⟩, by simpa using hyt⟩
      omega

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

@[toIsoGraph]
theorem autCount_pos (G : CGraph) : 0 < G.autCount := Nat.card_pos

/-- An automorphism is in particular a permutation of the vertices. -/
@[toIsoGraph]
theorem autCount_le_factorial (G : CGraph) : G.autCount ≤ Nat.factorial (FinEnum.card G.V) := by
  classical
  calc G.autCount ≤ Nat.card (G.V ≃ G.V) :=
        Nat.card_le_card_of_injective (fun a : G.toSimple ≃g G.toSimple ↦ a.toEquiv)
          (fun _ _ h ↦ by ext v; exact congrArg (fun e : G.V ≃ G.V ↦ e v) h)
    _ = Nat.factorial (FinEnum.card G.V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← FinEnum.card_eq_fintypeCard']

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

/-- **A cycle has at most `2n` automorphisms.**  An automorphism is determined by the image of
`0` and the image of `1`, and the latter is one of the two neighbours of the former, so the pair
`(f 0, which neighbour)` is a complete and faithful record of `f`. -/
theorem autCount_cycle_le {N : ℕ} (hN : 3 ≤ N) : (cycle N).autCount ≤ 2 * N := by
  have h0N : 0 < N := by omega
  have h1N : 1 < N := by omega
  set code : (cycle N ≃cg cycle N) → (cycle N).V × Bool := fun f ↦
    (f ⟨0, h0N⟩, decide ((f ⟨1, h1N⟩).1 = ((f ⟨0, h0N⟩).1 + 1) % N)) with hcode
  have hadj01 : (cycle N).Adj ⟨0, h0N⟩ ⟨1, h1N⟩ = true := cycle_adj_of_succ rfl
  have hnbr : ∀ f : cycle N ≃cg cycle N,
      (f ⟨1, h1N⟩).1 = ((f ⟨0, h0N⟩).1 + 1) % N ∨
        (f ⟨1, h1N⟩).1 = ((f ⟨0, h0N⟩).1 + N - 1) % N := by
    intro f
    rw [← cycle_adj_eq_iff hN, f.adj_eq]
    exact hadj01
  have hinj : Function.Injective code := by
    intro f g h
    rw [hcode] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨he0, heb⟩ := h
    refine cycle_aut_eq hN he0 ?_
    refine Fin.ext ?_
    have hf := hnbr f
    have hg := hnbr g
    rw [he0] at hf
    rw [he0, decide_eq_decide] at heb
    have hne := cycle_nbrs_ne hN (g ⟨0, h0N⟩)
    generalize ((g ⟨0, h0N⟩).1 + 1) % N = p at hf hg heb hne
    generalize ((g ⟨0, h0N⟩).1 + N - 1) % N = q at hf hg hne
    omega
  have hcard : Nat.card ((cycle N).V × Bool) = 2 * N := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod,
      ← FinEnum.card_eq_fintypeCard' (α := (cycle N).V), card_cycle, Fintype.card_bool]
    omega
  have := Nat.card_le_card_of_injective code hinj
  rw [hcard] at this
  exact this

/-- The automorphism count is `1` exactly for an asymmetric graph. -/
theorem autCount_eq_one_iff (G : CGraph) :
    G.autCount = 1 ↔ ∀ a : G.toSimple ≃g G.toSimple, a = RelIso.refl _ := by
  rw [autCount, Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, -⟩ a
    exact hsub.elim a _
  · intro h
    exact ⟨⟨fun a b ↦ (h a).trans (h b).symm⟩, ⟨RelIso.refl _⟩⟩

/-! ### Automorphisms versus degrees and symmetry -/

/-- Automorphisms preserve degrees, so a graph whose vertices all have distinct degrees is
asymmetric. -/
theorem autCount_eq_one_of_degree_injective (G : CGraph)
    (h : Function.Injective fun v : G.V ↦ G.toSimple.degree v) : G.autCount = 1 := by
  rw [autCount_eq_one_iff]
  intro a
  ext v
  exact h (SimpleGraph.Iso.degree_eq a v)

/-- A vertex-transitive graph has at least `|V|` automorphisms: the automorphisms carrying a fixed
base vertex to each vertex in turn are already pairwise distinct. -/
@[toIsoGraph V_le_autCount_of_isVertexTransitive]
theorem card_le_autCount_of_isVertexTransitive (G : CGraph) [Nonempty G.V]
    (h : G.IsVertexTransitive) : FinEnum.card G.V ≤ G.autCount := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  choose f hf using h v₀
  have : Finite (G ≃cg G) := G.instFiniteAut
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (f u) v₀ = (f v) v₀ := by rw [huv]
    rw [hf u, hf v] at h1
    exact h1
  calc FinEnum.card G.V = Nat.card G.V := by
        rw [FinEnum.card_eq_fintypeCard', Nat.card_eq_fintype_card]
    _ ≤ Nat.card (G ≃cg G) := Nat.card_le_card_of_injective f hinj
    _ = G.autCount := rfl

/-- Too few automorphisms to move a base vertex everywhere. -/
@[toIsoGraph]
theorem not_isVertexTransitive_of_autCount_lt (G : CGraph) [Nonempty G.V]
    (h : G.autCount < FinEnum.card G.V) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.card_le_autCount_of_isVertexTransitive hvt) (by omega)

/-- Too few automorphisms to move a base arc everywhere. -/
@[toIsoGraph]
theorem not_isArcTransitive_of_autCount_lt (G : CGraph) (h : G.autCount < 2 * G.E) :
    ¬ G.IsArcTransitive := fun hat ↦
  absurd (G.two_mul_E_le_autCount_of_isArcTransitive hat) (by omega)

/-- **The cycle `Cₙ` has exactly `2n` automorphisms** for `n ≥ 3`: its automorphism group is the
dihedral group of order `2n`.  The lower bound is arc-transitivity together with the edge count,
and the upper bound is `autCount_cycle_le`. -/
@[toIsoGraph]
theorem autCount_cycle (n : ℕ) : (cycle (n + 3)).autCount = 2 * (n + 3) := by
  have hle := autCount_cycle_le (N := n + 3) (by omega)
  have hge := two_mul_E_le_autCount_of_isArcTransitive _ (isArcTransitive_cycle (n + 3))
  rw [E_cycle] at hge
  omega

@[toIsoGraph]
theorem autCount_mul_le_autCount_disjUnion (G H : CGraph) :
    G.autCount * H.autCount ≤ (G ⊕g H).autCount :=
  mul_autCount_le_autCount disjUnionAuto fun a a' b b' h ↦ by
    refine ⟨?_, ?_⟩
    · ext x
      exact Sum.inl_injective
        (congrArg (fun σ : G ⊕g H ≃cg G ⊕g H ↦ σ (.inl x)) h)
    · ext y
      exact Sum.inr_injective
        (congrArg (fun σ : G ⊕g H ≃cg G ⊕g H ↦ σ (.inr y)) h)

@[toIsoGraph]
theorem autCount_mul_le_autCount_join (G H : CGraph) :
    G.autCount * H.autCount ≤ (G ∇g H).autCount := by
  have h := autCount_mul_le_autCount_disjUnion Gᶜ Hᶜ
  rw [autCount_compl, autCount_compl, ← autCount_compl (Gᶜ ⊕g Hᶜ)] at h
  rwa [join_eq_compl_disjUnion]

/-- Two copies of the same graph can also be exchanged, which doubles the bound. -/
@[toIsoGraph]
theorem two_mul_autCount_mul_le_autCount_disjUnion_self (G : CGraph) [Nonempty G.V] :
    2 * (G.autCount * G.autCount) ≤ (G ⊕g G).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  have : Finite (G ⊕g G ≃cg G ⊕g G) := (G ⊕g G).instFiniteAut
  set f : Bool × (G ≃cg G) × (G ≃cg G) → (G ⊕g G ≃cg G ⊕g G) :=
    fun p ↦ if p.1 then (disjUnionAuto p.2.1 p.2.2).trans (disjUnionSwapAuto G)
      else disjUnionAuto p.2.1 p.2.2 with hfdef
  -- The two copies are told apart by which side `inl x₀` lands in, and each factor is read back
  -- off by forgetting the side.
  have hside : ∀ (c : Bool) (a b : G ≃cg G), (f (c, a, b) (Sum.inl x₀)).isRight = c := by
    rintro (_ | _) a b <;> simp [hfdef]
  have hfst : ∀ (c : Bool) (a b : G ≃cg G) (x : G.V),
      Sum.elim id id (f (c, a, b) (Sum.inl x)) = a x := by
    rintro (_ | _) a b x <;> simp [hfdef]
  have hsnd : ∀ (c : Bool) (a b : G ≃cg G) (y : G.V),
      Sum.elim id id (f (c, a, b) (Sum.inr y)) = b y := by
    rintro (_ | _) a b y <;> simp [hfdef]
  have hinj : Function.Injective f := by
    rintro ⟨c, a, b⟩ ⟨c', a', b'⟩ h
    have hc : c = c' := by rw [← hside c a b, ← hside c' a' b', h]
    subst hc
    have ha : a = a' := by
      ext x
      rw [← hfst c a b x, ← hfst c a' b' x, h]
    have hb : b = b' := by
      ext y
      rw [← hsnd c a b y, ← hsnd c a' b' y, h]
    rw [ha, hb]
  calc 2 * (G.autCount * G.autCount) = Nat.card (Bool × (G ≃cg G) × (G ≃cg G)) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
        rfl
    _ ≤ Nat.card (G ⊕g G ≃cg G ⊕g G) := Nat.card_le_card_of_injective f hinj
    _ = (G ⊕g G).autCount := rfl

@[toIsoGraph]
theorem autCount_mul_le_autCount_cartesianProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (G □g H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount cartesianProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg
      (fun σ : G □g H ≃cg G □g H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg
      (fun σ : G □g H ≃cg G □g H ↦ (σ (x₀, y)).2) h
    simpa using this

@[toIsoGraph]
theorem autCount_mul_le_autCount_tensorProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (G ⊗g H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount tensorProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : G ⊗g H ≃cg G ⊗g H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : G ⊗g H ≃cg G ⊗g H ↦ (σ (x₀, y)).2) h
    simpa using this

@[toIsoGraph]
theorem autCount_mul_le_autCount_strongProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (G ⊠g H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount strongProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : G ⊠g H ≃cg G ⊠g H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : G ⊠g H ≃cg G ⊠g H ↦ (σ (x₀, y)).2) h
    simpa using this

@[toIsoGraph]
theorem autCount_mul_le_autCount_lexProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (G ·g H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount lexProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : G ·g H ≃cg G ·g H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : G ·g H ≃cg G ·g H ↦ (σ (x₀, y)).2) h
    simpa using this

/-! ### Regular graphs -/

theorem isRegularWith_iff_forall_degree {G : CGraph} {k : ℕ} :
    G.IsRegularWith k ↔ ∀ v : G.V, G.toSimple.degree v = k := Iff.rfl

@[toIsoGraph]
theorem IsRegularWith.degSequence {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.degSequence = List.replicate (FinEnum.card G.V) k := degSequence_of_regular G h

/-- Squeezing the degrees between the two extremes forces regularity. -/
@[toIsoGraph]
theorem isRegularWith_of_maxDeg_le_of_le_minDeg {G : CGraph} {k : ℕ}
    (h1 : G.maxDeg ≤ k) (h2 : k ≤ G.minDeg) : G.IsRegularWith k := fun v ↦
  le_antisymm (le_trans (G.degree_le_maxDeg v) h1) (le_trans h2 (G.minDeg_le_degree v))

@[toIsoGraph]
theorem IsRegularWith.maxDeg_eq {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) [Nonempty G.V] :
    G.maxDeg = k := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  exact le_antisymm (maxDeg_le_of_forall fun v ↦ (h v).le) (h v₀ ▸ G.degree_le_maxDeg v₀)

@[toIsoGraph]
theorem IsRegularWith.minDeg_eq {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) [Nonempty G.V] :
    G.minDeg = k := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  exact le_antisymm (h v₀ ▸ G.minDeg_le_degree v₀) (le_minDeg_of_forall v₀ fun v ↦ (h v).ge)

/-- **Strongly regular graphs are regular**, with the same degree parameter. -/
@[toIsoGraph]
theorem IsSRGWith.isRegularWith {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) :
    G.IsRegularWith k := SimpleGraph.IsSRGWith.regular h

/-- **The complement of a `k`-regular graph is `(n - 1 - k)`-regular.** -/
@[toIsoGraph]
theorem IsRegularWith.compl {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    Gᶜ.IsRegularWith (FinEnum.card G.V - 1 - k) := fun v ↦ by
  rw [degree_compl, h v]

/-- A disjoint union of two `k`-regular graphs is `k`-regular. -/
@[toIsoGraph]
theorem IsRegularWith.disjUnion {G H : CGraph} {k : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith k) : (G ⊕g H).IsRegularWith k := by
  rintro (a | b)
  · rw [degree_disjUnion_inl]; exact hG a
  · rw [degree_disjUnion_inr]; exact hH b

/-- A join is regular exactly when the two sides end up with the same total degree: each vertex
of `G` picks up all of `H` and vice versa. -/
@[toIsoGraph]
theorem IsRegularWith.join {G H : CGraph} {k l m : ℕ}
    (hG : G.IsRegularWith k) (hH : H.IsRegularWith l)
    (h1 : k + FinEnum.card H.V = m) (h2 : FinEnum.card G.V + l = m) :
    (G ∇g H).IsRegularWith m := by
  rintro (a | b)
  · rw [degree_join_inl, hG a]; exact h1
  · rw [degree_join_inr, hH b]; exact h2

/-- The line graph of a `k`-regular graph is `(2k - 2)`-regular. -/
@[toIsoGraph]
theorem IsRegularWith.lineGraph {G : CGraph} {k : ℕ}
    (h : G.IsRegularWith k) : (CGraph.lineGraph G).IsRegularWith (2 * k - 2) := by
  refine lineGraph_vertex_cases fun u v huv ↦ ?_
  rw [degree_lineGraph_mk G huv, h u, h v]
  omega

/-! ### Consequences of regularity -/

theorem adj_eq_false_of_isRegularWith_zero {G : CGraph} (h : G.IsRegularWith 0) (x y : G.V) :
    G.Adj x y = false := by
  by_contra hxy
  have hadj : G.toSimple.Adj x y := by
    simp only [toSimple_adj]
    simpa using hxy
  have hpos : 0 < G.toSimple.degree x := (G.toSimple.degree_pos_iff_exists_adj x).2 ⟨y, hadj⟩
  have hd : G.toSimple.degree x = 0 := h x
  omega

/-! ### Girth three from strong regularity -/

/-- **A strongly regular graph with `ℓ > 0` has girth three**: `k > 0` produces an edge, and
`ℓ > 0` says its two endpoints have a common neighbour, which closes a triangle. -/
@[toIsoGraph]
theorem IsSRGWith.girth_eq_three {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hn : 0 < n) (hk : 0 < k) (hℓ : 0 < ℓ) : G.girth = 3 := by
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have hcard : FinEnum.card G.V = n := by
    rw [FinEnum.card_eq_fintypeCard']; exact h'.card
  obtain ⟨u⟩ := FinEnum.card_pos_iff.1 (show 0 < FinEnum.card G.V by omega)
  have hdeg : G.toSimple.degree u = k := h'.regular u
  obtain ⟨v, hv⟩ := (G.toSimple.degree_pos_iff_exists_adj u).1 (by omega)
  have hpos : 0 < Fintype.card (G.toSimple.commonNeighbors u v) := by
    rw [h'.of_adj u v hv]; exact hℓ
  obtain ⟨w, hw⟩ := Fintype.card_pos_iff.1 hpos
  exact girth_eq_three_of_triangle ((toSimple_adj _ _ _).1 hv)
    ((toSimple_adj _ _ _).1 hw.2) ((toSimple_adj _ _ _).1 hw.1.symm)

end

end CGraph

namespace IsoGraph

/-! ### Vertex- and arc-transitivity -/

@[simp] theorem isVertexTransitive_empty (n : ℕ) : IsVertexTransitive (empty n) :=
  CGraph.isVertexTransitive_empty n

@[simp] theorem isArcTransitive_empty (n : ℕ) : IsArcTransitive (empty n) :=
  CGraph.isArcTransitive_empty n

@[simp] theorem isVertexTransitive_complete (n : ℕ) : IsVertexTransitive (complete n) :=
  CGraph.isVertexTransitive_complete n

@[simp] theorem isArcTransitive_complete (n : ℕ) : IsArcTransitive (complete n) :=
  CGraph.isArcTransitive_complete n

@[simp] theorem isVertexTransitive_cycle (n : ℕ) : IsVertexTransitive (cycle n) :=
  CGraph.isVertexTransitive_cycle n

@[simp] theorem isArcTransitive_cycle (n : ℕ) : IsArcTransitive (cycle n) :=
  CGraph.isArcTransitive_cycle n

@[simp] theorem isVertexTransitive_compl (G : IsoGraph) :
    IsVertexTransitive Gᶜ ↔ IsVertexTransitive G :=
  ⟨fun h ↦ by simpa using h.compl, IsVertexTransitive.compl⟩

/-- The handshake lemma for a strongly regular graph: `n` vertices of degree `k` give `n * k / 2`
edges. -/
theorem IsSRGWith.two_mul_E {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    2 * G.E = n * k := by
  rw [← sum_degSequence, h.degSequence, List.sum_replicate, smul_eq_mul]

theorem ne_of_isVertexTransitive {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : ¬ IsVertexTransitive H) : G ≠ H := ne_of_pred hG hH

theorem ne_of_isArcTransitive {G H : IsoGraph} (hG : IsArcTransitive G)
    (hH : ¬ IsArcTransitive H) : G ≠ H := ne_of_pred hG hH

/-! ### Counting automorphisms -/

/-- **A graph and its complement have the same automorphisms.** -/
@[simp] theorem autCount_compl (G : IsoGraph) : Gᶜ.autCount = G.autCount := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, compl_mk, autCount_mk, autCount_mk]
  exact CGraph.autCount_compl _

/-- Two graphs with different automorphism counts are different. -/
theorem ne_of_autCount_ne {G H : IsoGraph} (h : G.autCount ≠ H.autCount) : G ≠ H :=
  fun hGH ↦ h (hGH ▸ rfl)

/-! ### Self-complementary graphs

`IsSelfComplementary G` is the equation `Gᶜ = G`, defined in `Invariants/Derived.lean`; what is
here is which graphs satisfy it and what it forces. -/

@[simp] theorem isSelfComplementary_empty_zero : IsSelfComplementary (empty 0) := by
  show (empty 0)ᶜ = empty 0
  rw [compl_empty, complete_zero]

@[simp] theorem isSelfComplementary_empty_one : IsSelfComplementary (empty 1) := by
  show (empty 1)ᶜ = empty 1
  rw [compl_empty, complete_one]

@[simp] theorem isSelfComplementary_path_four : IsSelfComplementary (path 4) :=
  compl_path_four

@[simp] theorem isSelfComplementary_cycle_five : IsSelfComplementary (cycle 5) :=
  compl_cycle_five

end IsoGraph
