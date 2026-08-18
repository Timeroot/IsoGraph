import IsoGraph.Containment.Monotone

/-!
# Splitting a containment along a disjoint union

`Containment/Monotone.lean` asks whether an operation preserves a containment; this file asks the
converse question for the disjoint union, and answers the half of it that is about the *maps*: if
`H ⊕g K` sits inside `C ⊕g D`, how do the two sit inside the two?

Each vertex of the pattern lands in one summand of the host, and no edge of the pattern can join
two vertices that land in different ones, because the host has no edge between its summands.  So
the pattern is cut in two by the side its vertices go to, and the cut is along whole connected
pieces: `H` splits as `H₁ ⊕g H₂` and `K` as `K₁ ⊕g K₂`, with `H₁ ⊕g K₁` inside `C` and
`H₂ ⊕g K₂` inside `D`.  That is `SubgraphOf.exists_split`, and `IsSubgraphOf.exists_split_disjUnion`
on isomorphism classes; `Containment/Ordered.lean` turns it into the cancellation theorem
`H ⊕g K ≤ₛ G ⊕g K → H ≤ₛ G` by induction on the number of vertices of `K`.

The construction the cut needs is `CGraph.induce G s`, the subgraph of `G` on the vertices where
`s` is true, on the subtype `{v // s v}`.  It is not in `Graphs/Constructions.lean` with the rest
of the constructions because it cannot follow them to `IsoGraph`: its second argument is a
predicate on the vertices of *this* representative, and an isomorphism class has no vertices.  It
comes with the two isomorphisms that make it useful here — `Iso.induceSplit`, which is the
splitting itself, and `Iso.induceDisjUnion`, which says that inducing on a disjoint union induces
on each summand.

The complement appears at the end, for one reason: `(G ∇g H)ᶜ = Gᶜ ⊕g Hᶜ`, so a fact about the
join follows from the same fact about the disjoint union in any order that complementation
preserves.  The induced subgraph order is the one that does — `InducedSubgraphOf.compl` — and it
is how the join is cancelled there.
-/

set_option autoImplicit false

namespace Sum

variable {α β : Type}

theorem eq_inl_getLeft (x : α ⊕ β) (h : x.isLeft) : x = .inl (x.getLeft h) :=
  eq_left_iff_getLeft_eq.2 ⟨h, rfl⟩

theorem eq_inr_getRight (x : α ⊕ β) (h : x.isRight) : x = .inr (x.getRight h) :=
  eq_right_iff_getRight_eq.2 ⟨h, rfl⟩

end Sum

namespace CGraph

/-! ## The subgraph induced on a set of vertices -/

/-- The subgraph of `G` induced on the vertices where `s` is true. -/
def induce (G : CGraph) (s : G.V → Bool) : CGraph where
  V := {v : G.V // s v}
  Adj x y := G.Adj x y
  symm x y := G.symm x y
  loopless x := G.loopless x

@[simp] theorem induce_adj (G : CGraph) (s : G.V → Bool) (x y : (G.induce s).V) :
    (G.induce s).Adj x y = G.Adj x.1 y.1 := rfl

/-- What `G` induces on a set of its vertices is an induced subgraph of `G`. -/
def InducedSubgraphOf.induce (G : CGraph) (s : G.V → Bool) :
    (G.induce s).InducedSubgraphOf G where
  toFun := Subtype.val
  injective' := Subtype.val_injective
  map_adj' _ _ h := h
  adj_map' _ _ h := h

/-- The vertices of `G`, sorted into the two sides of `s`. -/
def induceSplitEquiv (G : CGraph) (s : G.V → Bool) :
    G.V ≃ (G.induce s ⊕g G.induce fun v ↦ !s v).V where
  toFun v := if h : s v then .inl ⟨v, h⟩ else .inr ⟨v, by simp [h]⟩
  invFun x := Sum.elim Subtype.val Subtype.val x
  left_inv v := by by_cases h : s v <;> simp [h]
  right_inv x := by
    rcases x with ⟨v, hv⟩ | ⟨v, hv⟩
    · simp [hv]
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      simp [hv]

theorem induceSplitEquiv_apply_pos (G : CGraph) (s : G.V → Bool) (v : G.V) (h : s v) :
    induceSplitEquiv G s v = .inl ⟨v, h⟩ := dif_pos h

theorem induceSplitEquiv_apply_neg (G : CGraph) (s : G.V → Bool) (v : G.V) (h : ¬s v) :
    induceSplitEquiv G s v = .inr ⟨v, by simp [h]⟩ := dif_neg h

/-- **A graph no edge of which crosses `s` is the disjoint union of its two sides.** -/
def Iso.induceSplit (G : CGraph) (s : G.V → Bool) (h : ∀ x y, G.Adj x y → s x = s y) :
    G ≃cg G.induce s ⊕g G.induce fun v ↦ !s v :=
  isoOfAdj (H := G.induce s ⊕g G.induce fun v ↦ !s v) (induceSplitEquiv G s) fun x y ↦ by
    by_cases hx : s x <;> by_cases hy : s y
    · rw [induceSplitEquiv_apply_pos _ _ _ hx, induceSplitEquiv_apply_pos _ _ _ hy]; rfl
    · rw [induceSplitEquiv_apply_pos _ _ _ hx, induceSplitEquiv_apply_neg _ _ _ hy]
      exact (Bool.eq_false_iff.2 fun hadj ↦ hy (h x y hadj ▸ hx)).symm
    · rw [induceSplitEquiv_apply_neg _ _ _ hx, induceSplitEquiv_apply_pos _ _ _ hy]
      exact (Bool.eq_false_iff.2 fun hadj ↦ hx (h x y hadj ▸ hy)).symm
    · rw [induceSplitEquiv_apply_neg _ _ _ hx, induceSplitEquiv_apply_neg _ _ _ hy]; rfl

/-- Inducing on a disjoint union induces on each summand. -/
def Iso.induceDisjUnion (G H : CGraph) (s : (G ⊕g H).V → Bool) :
    (G ⊕g H).induce s ≃cg G.induce (fun v ↦ s (.inl v)) ⊕g H.induce fun v ↦ s (.inr v) :=
  isoOfAdj (G := (G ⊕g H).induce s)
    { toFun := fun x ↦ match x with
        | ⟨.inl a, ha⟩ => .inl ⟨a, ha⟩
        | ⟨.inr b, hb⟩ => .inr ⟨b, hb⟩
      invFun := fun x ↦ match x with
        | .inl ⟨a, ha⟩ => ⟨.inl a, ha⟩
        | .inr ⟨b, hb⟩ => ⟨.inr b, hb⟩
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl }
    (by rintro ⟨_ | _, _⟩ ⟨_ | _, _⟩ <;> rfl)

/-! ## Cutting an inclusion in two -/

namespace SubgraphOf

variable {A C D : CGraph}

/-- Which side of a disjoint union each vertex of the pattern lands on. -/
def side (f : A.SubgraphOf (C ⊕g D)) (v : A.V) : Bool := (f v).isLeft

/-- No edge of the pattern crosses the sides: the host has no edge between its summands. -/
theorem side_eq_of_adj (f : A.SubgraphOf (C ⊕g D)) {x y : A.V} (h : A.Adj x y) :
    f.side x = f.side y := by
  have hadj := f.map_adj h
  cases hx : f x <;> cases hy : f y <;> rw [hx, hy] at hadj <;> simp_all [side]

theorem isRight_of_not_side (f : A.SubgraphOf (C ⊕g D)) {v : A.V} (h : !f.side v) :
    (f v).isRight := by
  cases hv : f v <;> simp_all [side]

/-- The part of a subgraph inclusion that lands in the left summand. -/
def splitLeft (f : A.SubgraphOf (C ⊕g D)) : (A.induce f.side).SubgraphOf C where
  toFun x := (f x.1).getLeft x.2
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inl_getLeft (f x.1) x.2, Sum.eq_inl_getLeft (f y.1) y.2]
    exact congrArg Sum.inl hxy
  map_adj' x y hadj := by
    have h := f.map_adj (show A.Adj x.1 y.1 from hadj)
    rwa [Sum.eq_inl_getLeft (f x.1) x.2, Sum.eq_inl_getLeft (f y.1) y.2] at h

/-- The part of a subgraph inclusion that lands in the right summand. -/
def splitRight (f : A.SubgraphOf (C ⊕g D)) : (A.induce fun v ↦ !f.side v).SubgraphOf D where
  toFun x := (f x.1).getRight (f.isRight_of_not_side x.2)
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inr_getRight (f x.1) (f.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f y.1) (f.isRight_of_not_side y.2)]
    exact congrArg Sum.inr hxy
  map_adj' x y hadj := by
    have h := f.map_adj (show A.Adj x.1 y.1 from hadj)
    rwa [Sum.eq_inr_getRight (f x.1) (f.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f y.1) (f.isRight_of_not_side y.2)] at h

/-- **A subgraph inclusion between two disjoint unions splits into four.**  Each summand of the
pattern is cut in two by the summand of the host its vertices land in. -/
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).SubgraphOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).SubgraphOf c) ∧ Nonempty ((h₂ ⊕g k₂).SubgraphOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

end SubgraphOf

namespace InducedSubgraphOf

variable {A C D : CGraph}

@[inherit_doc SubgraphOf.side]
def side (f : A.InducedSubgraphOf (C ⊕g D)) (v : A.V) : Bool := f.toSubgraphOf.side v

/-- The part of an induced subgraph inclusion that lands in the left summand. -/
def splitLeft (f : A.InducedSubgraphOf (C ⊕g D)) : (A.induce f.side).InducedSubgraphOf C where
  toSubgraphOf := f.toSubgraphOf.splitLeft
  adj_map' x y hadj := by
    refine f.adj_map (x := x.1) (y := y.1) ?_
    rw [Sum.eq_inl_getLeft (f x.1) x.2, Sum.eq_inl_getLeft (f y.1) y.2]
    exact hadj

/-- The part of an induced subgraph inclusion that lands in the right summand. -/
def splitRight (f : A.InducedSubgraphOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.side v).InducedSubgraphOf D where
  toSubgraphOf := f.toSubgraphOf.splitRight
  adj_map' x y hadj := by
    refine f.adj_map (x := x.1) (y := y.1) ?_
    rw [Sum.eq_inr_getRight (f x.1) (f.toSubgraphOf.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f y.1) (f.toSubgraphOf.isRight_of_not_side y.2)]
    exact hadj

@[inherit_doc SubgraphOf.exists_split]
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).InducedSubgraphOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).InducedSubgraphOf c) ∧ Nonempty ((h₂ ⊕g k₂).InducedSubgraphOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.toSubgraphOf.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.toSubgraphOf.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

/-- **Complementation carries an induced subgraph inclusion to one between the complements.**  An
induced subgraph is decided by which vertices it keeps, and both graphs trade their edges for
their non-edges at once. -/
def compl {H G : CGraph} (f : H.InducedSubgraphOf G) : Hᶜ.InducedSubgraphOf Gᶜ where
  toFun := f
  injective' := f.injective
  map_adj' x y h := by
    simp only [compl_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true'] at h ⊢
    exact ⟨fun he ↦ h.1 (f.injective he), by rw [f.adj_eq]; exact h.2⟩
  adj_map' x y h := by
    simp only [compl_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true'] at h ⊢
    exact ⟨fun he ↦ h.1 (congrArg f he), by rw [← f.adj_eq]; exact h.2⟩

end InducedSubgraphOf

end CGraph

/-! ## On isomorphism classes -/

namespace IsoGraph

/-- **A subgraph inclusion between two disjoint unions splits into four.**  Each summand of the
pattern is cut in two by the summand of the host its vertices land in. -/
theorem IsSubgraphOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ₛ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ₛ C ∧ H₂ ⊕g K₂ ≤ₛ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isSubgraphOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isSubgraphOf_mk]; exact fc,
    by rw [disjUnion_mk, isSubgraphOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsInducedSubgraphOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ᵢₛ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ᵢₛ C ∧ H₂ ⊕g K₂ ≤ᵢₛ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isInducedSubgraphOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isInducedSubgraphOf_mk]; exact fc,
    by rw [disjUnion_mk, isInducedSubgraphOf_mk]; exact fd⟩

@[inherit_doc CGraph.InducedSubgraphOf.compl]
theorem IsInducedSubgraphOf.compl {H G : IsoGraph} (h : H ≤ᵢₛ G) : Hᶜ ≤ᵢₛ Gᶜ := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro h g ⟨f⟩
  exact ⟨f.compl⟩

end IsoGraph
