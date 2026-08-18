import IsoGraph.Containment.Algorithms.Cached
import IsoGraph.Containment.Monotone
import IsoGraph.Containment.Split
import IsoGraph.Values.Identities.Semiring

/-!
# The ordered algebraic structures

`Containment/Monotone.lean` proves that the sums and products of graphs are monotone in the
containment relations; `Values/Identities/Semiring.lean` packages those operations as `+` and `*`
in a scope apiece, and `Containment/Defs.lean` packages each relation as `≤` in a scope apiece.
This file is the two of them together: for every pair of scopes that can be opened at once, the
`Mathlib` class that says the order and the operation agree.

Nothing here is an instance globally — an instance is registered in the *order*'s scope, with its
type mentioning the operation's, so it is found exactly when both scopes are open:

```lean
open scoped IsoGraph.Subgraph IsoGraph.Semiring

example (a b c : IsoGraph) (h : a ≤ b) : a * c ≤ b * c := mul_le_mul_left h c
```

What each pair gets:

* the two sums, in the eight orders that are partial orders: `IsOrderedAddMonoid`, and in the
  homomorphism order, which is only a preorder, `AddLeftMono` and `AddRightMono`;
* the cartesian product, a commutative monoid, in the same eight: `IsOrderedMonoid`, again
  weakened to `MulLeftMono` and `MulRightMono` for the homomorphism order;
* the strong product, likewise, in every order but the topological minor and immersion ones,
  where it is not known to be monotone;
* the tensor product, which has no unit, and the lexicographic one, which is not commutative:
  `MulLeftMono` and `MulRightMono`, the most those classes allow;
* `ZeroLEOneClass` in the seven orders with a bottom element — every order but the quotient and
  the contraction one, whose least element `empty 0` is not below `empty 1`;
* and, premium, `IsOrderedRing` — an ordered *semi*ring, since graphs have no negation — in every
  order that has all three of those and a bottom: over `IsoGraph.Semiring` (`⊕g`, `□g`) that is
  the subgraph, induced subgraph, minor, induced minor, topological minor and immersion orders,
  and over `IsoGraph.StrongSemiring` (`⊕g`, `⊠g`) the first four of them.

The last section needs no operation at all: none of the nine orders has a greatest element, so
seven of them are `NoMaxOrder` and the quotient and contraction orders — where `empty 0` is
maximal — are `NoTopOrder`.  Those two are also the two with no least element, `NoBotOrder`; the
other seven have `⊥ = empty 0`, so no order here is `NoMinOrder`.

The cancellative classes ask for the converse implications — that `H ⊕g K ≤ G ⊕g K` forces
`H ≤ G` — which is a theorem about the containment relations and not about the algebra.  Eight of
those hold: the disjoint union cancels in all seven orders where it can, and the induced subgraph
order cancels the join as well, so each of those eight pairs gets `IsOrderedCancelAddMonoid` in
place of `IsOrderedAddMonoid`.  No product cancels in any of the nine orders, since `empty 0`
absorbs, so `IsOrderedCancelMonoid` and `IsStrictOrderedRing` are out of reach by construction;
the disjoint union does not cancel in the homomorphism or quotient orders, and the join does not
cancel in the five orders that contract or subdivide.  That leaves three cells open, all of them
the join.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ## What cancels

The cancellative classes need the converse of monotonicity: that `H ⊕g K ≤ G ⊕g K` forces
`H ≤ G`.  `Containment/Split.lean` cuts an inclusion of one disjoint union into another into four
pieces, and that is all the induction below needs.  Cancelling `K` from `H ⊕g K ≤ G ⊕g K` splits
`K` as `K₁ ⊕g K₂` with `H₂ ⊕g K₂` inside `K` itself, and either `K₂` is smaller than `K` — so the
induction hypothesis puts `H₂` inside `K₁`, and `H = H₁ ⊕g H₂ ≤ H₁ ⊕g K₁ ≤ G` — or `K₂` is all of
`K`, in which case counting vertices makes `K₁` and `H₂` empty and `H = H₁ ≤ G` outright.

The argument is written once, as `disjUnion_cancel_of_split`, and run for the seven orders whose
inclusions split: the subgraph and induced subgraph ones, and the five minor-like ones.  The join
follows for the induced subgraph order alone, by complementation.

This section comes first because the instances below use it.  What *fails* to cancel, which is
most of the table, is collected in `## Cancellation` after them. -/

/-- **How a relation that splits disjoint unions cancels them.**  The hypotheses are reflexivity,
transitivity, monotonicity under `⊕g`, that a containment does not gain vertices, and the
splitting itself; the conclusion is cancellation. -/
theorem disjUnion_cancel_of_split {R : IsoGraph → IsoGraph → Prop} (hrefl : ∀ a, R a a)
    (htrans : ∀ {a b c : IsoGraph}, R a b → R b c → R a c)
    (hmono : ∀ {a b c d : IsoGraph}, R a b → R c d → R (a ⊕g c) (b ⊕g d))
    (hV : ∀ {a b : IsoGraph}, R a b → a.V ≤ b.V)
    (hsplit : ∀ {H K C D : IsoGraph}, R (H ⊕g K) (C ⊕g D) →
      ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
        R (H₁ ⊕g K₁) C ∧ R (H₂ ⊕g K₂) D)
    (H G K : IsoGraph) (h : R (H ⊕g K) (G ⊕g K)) : R H G := by
  have key : ∀ n (H G K : IsoGraph), K.V = n → R (H ⊕g K) (G ⊕g K) → R H G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro H G K hK h
      obtain ⟨H₁, H₂, K₁, K₂, hH, hKd, h₁, h₂⟩ := hsplit h
      have hVK : K.V = K₁.V + K₂.V := by rw [hKd, V_disjUnion]
      by_cases hlt : K₂.V < n
      · rw [hKd] at h₂
        exact hH ▸ htrans (hmono (hrefl H₁) (ih K₂.V hlt H₂ K₁ K₂ rfl h₂)) h₁
      · have hV₂ := hV h₂
        rw [V_disjUnion] at hV₂
        have hK₁ : K₁ = empty 0 := V_eq_zero_iff.1 (by omega)
        have hH₂ : H₂ = empty 0 := V_eq_zero_iff.1 (by omega)
        rw [hK₁, disjUnion_empty_zero] at h₁
        rw [hH, hH₂, disjUnion_empty_zero]
        exact h₁
  exact key K.V H G K rfl h

/-- **The subgraph order cancels disjoint unions.** -/
theorem IsSubgraphOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ₛ G ⊕g K) : H ≤ₛ G :=
  disjUnion_cancel_of_split isSubgraphOf_refl isSubgraphOf_trans IsSubgraphOf.disjUnion
    IsSubgraphOf.V_le IsSubgraphOf.exists_split_disjUnion H G K h

/-- **The induced subgraph order cancels disjoint unions.** -/
theorem IsInducedSubgraphOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ᵢₛ G ⊕g K) :
    H ≤ᵢₛ G :=
  disjUnion_cancel_of_split isInducedSubgraphOf_refl isInducedSubgraphOf_trans
    IsInducedSubgraphOf.disjUnion IsInducedSubgraphOf.V_le
    IsInducedSubgraphOf.exists_split_disjUnion H G K h

/-- **The induced subgraph order cancels joins.**  The complement of a join is the disjoint union
of the complements, and complementation is a symmetry of this order. -/
theorem IsInducedSubgraphOf.join_cancel {H G K : IsoGraph} (h : H ∇g K ≤ᵢₛ G ∇g K) : H ≤ᵢₛ G := by
  have hc := h.compl
  rw [compl_join, compl_join] at hc
  simpa using (IsInducedSubgraphOf.disjUnion_cancel hc).compl

/-- **The minor order cancels disjoint unions.** -/
theorem IsMinorOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ₘ G ⊕g K) : H ≤ₘ G :=
  disjUnion_cancel_of_split isMinorOf_refl isMinorOf_trans IsMinorOf.disjUnion
    IsMinorOf.V_le IsMinorOf.exists_split_disjUnion H G K h

/-- **The induced minor order cancels disjoint unions.** -/
theorem IsInducedMinorOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ᵢₘ G ⊕g K) : H ≤ᵢₘ G :=
  disjUnion_cancel_of_split isInducedMinorOf_refl isInducedMinorOf_trans
    IsInducedMinorOf.disjUnion IsInducedMinorOf.V_le
    IsInducedMinorOf.exists_split_disjUnion H G K h

/-- **The contraction order cancels disjoint unions.** -/
theorem IsContractionOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ₚ G ⊕g K) : H ≤ₚ G :=
  disjUnion_cancel_of_split isContractionOf_refl isContractionOf_trans
    IsContractionOf.disjUnion IsContractionOf.V_le
    IsContractionOf.exists_split_disjUnion H G K h

/-- **The topological minor order cancels disjoint unions.** -/
theorem IsTopMinorOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ₜₘ G ⊕g K) : H ≤ₜₘ G :=
  disjUnion_cancel_of_split isTopMinorOf_refl isTopMinorOf_trans IsTopMinorOf.disjUnion
    IsTopMinorOf.V_le IsTopMinorOf.exists_split_disjUnion H G K h

/-- **The immersion order cancels disjoint unions.** -/
theorem IsImmersionMinorOf.disjUnion_cancel {H G K : IsoGraph} (h : H ⊕g K ≤ₑ G ⊕g K) : H ≤ₑ G :=
  disjUnion_cancel_of_split isImmersionMinorOf_refl isImmersionMinorOf_trans
    IsImmersionMinorOf.disjUnion IsImmersionMinorOf.V_le
    IsImmersionMinorOf.exists_split_disjUnion H G K h

namespace Hom

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_hasHomInto _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

scoped instance instAddLeftMonoDisjUnion : AddLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.disjUnion (hasHomInto_refl c) h⟩

scoped instance instAddRightMonoDisjUnion : AddRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.disjUnion h (hasHomInto_refl c)⟩

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instAddLeftMonoJoin : AddLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.join (hasHomInto_refl c) h⟩

scoped instance instAddRightMonoJoin : AddRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.join h (hasHomInto_refl c)⟩

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instMulLeftMonoCartesianProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.cartesianProduct (hasHomInto_refl c) h⟩

scoped instance instMulRightMonoCartesianProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.cartesianProduct h (hasHomInto_refl c)⟩

end CartesianProduct

section TensorProduct
open scoped IsoGraph.TensorProduct

scoped instance instMulLeftMonoTensorProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.tensorProduct (hasHomInto_refl c) h⟩

scoped instance instMulRightMonoTensorProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.tensorProduct h (hasHomInto_refl c)⟩

end TensorProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instMulLeftMonoStrongProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.strongProduct (hasHomInto_refl c) h⟩

scoped instance instMulRightMonoStrongProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.strongProduct h (hasHomInto_refl c)⟩

end StrongProduct

section LexProduct
open scoped IsoGraph.LexProduct

scoped instance instMulLeftMonoLexProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.lexProduct (hasHomInto_refl c) h⟩

scoped instance instMulRightMonoLexProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasHomInto.lexProduct h (hasHomInto_refl c)⟩

end LexProduct

end Hom

namespace Subgraph

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_isSubgraphOf _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

/-- The disjoint union cancels here, so this is the cancellative class rather than the plain
`IsOrderedAddMonoid`. -/
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsSubgraphOf.disjUnion h (isSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsSubgraphOf.disjUnion (isSubgraphOf_refl c) h
  le_of_add_le_add_left a b c h := IsSubgraphOf.disjUnion_cancel
    (show b ⊕g a ≤ₛ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsSubgraphOf.join h (isSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsSubgraphOf.join (isSubgraphOf_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsSubgraphOf.cartesianProduct h (isSubgraphOf_refl c)
  mul_le_mul_right _ _ h c := IsSubgraphOf.cartesianProduct (isSubgraphOf_refl c) h

end CartesianProduct

section TensorProduct
open scoped IsoGraph.TensorProduct

scoped instance instMulLeftMonoTensorProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsSubgraphOf.tensorProduct (isSubgraphOf_refl c) h⟩

scoped instance instMulRightMonoTensorProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsSubgraphOf.tensorProduct h (isSubgraphOf_refl c)⟩

end TensorProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instIsOrderedMonoidStrongProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsSubgraphOf.strongProduct h (isSubgraphOf_refl c)
  mul_le_mul_right _ _ h c := IsSubgraphOf.strongProduct (isSubgraphOf_refl c) h

end StrongProduct

section LexProduct
open scoped IsoGraph.LexProduct

scoped instance instMulLeftMonoLexProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsSubgraphOf.lexProduct (isSubgraphOf_refl c) h⟩

scoped instance instMulRightMonoLexProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsSubgraphOf.lexProduct h (isSubgraphOf_refl c)⟩

end LexProduct

section Semiring
open scoped IsoGraph.Semiring

/-- **An ordered semiring**, under the disjoint union and the cartesian product. -/
scoped instance instIsOrderedRingSemiring : IsOrderedRing IsoGraph := { }

end Semiring

section StrongSemiring
open scoped IsoGraph.StrongSemiring

/-- **An ordered semiring**, under the disjoint union and the strong product. -/
scoped instance instIsOrderedRingStrongSemiring : IsOrderedRing IsoGraph := { }

end StrongSemiring

end Subgraph

namespace InducedSubgraph

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_isInducedSubgraphOf _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

@[inherit_doc IsoGraph.Subgraph.instIsOrderedCancelAddMonoidDisjUnion]
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedSubgraphOf.disjUnion h (isInducedSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsInducedSubgraphOf.disjUnion (isInducedSubgraphOf_refl c) h
  le_of_add_le_add_left a b c h := IsInducedSubgraphOf.disjUnion_cancel
    (show b ⊕g a ≤ᵢₛ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

/-- The join cancels here too, by complementation. -/
scoped instance instIsOrderedCancelAddMonoidJoin : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedSubgraphOf.join h (isInducedSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsInducedSubgraphOf.join (isInducedSubgraphOf_refl c) h
  le_of_add_le_add_left a b c h := IsInducedSubgraphOf.join_cancel
    (show b ∇g a ≤ᵢₛ c ∇g a by rw [join_comm b a, join_comm c a]; exact h)

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsInducedSubgraphOf.cartesianProduct h (isInducedSubgraphOf_refl c)
  mul_le_mul_right _ _ h c := IsInducedSubgraphOf.cartesianProduct (isInducedSubgraphOf_refl c) h

end CartesianProduct

section TensorProduct
open scoped IsoGraph.TensorProduct

scoped instance instMulLeftMonoTensorProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsInducedSubgraphOf.tensorProduct (isInducedSubgraphOf_refl c) h⟩

scoped instance instMulRightMonoTensorProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsInducedSubgraphOf.tensorProduct h (isInducedSubgraphOf_refl c)⟩

end TensorProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instIsOrderedMonoidStrongProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsInducedSubgraphOf.strongProduct h (isInducedSubgraphOf_refl c)
  mul_le_mul_right _ _ h c := IsInducedSubgraphOf.strongProduct (isInducedSubgraphOf_refl c) h

end StrongProduct

section LexProduct
open scoped IsoGraph.LexProduct

scoped instance instMulLeftMonoLexProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsInducedSubgraphOf.lexProduct (isInducedSubgraphOf_refl c) h⟩

scoped instance instMulRightMonoLexProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsInducedSubgraphOf.lexProduct h (isInducedSubgraphOf_refl c)⟩

end LexProduct

section Semiring
open scoped IsoGraph.Semiring

/-- **An ordered semiring**, under the disjoint union and the cartesian product. -/
scoped instance instIsOrderedRingSemiring : IsOrderedRing IsoGraph := { }

end Semiring

section StrongSemiring
open scoped IsoGraph.StrongSemiring

/-- **An ordered semiring**, under the disjoint union and the strong product. -/
scoped instance instIsOrderedRingStrongSemiring : IsOrderedRing IsoGraph := { }

end StrongSemiring

end InducedSubgraph

namespace Quotient

section DisjUnion
open scoped IsoGraph.DisjUnion

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := HasQuotient.disjUnion h (hasQuotient_refl c)
  add_le_add_right _ _ h c := HasQuotient.disjUnion (hasQuotient_refl c) h

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := HasQuotient.join h (hasQuotient_refl c)
  add_le_add_right _ _ h c := HasQuotient.join (hasQuotient_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := HasQuotient.cartesianProduct h (hasQuotient_refl c)
  mul_le_mul_right _ _ h c := HasQuotient.cartesianProduct (hasQuotient_refl c) h

end CartesianProduct

section TensorProduct
open scoped IsoGraph.TensorProduct

scoped instance instMulLeftMonoTensorProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasQuotient.tensorProduct (hasQuotient_refl c) h⟩

scoped instance instMulRightMonoTensorProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasQuotient.tensorProduct h (hasQuotient_refl c)⟩

end TensorProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instIsOrderedMonoidStrongProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := HasQuotient.strongProduct h (hasQuotient_refl c)
  mul_le_mul_right _ _ h c := HasQuotient.strongProduct (hasQuotient_refl c) h

end StrongProduct

section LexProduct
open scoped IsoGraph.LexProduct

scoped instance instMulLeftMonoLexProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasQuotient.lexProduct (hasQuotient_refl c) h⟩

scoped instance instMulRightMonoLexProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ HasQuotient.lexProduct h (hasQuotient_refl c)⟩

end LexProduct

end Quotient

namespace Minor

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_isMinorOf _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

@[inherit_doc IsoGraph.Subgraph.instIsOrderedCancelAddMonoidDisjUnion]
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsMinorOf.disjUnion h (isMinorOf_refl c)
  add_le_add_right _ _ h c := IsMinorOf.disjUnion (isMinorOf_refl c) h
  le_of_add_le_add_left a b c h := IsMinorOf.disjUnion_cancel
    (show b ⊕g a ≤ₘ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsMinorOf.join h (isMinorOf_refl c)
  add_le_add_right _ _ h c := IsMinorOf.join (isMinorOf_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsMinorOf.cartesianProduct h (isMinorOf_refl c)
  mul_le_mul_right _ _ h c := IsMinorOf.cartesianProduct (isMinorOf_refl c) h

end CartesianProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instIsOrderedMonoidStrongProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsMinorOf.strongProduct h (isMinorOf_refl c)
  mul_le_mul_right _ _ h c := IsMinorOf.strongProduct (isMinorOf_refl c) h

end StrongProduct

section LexProduct
open scoped IsoGraph.LexProduct

scoped instance instMulLeftMonoLexProduct : MulLeftMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsMinorOf.lexProduct (isMinorOf_refl c) h⟩

scoped instance instMulRightMonoLexProduct : MulRightMono IsoGraph :=
  ⟨fun c _ _ h ↦ IsMinorOf.lexProduct h (isMinorOf_refl c)⟩

end LexProduct

section Semiring
open scoped IsoGraph.Semiring

/-- **An ordered semiring**, under the disjoint union and the cartesian product. -/
scoped instance instIsOrderedRingSemiring : IsOrderedRing IsoGraph := { }

end Semiring

section StrongSemiring
open scoped IsoGraph.StrongSemiring

/-- **An ordered semiring**, under the disjoint union and the strong product. -/
scoped instance instIsOrderedRingStrongSemiring : IsOrderedRing IsoGraph := { }

end StrongSemiring

end Minor

namespace InducedMinor

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_isInducedMinorOf _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

@[inherit_doc IsoGraph.Subgraph.instIsOrderedCancelAddMonoidDisjUnion]
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedMinorOf.disjUnion h (isInducedMinorOf_refl c)
  add_le_add_right _ _ h c := IsInducedMinorOf.disjUnion (isInducedMinorOf_refl c) h
  le_of_add_le_add_left a b c h := IsInducedMinorOf.disjUnion_cancel
    (show b ⊕g a ≤ᵢₘ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedMinorOf.join h (isInducedMinorOf_refl c)
  add_le_add_right _ _ h c := IsInducedMinorOf.join (isInducedMinorOf_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsInducedMinorOf.cartesianProduct h (isInducedMinorOf_refl c)
  mul_le_mul_right _ _ h c := IsInducedMinorOf.cartesianProduct (isInducedMinorOf_refl c) h

end CartesianProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instIsOrderedMonoidStrongProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsInducedMinorOf.strongProduct h (isInducedMinorOf_refl c)
  mul_le_mul_right _ _ h c := IsInducedMinorOf.strongProduct (isInducedMinorOf_refl c) h

end StrongProduct

section Semiring
open scoped IsoGraph.Semiring

/-- **An ordered semiring**, under the disjoint union and the cartesian product. -/
scoped instance instIsOrderedRingSemiring : IsOrderedRing IsoGraph := { }

end Semiring

section StrongSemiring
open scoped IsoGraph.StrongSemiring

/-- **An ordered semiring**, under the disjoint union and the strong product. -/
scoped instance instIsOrderedRingStrongSemiring : IsOrderedRing IsoGraph := { }

end StrongSemiring

end InducedMinor

namespace Contraction

section DisjUnion
open scoped IsoGraph.DisjUnion

@[inherit_doc IsoGraph.Subgraph.instIsOrderedCancelAddMonoidDisjUnion]
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsContractionOf.disjUnion h (isContractionOf_refl c)
  add_le_add_right _ _ h c := IsContractionOf.disjUnion (isContractionOf_refl c) h
  le_of_add_le_add_left a b c h := IsContractionOf.disjUnion_cancel
    (show b ⊕g a ≤ₚ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsContractionOf.join h (isContractionOf_refl c)
  add_le_add_right _ _ h c := IsContractionOf.join (isContractionOf_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsContractionOf.cartesianProduct h (isContractionOf_refl c)
  mul_le_mul_right _ _ h c := IsContractionOf.cartesianProduct (isContractionOf_refl c) h

end CartesianProduct

section StrongProduct
open scoped IsoGraph.StrongProduct

scoped instance instIsOrderedMonoidStrongProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsContractionOf.strongProduct h (isContractionOf_refl c)
  mul_le_mul_right _ _ h c := IsContractionOf.strongProduct (isContractionOf_refl c) h

end StrongProduct

end Contraction

namespace TopMinor

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_isTopMinorOf _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

@[inherit_doc IsoGraph.Subgraph.instIsOrderedCancelAddMonoidDisjUnion]
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsTopMinorOf.disjUnion h (isTopMinorOf_refl c)
  add_le_add_right _ _ h c := IsTopMinorOf.disjUnion (isTopMinorOf_refl c) h
  le_of_add_le_add_left a b c h := IsTopMinorOf.disjUnion_cancel
    (show b ⊕g a ≤ₜₘ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsTopMinorOf.join h (isTopMinorOf_refl c)
  add_le_add_right _ _ h c := IsTopMinorOf.join (isTopMinorOf_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsTopMinorOf.cartesianProduct h (isTopMinorOf_refl c)
  mul_le_mul_right _ _ h c := IsTopMinorOf.cartesianProduct (isTopMinorOf_refl c) h

end CartesianProduct

section Semiring
open scoped IsoGraph.Semiring

/-- **An ordered semiring**, under the disjoint union and the cartesian product. -/
scoped instance instIsOrderedRingSemiring : IsOrderedRing IsoGraph := { }

end Semiring

end TopMinor

namespace Immersion

section ZeroLEOne
open scoped IsoGraph.CartesianProduct

/-- `0 ≤ 1`: the empty graph is the bottom of this order, so it sits below the one-vertex graph. -/
scoped instance instZeroLEOneClass : ZeroLEOneClass IsoGraph where
  zero_le_one := empty_zero_isImmersionMinorOf _

end ZeroLEOne

section DisjUnion
open scoped IsoGraph.DisjUnion

@[inherit_doc IsoGraph.Subgraph.instIsOrderedCancelAddMonoidDisjUnion]
scoped instance instIsOrderedCancelAddMonoidDisjUnion : IsOrderedCancelAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsImmersionMinorOf.disjUnion h (isImmersionMinorOf_refl c)
  add_le_add_right _ _ h c := IsImmersionMinorOf.disjUnion (isImmersionMinorOf_refl c) h
  le_of_add_le_add_left a b c h := IsImmersionMinorOf.disjUnion_cancel
    (show b ⊕g a ≤ₑ c ⊕g a by rw [disjUnion_comm b a, disjUnion_comm c a]; exact h)

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsImmersionMinorOf.join h (isImmersionMinorOf_refl c)
  add_le_add_right _ _ h c := IsImmersionMinorOf.join (isImmersionMinorOf_refl c) h

end Join

section CartesianProduct
open scoped IsoGraph.CartesianProduct

scoped instance instIsOrderedMonoidCartesianProduct : IsOrderedMonoid IsoGraph where
  mul_le_mul_left _ _ h c := IsImmersionMinorOf.cartesianProduct h (isImmersionMinorOf_refl c)
  mul_le_mul_right _ _ h c := IsImmersionMinorOf.cartesianProduct (isImmersionMinorOf_refl c) h

end CartesianProduct

section Semiring
open scoped IsoGraph.Semiring

/-- **An ordered semiring**, under the disjoint union and the cartesian product. -/
scoped instance instIsOrderedRingSemiring : IsOrderedRing IsoGraph := { }

end Semiring

end Immersion

/-! ## Nothing at the top, and what there is at the bottom

None of the nine orders has a greatest element: a graph always sits inside a bigger one.  For the
seven that are relations of *inclusion* the witness is `G ⊕g empty 1`, one more isolated vertex,
which contains `G` and is not `G` — so those get `NoMaxOrder`, which is the stronger of the pair
(`NoMaxOrder → NoTopOrder` in any preorder).  The homomorphism order is only a preorder, and an
isolated vertex is no obstacle there — `G ⊕g empty 1` maps back into `G` as soon as `G` has a
vertex — so its witness is a disjoint clique `complete (G.V + 1)`, too big to map back by
`le_V_of_hasHomInto_complete`.

For the quotient and contraction orders `NoMaxOrder` is *false*: `empty 0` is a maximal element,
being a quotient — or a contraction — of nothing but itself.  It is a minimal element too, so it
is isolated, and those two orders get the weaker `NoTopOrder` instead.  What they do have, and the
other seven do not, is `NoBotOrder`: they have no bottom element at all, since a surjection onto
`empty 0` has to start there, whereas the seven inclusion orders have `⊥ = empty 0`.  `NoMinOrder`
is therefore false for all nine. -/

theorem ne_disjUnion_empty_one (G : IsoGraph) : G ≠ G ⊕g empty 1 := by
  intro h
  have hV := congrArg IsoGraph.V h
  simp at hV

theorem isSubgraphOf_disjUnion_empty_one (G : IsoGraph) : G ≤ₛ G ⊕g empty 1 := by
  simpa using IsSubgraphOf.disjUnion (isSubgraphOf_refl G) (empty_zero_isSubgraphOf (empty 1))

theorem isInducedSubgraphOf_disjUnion_empty_one (G : IsoGraph) : G ≤ᵢₛ G ⊕g empty 1 := by
  simpa using IsInducedSubgraphOf.disjUnion (isInducedSubgraphOf_refl G)
    (empty_zero_isInducedSubgraphOf (empty 1))

theorem isMinorOf_disjUnion_empty_one (G : IsoGraph) : G ≤ₘ G ⊕g empty 1 := by
  simpa using IsMinorOf.disjUnion (isMinorOf_refl G) (empty_zero_isMinorOf (empty 1))

theorem isInducedMinorOf_disjUnion_empty_one (G : IsoGraph) : G ≤ᵢₘ G ⊕g empty 1 := by
  simpa using IsInducedMinorOf.disjUnion (isInducedMinorOf_refl G)
    (empty_zero_isInducedMinorOf (empty 1))

theorem isTopMinorOf_disjUnion_empty_one (G : IsoGraph) : G ≤ₜₘ G ⊕g empty 1 := by
  simpa using IsTopMinorOf.disjUnion (isTopMinorOf_refl G) (empty_zero_isTopMinorOf (empty 1))

theorem isImmersionMinorOf_disjUnion_empty_one (G : IsoGraph) : G ≤ₑ G ⊕g empty 1 := by
  simpa using IsImmersionMinorOf.disjUnion (isImmersionMinorOf_refl G)
    (empty_zero_isImmersionMinorOf (empty 1))

theorem hasHomInto_disjUnion_left (G K : IsoGraph) : G ≤ₕ G ⊕g K := by
  simpa using HasHomInto.disjUnion (hasHomInto_refl G) (empty_zero_hasHomInto K)

theorem hasHomInto_disjUnion_right (G K : IsoGraph) : K ≤ₕ G ⊕g K := by
  simpa using HasHomInto.disjUnion (empty_zero_hasHomInto G) (hasHomInto_refl K)

/-- A disjoint clique on more vertices than `G` has cannot map back into `G`: a homomorphism out
of a clique is an inclusion. -/
theorem not_disjUnion_complete_hasHomInto (G : IsoGraph) :
    ¬G ⊕g complete (G.V + 1) ≤ₕ G := fun h ↦ by
  have hV := le_V_of_hasHomInto_complete
    (hasHomInto_trans (hasHomInto_disjUnion_right G (complete (G.V + 1))) h)
  omega

/-- **`empty 0` is a quotient of nothing but itself**, which is why the quotient order has a
maximal element and only `NoTopOrder`. -/
theorem eq_empty_zero_of_empty_zero_hasQuotient {G : IsoGraph} (h : empty 0 ≤/ G) :
    G = empty 0 := by
  by_contra hG
  exact absurd (HasQuotient.V_pos h (Nat.pos_of_ne_zero fun hV ↦ hG (V_eq_zero_iff.1 hV))) (by simp)

/-- **`empty 0` is a contraction of nothing but itself**; `eq_empty_zero_of_isContractionOf` is
the other half, that it contracts to nothing but itself. -/
theorem eq_empty_zero_of_empty_zero_isContractionOf {G : IsoGraph} (h : empty 0 ≤ₚ G) :
    G = empty 0 := by
  by_contra hG
  exact absurd (IsContractionOf.V_pos h (Nat.pos_of_ne_zero fun hV ↦ hG (V_eq_zero_iff.1 hV)))
    (by simp)

namespace Hom

/-- **No greatest graph**, witnessed by a disjoint clique. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a := ⟨a ⊕g complete (a.V + 1), lt_iff_le_not_ge.2
    ⟨hasHomInto_disjUnion_left a _, not_disjUnion_complete_hasHomInto a⟩⟩

end Hom

namespace Subgraph

/-- **No greatest graph**, witnessed by one more isolated vertex. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a :=
    ⟨a ⊕g empty 1, lt_of_le_of_ne (isSubgraphOf_disjUnion_empty_one a) (ne_disjUnion_empty_one a)⟩

end Subgraph

namespace InducedSubgraph

/-- **No greatest graph**, witnessed by one more isolated vertex. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a := ⟨a ⊕g empty 1,
    lt_of_le_of_ne (isInducedSubgraphOf_disjUnion_empty_one a) (ne_disjUnion_empty_one a)⟩

end InducedSubgraph

namespace Minor

/-- **No greatest graph**, witnessed by one more isolated vertex. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a :=
    ⟨a ⊕g empty 1, lt_of_le_of_ne (isMinorOf_disjUnion_empty_one a) (ne_disjUnion_empty_one a)⟩

end Minor

namespace InducedMinor

/-- **No greatest graph**, witnessed by one more isolated vertex. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a := ⟨a ⊕g empty 1,
    lt_of_le_of_ne (isInducedMinorOf_disjUnion_empty_one a) (ne_disjUnion_empty_one a)⟩

end InducedMinor

namespace TopMinor

/-- **No greatest graph**, witnessed by one more isolated vertex. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a :=
    ⟨a ⊕g empty 1, lt_of_le_of_ne (isTopMinorOf_disjUnion_empty_one a) (ne_disjUnion_empty_one a)⟩

end TopMinor

namespace Immersion

/-- **No greatest graph**, witnessed by one more isolated vertex. -/
scoped instance instNoMaxOrder : NoMaxOrder IsoGraph where
  exists_gt a := ⟨a ⊕g empty 1,
    lt_of_le_of_ne (isImmersionMinorOf_disjUnion_empty_one a) (ne_disjUnion_empty_one a)⟩

end Immersion

namespace Quotient

/-- **Nothing is above everything**: a graph with one more vertex is not a quotient of `a`.  Not
`NoMaxOrder`: `empty 0` is maximal, by `isMax_empty_zero`. -/
scoped instance instNoTopOrder : NoTopOrder IsoGraph where
  exists_not_le a := ⟨a ⊕g empty 1, fun h ↦ by have hV := HasQuotient.V_le h; simp at hV⟩

/-- **Nothing is below everything**: `a` is a quotient neither of `empty 0`, if it has a vertex,
nor of `empty 1`, if it has not.  Not `NoMinOrder`: `empty 0` is minimal, by `isMin_empty_zero`. -/
scoped instance instNoBotOrder : NoBotOrder IsoGraph where
  exists_not_ge a := by
    rcases Nat.eq_zero_or_pos a.V with h | h
    · exact ⟨empty 1, fun hle ↦ by have := HasQuotient.V_pos hle (by simp); omega⟩
    · refine ⟨empty 0, fun hle ↦ ?_⟩
      have hV := HasQuotient.V_le hle
      rw [V_empty] at hV
      omega

theorem isMax_empty_zero : IsMax (empty 0 : IsoGraph) := fun _ hb ↦ by
  rw [eq_empty_zero_of_empty_zero_hasQuotient hb]

theorem isMin_empty_zero : IsMin (empty 0 : IsoGraph) := fun _ hb ↦ by
  have hV := HasQuotient.V_le hb
  rw [V_empty, Nat.le_zero, V_eq_zero_iff] at hV
  subst hV
  exact hasQuotient_refl _

end Quotient

namespace Contraction

/-- **Nothing is above everything**: a graph with one more vertex is not a contraction of `a`.
Not `NoMaxOrder`: `empty 0` is maximal, by `isMax_empty_zero`. -/
scoped instance instNoTopOrder : NoTopOrder IsoGraph where
  exists_not_le a := ⟨a ⊕g empty 1, fun h ↦ by have hV := IsContractionOf.V_le h; simp at hV⟩

/-- **Nothing is below everything**: `a` contracts neither to `empty 0`, if it has a vertex, nor
to `empty 1`, if it has not.  Not `NoMinOrder`: `empty 0` is minimal, by `isMin_empty_zero`. -/
scoped instance instNoBotOrder : NoBotOrder IsoGraph where
  exists_not_ge a := by
    rcases Nat.eq_zero_or_pos a.V with h | h
    · exact ⟨empty 1, fun hle ↦ by have := IsContractionOf.V_pos hle (by simp); omega⟩
    · refine ⟨empty 0, fun hle ↦ ?_⟩
      have hV := IsContractionOf.V_le hle
      rw [V_empty] at hV
      omega

theorem isMax_empty_zero : IsMax (empty 0 : IsoGraph) := fun _ hb ↦ by
  rw [eq_empty_zero_of_empty_zero_isContractionOf hb]

theorem isMin_empty_zero : IsMin (empty 0 : IsoGraph) := fun _ hb ↦ by
  rw [eq_empty_zero_of_isContractionOf hb]

end Contraction

/-! ## Cancellation

The other half of each monotonicity question: when does `H op K ≤ G op K` force `H ≤ G`?  `## What
cancels`, above, has the eight cells where it does; this section has the rest.

*Never*, for the four products.  Each of them has `empty 0` for an absorbing element, so taking
`K = empty 0` makes the hypothesis vacuous while `empty 1 ≤ empty 0` is false in all nine orders —
that is `not_mul_cancel`, and its nine instances below, each stated for any operation with a zero.
`IsOrderedCancelMonoid` is therefore out of reach by construction, not merely unproved.

For the two sums the answer depends on the order, and the counterexamples are these.  A disjoint
union cannot be cancelled in the homomorphism order — two isolated vertices map onto one — nor in
the quotient order, where `empty 0 ⊕g empty 1` is a quotient of `empty 1 ⊕g empty 1` although
`empty 0` is a quotient of nothing but itself.  A join cannot be cancelled in the five orders that
may contract or subdivide: `complete 2 ∇g empty 2` is `K₄` less an edge and `empty 3 ∇g empty 2`
is `K₃,₂`, and contracting one edge of the latter gives the former, while `complete 2` has an edge
and `empty 3` has none.

Of the eleven cells that leaves, eight are settled above: the disjoint union cancels in all seven
orders where it can, and the join in the induced subgraph order.  The three still open are the
join in the homomorphism, subgraph and quotient orders.  None of them has a counterexample among
the graphs on at most three vertices, and all are expected to hold; what they want is the
splitting of `Containment/Split.lean` for the join, which complementation gives only in the one
order that it preserves.  `IsStrictOrderedRing` stays out of reach regardless, since it asks for a
product to cancel. -/

theorem not_empty_one_hasHomInto_empty_zero : ¬(empty 1 : IsoGraph) ≤ₕ empty 0 := fun h ↦ by
  have hV := le_V_of_hasHomInto_complete (n := 1) (G := empty 0) (by rwa [complete_one])
  simp at hV

theorem not_empty_one_isSubgraphOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ₛ empty 0 := fun h ↦ by
  have hV := h.V_le; simp at hV

theorem not_empty_one_isInducedSubgraphOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ᵢₛ empty 0 :=
  fun h ↦ by have hV := h.V_le; simp at hV

theorem not_empty_one_hasQuotient_empty_zero : ¬(empty 1 : IsoGraph) ≤/ empty 0 := fun h ↦ by
  have hV := HasQuotient.V_le h; simp at hV

theorem not_empty_one_isMinorOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ₘ empty 0 := fun h ↦ by
  have hV := h.V_le; simp at hV

theorem not_empty_one_isInducedMinorOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ᵢₘ empty 0 :=
  fun h ↦ by have hV := h.V_le; simp at hV

theorem not_empty_one_isContractionOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ₚ empty 0 := fun h ↦ by
  have hV := h.V_le; simp at hV

theorem not_empty_one_isTopMinorOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ₜₘ empty 0 := fun h ↦ by
  have hV := h.V_le; simp at hV

theorem not_empty_one_isImmersionMinorOf_empty_zero : ¬(empty 1 : IsoGraph) ≤ₑ empty 0 :=
  fun h ↦ by have hV := h.V_le; simp at hV

/-- **No product cancels, in any of the nine orders.**  Every product of graphs has `empty 0` for
an absorbing element, so `op c a ≤ op c b` says nothing whatever about `a` and `b` when `c` is
`empty 0`; all that is needed of the order is that `empty 1` is not below `empty 0`. -/
theorem not_mul_cancel {R : IsoGraph → IsoGraph → Prop} (hrefl : R (empty 0) (empty 0))
    (h10 : ¬R (empty 1) (empty 0)) (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, R (op c a) (op c b) → R a b := fun h ↦
  h10 (h (empty 1) (empty 0) (empty 0) (by rw [hzero, hzero]; exact hrefl))

theorem not_mul_cancel_hasHomInto (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ₕ op c b → a ≤ₕ b :=
  not_mul_cancel (hasHomInto_refl _) not_empty_one_hasHomInto_empty_zero op hzero

theorem not_mul_cancel_isSubgraphOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ₛ op c b → a ≤ₛ b :=
  not_mul_cancel (isSubgraphOf_refl _) not_empty_one_isSubgraphOf_empty_zero op hzero

theorem not_mul_cancel_isInducedSubgraphOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ᵢₛ op c b → a ≤ᵢₛ b :=
  not_mul_cancel (isInducedSubgraphOf_refl _) not_empty_one_isInducedSubgraphOf_empty_zero op hzero

theorem not_mul_cancel_hasQuotient (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤/ op c b → a ≤/ b :=
  not_mul_cancel (R := fun a b ↦ a ≤/ b) (hasQuotient_refl _)
    not_empty_one_hasQuotient_empty_zero op hzero

theorem not_mul_cancel_isMinorOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ₘ op c b → a ≤ₘ b :=
  not_mul_cancel (isMinorOf_refl _) not_empty_one_isMinorOf_empty_zero op hzero

theorem not_mul_cancel_isInducedMinorOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ᵢₘ op c b → a ≤ᵢₘ b :=
  not_mul_cancel (isInducedMinorOf_refl _) not_empty_one_isInducedMinorOf_empty_zero op hzero

theorem not_mul_cancel_isContractionOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ₚ op c b → a ≤ₚ b :=
  not_mul_cancel (isContractionOf_refl _) not_empty_one_isContractionOf_empty_zero op hzero

theorem not_mul_cancel_isTopMinorOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ₜₘ op c b → a ≤ₜₘ b :=
  not_mul_cancel (isTopMinorOf_refl _) not_empty_one_isTopMinorOf_empty_zero op hzero

theorem not_mul_cancel_isImmersionMinorOf (op : IsoGraph → IsoGraph → IsoGraph)
    (hzero : ∀ G, op (empty 0) G = empty 0) :
    ¬∀ a b c : IsoGraph, op c a ≤ₑ op c b → a ≤ₑ b :=
  not_mul_cancel (isImmersionMinorOf_refl _) not_empty_one_isImmersionMinorOf_empty_zero op hzero

/-! ### The two sums -/

/-- Two isolated vertices map onto one. -/
theorem hasHomInto_empty_two_one : (empty 2 : IsoGraph) ≤ₕ empty 1 := by
  show (⟦CGraph.empty 2⟧ : IsoGraph) ≤ₕ ⟦CGraph.empty 1⟧
  rw [hasHomInto_mk]
  exact (CGraph.homB_iff _ _).1 (by native_decide)

/-- One isolated vertex is a quotient of two. -/
theorem hasQuotient_empty_one_two : (empty 1 : IsoGraph) ≤/ empty 2 := by
  show (⟦CGraph.empty 1⟧ : IsoGraph) ≤/ ⟦CGraph.empty 2⟧
  rw [hasQuotient_mk]
  exact (CGraph.quotientB_iff _ _).1 (by native_decide)

/-- `K₄` less an edge is a contraction of `K₃,₂` — contract one edge of the bipartite graph and
nothing is left to delete. -/
theorem isContractionOf_join_complete_two :
    (complete 2 ∇g empty 2 : IsoGraph) ≤ₚ empty 3 ∇g empty 2 := by
  show (⟦CGraph.complete 2⟧ ∇g ⟦CGraph.empty 2⟧ : IsoGraph) ≤ₚ ⟦CGraph.empty 3⟧ ∇g ⟦CGraph.empty 2⟧
  rw [join_mk, join_mk, isContractionOf_mk]
  exact (CGraph.contractionB_iff _ _).1 (by native_decide)

/-- It is a topological minor of it as well: route the one missing edge through the third vertex
of the larger side. -/
theorem isTopMinorOf_join_complete_two :
    (complete 2 ∇g empty 2 : IsoGraph) ≤ₜₘ empty 3 ∇g empty 2 := by
  show (⟦CGraph.complete 2⟧ ∇g ⟦CGraph.empty 2⟧ : IsoGraph) ≤ₜₘ ⟦CGraph.empty 3⟧ ∇g ⟦CGraph.empty 2⟧
  rw [join_mk, join_mk, isTopMinorOf_mk]
  exact (CGraph.topMinorB_iff _ _).1 (by native_decide)

/-- **The homomorphism order does not cancel disjoint unions.**  `empty 1 ⊕g empty 1` maps into
`empty 0 ⊕g empty 1`, both vertices going to the one, but `empty 1` does not map into
`empty 0`. -/
theorem not_disjUnion_cancel_hasHomInto :
    ¬∀ H G K : IsoGraph, H ⊕g K ≤ₕ G ⊕g K → H ≤ₕ G := fun h ↦
  not_empty_one_hasHomInto_empty_zero
    (h (empty 1) (empty 0) (empty 1) (by simpa using hasHomInto_empty_two_one))

/-- **The quotient order does not cancel disjoint unions.**  `empty 0 ⊕g empty 1` is a quotient of
`empty 1 ⊕g empty 1`, but `empty 0` is a quotient of nothing but itself. -/
theorem not_disjUnion_cancel_hasQuotient :
    ¬∀ H G K : IsoGraph, H ⊕g K ≤/ G ⊕g K → H ≤/ G := fun h ↦
  absurd (h (empty 0) (empty 1) (empty 1) (by simpa using hasQuotient_empty_one_two))
    (fun hq ↦ by simpa using eq_empty_zero_of_empty_zero_hasQuotient hq)

/-- **The minor order does not cancel joins.**  `K₄` less an edge is a minor of `K₃,₂` — the two
graphs are `complete 2 ∇g empty 2` and `empty 3 ∇g empty 2` — but `complete 2` has an edge and
`empty 3` has none. -/
theorem not_join_cancel_isMinorOf :
    ¬∀ H G K : IsoGraph, H ∇g K ≤ₘ G ∇g K → H ≤ₘ G := fun h ↦ by
  have hE := (h (complete 2) (empty 3) (empty 2)
    isContractionOf_join_complete_two.isMinorOf).E_le
  simp at hE

@[inherit_doc not_join_cancel_isMinorOf]
theorem not_join_cancel_isInducedMinorOf :
    ¬∀ H G K : IsoGraph, H ∇g K ≤ᵢₘ G ∇g K → H ≤ᵢₘ G := fun h ↦ by
  have hE := (h (complete 2) (empty 3) (empty 2)
    isContractionOf_join_complete_two.isInducedMinorOf).E_le
  simp at hE

@[inherit_doc not_join_cancel_isMinorOf]
theorem not_join_cancel_isContractionOf :
    ¬∀ H G K : IsoGraph, H ∇g K ≤ₚ G ∇g K → H ≤ₚ G := fun h ↦ by
  have hE := (h (complete 2) (empty 3) (empty 2) isContractionOf_join_complete_two).E_le
  simp at hE

@[inherit_doc not_join_cancel_isMinorOf]
theorem not_join_cancel_isTopMinorOf :
    ¬∀ H G K : IsoGraph, H ∇g K ≤ₜₘ G ∇g K → H ≤ₜₘ G := fun h ↦ by
  have hE := (h (complete 2) (empty 3) (empty 2) isTopMinorOf_join_complete_two).E_le
  simp at hE

@[inherit_doc not_join_cancel_isMinorOf]
theorem not_join_cancel_isImmersionMinorOf :
    ¬∀ H G K : IsoGraph, H ∇g K ≤ₑ G ∇g K → H ≤ₑ G := fun h ↦ by
  have hE := (h (complete 2) (empty 3) (empty 2)
    isTopMinorOf_join_complete_two.isImmersionMinorOf).E_le
  simp at hE

/-! ## The instances in use

One order scope and one algebra scope at a time, and the `Mathlib` order lemmas apply to graphs. -/

section Examples

open scoped IsoGraph.Subgraph IsoGraph.Semiring

example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d := add_le_add h h'
example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a * c ≤ b * d := mul_le_mul' h h'
example (a : IsoGraph) : 0 ≤ a := bot_le
example : (0 : IsoGraph) ≤ 1 := zero_le_one
example (a b : IsoGraph) (h : a ≤ b) : a * a ≤ b * b := mul_le_mul' h h
/-- The disjoint union cancels, so `add_le_add_iff_left` is an iff. -/
example (a b c : IsoGraph) : c + a ≤ c + b ↔ a ≤ b := add_le_add_iff_left c

end Examples

section Examples

open scoped IsoGraph.InducedSubgraph IsoGraph.Join

/-- The join cancels in this order, the only one where it is known to. -/
example (a b c : IsoGraph) (h : a + c ≤ b + c) : a ≤ b := le_of_add_le_add_right h

end Examples

section Examples

open scoped IsoGraph.Minor IsoGraph.StrongSemiring

example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a * c ≤ b * d := mul_le_mul' h h'
example (a b c : IsoGraph) (h : a ≤ b) : c * a ≤ c * b := mul_le_mul_of_nonneg_left h bot_le
/-- The disjoint union cancels here too — a summand of a minor of `b ⊕g c` beyond `c` is a minor
of `b`. -/
example (a b c : IsoGraph) : a + c ≤ b + c ↔ a ≤ b := add_le_add_iff_right c

end Examples

section Examples

open scoped IsoGraph.Hom IsoGraph.LexProduct

example (a b c : IsoGraph) (h : a ≤ b) : c * a ≤ c * b := mul_le_mul_right h c
example (a b c : IsoGraph) (h : a ≤ b) : a * c ≤ b * c := mul_le_mul_left h c

end Examples

section Examples

open scoped IsoGraph.Immersion IsoGraph.Join

example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d := add_le_add h h'
example (a : IsoGraph) : 0 ≤ a := bot_le

end Examples

section Examples

open scoped IsoGraph.TopMinor IsoGraph.Semiring

example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a * c ≤ b * d := mul_le_mul' h h'
example (a b c : IsoGraph) (h : a ≤ b) : c * a ≤ c * b := mul_le_mul_of_nonneg_left h bot_le
example : (0 : IsoGraph) ≤ 1 := zero_le_one

end Examples

section Examples

open scoped IsoGraph.Minor

example (a : IsoGraph) : ∃ b, a < b := exists_gt a
example (a : IsoGraph) : ¬IsMax a := not_isMax a
/-- The other half fails: this order has a least element, so it is not `NoMinOrder`. -/
example : ¬NoMinOrder IsoGraph := fun _ ↦ @not_isMin IsoGraph _ ‹_› ⊥ isMin_bot

end Examples

section Examples

open scoped IsoGraph.Quotient

example (a : IsoGraph) : ∃ b, ¬b ≤ a := exists_not_le a
example (a : IsoGraph) : ∃ b, ¬a ≤ b := exists_not_ge a
/-- Neither strengthening holds: `empty 0` is both maximal and minimal here. -/
example : ¬NoMaxOrder IsoGraph := fun _ ↦ @not_isMax IsoGraph _ ‹_› _ IsoGraph.Quotient.isMax_empty_zero
example : ¬NoMinOrder IsoGraph := fun _ ↦ @not_isMin IsoGraph _ ‹_› _ IsoGraph.Quotient.isMin_empty_zero

end Examples

end IsoGraph
