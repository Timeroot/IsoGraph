import IsoGraph.Containment.Monotone
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
* the cartesian and strong products, which are commutative monoids: `IsOrderedMonoid`, again
  weakened to `MulLeftMono` and `MulRightMono` for the homomorphism order;
* the tensor product, which has no unit, and the lexicographic one, which is not commutative:
  `MulLeftMono` and `MulRightMono`, the most those classes allow;
* `ZeroLEOneClass` in the seven orders with a bottom element — every order but the quotient and
  the contraction one, whose least element `empty 0` is not below `empty 1`;
* and, premium, `IsOrderedRing` — an ordered *semi*ring, since graphs have no negation — in the
  four orders that have all three of those and a bottom: the subgraph, induced subgraph, minor and
  induced minor orders, over both distributive pairs `IsoGraph.Semiring` (`⊕g`, `□g`) and
  `IsoGraph.StrongSemiring` (`⊕g`, `⊠g`).

`IsStrictOrderedRing` and the cancellative classes `IsOrderedCancelAddMonoid` and
`IsOrderedCancelMonoid` are *not* here.  They ask for the converse implications — that
`H ⊕g K ≤ G ⊕g K` forces `H ≤ G` — which is a cancellation theorem about the containment relations
and not about the algebra, and none of the nine is proved to have it.
-/

set_option autoImplicit false

namespace IsoGraph

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsSubgraphOf.disjUnion h (isSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsSubgraphOf.disjUnion (isSubgraphOf_refl c) h

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedSubgraphOf.disjUnion h (isInducedSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsInducedSubgraphOf.disjUnion (isInducedSubgraphOf_refl c) h

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedSubgraphOf.join h (isInducedSubgraphOf_refl c)
  add_le_add_right _ _ h c := IsInducedSubgraphOf.join (isInducedSubgraphOf_refl c) h

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsMinorOf.disjUnion h (isMinorOf_refl c)
  add_le_add_right _ _ h c := IsMinorOf.disjUnion (isMinorOf_refl c) h

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsInducedMinorOf.disjUnion h (isInducedMinorOf_refl c)
  add_le_add_right _ _ h c := IsInducedMinorOf.disjUnion (isInducedMinorOf_refl c) h

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsContractionOf.disjUnion h (isContractionOf_refl c)
  add_le_add_right _ _ h c := IsContractionOf.disjUnion (isContractionOf_refl c) h

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsTopMinorOf.disjUnion h (isTopMinorOf_refl c)
  add_le_add_right _ _ h c := IsTopMinorOf.disjUnion (isTopMinorOf_refl c) h

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsTopMinorOf.join h (isTopMinorOf_refl c)
  add_le_add_right _ _ h c := IsTopMinorOf.join (isTopMinorOf_refl c) h

end Join

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

scoped instance instIsOrderedAddMonoidDisjUnion : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsImmersionMinorOf.disjUnion h (isImmersionMinorOf_refl c)
  add_le_add_right _ _ h c := IsImmersionMinorOf.disjUnion (isImmersionMinorOf_refl c) h

end DisjUnion

section Join
open scoped IsoGraph.Join

scoped instance instIsOrderedAddMonoidJoin : IsOrderedAddMonoid IsoGraph where
  add_le_add_left _ _ h c := IsImmersionMinorOf.join h (isImmersionMinorOf_refl c)
  add_le_add_right _ _ h c := IsImmersionMinorOf.join (isImmersionMinorOf_refl c) h

end Join

end Immersion

/-! ## The instances in use

One order scope and one algebra scope at a time, and the `Mathlib` order lemmas apply to graphs. -/

section Examples

open scoped IsoGraph.Subgraph IsoGraph.Semiring

example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d := add_le_add h h'
example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a * c ≤ b * d := mul_le_mul' h h'
example (a : IsoGraph) : 0 ≤ a := bot_le
example : (0 : IsoGraph) ≤ 1 := zero_le_one
example (a b : IsoGraph) (h : a ≤ b) : a * a ≤ b * b := mul_le_mul' h h

end Examples

section Examples

open scoped IsoGraph.Minor IsoGraph.StrongSemiring

example (a b c d : IsoGraph) (h : a ≤ b) (h' : c ≤ d) : a * c ≤ b * d := mul_le_mul' h h'
example (a b c : IsoGraph) (h : a ≤ b) : c * a ≤ c * b := mul_le_mul_of_nonneg_left h bot_le

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

end IsoGraph
