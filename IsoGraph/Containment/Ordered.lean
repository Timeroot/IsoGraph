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
