import IsoGraph.Algebra.Semiring
import IsoGraph.Algebra.Components
import IsoGraph.Algebra.Cancellation
import IsoGraph.Algebra.Factorization
import IsoGraph.Algebra.Connected
import IsoGraph.Algebra.UniqueFactorization
import IsoGraph.Algebra.Exponential

/-!
# The graph semiring

Isomorphism classes of finite simple graphs form a commutative semiring under disjoint union and
any one of the four products.  This folder sets the structure up, decides which of the usual
ring-theoretic properties hold, and studies the exponential.  The additive monoid is free on the
connected graphs, and `comps` reads a graph off as the multiset of its atoms; `Components.lean`
evaluates that multiset at every construction in the gallery.

It comes last: the counterexamples that settle the abstract questions are drawn from the whole of
`IsoGraph.SmallGraphs`.
-/
