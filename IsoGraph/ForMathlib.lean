import IsoGraph.ForMathlib.Analysis
import IsoGraph.ForMathlib.Array
import IsoGraph.ForMathlib.Bits
import IsoGraph.ForMathlib.Decide
import IsoGraph.ForMathlib.List
import IsoGraph.ForMathlib.Matrix
import IsoGraph.ForMathlib.Nat
import IsoGraph.ForMathlib.Perm
import IsoGraph.ForMathlib.QuadraticChar
import IsoGraph.ForMathlib.SimpleGraph
import IsoGraph.ForMathlib.ZMod

/-!
# Lemmas that belong to Mathlib

Everything in this folder is stated in Mathlib's language alone: no `CGraph`, no canonical form,
nothing from the rest of the development.  Each lemma was proved because something here needed
it, and each is a candidate to be contributed upstream — at which point the file it lives in
shrinks by one.

The modules are grouped by subject: `Nat`, `ZMod` and `Bits` for arithmetic and bit fiddling,
`List` and `Array` for the containers the canonical form runs on, `Decide` and `Perm` for two
small odds-and-ends, `QuadraticChar` for the character sums behind the Paley graphs, `Matrix` and
`Analysis` for the spectral computations, and `SimpleGraph` for the graph facts themselves —
chiefly that every invariant Mathlib defines is invariant under `SimpleGraph.Iso`, which is the
one lemma family here that the rest of the library leans on everywhere.

Nothing in this folder imports anything from `IsoGraph`, so the dependency runs one way only.
-/
