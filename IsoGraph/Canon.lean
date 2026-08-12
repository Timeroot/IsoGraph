import IsoGraph.Canon.Algorithm
import IsoGraph.Canon.Equivariance
import IsoGraph.Canon.Search
import IsoGraph.Canon.Autos
import IsoGraph.Canon.Node
import IsoGraph.Canon.Orbits
import IsoGraph.Canon.Progress
import IsoGraph.Canon.Monotone
import IsoGraph.Canon.Paths
import IsoGraph.Canon.Pinned
import IsoGraph.Canon.Jump
import IsoGraph.Canon.Leaves
import IsoGraph.Canon.Dominate
import IsoGraph.Canon.Branch
import IsoGraph.Canon.Optimal
import IsoGraph.Canon.Correct
import IsoGraph.Canon.Spec
import IsoGraph.Canon.Group
import IsoGraph.Canon.Subtree
import IsoGraph.Canon.Chain
import IsoGraph.Canon.Transitive

/-!
# The canonical labelling engine

A McKay-style individualisation–refinement canonical form for graphs on `Fin n`, and its
correctness.  `Algorithm.lean` is the code — plain functional Lean over `Array`, importing
nothing — and the remaining files establish that what it returns depends only on the isomorphism
class.  That statement is `canonAdj_relabel` in `Canon/Spec.lean`; `IsoGraph/Basic.lean` restates
it for abstract vertex types and for the quotient.
-/
