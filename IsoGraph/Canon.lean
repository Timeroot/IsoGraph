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

/-!
# The canonical labelling engine

A McKay-style individualisation–refinement canonical form for graphs on `Fin n`, and its
correctness proof.  `Algorithm.lean` is the code — plain functional Lean over `Array`, importing
nothing — and everything else is the proof that what it returns depends only on the isomorphism
class.  The single statement the rest of the development uses is `canonAdj_relabel` in
`Canon/Spec.lean`; `IsoGraph/Basic.lean` lifts it to abstract vertex types and to the quotient.
-/
