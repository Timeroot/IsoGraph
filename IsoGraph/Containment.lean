import IsoGraph.Containment.Algorithms.Backtrack
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Defs
import IsoGraph.Containment.Minors

/-!
# The containment relations

When a graph theorist says that `H` "sits inside" `G` they mean one of about eight things, and all
eight are a map between the two graphs with some property attached: an injection for a subgraph, a
surjection for a quotient, a partial map with connected fibres for a minor, a family of disjoint
paths for a topological minor, a family of edge-disjoint trails for an immersion.

`Containment/Defs.lean` defines each of them twice.  On `CGraph` it is a structure carrying that
map — `H.SubgraphOf G` is the *type* of ways `H` is a subgraph of `G` — with the structures
extending one another so that the implications between the relations are projections, and with
`ofIso`, `refl` and `trans` for each.  On `IsoGraph` it is the `Prop` that such a structure exists,
and each of those becomes a scoped order instance, with `empty 0` at the bottom.

`Containment/Minors.lean` finishes the two minor relations: a minor with as many vertices as its
host is a subgraph of it, which makes both minor orders antisymmetric and so partial orders, and
a minor has no more edges than its host.  It also composes immersions.

`Containment/Algorithms/` decides some of these relations, on `CGraph`, by search.  Each search
returns the containment *itself* when it succeeds — not a `Bool` — and a theorem that the type is
empty when it fails, so a successful answer needs no further proof and a failed one is still a
complete answer.  `Backtrack.lean` has the search skeleton, which is graph-agnostic: all the
pruning is discharged by a single implication, so making a search cleverer cannot make it wrong.
`Algorithms/InducedSubgraph.lean` is the induced subgraph relation.
-/
