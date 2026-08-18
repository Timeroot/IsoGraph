import IsoGraph.Containment.Algorithms.Backtrack
import IsoGraph.Containment.Algorithms.Cached
import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.Embedding
import IsoGraph.Containment.Algorithms.Hom
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Containment.Algorithms.Twins
import IsoGraph.Containment.Defs
import IsoGraph.Containment.Minors

/-!
# The containment relations

When a graph theorist says that `H` "sits inside" `G` they mean one of about eight things, and all
eight are a map between the two graphs with some property attached: an injection for a subgraph, a
surjection for a quotient, a partial map with connected fibres for a minor, a total one for a
contraction, a family of disjoint paths for a topological minor, a family of edge-disjoint trails
for an immersion.

`Containment/Defs.lean` defines each of them twice.  On `CGraph` it is a structure carrying that
map — `H.SubgraphOf G` is the *type* of ways `H` is a subgraph of `G` — with the structures
extending one another so that the implications between the relations are projections, and with
`ofIso`, `refl` and `trans` for each.  On `IsoGraph` it is the `Prop` that such a structure exists,
and each of those becomes a scoped order instance, with `empty 0` at the bottom.

`Containment/Minors.lean` finishes the five relations `Defs.lean` leaves open.  A minor with as
many vertices as its host is a subgraph of it, which makes the minor, induced minor and contraction
orders antisymmetric, and a minor has no more edges than its host.  Topological minors and
immersions compose there, by substituting a path or a trail of `G` for each edge of one in `K`; a
topological minor is then shown to be a minor and an immersion to have no more edges than its host,
which gives those two their antisymmetry in turn.  All five are partial orders by the end of the
file — the contraction order alone without a bottom element, since a contraction deletes nothing.

`Containment/Algorithms/` decides some of these relations, on `CGraph`, by search.  Each search
returns the containment *itself* when it succeeds — not a `Bool` — and a theorem that the type is
empty when it fails, so a successful answer needs no further proof and a failed one is still a
complete answer.  `Backtrack.lean` has the search skeleton, which is graph-agnostic: all the
pruning is discharged by a single implication, so making a search cleverer cannot make it wrong.
`Algorithms/Embedding.lean` searches for an injection of the pattern into the host and is run two
ways, by `Algorithms/Subgraph.lean` and `Algorithms/InducedSubgraph.lean`, which differ only in
whether a non-edge of the pattern has to stay a non-edge; `Algorithms/Minor.lean` is the minor
relation, whose search builds the branch sets in an order that keeps them connected as it goes.
`Algorithms/Contraction.lean` runs the opposite way round, labelling every vertex of the host with
the block it goes into, because a contraction may throw nothing away.  `Algorithms/Hom.lean` drops
injectivity altogether, which decides both the homomorphism order — `k`-colourability, against
`complete k` — and the quotient one.  `Algorithms/Twins.lean` is shared between them all: it finds
the classes of interchangeable vertices of the pattern, so that no search looks at a solution and
its relabellings.

`Algorithms/Cached.lean` is the layer to call.  Each of the six searches there runs on adjacency
matrices of the pattern *and* the host rather than on their edge lists, which is worth an order of
magnitude on anything out of the gallery, and transports the answer back.

Three relations still have no search: **induced minor**, **topological minor** and **immersion**.
-/
