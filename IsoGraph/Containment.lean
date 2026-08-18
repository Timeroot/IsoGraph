import IsoGraph.Containment.Algorithms.Backtrack
import IsoGraph.Containment.Algorithms.Cached
import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.Embedding
import IsoGraph.Containment.Algorithms.Hom
import IsoGraph.Containment.Algorithms.Immersion
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Containment.Algorithms.TopMinor
import IsoGraph.Containment.Algorithms.Twins
import IsoGraph.Containment.Defs
import IsoGraph.Containment.Minors
import IsoGraph.Containment.Monotone
import IsoGraph.Containment.Ordered
import IsoGraph.Containment.Split

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

Outside those scopes each relation has a global notation, so that a statement can mention two of
them at once: `≤ₕ ≤ₛ ≤ᵢₛ ≤ₘ ≤ᵢₘ ≤ₚ ≤ₜₘ ≤ₑ` for hom, subgraph, induced subgraph, minor, induced
minor, contraction, topological minor and immersion, and `≤/` for the quotient order, whose
arguments the notation flips.

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
relation, whose search builds the branch sets in an order that keeps them connected as it goes, and
is run twice over: with its induced test switched on it decides the induced minor relation too.
`Algorithms/Contraction.lean` runs the opposite way round, labelling every vertex of the host with
the block it goes into, because a contraction may throw nothing away.  `Algorithms/TopMinor.lean`
places the branch vertices and the subdivided paths in one interleaved search, so that each path is
routed as soon as both of its ends are down, and `Algorithms/Immersion.lean` runs that search with
the disjointness moved from vertices to edges, so that what it routes are trails rather than paths.
`Algorithms/Hom.lean` drops injectivity altogether, which decides both the homomorphism order —
`k`-colourability, against `complete k` — and the quotient one.  `Algorithms/Twins.lean` is shared
between them all: it finds the classes of interchangeable vertices of the pattern, so that no
search looks at a solution and its relabellings.

`Containment/Monotone.lean` crosses the nine relations with the two sums and four products of
`Values/Identities/Semiring.lean`: for which of the fifty-four pairs does `H ≤ G` and `H' ≤ G'`
give `H op H' ≤ G op G'`?  The four relations that are a map of vertices always do, whatever the
operation; the minor relations need the branch sets of the product to stay connected, which rules
out the tensor product; the two that replace an edge by a walk get the two sums, where the walks of
the two summands cannot meet, and the cartesian product, where an edge moves one coordinate and its
walk runs along one row or one column.  Each entry is a construction on the `CGraph`
models and a theorem about `IsoGraph` lifted from it.

`Containment/Split.lean` cuts an inclusion apart along a disjoint union.  A subgraph of `C ⊕g D`
sends each vertex to one side or the other, and by connectivity a whole component goes the same
way, so the source splits as well: `H ⊕g K ≤ C ⊕g D` gives `H = H₁ ⊕g H₂` and `K = K₁ ⊕g K₂` with
`H₁ ⊕g K₁ ≤ C` and `H₂ ⊕g K₂ ≤ D`.  The splitting needs a construction the rest of the library
does without — the induced subgraph on a set of vertices, which is a `CGraph` and not an
`IsoGraph` operation, since it depends on the labelling.  The file also complements an induced
subgraph, which turns every statement about the disjoint union into one about the join.

`Containment/Ordered.lean` reads that table back as typeclasses.  Opening an order scope and an
algebra scope at once — `IsoGraph.Subgraph` and `IsoGraph.Semiring`, say — turns on
`IsOrderedAddMonoid`, `IsOrderedMonoid`, `ZeroLEOneClass` and, over the two distributive pairs,
`IsOrderedRing`, so the ordered-algebra lemmas of `Mathlib` apply to graphs.  It also has the two
questions that are about the orders alone: none of the nine has a greatest element, and only the
quotient and contraction orders have no least one; and cancellation, where the splitting above,
run by induction on the number of vertices cancelled, upgrades three of those pairs to
`IsOrderedCancelAddMonoid` — the disjoint union in the subgraph and induced subgraph orders, the
join in the induced subgraph order — while no product cancels in any of the nine, and the two sums
each fail in several.

`Algorithms/Cached.lean` is the layer to call.  Each of the nine searches there runs on adjacency
matrices of the pattern *and* the host rather than on their edge lists, which is worth an order of
magnitude on anything out of the gallery, and transports the answer back.
-/
