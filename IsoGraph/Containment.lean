import IsoGraph.Containment.Defs

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
-/
