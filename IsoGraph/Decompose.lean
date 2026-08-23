import IsoGraph.Decompose.Cert
import IsoGraph.Decompose.Atlas
import IsoGraph.Decompose.Tactic
import IsoGraph.Decompose.Spectrum

/-!
# Describing a graph

Given a graph presented as an adjacency table — the output of a construction, a line graph, a
Mycielskian — what *is* it?  This folder answers that question mechanically: it searches for a
description of the graph as a formula in named graphs, disjoint unions, joins and complements, and
returns the description together with an isomorphism proving it right.

`Decompose/Cert.lean` is the checker.  A pair of lists of naturals describes a bijection of vertex
sets and its inverse; `isoListOK` is a `Bool` saying that the bijection preserves adjacency, and
`isoOfList` turns a proof of that into a `CGraph.Iso`.  The point of routing everything through a
list is that checking one is a closed computation, so `decide` suffices — the kernel never sees the
search, only the answer, and there is no `native_decide` anywhere.

`Decompose/Atlas.lean` is the search.  It carries an atlas of some fifteen hundred graphs — the
individually named ones, the strongly regular ones, and the finite initial segments of the infinite
families — indexed by canonical code, and a recursive procedure that looks a graph up, and failing
that splits it into components, or co-components, or complements it and tries again.  All of it is
ordinary compiled Lean working on a bitset adjacency matrix, not meta code.

`Decompose/Tactic.lean` is the interface: `#decompose_graph` to print a description,
`generate_graph_iso` to bind an isomorphism to it as a `let` in the context, and `decompose_graph`
to rewrite the graph in the goal to its description.

`Decompose/Spectrum.lean` is what the description is *for*: `compute_lapSpectrum` decomposes a
graph and then evaluates the Laplacian spectrum of the description, since the disjoint union, the
join and the complement all have unconditional rules for it.  The eigenvalues come out as explicit
real numbers — integers for a cograph, cosines for anything with a cycle or a path in it.
-/
