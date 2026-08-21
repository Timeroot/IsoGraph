import IsoGraph.Invariants.Basic
import IsoGraph.Invariants.Derived
import IsoGraph.Invariants.Fractional
import IsoGraph.Invariants.Connectivity
import IsoGraph.Invariants.Hamiltonian
import IsoGraph.Invariants.Certificates
import IsoGraph.Invariants.Symmetry

/-!
# The invariants

What can be said about a graph without naming its vertices.  `Invariants/Basic.lean` defines the
invariants themselves — the order, the number of edges, the degree sequence, the clique and
independence numbers, connectivity, girth, the chromatic number, … — each as a thin wrapper
around the corresponding Mathlib notion for `G.toSimple`, and each tagged `@[toIsoGraph]` so that
the attribute lifts it to `IsoGraph`.

`Invariants/Derived.lean` adds the three invariants that are read off *another* graph — the
chromatic index and the matching number from the line graph, the clique cover number from the
complement — together with self-complementarity, which on the quotient is the equation `Gᶜ = G`.
They come after the constructions rather than with the rest, because they need them.

`Invariants/Fractional.lean` relaxes two of them.  The fractional independence and chromatic
numbers are the values of linear programs, so they are real rather than natural numbers, and they
sit between the integer invariants they relax: `α ≤ α_f ≤ θ` and `ω ≤ χ_f ≤ χ`.  Being linear
programs they are far cheaper to certify than the things they bound, which is what
`IsoGraph/Fractional.lean` — the tactics `compute_fractional_indepNum` and
`compute_fractional_chromNum`, and a fast path for `graph_sat` — is for.

`Invariants/Connectivity.lean` and `Invariants/Hamiltonian.lean` add the three invariants that
Mathlib does not have at all: the edge connectivity, the vertex connectivity and Hamiltonicity.
Each is defined at the `CGraph` level from scratch — an edge cut is a set of vertices, a separator
is a two-colouring of what is left when a set is deleted — so that the definitions stay decidable
and transport along an isomorphism directly.  Whitney's `κ ≤ λ ≤ δ` relates the first two, and a
Hamiltonian graph is connected, so all three sit in one chain.

The remaining files are about *establishing* those quantities for a graph in hand.
`Invariants/Certificates.lean` turns a finite witness — a list of vertices closing into a cycle, a
neighbour table, a numbering — into girth, bipartiteness, regularity and connectivity statements
that would otherwise quantify over all of an infinite-looking search space.
`Invariants/Symmetry.lean` computes the automorphism group with the canonical labelling engine and
uses it to prove vertex- and arc-transitivity.
-/
