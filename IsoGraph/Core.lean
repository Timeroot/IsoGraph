import IsoGraph.Core.Defs
import IsoGraph.Core.Quotient
import IsoGraph.Core.CliqueSum
import IsoGraph.Core.Identities
import IsoGraph.Core.Counts
import IsoGraph.Core.Structure
import IsoGraph.Core.Symmetry
import IsoGraph.Core.Colouring

/-!
# The core library

The graphs that everything else is built from — the empty graph, the complete graph, the path and
the cycle — the operations that combine them, and what the invariants of `IsoGraph.Invariants` come
to on both.

The files split by topic, and each of them covers the whole of `Core.Defs`:

* `Core.Defs` — the definitions and the notation, nothing else.
* `Core.Quotient` — the same operations on `IsoGraph`, and the structural laws they satisfy there.
* `Core.CliqueSum` — gluing along a vertex or an edge.
* `Core.Identities` — equations between the constructions, mostly `simp` lemmas.
* `Core.Counts` — order, size, degrees.
* `Core.Structure` — connectivity, girth, distance, acyclicity.
* `Core.Symmetry` — automorphisms, transitivity, regularity.
* `Core.Colouring` — colourings, cliques, independent sets, covers, matchings.

Facts about the *named* graphs — the Petersen graph, the cages, the Kneser family — are not here;
they live in `IsoGraph.SmallGraphs`.
-/
