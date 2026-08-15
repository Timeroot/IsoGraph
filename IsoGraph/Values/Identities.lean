import IsoGraph.Values.Identities.Concrete
import IsoGraph.Values.Identities.Extremal
import IsoGraph.Values.Identities.Automorphisms
import IsoGraph.Values.Identities.EdgeColourings
import IsoGraph.Values.Identities.Identifications
import IsoGraph.Values.Identities.Tables
import IsoGraph.Values.Identities.Bounds
import IsoGraph.Values.Identities.Families
import IsoGraph.Values.Identities.Circulants
import IsoGraph.Values.Identities.TuranGraphs
import IsoGraph.Values.Identities.Grotzsch
import IsoGraph.Values.Identities.TreesAndCycles
import IsoGraph.Values.Identities.Brackets
import IsoGraph.Values.Identities.Complements
import IsoGraph.Values.Identities.Products
import IsoGraph.Values.Identities.Mycielskians
import IsoGraph.Values.Identities.Operators
import IsoGraph.Values.Identities.Semiring
import IsoGraph.Values.Identities.Exponential

/-!
# The identities between the constructions, and the tables of their invariants

`IsoGraph/Graphs/Quotient.lean` carries every construction of `IsoGraph/Graphs/Constructions.lean`
across to `IsoGraph`, the quotient by isomorphism.  Two `CGraph`s are *equal* only when the vertex
types are equal and the adjacency functions agree on the nose, which is far too fine a relation for
statements like "the complement of the 5-cycle is the 5-cycle"; on `IsoGraph` that statement is an
honest equation, and these modules collect a hundred or so of them, together with the value of
every invariant on every family.

## Proving an identity

Three tools cover almost everything.

* `IsoGraph.mk_eq_empty` and `IsoGraph.mk_eq_complete`: a graph with no edges is `empty` on its
  vertex count, and a graph with all of them is `complete`.  These two settle every degenerate
  case — `kneser n 0`, `hypercube 1`, `lexProduct (complete m) (complete n)`, … — with no
  bijection to write down, since `Fintype.equivFin` supplies one.
* `CGraph.isoOfAdj e (by decide)` for the small sporadic identities: `cycle 3 = complete 3`,
  `(cycle 5)ᶜ = cycle 5`, `hypercube 2 = cycle 4`.  The permutation is written out as a
  vector and the kernel checks all `n²` adjacencies.
* Rewriting with the identities already proved.  `join`, `bipartite`, `star`, `wheel`, `rook`, …
  are all built from `compl`, `disjUnion` and the products, so their identities follow from
  those without ever descending to `CGraph` again — see `join_complete`, `wheel_three` or
  `bipartite_one_one`.

## Transferring a fact

Each entry of the invariant tables is wanted twice: once for `CGraph`, where it is proved, and
once for `IsoGraph`, where it is used.  The `@[toIsoGraph]` attribute of
`IsoGraph/ToIsoGraph.lean` writes the second copy, so most of the `IsoGraph`-level statements
never appear in the source at all: the `CGraph`-level theorem is tagged where it is declared, and
the attribute generates its counterpart.  What it rewrites with are the bridging `…_mk` and
`…_def` lemmas gathered into the `isoTransfer` set at the end of `IsoGraph/Graphs/Quotient.lean`.

## The parts

The material is one long chain — each module uses what the ones before it proved — split for the
sake of the editor rather than the build.  The first four are the `CGraph`-level work; the rest
are the tables themselves, on the quotient.

| module | what is in it |
| --- | --- |
| `Identities/Concrete.lean` | explicit families, relabellings, and the invariants of the four products |
| `Identities/Extremal.lean` | Turán, Ramsey, Gallai, clique–coclique; covering, domination, radius, counting |
| `Identities/Automorphisms.lean` | automorphism counts, the handshaking lemma, regularity, matchings |
| `Identities/EdgeColourings.lean` | edge colourings by hand, the Petersen graph, the girth of the cycles |
| `Identities/Identifications.lean` | the equations between the constructions |
| `Identities/Tables.lean` | line graphs and Mycielskians; degrees, chromatic numbers, girths |
| `Identities/Bounds.lean` | the general bounds on the quotient, and the columns they govern |
| `Identities/Families.lean` | self-complementarity, and the families introduced for their own sake |
| `Identities/Circulants.lean` | the circulant graphs, the `2 × n` grid, and vertex transitivity |
| `Identities/TuranGraphs.lean` | the Turán, friendship and crown graphs |
| `Identities/Grotzsch.lean` | the Grötzsch graph and the Möbius ladders |
| `Identities/TreesAndCycles.lean` | tadpoles, lollipops, spiders and theta graphs |
| `Identities/Brackets.lean` | the bracketed entries, and the negative ones |
| `Identities/Complements.lean` | complements, and the graphs built from two named families |
| `Identities/Products.lean` | the four products applied to pairs of families |
| `Identities/Mycielskians.lean` | the Mycielskian and the line graph of everything, and of each other |
| `Identities/Operators.lean` | the folded cube, and the transitivity and regularity columns |
| `Identities/Semiring.lean` | the connected components, and the scoped algebra of the six operations |
| `Identities/Exponential.lean` | the graph exponential, and the exponent laws it fails |
-/
