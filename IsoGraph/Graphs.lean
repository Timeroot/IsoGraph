import IsoGraph.Graphs.Cache
import IsoGraph.Graphs.Constructions
import IsoGraph.Graphs.Quotient
import IsoGraph.Graphs.CliqueSum
import IsoGraph.Graphs.SRG
import IsoGraph.Graphs.Polyhedra
import IsoGraph.Graphs.NamedSmallGraphs
import IsoGraph.Graphs.NamedGraphs
import IsoGraph.Graphs.NamedSolids
import IsoGraph.Graphs.NamedCages
import IsoGraph.Graphs.Balaban11Cage
import IsoGraph.Graphs.Tutte12Cage

/-!
# The graphs

Everything that builds a graph.  `Graphs/Constructions.lean` has the families and the operations
— `empty`, `complete`, `path`, `cycle`, `kneser`, the products, the complement, the join — as
`CGraph`s, with a concrete vertex type; `Graphs/Quotient.lean` carries each of them across to
`IsoGraph`, the quotient by isomorphism, so that the equations between them can be stated as
equations; `Graphs/CliqueSum.lean` glues two graphs along a shared vertex or edge.
`Graphs/Polyhedra.lean` describes a polyhedron by its faces and builds its truncation,
rectification, kis and vertex–face incidence graph from that list alone.  `Graphs/Cache.lean`
replaces the adjacency function of a graph on `Fin n` by a lookup in a precomputed `n × n` array,
which is the same graph — `CGraph.cache_eq` — and a faster one to search.

The rest is the gallery: individual graphs with proper names.  `Graphs/NamedSmallGraphs.lean`
names all 143 connected graphs on at most six vertices, `Graphs/SRG.lean` collects the strongly
regular ones, and the four `Named…` and `…Cage` modules hold the larger sporadic graphs — the
cages, the Archimedean and Catalan solids, the generalized Petersen graphs.  The last two are one
graph each: their girth proofs dominate the build, and in modules of their own they are checked in
parallel with the rest.
-/
