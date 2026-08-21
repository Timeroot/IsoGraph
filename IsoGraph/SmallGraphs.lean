import IsoGraph.SmallGraphs.Defs
import IsoGraph.SmallGraphs.Equalities
import IsoGraph.SmallGraphs.Counts
import IsoGraph.SmallGraphs.Structure
import IsoGraph.SmallGraphs.Symmetry
import IsoGraph.SmallGraphs.Colouring
import IsoGraph.SmallGraphs.Substructure
import IsoGraph.SmallGraphs.Values
import IsoGraph.SmallGraphs.Extremal
import IsoGraph.SmallGraphs.EdgeColourings
import IsoGraph.SmallGraphs.Identifications
import IsoGraph.SmallGraphs.Tables
import IsoGraph.SmallGraphs.Bounds
import IsoGraph.SmallGraphs.Families
import IsoGraph.SmallGraphs.Circulants
import IsoGraph.SmallGraphs.TuranGraphs
import IsoGraph.SmallGraphs.Grotzsch
import IsoGraph.SmallGraphs.TreesAndCycles
import IsoGraph.SmallGraphs.Brackets
import IsoGraph.SmallGraphs.Complements
import IsoGraph.SmallGraphs.Products
import IsoGraph.SmallGraphs.Mycielskians
import IsoGraph.SmallGraphs.Operators
import IsoGraph.SmallGraphs.SatValues
import IsoGraph.SmallGraphs.SolidValues
import IsoGraph.SmallGraphs.CageValues
import IsoGraph.SmallGraphs.CubicValues
import IsoGraph.SmallGraphs.BipartiteCageValues

/-!
# The named graphs

Everything known about the graphs of the gallery.  The head of the folder is topical, in the same
order as `IsoGraph.Core`:

* `SmallGraphs.Defs` — the definitions.
* `SmallGraphs.Equalities` — when one named graph *is* another; the normalising `simp` lemmas.
* `SmallGraphs.Counts`, `.Structure`, `.Symmetry`, `.Colouring` — the invariants, by topic.
* `SmallGraphs.Substructure` — which named graph sits inside which other, in each of the nine
  containment relations of `IsoGraph.Containment`.

The rest of the folder is a chain, each file taking up where the one before leaves off.  It is
organised by the family or the operator under study — `Circulants`, `TuranGraphs`, `Grotzsch`,
`TreesAndCycles`, `Complements`, `Products`, `Mycielskians`, `Operators` — with `Tables`,
`Bounds` and `Brackets` holding the values that are read off a table or squeezed between two
bounds rather than computed directly.

Five leaves hang off `Operators`, all holding values whose hard half is a SAT refutation:
`SatValues` for the Chvátal, Tietze and Robertson graphs, `SolidValues` for the Platonic,
Archimedean and Catalan solids, `CageValues` for the cages and the small named cubic graphs,
`CubicValues` for five more cubic graphs, the Wagner graph up to the truncated icosahedron, and
`BipartiteCageValues` for the six large bipartite cages, the Harries graph up to the Tutte
12-cage.
-/
