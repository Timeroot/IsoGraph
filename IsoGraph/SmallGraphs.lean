import IsoGraph.SmallGraphs.Defs
import IsoGraph.SmallGraphs.Equalities
import IsoGraph.SmallGraphs.Counts
import IsoGraph.SmallGraphs.Structure
import IsoGraph.SmallGraphs.Symmetry
import IsoGraph.SmallGraphs.Colouring
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

/-!
# The named graphs

Everything known about the graphs of the gallery.  The head of the folder is topical, in the same
order as `IsoGraph.Core`:

* `SmallGraphs.Defs` — the definitions.
* `SmallGraphs.Equalities` — when one named graph *is* another; the normalising `simp` lemmas.
* `SmallGraphs.Counts`, `.Structure`, `.Symmetry`, `.Colouring` — the invariants, by topic.

The rest of the folder is a chain, each file taking up where the one before leaves off.  It is
organised by the family or the operator under study — `Circulants`, `TuranGraphs`, `Grotzsch`,
`TreesAndCycles`, `Complements`, `Products`, `Mycielskians`, `Operators` — with `Tables`,
`Bounds` and `Brackets` holding the values that are read off a table or squeezed between two
bounds rather than computed directly.
-/
