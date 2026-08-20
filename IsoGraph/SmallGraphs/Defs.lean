import IsoGraph.SmallGraphs.Defs.Families
import IsoGraph.SmallGraphs.Defs.SRG
import IsoGraph.SmallGraphs.Defs.Polyhedra
import IsoGraph.SmallGraphs.Defs.Small
import IsoGraph.SmallGraphs.Defs.Named
import IsoGraph.SmallGraphs.Defs.Solids
import IsoGraph.SmallGraphs.Defs.Cages
import IsoGraph.SmallGraphs.Defs.Balaban11Cage
import IsoGraph.SmallGraphs.Defs.Tutte12Cage

/-!
# The gallery

Definitions of the named graphs and of the parametrised families, and nothing else: no invariant is
computed here.  `Defs.Families` comes very early — the core library states its own lemmas for the
Kneser and circulant families — and the rest come after `IsoGraph.Core`, because the girth
certificates of the cages already need the core invariant lemmas.
-/
