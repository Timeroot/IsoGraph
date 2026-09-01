import IsoGraph.Invariants.LongestPath
import IsoGraph.SmallGraphs.Defs.Families

/-!
# Longest paths in named graphs

Headline values of longest-path invariants for graphs in the gallery.
-/

namespace IsoGraph

/-- The five-dimensional snake-in-the-box has length thirteen. -/
theorem longestInducedPath_hypercube_five : (hypercube 5).longestInducedPath = 13 := by
  native_decide

end IsoGraph
