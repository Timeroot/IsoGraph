import IsoGraph.Invariants.LongestPath
import IsoGraph.SmallGraphs.Defs.Families

/-!
# Longest paths in named graphs

Headline values of longest-path invariants for graphs in the gallery.
-/

namespace IsoGraph

/-- The zero-dimensional hypercube has no edges. -/
theorem longestInducedPath_hypercube_zero : (hypercube 0).longestInducedPath = 0 := by
  native_decide

/-- The one-dimensional snake-in-the-box has length one. -/
theorem longestInducedPath_hypercube_one : (hypercube 1).longestInducedPath = 1 := by
  native_decide

/-- The two-dimensional snake-in-the-box has length two. -/
theorem longestInducedPath_hypercube_two : (hypercube 2).longestInducedPath = 2 := by
  native_decide

/-- The three-dimensional snake-in-the-box has length four. -/
theorem longestInducedPath_hypercube_three : (hypercube 3).longestInducedPath = 4 := by
  native_decide

/-- The four-dimensional snake-in-the-box has length seven. -/
theorem longestInducedPath_hypercube_four : (hypercube 4).longestInducedPath = 7 := by
  native_decide

/-- The five-dimensional snake-in-the-box has length thirteen. -/
theorem longestInducedPath_hypercube_five : (hypercube 5).longestInducedPath = 13 := by
  native_decide

end IsoGraph
