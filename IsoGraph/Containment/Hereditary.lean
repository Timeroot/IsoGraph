import IsoGraph.Containment.Defs

/-!
# Hereditary graph properties

Facts inherited by a graph contained in another one.
-/

namespace CGraph

namespace InducedSubgraphOf

variable {H : CGraph} {n : ℕ}

/-- An induced subgraph of a complete graph is complete. -/
theorem eq_complete (f : H.InducedSubgraphOf (complete n)) :
    (⟦H⟧ : IsoGraph) = IsoGraph.complete (FinEnum.card H.V) := by
  rw [IsoGraph.mk_eq_complete]
  intro x y hxy
  apply f.adj_map
  simp
  grind [f.injective]

end InducedSubgraphOf

namespace SubgraphOf

variable {H G : CGraph}

/-- A subgraph of an acyclic graph is acyclic. -/
theorem isAcyclic (f : H.SubgraphOf G) (hG : G.IsAcyclic) : H.IsAcyclic := by
  let φ : H.toSimple →g G.toSimple := ⟨f, fun h ↦ f.map_adj (by simpa using h)⟩
  exact hG.comap φ f.injective

/-- A subgraph of a bipartite graph is bipartite. -/
theorem isBipartite (f : H.SubgraphOf G) (hG : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := hG
  exact ⟨fun v ↦ c (f v), fun x y hxy ↦ hc _ _ (f.map_adj hxy)⟩

end SubgraphOf

end CGraph

namespace IsoGraph

/-- An induced subgraph of a complete graph is complete. -/
theorem IsInducedSubgraphOf.eq_complete {H : IsoGraph} {n : ℕ}
    (f : H ≤ᵢₛ complete n) : H = complete H.V := by
  obtain ⟨H, rfl⟩ := exists_cgraph H
  obtain ⟨f⟩ := f
  exact f.eq_complete

/-- A subgraph of a bipartite graph is bipartite. -/
theorem IsSubgraphOf.isBipartite {H G : IsoGraph} (f : H ≤ₛ G) (hG : G.IsBipartite) :
    H.IsBipartite := by
  obtain ⟨H, rfl⟩ := exists_cgraph H
  obtain ⟨G, rfl⟩ := exists_cgraph G
  obtain ⟨f⟩ := f
  rw [isBipartite_mk] at hG ⊢
  exact f.isBipartite hG

/-- A subgraph of an acyclic graph is acyclic. -/
theorem IsSubgraphOf.isAcyclic {H G : IsoGraph} (f : H ≤ₛ G) (hG : G.IsAcyclic) :
    H.IsAcyclic := by
  obtain ⟨H, rfl⟩ := exists_cgraph H
  obtain ⟨G, rfl⟩ := exists_cgraph G
  obtain ⟨f⟩ := f
  rw [isAcyclic_mk] at hG ⊢
  exact f.isAcyclic hG

end IsoGraph
