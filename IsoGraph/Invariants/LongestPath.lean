import IsoGraph.Containment.Algorithms.Cached

/-!

# Longest paths and longest induced paths

This module defines invariants of an `IsoGraph` defined in terms of path

## Main definitions

- `longestPathOrder` : The maximum order (number of vertices) of a path in `G`.
- `longestInducedPathOrder` : The maximum order (number of vertices) of an induced path in `G`.

## Main theorems

- `longestPathOrder_eq_sSup` : Characterization of `longestPathOrder` as the supremum over all path orders in `G`.
- `longestInducedPathOrder_eq_sSup` : Characterization of `longestInducedPathOrder` as the supremum over all induced path orders in `G`.

## Design choices

- In the literature, "length of a path" refers to the number of edges in the path, but internally it is more convenient to use the number of vertices, which we call the "order" of the path. This is because every graph has a path of order 0. We define `longestPath = longestPathOrder - 1`, etc.
- We define the invariants directly on `IsoGraph` rather than on `CGraph`/`SimpleGraph`

-/

set_option autoImplicit false

namespace IsoGraph

/-- `G` contains a path on `n` vertices. -/
def HasPathOfOrder (G : IsoGraph) (n : ℕ) : Prop :=
  path n ≤ₛ G

/-- `G` contains an induced path on `n` vertices. -/
def HasInducedPathOfOrder (G : IsoGraph) (n : ℕ) : Prop :=
  path n ≤ᵢₛ G

instance (G : IsoGraph) : DecidablePred G.HasPathOfOrder :=
  fun n ↦ instDecidableIsSubgraphOf (path n) G

instance (G : IsoGraph) : DecidablePred G.HasInducedPathOfOrder :=
  fun n ↦ instDecidableIsInducedSubgraphOf (path n) G

/-- Every induced path is a path. -/
theorem HasInducedPathOfOrder.hasPathOfOrder {G : IsoGraph} {n : ℕ}
    (h : G.HasInducedPathOfOrder n) : G.HasPathOfOrder n :=
  h.isSubgraphOf

/-- Removing the final vertex of a path gives a path of the preceding order. -/
theorem HasPathOfOrder.pred {G : IsoGraph} {n : ℕ} (h : G.HasPathOfOrder n) :
    G.HasPathOfOrder (n - 1) := by
  apply isSubgraphOf_trans (G := path n) ?_ h
  cases n with
  | zero => exact isSubgraphOf_refl _
  | succ n =>
      change Nonempty (CGraph.SubgraphOf (CGraph.path n) (CGraph.path (n + 1)))
      refine ⟨{
        toFun := fun i ↦ ⟨i.1, Nat.lt_succ_of_lt i.2⟩
        injective' := fun _ _ hij ↦ Fin.ext (congrArg (fun i : Fin (n + 1) ↦ i.1) hij)
        map_adj' := ?_
      }⟩
      intro i j hij
      change (decide (i ≠ j) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) = true at hij
      change (decide ((⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) ≠
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) = true
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hij ⊢
      exact ⟨fun heq ↦ hij.1 (Fin.ext (congrArg (fun k : Fin (n + 1) ↦ k.1) heq)), hij.2⟩

/-- The possible orders of path subgraphs of `G`. -/
def pathOrders (G : IsoGraph) : Finset ℕ :=
  (Finset.range (G.V + 1)).filter G.HasPathOfOrder

/-- The possible orders of induced path subgraphs of `G`. -/
def inducedPathOrders (G : IsoGraph) : Finset ℕ :=
  (Finset.range (G.V + 1)).filter G.HasInducedPathOfOrder

/-- The maximum order, or number of vertices, of a path in `G`. -/
def longestPathOrder (G : IsoGraph) : ℕ :=
  G.pathOrders.sup id

/-- The maximum order, or number of vertices, of an induced path in `G`. -/
def longestInducedPathOrder (G : IsoGraph) : ℕ :=
  G.inducedPathOrders.sup id

/-- The maximum length, or number of edges, of a path in `G`. -/
def longestPath (G : IsoGraph) : ℕ :=
  G.longestPathOrder - 1

/-- The maximum length, or number of edges, of an induced path in `G`. -/
def longestInducedPath (G : IsoGraph) : ℕ :=
  G.longestInducedPathOrder - 1

/-- A path of maximum order is a subgraph of `G`. -/
theorem longestPathOrder_isSubgraphOf (G : IsoGraph) : path G.longestPathOrder ≤ₛ G := by
  have hne : G.pathOrders.Nonempty := by
    refine ⟨0, ?_⟩
    rw [pathOrders, Finset.mem_filter]
    exact ⟨by simp, by simpa [HasPathOfOrder] using empty_zero_isSubgraphOf G⟩
  have hmem : G.longestPathOrder ∈ G.pathOrders := by
    rcases Finset.sup_mem_of_nonempty (f := id) hne with ⟨n, hn, h⟩
    simpa [longestPathOrder] using h ▸ hn
  exact (Finset.mem_filter.mp hmem).2

/-- No path subgraph of `G` has greater order than a longest path. -/
theorem pathOrder_le_longestPathOrder {G : IsoGraph} {n : ℕ} (h : path n ≤ₛ G) :
    n ≤ G.longestPathOrder := by
  have hnV : n ≤ G.V := by simpa using h.V_le
  apply Finset.le_sup (f := id)
  rw [pathOrders, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by omega), h⟩

/-- `longestPathOrder` is the supremum over all path orders in `G`. -/
theorem longestPathOrder_eq_sSup (G : IsoGraph) :
    G.longestPathOrder = sSup {n : ℕ | G.HasPathOfOrder n} := by
  apply le_antisymm
  · apply le_csSup
    · exact ⟨G.V, fun n hn ↦ by
        simpa using (show path n ≤ₛ G from hn).V_le⟩
    · exact G.longestPathOrder_isSubgraphOf
  · apply csSup_le
    · exact ⟨0, by simpa [HasPathOfOrder] using empty_zero_isSubgraphOf G⟩
    · intro n hn
      exact pathOrder_le_longestPathOrder hn

/-- An induced path of maximum order is an induced subgraph of `G`. -/
theorem longestInducedPathOrder_isInducedSubgraphOf (G : IsoGraph) :
    path G.longestInducedPathOrder ≤ᵢₛ G := by
  have hne : G.inducedPathOrders.Nonempty := by
    refine ⟨0, ?_⟩
    rw [inducedPathOrders, Finset.mem_filter]
    exact ⟨by simp, by simpa [HasInducedPathOfOrder] using empty_zero_isInducedSubgraphOf G⟩
  have hmem : G.longestInducedPathOrder ∈ G.inducedPathOrders := by
    rcases Finset.sup_mem_of_nonempty (f := id) hne with ⟨n, hn, h⟩
    simpa [longestInducedPathOrder] using h ▸ hn
  exact (Finset.mem_filter.mp hmem).2

/-- No induced path subgraph of `G` has greater order than a longest induced path. -/
theorem inducedPathOrder_le_longestInducedPathOrder {G : IsoGraph} {n : ℕ}
    (h : path n ≤ᵢₛ G) : n ≤ G.longestInducedPathOrder := by
  have hnV : n ≤ G.V := by simpa using h.V_le
  apply Finset.le_sup (f := id)
  rw [inducedPathOrders, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by omega), h⟩

/-- `longestInducedPathOrder` is the supremum over all induced path orders in `G`. -/
theorem longestInducedPathOrder_eq_sSup (G : IsoGraph) :
    G.longestInducedPathOrder = sSup {n : ℕ | G.HasInducedPathOfOrder n} := by
  apply le_antisymm
  · apply le_csSup
    · exact ⟨G.V, fun n hn ↦ by
        simpa using (show path n ≤ᵢₛ G from hn).V_le⟩
    · exact G.longestInducedPathOrder_isInducedSubgraphOf
  · apply csSup_le
    · exact ⟨0, by simpa [HasInducedPathOfOrder] using empty_zero_isInducedSubgraphOf G⟩
    · intro n hn
      exact inducedPathOrder_le_longestInducedPathOrder hn

end IsoGraph
