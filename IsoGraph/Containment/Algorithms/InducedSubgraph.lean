import IsoGraph.Containment.Algorithms.Embedding

/-!
# Deciding the induced subgraph relation

`CGraph.findInducedSubgraph` searches for an induced copy of `H` inside `G` and returns one if
there is one; `CGraph.isEmpty_inducedSubgraphOf_of_eq_none` is the other half of the answer, that
coming back empty means there is no such copy at all.

The search itself is `Algorithms/Embedding.lean`, run with `ind := true`, and everything
interesting about it — the search order, the pruning, the tabulated host, the symmetry breaking —
is documented there.  What is here is only the two ends: turning a finished assignment into an
`InducedSubgraphOf`, and turning a genuine `InducedSubgraphOf` into an assignment the search would
have found.  `Algorithms/Subgraph.lean` is the same two ends for the ordinary subgraph relation.

Deciding this relation is NP-hard — `H` a clique is the clique problem — so nothing here is
polynomial, and a pattern of a dozen vertices with no edges against a host of two dozen is already
enough to keep it busy.  The pruning is what makes the cases one actually asks about tractable.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {H G : CGraph} {rank : G.V → ℕ} {n : ℕ} {pairs : List (H.V × H.V)}

/-- The induced subgraph a complete, consistent assignment describes. -/
def InducedSubgraphOf.ofAsg (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst)
    (hg : goalAsg H G true rank n pairs r = true) : H.InducedSubgraphOf G where
  toFun := asgFun H G r hcov
  injective' := asgFun_injective hg
  map_adj' _ _ h := asgFun_map_adj hg h
  adj_map' _ _ h := asgFun_adj_map hg h

/-- **Relabelling an embedding along an automorphism of the pattern.** -/
def InducedSubgraphOf.reindex (f : H.InducedSubgraphOf G) {σ : H.V → H.V}
    (hinj : Function.Injective σ) (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    H.InducedSubgraphOf G where
  toFun x := f (σ x)
  injective' := f.injective.comp hinj
  map_adj' _ _ h := f.map_adj (by rw [hadj]; exact h)
  adj_map' _ _ h := by rw [← hadj]; exact f.adj_map h

/-- What `exists_sorted_pairs` needs of the induced subgraph relation: it is closed under
relabelling by an automorphism of the pattern. -/
theorem InducedSubgraphOf.exists_reindex (f : H.InducedSubgraphOf G) {σ : H.V → H.V}
    (hinj : Function.Injective σ) (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    ∃ g : H.InducedSubgraphOf G, ∀ x, g x = f (σ x) :=
  ⟨f.reindex hinj hadj, fun _ ↦ rfl⟩

variable (H G)

/-- **Is `H` an induced subgraph of `G`?**  Returns a witness if so.  See
`isEmpty_inducedSubgraphOf_of_eq_none` for the other half of the answer. -/
def findInducedSubgraph (rH : Roster H.V) (rG : Roster G.V) : Option (H.InducedSubgraphOf G) :=
  Option.pmap (p := fun r ↦ (∀ x : H.V, x ∈ r.map Prod.fst) ∧
      goalAsg H G true (hostRank G rG) rG.toList.length
        (symPairs H (searchOrder H rH.toList)) r = true)
    (fun r hr ↦ InducedSubgraphOf.ofAsg r hr.1 hr.2) (searchAsg H G true rH rG)
    (fun _ hr ↦ ⟨searchAsg_cov hr, searchAsg_goal hr⟩)

theorem findInducedSubgraph_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findInducedSubgraph H G rH rG = none ↔ searchAsg H G true rH rG = none :=
  Option.pmap_eq_none_iff

/-! ## Completeness -/

variable {H G}

/-- A vertex of an induced subgraph has no more neighbours than its image. -/
theorem degree_le_of_inducedSubgraphOf (f : H.InducedSubgraphOf G) (x : H.V) :
    H.toSimple.degree x ≤ G.toSimple.degree (f x) :=
  degree_le_of_map_adj f.injective (fun h ↦ f.map_adj h) x

/-- **Completeness**: when the search comes back empty, `H` is not an induced subgraph of `G`. -/
theorem isEmpty_inducedSubgraphOf_of_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findInducedSubgraph H G rH rG = none) : IsEmpty (H.InducedSubgraphOf G) := by
  rw [findInducedSubgraph_eq_none_iff, searchAsg] at h
  refine ⟨fun f ↦ ?_⟩
  split at h
  · -- the embedding is first relabelled to one the symmetry test accepts
    obtain ⟨g, hg⟩ := exists_sorted_pairs (fun (f : H.InducedSubgraphOf G) ↦ ⇑f)
      (fun f {_σ} hinj hadj ↦ f.exists_reindex hinj hadj) (hs := searchOrder H rH.toList)
      (hostRank G rG) (mem_searchOrder H rH.mem_toList) f
    have hsol : ((searchOrder H rH.toList).map fun x ↦ (x, g x)).map Prod.fst =
        searchOrder H rH.toList := by
      simp [Function.comp_def]
    have hri : Function.Injective (hostRank G rG) := fun u v huv ↦
      (List.idxOf_inj (rG.mem_toList u)).mp huv
    have hrn : ∀ v, hostRank G rG v < rG.toList.length := fun v ↦
      List.idxOf_lt_length_of_mem (rG.mem_toList v)
    have hn := Backtrack.dfs_eq_none
      (mem_candList H G true rG.mem_toList (rank := hostRank G rG) (fun _ ↦ rfl) _ _) h hsol
    rw [List.append_nil, goalAsg_of_emb true _ _ _ g.injective
      (fun x y _ ↦ edgeOk_of_eq (g.adj_eq x y).symm) _ (searchOrder_nodup H rH.toList)
      hri hrn symPairs_ne hg] at hn
    exact absurd hn (by simp)
  · exact absurd (show Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E from
      ⟨f.toSubgraphOf.card_le, f.toSubgraphOf.E_le⟩) ‹_›

/-- `H` is an induced subgraph of `G` exactly when the search fails to find one. -/
theorem isEmpty_inducedSubgraphOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.InducedSubgraphOf G) ↔ findInducedSubgraph H G rH rG = none := by
  refine ⟨fun h ↦ ?_, isEmpty_inducedSubgraphOf_of_eq_none⟩
  rcases hm : findInducedSubgraph H G rH rG with _ | f
  · rfl
  · exact (h.false f).elim

end CGraph
