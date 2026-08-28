import IsoGraph.Containment.Algorithms.Embedding

/-!
# Deciding the subgraph relation

`CGraph.findSubgraph` searches for a copy of `H` inside `G` — not necessarily an induced one — and
returns it if there is one; `CGraph.isEmpty_subgraphOf_of_eq_none` is the other half of the
answer.

The search is `Algorithms/Embedding.lean` run with `ind := false`, the same one
`Algorithms/InducedSubgraph.lean` runs with `ind := true`, and everything interesting about it is
documented there.  Only one test differs — `CGraph.edgeOk`, which for a subgraph asks that an edge
of `H` go to an edge of `G` and says nothing about a non-edge.

That one difference changes which instances are hard.  A pattern with no edges is an induced
subgraph of `G` only if `G` has an independent set that big, which is the hard part of the induced
problem; as an ordinary subgraph it is free, and the search finds it without backtracking once.
Going the other way, a clique is an induced subgraph exactly when it is a subgraph, and both are
the clique problem.  What the subgraph search is good at is a sparse pattern in a sparse host:
every vertex after the first is pinned to a neighbourhood, and the consistency test — weaker here
than in the induced case, since only edges of `H` constrain anything — still cuts most of what is
left.

It is also what `CGraph.preAdj` and `CGraph.preOther` are for.  Lean evaluates arguments before it
calls, so passing `p.nbrs.contains q.2` to `edgeOk` scans the candidate's neighbour list for every
already-placed vertex, adjacent to `a` or not.  Sorting the placed vertices by whether they are
neighbours of `a` — a question about the pattern, so it is asked once at the node and not once per
candidate — leaves the other half of `candKeep` with nothing to look up when `ind` is false, which
on a sparse pattern is nearly all of the pairs; on a benchmark that runs one node of the search
and nothing else that is worth about 1.4×.  A non-induced search need not even sort.  Injectivity
is all it asks of an already-placed vertex and it asks the same of every one of them, so
`preOther` hands over all the images and walks the assignment once instead of twice, which is
another 1.15× on the hardest case below.

## What it costs

Times on one shared machine, so read them as orders of magnitude.  Girth settles most of the small
cases outright: `C₆ ⊆ McGee`, `K₄ ⊆ McGee`, `K₃,₃ ⊆ Heawood` and `Petersen ⊆ McGee` all come back
empty in a millisecond or three, and `C₇ ⊆ McGee`, `C₈ ⊆ grid 5×5`, `grid 3×3 ⊆ grid 5×5` are
found about as fast.  Finding a Hamiltonian cycle is barely dearer: `C₂₄ ⊆ McGee`,
`grid 5×5 ⊆ grid 5×5` and `C₂₄ ⊆ grid 5×5` in 2 ms to 6 ms.  Proving there is none is the expensive
direction — `C₂₅ ⊆ grid 5×5`, and the 5×5 grid has no Hamiltonian cycle, the two colour classes
being 13 and 12 — and that is about 10 s of exhaustive search.  Nothing here knows about bipartite
parity, so that last one is the honest shape of the worst case: the search finds what is there
quickly and works hard to rule out what is not.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {H G : CGraph} {rank : G.V → ℕ} {n : ℕ} {pairs : List (H.V × H.V)}

/-- The subgraph a complete, consistent assignment describes. -/
def SubgraphOf.ofAsg (r : List (H.V × G.V)) (hcov : ∀ x : H.V, x ∈ r.map Prod.fst)
    (hg : goalAsg H G false rank n pairs r = true) : H.SubgraphOf G where
  toFun := asgFun H G r hcov
  injective' := asgFun_injective (validAsg_of_goalAsg hg)
  map_adj' _ _ h := asgFun_map_adj (validAsg_of_goalAsg hg) h

/-- **Relabelling an embedding along an automorphism of the pattern.** -/
def SubgraphOf.reindex (f : H.SubgraphOf G) {σ : H.V → H.V} (hinj : Function.Injective σ)
    (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) : H.SubgraphOf G where
  toFun x := f (σ x)
  injective' := f.injective.comp hinj
  map_adj' _ _ h := f.map_adj (by rw [hadj]; exact h)

/-- What `exists_sorted_pairs` needs of the subgraph relation: it is closed under relabelling by
an automorphism of the pattern. -/
theorem SubgraphOf.exists_reindex (f : H.SubgraphOf G) {σ : H.V → H.V}
    (hinj : Function.Injective σ) (hadj : ∀ x y, H.Adj (σ x) (σ y) = H.Adj x y) :
    ∃ g : H.SubgraphOf G, ∀ x, g x = f (σ x) :=
  ⟨f.reindex hinj hadj, fun _ ↦ rfl⟩

/-- A subgraph passes the non-induced edge test: what it preserves is exactly what is asked. -/
theorem SubgraphOf.edgeOk_map (f : H.SubgraphOf G) (x y : H.V) :
    edgeOk false (H.Adj x y) (G.Adj (f x) (f y)) = true := by
  cases hxy : H.Adj x y with
  | false => simp [edgeOk]
  | true => simpa [edgeOk] using f.map_adj (show H.Adj x y = true from hxy)

variable (H G)

/-- **Is `H` a subgraph of `G`?**  Returns a witness if so — not necessarily an induced one.  See
`isEmpty_subgraphOf_of_eq_none` for the other half of the answer. -/
def findSubgraph (rH : Roster H.V) (rG : Roster G.V) : Option (H.SubgraphOf G) :=
  Option.pmap (p := fun r ↦ (∀ x : H.V, x ∈ r.map Prod.fst) ∧
      goalAsg H G false (hostRank G rG) rG.toList.length
        (symPairs H (searchOrder H rH.toList)) r = true)
    (fun r hr ↦ SubgraphOf.ofAsg r hr.1 hr.2) (searchAsg H G false rH rG)
    (fun _ hr ↦ ⟨searchAsg_cov hr, searchAsg_goal hr⟩)

theorem findSubgraph_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findSubgraph H G rH rG = none ↔ searchAsg H G false rH rG = none :=
  Option.pmap_eq_none_iff

/-! ## Completeness -/

variable {H G}

/-- A vertex of a subgraph has no more neighbours than its image. -/
theorem degree_le_of_subgraphOf (f : H.SubgraphOf G) (x : H.V) :
    H.toSimple.degree x ≤ G.toSimple.degree (f x) :=
  degree_le_of_map_adj f.injective (fun h ↦ f.map_adj h) x

/-- **Completeness**: when the search comes back empty, `H` is not a subgraph of `G`. -/
theorem isEmpty_subgraphOf_of_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findSubgraph H G rH rG = none) : IsEmpty (H.SubgraphOf G) := by
  rw [findSubgraph_eq_none_iff, searchAsg] at h
  refine ⟨fun f ↦ ?_⟩
  split at h
  · -- the embedding is first relabelled to one the symmetry test accepts
    obtain ⟨g, hg⟩ := exists_sorted_pairs (fun (f : H.SubgraphOf G) ↦ ⇑f)
      (fun f {_σ} hinj hadj ↦ f.exists_reindex hinj hadj) (hs := searchOrder H rH.toList)
      (hostRank G rG) (mem_searchOrder H rH.mem_toList) f
    have hsol : ((searchOrder H rH.toList).map fun x ↦ (x, g x)).map Prod.fst =
        searchOrder H rH.toList := by
      simp [Function.comp_def]
    have hri : Function.Injective (hostRank G rG) := fun u v huv ↦
      (List.idxOf_inj (rG.mem_toList u)).mp huv
    have hrn : ∀ v, hostRank G rG v < rG.toList.length := fun v ↦
      List.idxOf_lt_length_of_mem (rG.mem_toList v)
    have hn := Backtrack.dfs_eq_none_keys
      (mem_candList H G false rG.mem_toList (rank := hostRank G rG) (fun _ ↦ rfl) _ _
        (fun _ ↦ rfl) (fun _ ↦ rfl)
        (keys := (searchOrder H rH.toList).reverse)
        (fun x ↦ List.mem_reverse.mpr (mem_searchOrder H rH.mem_toList x))
        (List.nodup_reverse.mpr (searchOrder_nodup H rH.toList))) h hsol (by simp)
    rw [List.append_nil, goalAsg_of_emb false _ _ _ g.injective
      (fun x y _ ↦ g.edgeOk_map x y) _ (searchOrder_nodup H rH.toList)
      hri hrn symPairs_ne hg] at hn
    exact absurd hn (by simp)
  · exact absurd (show FinEnum.card H.V ≤ FinEnum.card G.V ∧ H.E ≤ G.E from
      ⟨f.card_le, f.E_le⟩) ‹_›

/-- `H` is a subgraph of `G` exactly when the search fails to find one. -/
theorem isEmpty_subgraphOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.SubgraphOf G) ↔ findSubgraph H G rH rG = none := by
  refine ⟨fun h ↦ ?_, isEmpty_subgraphOf_of_eq_none⟩
  rcases hm : findSubgraph H G rH rG with _ | f
  · rfl
  · exact (h.false f).elim

end CGraph
