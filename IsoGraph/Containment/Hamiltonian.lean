import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Invariants.Hamiltonian

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Hamiltonicity as a containment

`Invariants/Hamiltonian.lean` gives Hamiltonicity certificates in one direction only: a spanning
cycle, written out, proves a graph Hamiltonian, and nothing there proves a graph *not*
Hamiltonian except the necessary conditions — connectedness, minimum degree two, girth, the
independence bound.  Those refute the easy cases and say nothing about the hard ones.

The observation that closes the gap is that a Hamiltonian cycle is a *spanning cycle subgraph*:

```
G.IsHamiltonian ↔ Nonempty ((cycle G.card).SubgraphOf G)
```

for `G` on three vertices or more.  The right-hand side is exactly what the subgraph search of
`Containment/Algorithms/Subgraph.lean` decides, so Hamiltonicity comes with a decision procedure
after all — one that is complete, and whose negative answer `native_decide` will check.  It is a
search over the `n!` orderings in the worst case, pruned by the adjacency constraints, and on the
graphs of `SmallGraphs/` it is fast on the Hamiltonian ones and slow on the non-Hamiltonian ones,
which is the usual asymmetry.

Both halves are stated: `isHamiltonian_of_nonempty_subgraphOf_cycle` for a found cycle and
`not_isHamiltonian_of_findSubgraph_cycle_eq_none` for an exhausted search.  The gallery's
refutations are in `SmallGraphs/Substructure.lean`, with the other exhausted searches.
-/

set_option autoImplicit false

namespace CGraph

/-- **Hamiltonicity is a spanning cycle.**  A Hamiltonian cycle visits every vertex once and
closes up, which is an injection of `cycle n` into `G` preserving adjacency with `n = G.card`;
conversely such an injection is a bijection, and reading `G` along it gives the cycle back.

Below three vertices the two sides part company: `cycle 0`, `cycle 1` and `cycle 2` are all
edgeless, so they embed in anything of the right size, while `IsHamiltonian` holds on one vertex
and fails on none and on two. -/
theorem isHamiltonian_iff_nonempty_subgraphOf_cycle {G : CGraph} (h3 : 3 ≤ G.card) :
    G.IsHamiltonian ↔ Nonempty ((cycle G.card).SubgraphOf G) := by
  have : NeZero G.card := ⟨by omega⟩
  constructor
  · intro h
    obtain ⟨f, hinj, hadj⟩ := h.exists_cyclicNumbering h3
    refine ⟨⟨fun i ↦ f i.1, fun i j hij ↦ Fin.ext (hinj i.1 i.2 j.1 j.2 hij), fun x y hxy ↦ ?_⟩⟩
    rw [cycle_adj_val] at hxy
    obtain ⟨-, hs | hs⟩ := hxy
    · rw [← hs]; exact hadj x.1 x.2
    · rw [← G.symm]; rw [← hs]; exact hadj y.1 y.2
  · rintro ⟨φ⟩
    refine isHamiltonian_of_cyclicNumbering (n := G.card) (fun i ↦ φ (vtx G.card i)) h3 rfl
      (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
    · have h1 : (vtx G.card i : Fin G.card) = vtx G.card j := φ.injective hij
      rw [Fin.ext_iff, vtx_val hi, vtx_val hj] at h1
      exact h1
    · refine φ.map_adj ?_
      rw [cycle_adj_val, vtx_val hi, vtx_val (Nat.mod_lt _ (by omega) : (i + 1) % G.card < G.card)]
      rcases Nat.lt_or_ge (i + 1) G.card with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · have : i + 1 = G.card := by omega
        rw [this, Nat.mod_self]
        omega

/-- A spanning cycle subgraph is a Hamiltonian cycle. -/
theorem isHamiltonian_of_nonempty_subgraphOf_cycle {G : CGraph} {n : ℕ} (h3 : 3 ≤ n)
    (hcard : G.card = n) (h : Nonempty ((cycle n).SubgraphOf G)) : G.IsHamiltonian := by
  subst hcard
  exact (isHamiltonian_iff_nonempty_subgraphOf_cycle h3).2 h

/-- No spanning cycle, no Hamiltonian cycle. -/
theorem not_isHamiltonian_of_isEmpty_subgraphOf_cycle {G : CGraph} {n : ℕ} (h3 : 3 ≤ n)
    (hcard : G.card = n) (h : IsEmpty ((cycle n).SubgraphOf G)) : ¬ G.IsHamiltonian := by
  subst hcard
  exact fun hh ↦ h.false ((isHamiltonian_iff_nonempty_subgraphOf_cycle h3).1 hh).some

/-- **An exhausted search for a spanning cycle refutes Hamiltonicity.**  The refutation
`Invariants/Hamiltonian.lean` cannot give: `findSubgraph` is complete, so `none` means there is no
spanning cycle to find, and `native_decide` on that equation is the certificate. -/
theorem not_isHamiltonian_of_findSubgraph_cycle_eq_none {G : CGraph} {n : ℕ} (h3 : 3 ≤ n)
    (hcard : G.card = n) {rH : Backtrack.Roster (cycle n).V} {rG : Backtrack.Roster G.V}
    (h : findSubgraph (cycle n) G rH rG = none) : ¬ G.IsHamiltonian :=
  not_isHamiltonian_of_isEmpty_subgraphOf_cycle h3 hcard (isEmpty_subgraphOf_of_eq_none h)

end CGraph

/-! ## The spanning cycle on `IsoGraph` -/

namespace IsoGraph

/-- **Hamiltonicity is a spanning cycle**, on the quotient: `G` is Hamiltonian exactly when the
cycle on `G.V` vertices is a subgraph of it.  Being a subgraph is `≤ₛ`, the first of the
containment orders of `IsoGraph/Containment/Defs.lean`, so this reads the invariant off the
order. -/
theorem isHamiltonian_iff_isSubgraphOf_cycle {G : IsoGraph} (h3 : 3 ≤ G.V) :
    G.IsHamiltonian ↔ cycle G.V ≤ₛ G := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [V_mk] at h3 ⊢
  rw [isHamiltonian_mk, cycle_def, isSubgraphOf_mk]
  exact CGraph.isHamiltonian_iff_nonempty_subgraphOf_cycle h3

/-- A graph with no spanning cycle is not Hamiltonian. -/
theorem not_isHamiltonian_of_not_isSubgraphOf_cycle {G : IsoGraph} (h3 : 3 ≤ G.V)
    (h : ¬ (cycle G.V ≤ₛ G)) : ¬ G.IsHamiltonian :=
  fun hh ↦ h ((isHamiltonian_iff_isSubgraphOf_cycle h3).1 hh)

/-- A spanning cycle is a Hamiltonian cycle. -/
theorem IsSubgraphOf.isHamiltonian {G : IsoGraph} (h3 : 3 ≤ G.V) (h : cycle G.V ≤ₛ G) :
    G.IsHamiltonian :=
  (isHamiltonian_iff_isSubgraphOf_cycle h3).2 h

end IsoGraph
