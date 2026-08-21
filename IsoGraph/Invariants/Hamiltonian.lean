import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import IsoGraph.Invariants.Connectivity

/-!
# Hamiltonicity

A graph is Hamiltonian if some cycle passes through every vertex.  Unlike the other invariants
here this one is a `Prop`, and unlike connectivity it has no cheap decision procedure: the
predicate is `SimpleGraph.IsHamiltonian` for `G.toSimple`, and deciding it by exhaustion is a
search over all `n!` orderings.  What this file provides instead is the two things that make it
usable: the invariance theorem, so that Hamiltonicity descends to `IsoGraph`, and *certificates*.

To prove a graph Hamiltonian, exhibit the cycle.  `isHamiltonian_of_cycleList` takes it as a list
of vertices, in the format of `IsoGraph/Invariants/Certificates.lean`, and asks that its length be
the order of the graph.  `isHamiltonian_of_cyclicNumbering` takes it as a numbering `f : ℕ → G.V`
of the vertices with `f i` adjacent to `f (i + 1 mod n)` — which is how the graphs of
`SmallGraphs/Defs/` are numbered in the first place, so for those the hypotheses are `n`
adjacency queries and nothing else.

To prove a graph *not* Hamiltonian there is no certificate, only necessary conditions: a
Hamiltonian graph is connected, and on three vertices or more it contains a cycle of length its
order, so its girth is at most that.
-/

set_option autoImplicit false

namespace CGraph

variable (G : CGraph)

/-! ## Hamiltonicity -/

/-- The graph has a cycle through every vertex.  Mathlib's convention, inherited here: the
one-vertex graph is Hamiltonian, having no cycle to speak of. -/
def IsHamiltonian : Prop := G.toSimple.IsHamiltonian

theorem isHamiltonian_of_iso {G H : CGraph} (i : G ≃cg H) (h : G.IsHamiltonian) :
    H.IsHamiltonian := by
  intro hcard
  have hGH : Fintype.card G.V = Fintype.card H.V := by
    rw [G.fintypeCard, H.fintypeCard]; exact i.card_eq
  obtain ⟨a, p, hp⟩ := h (by rw [hGH]; exact hcard)
  exact ⟨_, p.map (Iso.toSimpleIso i).toHom,
    hp.map _ (Iso.toSimpleIso i).toEquiv.bijective⟩

@[toIsoGraph]
theorem isHamiltonian_iff_of_iso {G H : CGraph} (i : G ≃cg H) :
    G.IsHamiltonian ↔ H.IsHamiltonian :=
  ⟨isHamiltonian_of_iso i, isHamiltonian_of_iso i.symm⟩

/-! ### What Hamiltonicity gives -/

theorem IsHamiltonian.isConnected {G : CGraph} (h : G.IsHamiltonian) : G.IsConnected :=
  SimpleGraph.IsHamiltonian.connected h

theorem IsHamiltonian.one_le_edgeConn {G : CGraph} (h : G.IsHamiltonian) (h2 : 2 ≤ G.card) :
    1 ≤ G.edgeConn :=
  (G.one_le_edgeConn_iff h2).2 h.isConnected

theorem IsHamiltonian.one_le_vertexConn {G : CGraph} (h : G.IsHamiltonian) (h2 : 2 ≤ G.card) :
    1 ≤ G.vertexConn :=
  (G.one_le_vertexConn_iff h2).2 h.isConnected

theorem not_isHamiltonian_of_not_isConnected (h : ¬ G.IsConnected) : ¬ G.IsHamiltonian :=
  fun hh ↦ h hh.isConnected

/-- A Hamiltonian cycle is a cycle: on three vertices or more, a Hamiltonian graph is not a
forest, and its girth is at most its order. -/
theorem IsHamiltonian.not_isAcyclic {G : CGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.card) :
    ¬ G.IsAcyclic := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  obtain ⟨a, p, hp⟩ := h (by omega)
  exact not_isAcyclic_of_isCycle hp.isCycle

/-- A graph with no cycle at all has no Hamiltonian cycle, once there are three vertices to run
one through. -/
theorem not_isHamiltonian_of_isAcyclic {G : CGraph} (h : G.IsAcyclic) (h3 : 3 ≤ G.card) :
    ¬ G.IsHamiltonian := fun hh ↦ hh.not_isAcyclic h3 h

theorem IsHamiltonian.girth_le_card {G : CGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.card) :
    G.girth ≤ G.card := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  obtain ⟨a, p, hp⟩ := h (by omega)
  have hlen : p.length = G.card := by rw [hp.length_eq, hFC]
  exact hlen ▸ girth_le_length hp.isCycle

/-- The one-vertex graph is Hamiltonian by convention, the empty graph is not. -/
theorem isHamiltonian_of_card_eq_one (h : G.card = 1) : G.IsHamiltonian := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  exact fun hc ↦ absurd (by omega) hc

theorem not_isHamiltonian_of_card_eq_zero (h : G.card = 0) : ¬ G.IsHamiltonian := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  have : IsEmpty G.V := Fintype.card_eq_zero_iff.1 (by omega)
  exact SimpleGraph.not_isHamiltonian_of_isEmpty

/-! ### Certificates -/

/-- **A cycle list through every vertex is a certificate of Hamiltonicity.**  The hypotheses are
those of `exists_cycle_of_cycleList`, with the length pinned to the order of the graph. -/
theorem isHamiltonian_of_cycleList {G : CGraph} (u : G.V) (vs : List G.V)
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u)
    (hlen : vs.length + 1 = G.card) : G.IsHamiltonian := by
  intro _
  obtain ⟨x, w, hw, hl⟩ := exists_cycle_of_cycleList u vs h2 hnd hch hcl
  refine ⟨x, w, SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.2 ⟨hw, ?_⟩⟩
  rw [hl, hlen, G.fintypeCard]

private theorem getLastD_map_range {α : Type} (f : ℕ → α) (m : ℕ) (hm : 0 < m) (u : α) :
    ((List.range m).map fun i ↦ f (i + 1)).getLastD u = f m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ, List.map_append]
  simp

/-- **A cyclic numbering of the vertices is a certificate of Hamiltonicity.**  Number the
vertices `f 0, f 1, …, f (n-1)`, all distinct, with `f i` adjacent to `f (i + 1 mod n)`: that is
the Hamiltonian cycle.  The hypotheses are `n` adjacency queries and an injectivity check, both
decidable, and neither of them a search. -/
theorem isHamiltonian_of_cyclicNumbering {G : CGraph} {n : ℕ} (f : ℕ → G.V) (h3 : 3 ≤ n)
    (hcard : G.card = n) (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hadj : ∀ i < n, G.Adj (f i) (f ((i + 1) % n)) = true) : G.IsHamiltonian := by
  have hlist : (List.range n).map f = f 0 :: (List.range (n - 1)).map fun i ↦ f (i + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  refine isHamiltonian_of_cycleList (f 0) ((List.range (n - 1)).map fun i ↦ f (i + 1))
    (by simp; omega) ?_ ?_ ?_ (by simp; omega)
  · rw [← hlist]
    refine List.Nodup.map_on (fun i hi j hj hij ↦ ?_) (List.nodup_range)
    rw [List.mem_range] at hi hj
    exact hinj i hi j hj hij
  · rw [← hlist, List.isChain_map, List.isChain_range]
    intro m hm
    have := hadj m (by omega)
    rwa [Nat.mod_eq_of_lt (by omega)] at this
  · rw [getLastD_map_range f (n - 1) (by omega)]
    have := hadj (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega, Nat.mod_self] at this

/-! ### The Hamiltonian small graphs -/

/-- The numeral of `vtx n i` is `i`, for `i` in range. -/
theorem vtx_val {n : ℕ} [NeZero n] {i : ℕ} (hi : i < n) : (vtx n i).1 = i :=
  Nat.mod_eq_of_lt hi

theorem isHamiltonian_complete {n : ℕ} (h3 : 3 ≤ n) : (complete n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_of_cyclicNumbering (n := n) (fun i ↦ vtx n i) h3 (card_complete n)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [complete_adj, decide_eq_true_eq]
    intro hc
    have := congrArg Fin.val hc
    rw [vtx_val hi, vtx_val (Nat.mod_lt _ (by omega))] at this
    exact ne_succ_mod h3 hi this

/-- **A graph given by an edge list containing the ring is Hamiltonian.**  The graphs of
`SmallGraphs/Defs/` are numbered so that `0 - 1 - ⋯ - (n-1) - 0` is a cycle whenever there is one
at all; for those the hypothesis is a lookup, not a search. -/
theorem isHamiltonian_ofEdges {n : ℕ} {es : List (ℕ × ℕ)} (h3 : 3 ≤ n)
    (hring : ∀ i < n, (i, (i + 1) % n) ∈ es) : (ofEdges n es).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_of_cyclicNumbering (n := n) (fun i ↦ vtx n i) h3 (card_ofEdges n es)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [ofEdges_adj_val, vtx_val hi, vtx_val (Nat.mod_lt _ (by omega))]
    exact ⟨ne_succ_mod h3 hi, Or.inl (hring i hi)⟩

/-- The LCF code lists the cycle it is read along: the ring edge `i - (i + 1 mod n)` is the first
of the two edges that vertex `i` contributes. -/
theorem mem_lcfEdges (ss : List ℤ) (r : ℕ) {i : ℕ} (hi : i < ss.length * r) :
    (i, (i + 1) % (ss.length * r)) ∈ lcfEdges ss r :=
  List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩

/-- **A graph given by an LCF code is Hamiltonian** — that is what an LCF code is: a Hamiltonian
cycle, with one chord hung at each vertex. -/
theorem isHamiltonian_lcfEdges {n : ℕ} (ss : List ℤ) (r : ℕ) (hn : ss.length * r = n)
    (h3 : 3 ≤ n) : (ofEdges n (lcfEdges ss r)).IsHamiltonian :=
  isHamiltonian_ofEdges h3 fun i hi ↦ by subst hn; exact mem_lcfEdges ss r hi

theorem isHamiltonian_cycle {n : ℕ} (h3 : 3 ≤ n) : (cycle n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_of_cyclicNumbering (n := n) (fun i ↦ vtx n i) h3 (card_cycle n)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [cycle_adj_val, vtx_val hi, vtx_val (Nat.mod_lt _ (by omega))]
    exact ⟨ne_succ_mod h3 hi, Or.inl rfl⟩

end CGraph

/-! ## Hamiltonicity on `IsoGraph`

Hamiltonicity is an isomorphism invariant, so it descends to the quotient; these are the
`IsoGraph`-level copies of the necessary conditions and of the two computed families. -/

namespace IsoGraph

variable (G : IsoGraph)

theorem IsHamiltonian.isConnected {G : IsoGraph} (h : G.IsHamiltonian) : G.IsConnected := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [isHamiltonian_mk] at h
  rw [isConnected_mk]
  exact h.isConnected

theorem not_isHamiltonian_of_not_isConnected (h : ¬ G.IsConnected) : ¬ G.IsHamiltonian :=
  fun hh ↦ h hh.isConnected

theorem IsHamiltonian.one_le_edgeConn {G : IsoGraph} (h : G.IsHamiltonian) (h2 : 2 ≤ G.V) :
    1 ≤ G.edgeConn := (G.one_le_edgeConn_iff h2).2 h.isConnected

theorem IsHamiltonian.one_le_vertexConn {G : IsoGraph} (h : G.IsHamiltonian) (h2 : 2 ≤ G.V) :
    1 ≤ G.vertexConn := (G.one_le_vertexConn_iff h2).2 h.isConnected

theorem IsHamiltonian.not_isAcyclic {G : IsoGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.V) :
    ¬ G.IsAcyclic := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [isHamiltonian_mk] at h
  rw [V_mk] at h3
  rw [isAcyclic_mk]
  exact h.not_isAcyclic h3

theorem IsHamiltonian.girth_le_V {G : IsoGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.V) :
    G.girth ≤ G.V := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [isHamiltonian_mk] at h
  rw [V_mk] at h3 ⊢
  rw [girth_mk]
  exact h.girth_le_card h3

theorem not_isHamiltonian_of_isAcyclic {G : IsoGraph} (h : G.IsAcyclic) (h3 : 3 ≤ G.V) :
    ¬ G.IsHamiltonian := fun hh ↦ hh.not_isAcyclic h3 h

theorem isHamiltonian_complete {n : ℕ} (h3 : 3 ≤ n) : (complete n).IsHamiltonian := by
  rw [complete_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_complete h3

theorem isHamiltonian_cycle {n : ℕ} (h3 : 3 ≤ n) : (cycle n).IsHamiltonian := by
  rw [cycle_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_cycle h3

end IsoGraph
