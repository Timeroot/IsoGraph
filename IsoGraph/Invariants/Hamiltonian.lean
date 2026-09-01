import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import IsoGraph.Invariants.Connectivity

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

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

To prove a graph *not* Hamiltonian there is no certificate here, only necessary conditions: a
Hamiltonian graph is connected, its minimum degree is at least two, its independence number is at
most half its order, and on three vertices or more it contains a cycle of length its order, so its
girth is at most that.  A genuine refutation — an exhaustive search for the spanning cycle — needs
the machinery of `IsoGraph/Containment/`, and is in `Containment/Hamiltonian.lean`.
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
    hp.map (Iso.toSimpleIso i).toEquiv.bijective⟩

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

/-- A separator's two-colouring is constant along any walk that avoids the separator. -/
private theorem const_on_support {G : CGraph} {f : G.V → Bool} {s : Finset G.V}
    (hf : ∀ u w : G.V, u ∉ s → w ∉ s → G.Adj u w = true → f u = f w)
    {a b : G.V} (p : G.toSimple.Walk a b) (hp : ∀ x ∈ p.support, x ∉ s) :
    ∀ x ∈ p.support, f x = f a := by
  induction p with
  | nil => intro x hx; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx; rw [hx]
  | @cons u w b h q ih =>
      intro x hx
      have hu : u ∉ s := hp u (by simp)
      have hw : w ∉ s := hp w (by simp)
      have huw : f u = f w := hf u w hu hw ((toSimple_adj _ _ _).1 h)
      rcases List.mem_cons.1 (by simpa using hx) with hxu | hx'
      · rw [hxu]
      · rw [ih (fun y hy ↦ hp y (by simp [hy])) x hx', huw]

/-- **A Hamiltonian graph has no cut vertex.**  Rotate the spanning cycle to start at `v`, then
drop `v` from both of its ends: what is left is a walk through every *other* vertex which never
touches `v`.  A separator `{v}` would two-colour that walk without ever giving two adjacent
vertices different colours, so the walk is monochrome — and yet it contains a vertex of each
colour. -/
theorem IsHamiltonian.not_isSeparator_singleton {G : CGraph} (h : G.IsHamiltonian)
    (h3 : 3 ≤ G.card) (v : G.V) : ¬ G.IsSeparator {v} := by
  rintro ⟨f, ⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩, hconst⟩
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  obtain ⟨u, c₀, hc₀⟩ := h (by omega)
  have hv : v ∈ c₀.support := hc₀.mem_support v
  set c := c₀.rotate v hv with hcdef
  have hcyc : c.IsCycle := hc₀.isCycle.rotate hv
  have hcham : c.IsHamiltonianCycle := by
    rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
    refine ⟨hcyc, fun x ↦ ?_⟩
    rw [(SimpleGraph.Walk.support_rotate c₀ v hv).perm.count_eq]
    exact (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.1 hc₀).2 x
  have hlen : 3 ≤ c.length := hcyc.three_le_length
  have hnil : ¬ c.Nil := by rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega
  have hlt : c.tail.length + 1 = c.length := SimpleGraph.Walk.length_tail_add_one hnil
  have hnil2 : ¬ c.tail.Nil := by rw [← SimpleGraph.Walk.length_eq_zero_iff]; omega
  have hnil3 : ¬ c.tail.reverse.Nil := by
    rw [← SimpleGraph.Walk.length_eq_zero_iff, SimpleGraph.Walk.length_reverse]
    omega
  have hcount : ∀ x, c.tail.reverse.support.count x = 1 := by
    intro x
    rw [SimpleGraph.Walk.support_reverse, List.count_reverse]
    exact hcham.isHamiltonian_tail x
  have hsupp : v :: c.tail.reverse.tail.support = c.tail.reverse.support :=
    SimpleGraph.Walk.cons_support_tail hnil3
  have hvnot : v ∉ c.tail.reverse.tail.support := by
    have h1 := hcount v
    rw [← hsupp, List.count_cons_self] at h1
    exact List.count_eq_zero.1 (by omega)
  have hmem : ∀ x : G.V, x ≠ v → x ∈ c.tail.reverse.tail.support := by
    intro x hx
    have h1 := hcount x
    rw [← hsupp] at h1
    by_contra hxx
    simp [List.count_cons, List.count_eq_zero.2 hxx] at h1
    exact hx h1.symm
  have hnots : ∀ x ∈ c.tail.reverse.tail.support, x ∉ ({v} : Finset G.V) := by
    intro x hx hmemv
    exact hvnot ((Finset.mem_singleton.1 hmemv) ▸ hx)
  have hall := const_on_support hconst c.tail.reverse.tail hnots
  have hA := hall a (hmem a fun hh ↦ ha (Finset.mem_singleton.2 hh))
  have hB := hall b (hmem b fun hh ↦ hb (Finset.mem_singleton.2 hh))
  rw [hfa] at hA
  rw [hfb] at hB
  exact Bool.noConfusion (hA.trans hB.symm)

/-- **A Hamiltonian graph on three vertices or more is 2-connected.**  Nothing smaller than a pair
separates it: the empty set does not, since it is connected, and no single vertex does either. -/
@[toIsoGraph]
theorem IsHamiltonian.two_le_vertexConn {G : CGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.card) :
    2 ≤ G.vertexConn := by
  refine G.le_vertexConn_of_forall_card_lt (by omega) fun s hs hsep ↦ ?_
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · exact G.not_isConnected_of_isSeparator_empty hsep h.isConnected
  · have hone : s.card = 1 := by have := Finset.card_pos.2 hne; omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hone
    exact h.not_isSeparator_singleton h3 v hsep

/-- **A Hamiltonian graph on three vertices or more is 2-edge-connected**, by Whitney's `κ ≤ λ`. -/
@[toIsoGraph]
theorem IsHamiltonian.two_le_edgeConn {G : CGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.card) :
    2 ≤ G.edgeConn :=
  le_trans (h.two_le_vertexConn h3) G.vertexConn_le_edgeConn

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

/-- **A Hamiltonian graph carries a cyclic numbering of its vertices**: the converse of
`isHamiltonian_of_cyclicNumbering`, and the form in which the spanning cycle is easiest to use.
The numbering is total on `ℕ`, with the two conditions asked only below `G.card`; outside that
range it is whatever `Walk.getVert` returns, which is the last vertex of the cycle. -/
theorem IsHamiltonian.exists_cyclicNumbering {G : CGraph} (h : G.IsHamiltonian) (h3 : 3 ≤ G.card) :
    ∃ f : ℕ → G.V, (∀ i < G.card, ∀ j < G.card, f i = f j → i = j) ∧
      ∀ i < G.card, G.Adj (f i) (f ((i + 1) % G.card)) = true := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  obtain ⟨a, c, hc⟩ := h (by omega)
  have hlen : c.length = G.card := by rw [hc.length_eq, hFC]
  refine ⟨c.getVert, fun i hi j hj hij ↦ ?_, fun i hi ↦ ?_⟩
  · exact hc.isCycle.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
  · rcases Nat.lt_or_ge (i + 1) G.card with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      exact (G.toSimple_adj _ _).1 (c.adj_getVert_succ (by omega))
    · have hi1 : i + 1 = G.card := by omega
      have hadj := c.adj_getVert_succ (i := i) (by omega)
      rw [hi1, ← hlen, c.getVert_length] at hadj
      rw [hi1, Nat.mod_self, c.getVert_zero]
      exact (G.toSimple_adj _ _).1 hadj

/-- **A Hamiltonian graph has no independent set larger than half of it**, `2α ≤ n`.  Walk the
spanning cycle: an independent set occupies a set `T` of positions, and because no two consecutive
positions are both in it, `T` and its shift by one are disjoint subsets of the same size — two
disjoint copies of `α` inside `n` positions.

Contrapositively this refutes Hamiltonicity from a single large independent set, which is the
usual way to see that an unbalanced complete multipartite graph, or a star, is not Hamiltonian. -/
@[toIsoGraph IsHamiltonian.two_mul_indepNum_le_V]
theorem IsHamiltonian.two_mul_indepNum_le_card {G : CGraph} (h : G.IsHamiltonian)
    (h3 : 3 ≤ G.card) : 2 * G.indepNum ≤ G.card := by
  classical
  obtain ⟨f, hinj, hadj⟩ := h.exists_cyclicNumbering h3
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  have hinjOn : Set.InjOn f ↑(Finset.range G.card) := fun i hi j hj hij ↦
    hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij
  -- `f` hits every vertex: it is injective on `n` positions and there are `n` vertices.
  have hsurj : ∀ v : G.V, ∃ i, i < G.card ∧ f i = v := by
    have huniv : (Finset.range G.card).image f = Finset.univ :=
      Finset.eq_univ_of_card _ (by
        rw [Finset.card_image_of_injOn hinjOn, Finset.card_range, hFC])
    intro v
    obtain ⟨i, hi, hfi⟩ := Finset.mem_image.1 (huniv ▸ Finset.mem_univ v)
    exact ⟨i, Finset.mem_range.1 hi, hfi⟩
  have key : ∀ s : Finset G.V, G.toSimple.IsIndepSet (s : Set G.V) → 2 * s.card ≤ G.card := by
    intro s hs
    set T : Finset ℕ := (Finset.range G.card).filter fun i ↦ f i ∈ s with hTdef
    have hTlt : ∀ i ∈ T, i < G.card := fun i hi ↦ Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hTmem : ∀ i ∈ T, f i ∈ s := fun i hi ↦ (Finset.mem_filter.1 hi).2
    have hcardT : T.card = s.card :=
      Finset.card_bij (fun i _ ↦ f i) hTmem
        (fun i hi j hj hij ↦ hinj i (hTlt i hi) j (hTlt j hj) hij) fun v hv ↦ by
          obtain ⟨i, hi, rfl⟩ := hsurj v
          exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hv⟩, rfl⟩
    have hginj : ∀ i ∈ T, ∀ j ∈ T, (i + 1) % G.card = (j + 1) % G.card → i = j := by
      intro i hi j hj hij
      have h1 := hTlt i hi
      have h2 := hTlt j hj
      rcases Nat.lt_or_ge (i + 1) G.card with hl1 | hl1 <;>
        rcases Nat.lt_or_ge (j + 1) G.card with hl2 | hl2
      · rwa [Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hl2, Nat.add_right_cancel_iff] at hij
      · rw [Nat.mod_eq_of_lt hl1, show j + 1 = G.card by omega, Nat.mod_self] at hij; omega
      · rw [Nat.mod_eq_of_lt hl2, show i + 1 = G.card by omega, Nat.mod_self] at hij; omega
      · omega
    -- No position and its successor are both in `T`: those two vertices are adjacent.
    have hdisj : Disjoint T (T.image fun i ↦ (i + 1) % G.card) := by
      rw [Finset.disjoint_right]
      intro k hk hkT
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
      have hA : G.toSimple.Adj (f j) (f ((j + 1) % G.card)) :=
        (G.toSimple_adj _ _).2 (hadj j (hTlt j hj))
      exact hs (Finset.mem_coe.2 (hTmem j hj)) (Finset.mem_coe.2 (hTmem _ hkT)) hA.ne hA
    have himgcard : (T.image fun i ↦ (i + 1) % G.card).card = T.card :=
      Finset.card_image_of_injOn fun i hi j hj hij ↦
        hginj i (Finset.mem_coe.1 hi) j (Finset.mem_coe.1 hj) hij
    have hsub : T ∪ (T.image fun i ↦ (i + 1) % G.card) ⊆ Finset.range G.card := by
      intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · exact Finset.mem_range.2 (hTlt k hk)
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_range.2 (Nat.mod_lt _ (by omega))
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, himgcard, hcardT, Finset.card_range] at hcount
    omega
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  show 2 * G.toSimple.indepNum ≤ G.card
  rw [← hcard]
  exact key s hs

/-- A graph with an independent set on more than half its vertices is not Hamiltonian. -/
theorem not_isHamiltonian_of_card_lt_two_mul_indepNum {G : CGraph} (h3 : 3 ≤ G.card)
    (h : G.card < 2 * G.indepNum) : ¬ G.IsHamiltonian :=
  fun hH ↦ absurd (hH.two_mul_indepNum_le_card h3) (by omega)

/-- **A Hamiltonian graph has minimum degree at least two.**  Every vertex lies on the spanning
cycle, and there it has a successor and a predecessor, which a cycle keeps apart. -/
theorem IsHamiltonian.two_le_minDeg {G : CGraph} (h : G.IsHamiltonian) (h2 : 2 ≤ G.card) :
    2 ≤ G.minDeg := by
  have hnt : Nontrivial G.V := Fintype.one_lt_card_iff_nontrivial.1 (by
    rw [G.fintypeCard]; exact h2)
  have hne : Nonempty G.V := hnt.to_nonempty
  show 2 ≤ G.toSimple.minDegree
  refine G.toSimple.le_minDegree_of_forall_le_degree 2 fun v ↦ ?_
  obtain ⟨p, hp⟩ := SimpleGraph.IsHamiltonian.exists_isHamiltonianCycle h v
  have hnil := hp.isCycle.not_nil
  have hsnd : p.snd ∈ G.toSimple.neighborFinset v :=
    SimpleGraph.mem_neighborFinset _ _ _ |>.2 (p.adj_snd hnil)
  have hpen : p.penultimate ∈ G.toSimple.neighborFinset v :=
    SimpleGraph.mem_neighborFinset _ _ _ |>.2 (p.adj_penultimate hnil).symm
  calc 2 = ({p.snd, p.penultimate} : Finset G.V).card :=
        (Finset.card_pair hp.isCycle.snd_ne_penultimate).symm
    _ ≤ (G.toSimple.neighborFinset v).card :=
        Finset.card_le_card (by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hsnd
          · rw [Finset.mem_singleton] at hx; exact hx ▸ hpen)
    _ = G.toSimple.degree v := rfl

/-- A graph with a leaf, or with an isolated vertex, is not Hamiltonian. -/
theorem not_isHamiltonian_of_minDeg_lt_two {G : CGraph} (h2 : 2 ≤ G.card) (h : G.minDeg < 2) :
    ¬ G.IsHamiltonian :=
  fun hH ↦ absurd (hH.two_le_minDeg h2) (by omega)

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

/-- The numeral of `vtx n i` is `i`, for `i` in range. -/
theorem vtx_val {n : ℕ} [NeZero n] {i : ℕ} (hi : i < n) : (vtx n i).1 = i :=
  Nat.mod_eq_of_lt hi

/-! ### Certificates from a Hamiltonian path

Two operations turn a *path* through every vertex into a *cycle* through every vertex: coning,
which adds an apex adjacent to both ends, and prisming, which lays a second copy of the graph
alongside and crosses over at the ends.  Both certificates below take the path in the same shape
as `isHamiltonian_of_cyclicNumbering` takes its cycle — a numbering `g : ℕ → X.V` of the vertices
with `g i` adjacent to `g (i + 1)` — minus the wrap-around, which is exactly what the operation
supplies. -/

/-- **Coning over a Hamiltonian path gives a Hamiltonian graph.**  Number the vertices of `X`
along the path; `complete 1 ∇g X` runs the path and comes back through the apex. -/
theorem isHamiltonian_join_complete_one {X : CGraph} {n : ℕ} (g : ℕ → X.V) (h2 : 2 ≤ n)
    (hcard : X.card = n) (hinj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    (hadj : ∀ i, i + 1 < n → X.Adj (g i) (g (i + 1)) = true) :
    (complete 1 ∇g X).IsHamiltonian := by
  refine isHamiltonian_of_cyclicNumbering (n := n + 1)
    (fun i ↦ if i = 0 then Sum.inl (vtx 1 0) else Sum.inr (g (i - 1))) (by omega)
    (by show FinEnum.card (complete 1 ∇g X).V = n + 1
        rw [card_join, show FinEnum.card X.V = n from hcard,
          show FinEnum.card (complete 1).V = 1 from rfl, Nat.add_comm]) ?_ ?_
  · intro i hi j hj hij
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · simp [Nat.ne_of_gt hj0] at hij
    · simp [Nat.ne_of_gt hi0] at hij
    · simp only [Nat.ne_of_gt hi0, Nat.ne_of_gt hj0, if_false] at hij
      have := hinj (i - 1) (by omega) (j - 1) (by omega) (Sum.inr_injective hij)
      omega
  · intro i hi
    rcases Nat.lt_or_ge (i + 1) (n + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [if_pos rfl, if_neg (by omega), join_adj_inl_inr]
      · rw [if_neg (by omega), if_neg (by omega), join_adj_inr_inr,
          show i + 1 - 1 = (i - 1) + 1 by omega]
        exact hadj (i - 1) (by omega)
    · have hin : i = n := by omega
      subst hin
      rw [Nat.mod_self, if_pos rfl, if_neg (by omega), join_adj_inr_inl]

/-- One step along the `X` factor of `X □g complete 2`, staying in the same copy. -/
private theorem adj_prod_left {X : CGraph} {a b : X.V} (c : (complete 2).V)
    (h : X.Adj a b = true) : (X □g complete 2).Adj (a, c) (b, c) = true := by
  rw [cartesianProduct_adj]
  simp [h]

/-- One step across the rung of `X □g complete 2`, staying over the same vertex of `X`. -/
private theorem adj_prod_right {X : CGraph} (a : X.V) {c d : (complete 2).V}
    (h : (complete 2).Adj c d = true) : (X □g complete 2).Adj (a, c) (a, d) = true := by
  rw [cartesianProduct_adj]
  show (decide (a = a) && (complete 2).Adj c d || X.Adj a a && decide (c = d)) = true
  rw [h, decide_eq_true (rfl : a = a), Bool.and_true, Bool.true_or]

/-- **A graph with a Hamiltonian path gives a Hamiltonian prism.**  Run the path along one copy,
cross the rung at the far end, run it back along the other, and cross back. -/
theorem isHamiltonian_cartesianProduct_complete_two {X : CGraph} {n : ℕ} (g : ℕ → X.V)
    (h2 : 2 ≤ n) (hcard : X.card = n) (hinj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    (hadj : ∀ i, i + 1 < n → X.Adj (g i) (g (i + 1)) = true) :
    (X □g complete 2).IsHamiltonian := by
  refine isHamiltonian_of_cyclicNumbering (n := 2 * n)
    (fun i ↦ if i < n then (g i, vtx 2 0) else (g (2 * n - 1 - i), vtx 2 1)) (by omega)
    (by show FinEnum.card (X □g complete 2).V = 2 * n
        rw [card_cartesianProduct, show FinEnum.card X.V = n from hcard,
          show FinEnum.card (complete 2).V = 2 from rfl, Nat.mul_comm]) ?_ ?_
  · intro i hi j hj hij
    have hne : (vtx 2 0) ≠ (vtx 2 1) := by decide
    by_cases hin : i < n <;> by_cases hjn : j < n
    · rw [if_pos hin, if_pos hjn, Prod.mk.injEq] at hij
      exact hinj i hin j hjn hij.1
    · rw [if_pos hin, if_neg hjn, Prod.mk.injEq] at hij
      exact absurd hij.2 hne
    · rw [if_neg hin, if_pos hjn, Prod.mk.injEq] at hij
      exact absurd hij.2.symm hne
    · rw [if_neg hin, if_neg hjn, Prod.mk.injEq] at hij
      have := hinj (2 * n - 1 - i) (by omega) (2 * n - 1 - j) (by omega) hij.1
      omega
  · intro i hi
    have hrung : (complete 2).Adj (vtx 2 0) (vtx 2 1) = true := by decide
    have hrung' : (complete 2).Adj (vtx 2 1) (vtx 2 0) = true := by decide
    rcases Nat.lt_or_ge (i + 1) (2 * n) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      rcases Nat.lt_or_ge (i + 1) n with h1 | h1
      · rw [if_pos (by omega), if_pos h1]
        exact adj_prod_left _ (hadj i h1)
      · rcases Nat.eq_or_lt_of_le h1 with heq | hgt
        · rw [if_pos (by omega), if_neg (by omega), show 2 * n - 1 - (i + 1) = i by omega]
          exact adj_prod_right _ hrung
        · rw [if_neg (by omega), if_neg (by omega),
            show 2 * n - 1 - i = (2 * n - 1 - (i + 1)) + 1 by omega]
          exact adj_prod_left _ ((X.symm _ _).trans (hadj (2 * n - 1 - (i + 1)) (by omega)))
    · have hin : i = 2 * n - 1 := by omega
      subst hin
      rw [show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self, if_neg (by omega),
        if_pos (by omega), show 2 * n - 1 - (2 * n - 1) = 0 by omega]
      exact adj_prod_right _ hrung'

/-! ### A certificate from an equal split

The join needs no path on either side: if the two halves have the same order, alternating between
them walks a Hamiltonian cycle out of the joining edges alone. -/

/-- **The join of two graphs of the same order is Hamiltonian.**  With `n` vertices on each side,
the cycle `g₀ h₀ g₁ h₁ ⋯` uses only the edges the join adds, so neither factor needs an edge of
its own. -/
@[toIsoGraph]
theorem isHamiltonian_join_of_card_eq {G H : CGraph} (hcard : H.card = G.card) (h2 : 2 ≤ G.card) :
    (G ∇g H).IsHamiltonian := by
  have : NeZero G.card := ⟨by omega⟩
  refine isHamiltonian_of_cyclicNumbering (n := 2 * G.card)
    (fun i ↦ if i % 2 = 0 then Sum.inl (FinEnum.equiv.symm (vtx G.card (i / 2)))
      else Sum.inr (FinEnum.equiv.symm (Fin.cast hcard.symm (vtx G.card (i / 2)))))
    (by omega)
    (by show FinEnum.card (G ∇g H).V = 2 * FinEnum.card G.V
        rw [card_join, show FinEnum.card H.V = FinEnum.card G.V from hcard, two_mul]) ?_ ?_
  · intro i hi j hj hij
    have hi2 : i / 2 < G.card := by omega
    have hj2 : j / 2 < G.card := by omega
    by_cases hie : i % 2 = 0 <;> by_cases hje : j % 2 = 0
    · rw [if_pos hie, if_pos hje] at hij
      have h := congrArg Fin.val (FinEnum.equiv.symm.injective (Sum.inl_injective hij))
      rw [vtx_val hi2, vtx_val hj2] at h
      omega
    · rw [if_pos hie, if_neg hje] at hij; simp at hij
    · rw [if_neg hie, if_pos hje] at hij; simp at hij
    · rw [if_neg hie, if_neg hje] at hij
      have h := congrArg Fin.val (FinEnum.equiv.symm.injective (Sum.inr_injective hij))
      simp only [Fin.val_cast] at h
      rw [Nat.mod_eq_of_lt hi2, Nat.mod_eq_of_lt hj2] at h
      omega
  · intro i hi
    rcases Nat.lt_or_ge (i + 1) (2 * G.card) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      by_cases hie : i % 2 = 0
      · rw [if_pos hie, if_neg (by omega), join_adj_inl_inr]
      · rw [if_neg hie, if_pos (by omega), join_adj_inr_inl]
    · have hin : i = 2 * G.card - 1 := by omega
      subst hin
      rw [show 2 * G.card - 1 + 1 = 2 * G.card by omega, Nat.mod_self, if_neg (by omega),
        if_pos rfl, join_adj_inr_inl]

/-- **The complement of a balanced disjoint union is Hamiltonian.**  Complementing a disjoint
union gives a join, and a join of two graphs of the same order is Hamiltonian. -/
@[toIsoGraph]
theorem isHamiltonian_compl_disjUnion {G H : CGraph} (hcard : H.card = G.card)
    (h2 : 2 ≤ G.card) : ((G ⊕g H)ᶜ).IsHamiltonian := by
  rw [compl_disjUnion]
  exact isHamiltonian_join_of_card_eq (by simpa using hcard) (by simpa using h2)

/-! ### Certificates from a spanning subgraph

A Hamiltonian cycle survives adding edges.  Two of the four products dominate the Cartesian one on
the same vertex set, so the prism certificate above carries over to them unchanged. -/

/-- **Adding the diagonal edges keeps a Hamiltonian cycle.**  The Cartesian product is a spanning
subgraph of the strong product. -/
@[toIsoGraph]
theorem isHamiltonian_strongProduct_of_cartesianProduct {G H : CGraph}
    (h : (G □g H).IsHamiltonian) : (G ⊠g H).IsHamiltonian := by
  refine SimpleGraph.IsHamiltonian.mono (fun p q hpq ↦ ?_) h
  rw [toSimple_adj, cartesianProduct_adj] at hpq
  show (G ⊠g H).Adj p q = true
  rw [strongProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hpq ⊢
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hne : p.2 ≠ q.2 := fun hc ↦ H.loopless q.2 (hc ▸ h2)
    exact ⟨fun hc ↦ hne (congrArg Prod.snd hc), Or.inl h1, Or.inr h2⟩
  · have hne : p.1 ≠ q.1 := fun hc ↦ G.loopless q.1 (hc ▸ h1)
    exact ⟨fun hc ↦ hne (congrArg Prod.fst hc), Or.inr h1, Or.inl h2⟩

/-- **The lexicographic product dominates the Cartesian one.**  Every Cartesian edge is a
lexicographic edge, so a Hamiltonian cycle in `G □g H` is one in `G ·g H`. -/
@[toIsoGraph]
theorem isHamiltonian_lexProduct_of_cartesianProduct {G H : CGraph}
    (h : (G □g H).IsHamiltonian) : (G ·g H).IsHamiltonian := by
  refine SimpleGraph.IsHamiltonian.mono (fun p q hpq ↦ ?_) h
  rw [toSimple_adj, cartesianProduct_adj] at hpq
  show (G ·g H).Adj p q = true
  rw [lexProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq ⊢
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl h1

/-! ### A certificate for the lexicographic product

The lexicographic product asks even less of its second factor than the spanning-subgraph argument
above: `G ·g H` is Hamiltonian as soon as `G` is, whatever `H` is.  Adjacent copies of `H` are
completely joined, so a lap of the cycle of `G` can pick up one vertex of `H` from each copy, and
`H.card` laps pick up all of them. -/

/-- **The lexicographic product of a Hamiltonian graph with anything is Hamiltonian.**  Walk the
cycle of `G` once for every vertex of `H`, taking the `k`-th vertex of `H` on the `k`-th lap: a lap
changes at a step of the cycle, so every step of the walk still moves between adjacent copies and
the second factor never needs an edge. -/
theorem isHamiltonian_lexProduct_of_cyclicNumbering {G H : CGraph} {n m : ℕ} (f : ℕ → G.V)
    (h3 : 3 ≤ n) (hm : 0 < m) (hcard : G.card = n) (hcardH : H.card = m)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hadj : ∀ i < n, G.Adj (f i) (f ((i + 1) % n)) = true) : (G ·g H).IsHamiltonian := by
  have hmz : NeZero m := ⟨by omega⟩
  have hone : (1 : ℕ) % n = 1 := Nat.mod_eq_of_lt (by omega)
  refine isHamiltonian_of_cyclicNumbering (n := n * m)
    (fun i ↦ (f (i % n), FinEnum.equiv.symm (Fin.cast hcardH.symm (vtx m (i / n)))))
    (le_trans h3 (Nat.le_mul_of_pos_right n hm))
    (by show FinEnum.card (G ·g H).V = n * m
        rw [card_lexProduct, show FinEnum.card G.V = n from hcard,
          show FinEnum.card H.V = m from hcardH]) ?_ ?_
  · intro i hi j hj hij
    have hin : i / n < m := Nat.div_lt_of_lt_mul (by omega)
    have hjn : j / n < m := Nat.div_lt_of_lt_mul (by omega)
    rw [Prod.mk.injEq] at hij
    have hmod : i % n = j % n :=
      hinj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) hij.1
    have hdiv : i / n = j / n := by
      have h := congrArg Fin.val (FinEnum.equiv.symm.injective hij.2)
      simp only [Fin.val_cast] at h
      rwa [Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hjn] at h
    have hi' := Nat.div_add_mod i n
    have hj' := Nat.div_add_mod j n
    rw [hdiv, hmod] at hi'
    exact hi'.symm.trans hj'
  · intro i hi
    simp only [lexProduct_adj, Bool.or_eq_true]
    refine Or.inl ?_
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro m rfl), show (i + 1) % n = (i % n + 1) % n by
      rw [Nat.add_mod, hone]]
    exact hadj (i % n) (Nat.mod_lt _ (by omega))

/-! ### The Hamiltonian small graphs -/

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

/-- **`K_m · H` is Hamiltonian.**  Blowing up each vertex of a complete graph into a copy of any
nonempty graph keeps a Hamiltonian cycle: the copies are completely joined in the order the cycle
of `K_m` visits them. -/
@[toIsoGraph]
theorem isHamiltonian_lexProduct_complete {m : ℕ} (h3 : 3 ≤ m) {H : CGraph} (hH : 0 < H.card) :
    (complete m ·g H).IsHamiltonian := by
  have hn : NeZero m := ⟨by omega⟩
  refine isHamiltonian_lexProduct_of_cyclicNumbering (fun i ↦ vtx m i) h3 hH (card_complete m)
    rfl (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have h := congrArg Fin.val hij
    rwa [vtx_val hi, vtx_val hj] at h
  · rw [complete_adj, decide_eq_true_eq]
    intro hc
    have h := congrArg Fin.val hc
    rw [vtx_val hi, vtx_val (Nat.mod_lt _ (by omega))] at h
    exact ne_succ_mod h3 hi h

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

theorem IsHamiltonian.two_le_minDeg {G : IsoGraph} (h : G.IsHamiltonian) (h2 : 2 ≤ G.V) :
    2 ≤ G.minDeg := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [isHamiltonian_mk] at h
  rw [V_mk] at h2
  rw [minDeg_mk]
  exact h.two_le_minDeg h2

/-- A graph with a leaf, or with an isolated vertex, is not Hamiltonian. -/
theorem not_isHamiltonian_of_minDeg_lt_two {G : IsoGraph} (h2 : 2 ≤ G.V) (h : G.minDeg < 2) :
    ¬ G.IsHamiltonian := fun hh ↦ absurd (hh.two_le_minDeg h2) (by omega)

/-- A graph with an independent set on more than half its vertices is not Hamiltonian. -/
theorem not_isHamiltonian_of_V_lt_two_mul_indepNum {G : IsoGraph} (h3 : 3 ≤ G.V)
    (h : G.V < 2 * G.indepNum) : ¬ G.IsHamiltonian :=
  fun hh ↦ absurd (hh.two_mul_indepNum_le_V h3) (by omega)

theorem isHamiltonian_complete {n : ℕ} (h3 : 3 ≤ n) : (complete n).IsHamiltonian := by
  rw [complete_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_complete h3

theorem isHamiltonian_cycle {n : ℕ} (h3 : 3 ≤ n) : (cycle n).IsHamiltonian := by
  rw [cycle_def, isHamiltonian_mk]
  exact CGraph.isHamiltonian_cycle h3

end IsoGraph
