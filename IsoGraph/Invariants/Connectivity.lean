import IsoGraph.Core.Counts

/-!
# Connectivity

The two connectivities: `CGraph.edgeConn`, the least number of *edges* whose removal disconnects
the graph, and `CGraph.vertexConn`, the least number of *vertices*.  Both are infima over finite
search spaces — the cuts `s ⊆ V` for the first, the separating sets for the second — and both are
`sInf` of a set of naturals, so a graph with nothing to disconnect gets the value `0`.  The one
wrinkle is the complete graph, which no vertex deletion disconnects: as usual, `n - 1` is thrown
into the infimum defining `vertexConn` so that `vertexConn (complete n) = n - 1`.

Each invariant comes with a witness lemma (`edgeConn_le_of_isCut`, `vertexConn_le_of_isSeparator`),
a lower-bound lemma that quantifies over the search space (`le_edgeConn`, `le_vertexConn`), and
their combination (`edgeConn_eq`, `vertexConn_eq`); `IsCut` and `IsSeparator` are decidable, so on
a small graph the lower bound is a `decide`.  The facts relating them are that both vanish exactly
when the graph is disconnected or trivial, and Whitney's `vertexConn_le_edgeConn ≤ minDeg`.

Separation is phrased without deleting anything: `G.IsSeparator s` asks for a two-colouring of the
vertices, constant along every edge that avoids `s`, and non-constant outside `s`.  That keeps the
statement inside `G.V` — no subtype, no induced subgraph — which is what makes it decidable and
what makes it transport along an isomorphism in three lines.
-/

set_option autoImplicit false

open Fintype

namespace CGraph

variable (G : CGraph)

/-! ## Edge cuts -/

/-- The edges leaving `s`, as ordered pairs with the tail inside `s` and the head outside it. -/
def crossing (s : Finset G.V) : Finset (G.V × G.V) :=
  (s ×ˢ sᶜ).filter fun p ↦ G.Adj p.1 p.2 = true

@[simp] theorem mem_crossing {G : CGraph} {s : Finset G.V} {p : G.V × G.V} :
    p ∈ G.crossing s ↔ p.1 ∈ s ∧ p.2 ∉ s ∧ G.Adj p.1 p.2 = true := by
  simp only [crossing, Finset.mem_filter, Finset.mem_product, Finset.mem_compl, and_assoc]

/-- The number of edges leaving `s`. -/
def cutSize (s : Finset G.V) : ℕ := (G.crossing s).card

/-- `s` is a **cut**: it is neither empty nor everything, so deleting the edges that leave it
disconnects the graph. -/
def IsCut (s : Finset G.V) : Prop := s.Nonempty ∧ sᶜ.Nonempty

/-- **Edge connectivity**: the least number of edges whose removal disconnects the graph.  A
graph on at most one vertex has no cuts at all, and the infimum of the empty set is `0`. -/
noncomputable def edgeConn : ℕ := sInf {k | ∃ s : Finset G.V, G.IsCut s ∧ G.cutSize s = k}

theorem Iso.adj_symm_eq {G H : CGraph} (i : G ≃cg H) (x y : H.V) :
    G.Adj (i.symm x) (i.symm y) = H.Adj x y := by
  have := i.adj_eq (i.symm x) (i.symm y)
  rw [i.apply_symm_apply, i.apply_symm_apply] at this
  exact this.symm

/-- Membership in the image of a set of vertices under an isomorphism. -/
theorem mem_map_iso {G H : CGraph} (i : G ≃cg H) {s : Finset G.V} {x : G.V} :
    i x ∈ s.map i.toEquiv.toEmbedding ↔ x ∈ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ Finset.mem_map.2 ⟨x, h, rfl⟩⟩
  obtain ⟨z, hz, hzx⟩ := Finset.mem_map.1 h
  exact (i.toEquiv.injective hzx : z = x) ▸ hz

theorem mem_map_iso' {G H : CGraph} (i : G ≃cg H) {s : Finset G.V} {y : H.V} :
    y ∈ s.map i.toEquiv.toEmbedding ↔ i.symm y ∈ s := by
  rw [← mem_map_iso i, i.apply_symm_apply]

theorem cutSize_map {G H : CGraph} (i : G ≃cg H) (s : Finset G.V) :
    H.cutSize (s.map i.toEquiv.toEmbedding) = G.cutSize s := by
  refine Finset.card_nbij' (fun p ↦ (i.symm p.1, i.symm p.2)) (fun p ↦ (i p.1, i p.2))
    (fun p hp ↦ ?_) (fun p hp ↦ ?_) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · simp only [Finset.mem_coe, mem_crossing, mem_map_iso'] at hp ⊢
    exact ⟨hp.1, hp.2.1, by rw [Iso.adj_symm_eq]; exact hp.2.2⟩
  · simp only [Finset.mem_coe, mem_crossing, mem_map_iso] at hp ⊢
    exact ⟨hp.1, hp.2.1, by rw [i.adj_eq]; exact hp.2.2⟩
  · exact Prod.ext (i.apply_symm_apply _) (i.apply_symm_apply _)
  · exact Prod.ext (RelIso.symm_apply_apply i _) (RelIso.symm_apply_apply i _)

theorem IsCut.map {G H : CGraph} (i : G ≃cg H) {s : Finset G.V} (h : G.IsCut s) :
    H.IsCut (s.map i.toEquiv.toEmbedding) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  rw [Finset.mem_compl] at hy
  exact ⟨⟨i x, (mem_map_iso i).2 hx⟩,
    ⟨i y, Finset.mem_compl.2 fun h ↦ hy ((mem_map_iso i).1 h)⟩⟩

@[toIsoGraph]
theorem edgeConn_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.edgeConn = H.edgeConn := by
  have hset : {k | ∃ s : Finset G.V, G.IsCut s ∧ G.cutSize s = k}
      = {k | ∃ s : Finset H.V, H.IsCut s ∧ H.cutSize s = k} := by
    ext k
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.map i.toEquiv.toEmbedding, hs.map i, cutSize_map i s⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.map i.symm.toEquiv.toEmbedding, hs.map i.symm, cutSize_map i.symm s⟩
  unfold edgeConn
  rw [hset]

/-! ### Bounding the edge connectivity -/

theorem edgeConn_le_of_isCut {s : Finset G.V} (h : G.IsCut s) : G.edgeConn ≤ G.cutSize s :=
  Nat.sInf_le ⟨s, h, rfl⟩

theorem card_le_one_of_not_isCut {s : Finset G.V} (h : G.IsCut s) : 2 ≤ G.card := by
  have h1 : 0 < s.card := Finset.card_pos.2 h.1
  have h2 : 0 < sᶜ.card := Finset.card_pos.2 h.2
  have h3 : s.card + sᶜ.card = G.card := by
    rw [Finset.card_add_card_compl]
    exact G.fintypeCard
  omega

theorem exists_isCut (h2 : 2 ≤ G.card) : ∃ s : Finset G.V, G.IsCut s := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  obtain ⟨x, y, hxy⟩ := @Fintype.exists_pair_of_one_lt_card G.V _ (by omega)
  exact ⟨{x}, ⟨⟨x, Finset.mem_singleton_self x⟩, ⟨y, by simp [Ne.symm hxy]⟩⟩⟩

/-- The infimum defining the edge connectivity is attained. -/
theorem exists_cutSize_eq_edgeConn (h2 : 2 ≤ G.card) :
    ∃ s : Finset G.V, G.IsCut s ∧ G.cutSize s = G.edgeConn := by
  obtain ⟨s, hs⟩ := G.exists_isCut h2
  have hne : {k | ∃ t : Finset G.V, G.IsCut t ∧ G.cutSize t = k}.Nonempty :=
    ⟨G.cutSize s, s, hs, rfl⟩
  exact Nat.sInf_mem hne

/-- **A lower bound on the edge connectivity**, by exhausting the cuts.  `IsCut` and `cutSize`
are decidable, so for a graph with few enough vertices this is a `decide`. -/
theorem le_edgeConn {k : ℕ} (h2 : 2 ≤ G.card)
    (h : ∀ s : Finset G.V, G.IsCut s → k ≤ G.cutSize s) : k ≤ G.edgeConn := by
  obtain ⟨s, hs, hse⟩ := G.exists_cutSize_eq_edgeConn h2
  exact hse ▸ h s hs

/-- The edge connectivity, from a cut of the right size and a lower bound. -/
theorem edgeConn_eq {k : ℕ} {s : Finset G.V} (h2 : 2 ≤ G.card) (hs : G.IsCut s)
    (hk : G.cutSize s = k) (hmin : ∀ t : Finset G.V, G.IsCut t → k ≤ G.cutSize t) :
    G.edgeConn = k :=
  le_antisymm (hk ▸ G.edgeConn_le_of_isCut hs) (G.le_edgeConn h2 hmin)

theorem cutSize_singleton (v : G.V) : G.cutSize {v} = (G.nbrs v).card := by
  rw [cutSize]
  refine Finset.card_nbij' (fun p ↦ p.2) (fun w ↦ (v, w)) (fun p hp ↦ ?_) (fun w hw ↦ ?_)
    (fun p hp ↦ ?_) (fun w _ ↦ rfl)
  · simp only [Finset.mem_coe, mem_crossing, Finset.mem_singleton] at hp
    simp only [Finset.mem_coe, mem_nbrs, ← hp.1]
    exact hp.2.2
  · simp only [Finset.mem_coe, mem_nbrs] at hw
    refine Finset.mem_coe.2 (mem_crossing.2 ⟨Finset.mem_singleton_self v, fun hvw ↦ ?_, hw⟩)
    rw [Finset.mem_singleton] at hvw
    have hvw' : w = v := hvw
    subst hvw'
    exact G.loopless _ hw
  · simp only [Finset.mem_coe, mem_crossing, Finset.mem_singleton] at hp
    exact Prod.ext hp.1.symm rfl

theorem cutSize_singleton_eq_degree (v : G.V) : G.cutSize {v} = G.toSimple.degree v := by
  rw [cutSize_singleton, SimpleGraph.degree, neighborFinset_eq_nbrs]

/-- **The edge connectivity is at most the minimum degree**: the edges at a single vertex are a
cut. -/
theorem edgeConn_le_minDeg (h2 : 2 ≤ G.card) : G.edgeConn ≤ G.minDeg := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  have hne : Nonempty G.V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨v, hv⟩ := G.toSimple.exists_minimal_degree_vertex
  have hcompl : ({v} : Finset G.V)ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton]
    omega
  calc G.edgeConn ≤ G.cutSize {v} :=
        G.edgeConn_le_of_isCut ⟨⟨v, Finset.mem_singleton_self v⟩, hcompl⟩
    _ = G.toSimple.degree v := G.cutSize_singleton_eq_degree v
    _ = G.minDeg := hv.symm

/-! ### Edge connectivity and connectedness -/

/-- A walk that starts inside `s` and ends outside it crosses the cut. -/
theorem exists_mem_crossing_of_walk {G : CGraph} {s : Finset G.V} :
    ∀ {u v : G.V}, G.toSimple.Walk u v → u ∈ s → v ∉ s → ∃ p, p ∈ G.crossing s := by
  intro u v w
  induction w with
  | nil => intro h1 h2; exact absurd h1 h2
  | @cons x y z hxy _ ih =>
      intro hx hz
      by_cases hy : y ∈ s
      · exact ih hy hz
      · exact ⟨(x, y), mem_crossing.2 ⟨hx, hy, hxy⟩⟩

theorem cutSize_pos_of_isConnected (hG : G.IsConnected) {s : Finset G.V} (hs : G.IsCut s) :
    0 < G.cutSize s := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hs
  rw [Finset.mem_compl] at hy
  obtain ⟨w⟩ := hG.preconnected x y
  obtain ⟨p, hp⟩ := exists_mem_crossing_of_walk w hx hy
  exact Finset.card_pos.2 ⟨p, hp⟩

theorem exists_isCut_cutSize_eq_zero (h2 : 2 ≤ G.card) (h : ¬ G.IsConnected) :
    ∃ s : Finset G.V, G.IsCut s ∧ G.cutSize s = 0 := by
  classical
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  have hne : Nonempty G.V := Fintype.card_pos_iff.1 (by omega)
  have hpre : ¬ G.toSimple.Preconnected :=
    fun hp ↦ h ((SimpleGraph.connected_iff G.toSimple).2 ⟨hp, hne⟩)
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬ G.toSimple.Reachable u v := by
    by_contra hc
    push Not at hc
    exact hpre hc
  refine ⟨Finset.univ.filter fun x ↦ G.toSimple.Reachable u x,
    ⟨⟨u, by simp⟩, ⟨v, by simp [huv]⟩⟩, ?_⟩
  rw [cutSize, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨a, b⟩ hab
  rw [mem_crossing] at hab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
  exact hab.2.1 (hab.1.trans (SimpleGraph.Adj.reachable hab.2.2))

/-- The edge connectivity is zero exactly when there is nothing to disconnect, or the graph is
already disconnected. -/
theorem edgeConn_eq_zero_iff : G.edgeConn = 0 ↔ G.card ≤ 1 ∨ ¬ G.IsConnected := by
  constructor
  · intro h
    by_cases h2 : 2 ≤ G.card
    · refine Or.inr fun hconn ↦ ?_
      obtain ⟨s, hs, hse⟩ := G.exists_cutSize_eq_edgeConn h2
      have := G.cutSize_pos_of_isConnected hconn hs
      omega
    · exact Or.inl (by omega)
  · intro h
    rcases le_or_gt G.card 1 with h1 | h1
    · refine Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_iff_forall_notMem.2 ?_))
      rintro k ⟨s, hs, -⟩
      have := G.card_le_one_of_not_isCut hs
      omega
    · obtain ⟨s, hs, h0⟩ := G.exists_isCut_cutSize_eq_zero (by omega) (h.resolve_left (by omega))
      exact Nat.sInf_eq_zero.2 (Or.inl ⟨s, hs, h0⟩)

/-! ## Vertex connectivity -/

/-- `s` **separates** `G`: with the vertices of `s` deleted, what is left falls into two
nonempty pieces with no edge between them.  The two pieces are recorded by a `Bool`-valued
function that is constant along every edge avoiding `s`. -/
def IsSeparator (s : Finset G.V) : Prop :=
  ∃ f : G.V → Bool, (∃ a ∉ s, f a = true) ∧ (∃ b ∉ s, f b = false) ∧
    ∀ u v, u ∉ s → v ∉ s → G.Adj u v = true → f u = f v

/-- **Vertex connectivity**: the least number of vertices whose deletion disconnects the graph.
No deletion disconnects a complete graph, so `n - 1` is thrown into the infimum — the usual
convention, and the value it takes on `complete n`. -/
noncomputable def vertexConn : ℕ :=
  sInf (insert (G.card - 1) {k | ∃ s : Finset G.V, G.IsSeparator s ∧ s.card = k})

theorem IsSeparator.map {G H : CGraph} (i : G ≃cg H) {s : Finset G.V} (h : G.IsSeparator s) :
    H.IsSeparator (s.map i.toEquiv.toEmbedding) := by
  obtain ⟨f, ⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩, hconst⟩ := h
  refine ⟨fun y ↦ f (i.symm y), ⟨i a, fun hc ↦ ha ((mem_map_iso i).1 hc), ?_⟩,
    ⟨i b, fun hc ↦ hb ((mem_map_iso i).1 hc), ?_⟩, fun u v hu hv huv ↦ ?_⟩
  · simp only [RelIso.symm_apply_apply]; exact hfa
  · simp only [RelIso.symm_apply_apply]; exact hfb
  · exact hconst _ _ (fun hc ↦ hu ((mem_map_iso' i).2 hc)) (fun hc ↦ hv ((mem_map_iso' i).2 hc))
      (by rw [Iso.adj_symm_eq]; exact huv)

@[toIsoGraph]
theorem vertexConn_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.vertexConn = H.vertexConn := by
  have hcard : G.card = H.card := i.card_eq
  have hset : {k | ∃ s : Finset G.V, G.IsSeparator s ∧ s.card = k}
      = {k | ∃ s : Finset H.V, H.IsSeparator s ∧ s.card = k} := by
    ext k
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.map i.toEquiv.toEmbedding, hs.map i, Finset.card_map _⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.map i.symm.toEquiv.toEmbedding, hs.map i.symm, Finset.card_map _⟩
  unfold vertexConn
  rw [hset, hcard]

/-! ### Bounding the vertex connectivity -/

theorem vertexConn_le_card_sub_one : G.vertexConn ≤ G.card - 1 :=
  Nat.sInf_le (Set.mem_insert _ _)

theorem vertexConn_le_of_isSeparator {s : Finset G.V} (h : G.IsSeparator s) :
    G.vertexConn ≤ s.card :=
  Nat.sInf_le (Set.mem_insert_of_mem _ ⟨s, h, rfl⟩)

/-- **A lower bound on the vertex connectivity**, by exhausting the separators.  `IsSeparator`
is decidable, so for a graph with few enough vertices this is a `decide`. -/
theorem le_vertexConn {k : ℕ} (hcard : k ≤ G.card - 1)
    (h : ∀ s : Finset G.V, G.IsSeparator s → k ≤ s.card) : k ≤ G.vertexConn := by
  unfold vertexConn
  have hne : (insert (G.card - 1)
      {k | ∃ s : Finset G.V, G.IsSeparator s ∧ s.card = k}).Nonempty := ⟨_, Set.mem_insert _ _⟩
  rcases Nat.sInf_mem hne with h1 | ⟨s, hs, hsc⟩
  · omega
  · exact hsc ▸ h s hs

/-- **A lower bound on the vertex connectivity, searching only the small sets.**  A separator on
`k` vertices or more is no obstacle to `k ≤ κ`, so only the sets of fewer than `k` vertices have
to be ruled out.  Deciding `IsSeparator` costs `2ⁿ` on its own, so cutting the outer search from
all `2ⁿ` sets down to the `∑_{i<k} C(n,i)` small ones is what makes the check affordable. -/
theorem le_vertexConn_of_forall_card_lt {k : ℕ} (hcard : k ≤ G.card - 1)
    (h : ∀ s : Finset G.V, s.card < k → ¬ G.IsSeparator s) : k ≤ G.vertexConn :=
  G.le_vertexConn hcard fun s hs ↦ by
    by_contra hlt
    exact h s (by omega) hs

/-- The vertex connectivity, from a separator of the right size and a lower bound. -/
theorem vertexConn_eq {k : ℕ} {s : Finset G.V} (hs : G.IsSeparator s) (hk : s.card = k)
    (hcard : k ≤ G.card - 1) (hmin : ∀ t : Finset G.V, G.IsSeparator t → k ≤ t.card) :
    G.vertexConn = k :=
  le_antisymm (hk ▸ G.vertexConn_le_of_isSeparator hs) (G.le_vertexConn hcard hmin)

/-! ### Vertex connectivity and connectedness -/

theorem not_isConnected_of_isSeparator_empty (h : G.IsSeparator ∅) : ¬ G.IsConnected := by
  obtain ⟨f, ⟨a, -, hfa⟩, ⟨b, -, hfb⟩, hconst⟩ := h
  intro hconn
  have hab : f a = f b :=
    eq_of_forall_adj hconn (φ := f) (fun x y hxy ↦ hconst x y (by simp) (by simp) hxy) a b
  rw [hfa, hfb] at hab
  exact Bool.noConfusion hab

theorem isSeparator_empty_of_not_isConnected (h2 : 2 ≤ G.card) (h : ¬ G.IsConnected) :
    G.IsSeparator ∅ := by
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  have hne : Nonempty G.V := Fintype.card_pos_iff.1 (by omega)
  have hpre : ¬ G.toSimple.Preconnected :=
    fun hp ↦ h ((SimpleGraph.connected_iff G.toSimple).2 ⟨hp, hne⟩)
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬ G.toSimple.Reachable u v := by
    by_contra hc
    push Not at hc
    exact hpre hc
  refine ⟨fun x ↦ decide (G.toSimple.Reachable u x), ⟨u, by simp, by simp⟩,
    ⟨v, by simp, by simp [huv]⟩, fun x y _ _ hxy ↦ ?_⟩
  have hiff : G.toSimple.Reachable u x ↔ G.toSimple.Reachable u y :=
    ⟨fun hr ↦ hr.trans (SimpleGraph.Adj.reachable hxy),
      fun hr ↦ hr.trans (SimpleGraph.Adj.reachable hxy).symm⟩
  simp only [hiff]

/-- The vertex connectivity is zero exactly when there is nothing to disconnect, or the graph is
already disconnected. -/
theorem vertexConn_eq_zero_iff : G.vertexConn = 0 ↔ G.card ≤ 1 ∨ ¬ G.IsConnected := by
  constructor
  · intro h
    rcases le_or_gt G.card 1 with h1 | h1
    · exact Or.inl h1
    refine Or.inr ?_
    have hne : (insert (G.card - 1)
        {k | ∃ s : Finset G.V, G.IsSeparator s ∧ s.card = k}).Nonempty := ⟨_, Set.mem_insert _ _⟩
    have h0 : (0 : ℕ) ∈ insert (G.card - 1)
        {k | ∃ s : Finset G.V, G.IsSeparator s ∧ s.card = k} := by
      rw [← h]; exact Nat.sInf_mem hne
    rcases h0 with he | ⟨s, hs, hsc⟩
    · omega
    · rw [Finset.card_eq_zero] at hsc
      exact G.not_isConnected_of_isSeparator_empty (hsc ▸ hs)
  · intro h
    have hle := G.vertexConn_le_card_sub_one
    rcases le_or_gt G.card 1 with h1 | h1
    · omega
    · have hsep := G.isSeparator_empty_of_not_isConnected (by omega) (h.resolve_left (by omega))
      simpa using G.vertexConn_le_of_isSeparator hsep

/-! ### Whitney's inequality -/

private theorem card_sub_one_le_mul {p q n : ℕ} (hp : 0 < p) (hq : 0 < q) (h : p + q = n) :
    n - 1 ≤ p * q := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hexp : (p' + 1) * (q' + 1) = p' * q' + p' + q' + 1 := by ring
  omega

/-- A cut every one of whose pairs is an edge is complete bipartite. -/
theorem cutSize_eq_mul_of_forall_adj {s : Finset G.V}
    (h : ∀ a ∈ s, ∀ b, b ∉ s → G.Adj a b = true) : G.cutSize s = s.card * sᶜ.card := by
  have hfil : ∀ p ∈ s ×ˢ sᶜ, G.Adj p.1 p.2 = true := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_product, Finset.mem_compl] at hab
    exact h a hab.1 b hab.2
  rw [cutSize, crossing, Finset.filter_true_of_mem hfil, Finset.card_product]

theorem card_sub_one_le_cutSize_of_forall_adj {s : Finset G.V} (hs : G.IsCut s)
    (h : ∀ a ∈ s, ∀ b, b ∉ s → G.Adj a b = true) : G.card - 1 ≤ G.cutSize s := by
  have hsum : s.card + sᶜ.card = G.card := by
    rw [Finset.card_add_card_compl]; exact G.fintypeCard
  rw [G.cutSize_eq_mul_of_forall_adj h]
  exact card_sub_one_le_mul (Finset.card_pos.2 hs.1) (Finset.card_pos.2 hs.2) hsum

/-- **Whitney's inequality**: the vertex connectivity is at most the edge connectivity.

Take a minimum edge cut, with sides `s` and `sᶜ`.  If some `a ∈ s` and `b ∉ s` are non-adjacent
then the neighbours of `a` outside `s`, together with the vertices of `s` other than `a` that
have a neighbour outside `s`, separate `a` from `b`, and each of them accounts for a distinct
edge of the cut.  If instead every such pair is adjacent then the cut has `|s| ⬝ |sᶜ| ≥ n - 1`
edges, which is already at least the vertex connectivity. -/
theorem vertexConn_le_edgeConn (G : CGraph) : G.vertexConn ≤ G.edgeConn := by
  classical
  have hFC : Fintype.card G.V = G.card := G.fintypeCard
  have hle := G.vertexConn_le_card_sub_one
  rcases le_or_gt G.card 1 with h1 | h1
  · omega
  obtain ⟨s, hs, hse⟩ := G.exists_cutSize_eq_edgeConn h1
  rw [← hse]
  by_cases hall : ∀ a ∈ s, ∀ b, b ∉ s → G.Adj a b = true
  · have := G.card_sub_one_le_cutSize_of_forall_adj hs hall
    omega
  push Not at hall
  obtain ⟨a, ha, b, hb, hab⟩ := hall
  set T : Finset G.V :=
    (G.nbrs a \ s) ∪ (s.erase a).filter (fun x ↦ (G.nbrs x \ s).Nonempty) with hT
  have hmemT : ∀ x, x ∈ T ↔
      (x ∈ G.nbrs a ∧ x ∉ s) ∨ (x ∈ s ∧ x ≠ a ∧ (G.nbrs x \ s).Nonempty) := by
    intro x
    simp only [hT, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_erase]
    tauto
  have hkey : ∀ u v : G.V, u ∉ T → v ∉ T → G.Adj u v = true → u ∈ s → v ∈ s := by
    intro u v hu hv huv hus
    by_contra hvs
    by_cases hua : u = a
    · subst hua
      exact hv ((hmemT v).2 (Or.inl ⟨(G.mem_nbrs u v).2 huv, hvs⟩))
    · exact hu ((hmemT u).2
        (Or.inr ⟨hus, hua, ⟨v, Finset.mem_sdiff.2 ⟨(G.mem_nbrs u v).2 huv, hvs⟩⟩⟩))
  have hsep : G.IsSeparator T := by
    refine ⟨fun x ↦ decide (x ∈ s), ⟨a, ?_, by simp [ha]⟩, ⟨b, ?_, by simp [hb]⟩,
      fun u v hu hv huv ↦ ?_⟩
    · intro hc
      rcases (hmemT a).1 hc with ⟨-, hna⟩ | ⟨-, hne, -⟩
      · exact hna ha
      · exact hne rfl
    · intro hc
      rcases (hmemT b).1 hc with ⟨hnb, -⟩ | ⟨hbs, -, -⟩
      · exact hab ((G.mem_nbrs a b).1 hnb)
      · exact hb hbs
    · by_cases hus : u ∈ s
      · simp [hus, hkey u v hu hv huv hus]
      · have hvs : v ∉ s := fun hvs ↦ hus (hkey v u hv hu (by rw [G.symm]; exact huv) hvs)
        simp [hus, hvs]
  have hcard : T.card ≤ G.cutSize s := by
    rw [cutSize]
    refine Finset.card_le_card_of_injOn
      (fun x ↦ if hd : x ∈ s ∧ (G.nbrs x \ s).Nonempty then (x, hd.2.choose) else (a, x))
      (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)
    · simp only [Finset.mem_coe] at hx ⊢
      by_cases hc : x ∈ s ∧ (G.nbrs x \ s).Nonempty
      · rw [dif_pos hc]
        have hw := hc.2.choose_spec
        rw [Finset.mem_sdiff, G.mem_nbrs] at hw
        exact mem_crossing.2 ⟨hc.1, hw.2, hw.1⟩
      · rw [dif_neg hc]
        rcases (hmemT x).1 hx with ⟨hxa, hxs⟩ | ⟨hxs, -, hxn⟩
        · exact mem_crossing.2 ⟨ha, hxs, (G.mem_nbrs a x).1 hxa⟩
        · exact absurd ⟨hxs, hxn⟩ hc
    · simp only [Finset.mem_coe] at hx hy
      dsimp only at hxy
      by_cases hcx : x ∈ s ∧ (G.nbrs x \ s).Nonempty <;>
        by_cases hcy : y ∈ s ∧ (G.nbrs y \ s).Nonempty
      · rw [dif_pos hcx, dif_pos hcy] at hxy
        exact congrArg Prod.fst hxy
      · rw [dif_pos hcx, dif_neg hcy] at hxy
        rcases (hmemT x).1 hx with ⟨-, hxs⟩ | ⟨-, hne, -⟩
        · exact absurd hcx.1 hxs
        · exact absurd (congrArg Prod.fst hxy) hne
      · rw [dif_neg hcx, dif_pos hcy] at hxy
        rcases (hmemT y).1 hy with ⟨-, hys⟩ | ⟨-, hne, -⟩
        · exact absurd hcy.1 hys
        · exact absurd (congrArg Prod.fst hxy).symm hne
      · rw [dif_neg hcx, dif_neg hcy] at hxy
        exact congrArg Prod.snd hxy
  exact le_trans (G.vertexConn_le_of_isSeparator hsep) hcard

/-- The second half of Whitney's chain `κ ≤ λ ≤ δ`. -/
theorem vertexConn_le_minDeg (h2 : 2 ≤ G.card) : G.vertexConn ≤ G.minDeg :=
  le_trans G.vertexConn_le_edgeConn (G.edgeConn_le_minDeg h2)

/-- One edge has to go, exactly when the graph is connected. -/
theorem one_le_edgeConn_iff (h2 : 2 ≤ G.card) : 1 ≤ G.edgeConn ↔ G.IsConnected := by
  have h := G.edgeConn_eq_zero_iff
  refine ⟨fun hk ↦ by_contra fun hc ↦ ?_, fun hc ↦ ?_⟩
  · have := h.2 (Or.inr hc)
    omega
  · have h0 : ¬ G.edgeConn = 0 := fun h0 ↦ (h.1 h0).elim (fun hn ↦ by omega) fun hn ↦ hn hc
    omega

/-- One vertex has to go, exactly when the graph is connected. -/
theorem one_le_vertexConn_iff (h2 : 2 ≤ G.card) : 1 ≤ G.vertexConn ↔ G.IsConnected := by
  have h := G.vertexConn_eq_zero_iff
  refine ⟨fun hk ↦ by_contra fun hc ↦ ?_, fun hc ↦ ?_⟩
  · have := h.2 (Or.inr hc)
    omega
  · have h0 : ¬ G.vertexConn = 0 := fun h0 ↦ (h.1 h0).elim (fun hn ↦ by omega) fun hn ↦ hn hc
    omega

/-! ## Decidability, and the complete graphs -/

instance instDecidableIsCut (s : Finset G.V) : Decidable (G.IsCut s) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ sᶜ.Nonempty))

/-- Separation is decidable, by enumerating the `2ⁿ` two-colourings of the vertices; this is for
small graphs, and `native_decide`. -/
instance instDecidableIsSeparator (s : Finset G.V) : Decidable (G.IsSeparator s) :=
  inferInstanceAs (Decidable (∃ f : G.V → Bool, (∃ a ∉ s, f a = true) ∧ (∃ b ∉ s, f b = false) ∧
    ∀ u v, u ∉ s → v ∉ s → G.Adj u v = true → f u = f v))

theorem adj_complete_of_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) : (complete n).Adj i j = true := by
  simp [complete_adj, h]

theorem not_isSeparator_complete (n : ℕ) (s : Finset (complete n).V) :
    ¬ (complete n).IsSeparator s := by
  rintro ⟨f, ⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩, hconst⟩
  have hne : a ≠ b := by
    intro h
    rw [h, hfb] at hfa
    exact Bool.noConfusion hfa
  have hf := hconst a b ha hb (adj_complete_of_ne hne)
  rw [hfa, hfb] at hf
  exact Bool.noConfusion hf

/-- Nothing separates a complete graph, so its vertex connectivity is the junk value `n - 1` —
which is also the honest answer: `n - 1` vertices have to go before one is left alone. -/
@[simp] theorem vertexConn_complete (n : ℕ) : (complete n).vertexConn = n - 1 := by
  have hcard : (complete n).card = n := card_complete n
  have hle := (complete n).vertexConn_le_card_sub_one
  exact le_antisymm (by omega)
    ((complete n).le_vertexConn (by omega) fun s hs ↦ absurd hs (not_isSeparator_complete n s))

@[simp] theorem edgeConn_complete (n : ℕ) : (complete n).edgeConn = n - 1 := by
  have hcard : (complete n).card = n := card_complete n
  rcases le_or_gt n 1 with h1 | h1
  · have h0 : (complete n).edgeConn = 0 :=
      ((complete n).edgeConn_eq_zero_iff).2 (Or.inl (by omega))
    omega
  have hdeg : ∀ v : (complete n).V, ((complete n).nbrs v).card = n - 1 := by
    intro v
    have hev : (complete n).nbrs v = (Finset.univ : Finset (complete n).V).erase v := by
      ext w
      simp only [mem_nbrs, Finset.mem_erase, Finset.mem_univ, and_true, complete_adj,
        decide_eq_true_eq, ne_eq]
      exact ⟨Ne.symm, Ne.symm⟩
    rw [hev, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp
  have h0n : (0 : ℕ) < n := by omega
  refine (complete n).edgeConn_eq (s := {⟨0, h0n⟩}) (by omega)
    ⟨⟨_, Finset.mem_singleton_self _⟩, ⟨⟨1, h1⟩, Finset.mem_compl.2 fun hm ↦
      Nat.one_ne_zero (congrArg Fin.val (Finset.mem_singleton.1 hm))⟩⟩ ?_ ?_
  · rw [cutSize_singleton, hdeg]
  · intro t ht
    have hall : ∀ a ∈ t, ∀ b, b ∉ t → (complete n).Adj a b = true := fun a ha b hb ↦
      adj_complete_of_ne fun h ↦ hb (h ▸ ha)
    have := (complete n).card_sub_one_le_cutSize_of_forall_adj ht hall
    omega

/-! ### The cycle

The first family whose connectivities are not read off `minDeg` and connectedness alone: a cycle
is 2-connected and 2-edge-connected.  Both lower bounds run on the same observation — a set of
vertices closed under the successor is everything — applied to a cut and to the two colour classes
of a would-be separator. -/

/-- Along a cycle of length at least three, no vertex is its own successor. -/
theorem ne_succ_mod {n i : ℕ} (h3 : 3 ≤ n) (hi : i < n) : i ≠ (i + 1) % n := by
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have hin : i + 1 = n := by omega
    rw [hin, Nat.mod_self]; omega

/-- The successor of a vertex of a cycle. -/
private def csucc {n : ℕ} (h3 : 3 ≤ n) (i : (cycle n).V) : (cycle n).V :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩

private theorem csucc_val {n : ℕ} (h3 : 3 ≤ n) (i : (cycle n).V) :
    (csucc h3 i).1 = (i.1 + 1) % n := rfl

private theorem adj_csucc {n : ℕ} (h3 : 3 ≤ n) (i : (cycle n).V) :
    (cycle n).Adj i (csucc h3 i) = true := by
  rw [cycle_adj_val]
  exact ⟨ne_succ_mod h3 i.isLt, Or.inl rfl⟩

/-- **Going around the cycle**: a property that holds somewhere and is inherited by the successor
holds everywhere. -/
private theorem forall_of_csucc_closed {n : ℕ} (h3 : 3 ≤ n) {P : (cycle n).V → Prop}
    {k : (cycle n).V} (hk : P k) (hstep : ∀ i, P i → P (csucc h3 i)) (j : (cycle n).V) : P j := by
  have hiter : ∀ m : ℕ, ∃ v, P v ∧ v.1 = (k.1 + m) % n := by
    intro m
    induction m with
    | zero => exact ⟨k, hk, by rw [Nat.add_zero, Nat.mod_eq_of_lt k.isLt]⟩
    | succ m ih =>
      obtain ⟨v, hv, hval⟩ := ih
      refine ⟨csucc h3 v, hstep v hv, ?_⟩
      rw [csucc_val, hval, Nat.mod_add_mod, Nat.add_assoc]
  obtain ⟨v, hv, hval⟩ := hiter (j.1 + n - k.1)
  have hk' := k.isLt
  have hj' := j.isLt
  have hmod : (k.1 + (j.1 + n - k.1)) % n = j.1 := by
    rw [show k.1 + (j.1 + n - k.1) = j.1 + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj']
  rw [hmod] at hval
  exact (Fin.ext hval : v = j) ▸ hv

/-- A set of vertices of a cycle that is closed under the successor and is nonempty is
everything. -/
private theorem eq_univ_of_csucc_mem {n : ℕ} (h3 : 3 ≤ n) {s : Finset (cycle n).V}
    (hne : s.Nonempty) (h : ∀ i ∈ s, csucc h3 i ∈ s) : s = Finset.univ := by
  obtain ⟨k, hk⟩ := hne
  exact Finset.eq_univ_of_forall fun j ↦ forall_of_csucc_closed h3 hk (fun i hi ↦ h i hi) j

/-- **A cycle is 2-edge-connected.** -/
theorem two_le_edgeConn_cycle {n : ℕ} (h3 : 3 ≤ n) : 2 ≤ (cycle n).edgeConn := by
  refine (cycle n).le_edgeConn (by rw [show (cycle n).card = n from card_cycle n]; omega)
    fun s hs ↦ ?_
  obtain ⟨hsne, hscne⟩ := hs
  -- an edge leaving `s`
  obtain ⟨i, hi, hi'⟩ : ∃ i ∈ s, csucc h3 i ∉ s := by
    by_contra hc
    push Not at hc
    have := eq_univ_of_csucc_mem h3 hsne hc
    rw [this] at hscne
    simp at hscne
  -- an edge leaving `sᶜ`, that is, an edge entering `s`
  obtain ⟨j, hj, hj'⟩ : ∃ j ∈ sᶜ, csucc h3 j ∉ sᶜ := by
    by_contra hc
    push Not at hc
    have := eq_univ_of_csucc_mem h3 hscne hc
    rw [Finset.compl_eq_univ_iff] at this
    rw [this] at hsne
    simp at hsne
  rw [Finset.mem_compl] at hj
  rw [Finset.mem_compl, not_not] at hj'
  refine Finset.one_lt_card.2 ⟨(i, csucc h3 i), ?_, (csucc h3 j, j), ?_, ?_⟩
  · exact mem_crossing.2 ⟨hi, hi', adj_csucc h3 i⟩
  · exact mem_crossing.2 ⟨hj', hj, by
      have := adj_csucc h3 j
      rw [← (cycle n).symm] at this
      exact this⟩
  · intro heq
    have h1 : i = csucc h3 j := congrArg Prod.fst heq
    have h2 : csucc h3 i = j := congrArg Prod.snd heq
    have e1 : i.1 = (j.1 + 1) % n := by rw [h1, csucc_val]
    have e2 : (i.1 + 1) % n = j.1 := by rw [← csucc_val h3 i, h2]
    have hj'' := j.isLt
    rcases Nat.lt_or_ge (j.1 + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at e1
      rw [e1] at e2
      rcases Nat.lt_or_ge (j.1 + 1 + 1) n with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at e2; omega
      · rw [show j.1 + 1 + 1 = n by omega, Nat.mod_self] at e2; omega
    · rw [show j.1 + 1 = n by omega, Nat.mod_self] at e1
      rw [e1, Nat.mod_eq_of_lt (by omega)] at e2
      omega

/-- No single vertex separates a cycle: with `v` deleted what is left is a path, so the colouring
of a would-be separator is constant on it. -/
theorem not_isSeparator_cycle {n : ℕ} (h3 : 3 ≤ n) {s : Finset (cycle n).V} (hs : s.card ≤ 1) :
    ¬ (cycle n).IsSeparator s := by
  rintro ⟨f, ⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩, hconst⟩
  -- a vertex `v` that contains everything `s` might contain, and is neither `a` nor `b`
  obtain ⟨v, hv, hva, hvb⟩ : ∃ v : (cycle n).V, (∀ x ∈ s, x = v) ∧ a ≠ v ∧ b ≠ v := by
    rcases Finset.card_le_one.1 hs with hone
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨w, hw⟩
    · -- nothing to avoid: any vertex other than `a` and `b` will do
      have hab : a.1 ≠ b.1 := fun h ↦ by
        have hf : f a = f b := congrArg f (Fin.ext h : a = b)
        rw [hfa, hfb] at hf
        exact Bool.noConfusion hf
      have hlt : ∃ m : ℕ, m < n ∧ m ≠ a.1 ∧ m ≠ b.1 := by
        by_contra hc
        push Not at hc
        have h0 := hc 0 (by omega)
        have h1 := hc 1 (by omega)
        have h2 := hc 2 (by omega)
        omega
      obtain ⟨m, hm, hma, hmb⟩ := hlt
      exact ⟨⟨m, hm⟩, by simp, fun h ↦ hma (congrArg Fin.val h).symm,
        fun h ↦ hmb (congrArg Fin.val h).symm⟩
    · exact ⟨w, fun x hx ↦ hone x hx w hw, fun h ↦ ha (h ▸ hw), fun h ↦ hb (h ▸ hw)⟩
  have hns : ∀ x : (cycle n).V, x ≠ v → x ∉ s := fun x hx hxs ↦ hx (hv x hxs)
  -- `f` is constant off `v`
  have hconstv : ∀ x : (cycle n).V, x ≠ v → f x = f (csucc h3 v) := by
    intro x
    refine forall_of_csucc_closed h3 (P := fun y ↦ y ≠ v → f y = f (csucc h3 v))
      (k := v) (fun hc ↦ absurd rfl hc) (fun i hi hne ↦ ?_) x
    by_cases hiv : i = v
    · rw [hiv]
    · rw [← hi hiv]
      exact (hconst i (csucc h3 i) (hns i hiv) (hns _ hne) (adj_csucc h3 i)).symm
  rw [hconstv a hva] at hfa
  rw [hconstv b hvb] at hfb
  rw [hfa] at hfb
  exact Bool.noConfusion hfb

/-- **A cycle is 2-connected.** -/
theorem two_le_vertexConn_cycle {n : ℕ} (h3 : 3 ≤ n) : 2 ≤ (cycle n).vertexConn :=
  (cycle n).le_vertexConn_of_forall_card_lt
    (by rw [show (cycle n).card = n from card_cycle n]; omega)
    fun s hs ↦ not_isSeparator_cycle h3 (by omega)

end CGraph

/-! ## The two connectivities on `IsoGraph`

Both are invariants, so both descend to the quotient; these are the `IsoGraph`-level copies of the
facts above, proved by `Quotient.inductionOn` and the agreement lemmas. -/

namespace IsoGraph

variable (G : IsoGraph)

/-- **Whitney's inequality**, first half: `κ ≤ λ`. -/
theorem vertexConn_le_edgeConn : G.vertexConn ≤ G.edgeConn := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [vertexConn_mk, edgeConn_mk]
  exact G.vertexConn_le_edgeConn

/-- **Whitney's inequality**, second half: `λ ≤ δ`. -/
theorem edgeConn_le_minDeg (h2 : 2 ≤ G.V) : G.edgeConn ≤ G.minDeg := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [edgeConn_mk, minDeg_mk, V_mk] at *
  exact G.edgeConn_le_minDeg h2

theorem vertexConn_le_minDeg (h2 : 2 ≤ G.V) : G.vertexConn ≤ G.minDeg :=
  le_trans G.vertexConn_le_edgeConn (G.edgeConn_le_minDeg h2)

theorem vertexConn_le_V_sub_one : G.vertexConn ≤ G.V - 1 := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [vertexConn_mk, V_mk]
  exact G.vertexConn_le_card_sub_one

theorem edgeConn_eq_zero_iff : G.edgeConn = 0 ↔ G.V ≤ 1 ∨ ¬ G.IsConnected := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [edgeConn_mk, V_mk, isConnected_mk]
  exact G.edgeConn_eq_zero_iff

theorem vertexConn_eq_zero_iff : G.vertexConn = 0 ↔ G.V ≤ 1 ∨ ¬ G.IsConnected := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [vertexConn_mk, V_mk, isConnected_mk]
  exact G.vertexConn_eq_zero_iff

theorem one_le_edgeConn_iff (h2 : 2 ≤ G.V) : 1 ≤ G.edgeConn ↔ G.IsConnected := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [edgeConn_mk, V_mk, isConnected_mk] at *
  exact G.one_le_edgeConn_iff h2

theorem one_le_vertexConn_iff (h2 : 2 ≤ G.V) : 1 ≤ G.vertexConn ↔ G.IsConnected := by
  induction G using Quotient.inductionOn with | _ G =>
  simp only [vertexConn_mk, V_mk, isConnected_mk] at *
  exact G.one_le_vertexConn_iff h2

@[simp] theorem edgeConn_complete (n : ℕ) : (complete n).edgeConn = n - 1 := by
  rw [complete_def, edgeConn_mk, CGraph.edgeConn_complete]

@[simp] theorem vertexConn_complete (n : ℕ) : (complete n).vertexConn = n - 1 := by
  rw [complete_def, vertexConn_mk, CGraph.vertexConn_complete]

end IsoGraph
