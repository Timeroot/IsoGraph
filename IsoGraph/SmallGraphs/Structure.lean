import IsoGraph.SmallGraphs.Counts
import IsoGraph.Invariants.Hamiltonian

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Connectivity, girth and distance in the named graphs

Connectivity, girth, radius, diameter and acyclicity of the named graphs and the parametrised
families, together with their edge and vertex connectivities and their Hamiltonicity.
-/

/-! ### Reading an LCF code

An LCF code is a list of signed steps and a repeat count; `lcfChord` and `IsValidLcf` say what it
means, and mention no graph at all.  They therefore live outside both `CGraph` and `IsoGraph`, and
a fact stated with them reads the same at either level. -/

/-- The chord the code `[ss]^r` hangs at vertex `i`: the entry `ss[i mod |ss|]`, read as a signed
step around the ring of `ss.length * r` vertices. -/
def lcfChord (ss : List ℤ) (r : ℕ) (i : ℕ) : ℕ :=
  ((((i : ℤ) + ss.getD (i % ss.length) 0) % (ss.length * r : ℕ)
      + (ss.length * r : ℕ)) % (ss.length * r : ℕ)).toNat

/-- **A valid LCF code**: the chords are a perfect matching on the ring, disjoint from it.  The
chord at `i` comes back to `i`, and it is neither `i` itself nor either of `i`'s ring neighbours.
Nothing in `lcfEdges` enforces any of this — an arbitrary list of steps need not even describe a
cubic graph — but every code in the gallery satisfies it, by `decide`. -/
def IsValidLcf (ss : List ℤ) (r : ℕ) : Prop :=
  ∀ i < ss.length * r,
    lcfChord ss r (lcfChord ss r i) = i ∧ lcfChord ss r i ≠ i ∧
      lcfChord ss r i ≠ (i + 1) % (ss.length * r) ∧
      lcfChord ss r i ≠ (i + ss.length * r - 1) % (ss.length * r)

instance (ss : List ℤ) (r : ℕ) : Decidable (IsValidLcf ss r) := by
  unfold IsValidLcf; infer_instance

namespace CGraph

section
open Fintype
variable (G H : CGraph)

@[simp] theorem isConnected_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).IsConnected := by
  rw [bipartite_eq_compl]
  simp only [CGraph.IsConnected, compl_toSimple]
  show SimpleGraph.Connected ((complete (m + 1)).disjUnion (complete (n + 1))).toSimpleᶜ
  have : Nonempty ((complete (m + 1)).disjUnion (complete (n + 1))).V :=
    ⟨Sum.inl ⟨0, Nat.zero_lt_succ _⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  -- The complement of a disjoint union of two complete graphs keeps exactly the crossing pairs:
  -- opposite sides are adjacent, and two vertices on the same side are joined in two hops.
  have h_cross_adj : ∀ (a : Fin (m + 1)) (b : Fin (n + 1)),
      ((complete (m + 1)).disjUnion (complete (n + 1))).toSimpleᶜ.Adj (Sum.inl a) (Sum.inr b) := by
    intro a b
    simp [SimpleGraph.compl_adj, CGraph.toSimple_adj, disjUnion_adj_inl_inr]
  have h_cross_adj2 : ∀ (a : Fin (m + 1)) (b : Fin (n + 1)),
      ((complete (m + 1)).disjUnion (complete (n + 1))).toSimpleᶜ.Adj (Sum.inr b) (Sum.inl a) := by
    intro a b
    simp [SimpleGraph.compl_adj, CGraph.toSimple_adj, disjUnion_adj_inr_inl]
  rcases u with ⟨a, ha⟩ | ⟨b, hb⟩ <;> rcases v with ⟨c, hc⟩ | ⟨d, hd⟩
  · -- inl → inl: hop through the right side
    exact (h_cross_adj ⟨a, ha⟩ ⟨0, Nat.zero_lt_succ n⟩).reachable.trans
      (h_cross_adj2 ⟨c, hc⟩ ⟨0, Nat.zero_lt_succ n⟩).reachable
  · -- inl → inr: direct
    exact (h_cross_adj ⟨a, ha⟩ ⟨d, hd⟩).reachable
  · -- inr → inl: direct
    exact (h_cross_adj2 ⟨c, hc⟩ ⟨b, hb⟩).reachable
  · -- inr → inr: hop through the left side
    exact (h_cross_adj2 ⟨0, Nat.zero_lt_succ m⟩ ⟨b, hb⟩).reachable.trans
      (h_cross_adj ⟨0, Nat.zero_lt_succ m⟩ ⟨d, hd⟩).reachable

end

section
variable {G H : CGraph}

@[toIsoGraph]
theorem diameter_join_le_two (G H : CGraph) [Nonempty G.V]
    [Nonempty H.V] : (G ∇g H).diameter ≤ 2 :=
  diameter_le_two _ (two_step_join G H)

/-- **A join has `λ = δ`.**  Every two vertices of `G ∇g H` are two steps apart at worst, so
Plesník's theorem applies and the edge connectivity is the minimum degree — no join is ever cheaper
to disconnect than its cheapest vertex is to isolate. -/
@[toIsoGraph]
theorem edgeConn_join_eq_minDeg (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    (G ∇g H).edgeConn = (G ∇g H).minDeg := by
  refine edgeConn_eq_minDeg_of_two_step _ ?_ (two_step_join G H)
  have hc : (G ∇g H).card = G.card + H.card := card_join G H
  have h1 : 0 < G.card := FinEnum.card_pos_iff.2 ‹Nonempty G.V›
  have h2 : 0 < H.card := FinEnum.card_pos_iff.2 ‹Nonempty H.V›
  omega

/-- **A strong product of two graphs of diameter at most two has `λ = δ`.**  The strong product
keeps the coordinates independent, so two steps in each factor combine into two steps in the
product and Plesník's theorem applies. -/
@[toIsoGraph]
theorem edgeConn_strongProduct_eq_minDeg (G H : CGraph) (hG : G.IsConnected) (hH : H.IsConnected)
    (hdG : G.diameter ≤ 2) (hdH : H.diameter ≤ 2) (h2 : 2 ≤ G.card * H.card) :
    (G ⊠g H).edgeConn = (G ⊠g H).minDeg := by
  have hc : (G ⊠g H).card = G.card * H.card := card_strongProduct G H
  exact edgeConn_eq_minDeg_of_two_step _ (by omega)
    (two_step_strongProduct G H (fun u v hne ↦ G.exists_adj_adj_of_diameter_le_two hG hdG hne)
      (fun u v hne ↦ H.exists_adj_adj_of_diameter_le_two hH hdH hne))

/-- **A blow-up of a graph of diameter at most two has `λ = δ`.**  The second factor is
unconstrained: a blow-up of a two-step graph is again two-step, whatever is put in the fibres. -/
@[toIsoGraph]
theorem edgeConn_lexProduct_eq_minDeg (G H : CGraph) (hG : G.IsConnected) (hdG : G.diameter ≤ 2)
    (h2 : 2 ≤ G.card) (hH : 1 ≤ H.card) :
    (G ·g H).edgeConn = (G ·g H).minDeg := by
  have hstep : ∀ u v : G.V, u ≠ v →
      G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v :=
    fun u v hne ↦ G.exists_adj_adj_of_diameter_le_two hG hdG hne
  have hc : (G ·g H).card = G.card * H.card := card_lexProduct G H
  have hm : 2 * 1 ≤ G.card * H.card := Nat.mul_le_mul h2 hH
  exact edgeConn_eq_minDeg_of_two_step _ (by omega)
    (two_step_lexProduct G H hstep (G.exists_adj_of_two_step h2 hstep))

/-- **The Mycielskian of a graph of diameter at most two again has diameter at most two.**  This
sharpens the general bound `diameter_mycielskian_le_four`. -/
@[toIsoGraph]
theorem diameter_mycielskian_le_two (G : CGraph) (hG : G.IsConnected) (hdG : G.diameter ≤ 2)
    (h2 : 2 ≤ G.card) : (mycielskian G).diameter ≤ 2 := by
  have hstep : ∀ u v : G.V, u ≠ v →
      G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v :=
    fun u v hne ↦ G.exists_adj_adj_of_diameter_le_two hG hdG hne
  exact diameter_le_two _ (two_step_mycielskian G hstep (G.exists_adj_of_two_step h2 hstep))

/-- **The Mycielskian of a graph of diameter at most two has `λ = δ`**, by Plesník's theorem and
`diameter_mycielskian_le_two`. -/
@[toIsoGraph]
theorem edgeConn_mycielskian_eq_minDeg (G : CGraph) (hG : G.IsConnected) (hdG : G.diameter ≤ 2)
    (h2 : 2 ≤ G.card) : (mycielskian G).edgeConn = (mycielskian G).minDeg := by
  have hstep : ∀ u v : G.V, u ≠ v →
      G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v :=
    fun u v hne ↦ G.exists_adj_adj_of_diameter_le_two hG hdG hne
  have hc : (mycielskian G).card = 2 * G.card + 1 := card_mycielskian G
  exact edgeConn_eq_minDeg_of_two_step _ (by omega)
    (two_step_mycielskian G hstep (G.exists_adj_of_two_step h2 hstep))

/-- **Plesník's theorem for diameter at most two**, in the form that also covers the complete
graphs: a connected graph of diameter at most two on two vertices or more has `λ = δ`. -/
@[toIsoGraph]
theorem edgeConn_eq_minDeg_of_diameter_le_two (G : CGraph) (hG : G.IsConnected)
    (hd : G.diameter ≤ 2) (h2 : 2 ≤ G.card) : G.edgeConn = G.minDeg :=
  edgeConn_eq_minDeg_of_two_step _ h2 fun _ _ hne ↦ G.exists_adj_adj_of_diameter_le_two hG hd hne

/-! ### The edge connectivity of a cartesian product

A cartesian product is a grid of copies of `G` — one *row* for each vertex of `H` — laid over a
grid of copies of `H` — one *column* for each vertex of `G`.  Every edge of `G □g H` lies in
exactly one of those copies, so an edge cut is nothing but a choice of a cut in each. -/

/-- The trace of a set of vertices of `G □g H` on the copy of `G` sitting over `x`. -/
def cartesianRow {G H : CGraph} (S : Finset (G.V × H.V)) (x : H.V) : Finset G.V :=
  Finset.univ.filter fun a ↦ (a, x) ∈ S

/-- The trace of a set of vertices of `G □g H` on the copy of `H` sitting over `a`. -/
def cartesianCol {G H : CGraph} (S : Finset (G.V × H.V)) (a : G.V) : Finset H.V :=
  Finset.univ.filter fun x ↦ (a, x) ∈ S

@[simp] theorem mem_cartesianRow {G H : CGraph} {S : Finset (G.V × H.V)} {x : H.V} {a : G.V} :
    a ∈ cartesianRow S x ↔ (a, x) ∈ S := by simp [cartesianRow]

@[simp] theorem mem_cartesianCol {G H : CGraph} {S : Finset (G.V × H.V)} {a : G.V} {x : H.V} :
    x ∈ cartesianCol S a ↔ (a, x) ∈ S := by simp [cartesianCol]

/-- Every edge leaving `S` in a cartesian product moves in exactly one coordinate, so the edges
leaving `S` are counted row by row and column by column. -/
theorem cutSize_cartesianProduct (G H : CGraph) (S : Finset (G.V × H.V)) :
    (G □g H).cutSize S
      = (∑ x : H.V, G.cutSize (cartesianRow S x)) + ∑ a : G.V, H.cutSize (cartesianCol S a) := by
  classical
  rw [cutSize, ← Finset.card_filter_add_card_filter_not
    (s := (G □g H).crossing S) (fun p ↦ p.1.2 = p.2.2)]
  congr 1
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun p ↦ p.1.2) (t := (Finset.univ : Finset H.V))
      (fun p _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [cutSize]
    refine Finset.card_nbij' (fun p ↦ (p.1.1, p.2.1)) (fun q ↦ ((q.1, x), (q.2, x)))
      (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun p hp ↦ ?_) (fun q _ ↦ rfl)
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, mem_crossing] at hp
      obtain ⟨⟨⟨h1, h2, hadj⟩, heq⟩, hx⟩ := hp
      rw [cartesianProduct_adj] at hadj
      have hg : G.Adj p.1.1 p.2.1 = true := by
        rcases Bool.or_eq_true_iff.1 hadj with h | h
        · rw [heq] at h; simp [H.loopless] at h
        · exact (Bool.and_eq_true_iff.1 h).1
      have h1' : (p.1.1, x) = p.1 := by rw [← hx]; rfl
      have h2' : (p.2.1, x) = p.2 := by rw [← hx, heq]; rfl
      refine Finset.mem_coe.2 (mem_crossing.2 ⟨?_, ?_, hg⟩)
      · rw [mem_cartesianRow, h1']; exact h1
      · rw [mem_cartesianRow, h2']; exact h2
    · rw [Finset.mem_coe, mem_crossing, mem_cartesianRow, mem_cartesianRow] at hq
      obtain ⟨hq1, hq2, hqa⟩ := hq
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_filter.2
        ⟨mem_crossing.2 ⟨hq1, hq2, ?_⟩, rfl⟩, rfl⟩)
      rw [cartesianProduct_adj]
      simp [hqa]
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨-, heq⟩, hx⟩ := hp
      have h1' : (p.1.1, x) = p.1 := by rw [← hx]; rfl
      have h2' : (p.2.1, x) = p.2 := by rw [← hx, heq]; rfl
      calc ((p.1.1, x), (p.2.1, x)) = (p.1, p.2) := by rw [h1', h2']
        _ = p := rfl
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun p ↦ p.1.1) (t := (Finset.univ : Finset G.V))
      (fun p _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [cutSize]
    refine Finset.card_nbij' (fun p ↦ (p.1.2, p.2.2)) (fun q ↦ ((a, q.1), (a, q.2)))
      (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun p hp ↦ ?_) (fun q _ ↦ rfl)
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, mem_crossing] at hp
      obtain ⟨⟨⟨h1, h2, hadj⟩, hne⟩, ha⟩ := hp
      rw [cartesianProduct_adj] at hadj
      have hfst : p.1.1 = p.2.1 ∧ H.Adj p.1.2 p.2.2 = true := by
        rcases Bool.or_eq_true_iff.1 hadj with h | h
        · obtain ⟨h', h''⟩ := Bool.and_eq_true_iff.1 h
          exact ⟨of_decide_eq_true h', h''⟩
        · exact absurd (of_decide_eq_true (Bool.and_eq_true_iff.1 h).2) hne
      have h1' : (a, p.1.2) = p.1 := by rw [← ha]; rfl
      have h2' : (a, p.2.2) = p.2 := by rw [← ha, hfst.1]; rfl
      refine Finset.mem_coe.2 (mem_crossing.2 ⟨?_, ?_, hfst.2⟩)
      · rw [mem_cartesianCol, h1']; exact h1
      · rw [mem_cartesianCol, h2']; exact h2
    · rw [Finset.mem_coe, mem_crossing, mem_cartesianCol, mem_cartesianCol] at hq
      obtain ⟨hq1, hq2, hqa⟩ := hq
      have hne : ¬ q.1 = q.2 := by
        intro h
        rw [h] at hqa
        simp [H.loopless] at hqa
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_filter.2
        ⟨mem_crossing.2 ⟨hq1, hq2, ?_⟩, hne⟩, rfl⟩)
      rw [cartesianProduct_adj]
      simp [hqa]
    · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, mem_crossing] at hp
      obtain ⟨⟨⟨-, -, hadj⟩, hne⟩, ha⟩ := hp
      rw [cartesianProduct_adj] at hadj
      have hfst : p.1.1 = p.2.1 := by
        rcases Bool.or_eq_true_iff.1 hadj with h | h
        · exact of_decide_eq_true (Bool.and_eq_true_iff.1 h).1
        · exact absurd (of_decide_eq_true (Bool.and_eq_true_iff.1 h).2) hne
      have h1' : (a, p.1.2) = p.1 := by rw [← ha]; rfl
      have h2' : (a, p.2.2) = p.2 := by rw [← ha, hfst]; rfl
      calc ((a, p.1.2), (a, p.2.2)) = (p.1, p.2) := by rw [h1', h2']
        _ = p := rfl

/-- Every edge cut of a cartesian product of two connected graphs is at least as big as the sum
of the two edge connectivities. -/
theorem edgeConn_add_edgeConn_le_cutSize_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) (hG2 : 2 ≤ G.card) (hH2 : 2 ≤ H.card)
    (S : Finset (G.V × H.V)) (hS : (G □g H).IsCut S) :
    G.edgeConn + H.edgeConn ≤ (G □g H).cutSize S := by
  classical
  have hGc : FinEnum.card G.V = G.card := rfl
  have hHc : FinEnum.card H.V = H.card := rfl
  have hGV : Nonempty G.V := FinEnum.card_pos_iff.1 (by omega)
  have hHV : Nonempty H.V := FinEnum.card_pos_iff.1 (by omega)
  have hlowG : 1 ≤ G.edgeConn := (G.one_le_edgeConn_iff hG2).2 hG
  have hlowH : 1 ≤ H.edgeConn := (H.one_le_edgeConn_iff hH2).2 hH
  have hcapG : G.edgeConn ≤ G.card - 1 := by
    have h1 := G.edgeConn_le_minDeg hG2
    have h2 := G.minDeg_le_maxDeg
    have h3 : G.maxDeg < FinEnum.card G.V := maxDeg_lt_card
    omega
  have hcapH : H.edgeConn ≤ H.card - 1 := by
    have h1 := H.edgeConn_le_minDeg hH2
    have h2 := H.minDeg_le_maxDeg
    have h3 : H.maxDeg < FinEnum.card H.V := maxDeg_lt_card
    omega
  rw [cutSize_cartesianProduct]
  by_cases hrow : ∃ x : H.V, G.IsCut (cartesianRow S x)
  · by_cases hcol : ∃ a : G.V, H.IsCut (cartesianCol S a)
    · obtain ⟨x, hx⟩ := hrow
      obtain ⟨a, ha⟩ := hcol
      have h1 : G.edgeConn ≤ ∑ y : H.V, G.cutSize (cartesianRow S y) :=
        le_trans (G.edgeConn_le_of_isCut hx)
          (Finset.single_le_sum (f := fun y ↦ G.cutSize (cartesianRow S y))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x))
      have h2 : H.edgeConn ≤ ∑ b : G.V, H.cutSize (cartesianCol S b) :=
        le_trans (H.edgeConn_le_of_isCut ha)
          (Finset.single_le_sum (f := fun b ↦ H.cutSize (cartesianCol S b))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a))
      omega
    · -- no column separates `H`, so every column is empty or everything and the rows all agree
      have hdich : ∀ a : G.V, cartesianCol S a = ∅ ∨ cartesianCol S a = Finset.univ := by
        intro a
        have h := not_exists.1 hcol a
        rw [IsCut, not_and_or, Finset.not_nonempty_iff_eq_empty,
          Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
        exact h
      set T : Finset G.V := Finset.univ.filter fun a ↦ cartesianCol S a = Finset.univ with hT
      have hrowT : ∀ x : H.V, cartesianRow S x = T := by
        intro x
        ext a
        simp only [mem_cartesianRow, hT, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hax
          rcases hdich a with h | h
          · exact absurd (mem_cartesianCol.2 hax) (by rw [h]; simp)
          · exact h
        · intro h
          exact mem_cartesianCol.1 (h ▸ Finset.mem_univ x)
      have hTcut : G.IsCut T := by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hS
        rw [Finset.mem_compl] at hq
        refine ⟨⟨p.1, ?_⟩, ⟨q.1, ?_⟩⟩
        · rw [← hrowT p.2]; exact mem_cartesianRow.2 hp
        · rw [Finset.mem_compl, ← hrowT q.2]
          exact fun h ↦ hq (mem_cartesianRow.1 h)
      have hsum : ∑ x : H.V, G.cutSize (cartesianRow S x) = H.card * G.cutSize T := by
        simp only [hrowT, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rw [show Fintype.card H.V = H.card from H.fintypeCard]
      have hcut : G.edgeConn ≤ G.cutSize T := G.edgeConn_le_of_isCut hTcut
      have hstep : G.edgeConn + H.edgeConn ≤ H.card * G.edgeConn := by
        have h : H.card - 1 ≤ (H.card - 1) * G.edgeConn := by
          simpa using Nat.mul_le_mul_left (H.card - 1) hlowG
        have hc : H.card = (H.card - 1) + 1 := by omega
        calc G.edgeConn + H.edgeConn ≤ (H.card - 1) * G.edgeConn + G.edgeConn := by omega
          _ = ((H.card - 1) + 1) * G.edgeConn := by ring
          _ = H.card * G.edgeConn := by rw [← hc]
      have hmono : H.card * G.edgeConn ≤ H.card * G.cutSize T := Nat.mul_le_mul_left _ hcut
      omega
  · -- no row separates `G`, so every row is empty or everything and the columns all agree
    have hdich : ∀ x : H.V, cartesianRow S x = ∅ ∨ cartesianRow S x = Finset.univ := by
      intro x
      have h := not_exists.1 hrow x
      rw [IsCut, not_and_or, Finset.not_nonempty_iff_eq_empty,
        Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
      exact h
    set T : Finset H.V := Finset.univ.filter fun x ↦ cartesianRow S x = Finset.univ with hT
    have hcolT : ∀ a : G.V, cartesianCol S a = T := by
      intro a
      ext x
      simp only [mem_cartesianCol, hT, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hax
        rcases hdich x with h | h
        · exact absurd (mem_cartesianRow.2 hax) (by rw [h]; simp)
        · exact h
      · intro h
        exact mem_cartesianRow.1 (h ▸ Finset.mem_univ a)
    have hTcut : H.IsCut T := by
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hS
      rw [Finset.mem_compl] at hq
      refine ⟨⟨p.2, ?_⟩, ⟨q.2, ?_⟩⟩
      · rw [← hcolT p.1]; exact mem_cartesianCol.2 hp
      · rw [Finset.mem_compl, ← hcolT q.1]
        exact fun h ↦ hq (mem_cartesianCol.1 h)
    have hsum : ∑ a : G.V, H.cutSize (cartesianCol S a) = G.card * H.cutSize T := by
      simp only [hcolT, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [show Fintype.card G.V = G.card from G.fintypeCard]
    have hcut : H.edgeConn ≤ H.cutSize T := H.edgeConn_le_of_isCut hTcut
    have hstep : G.edgeConn + H.edgeConn ≤ G.card * H.edgeConn := by
      have h : G.card - 1 ≤ (G.card - 1) * H.edgeConn := by
        simpa using Nat.mul_le_mul_left (G.card - 1) hlowH
      have hc : G.card = (G.card - 1) + 1 := by omega
      calc G.edgeConn + H.edgeConn ≤ (G.card - 1) * H.edgeConn + H.edgeConn := by omega
        _ = ((G.card - 1) + 1) * H.edgeConn := by ring
        _ = G.card * H.edgeConn := by rw [← hc]
    have hmono : G.card * H.edgeConn ≤ G.card * H.cutSize T := Nat.mul_le_mul_left _ hcut
    omega

/-- **The edge connectivity of a cartesian product is superadditive**: `λ(G □ H) ≥ λG + λH`.
An edge cut of `G □ H` either separates some copy of `G` and some copy of `H` — and then it
contains a cut of each — or else it is a whole slab of copies, and then it contains `|G|` or
`|H|` copies of a cut of a single factor. -/
@[toIsoGraph]
theorem edgeConn_add_edgeConn_le_edgeConn_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) (hG2 : 2 ≤ G.card) (hH2 : 2 ≤ H.card) :
    G.edgeConn + H.edgeConn ≤ (G □g H).edgeConn := by
  have hc : (G □g H).card = G.card * H.card := card_cartesianProduct G H
  have h4 : 2 * 2 ≤ G.card * H.card := Nat.mul_le_mul hG2 hH2
  exact (G □g H).le_edgeConn (by omega)
    (edgeConn_add_edgeConn_le_cutSize_cartesianProduct G H hG hH hG2 hH2)

/-! ### The vertex connectivity of a cartesian product -/

/-- A subset of `G □g H` is counted row by row. -/
theorem card_eq_sum_card_cartesianRow {G H : CGraph} (S : Finset (G.V × H.V)) :
    S.card = ∑ x : H.V, (cartesianRow S x).card := by
  classical
  have h : S.card = ∑ p : G.V × H.V, if p ∈ S then 1 else 0 := by simp
  rw [h, Fintype.sum_prod_type]
  simp only [cartesianRow, Finset.card_filter]
  exact Finset.sum_comm

/-- A subset of `G □g H` is counted column by column. -/
theorem card_eq_sum_card_cartesianCol {G H : CGraph} (S : Finset (G.V × H.V)) :
    S.card = ∑ a : G.V, (cartesianCol S a).card := by
  classical
  have h : S.card = ∑ p : G.V × H.V, if p ∈ S then 1 else 0 := by simp
  rw [h, Fintype.sum_prod_type]
  simp only [cartesianCol, Finset.card_filter]

/-- If a colouring witnessing that `S` separates `G □g H` takes both values on the copy of `G`
sitting over `x`, then the trace of `S` on that copy separates `G`. -/
theorem isSeparator_cartesianRow {G H : CGraph} {S : Finset (G.V × H.V)}
    {f : (G □g H).V → Bool}
    (hf : ∀ u v : (G □g H).V, u ∉ S → v ∉ S → (G □g H).Adj u v = true → f u = f v)
    (x : H.V) {a b : G.V} (ha : (a, x) ∉ S) (hb : (b, x) ∉ S) (hab : f (a, x) ≠ f (b, x)) :
    G.IsSeparator (cartesianRow S x) := by
  classical
  have hadj : ∀ u v : G.V, G.Adj u v = true → (G □g H).Adj (u, x) (v, x) = true := by
    intro u v h
    rw [cartesianProduct_adj]
    simp [h]
  have hcase : (f (a, x) = true ∧ f (b, x) = false) ∨ (f (a, x) = false ∧ f (b, x) = true) := by
    revert hab
    cases hfa : f (a, x) <;> cases hfb : f (b, x) <;> simp
  refine ⟨fun c ↦ f (c, x), ?_, ?_, fun u v hu hv huv ↦
    hf (u, x) (v, x) (by simpa using hu) (by simpa using hv) (hadj u v huv)⟩
  · rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
    · exact ⟨a, by simpa using ha, h⟩
    · exact ⟨b, by simpa using hb, h⟩
  · rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact ⟨b, by simpa using hb, h⟩
    · exact ⟨a, by simpa using ha, h⟩

/-- A colouring that is constant along the edges of `H` inside the fibre over `a`, and that takes
both values there, exhibits the trace of `S` on that fibre as a separator of `H`.  The fibres of
the cartesian and of the lexicographic product both carry the adjacency of `H`, so both can appeal
to this. -/
theorem isSeparator_cartesianCol_of_forall {G H : CGraph} {S : Finset (G.V × H.V)}
    {f : G.V × H.V → Bool} {a : G.V}
    (hf : ∀ u v : H.V, (a, u) ∉ S → (a, v) ∉ S → H.Adj u v = true → f (a, u) = f (a, v))
    {x y : H.V} (hx : (a, x) ∉ S) (hy : (a, y) ∉ S) (hxy : f (a, x) ≠ f (a, y)) :
    H.IsSeparator (cartesianCol S a) := by
  classical
  have hcase : (f (a, x) = true ∧ f (a, y) = false) ∨ (f (a, x) = false ∧ f (a, y) = true) := by
    revert hxy
    cases hfx : f (a, x) <;> cases hfy : f (a, y) <;> simp
  refine ⟨fun z ↦ f (a, z), ?_, ?_, fun u v hu hv huv ↦
    hf u v (by simpa using hu) (by simpa using hv) huv⟩
  · rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
    · exact ⟨x, by simpa using hx, h⟩
    · exact ⟨y, by simpa using hy, h⟩
  · rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact ⟨y, by simpa using hy, h⟩
    · exact ⟨x, by simpa using hx, h⟩

/-- If a colouring witnessing that `S` separates `G □g H` takes both values on the copy of `H`
sitting over `a`, then the trace of `S` on that copy separates `H`. -/
theorem isSeparator_cartesianCol {G H : CGraph} {S : Finset (G.V × H.V)}
    {f : (G □g H).V → Bool}
    (hf : ∀ u v : (G □g H).V, u ∉ S → v ∉ S → (G □g H).Adj u v = true → f u = f v)
    (a : G.V) {x y : H.V} (hx : (a, x) ∉ S) (hy : (a, y) ∉ S) (hxy : f (a, x) ≠ f (a, y)) :
    H.IsSeparator (cartesianCol S a) :=
  isSeparator_cartesianCol_of_forall
    (fun u v hu hv huv ↦ hf (a, u) (a, v) hu hv (by rw [cartesianProduct_adj]; simp [huv]))
    hx hy hxy

/-- Every separator of a cartesian product of two connected graphs is at least as big as the sum
of the two vertex connectivities. -/
theorem vertexConn_add_vertexConn_le_card_of_isSeparator (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) (hG2 : 2 ≤ G.card) (hH2 : 2 ≤ H.card)
    (S : Finset (G.V × H.V)) (hS : (G □g H).IsSeparator S) :
    G.vertexConn + H.vertexConn ≤ S.card := by
  classical
  obtain ⟨f, ⟨p₀, hp₀S, hp₀⟩, ⟨q₀, hq₀S, hq₀⟩, hf⟩ := hS
  obtain ⟨a₀, y₀⟩ := p₀
  obtain ⟨a₁, y₁⟩ := q₀
  have hGcard : Fintype.card G.V = G.card := G.fintypeCard
  have hHcard : Fintype.card H.V = H.card := H.fintypeCard
  have hkG1 : 1 ≤ G.vertexConn := (G.one_le_vertexConn_iff hG2).2 hG
  have hkH1 : 1 ≤ H.vertexConn := (H.one_le_vertexConn_iff hH2).2 hH
  have hkGn : G.vertexConn ≤ G.card - 1 := G.vertexConn_le_card_sub_one
  have hkHn : H.vertexConn ≤ H.card - 1 := H.vertexConn_le_card_sub_one
  have hrow : ∀ (x : H.V) (a b : G.V), (a, x) ∉ S → (b, x) ∉ S → f (a, x) ≠ f (b, x) →
      G.vertexConn ≤ (cartesianRow S x).card :=
    fun x a b ha hb hab ↦ G.vertexConn_le_of_isSeparator (isSeparator_cartesianRow hf x ha hb hab)
  have hcol : ∀ (a : G.V) (x y : H.V), (a, x) ∉ S → (a, y) ∉ S → f (a, x) ≠ f (a, y) →
      H.vertexConn ≤ (cartesianCol S a).card :=
    fun a x y hx hy hxy ↦ H.vertexConn_le_of_isSeparator (isSeparator_cartesianCol hf a hx hy hxy)
  have hsumRow : S.card = ∑ x : H.V, (cartesianRow S x).card := card_eq_sum_card_cartesianRow S
  have hsumCol : S.card = ∑ a : G.V, (cartesianCol S a).card := card_eq_sum_card_cartesianCol S
  by_cases hcolBi : ∃ (a : G.V) (x y : H.V), (a, x) ∉ S ∧ (a, y) ∉ S ∧ f (a, x) ≠ f (a, y)
  · -- Some copy of `H` sees both colours, so its trace already contains a separator of `H`.
    obtain ⟨c, xT, xF, hxT, hxF, hxne⟩ := hcolBi
    have hCc : H.vertexConn ≤ (cartesianCol S c).card := hcol c xT xF hxT hxF hxne
    by_cases hmix : ∃ (x : H.V) (a b : G.V),
        (c, x) ∉ S ∧ (a, x) ∉ S ∧ (b, x) ∉ S ∧ f (a, x) ≠ f (b, x)
    · -- A row that meets the copy of `H` over `c` is bichromatic: the two traces are disjoint.
      obtain ⟨x, a, b, hcx, ha, hb, hab⟩ := hmix
      have hRx : G.vertexConn ≤ (cartesianRow S x).card := hrow x a b ha hb hab
      have hdisj : Disjoint ((cartesianRow S x).image (fun d ↦ (d, x)))
          ((cartesianCol S c).image (fun y ↦ (c, y))) := by
        rw [Finset.disjoint_left]
        rintro p hp hq
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨y, hy, hpy⟩ := Finset.mem_image.1 hq
        have h1 : c = d := congrArg Prod.fst hpy
        subst h1
        exact hcx (mem_cartesianRow.1 hd)
      have hsub : (cartesianRow S x).image (fun d ↦ (d, x)) ∪
          (cartesianCol S c).image (fun y ↦ (c, y)) ⊆ S := by
        intro p hp
        rcases Finset.mem_union.1 hp with h | h
        · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 h
          exact mem_cartesianRow.1 hd
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
          exact mem_cartesianCol.1 hy
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun d d' hd ↦ congrArg Prod.fst hd),
        Finset.card_image_of_injective _ (fun y y' hy ↦ congrArg Prod.snd hy)] at hcard
      omega
    · -- Otherwise every row through that copy is monochromatic, so every column meets `S`.
      push Not at hmix
      have hall : ∀ a : G.V, 1 ≤ (cartesianCol S a).card := by
        intro a
        by_cases h1 : (a, xT) ∈ S
        · exact Finset.card_pos.2 ⟨xT, mem_cartesianCol.2 h1⟩
        by_cases h2 : (a, xF) ∈ S
        · exact Finset.card_pos.2 ⟨xF, mem_cartesianCol.2 h2⟩
        have e1 : f (a, xT) = f (c, xT) := hmix xT a c hxT h1 hxT
        have e2 : f (a, xF) = f (c, xF) := hmix xF a c hxF h2 hxF
        have hne : f (a, xT) ≠ f (a, xF) := by rw [e1, e2]; exact hxne
        exact le_trans hkH1 (hcol a xT xF h1 h2 hne)
      have hsplit : (cartesianCol S c).card + ∑ a ∈ Finset.univ.erase c, (cartesianCol S a).card
          = ∑ a : G.V, (cartesianCol S a).card :=
        Finset.add_sum_erase Finset.univ (fun a ↦ (cartesianCol S a).card) (Finset.mem_univ c)
      have hge : (Finset.univ.erase c).card
          ≤ ∑ a ∈ Finset.univ.erase c, (cartesianCol S a).card := by
        calc (Finset.univ.erase c).card = ∑ _a ∈ Finset.univ.erase c, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ _ := Finset.sum_le_sum fun a _ ↦ hall a
      have herase : (Finset.univ.erase c).card = G.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, hGcard]
      omega
  · push Not at hcolBi
    by_cases hrowBi : ∃ (x : H.V) (a b : G.V), (a, x) ∉ S ∧ (b, x) ∉ S ∧ f (a, x) ≠ f (b, x)
    · -- No column is bichromatic but some row is: every row now meets `S`.
      obtain ⟨w, aT, aF, haT, haF, hane⟩ := hrowBi
      have hRw : G.vertexConn ≤ (cartesianRow S w).card := hrow w aT aF haT haF hane
      have hall : ∀ y : H.V, 1 ≤ (cartesianRow S y).card := by
        intro y
        by_cases h1 : (aT, y) ∈ S
        · exact Finset.card_pos.2 ⟨aT, mem_cartesianRow.2 h1⟩
        by_cases h2 : (aF, y) ∈ S
        · exact Finset.card_pos.2 ⟨aF, mem_cartesianRow.2 h2⟩
        have e1 : f (aT, y) = f (aT, w) := hcolBi aT y w h1 haT
        have e2 : f (aF, y) = f (aF, w) := hcolBi aF y w h2 haF
        have hne : f (aT, y) ≠ f (aF, y) := by rw [e1, e2]; exact hane
        exact le_trans hkG1 (hrow y aT aF h1 h2 hne)
      have hsplit : (cartesianRow S w).card + ∑ y ∈ Finset.univ.erase w, (cartesianRow S y).card
          = ∑ y : H.V, (cartesianRow S y).card :=
        Finset.add_sum_erase Finset.univ (fun y ↦ (cartesianRow S y).card) (Finset.mem_univ w)
      have hge : (Finset.univ.erase w).card
          ≤ ∑ y ∈ Finset.univ.erase w, (cartesianRow S y).card := by
        calc (Finset.univ.erase w).card = ∑ _y ∈ Finset.univ.erase w, 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ _ := Finset.sum_le_sum fun y _ ↦ hall y
      have herase : (Finset.univ.erase w).card = H.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, hHcard]
      omega
    · -- No row and no column is bichromatic: the colour of a vertex off `S` depends on neither
      -- coordinate alone, and counting the rows against the columns gives `|S| ≥ n + m - 2`.
      push Not at hrowBi
      obtain ⟨AT, hAT⟩ : ∃ T : Finset G.V, ∀ a, a ∈ T ↔ ∃ y : H.V, (a, y) ∉ S ∧ f (a, y) = true :=
        ⟨Finset.univ.filter (fun a ↦ ∃ y : H.V, (a, y) ∉ S ∧ f (a, y) = true), by simp⟩
      obtain ⟨AF, hAF⟩ : ∃ T : Finset G.V, ∀ a, a ∈ T ↔ ∃ y : H.V, (a, y) ∉ S ∧ f (a, y) = false :=
        ⟨Finset.univ.filter (fun a ↦ ∃ y : H.V, (a, y) ∉ S ∧ f (a, y) = false), by simp⟩
      obtain ⟨BT, hBT⟩ : ∃ T : Finset H.V, ∀ x, x ∈ T ↔ ∃ b : G.V, (b, x) ∉ S ∧ f (b, x) = true :=
        ⟨Finset.univ.filter (fun x ↦ ∃ b : G.V, (b, x) ∉ S ∧ f (b, x) = true), by simp⟩
      obtain ⟨Z, hZ⟩ : ∃ T : Finset G.V, ∀ a, a ∈ T ↔ (a ∉ AT ∧ a ∉ AF) :=
        ⟨Finset.univ \ (AT ∪ AF), by intro a; simp⟩
      have hATa₀ : a₀ ∈ AT := (hAT a₀).2 ⟨y₀, hp₀S, hp₀⟩
      have hAFa₁ : a₁ ∈ AF := (hAF a₁).2 ⟨y₁, hq₀S, hq₀⟩
      have hBTy₀ : y₀ ∈ BT := (hBT y₀).2 ⟨a₀, hp₀S, hp₀⟩
      have hBTy₁ : y₁ ∉ BT := by
        intro h
        obtain ⟨b, hb, hbt⟩ := (hBT y₁).1 h
        have hbb := hrowBi y₁ b a₁ hb hq₀S
        rw [hbt, hq₀] at hbb
        simp at hbb
      have hdisjA : Disjoint AT AF := by
        rw [Finset.disjoint_left]
        intro a hat haf
        obtain ⟨y, hy, hyt⟩ := (hAT a).1 hat
        obtain ⟨y', hy', hyf⟩ := (hAF a).1 haf
        have hcc := hcolBi a y y' hy hy'
        rw [hyt, hyf] at hcc
        simp at hcc
      have hcardZ : Z.card + (AT.card + AF.card) = G.card := by
        have hZeq : Z = Finset.univ \ (AT ∪ AF) := by ext a; rw [hZ]; simp
        rw [hZeq, ← Finset.card_union_of_disjoint hdisjA,
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, hGcard]
      have hcardB : (Finset.univ \ BT).card + BT.card = H.card := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, hHcard]
      have hp1 : 1 ≤ AT.card := Finset.card_pos.2 ⟨a₀, hATa₀⟩
      have hq1 : 1 ≤ AF.card := Finset.card_pos.2 ⟨a₁, hAFa₁⟩
      have hr1 : 1 ≤ BT.card := Finset.card_pos.2 ⟨y₀, hBTy₀⟩
      have hs1 : 1 ≤ (Finset.univ \ BT).card :=
        Finset.card_pos.2 ⟨y₁, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hBTy₁⟩⟩
      have hrowB : ∀ x ∈ BT, AF.card + Z.card ≤ (cartesianRow S x).card := by
        intro x hx
        obtain ⟨b, hb, hbt⟩ := (hBT x).1 hx
        have hsub : AF ∪ Z ⊆ cartesianRow S x := by
          intro a ha
          rw [mem_cartesianRow]
          by_contra hmem
          rcases Finset.mem_union.1 ha with h | h
          · obtain ⟨y, hy, hyf⟩ := (hAF a).1 h
            have e1 : f (a, x) = f (b, x) := hrowBi x a b hmem hb
            have e2 : f (a, x) = f (a, y) := hcolBi a x y hmem hy
            rw [hbt] at e1
            rw [hyf, e1] at e2
            simp at e2
          · have hz := (hZ a).1 h
            cases hfx : f (a, x)
            · exact hz.2 ((hAF a).2 ⟨x, hmem, hfx⟩)
            · exact hz.1 ((hAT a).2 ⟨x, hmem, hfx⟩)
        have hd : Disjoint AF Z := by
          rw [Finset.disjoint_left]
          intro a haf haz
          exact ((hZ a).1 haz).2 haf
        calc AF.card + Z.card = (AF ∪ Z).card := (Finset.card_union_of_disjoint hd).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hrowNB : ∀ x ∈ Finset.univ \ BT, AT.card + Z.card ≤ (cartesianRow S x).card := by
        intro x hx
        have hxn : x ∉ BT := (Finset.mem_sdiff.1 hx).2
        have hsub : AT ∪ Z ⊆ cartesianRow S x := by
          intro a ha
          rw [mem_cartesianRow]
          by_contra hmem
          rcases Finset.mem_union.1 ha with h | h
          · obtain ⟨y, hy, hyt⟩ := (hAT a).1 h
            have e2 : f (a, x) = f (a, y) := hcolBi a x y hmem hy
            rw [hyt] at e2
            exact hxn ((hBT x).2 ⟨a, hmem, e2⟩)
          · have hz := (hZ a).1 h
            cases hfx : f (a, x)
            · exact hz.2 ((hAF a).2 ⟨x, hmem, hfx⟩)
            · exact hz.1 ((hAT a).2 ⟨x, hmem, hfx⟩)
        have hd : Disjoint AT Z := by
          rw [Finset.disjoint_left]
          intro a hat haz
          exact ((hZ a).1 haz).1 hat
        calc AT.card + Z.card = (AT ∪ Z).card := (Finset.card_union_of_disjoint hd).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hsplit : ∑ x ∈ Finset.univ \ BT, (cartesianRow S x).card
          + ∑ x ∈ BT, (cartesianRow S x).card = ∑ x : H.V, (cartesianRow S x).card :=
        Finset.sum_sdiff (Finset.subset_univ BT)
      have hb1 : BT.card * (AF.card + Z.card) ≤ ∑ x ∈ BT, (cartesianRow S x).card := by
        calc BT.card * (AF.card + Z.card) = ∑ _x ∈ BT, (AF.card + Z.card) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum hrowB
      have hb2 : (Finset.univ \ BT).card * (AT.card + Z.card)
          ≤ ∑ x ∈ Finset.univ \ BT, (cartesianRow S x).card := by
        calc (Finset.univ \ BT).card * (AT.card + Z.card)
            = ∑ _x ∈ Finset.univ \ BT, (AT.card + Z.card) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum hrowNB
      have hmulle : ∀ u v : ℕ, 1 ≤ u → 1 ≤ v → u + v ≤ u * v + 1 := by
        intro u v hu hv
        obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hu
        obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hv
        have hexp : (1 + u) * (1 + v) = 1 + u + v + u * v := by ring
        omega
      have hexp1 : BT.card * (AF.card + Z.card) = BT.card * AF.card + BT.card * Z.card := by ring
      have hexp2 : (Finset.univ \ BT).card * (AT.card + Z.card)
          = (Finset.univ \ BT).card * AT.card + (Finset.univ \ BT).card * Z.card := by ring
      have hm1 : BT.card + AF.card ≤ BT.card * AF.card + 1 := hmulle _ _ hr1 hq1
      have hm2 : (Finset.univ \ BT).card + AT.card
          ≤ (Finset.univ \ BT).card * AT.card + 1 := hmulle _ _ hs1 hp1
      have hz1 : Z.card ≤ BT.card * Z.card := Nat.le_mul_of_pos_left _ hr1
      have hz2 : Z.card ≤ (Finset.univ \ BT).card * Z.card := Nat.le_mul_of_pos_left _ hs1
      omega

/-- **The vertex connectivity of a cartesian product is superadditive**: `κ(G □ H) ≥ κG + κH`.
A separator of `G □ H` either meets a bichromatic copy of `G` and a bichromatic copy of `H` in
disjoint sets — and then it contains a separator of each — or the colouring is forced to depend on
both coordinates at once, and then every one of the `|H|` rows already costs a whole side of the
partition of `G`. -/
@[toIsoGraph]
theorem vertexConn_add_vertexConn_le_vertexConn_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) (hG2 : 2 ≤ G.card) (hH2 : 2 ≤ H.card) :
    G.vertexConn + H.vertexConn ≤ (G □g H).vertexConn := by
  have hc : (G □g H).card = G.card * H.card := card_cartesianProduct G H
  have hkG := G.vertexConn_le_card_sub_one
  have hkH := H.vertexConn_le_card_sub_one
  have hbig : G.card + H.card ≤ G.card * H.card := Nat.add_le_mul hG2 hH2
  exact (G □g H).le_vertexConn (by omega)
    fun S hS ↦ vertexConn_add_vertexConn_le_card_of_isSeparator G H hG hH hG2 hH2 S hS

/-- The cartesian product is a spanning subgraph of the strong product, so anything that separates
the strong product separates the cartesian product as well. -/
theorem isSeparator_cartesianProduct_of_strongProduct {G H : CGraph} {S : Finset (G.V × H.V)}
    (hS : (G ⊠g H).IsSeparator S) : (G □g H).IsSeparator S := by
  obtain ⟨f, htrue, hfalse, hadj⟩ := hS
  refine ⟨f, htrue, hfalse, fun u v hu hv huv ↦ hadj u v hu hv ?_⟩
  rw [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at huv
  rw [strongProduct_adj]
  rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hne : u ≠ v := fun he ↦ by rw [he] at h2; simp [H.loopless] at h2
    simp [hne, h1, h2]
  · have hne : u ≠ v := fun he ↦ by rw [he] at h1; simp [G.loopless] at h1
    simp [hne, h1, h2]

/-- **The vertex connectivity of a strong product is superadditive**: `κ(G ⊠ H) ≥ κG + κH`.  The
strong product has every edge of the cartesian product, so a separator of it separates the
cartesian product too and the bound above carries over. -/
@[toIsoGraph]
theorem vertexConn_add_vertexConn_le_vertexConn_strongProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) (hG2 : 2 ≤ G.card) (hH2 : 2 ≤ H.card) :
    G.vertexConn + H.vertexConn ≤ (G ⊠g H).vertexConn := by
  have hc : (G ⊠g H).card = G.card * H.card := card_strongProduct G H
  have hkG := G.vertexConn_le_card_sub_one
  have hkH := H.vertexConn_le_card_sub_one
  have hbig : G.card + H.card ≤ G.card * H.card := Nat.add_le_mul hG2 hH2
  exact (G ⊠g H).le_vertexConn (by omega) fun S hS ↦
    vertexConn_add_vertexConn_le_card_of_isSeparator G H hG hH hG2 hH2 S
      (isSeparator_cartesianProduct_of_strongProduct hS)

/-! ### The connectivity of a lexicographic product

The lexicographic product `G ·g H` replaces every vertex of `G` by a copy of `H` and joins two
copies completely whenever the two vertices were adjacent.  A separator either swallows whole
copies — and then the copies it swallows separate `G` — or it leaves a single copy standing and
separates `H` inside it. -/

/-- Inside one fibre of `G ·g H` the adjacency is that of `H`. -/
theorem lexProduct_adj_self {G H : CGraph} (a : G.V) (x y : H.V) :
    (G ·g H).Adj (a, x) (a, y) = H.Adj x y := by
  rw [lexProduct_adj]
  simp [G.loopless]

/-- Two adjacent fibres of `G ·g H` are completely joined. -/
theorem lexProduct_adj_of_adj {G H : CGraph} {a b : G.V} (h : G.Adj a b = true) (x y : H.V) :
    (G ·g H).Adj (a, x) (b, y) = true := by
  rw [lexProduct_adj]
  simp [h]

/-- **Every separator of a lexicographic product is large.**  A separator `S` of `G ·g H` either
swallows enough whole fibres to separate `G` — and then it swallows at least `κ(G)` of them — or
it leaves exactly one fibre standing, and then it swallows all the others and separates `H`
inside the one that is left. -/
theorem min_le_card_of_isSeparator_lexProduct (G H : CGraph)
    (S : Finset (G.V × H.V)) (hS : (G ·g H).IsSeparator S) :
    min (G.vertexConn * H.card) ((G.card - 1) * H.card + H.vertexConn) ≤ S.card := by
  classical
  obtain ⟨f, ⟨p₀, hp₀S, hp₀⟩, ⟨q₀, hq₀S, hq₀⟩, hf⟩ := hS
  obtain ⟨a₀, y₀⟩ := p₀
  obtain ⟨a₁, y₁⟩ := q₀
  have hGcard : Fintype.card G.V = G.card := G.fintypeCard
  have hHcard : Fintype.card H.V = H.card := H.fintypeCard
  -- `T` collects the fibres that `S` swallows whole.
  obtain ⟨T, hT⟩ : ∃ T : Finset G.V, ∀ a, a ∈ T ↔ cartesianCol S a = Finset.univ :=
    ⟨Finset.univ.filter fun a ↦ cartesianCol S a = Finset.univ, by simp⟩
  have hfull : ∀ a ∈ T, ∀ x : H.V, (a, x) ∈ S := fun a ha x ↦
    mem_cartesianCol.1 (by rw [(hT a).1 ha]; exact Finset.mem_univ x)
  have hfree : ∀ a : G.V, a ∉ T → ∃ x : H.V, (a, x) ∉ S := by
    intro a ha
    by_contra hcon
    push Not at hcon
    exact ha ((hT a).2 (Finset.eq_univ_iff_forall.2 fun x ↦ mem_cartesianCol.2 (hcon x)))
  have ha₀ : a₀ ∉ T := fun h ↦ hp₀S (hfull a₀ h y₀)
  have ha₁ : a₁ ∉ T := fun h ↦ hq₀S (hfull a₁ h y₁)
  have hTle : T.card * H.card ≤ S.card := by
    have hsub : T ×ˢ (Finset.univ : Finset H.V) ⊆ S := fun p hp ↦
      hfull p.1 (Finset.mem_product.1 hp).1 p.2
    have h := Finset.card_le_card hsub
    rwa [Finset.card_product, Finset.card_univ, hHcard] at h
  by_cases hsep : G.IsSeparator T
  · exact le_trans (min_le_left _ _)
      (le_trans (Nat.mul_le_mul (G.vertexConn_le_of_isSeparator hsep) (le_refl H.card)) hTle)
  -- `T` does not separate `G`, so each colour spreads from any fibre that shows it to all the
  -- fibres that are left standing.
  have hspread : ∀ (c : Bool) (a : G.V) (x : H.V), (a, x) ∉ S → f (a, x) = c →
      ∀ b : G.V, b ∉ T → ∃ y : H.V, (b, y) ∉ S ∧ f (b, y) = c := by
    intro c a x hax hfx b hb
    by_contra hcon
    have haT : a ∉ T := fun h ↦ hax (hfull a h x)
    refine hsep ⟨fun d ↦ decide (∃ y : H.V, (d, y) ∉ S ∧ f (d, y) = c),
      ⟨a, haT, decide_eq_true ⟨x, hax, hfx⟩⟩, ⟨b, hb, decide_eq_false hcon⟩, ?_⟩
    have key : ∀ s t : G.V, t ∉ T → G.Adj s t = true →
        (∃ y : H.V, (s, y) ∉ S ∧ f (s, y) = c) → ∃ y : H.V, (t, y) ∉ S ∧ f (t, y) = c := by
      rintro s t ht hst ⟨y, hy, hfy⟩
      obtain ⟨z, hz⟩ := hfree t ht
      exact ⟨z, hz, by
        rw [← hfy]
        exact (hf (s, y) (t, z) hy hz (lexProduct_adj_of_adj hst y z)).symm⟩
    intro u v hu hv huv
    rw [decide_eq_decide]
    exact ⟨key u v hv huv, key v u hu (by rw [← G.symm u v]; exact huv)⟩
  -- Hence every standing fibre shows both colours.
  have hbiT : ∀ (c : Bool) (b : G.V), b ∉ T → ∃ y : H.V, (b, y) ∉ S ∧ f (b, y) = c := by
    intro c b hb
    cases c
    · exact hspread false a₁ y₁ hq₀S hq₀ b hb
    · exact hspread true a₀ y₀ hp₀S hp₀ b hb
  -- Two standing fibres cannot be adjacent: they would be completely joined, and one of them
  -- shows a vertex coloured `true` while the other shows one coloured `false`.
  have hnoadj : ∀ u v : G.V, u ∉ T → v ∉ T → G.Adj u v = true → False := by
    intro u v hu hv huv
    obtain ⟨y, hy, hfy⟩ := hbiT true u hu
    obtain ⟨z, hz, hfz⟩ := hbiT false v hv
    have h := hf (u, y) (v, z) hy hz (lexProduct_adj_of_adj huv y z)
    rw [hfy, hfz] at h
    simp at h
  -- So if two fibres were standing, *any* colouring would witness that `T` separates `G`.
  have huniq : ∀ u v : G.V, u ∉ T → v ∉ T → u = v := by
    intro u v hu hv
    by_contra hne
    exact hsep ⟨fun d ↦ decide (d = u), ⟨u, hu, decide_eq_true rfl⟩,
      ⟨v, hv, decide_eq_false fun h ↦ hne h.symm⟩,
      fun s t hs ht hst ↦ (hnoadj s t hs ht hst).elim⟩
  -- Exactly one fibre stands, and `S` separates `H` inside it.
  have hTcard : G.card - 1 ≤ T.card := by
    have hsub : Finset.univ.erase a₀ ⊆ T := by
      intro b hb
      by_contra hbT
      exact (Finset.mem_erase.1 hb).1 (huniq b a₀ hbT ha₀)
    have h := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ, hGcard] at h
  have hcolsep : H.IsSeparator (cartesianCol S a₀) := by
    obtain ⟨y, hy, hfy⟩ := hbiT true a₀ ha₀
    obtain ⟨z, hz, hfz⟩ := hbiT false a₀ ha₀
    refine isSeparator_cartesianCol_of_forall (S := S) (f := f) (a := a₀) ?_ hy hz
      (by rw [hfy, hfz]; simp)
    intro u v hu hv huv
    exact hf (a₀, u) (a₀, v) hu hv (by rw [lexProduct_adj_self]; exact huv)
  have hHle : H.vertexConn ≤ (cartesianCol S a₀).card := H.vertexConn_le_of_isSeparator hcolsep
  have hsub2 : (T ×ˢ (Finset.univ : Finset H.V)) ∪
      ((cartesianCol S a₀).image fun y ↦ (a₀, y)) ⊆ S := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hfull p.1 (Finset.mem_product.1 h).1 p.2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact mem_cartesianCol.1 hy
  have hdisj : Disjoint (T ×ˢ (Finset.univ : Finset H.V))
      ((cartesianCol S a₀).image fun y ↦ (a₀, y)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    exact ha₀ (Finset.mem_product.1 hp).1
  have h := Finset.card_le_card hsub2
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_univ, hHcard,
    Finset.card_image_of_injective _ fun y y' hy ↦ congrArg Prod.snd hy] at h
  have hmul : (G.card - 1) * H.card ≤ T.card * H.card := Nat.mul_le_mul hTcard (le_refl H.card)
  have hfin : (G.card - 1) * H.card + H.vertexConn ≤ S.card := by omega
  exact le_trans (min_le_right _ _) hfin

/-- **The vertex connectivity of a lexicographic product**, from below. -/
@[toIsoGraph]
theorem min_le_vertexConn_lexProduct (G H : CGraph) (hH1 : 1 ≤ H.card) :
    min (G.vertexConn * H.card) ((G.card - 1) * H.card + H.vertexConn) ≤ (G ·g H).vertexConn := by
  have hc : (G ·g H).card = G.card * H.card := card_lexProduct G H
  have hkG := G.vertexConn_le_card_sub_one
  have h1 : G.vertexConn * H.card ≤ G.card * H.card - H.card :=
    calc G.vertexConn * H.card ≤ (G.card - 1) * H.card := Nat.mul_le_mul hkG (le_refl H.card)
      _ = G.card * H.card - H.card := by rw [Nat.sub_mul, one_mul]
  have h2 := min_le_left (G.vertexConn * H.card) ((G.card - 1) * H.card + H.vertexConn)
  exact (G ·g H).le_vertexConn (by omega)
    fun S hS ↦ min_le_card_of_isSeparator_lexProduct G H S hS

/-- **The vertex connectivity of a lexicographic product with a non-complete first factor** is
`κ(G ·g H) = κ(G) · |H|`: blowing every vertex of `G` up into a copy of `H` multiplies the
connectivity by the size of the copy.  (For a complete `G` the answer is instead
`(|G| - 1) · |H| + κ(H)`, since then no set of whole fibres separates.) -/
@[toIsoGraph]
theorem vertexConn_lexProduct (G H : CGraph) (hH1 : 1 ≤ H.card) (hG : G.vertexConn < G.card - 1) :
    (G ·g H).vertexConn = G.vertexConn * H.card := by
  classical
  have hHcard : Fintype.card H.V = H.card := H.fintypeCard
  obtain ⟨y⟩ : Nonempty H.V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨T, hT, hTc⟩ :=
    G.vertexConn_eq_card_sub_one_or_exists_isSeparator.resolve_left (by omega)
  obtain ⟨g, ⟨a, haT, hga⟩, ⟨b, hbT, hgb⟩, hgadj⟩ := hT
  have hupper : (G ·g H).vertexConn ≤ G.vertexConn * H.card := by
    have hconst : ∀ u v : G.V × H.V, u ∉ T ×ˢ (Finset.univ : Finset H.V) →
        v ∉ T ×ˢ (Finset.univ : Finset H.V) → (G ·g H).Adj u v = true → g u.1 = g v.1 := by
      intro u v hu hv huv
      have hu1 : u.1 ∉ T := fun h ↦ hu (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
      have hv1 : v.1 ∉ T := fun h ↦ hv (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
      rw [lexProduct_adj, Bool.or_eq_true, Bool.and_eq_true] at huv
      rcases huv with h | ⟨h1, -⟩
      · exact hgadj u.1 v.1 hu1 hv1 h
      · rw [of_decide_eq_true h1]
    have hsep : (G ·g H).IsSeparator (T ×ˢ (Finset.univ : Finset H.V)) :=
      ⟨fun p ↦ g p.1, ⟨(a, y), fun h ↦ haT (Finset.mem_product.1 h).1, hga⟩,
        ⟨(b, y), fun h ↦ hbT (Finset.mem_product.1 h).1, hgb⟩, hconst⟩
    have h := (G ·g H).vertexConn_le_of_isSeparator hsep
    rwa [Finset.card_product, Finset.card_univ, hHcard, hTc] at h
  have hlow := min_le_vertexConn_lexProduct G H hH1
  have hmin : min (G.vertexConn * H.card) ((G.card - 1) * H.card + H.vertexConn)
      = G.vertexConn * H.card :=
    min_eq_left (le_trans (Nat.mul_le_mul (by omega) (le_refl H.card)) (Nat.le_add_right _ _))
  rw [hmin] at hlow
  omega

/-- A join is of diameter exactly two as soon as one side has a non-adjacent pair. -/
theorem diameter_join_of_not_adj (G H : CGraph)
    [Nonempty H.V] {a c : G.V} (hne : a ≠ c) (hadj : G.Adj a c = false) :
    (G ∇g H).diameter = 2 := by
  have : Nonempty G.V := ⟨a⟩
  refine diameter_eq_two _ (two_step_join G H) (u := Sum.inl a) (v := Sum.inl c) ?_ ?_
  · exact fun h ↦ hne (Sum.inl.inj h)
  · simp [hadj]

/-- **A join whose left factor is not complete has diameter two.** -/
@[toIsoGraph]
theorem diameter_join_left {G H : CGraph} [Nonempty H.V]
    (h : G.E < (FinEnum.card G.V).choose 2) : (G ∇g H).diameter = 2 := by
  obtain ⟨a, c, hne, hadj⟩ := exists_not_adj_of_E_lt G h
  exact diameter_join_of_not_adj G H hne hadj

/-- **A complete bipartite graph with two or more vertices on each side has diameter two**: it is
the join of two edgeless graphs, and an edgeless graph on two or more vertices is not complete. -/
@[simp] theorem diameter_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).diameter = 2 := by
  have : Nonempty (empty (n + 2)).V := ⟨⟨0, by omega⟩⟩
  rw [bipartite_eq_join]
  refine diameter_join_left ?_
  rw [E_empty, card_empty]
  exact Nat.choose_pos (by omega)

theorem diameter_compl_le_two (G : CGraph) (h : ¬ G.toSimple.Preconnected) :
    Gᶜ.diameter ≤ 2 :=
  diameter_le_two _ (two_step_compl G h)

/-- **The complement of a disconnected graph is connected.** -/
theorem isConnected_compl_of_not_preconnected (G : CGraph) [Nonempty G.V]
    (h : ¬ G.toSimple.Preconnected) : Gᶜ.IsConnected := by
  have : Nonempty Gᶜ.V := ‹Nonempty G.V›
  exact SimpleGraph.connected_of_ediam_ne_top
    (ne_top_of_le_ne_top (by simp) (ediam_le_two _ (two_step_compl G h)))

/-- **The complement of a disconnected graph is connected**, phrased with `IsConnected` rather
than `Preconnected` so that it transfers to `IsoGraph`. -/
@[toIsoGraph]
theorem isConnected_compl_of_not_isConnected {G : CGraph} [Nonempty G.V] (h : ¬ G.IsConnected) :
    Gᶜ.IsConnected :=
  isConnected_compl_of_not_preconnected G fun hp ↦ h ⟨hp⟩

/-- If the graph is disconnected and has an edge, its complement has diameter exactly two. -/
theorem diameter_compl_eq_two (G : CGraph) (h : ¬ G.toSimple.Preconnected)
    (hE : 0 < G.E) : Gᶜ.diameter = 2 := by
  obtain ⟨u, v, hne, hadj⟩ := exists_not_adj_of_E_lt Gᶜ
    (show Gᶜ.E < (FinEnum.card G.V).choose 2 by have hc := G.E_compl; omega)
  refine diameter_eq_two _ (two_step_compl G h) hne fun hc ↦ ?_
  have hc' : Gᶜ.Adj u v = true := by simpa using hc
  rw [hc'] at hadj
  exact Bool.noConfusion hadj

/-- Two colours suffice exactly when the graph is bipartite. -/
@[toIsoGraph]
theorem isBipartite_iff_chromNum_le_two {G : CGraph} : G.IsBipartite ↔ G.chromNum ≤ 2 :=
  G.isBipartite_iff_colorable.trans chromNum_le_iff_colorable.symm

/-- **Radius one and domination number one are the same condition** on a graph with at least two
vertices: both say that some vertex sees the whole graph. -/
@[toIsoGraph]
theorem radius_eq_one_iff_domNum_eq_one (G : CGraph) (hV : 1 < FinEnum.card G.V) :
    G.radius = 1 ↔ G.domNum = 1 := by
  rw [domNum_eq_one_iff]
  exact ⟨G.exists_universal_of_radius_eq_one, fun ⟨_, hv⟩ ↦ radius_eq_one_of_universal hv hV⟩

/-- **A vertex-transitive graph has radius equal to its diameter**: every vertex is as central as
every other, so the least and the greatest eccentricity agree. -/
@[toIsoGraph]
theorem radius_eq_diameter_of_isVertexTransitive (G : CGraph) (h : G.IsVertexTransitive) :
    G.radius = G.diameter := by
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : G.toSimple.radius = ⊤ := SimpleGraph.radius_eq_top_of_isEmpty
    have h2 : G.toSimple.diam = 0 := by
      rw [SimpleGraph.diam_eq_zero]
      exact Or.inr (by infer_instance)
    simp [radius, diameter, h1, h2]
  · have key : G.toSimple.radius = G.toSimple.ediam := by
      rw [SimpleGraph.radius_eq_ediam_iff]
      refine ⟨G.toSimple.eccent Classical.ofNonempty, fun u ↦ ?_⟩
      obtain ⟨σ, hσ⟩ := h Classical.ofNonempty u
      rw [← hσ]
      exact (SimpleGraph.Iso.eccent_eq (CGraph.Iso.toSimpleIso σ) _).symm
    simp [radius, diameter, SimpleGraph.diam, key]

@[simp, toIsoGraph] theorem numComponents_disjUnion (G H : CGraph) :
    (G ⊕g H).numComponents = G.numComponents + H.numComponents := by
  rw [numComponents, numComponents, numComponents,
    Nat.card_congr (disjUnionComponentEquiv G H), Nat.card_sum]

/-- **At most one of a graph and its complement is disconnected.** -/
@[toIsoGraph]
theorem numComponents_compl_eq_one (G : CGraph) (h : 2 ≤ G.numComponents) :
    Gᶜ.numComponents = 1 := by
  have hne : Nonempty G.V := FinEnum.card_pos_iff.1
    ((numComponents_pos_iff G).1 (by omega))
  rw [numComponents_eq_one_iff]
  refine G.isConnected_compl_of_not_preconnected (fun hpre ↦ ?_)
  have : Subsingleton G.toSimple.ConnectedComponent := hpre.subsingleton_connectedComponent
  have : G.numComponents = 1 := by
    rw [numComponents]
    exact Nat.card_eq_one_iff_unique.2 ⟨this, inferInstance⟩
  omega

/-- One vertex from each component is an independent set, so there are at most `α(G)` components. -/
@[toIsoGraph]
theorem numComponents_le_indepNum (G : CGraph) : G.numComponents ≤ G.indepNum := by
  classical
  choose f hout using G.surjective_connectedComponentMk
  have hinj : Function.Injective f := fun c d h ↦ by rw [← hout c, ← hout d, h]
  set s : Finset G.V := Finset.univ.image f with hs
  have hcard : s.card = G.numComponents := by
    rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, numComponents,
      Fintype.card_eq_nat_card]
  have hindep : G.toSimple.IsIndepSet s := by
    intro x hx y hy hxy hadj
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    refine hxy ?_
    have : c = d := by
      rw [← hout c, ← hout d]
      exact SimpleGraph.ConnectedComponent.sound hadj.reachable
    rw [this]
  calc G.numComponents = s.card := hcard.symm
    _ ≤ G.indepNum := hindep.card_le_indepNum

/-- A dominating set must meet every component, so there are at most `γ(G)` components. -/
@[toIsoGraph]
theorem numComponents_le_domNum (G : CGraph) : G.numComponents ≤ G.domNum := by
  classical
  obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
  have hsurj : Function.Surjective
      (fun v : {x : G.V // x ∈ s} ↦ G.toSimple.connectedComponentMk v.1) := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      rcases hs v with hv | ⟨u, hu, hadj⟩
      · exact ⟨⟨v, hv⟩, rfl⟩
      · exact ⟨⟨u, hu⟩, SimpleGraph.ConnectedComponent.sound
          (SimpleGraph.Adj.reachable (G.toSimple_adj u v |>.2 hadj))⟩
  rw [numComponents]
  calc Nat.card G.toSimple.ConnectedComponent
      ≤ Nat.card {x : G.V // x ∈ s} := Nat.card_le_card_of_surjective _ hsurj
    _ = s.card := Nat.card_eq_finsetCard s
    _ = G.domNum := hcard

/-- The join of two nonempty graphs is connected, hence has one component. -/
theorem numComponents_join (G H : CGraph)
    (hG : 0 < FinEnum.card G.V) (hH : 0 < FinEnum.card H.V) :
    (G ∇g H).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_join G H hG hH)

/-- A graph has as many components as vertices exactly when it has no edges. -/
@[toIsoGraph numComponents_eq_V_iff]
theorem numComponents_eq_card_iff (G : CGraph) :
    G.numComponents = FinEnum.card G.V ↔ G.E = 0 := by
  classical
  constructor
  · intro h
    by_contra hE
    obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos (Nat.pos_of_ne_zero hE)
    have hadj : G.toSimple.Adj a b := hab
    have hnotinj : ¬ Function.Injective G.toSimple.connectedComponentMk := fun hinj ↦
      hadj.ne (hinj (SimpleGraph.ConnectedComponent.sound hadj.reachable))
    have hlt := Fintype.card_lt_of_surjective_not_injective _ G.surjective_connectedComponentMk
      hnotinj
    rw [Fintype.card_eq_nat_card] at hlt
    rw [numComponents, FinEnum.card_eq_fintypeCard'] at h
    omega
  · intro h
    have hbot : G.toSimple = ⊥ := by
      ext a b
      simp only [SimpleGraph.bot_adj, iff_false]
      intro hadj
      have := E_pos_of_adj hadj
      omega
    have hinj : Function.Injective G.toSimple.connectedComponentMk := by
      intro u v huv
      have hr : G.toSimple.Reachable u v := SimpleGraph.ConnectedComponent.exact huv
      rw [hbot] at hr
      exact SimpleGraph.reachable_bot.1 hr
    rw [numComponents,
      ← Nat.card_eq_of_bijective _ ⟨hinj, G.surjective_connectedComponentMk⟩,
      Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard']

theorem numComponents_lt_card_of_E_pos (G : CGraph) (h : 0 < G.E) :
    G.numComponents < FinEnum.card G.V := by
  have hle := G.numComponents_le_card
  have := (G.numComponents_eq_card_iff).not.2 (by omega : ¬ G.E = 0)
  omega

/-- **The girth of a cycle is its length.** -/
@[toIsoGraph]
theorem girth_cycle (n : ℕ) : (cycle (n + 3)).girth = n + 3 := by
  refine le_antisymm ?_ ?_
  · have h := girth_le_V (not_isAcyclic_cycle n)
    rwa [card_cycle] at h
  · exact le_girth_of_forall_cycleList
      (fun u vs h2 hlt hnd hch hcl ↦
        cycle_no_short_cycleList (by omega) u vs h2 hlt hnd hch hcl)
      (not_isAcyclic_cycle n)

end

/-! ### Hamiltonicity of the named graphs

Every graph in the gallery that is presented by an LCF code carries its Hamiltonian cycle in that
presentation: the ring `0 – 1 – ⋯ – (n-1) – 0` of `lcfEdges` *is* a Hamiltonian cycle, so
`isHamiltonian_lcfEdges` turns the definition into a certificate and the only side condition left
is `3 ≤ n`.  The four graphs that are defined by hand and only later identified with an LCF code
are transported along that identification. -/

section
open NamedGraphs

/-- A graph given by an LCF code is Hamiltonian: its defining ring is a Hamiltonian cycle. -/
@[toIsoGraph]
theorem isHamiltonian_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    (lcf ss r).IsHamiltonian :=
  isHamiltonian_lcfEdges ss r rfl h3

theorem isHamiltonian_heawood : heawood.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_mcgee : mcgee.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_tutteCoxeter : tutteCoxeter.IsHamiltonian :=
  isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_franklin : franklin.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_pappus : pappus.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_folkman : folkman.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_frucht : frucht.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_bidiakisCube : bidiakisCube.IsHamiltonian :=
  isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_dyck : dyck.IsHamiltonian := isHamiltonian_lcf _ _ (by norm_num)

theorem isHamiltonian_mobiusKantor : mobiusKantor.IsHamiltonian :=
  isHamiltonian_of_iso mobiusKantorLcfIso (isHamiltonian_lcf _ _ (by norm_num))

theorem isHamiltonian_desargues : desargues.IsHamiltonian :=
  isHamiltonian_of_iso desarguesLcfIso (isHamiltonian_lcf _ _ (by norm_num))

theorem isHamiltonian_dodecahedron : dodecahedron.IsHamiltonian :=
  isHamiltonian_of_iso dodecahedronLcfIso (isHamiltonian_lcf _ _ (by norm_num))

@[toIsoGraph]
theorem isHamiltonian_nauru : nauru.IsHamiltonian :=
  isHamiltonian_of_iso nauruLcfIso (isHamiltonian_lcf _ _ (by norm_num))

theorem isHamiltonian_balaban10Cage : balaban10Cage.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_biggsSmith : biggsSmith.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_ljubljana : ljubljana.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_harries : harries.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_harriesWong : harriesWong.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_gray : gray.IsHamiltonian := isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_foster : foster.IsHamiltonian := isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_balaban11Cage : balaban11Cage.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

theorem isHamiltonian_tutte12Cage : tutte12Cage.IsHamiltonian :=
  isHamiltonian_lcfEdges _ _ rfl (by norm_num)

end

/-! ### Hamiltonicity of the parametrised families

A wheel is a cone on a cycle and a fan is a cone on a path, so both are
`isHamiltonian_join_complete_one`; a prism is a cycle times `K₂` and a ladder is a path times
`K₂`, so both are `isHamiltonian_cartesianProduct_complete_two`.  In all four cases the numbering
handed to the certificate is the one the family is defined with, so the side conditions are the
adjacency lemma of the underlying cycle or path and nothing else.  A balanced complete bipartite
graph is Hamiltonian by alternating sides, a crown graph by alternating sides with a shift, and a
circulant is Hamiltonian as soon as its connection set contains a step of `1`. -/

@[toIsoGraph]
theorem isHamiltonian_wheel {n : ℕ} (h2 : 2 ≤ n) : (wheel n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_join_complete_one (fun i ↦ vtx n i) h2 (card_cycle n)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [cycle_adj_val, vtx_val (by omega : i < n), vtx_val hi]
    exact ⟨by omega, Or.inl (Nat.mod_eq_of_lt hi)⟩

theorem isHamiltonian_fan {n : ℕ} (h2 : 2 ≤ n) : (fan n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_join_complete_one (fun i ↦ vtx n i) h2 (card_path n)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [path_adj_val, vtx_val (by omega : i < n), vtx_val hi]
    exact ⟨by omega, Or.inl rfl⟩

theorem isHamiltonian_prism {n : ℕ} (h3 : 3 ≤ n) : (prism n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_cartesianProduct_complete_two (fun i ↦ vtx n i) (by omega) (card_cycle n)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [cycle_adj_val, vtx_val (by omega : i < n), vtx_val hi]
    exact ⟨by omega, Or.inl (Nat.mod_eq_of_lt hi)⟩

theorem isHamiltonian_ladder {n : ℕ} (h2 : 2 ≤ n) : (ladder n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_cartesianProduct_complete_two (fun i ↦ vtx n i) h2 (card_path n)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have : i % n = j % n := congrArg Fin.val hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · rw [path_adj_val, vtx_val (by omega : i < n), vtx_val hi]
    exact ⟨by omega, Or.inl rfl⟩

/-- **The balanced complete bipartite graph is Hamiltonian.**  It is the join of two empty graphs
of the same order, so alternating sides walks the cycle. -/
@[toIsoGraph]
theorem isHamiltonian_bipartite {n : ℕ} (h2 : 2 ≤ n) : (bipartite n n).IsHamiltonian := by
  rw [bipartite_eq_join]
  exact isHamiltonian_join_of_card_eq (by simp) (by simpa using h2)

/-- **The crown graph is Hamiltonian.**  Take the two sides alternately, the first in the order
`0, 1, …` and the second shifted by two.  The shift is what keeps consecutive vertices out of the
perfect matching the crown is missing, and shifting by two rather than one is what keeps the step
after it clear as well; there has to be room for both, whence three vertices a side. -/
theorem isHamiltonian_crown {n : ℕ} (h3 : 3 ≤ n) : (crown n).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  -- the shifted numbering of the second side, reduced
  have hshift : ∀ a < n, (a + 2) % n = if a + 2 < n then a + 2 else a + 2 - n := by
    intro a ha
    rcases Nat.lt_or_ge (a + 2) n with h | h
    · rw [if_pos h, Nat.mod_eq_of_lt h]
    · rw [if_neg (by omega), Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ a b : ℕ, a % n ≠ b % n → vtx n a ≠ vtx n b :=
    fun _ _ h hc ↦ h (congrArg Fin.val hc)
  have key : ∀ a b : Fin n, a ≠ b →
      (crown n).Adj (a, vtx 2 0) (b, vtx 2 1) = true ∧
      (crown n).Adj (a, vtx 2 1) (b, vtx 2 0) = true := by
    intro a b hab
    constructor <;>
      · show (complete n ⊗g complete 2).Adj _ _ = true
        rw [tensorProduct_adj, complete_adj, complete_adj]
        simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
        exact ⟨hab, by decide⟩
  refine isHamiltonian_of_cyclicNumbering (n := 2 * n)
    (fun i ↦ if i % 2 = 0 then (vtx n (i / 2), vtx 2 0) else (vtx n (i / 2 + 2), vtx 2 1))
    (by omega)
    (by show FinEnum.card (crown n).V = 2 * n
        show n * 2 = 2 * n
        omega) ?_ ?_
  · intro i hi j hj hij
    have hside : (vtx 2 0) ≠ (vtx 2 1) := by decide
    have hi2 : i / 2 < n := by omega
    have hj2 : j / 2 < n := by omega
    by_cases hie : i % 2 = 0 <;> by_cases hje : j % 2 = 0
    · rw [if_pos hie, if_pos hje, Prod.mk.injEq] at hij
      have h := congrArg Fin.val hij.1
      rw [vtx_val hi2, vtx_val hj2] at h
      omega
    · rw [if_pos hie, if_neg hje, Prod.mk.injEq] at hij
      exact absurd hij.2 hside
    · rw [if_neg hie, if_pos hje, Prod.mk.injEq] at hij
      exact absurd hij.2.symm hside
    · rw [if_neg hie, if_neg hje, Prod.mk.injEq] at hij
      have h : (i / 2 + 2) % n = (j / 2 + 2) % n := congrArg Fin.val hij.1
      rw [hshift _ hi2, hshift _ hj2] at h
      split at h <;> split at h <;> omega
  · intro i hi
    have hi2 : i / 2 < n := by omega
    rcases Nat.lt_or_ge (i + 1) (2 * n) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      by_cases hie : i % 2 = 0
      · rw [if_pos hie, if_neg (by omega), show (i + 1) / 2 = i / 2 by omega]
        refine (key _ _ (hne _ _ ?_)).1
        rw [Nat.mod_eq_of_lt hi2, hshift _ hi2]
        split <;> omega
      · rw [if_neg hie, if_pos (by omega), show (i + 1) / 2 = i / 2 + 1 by omega]
        refine (key _ _ (hne _ _ ?_)).2
        rw [Nat.mod_eq_of_lt (by omega : i / 2 + 1 < n), hshift _ hi2]
        split <;> omega
    · have hin : i = 2 * n - 1 := by omega
      subst hin
      rw [show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self, if_neg (by omega), if_pos rfl]
      refine (key _ _ (hne _ _ ?_)).2
      rw [show (2 * n - 1) / 2 = n - 1 by omega, hshift _ (by omega)]
      simp only [Nat.zero_div, Nat.zero_mod]
      split <;> omega

/-- **A circulant whose connection set contains `1` is Hamiltonian.**  The ring it is written on
is the Hamiltonian cycle. -/
@[toIsoGraph]
theorem isHamiltonian_circulant {n : ℕ} {S : List ℕ} (h3 : 3 ≤ n) (h1 : 1 ∈ S) :
    (circulant n S).IsHamiltonian := by
  have hn : NeZero n := ⟨by omega⟩
  refine isHamiltonian_of_cyclicNumbering (n := n) (fun i ↦ vtx n i) h3 (card_circulant n S)
    (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · have h := congrArg Fin.val hij
    rwa [vtx_val hi, vtx_val hj] at h
  · have hsucc : (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
      rcases Nat.lt_or_ge (i + 1) n with h | h
      · rw [if_neg (by omega), Nat.mod_eq_of_lt h]
      · rw [if_pos (by omega), show i + 1 = n by omega, Nat.mod_self]
    have hlt : (i + 1) % n < n := Nat.mod_lt _ (by omega)
    have hval : ((i + 1) % n + n - i) % n = 1 := by
      rw [hsucc]
      rcases Nat.lt_or_ge (i + 1) n with h | h
      · rw [if_neg (by omega), show i + 1 + n - i = n + 1 by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)]
      · rw [if_pos (by omega), show 0 + n - i = 1 by omega, Nat.mod_eq_of_lt (by omega)]
    simp only [circulant, ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, ne_eq, decide_eq_true_eq]
    refine ⟨fun h ↦ ?_, Or.inl ?_⟩
    · have h' := congrArg Fin.val h
      rw [vtx_val hi, vtx_val hlt, hsucc] at h'
      split at h' <;> omega
    · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hlt, hval]
      simpa using h1

/-! ### The connectivity of the Petersen graph

The Petersen graph is 3-connected, and 3-edge-connected.  Both upper bounds come from Whitney's
inequality `κ ≤ λ ≤ δ` and 3-regularity; the two lower bounds are the searches that the definitions
ask for, cut by cut and separator by separator. -/

theorem edgeConn_petersen : petersen.edgeConn = 3 := by
  have hcard : petersen.card = 10 := card_petersen
  have hreg : petersen.IsRegularWith 3 := by native_decide
  have : Nonempty petersen.V := ⟨⟨{0, 1}, by decide⟩⟩
  refine le_antisymm ?_ (petersen.le_edgeConn (by omega) (by native_decide))
  have h := petersen.edgeConn_le_minDeg (by omega)
  rwa [hreg.minDeg_eq] at h

theorem vertexConn_petersen : petersen.vertexConn = 3 := by
  have hcard : petersen.card = 10 := card_petersen
  refine le_antisymm ?_ (petersen.le_vertexConn_of_forall_card_lt (by omega) (by native_decide))
  rw [← edgeConn_petersen]
  exact petersen.vertexConn_le_edgeConn

/-! ### The generalized Petersen graphs

`gp n k` is the outer `n`-cycle, the inner circulant on the step `k`, and the `n` spokes between
them.  Every vertex therefore has three neighbours, and the whole graph is connected — which is
everything the degree- and component-counting invariants need, uniformly in `n` and `k`.

The four little modular-arithmetic facts below are what the neighbour lists cost: a `%` normal
form to feed `omega`, that a nonzero step moves a residue, that distinct steps land distinct, and
that stepping back and forward again returns. -/

section Ring

private theorem add_mod_eq_ite {n i d : ℕ} (hi : i < n) (hd : d < n) :
    (i + d) % n = if i + d < n then i + d else i + d - n := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

private theorem add_mod_ne_self {n i d : ℕ} (hi : i < n) (hd : 0 < d) (hdn : d < n) :
    (i + d) % n ≠ i := by
  rw [add_mod_eq_ite hi hdn]
  split <;> omega

private theorem add_mod_inj {n i d e : ℕ} (hi : i < n) (hd : d < n) (he : e < n)
    (h : (i + d) % n = (i + e) % n) : d = e := by
  rw [add_mod_eq_ite hi hd, add_mod_eq_ite hi he] at h
  split at h <;> split at h <;> omega

private theorem shift_back {n i k : ℕ} (hi : i < n) (hk : k ≤ n) :
    ((i + n - k) % n + k) % n = i := by
  rw [Nat.mod_add_mod]
  have h : i + n - k + k = i + n := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

end Ring

section GP

theorem mem_gpEdges {n k a b : ℕ} :
    (a, b) ∈ gpEdges n k ↔ ∃ i < n,
      (a = i ∧ b = (i + 1) % n) ∨ (a = i ∧ b = n + i) ∨
        (a = n + i ∧ b = n + (i + k) % n) := by
  simp [gpEdges, List.mem_flatMap, Prod.ext_iff]

/-- The three neighbours of an outer vertex: the two along the rim, and its spoke. -/
theorem mem_gpEdges_outer {n k i w : ℕ} (hn : 2 ≤ n) (hi : i < n) :
    ((i, w) ∈ gpEdges n k ∨ (w, i) ∈ gpEdges n k) ↔
      (w = (i + 1) % n ∨ w = (i + n - 1) % n ∨ w = n + i) := by
  constructor
  · rintro (h | h)
    · rw [mem_gpEdges] at h
      obtain ⟨j, hj, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨he, -⟩)⟩ := h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · omega
    · rw [mem_gpEdges] at h
      obtain ⟨j, hj, (⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩)⟩ := h
      · refine Or.inr (Or.inl ?_)
        subst he
        rcases lt_or_ge (w + 1) n with h1 | h1
        · rw [Nat.mod_eq_of_lt h1]
          have h2 : w + 1 + n - 1 = w + n := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
        · have h2 : (w + 1) % n = 0 := by
            have h4 : w + 1 = n := by omega
            rw [h4, Nat.mod_self]
          rw [h2]
          have h3 : 0 + n - 1 = n - 1 := by omega
          rw [h3, Nat.mod_eq_of_lt (by omega)]
          omega
      · omega
      · omega
  · rintro (rfl | rfl | rfl)
    · exact Or.inl (mem_gpEdges.2 ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (mem_gpEdges.2 ⟨(i + n - 1) % n, Nat.mod_lt _ (by omega),
        Or.inl ⟨rfl, (shift_back hi (by omega)).symm⟩⟩)
    · exact Or.inl (mem_gpEdges.2 ⟨i, hi, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)

/-- The three neighbours of an inner vertex: the two `k`-steps around the hub, and its spoke. -/
theorem mem_gpEdges_inner {n k i w : ℕ} (hi : i < n) (hk : k < n) :
    ((n + i, w) ∈ gpEdges n k ∨ (w, n + i) ∈ gpEdges n k) ↔
      (w = n + (i + k) % n ∨ w = n + (i + n - k) % n ∨ w = i) := by
  constructor
  · rintro (h | h)
    · rw [mem_gpEdges] at h
      obtain ⟨j, hj, (⟨he, -⟩ | ⟨he, -⟩ | ⟨he, hw⟩)⟩ := h
      · omega
      · omega
      · have hji : j = i := by omega
        subst hji
        exact Or.inl hw
    · rw [mem_gpEdges] at h
      obtain ⟨j, hj, (⟨hw, he⟩ | ⟨hw, he⟩ | ⟨hw, he⟩)⟩ := h
      · have := Nat.mod_lt (j + 1) (show 0 < n by omega)
        omega
      · exact Or.inr (Or.inr (by omega))
      · refine Or.inr (Or.inl ?_)
        have hji : (j + k) % n = i := by omega
        have hkey : (i + n - k) % n = j := by
          rw [← hji, add_mod_eq_ite hj hk]
          split
          · have h2 : j + k + n - k = j + n := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
          · have h2 : j + k - n + n - k = j := by omega
            rw [h2, Nat.mod_eq_of_lt hj]
        omega
  · rintro (rfl | rfl | rfl)
    · exact Or.inl (mem_gpEdges.2 ⟨i, hi, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
    · refine Or.inr (mem_gpEdges.2 ⟨(i + n - k) % n, Nat.mod_lt _ (by omega),
        Or.inr (Or.inr ⟨rfl, ?_⟩)⟩)
      rw [shift_back hi (le_of_lt hk)]
    · exact Or.inr (mem_gpEdges.2 ⟨w, hi, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)

/-- `rw` will not see through the `def` to reach `ofEdges_adj_val`; this states it for `gp`. -/
theorem gp_adj_val {n k : ℕ} (u v : (gp n k).V) :
    (gp n k).Adj u v = true ↔
      u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ gpEdges n k ∨ (v.1, u.1) ∈ gpEdges n k) :=
  ofEdges_adj_val (2 * n) (gpEdges n k) u v

/-- **Every generalized Petersen graph is cubic.**  `2 * k ≠ n` is what stops the two `k`-steps
out of an inner vertex from being the same edge. -/
@[toIsoGraph]
theorem isRegularWith_gp {n k : ℕ} (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    (gp n k).IsRegularWith 3 := by
  intro v
  have hv2 : v.1 < 2 * n := v.2
  rcases lt_or_ge v.1 n with hlt | hge
  · have h1 : (v.1 + 1) % n < n := Nat.mod_lt _ (by omega)
    have h2 : (v.1 + n - 1) % n < n := Nat.mod_lt _ (by omega)
    have hne : (v.1 + 1) % n ≠ (v.1 + n - 1) % n := by
      intro he
      have hrw : v.1 + n - 1 = v.1 + (n - 1) := by omega
      rw [hrw] at he
      have := add_mod_inj hlt (by omega : (1 : ℕ) < n) (by omega : n - 1 < n) he
      omega
    have hs1 : (v.1 + 1) % n ≠ v.1 := add_mod_ne_self hlt (by omega) (by omega)
    have hs2 : (v.1 + n - 1) % n ≠ v.1 := by
      have hrw : v.1 + n - 1 = v.1 + (n - 1) := by omega
      rw [hrw]
      exact add_mod_ne_self hlt (by omega) (by omega)
    refine (degree_ofEdges (2 * n) (gpEdges n k) v
      [(v.1 + 1) % n, (v.1 + n - 1) % n, n + v.1] ?_ ?_ ?_ ?_).trans rfl
    · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hne, by omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h ↦ hs1 h.symm, fun h ↦ hs2 h.symm, by omega⟩
    · intro w _
      rw [mem_gpEdges_outer (by omega) hlt]
      simp
  · set i := v.1 - n with hidef
    have hvi : v.1 = n + i := by omega
    have hi : i < n := by omega
    have h1 : (i + k) % n < n := Nat.mod_lt _ (by omega)
    have h2 : (i + n - k) % n < n := Nat.mod_lt _ (by omega)
    have hne : (i + k) % n ≠ (i + n - k) % n := by
      intro he
      have hrw : i + n - k = i + (n - k) := by omega
      rw [hrw] at he
      have := add_mod_inj hi hkn (by omega : n - k < n) he
      omega
    have hs1 : (i + k) % n ≠ i := add_mod_ne_self hi hk hkn
    have hs2 : (i + n - k) % n ≠ i := by
      have hrw : i + n - k = i + (n - k) := by omega
      rw [hrw]
      exact add_mod_ne_self hi (by omega) (by omega)
    refine (degree_ofEdges (2 * n) (gpEdges n k) v
      [n + (i + k) % n, n + (i + n - k) % n, i] ?_ ?_ ?_ ?_).trans rfl
    · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by omega, by omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by omega, by omega, by omega⟩
    · intro w _
      rw [hvi, mem_gpEdges_inner hi hkn]
      simp

/-- **Every generalized Petersen graph is connected**: an outer vertex steps back around the
ring, an inner vertex steps down its spoke, and both descents end at vertex `0`. -/
@[toIsoGraph]
theorem isConnected_gp {n k : ℕ} (hn : 0 < n) : (gp n k).IsConnected := by
  refine isConnected_of_rank (fun v ↦ v.1) ⟨0, by omega⟩ ?_
  intro v hv
  have hv2 : v.1 < 2 * n := v.2
  have hv0 : v.1 ≠ 0 := fun h ↦ hv (Fin.ext h)
  rcases lt_or_ge v.1 n with hlt | hge
  · refine ⟨⟨v.1 - 1, by omega⟩, by simp; omega, ?_⟩
    rw [gp_adj_val]
    refine ⟨by simp; omega, Or.inr (mem_gpEdges.2 ⟨v.1 - 1, by omega, Or.inl ⟨rfl, ?_⟩⟩)⟩
    show v.1 = (v.1 - 1 + 1) % n
    rw [show v.1 - 1 + 1 = v.1 by omega, Nat.mod_eq_of_lt hlt]
  · refine ⟨⟨v.1 - n, by omega⟩, by simp; omega, ?_⟩
    rw [gp_adj_val]
    refine ⟨by simp; omega, Or.inr (mem_gpEdges.2 ⟨v.1 - n, by omega, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩)⟩
    show v.1 = n + (v.1 - n)
    omega

end GP

/-! ### Graphs given by an LCF code

The ring gives every vertex two neighbours; the chord gives it a third, provided the code is
valid.  That the code *is* valid is a finite check on the code alone — see `IsValidLcf` — so each
of the named LCF graphs discharges it with `decide`, and the cubicness proof itself is done once,
here, for all of them. -/

section LCF

theorem lcfEdges_eq (ss : List ℤ) (r : ℕ) :
    lcfEdges ss r = (List.range (ss.length * r)).flatMap
      fun i ↦ [(i, (i + 1) % (ss.length * r)), (i, lcfChord ss r i)] := rfl

theorem lcfChord_lt {ss : List ℤ} {r : ℕ} (hN : 0 < ss.length * r) (i : ℕ) :
    lcfChord ss r i < ss.length * r := by
  have hN' : (0 : ℤ) < ((ss.length * r : ℕ) : ℤ) := by exact_mod_cast hN
  have h1 : 0 ≤ (((i : ℤ) + ss.getD (i % ss.length) 0) % ((ss.length * r : ℕ) : ℤ)
      + ((ss.length * r : ℕ) : ℤ)) % ((ss.length * r : ℕ) : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hN')
  have h2 : (((i : ℤ) + ss.getD (i % ss.length) 0) % ((ss.length * r : ℕ) : ℤ)
      + ((ss.length * r : ℕ) : ℤ)) % ((ss.length * r : ℕ) : ℤ) < ((ss.length * r : ℕ) : ℤ) :=
    Int.emod_lt_of_pos _ hN'
  unfold lcfChord
  omega

theorem mem_lcfEdges_iff {ss : List ℤ} {r a b : ℕ} :
    (a, b) ∈ lcfEdges ss r ↔ ∃ i < ss.length * r,
      (a = i ∧ b = (i + 1) % (ss.length * r)) ∨ (a = i ∧ b = lcfChord ss r i) := by
  rw [lcfEdges_eq]
  simp [List.mem_flatMap, Prod.ext_iff]

/-- The three neighbours of a vertex on the ring: the two rim edges, and the chord. -/
theorem mem_lcfEdges_at {ss : List ℤ} {r : ℕ} (hn : 2 ≤ ss.length * r) (hv : IsValidLcf ss r)
    {i w : ℕ} (hi : i < ss.length * r) :
    ((i, w) ∈ lcfEdges ss r ∨ (w, i) ∈ lcfEdges ss r) ↔
      (w = (i + 1) % (ss.length * r) ∨ w = (i + ss.length * r - 1) % (ss.length * r) ∨
        w = lcfChord ss r i) := by
  constructor
  · rintro (h | h)
    · rw [mem_lcfEdges_iff] at h
      obtain ⟨j, hj, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · rw [mem_lcfEdges_iff] at h
      obtain ⟨j, hj, (⟨rfl, he⟩ | ⟨rfl, he⟩)⟩ := h
      · refine Or.inr (Or.inl ?_)
        subst he
        rcases lt_or_ge (w + 1) (ss.length * r) with h1 | h1
        · rw [Nat.mod_eq_of_lt h1]
          have h2 : w + 1 + ss.length * r - 1 = w + ss.length * r := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
        · have h2 : (w + 1) % (ss.length * r) = 0 := by
            have h4 : w + 1 = ss.length * r := by omega
            rw [h4, Nat.mod_self]
          rw [h2]
          have h3 : 0 + ss.length * r - 1 = ss.length * r - 1 := by omega
          rw [h3, Nat.mod_eq_of_lt (by omega)]
          omega
      · exact Or.inr (Or.inr (he ▸ ((hv w hj).1).symm))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl (mem_lcfEdges_iff.2 ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (mem_lcfEdges_iff.2 ⟨(i + ss.length * r - 1) % (ss.length * r),
        Nat.mod_lt _ (by omega), Or.inl ⟨rfl, (shift_back hi (by omega)).symm⟩⟩)
    · exact Or.inl (mem_lcfEdges_iff.2 ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩)

/-- `rw` will not see through the `def` to reach `ofEdges_adj_val`; this states it for `lcf`. -/
theorem lcf_adj_val {ss : List ℤ} {r : ℕ} (u v : (lcf ss r).V) :
    (lcf ss r).Adj u v = true ↔
      u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ lcfEdges ss r ∨ (v.1, u.1) ∈ lcfEdges ss r) :=
  ofEdges_adj_val (ss.length * r) (lcfEdges ss r) u v

/-- **A graph given by a valid LCF code is cubic**: two ring edges and one chord at every
vertex. -/
@[toIsoGraph]
theorem isRegularWith_lcf {ss : List ℤ} {r : ℕ} (h3 : 3 ≤ ss.length * r)
    (hv : IsValidLcf ss r) : (lcf ss r).IsRegularWith 3 := by
  intro v
  have hv2 : v.1 < ss.length * r := v.2
  have hN : 0 < ss.length * r := by omega
  have h1 : (v.1 + 1) % (ss.length * r) < ss.length * r := Nat.mod_lt _ hN
  have h2 : (v.1 + ss.length * r - 1) % (ss.length * r) < ss.length * r := Nat.mod_lt _ hN
  have hc := lcfChord_lt hN v.1
  obtain ⟨-, hci, hcs, hcp⟩ := hv v.1 hv2
  have hne : (v.1 + 1) % (ss.length * r) ≠ (v.1 + ss.length * r - 1) % (ss.length * r) := by
    intro he
    have hrw : v.1 + ss.length * r - 1 = v.1 + (ss.length * r - 1) := by omega
    rw [hrw] at he
    have := add_mod_inj hv2 (by omega : (1 : ℕ) < ss.length * r)
      (by omega : ss.length * r - 1 < ss.length * r) he
    omega
  have hs1 : (v.1 + 1) % (ss.length * r) ≠ v.1 := add_mod_ne_self hv2 (by omega) (by omega)
  have hs2 : (v.1 + ss.length * r - 1) % (ss.length * r) ≠ v.1 := by
    have hrw : v.1 + ss.length * r - 1 = v.1 + (ss.length * r - 1) := by omega
    rw [hrw]
    exact add_mod_ne_self hv2 (by omega) (by omega)
  refine (degree_ofEdges (ss.length * r) (lcfEdges ss r) v
    [(v.1 + 1) % (ss.length * r), (v.1 + ss.length * r - 1) % (ss.length * r),
      lcfChord ss r v.1] ?_ ?_ ?_ ?_).trans rfl
  · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hne, fun h ↦ hcs h.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h ↦ hcp h.symm
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h ↦ hs1 h.symm, fun h ↦ hs2 h.symm, fun h ↦ hci h.symm⟩
  · intro w _
    rw [mem_lcfEdges_at (by omega) hv hv2]
    simp

end LCF

end CGraph

namespace IsoGraph

/-! ### Trees, and Euler's count -/

theorem IsTree.E_add_one {G : IsoGraph} (h : IsTree G) : G.E + 1 = G.V :=
  ((isTree_iff G).1 h).2

/-- Too few edges to be connected. -/
theorem not_isConnected_of_E_add_one_lt {G : IsoGraph} (h : G.E + 1 < G.V) : ¬ IsConnected G :=
  fun hc ↦ absurd hc.V_le_E_add_one (by omega)

@[simp] theorem not_isConnected_empty (n : ℕ) : ¬ IsConnected (empty (n + 2)) :=
  not_isConnected_of_E_add_one_lt (by simp)

@[simp] theorem not_isTree_cycle (n : ℕ) : ¬ IsTree (cycle (n + 3)) := by
  rw [isTree_iff, E_cycle, V_cycle]
  rintro ⟨-, h⟩
  omega

@[simp] theorem not_isTree_complete (n : ℕ) : ¬ IsTree (complete (n + 3)) := by
  rw [isTree_iff, E_complete, V_complete]
  rintro ⟨-, h⟩
  rw [show n + 3 = (n + 2) + 1 from rfl, choose_two_succ] at h
  have : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
  omega

/-- Anything connected that is not a tree has a cycle. -/
theorem not_isAcyclic_of_isConnected {G : IsoGraph} (hc : IsConnected G) (h : ¬ IsTree G) :
    ¬ IsAcyclic G :=
  fun ha ↦ h ((isTree_iff_isConnected_and_isAcyclic G).2 ⟨hc, ha⟩)

@[simp] theorem not_isAcyclic_complete (n : ℕ) : ¬ IsAcyclic (complete (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_complete (n + 2)) (not_isTree_complete n)

/-! ### The diameter of a join -/

/-- A join whose right factor is not complete has diameter two. -/
theorem diameter_join_right {G H : IsoGraph} (hG : 0 < G.V) (h : H.E < H.V.choose 2) :
    (G ∇g H).diameter = 2 := by
  rw [join_comm]
  exact diameter_join_left hG h

@[simp] theorem girth_complete (n : ℕ) : (complete (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

@[simp] theorem girth_cycle_three : (cycle 3).girth = 3 := by
  rw [cycle_three]; exact girth_complete 0

theorem girth_join_left {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    (G ∇g H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_join]
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hG
  have h2 : 1 ≤ H.cliqueNum := one_le_cliqueNum hH
  omega

theorem girth_join_right {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.E) :
    (G ∇g H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_join]
  have h1 : 1 ≤ G.cliqueNum := one_le_cliqueNum hG
  have h2 : 2 ≤ H.cliqueNum := two_le_cliqueNum_of_E_pos hH
  omega

theorem girth_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    (G ⊠g H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_strongProduct]
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hG
  have h2 : 2 ≤ H.cliqueNum := two_le_cliqueNum_of_E_pos hH
  calc 3 ≤ 2 * 2 := by norm_num
    _ ≤ G.cliqueNum * H.cliqueNum := Nat.mul_le_mul h1 h2

theorem girth_lexProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    (G ·g H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_lexProduct]
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hG
  have h2 : 2 ≤ H.cliqueNum := two_le_cliqueNum_of_E_pos hH
  calc 3 ≤ 2 * 2 := by norm_num
    _ ≤ G.cliqueNum * H.cliqueNum := Nat.mul_le_mul h1 h2

/-- Either way round: on six vertices a graph or its complement has girth three. -/
theorem girth_eq_three_or_girth_compl_eq_three (G : IsoGraph) (h : 6 ≤ G.V) :
    G.girth = 3 ∨ Gᶜ.girth = 3 := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · exact Or.inl (girth_eq_three_iff.2 h')
  · exact Or.inr (girth_eq_three_iff.2 (by rwa [cliqueNum_compl]))

@[simp] theorem radius_empty (n : ℕ) : (empty n).radius = 0 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_empty n), diameter_empty]

@[simp] theorem radius_complete (n : ℕ) : (complete (n + 2)).radius = 1 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_complete _),
    diameter_complete]

@[simp] theorem radius_cycle (n : ℕ) : (cycle (n + 1)).radius = (n + 1) / 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_cycle _), diameter_cycle]

/-! ### Components versus the other invariants -/

@[simp] theorem numComponents_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_join hG hH)

theorem numComponents_lt_V_of_E_pos {G : IsoGraph} (h : 0 < G.E) : G.numComponents < G.V := by
  have hle := G.numComponents_le_V
  have := (G.numComponents_eq_V_iff).not.2 (by omega : ¬ G.E = 0)
  omega

theorem not_isConnected_of_E_add_one_lt_V {G : IsoGraph} (h : G.E + 1 < G.V) :
    ¬ G.IsConnected := fun hc ↦ by
  have := V_le_E_add_one_of_isConnected hc
  omega

/-- Each connected component needs a clique of its own. -/
theorem numComponents_le_cliqueCoverNum (G : IsoGraph) :
    G.numComponents ≤ G.cliqueCoverNum :=
  le_trans G.numComponents_le_indepNum G.indepNum_le_cliqueCoverNum

/-! ### The radius of a join

A join of two nonempty graphs has diameter at most two, so its radius is one or two, and it is
one exactly when one of the two factors has a dominating vertex. -/

theorem radius_join_eq_one {G H : IsoGraph} (hV : 1 < G.V + H.V)
    (h : G.domNum = 1 ∨ H.domNum = 1) : (G ∇g H).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one (by rwa [V_join]), domNum_join_eq_one_iff]
  exact h

theorem radius_join_eq_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h1 : G.domNum ≠ 1) (h2 : H.domNum ≠ 1) : (G ∇g H).radius = 2 := by
  have hV : 1 < (G ∇g H).V := by rw [V_join]; omega
  have hne : (G ∇g H).radius ≠ 1 := by
    intro h
    rw [radius_eq_one_iff_domNum_eq_one hV, domNum_join_eq_one_iff] at h
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  have hle := radius_le_diameter (G ∇g H)
  have hd := diameter_join_le_two _ _ hG hH
  have hpos := radius_pos (isConnected_join hG hH) hV
  omega

/-! ### The radius of a strong or lexicographic product -/

theorem radius_strongProduct_eq_one {G H : IsoGraph} (hV : 1 < (G ⊠g H).V)
    (hG : G.domNum = 1) (hH : H.domNum = 1) : (G ⊠g H).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one hV]
  exact domNum_strongProduct_eq_one hG hH

theorem radius_lexProduct_eq_one {G H : IsoGraph} (hV : 1 < (G ·g H).V)
    (hG : G.domNum = 1) (hH : H.domNum = 1) : (G ·g H).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one hV, domNum_lexProduct G hH]
  exact hG

theorem not_isTree_lineGraph {G : IsoGraph} (h : 3 ≤ G.maxDeg) : ¬ IsTree (lineGraph G) :=
  not_isTree_of_girth_pos (by rw [girth_lineGraph_eq_three h]; omega)

/-- A graph with no edges is a tree exactly when it is the one-point graph. -/
@[simp] theorem isTree_empty_iff (n : ℕ) : IsTree (empty n) ↔ n = 1 := by
  rw [isTree_iff, E_empty, V_empty]
  refine ⟨fun ⟨_, h⟩ ↦ by omega, ?_⟩
  rintro rfl
  exact ⟨by simp [isConnected_empty_one], rfl⟩

@[simp] theorem not_isTree_empty (n : ℕ) : ¬ IsTree (empty (n + 2)) := by
  rw [isTree_empty_iff]; omega

/-! ### Counting edges detects the cycles

A graph with at least as many edges as vertices cannot be a tree, and if it is also connected it
cannot be acyclic.  This is the cheapest cycle detector in the library: it needs no witness
cycle, only the two counts.
-/

theorem not_isTree_of_V_le_E {G : IsoGraph} (h : G.V ≤ G.E) : ¬ IsTree G :=
  fun ht ↦ by have := ht.E_add_one; omega

theorem not_isTree_of_not_isAcyclic {G : IsoGraph} (h : ¬ IsAcyclic G) : ¬ IsTree G :=
  fun ht ↦ h ((isTree_iff_isConnected_and_isAcyclic G).1 ht).2

theorem not_isAcyclic_of_V_le_E {G : IsoGraph} (hc : IsConnected G) (h : G.V ≤ G.E) :
    ¬ IsAcyclic G :=
  not_isAcyclic_of_isConnected hc (not_isTree_of_V_le_E h)

theorem radius_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 1) □g cycle (n + 1)).radius = (m + 1) / 2 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_cycle m) (isConnected_cycle n), radius_cycle,
    radius_cycle]

theorem diameter_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 1) □g path (n + 1)).diameter = (m + 1) / 2 + n := by
  rw [diameter_cartesianProduct (isConnected_cycle m) (isConnected_path n), diameter_cycle,
    diameter_path]

theorem radius_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 1) □g path (n + 1)).radius = (m + 1) / 2 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_cycle m) (isConnected_path n), radius_cycle,
    radius_path]

@[simp] theorem isConnected_strongProduct_cycle (m n : ℕ) :
    IsConnected (cycle (m + 1) ⊠g cycle (n + 1)) :=
  isConnected_strongProduct (isConnected_cycle m) (isConnected_cycle n)

@[simp] theorem girth_strongProduct_cycle (m n : ℕ) :
    (cycle (m + 3) ⊠g cycle (n + 3)).girth = 3 :=
  girth_strongProduct (by rw [E_cycle]; omega) (by rw [E_cycle]; omega)

@[simp] theorem isConnected_lexProduct_cycle (m n : ℕ) :
    IsConnected (cycle (m + 1) ·g cycle (n + 1)) :=
  isConnected_lexProduct (isConnected_cycle m) (isConnected_cycle n)

@[simp] theorem girth_lexProduct_cycle (m n : ℕ) :
    (cycle (m + 3) ·g cycle (n + 3)).girth = 3 :=
  girth_lexProduct (by rw [E_cycle]; omega) (by rw [E_cycle]; omega)

@[simp] theorem isConnected_lexProduct_path (m n : ℕ) :
    IsConnected (path (m + 1) ·g path (n + 1)) :=
  isConnected_lexProduct (isConnected_path m) (isConnected_path n)

@[simp] theorem girth_lexProduct_path (m n : ℕ) :
    (path (m + 2) ·g path (n + 2)).girth = 3 :=
  girth_lexProduct (by rw [E_path]; omega) (by rw [E_path]; omega)

theorem not_isBipartite_lexProduct_path (m n : ℕ) :
    ¬ IsBipartite (path (m + 2) ·g path (n + 2)) :=
  not_isBipartite_lexProduct (by rw [E_path]; omega) (by rw [E_path]; omega)

@[simp] theorem girth_strongProduct_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 2)).girth = 3 :=
  girth_strongProduct (E_complete_pos m) (E_complete_pos n)

theorem isConnected_strongProduct_complete (m n : ℕ) :
    IsConnected (complete (m + 1) ⊠g complete (n + 1)) :=
  isConnected_strongProduct (isConnected_complete m) (isConnected_complete n)

@[simp] theorem girth_lexProduct_complete (m n : ℕ) :
    (complete (m + 2) ·g complete (n + 2)).girth = 3 :=
  girth_lexProduct (E_complete_pos m) (E_complete_pos n)

theorem isConnected_lexProduct_complete (m n : ℕ) :
    IsConnected (complete (m + 1) ·g complete (n + 1)) :=
  isConnected_lexProduct (isConnected_complete m) (isConnected_complete n)

theorem radius_strongProduct_of_domNum_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 1)).radius = 1 := by
  refine radius_strongProduct_eq_one ?_ (domNum_complete (m + 1)) (domNum_complete n)
  rw [V_strongProduct, V_complete, V_complete]
  have h : 2 * 1 ≤ (m + 2) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem radius_lexProduct_complete (m n : ℕ) :
    (complete (m + 2) ·g complete (n + 1)).radius = 1 := by
  refine radius_lexProduct_eq_one ?_ (domNum_complete (m + 1)) (domNum_complete n)
  rw [V_lexProduct, V_complete, V_complete]
  have h : 2 * 1 ≤ (m + 2) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem diameter_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) □g cycle (n + 1)).diameter = 1 + (n + 1) / 2 := by
  rw [diameter_cartesianProduct (isConnected_complete (m + 1)) (isConnected_cycle n),
    diameter_complete, diameter_cycle]

theorem radius_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) □g cycle (n + 1)).radius = 1 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_complete (m + 1)) (isConnected_cycle n),
    radius_complete, radius_cycle]

theorem girth_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 3) □g cycle (n + 3)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_cartesianProduct (G := complete (m + 3)) (H := cycle (n + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [cliqueNum_complete] at h
  omega

theorem diameter_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 1)).diameter = 1 + n := by
  rw [diameter_cartesianProduct (isConnected_complete (m + 1)) (isConnected_path n),
    diameter_complete, diameter_path]

theorem radius_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 1)).radius = 1 + (n + 1) / 2 := by
  rw [radius_cartesianProduct (isConnected_complete (m + 1)) (isConnected_path n),
    radius_complete, radius_path]

theorem girth_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 3) □g path (n + 2)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_cartesianProduct (G := complete (m + 3)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_complete] at h
  omega

theorem isConnected_tensorProduct_cycle_odd_cycle (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g cycle (n + 3)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_cycle (n + 2))
    (not_isBipartite_cycle_odd a) (by rw [E_cycle]; omega)

theorem numComponents_tensorProduct_cycle_odd_cycle (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g cycle (n + 3)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_cycle a n)

theorem isConnected_tensorProduct_cycle_odd_path (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g path (n + 2)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_path (n + 1))
    (not_isBipartite_cycle_odd a) (by rw [E_path]; omega)

theorem numComponents_tensorProduct_cycle_odd_path (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g path (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_path a n)

theorem isConnected_tensorProduct_cycle_odd_complete (a n : ℕ) :
    IsConnected (cycle (2 * a + 3) ⊗g complete (n + 2)) :=
  isConnected_tensorProduct (isConnected_cycle (2 * a + 2)) (isConnected_complete (n + 1))
    (not_isBipartite_cycle_odd a) (E_complete_pos n)

theorem numComponents_tensorProduct_cycle_odd_complete (a n : ℕ) :
    (cycle (2 * a + 3) ⊗g complete (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_cycle_odd_complete a n)

theorem isConnected_tensorProduct_complete_cycle (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g cycle (n + 3)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_cycle (n + 2))
    (not_isBipartite_complete m) (by rw [E_cycle]; omega)

theorem numComponents_tensorProduct_complete_cycle (m n : ℕ) :
    (complete (m + 3) ⊗g cycle (n + 3)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_cycle m n)

theorem isConnected_tensorProduct_complete_path (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g path (n + 2)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_path (n + 1))
    (not_isBipartite_complete m) (by rw [E_path]; omega)

theorem numComponents_tensorProduct_complete_path (m n : ℕ) :
    (complete (m + 3) ⊗g path (n + 2)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct_complete_path m n)

theorem girth_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ⊠g cycle (n + 3)).girth = 3 :=
  girth_strongProduct (E_complete_pos m) (by rw [E_cycle]; omega)

theorem girth_lexProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ·g cycle (n + 3)).girth = 3 :=
  girth_lexProduct (E_complete_pos m) (by rw [E_cycle]; omega)

theorem girth_strongProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ⊠g path (n + 2)).girth = 3 :=
  girth_strongProduct (E_complete_pos m) (by rw [E_path]; omega)

theorem girth_lexProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ·g path (n + 2)).girth = 3 :=
  girth_lexProduct (E_complete_pos m) (by rw [E_path]; omega)

theorem diameter_join_path_complete (m n : ℕ) :
    (path (m + 3) ∇g complete (n + 1)).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 from by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_complete]; omega) ?_
  rw [E_path, V_path, h]
  omega

theorem diameter_join_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ∇g complete (n + 1)).diameter = 2 := by
  have h : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
    rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 from by omega]
  have h2 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 4) * (m + 3) = m * m + 7 * m + 12 := by ring
    omega
  refine diameter_join_left (by rw [V_complete]; omega) ?_
  rw [E_cycle, V_cycle, h]
  omega

theorem girth_lineGraph_mycielskian {G : IsoGraph} (h3 : 3 ≤ max (2 * maxDeg G) G.V) :
    (lineGraph (mycielskian G)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_mycielskian]; exact h3)

theorem not_isBipartite_lineGraph_mycielskian {G : IsoGraph}
    (h3 : 3 ≤ max (2 * maxDeg G) G.V) : ¬ IsBipartite (lineGraph (mycielskian G)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_mycielskian]; exact h3)

theorem not_isAcyclic_lineGraph_mycielskian {G : IsoGraph}
    (h3 : 3 ≤ max (2 * maxDeg G) G.V) : ¬ IsAcyclic (lineGraph (mycielskian G)) :=
  not_isAcyclic_lineGraph (by rw [maxDeg_mycielskian]; exact h3)

theorem not_isTree_lineGraph_mycielskian {G : IsoGraph}
    (h3 : 3 ≤ max (2 * maxDeg G) G.V) : ¬ IsTree (lineGraph (mycielskian G)) :=
  not_isTree_lineGraph (by rw [maxDeg_mycielskian]; exact h3)

/-! ### The connectivities of the basic families

`λ` and `κ` of the basic families.  Most are settled by connectedness and `minDeg` alone: an empty
graph and a disjoint union are disconnected, so both vanish; a path is connected with a degree-one
endpoint, so both are one.  The cycle needs an argument of its own for the lower bound — that is
`CGraph.two_le_edgeConn_cycle` and `CGraph.two_le_vertexConn_cycle` — and `minDeg` for the upper.
-/

@[simp] theorem edgeConn_empty (n : ℕ) : (empty n).edgeConn = 0 := by
  rw [edgeConn_eq_zero_iff]
  match n with
  | 0 | 1 => exact Or.inl (by simp)
  | (m + 2) => exact Or.inr (not_isConnected_empty m)

@[simp] theorem vertexConn_empty (n : ℕ) : (empty n).vertexConn = 0 := by
  rw [vertexConn_eq_zero_iff]
  match n with
  | 0 | 1 => exact Or.inl (by simp)
  | (m + 2) => exact Or.inr (not_isConnected_empty m)

@[simp] theorem edgeConn_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).edgeConn = 0 := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [V_mk] at hG hH
  rw [disjUnion_mk, edgeConn_mk]
  exact (G ⊕g H).edgeConn_eq_zero_iff.2 (Or.inr (CGraph.not_isConnected_disjUnion G H hG hH))

@[simp] theorem vertexConn_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).vertexConn = 0 := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [V_mk] at hG hH
  rw [disjUnion_mk, vertexConn_mk]
  exact (G ⊕g H).vertexConn_eq_zero_iff.2 (Or.inr (CGraph.not_isConnected_disjUnion G H hG hH))

@[simp] theorem edgeConn_path (n : ℕ) : (path (n + 2)).edgeConn = 1 := by
  refine le_antisymm ?_ ((one_le_edgeConn_iff _ (by rw [V_path]; omega)).2 (isConnected_path _))
  have h := edgeConn_le_minDeg (path (n + 2)) (by rw [V_path]; omega)
  rwa [minDeg_path] at h

@[simp] theorem vertexConn_path (n : ℕ) : (path (n + 2)).vertexConn = 1 := by
  refine le_antisymm ?_ ((one_le_vertexConn_iff _ (by rw [V_path]; omega)).2 (isConnected_path _))
  have h := vertexConn_le_edgeConn (path (n + 2))
  rwa [edgeConn_path] at h

@[simp] theorem edgeConn_cycle (n : ℕ) : (cycle (n + 3)).edgeConn = 2 := by
  refine le_antisymm ?_ ?_
  · have h := edgeConn_le_minDeg (cycle (n + 3)) (by rw [V_cycle]; omega)
    rwa [minDeg_cycle] at h
  · rw [cycle_def, edgeConn_mk]
    exact CGraph.two_le_edgeConn_cycle (by omega)

@[simp] theorem vertexConn_cycle (n : ℕ) : (cycle (n + 3)).vertexConn = 2 := by
  refine le_antisymm ?_ ?_
  · have h := vertexConn_le_edgeConn (cycle (n + 3))
    rwa [edgeConn_cycle] at h
  · rw [cycle_def, vertexConn_mk]
    exact CGraph.two_le_vertexConn_cycle (by omega)

/-! ### The edge connectivity of the products of a graph of diameter two

Plesník's theorem gives `λ = δ` for each of these, and the minimum degree is known in closed
form, so the edge connectivity is too. -/

/-- **The minimum degree of a Mycielskian** collapses to `δ(G) + 1` as soon as `G` is connected
with two vertices: the shadow of a vertex of least degree beats both the doubled copies and the
apex. -/
theorem minDeg_mycielskian_eq (G : IsoGraph) (hG : G.IsConnected) (h2 : 2 ≤ G.V) :
    (mycielskian G).minDeg = G.minDeg + 1 := by
  have hd1 : 1 ≤ G.minDeg := le_trans ((one_le_edgeConn_iff G h2).2 hG) (edgeConn_le_minDeg G h2)
  have hlt : G.minDeg < G.V := lt_of_le_of_lt (minDeg_le_maxDeg G) (maxDeg_lt_V (by omega))
  rw [minDeg_mycielskian G (by omega)]
  omega

/-- The strong product of two graphs of diameter at most two is maximally edge connected:
`λ(G ⊠ H) = (δ G + 1)(δ H + 1) - 1`. -/
theorem edgeConn_strongProduct {G H : IsoGraph} (hG : G.IsConnected) (hH : H.IsConnected)
    (hdG : G.diameter ≤ 2) (hdH : H.diameter ≤ 2) (h2 : 2 ≤ G.V * H.V) :
    (G ⊠g H).edgeConn = (G.minDeg + 1) * (H.minDeg + 1) - 1 := by
  have hG0 : 0 < G.V := Nat.pos_of_ne_zero fun h ↦ by simp [h] at h2
  have hH0 : 0 < H.V := Nat.pos_of_ne_zero fun h ↦ by simp [h] at h2
  rw [edgeConn_strongProduct_eq_minDeg hG hH hdG hdH h2, minDeg_strongProduct hG0 hH0]

/-- A blow-up of a graph of diameter at most two is maximally edge connected:
`λ(G · H) = δ(G)·|H| + δ(H)`. -/
theorem edgeConn_lexProduct {G H : IsoGraph} (hG : G.IsConnected) (hdG : G.diameter ≤ 2)
    (h2 : 2 ≤ G.V) (hH : 1 ≤ H.V) : (G ·g H).edgeConn = G.minDeg * H.V + H.minDeg := by
  rw [edgeConn_lexProduct_eq_minDeg hG hdG h2 hH, minDeg_lexProduct (by omega) hH]

/-- The Mycielskian of a connected graph of diameter at most two is maximally edge connected:
`λ(μ G) = δ(G) + 1`. -/
theorem edgeConn_mycielskian {G : IsoGraph} (hG : G.IsConnected) (hdG : G.diameter ≤ 2)
    (h2 : 2 ≤ G.V) : (mycielskian G).edgeConn = G.minDeg + 1 := by
  rw [edgeConn_mycielskian_eq_minDeg hG hdG h2, minDeg_mycielskian_eq G hG h2]

/-- **A cartesian product of maximally edge connected graphs is maximally edge connected**:
if `λ = δ` in both factors then `λ(G □ H) = δ(G) + δ(H)`. -/
theorem edgeConn_cartesianProduct {G H : IsoGraph} (hG : G.IsConnected) (hH : H.IsConnected)
    (hG2 : 2 ≤ G.V) (hH2 : 2 ≤ H.V) (hGm : G.edgeConn = G.minDeg) (hHm : H.edgeConn = H.minDeg) :
    (G □g H).edgeConn = G.minDeg + H.minDeg := by
  have hlow := edgeConn_add_edgeConn_le_edgeConn_cartesianProduct hG hH hG2 hH2
  have h4 : 2 * 2 ≤ G.V * H.V := Nat.mul_le_mul hG2 hH2
  have hhigh := edgeConn_le_minDeg (G □g H) (by rw [V_cartesianProduct]; omega)
  rw [minDeg_cartesianProduct (by omega) (by omega)] at hhigh
  omega

/-- The cartesian product of two graphs of diameter at most two is maximally edge connected. -/
theorem edgeConn_cartesianProduct_of_diameter_le_two {G H : IsoGraph} (hG : G.IsConnected)
    (hH : H.IsConnected) (hdG : G.diameter ≤ 2) (hdH : H.diameter ≤ 2) (hG2 : 2 ≤ G.V)
    (hH2 : 2 ≤ H.V) : (G □g H).edgeConn = G.minDeg + H.minDeg :=
  edgeConn_cartesianProduct hG hH hG2 hH2 (edgeConn_eq_minDeg_of_diameter_le_two hG hdG hG2)
    (edgeConn_eq_minDeg_of_diameter_le_two hH hdH hH2)

/-- **A cartesian product of maximally connected graphs is maximally connected**: if `κ = δ` in
both factors then `κ(G □ H) = δ(G) + δ(H)`. -/
theorem vertexConn_cartesianProduct {G H : IsoGraph} (hG : G.IsConnected) (hH : H.IsConnected)
    (hG2 : 2 ≤ G.V) (hH2 : 2 ≤ H.V) (hGm : G.vertexConn = G.minDeg)
    (hHm : H.vertexConn = H.minDeg) : (G □g H).vertexConn = G.minDeg + H.minDeg := by
  have hlow := vertexConn_add_vertexConn_le_vertexConn_cartesianProduct hG hH hG2 hH2
  have h4 : 2 * 2 ≤ G.V * H.V := Nat.mul_le_mul hG2 hH2
  have hhigh := vertexConn_le_minDeg (G □g H) (by rw [V_cartesianProduct]; omega)
  rw [minDeg_cartesianProduct (by omega) (by omega)] at hhigh
  omega

/-- **The connectivity of a rook's graph**: `κ(Kₘ □ Kₙ) = m + n - 2`. -/
@[simp] theorem vertexConn_rook (m n : ℕ) : (rook (m + 2) (n + 2)).vertexConn = m + n + 2 := by
  rw [show rook (m + 2) (n + 2) = complete (m + 2) □g complete (n + 2) from rfl,
    vertexConn_cartesianProduct (isConnected_complete _) (isConnected_complete _)
      (by rw [V_complete]; omega) (by rw [V_complete]; omega)
      (by rw [vertexConn_complete, minDeg_complete]) (by rw [vertexConn_complete, minDeg_complete]),
    minDeg_complete, minDeg_complete]
  omega

/-- **The connectivity of a prism**: a cycle is `2`-connected and `K₂` is `1`-connected, so the
prism over it is `3`-connected. -/
@[simp] theorem vertexConn_prism (n : ℕ) : (prism (n + 3)).vertexConn = 3 := by
  rw [show prism (n + 3) = cycle (n + 3) □g complete 2 from rfl,
    vertexConn_cartesianProduct (isConnected_cycle _) (isConnected_complete 1)
      (by rw [V_cycle]; omega) (by rw [V_complete])
      (by rw [vertexConn_cycle, minDeg_cycle]) (by rw [vertexConn_complete, minDeg_complete]),
    minDeg_cycle, minDeg_complete]

/-! ### The connectivity of the Petersen graph, on the quotient -/

@[simp] theorem edgeConn_petersen : petersen.edgeConn = 3 := by
  show (kneser 5 2).edgeConn = 3
  rw [kneser_def, edgeConn_mk]
  exact CGraph.edgeConn_petersen

@[simp] theorem vertexConn_petersen : petersen.vertexConn = 3 := by
  show (kneser 5 2).vertexConn = 3
  rw [kneser_def, vertexConn_mk]
  exact CGraph.vertexConn_petersen

/-! ### Graphs given by an LCF code

The code `[ss]^r` describes `ss.length * r` vertices strung on a ring, so everything that follows
from having a Hamiltonian cycle holds for the whole family at once, with no arithmetic on the
code.  The chords are what makes each such graph interesting, and they play no part here. -/

@[simp] theorem V_lcf (ss : List ℤ) (r : ℕ) : (lcf ss r).V = ss.length * r :=
  CGraph.card_lcf ss r

@[simp] theorem V_gp (n k : ℕ) : (gp n k).V = 2 * n := CGraph.card_gp n k

theorem isConnected_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    (lcf ss r).IsConnected := (isHamiltonian_lcf ss r h3).isConnected

theorem numComponents_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    (lcf ss r).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_lcf ss r h3)

theorem not_isAcyclic_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    ¬ (lcf ss r).IsAcyclic :=
  (isHamiltonian_lcf ss r h3).not_isAcyclic (by rw [V_lcf]; omega)

theorem not_isTree_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    ¬ (lcf ss r).IsTree :=
  fun h ↦ not_isAcyclic_lcf ss r h3 h.2

/-- **Every other edge of the ring is a matching**, and it leaves at most one vertex over.  The
chords play no part, so the code need not even be a valid one. -/
@[simp] theorem matchNum_lcf (ss : List ℤ) (r : ℕ) :
    (lcf ss r).matchNum = ss.length * r / 2 := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V (lcf ss r)
    rw [V_lcf] at h
    omega
  · have h := CGraph.card_le_matchNum (G := CGraph.lcf ss r)
      (fun i : Fin (ss.length * r / 2) ↦
        (⟨2 * i.1, by have := i.2; omega⟩ : Fin (ss.length * r)))
      (fun i : Fin (ss.length * r / 2) ↦
        (⟨2 * i.1 + 1, by have := i.2; omega⟩ : Fin (ss.length * r)))
      (fun i ↦ by
        have hi := i.2
        rw [CGraph.lcf_adj_val]
        refine ⟨by show 2 * i.1 ≠ 2 * i.1 + 1; omega,
          Or.inl (CGraph.mem_lcfEdges_iff.2 ⟨2 * i.1, by omega, Or.inl ⟨rfl, ?_⟩⟩)⟩
        show 2 * i.1 + 1 = (2 * i.1 + 1) % (ss.length * r)
        rw [Nat.mod_eq_of_lt (by omega)])
      (fun i j hij ↦ by
        have hi := i.2
        have hj := j.2
        have hne : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
        exact ⟨Fin.ne_of_val_ne (by show 2 * i.1 ≠ 2 * j.1; omega),
          Fin.ne_of_val_ne (by show 2 * i.1 ≠ 2 * j.1 + 1; omega),
          Fin.ne_of_val_ne (by show 2 * i.1 + 1 ≠ 2 * j.1; omega),
          Fin.ne_of_val_ne (by show 2 * i.1 + 1 ≠ 2 * j.1 + 1; omega)⟩)
    rw [Fintype.card_fin] at h
    rw [lcf_def, matchNum_mk]
    exact h

section ValidLcf

variable {ss : List ℤ} {r : ℕ}

theorem minDeg_lcf (h3 : 3 ≤ ss.length * r) (hv : IsValidLcf ss r) : minDeg (lcf ss r) = 3 :=
  (isRegularWith_lcf h3 hv).minDeg_eq (by rw [V_lcf]; omega)

theorem maxDeg_lcf (h3 : 3 ≤ ss.length * r) (hv : IsValidLcf ss r) : maxDeg (lcf ss r) = 3 :=
  (isRegularWith_lcf h3 hv).maxDeg_eq (by rw [V_lcf]; omega)

theorem degSequence_lcf (h3 : 3 ≤ ss.length * r) (hv : IsValidLcf ss r) :
    (lcf ss r).degSequence = List.replicate (ss.length * r) 3 := by
  rw [(isRegularWith_lcf h3 hv).degSequence, V_lcf]

theorem degMultiset_lcf (h3 : 3 ≤ ss.length * r) (hv : IsValidLcf ss r) :
    (lcf ss r).degMultiset = Multiset.replicate (ss.length * r) 3 := by
  rw [← coe_degSequence, degSequence_lcf h3 hv, Multiset.coe_replicate]

/-- A cubic graph has `3n/2` edges; stated doubled, so that no division appears. -/
theorem two_mul_E_lcf (h3 : 3 ≤ ss.length * r) (hv : IsValidLcf ss r) :
    2 * (lcf ss r).E = ss.length * r * 3 :=
  two_mul_E_of_degSequence_replicate (degSequence_lcf h3 hv)

end ValidLcf

/-! ### The generalized Petersen graphs

`gp n k` is cubic and connected for every admissible `n` and `k`, which settles its degrees, its
component count, and — since a cubic graph on `2n` vertices has `3n` edges, one too many for a
tree — its acyclicity. -/

section GP

variable {n k : ℕ}

theorem numComponents_gp (hn : 0 < n) : (gp n k).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_gp hn)

theorem minDeg_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    minDeg (gp n k) = 3 :=
  (isRegularWith_gp h3 hk hkn h2k).minDeg_eq (by rw [V_gp]; omega)

theorem maxDeg_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    maxDeg (gp n k) = 3 :=
  (isRegularWith_gp h3 hk hkn h2k).maxDeg_eq (by rw [V_gp]; omega)

theorem degSequence_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    (gp n k).degSequence = List.replicate (2 * n) 3 := by
  rw [(isRegularWith_gp h3 hk hkn h2k).degSequence, V_gp]

theorem degMultiset_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    (gp n k).degMultiset = Multiset.replicate (2 * n) 3 := by
  rw [← coe_degSequence, degSequence_gp h3 hk hkn h2k, Multiset.coe_replicate]

theorem E_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    (gp n k).E = 3 * n := by
  have h := two_mul_E_of_degSequence_replicate (degSequence_gp h3 hk hkn h2k)
  omega

theorem not_isTree_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    ¬ IsTree (gp n k) :=
  not_isTree_of_V_le_E (by rw [V_gp, E_gp h3 hk hkn h2k]; omega)

theorem not_isAcyclic_gp (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    ¬ (gp n k).IsAcyclic :=
  fun h ↦ not_isTree_gp h3 hk hkn h2k ⟨isConnected_gp (by omega), h⟩

/-- **The spokes of a generalized Petersen graph are a perfect matching.**  Spoke `i` joins the
outer vertex `i` to the inner vertex `n + i`, so the `n` of them cover all `2n` vertices; no
condition on `k` is needed, since the spokes are there whatever the inner ring does. -/
@[simp] theorem matchNum_gp (n k : ℕ) : (gp n k).matchNum = n := by
  refine le_antisymm ?_ ?_
  · have h := two_mul_matchNum_le_V (gp n k)
    rw [V_gp] at h
    omega
  · have h := CGraph.card_le_matchNum (G := CGraph.gp n k)
      (fun i : Fin n ↦ (⟨i.1, by have := i.2; omega⟩ : Fin (2 * n)))
      (fun i : Fin n ↦ (⟨n + i.1, by have := i.2; omega⟩ : Fin (2 * n)))
      (fun i ↦ by
        have hi := i.2
        rw [CGraph.gp_adj_val]
        exact ⟨by show i.1 ≠ n + i.1; omega,
          Or.inl (CGraph.mem_gpEdges.2 ⟨i.1, hi, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
      (fun i j hij ↦ by
        have hi := i.2
        have hj := j.2
        have hne : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
        exact ⟨Fin.ne_of_val_ne (by show i.1 ≠ j.1; omega),
          Fin.ne_of_val_ne (by show i.1 ≠ n + j.1; omega),
          Fin.ne_of_val_ne (by show n + i.1 ≠ j.1; omega),
          Fin.ne_of_val_ne (by show n + i.1 ≠ n + j.1; omega)⟩)
    rw [Fintype.card_fin] at h
    rw [gp_def, matchNum_mk]
    exact h

end GP

/-! ### Hamiltonian families, on the quotient

`fan`, `ladder`, `prism` and `crown` abbreviate a join or a product, and the abbreviation is
unfolded on the way through `@[toIsoGraph]`; these four are stated by hand so that the family name
survives into the quotient statement. -/

theorem isHamiltonian_fan {n : ℕ} (h2 : 2 ≤ n) : (fan n).IsHamiltonian := by
  rw [show fan n = complete 1 ∇g path n from rfl, complete_def, path_def, join_mk,
    isHamiltonian_mk]
  exact CGraph.isHamiltonian_fan h2

theorem isHamiltonian_prism {n : ℕ} (h3 : 3 ≤ n) : (prism n).IsHamiltonian := by
  rw [show prism n = cycle n □g complete 2 from rfl, cycle_def, complete_def,
    cartesianProduct_mk, isHamiltonian_mk]
  exact CGraph.isHamiltonian_prism h3

theorem isHamiltonian_ladder {n : ℕ} (h2 : 2 ≤ n) : (ladder n).IsHamiltonian := by
  rw [show ladder n = path n □g complete 2 from rfl, path_def, complete_def,
    cartesianProduct_mk, isHamiltonian_mk]
  exact CGraph.isHamiltonian_ladder h2

theorem isHamiltonian_crown {n : ℕ} (h3 : 3 ≤ n) : (crown n).IsHamiltonian := by
  rw [show crown n = complete n ⊗g complete 2 from rfl, complete_def, complete_def,
    tensorProduct_mk, isHamiltonian_mk]
  exact CGraph.isHamiltonian_crown h3

/-! ### Graphs that are not Hamiltonian -/

theorem not_isHamiltonian_empty (n : ℕ) : ¬ IsHamiltonian (empty (n + 2)) :=
  not_isHamiltonian_of_not_isConnected _ (not_isConnected_empty n)

theorem not_isHamiltonian_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ IsHamiltonian (G ⊕g H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [V_mk] at hG hH
  rw [disjUnion_mk, isHamiltonian_mk]
  exact CGraph.not_isHamiltonian_of_not_isConnected _ (CGraph.not_isConnected_disjUnion G H hG hH)

theorem not_isHamiltonian_path (n : ℕ) : ¬ IsHamiltonian (path (n + 3)) :=
  not_isHamiltonian_of_isAcyclic (isAcyclic_path _) (by rw [V_path]; omega)

/-- A tree on three vertices or more is not Hamiltonian: it has no cycle to be one. -/
theorem IsTree.not_isHamiltonian {G : IsoGraph} (h : IsTree G) (h3 : 3 ≤ G.V) :
    ¬ IsHamiltonian G :=
  not_isHamiltonian_of_isAcyclic ((isTree_iff_isConnected_and_isAcyclic G).1 h).2 h3

end IsoGraph
