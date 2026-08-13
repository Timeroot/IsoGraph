import IsoGraph.Values.Identities.Families

/-!
# Circulants, grids, and vertex transitivity

The invariants of the circulant graphs, which are their own chapter because the parameters are a
list of jumps rather than a number, and then the `2 × n` grid, whose whole table follows from its
degree sequence.

Vertex transitivity is the other theme: the families that have it, what it gives (the common
degree, the clique–coclique consequences for the Johnson graphs), and the graphs that fail it
because their degrees are not all equal.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ### Invariants of the circulant graphs

Every circulant graph is vertex transitive, and a great deal follows from that alone: it is
regular, its radius equals its diameter, and the clique–coclique bound `α · ω ≤ |V|` applies.
The complement of a circulant is again vertex transitive. -/

theorem exists_degSequence_replicate_circulant (n : ℕ) (S : List ℕ) :
    ∃ k, degSequence (circulant n S) = List.replicate n k := by
  have h := exists_degSequence_replicate_of_isVertexTransitive (isVertexTransitive_circulant n S)
  rwa [V_circulant] at h

theorem exists_isRegularWith_circulant (n : ℕ) (S : List ℕ) :
    ∃ k, (circulant n S).IsRegularWith k :=
  exists_isRegularWith_of_isVertexTransitive (isVertexTransitive_circulant n S)

/-- A circulant graph is regular, so its vertex and edge counts pin down its degree sequence. -/
theorem degSequence_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : degSequence (circulant n S) = List.replicate n k := by
  have h := degSequence_of_isVertexTransitive (k := k) (isVertexTransitive_circulant n S)
    (by rwa [V_circulant]) (by rwa [V_circulant])
  rwa [V_circulant] at h

@[simp] theorem maxDeg_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : maxDeg (circulant n S) = k :=
  maxDeg_eq_of_degSequence_replicate hn (degSequence_circulant hn hk)

@[simp] theorem minDeg_circulant {n k : ℕ} {S : List ℕ} (hn : 0 < n)
    (hk : n * k = 2 * (circulant n S).E) : minDeg (circulant n S) = k :=
  minDeg_eq_of_degSequence_replicate hn (degSequence_circulant hn hk)

@[simp] theorem radius_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).radius = (circulant n S).diameter :=
  radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_circulant n S)

theorem indepNum_mul_cliqueNum_le_V_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).indepNum * (circulant n S).cliqueNum ≤ n := by
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_circulant n S)
  rwa [V_circulant] at h

theorem two_mul_indepNum_le_V_circulant {n : ℕ} {S : List ℕ} (hE : 0 < (circulant n S).E) :
    2 * (circulant n S).indepNum ≤ n := by
  have h := two_mul_indepNum_le_V (isVertexTransitive_circulant n S) hE
  rwa [V_circulant] at h

@[simp] theorem isVertexTransitive_compl_circulant (n : ℕ) (S : List ℕ) :
    IsVertexTransitive (circulant n S)ᶜ :=
  (isVertexTransitive_circulant n S).compl

theorem coverNum_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).coverNum = n - (circulant n S).indepNum := by
  have h := (circulant n S).coverNum_add_indepNum
  rw [V_circulant] at h
  omega

/-- A rook graph has a matching that misses at most one vertex. -/
theorem matchNum_rook (m n : ℕ) :
    (rook (m + 1) (n + 1)).matchNum = (m + 1) * (n + 1) / 2 := by
  rw [matchNum_eq]
  apply le_antisymm
  · -- Upper bound: 2 * indepNum(L(rook)) ≤ V(rook) = (m+1)*(n+1)
    have h := (rook (m + 1) (n + 1)).two_mul_matchNum_le_V
    rw [matchNum_eq] at h
    rw [show (rook (m + 1) (n + 1)).V = (m + 1) * (n + 1) from by simp [rook]] at h
    omega
  · -- Lower bound
    rw [← matchNum_eq]
    rw [rook, matchNum_eq]
    -- Case split on parity of n+1
    rcases Nat.even_or_odd' (n + 1) with ⟨k, hk | hk⟩
    · -- n+1 = 2*k (even): horizontal pairing in each row, (m+1)*k edges
      rw [hk]
      have : (m + 1) * (2 * k) / 2 = (m + 1) * k := by
        have : ∀ a b : ℕ, a * (2 * b) / 2 = a * b := fun a b => by
          rw
            [show a * (2 * b) = 2 * (a * b) from by ring,
              Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
        rw [this]
      rw [this]
      dsimp only [complete]
      rw [cartesianProduct_mk, lineGraph_mk, indepNum_mk]
      -- Build S = image of horizontal edges H(i,j) for i : Fin(m+1), j : Fin k
      let v0 : Fin (m + 1) × Fin k → Fin (m + 1) × Fin (2 * k) := fun ⟨i, j⟩ => (i,
        ⟨2 * (j : ℕ), by omega⟩)
      let v1 : Fin (m + 1) × Fin k → Fin (m + 1) × Fin (2 * k) := fun ⟨i, j⟩ => (i,
        ⟨2 * (j : ℕ) + 1, by omega⟩)
      have huv_adj : ∀ p : Fin (m + 1) × Fin k,
          (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete (2 * k))).Adj (v0 p)
            (v1 p) := by
        intro ⟨i, j⟩
        rw [CGraph.cartesianProduct_adj]
        simp [v0, v1, CGraph.complete_adj]
      -- edgeVertex for horizontal edges
      let edgeVertex : Fin (m + 1) × Fin k → (CGraph.lineGraph (CGraph.cartesianProduct
        (CGraph.complete (m + 1)) (CGraph.complete (2 * k)))).V :=
        fun p => ⟨Sym2.mk (v0 p, v1 p), by
          rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
          exact huv_adj p⟩
      let S : Finset ((CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1))
        (CGraph.complete (2 * k)))).V) :=
        Finset.univ.image edgeVertex
      -- Disjointness
      have hv0_fst : ∀ p : Fin (m + 1) × Fin k, (v0 p).1 = p.1 := by simp [v0]
      have hv1_fst : ∀ p : Fin (m + 1) × Fin k, (v1 p).1 = p.1 := by simp [v1]
      have hv0_snd_eq : ∀ p : Fin (m + 1) × Fin k, (v0 p).2.val = 2 * (p.2 : ℕ) := by simp [v0]
      have hv1_snd_eq : ∀ p : Fin (m + 1) × Fin k, (v1 p).2.val = 2 * (p.2 : ℕ) + 1 := by simp [v1]
      have hne_snd : ∀ p : Fin (m + 1) × Fin k, (v0 p).2 ≠ (v1 p).2 := by
        intro ⟨i, j⟩
        simp [v0, v1]
      have hdisjoint : ∀ p q : Fin (m + 1) × Fin k, p ≠ q →
          ¬∃ v : Fin (m + 1) × Fin (2 * k), v ∈ (Sym2.mk (v0 p, v1 p) : Sym2 (Fin (m + 1) × Fin (2 *
            k))) ∧
            v ∈ (Sym2.mk (v0 q, v1 q) : Sym2 (Fin (m + 1) × Fin (2 * k))) := by
        intro p q hpq ⟨v, hv1, hv2⟩
        rw [Sym2.mem_iff] at hv1 hv2
        -- hv1 : v = v0 p ∨ v = v1 p, hv2 : v = v0 q ∨ v = v1 q
        -- v0 p has fst = p.1, snd.val = 2*p.2; v1 p has fst = p.1, snd.val = 2*p.2+1
        -- Same for q. Since 2*a and 2*b+1 have different parity, v0 p can only equal v0 q or v1 q
        -- with appropriate parity match. But v0 p (even snd) can't equal v1 q (odd snd), and vice
        -- versa.
        -- And v0 p = v0 q implies p = q, contradiction. Same for v1.
        rcases hv1 with rfl | rfl
        · -- v = v0 p
          rcases hv2 with hx | hx
          · -- v = v0 q
            dsimp [v0] at hx
            have h1 : p.1 = q.1 := by simpa using congr_arg Prod.fst hx
            have h2 : (p.2 : ℕ) = (q.2 : ℕ) := by simpa using congr_arg Prod.snd hx
            exact hpq (Prod.ext h1 (Fin.ext h2))
          · -- v = v1 q, parity contradiction
            dsimp [v1] at hx
            have h2 : ((v0 p).2 : ℕ) = ((v1 q).2 : ℕ) := by
              have := congr_arg Prod.snd hx; exact congr_arg Fin.val this
            simp [hv0_snd_eq, hv1_snd_eq] at h2
            omega
        · -- v = v1 p
          rcases hv2 with hx | hx
          · -- v = v0 q, parity contradiction
            dsimp [v0] at hx
            have h2 : ((v1 p).2 : ℕ) = ((v0 q).2 : ℕ) := by
              have := congr_arg Prod.snd hx; exact congr_arg Fin.val this
            simp [hv0_snd_eq, hv1_snd_eq] at h2
            omega
          · -- v = v1 q
            dsimp [v1] at hx
            have h1 : p.1 = q.1 := by simpa using congr_arg Prod.fst hx
            have h2 : (p.2 : ℕ) = (q.2 : ℕ) := by simpa using congr_arg Prod.snd hx
            exact hpq (Prod.ext h1 (Fin.ext h2))
      -- Independence
      have hS_indep : (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1))
        (CGraph.complete (2 * k)))).toSimple.IsIndepSet S := by
        intro e he f hf haf
        simp only [S] at he hf
        rw [Finset.mem_coe, Finset.mem_image] at he hf
        obtain ⟨x, _, rfl⟩ := he
        obtain ⟨y, _, rfl⟩ := hf
        simp [CGraph.toSimple_adj, CGraph.lineGraph_adj]
        intro _
        have hne : x ≠ y := fun h => haf (h ▸ rfl)
        intro v hv hx1v
        exact hdisjoint x y hne ⟨v, hv, hx1v⟩
      -- Injectivity
      have hinj : Function.Injective edgeVertex := by
        intro p q hxy
        have hsym2 : Sym2.mk (v0 p, v1 p) = Sym2.mk (v0 q, v1 q) := Subtype.ext_iff.mp hxy
        rcases Sym2.eq_iff.1 hsym2 with ⟨h1, _⟩ | ⟨h1, h2⟩
        · -- v0 p = v0 q
          dsimp [v0] at h1
          have hp1 : p.1 = q.1 := by simpa using congr_arg Prod.fst h1
          have hp2 : (p.2 : ℕ) = (q.2 : ℕ) := by simpa using congr_arg Prod.snd h1
          exact Prod.ext hp1 (Fin.ext hp2)
        · -- v0 p = v1 q and v1 p = v0 q: parity contradiction
          exfalso
          dsimp [v0, v1] at h1 h2
          have := congr_arg (fun x : Fin (m+1) × Fin (2*k) => (x.2 : ℕ)) h1
          simp at this
          omega
      -- Cardinality
      have hS_card : S.card = (m + 1) * k := by
        show Finset.card (Finset.image edgeVertex Finset.univ) = (m + 1) * k
        rw [Finset.card_image_of_injective _ hinj]
        simp [Finset.card_univ, Fintype.card_prod]
      exact hS_card ▸ hS_indep.card_le_indepNum
    · -- n+1 = 2*k+1 (odd): horizontal edges in all rows + vertical edges in last column
      rw [hk]
      -- Target: (m+1)*(2*k+1)/2 ≤ indepNum ...
      -- (m+1)*(2*k+1)/2 = (m+1)*k + (m+1)/2
      have htarget : (m + 1) * (2 * k + 1) / 2 = (m + 1) * k + (m + 1) / 2 := by
        have : (m + 1) * (2 * k + 1) = 2 * ((m + 1) * k) + (m + 1) := by ring
        rw [this]
        omega
      rw [htarget]
      -- Build horizontal edges H(i,j) for i : Fin(m+1), j : Fin k
      -- and vertical edges V(t) for t : Fin((m+1)/2) in column n = 2*k
      let mv2 := (m + 1) / 2
      -- Final column index
      let last_col : Fin (2 * k + 1) := ⟨2 * k, by omega⟩
      -- Horizontal edge endpoints
      let hv0 : Fin (m + 1) × Fin k → Fin (m + 1) × Fin (2 * k + 1) :=
        fun ⟨i, j⟩ => (i, ⟨2 * (j : ℕ), by omega⟩)
      let hv1 : Fin (m + 1) × Fin k → Fin (m + 1) × Fin (2 * k + 1) :=
        fun ⟨i, j⟩ => (i, ⟨2 * (j : ℕ) + 1, by omega⟩)
      -- Vertical edge endpoints (in last column)
      let hv0v : Fin mv2 → Fin (m + 1) × Fin (2 * k + 1) :=
        fun t => (⟨2 * (t : ℕ), by omega⟩, last_col)
      let hv1v : Fin mv2 → Fin (m + 1) × Fin (2 * k + 1) :=
        fun t => (⟨2 * (t : ℕ) + 1, by omega⟩, last_col)
      -- Adjacency for horizontal edges
      have hh_adj : ∀ p : Fin (m + 1) × Fin k,
          (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete (2 * k + 1))).Adj (hv0
            p) (hv1 p) := by
        intro ⟨i, j⟩
        rw [CGraph.cartesianProduct_adj]
        simp [hv0, hv1, CGraph.complete_adj]
      -- Adjacency for vertical edges
      have hvv_adj : ∀ t : Fin mv2,
          (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete (2 * k + 1))).Adj
            (hv0v t) (hv1v t) := by
        intro t
        rw [CGraph.cartesianProduct_adj]
        simp [hv0v, hv1v, last_col, CGraph.complete_adj]
      -- edgeVertex for horizontal edges
      let hEdgeVertex : Fin (m + 1) × Fin k →
          (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete (2 *
            k + 1)))).V :=
        fun p => ⟨Sym2.mk (hv0 p, hv1 p), by
          rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
          exact hh_adj p⟩
      -- edgeVertex for vertical edges
      let vEdgeVertex : Fin mv2 →
          (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete (2 *
            k + 1)))).V :=
        fun t => ⟨Sym2.mk (hv0v t, hv1v t), by
          rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
          exact hvv_adj t⟩
      -- Helper: horizontal edge endpoints have 2nd coord < 2*k < 2*k+1, so ≠ last_col
      have hH_col_lt : ∀ p : Fin (m + 1) × Fin k, (hv0 p).2.val < 2 * k ∧ (hv1 p).2.val < 2 * k :=
        by
        simp [hv0, hv1]; intros; omega
      -- last_col.val = 2*k
      have hlast_col_val : last_col.val = 2 * k := rfl
      -- Horizontal edges disjoint from vertical edges (different columns)
      have hv0v_snd_val : ∀ t : Fin mv2, (hv0v t).2.val = 2 * k := by simp [hv0v, hlast_col_val]
      have hv1v_snd_val : ∀ t : Fin mv2, (hv1v t).2.val = 2 * k := by simp [hv1v, hlast_col_val]
      have hHV_disjoint : ∀ p : Fin (m + 1) × Fin k, ∀ t : Fin mv2,
          ¬∃ v : Fin (m + 1) × Fin (2 * k + 1), v ∈ (Sym2.mk (hv0 p, hv1 p) : Sym2 _) ∧
            v ∈ (Sym2.mk (hv0v t, hv1v t) : Sym2 _) := by
        intro p t ⟨v, hv1, hv2⟩
        rw [Sym2.mem_iff] at hv1 hv2
        have hlt0 := (hH_col_lt p).1
        rcases hv1 with hv1 | hv1
        · rcases hv2 with hv2 | hv2
          · exfalso; rw [hv1] at hv2; have h2 := congr_arg Prod.snd hv2; have := hv0v_snd_val t;
              omega
          · exfalso; rw [hv1] at hv2; have h2 := congr_arg Prod.snd hv2; have := hv1v_snd_val t;
              omega
        · rcases hv2 with hv2 | hv2
          · exfalso; rw [hv1] at hv2; have h2 := congr_arg Fin.val (congr_arg Prod.snd hv2); have :=
              (hH_col_lt p).2; have := hv0v_snd_val t; omega
          · exfalso; rw [hv1] at hv2; have h2 := congr_arg Fin.val (congr_arg Prod.snd hv2); have :=
              (hH_col_lt p).2; have := hv1v_snd_val t; omega
      -- Vertical edges disjoint among themselves
      have hv0v_fst : ∀ t : Fin mv2, (hv0v t).1.val = 2 * (t : ℕ) := by simp [hv0v]
      have hv1v_fst : ∀ t : Fin mv2, (hv1v t).1.val = 2 * (t : ℕ) + 1 := by simp [hv1v]
      have hv0v_snd : ∀ t : Fin mv2, (hv0v t).2 = last_col := by simp [hv0v]
      have hv1v_snd : ∀ t : Fin mv2, (hv1v t).2 = last_col := by simp [hv1v]
      have hne_snd_v : ∀ t : Fin mv2, (hv0v t).1 ≠ (hv1v t).1 := by
        intro t; simp [hv0v, hv1v]
      have hVV_disjoint : ∀ t t' : Fin mv2, t ≠ t' →
          ¬∃ v : Fin (m + 1) × Fin (2 * k + 1), v ∈ (Sym2.mk (hv0v t, hv1v t) : Sym2 _) ∧
            v ∈ (Sym2.mk (hv0v t', hv1v t') : Sym2 _) := by
        intro t t' hne ⟨v, hv1, hv2⟩
        rw [Sym2.mem_iff] at hv1 hv2
        rcases hv1 with rfl | rfl
        · rcases hv2 with hx | hx
          · dsimp [hv0v] at hx
            have h1 : (t : ℕ) = (t' : ℕ) := by
              have := congr_arg Prod.fst hx
              simp at this
              omega
            exact hne (Fin.ext h1)
          · dsimp [hv1v] at hx
            have h2 : ((hv0v t).1 : ℕ) = ((hv1v t').1 : ℕ) := by
              have := congr_arg Prod.fst hx; exact congr_arg Fin.val this
            simp [hv0v_fst, hv1v_fst] at h2
            omega
        · rcases hv2 with hx | hx
          · dsimp [hv0v] at hx
            have h2 : ((hv1v t).1 : ℕ) = ((hv0v t').1 : ℕ) := by
              have := congr_arg Prod.fst hx; exact congr_arg Fin.val this
            simp [hv0v_fst, hv1v_fst] at h2
            omega
          · dsimp [hv1v] at hx
            have h1 : (t : ℕ) = (t' : ℕ) := by
              have := congr_arg Prod.fst hx
              simp at this
              omega
            exact hne (Fin.ext h1)
      -- EdgeVertex injectivity
      have hhEdge_inj : Function.Injective hEdgeVertex := by
        intro p q hxy
        have hsym2 : Sym2.mk (hv0 p, hv1 p) = Sym2.mk (hv0 q, hv1 q) := Subtype.ext_iff.mp hxy
        rcases Sym2.eq_iff.1 hsym2 with ⟨h1, _⟩ | ⟨h1, h2⟩
        · dsimp [hv0] at h1
          have hp1 : p.1 = q.1 := by simpa using congr_arg Prod.fst h1
          have hp2 : (p.2 : ℕ) = (q.2 : ℕ) := by
            have := congr_arg Prod.snd h1
            simp at this
            omega
          exact Prod.ext hp1 (Fin.ext hp2)
        · exfalso
          dsimp [hv0, hv1] at h1 h2
          have := congr_arg (fun x : Fin (m+1) × Fin (2*k+1) => (x.2 : ℕ)) h1
          simp at this
          omega
      have hvEdge_inj : Function.Injective vEdgeVertex := by
        intro t t' hxy
        have hsym2 : Sym2.mk (hv0v t, hv1v t) = Sym2.mk (hv0v t', hv1v t') := Subtype.ext_iff.mp hxy
        rcases Sym2.eq_iff.1 hsym2 with ⟨h1, _⟩ | ⟨h1, h2⟩
        · dsimp [hv0v] at h1
          have ht : (t : ℕ) = (t' : ℕ) := by
            have := congr_arg Prod.fst h1
            simp at this
            omega
          exact Fin.ext ht
        · exfalso
          dsimp [hv0v, hv1v] at h1 h2
          have := congr_arg (fun x : Fin (m+1) × Fin (2*k+1) => (x.1 : ℕ)) h1
          simp at this
          omega
      -- H-image and V-image are disjoint as Finsets
      have hS_disjoint : Disjoint (Finset.univ.image hEdgeVertex) (Finset.univ.image vEdgeVertex) :=
        by
        rw [Finset.disjoint_left]
        intro e he1 he2
        rw [Finset.mem_image] at he1 he2
        obtain ⟨p, _, hp⟩ := he1
        obtain ⟨t, _, ht⟩ := he2
        exfalso
        have heq : hEdgeVertex p = vEdgeVertex t := hp.trans ht.symm
        have hsym2 : Sym2.mk (hv0 p, hv1 p) = Sym2.mk (hv0v t, hv1v t) := Subtype.ext_iff.mp heq
        exact hHV_disjoint p t ⟨hv0 p, Sym2.mem_mk_left _ _, hsym2 ▸ Sym2.mem_mk_left _ _⟩
      -- H-image is independent
      have hhS_indep : (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1))
        (CGraph.complete (2 * k + 1)))).toSimple.IsIndepSet (Finset.univ.image hEdgeVertex) := by
        intro e he f hf haf
        simp only [Finset.coe_image, Set.mem_image] at he hf
        obtain ⟨x, _, rfl⟩ := he
        obtain ⟨y, _, rfl⟩ := hf
        simp [CGraph.toSimple_adj, CGraph.lineGraph_adj]
        intro _
        have hne : x ≠ y := fun h => haf (h ▸ rfl)
        intro v hv hx1v
        have : ∀ p q : Fin (m + 1) × Fin k, p ≠ q →
            ¬∃ v : Fin (m + 1) × Fin (2 * k + 1), v ∈ (Sym2.mk (hv0 p, hv1 p) : Sym2 _) ∧
              v ∈ (Sym2.mk (hv0 q, hv1 q) : Sym2 _) := by
          intro p q hpq ⟨v, hv1, hv2⟩
          rw [Sym2.mem_iff] at hv1 hv2
          rcases hv1 with rfl | rfl
          · rcases hv2 with hx | hx
            · -- hv0 p = hv0 q
              dsimp [hv0] at hx
              have h1 : p.1 = q.1 := by simpa using congr_arg Prod.fst hx
              have h2 : (p.2 : ℕ) = (q.2 : ℕ) := by
                simpa using congr_arg Fin.val (congr_arg Prod.snd hx)
              exact hpq (Prod.ext h1 (Fin.ext h2))
            · -- hv0 p = hv1 q, parity contradiction
              dsimp [hv0, hv1] at hx
              have := congr_arg (fun x : Fin (m+1) × Fin (2*k+1) => (x.2 : ℕ)) hx
              simp at this; omega
          · rcases hv2 with hx | hx
            · -- hv1 p = hv0 q, parity contradiction
              dsimp [hv0, hv1] at hx
              have := congr_arg (fun x : Fin (m+1) × Fin (2*k+1) => (x.2 : ℕ)) hx
              simp at this; omega
            · -- hv1 p = hv1 q
              dsimp [hv1] at hx
              have h1 : p.1 = q.1 := by simpa using congr_arg Prod.fst hx
              have h2 : (p.2 : ℕ) = (q.2 : ℕ) := by
                simpa using congr_arg Fin.val (congr_arg Prod.snd hx)
              exact hpq (Prod.ext h1 (Fin.ext h2))
        exact this x y hne ⟨v, hv, hx1v⟩
      -- V-image is independent
      have hvS_indep : (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1))
        (CGraph.complete (2 * k + 1)))).toSimple.IsIndepSet (Finset.univ.image vEdgeVertex) := by
        intro e he f hf haf
        simp only [Finset.coe_image, Set.mem_image] at he hf
        obtain ⟨t, _, rfl⟩ := he
        obtain ⟨t', _, rfl⟩ := hf
        simp [CGraph.toSimple_adj, CGraph.lineGraph_adj]
        intro _
        have hne : t ≠ t' := fun h => haf (h ▸ rfl)
        intro v hv hv1v
        exact hVV_disjoint t t' hne ⟨v, hv, hv1v⟩
      -- H and V images have no edges between them in lineGraph (disjoint vertex sets gives this...
      -- actually indep set across union needs more)
      -- Actually, for the union to be independent, we need: no edges within H (done), no edges
      -- within V (done), and no edges between H and V.
      -- No edges between H and V in lineGraph means H edges and V edges don't share endpoints,
      -- which is hHV_disjoint.
      have h_cross : ∀ p : Fin (m + 1) × Fin k, ∀ t : Fin mv2,
          ¬(CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete (2
            * k + 1)))).Adj (hEdgeVertex p) (vEdgeVertex t) := by
        intro p t
        simp [CGraph.lineGraph_adj, hEdgeVertex, vEdgeVertex]
        have hne0 : hv0 p ≠ hv0v t := by
          intro h
          have h1 := congr_arg Prod.snd h
          have h2 := (hH_col_lt p).1
          simp [hv0v_snd] at h1
          have := congr_arg Fin.val h1
          simp at this
          omega
        have hne1 : hv0 p ≠ hv1v t := by
          intro h
          have h1 := congr_arg Prod.snd h
          have h2 := (hH_col_lt p).1
          simp [hv1v_snd] at h1
          have := congr_arg Fin.val h1
          simp at this
          omega
        have hne2 : hv1 p ≠ hv0v t := by
          intro h
          have h1 := congr_arg Prod.snd h
          have h2 := (hH_col_lt p).2
          simp [hv0v_snd] at h1
          have := congr_arg Fin.val h1
          simp at this
          omega
        have hne3 : hv1 p ≠ hv1v t := by
          intro h
          have h1 := congr_arg Prod.snd h
          have h2 := (hH_col_lt p).2
          simp [hv1v_snd] at h1
          have := congr_arg Fin.val h1
          simp at this
          omega
        intro _ _
        exact ⟨⟨hne0, hne1⟩, hne2, hne3⟩
      have h_union_indep : (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1))
        (CGraph.complete (2 * k + 1)))).toSimple.IsIndepSet
          (↑(Finset.univ.image hEdgeVertex ∪ Finset.univ.image vEdgeVertex)) := by
        have h_cross_toSimple : ∀ p : Fin (m + 1) × Fin k, ∀ t : Fin mv2,
            ¬(CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete
              (2 * k + 1)))).toSimple.Adj (hEdgeVertex p) (vEdgeVertex t) := by
          intro p t hadj
          rw [CGraph.toSimple_adj] at hadj
          exact h_cross p t hadj
        have h_cross_toSimple' : ∀ p : Fin (m + 1) × Fin k, ∀ t : Fin mv2,
            ¬(CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete
              (2 * k + 1)))).toSimple.Adj (vEdgeVertex t) (hEdgeVertex p) := by
          intro p t hadj
          rw [CGraph.toSimple_adj] at hadj
          have hsymm : ∀ e f : (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1))
            (CGraph.complete (2 * k + 1)))).V,
              (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete
                (2 * k + 1)))).Adj e f =
              (CGraph.lineGraph (CGraph.cartesianProduct (CGraph.complete (m + 1)) (CGraph.complete
                (2 * k + 1)))).Adj f e := by
            intro e f
            rw [CGraph.lineGraph_adj, CGraph.lineGraph_adj]
            simp [and_comm, eq_comm]
          rw [hsymm] at hadj
          exact h_cross p t hadj
        intro e he f hf haf
        simp at he hf
        rcases he with he | he
        · obtain ⟨p, hp, rfl⟩ := he
          rcases hf with hf | hf
          · obtain ⟨q, hq, rfl⟩ := hf
            exact hhS_indep (Finset.mem_image_of_mem _ (Finset.mem_univ (p, hp)))
                (Finset.mem_image_of_mem _ (Finset.mem_univ (q, hq))) haf
          · obtain ⟨t', ht', rfl⟩ := hf
            exact h_cross_toSimple (p, hp) t'
        · obtain ⟨t, ht, rfl⟩ := he
          rcases hf with hf | hf
          · obtain ⟨q, hq, rfl⟩ := hf
            exact h_cross_toSimple' (q, hq) t
          · obtain ⟨t', ht', rfl⟩ := hf
            exact hvS_indep (Finset.mem_image_of_mem _ (Finset.mem_univ t))
                (Finset.mem_image_of_mem _ (Finset.mem_univ t')) haf
      -- Cardinality
      have hS_card : ((Finset.univ.image hEdgeVertex) ∪ (Finset.univ.image vEdgeVertex)).card = (m +
        1) * k + (m + 1) / 2 := by
        rw [Finset.card_union_of_disjoint hS_disjoint]
        rw [Finset.card_image_of_injective _ hhEdge_inj, Finset.card_image_of_injective _
          hvEdge_inj]
        simp [Finset.card_univ, Fintype.card_prod, mv2]
      -- Now lift to IsoGraph level and conclude
      dsimp only [IsoGraph.complete]
      rw [cartesianProduct_mk, lineGraph_mk, indepNum_mk]
      exact hS_card ▸ h_union_indep.card_le_indepNum

/-- Two `k`-sets differing in `d` elements are at distance `d`, and `d ≤ min k (n - k)`. -/
theorem diameter_johnson {n k : ℕ} (hk : k ≤ n) :
    (johnson n k).diameter = min k (n - k) := by
  -- johnson here is IsoGraph.johnson = ⟦CGraph.johnson n k⟧
  -- We need to work with CGraph.johnson n k
  have : (johnson n k : IsoGraph) = Quotient.mk _ (CGraph.johnson n k) := rfl
  rw [this, diameter_mk]
  simp [CGraph.diameter, SimpleGraph.diam]
  set G := (CGraph.johnson n k).toSimple
  -- Adjacency in G
  have adj_char : ∀ s t : (CGraph.johnson n k).V, G.Adj s t ↔ s ≠ t ∧ (s.val ∩ t.val).card = k - 1
    := by
    simp [G, CGraph.johnson_adj]
  -- Key: edist(s, t) = k - |s ∩ t|.card
  -- Step 1: Upper bound on edist via swap path
  have edist_le_k_inter : ∀ s t : (CGraph.johnson n k).V, G.edist s t ≤ (k - (s.val ∩ t.val).card :
    ℕ∞) := by
    -- Bound edist by |s \ t| = k - |s ∩ t|
    -- Induction: if s = t, edist = 0. If s ≠ t, swap one element to get closer.
    have key : ∀ d : ℕ, ∀ s t : (CGraph.johnson n k).V, k - (s.val ∩ t.val).card = d → G.edist s t ≤
      (d : ℕ∞) := by
      intro d
      induction d with
      | zero =>
        intro s t h0
        have hcard_le : (s.val ∩ t.val).card ≤ k := by
          exact le_trans (Finset.card_le_card Finset.inter_subset_left) s.property.le
        have hcard_inter : (s.val ∩ t.val).card = k := by omega
        have hsub_s : s.val ⊆ t.val := by
          have hel : (s.val ∩ t.val) = s.val :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left
              (by show (s.val).card ≤ (s.val ∩ t.val).card; rw [hcard_inter]; exact s.property.le)
          exact Finset.inter_eq_left.mp hel
        have hsub_t : t.val ⊆ s.val := by
          have hcard_inter' : (t.val ∩ s.val).card = k := by
            rw [Finset.inter_comm]
            exact hcard_inter
          have hel : (t.val ∩ s.val) = t.val :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left
              (by show (t.val).card ≤ (t.val ∩ s.val).card; rw [hcard_inter']; exact t.property.le)
          exact Finset.inter_eq_left.mp hel
        have : s.val = t.val := Finset.Subset.antisymm hsub_s hsub_t
        simp [Subtype.ext this, SimpleGraph.edist_self]
      | succ d ih =>
        intro s t hd
        have hcard_inter : (s.val ∩ t.val).card = k - (d + 1) := by omega
        have hcard_st : (s.val \ t.val).card = d + 1 := by
          rw [Finset.card_sdiff, s.property, Finset.inter_comm, hcard_inter]
          omega
        have hcard_ts : (t.val \ s.val).card = d + 1 := by
          rw [Finset.card_sdiff, t.property, hcard_inter]
          omega
        have hk1 : 1 ≤ k := by omega
        obtain ⟨a, ha_s, ha_t⟩ : ∃ a, a ∈ s.val ∧ a ∉ t.val := by
          obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (s.val \ t.val).card)
          exact ⟨a, Finset.mem_sdiff.mp ha |>.1, Finset.mem_sdiff.mp ha |>.2⟩
        obtain ⟨b, hb_t, hb_s⟩ : ∃ b, b ∈ t.val ∧ b ∉ s.val := by
          obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (t.val \ s.val).card)
          exact ⟨b, Finset.mem_sdiff.mp hb |>.1, Finset.mem_sdiff.mp hb |>.2⟩
        let s'_val : Finset (Fin n) := (s.val \ {a}) ∪ {b}
        have hs'_card : s'_val.card = k := by
          have hdisj : Disjoint (s.val \ {a}) {b} := by
            rw [Finset.disjoint_singleton_right]
            exact fun h => hb_s (Finset.mem_sdiff.mp h |>.1)
          have hcard_sa : (s.val ∩ {a}).card = 1 := by
            rw [Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr ha_s)]
            exact Finset.card_singleton a
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff]
          rw
            [show ({a} ∩ s.val).card = (s.val ∩ {a}).card by rw [Finset.inter_comm],
              hcard_sa, Finset.card_singleton, s.property]
          omega
        let s' : (CGraph.johnson n k).V := ⟨s'_val, hs'_card⟩
        have hab : a ≠ b := by intro h; exact ha_t (h ▸ hb_t)
        have ha_not_in_s' : a ∉ s'_val := by
          simp [s'_val, Finset.mem_sdiff, Finset.mem_singleton]
          tauto
        have hne : s ≠ s' := by
          intro heq
          apply ha_not_in_s'
          have heq2 : s.val = s'_val := Subtype.ext_iff.mp heq
          rw [← heq2]
          exact ha_s
        have hinter_ss' : (s.val ∩ s'_val).card = k - 1 := by
          have hex : s.val ∩ s'_val = s.val \ {a} := by
            ext x
            simp [s'_val, Finset.mem_sdiff, Finset.mem_singleton]
            by_cases hx : x = a
            · subst hx; simp [hab]
            · simp [hx]; exact fun _ => Or.inr ‹_›
          have hcard_sa : (s.val ∩ {a}).card = 1 := by
            rw [Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr ha_s)]
            exact Finset.card_singleton a
          rw [hex, Finset.card_sdiff]
          rw
            [show ({a} ∩ s.val).card = (s.val ∩ {a}).card by rw [Finset.inter_comm],
              hcard_sa, s.property]
        have hadj : G.Adj s s' := by
          rw [adj_char]
          exact ⟨hne, hinter_ss'⟩
        have hinter_s't : (s'_val ∩ t.val).card = (s.val ∩ t.val).card + 1 := by
          have hex : s'_val ∩ t.val = (s.val ∩ t.val) ∪ {b} := by
            ext x
            simp [s'_val, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_inter]
            by_cases hx : x = b
            · subst hx; simp [hb_t]
            · simp [hx]
              exact fun hxt _ hxa => ha_t (hxa ▸ hxt)
          rw [hex]
          have hdisj2 : Disjoint (s.val ∩ t.val) {b} := by
            rw [Finset.disjoint_singleton_right]
            intro h; exact hb_s (Finset.mem_of_mem_inter_left h)
          rw [Finset.card_union_of_disjoint hdisj2, Finset.card_singleton]
        have hid : k - (s'_val ∩ t.val).card = d := by
          rw [hinter_s't, hcard_inter]
          omega
        have hedist_s't : G.edist s' t ≤ ↑d := ih s' t hid
        have hedist_ss' : G.edist s s' ≤ 1 := by
          let hwalk : G.Walk s s' := SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.nil : G.Walk s'
            s')
          have h1 : G.edist s s' ≤ ↑hwalk.length := SimpleGraph.Walk.edist_le hwalk
          simp [hwalk] at h1
          exact h1
        have htri : G.edist s t ≤ G.edist s s' + G.edist s' t :=
          @SimpleGraph.edist_triangle _ G _ _ _
        calc G.edist s t
            ≤ G.edist s s' + G.edist s' t := htri
          _ ≤ (1 : ℕ∞) + ↑d := add_le_add hedist_ss' hedist_s't
          _ = ↑(d + 1) := by push_cast; ring
    intro s t
    exact key _ _ _ rfl
  -- Step 2: Lower bound on edist via potential
  -- Goal: (k : ℕ∞) - ↑|s∩t|.card ≤ edist s t
  have inter_le_k_sub_edist : ∀ s t : (CGraph.johnson n k).V, (k : ℕ∞) - ↑(s.val ∩ t.val).card ≤
    G.edist s t := by
    intro s t
    -- Potential φ(u) = |u \ t|.card. For adjacent u,v, φ(u) ≤ φ(v) + 1.
    -- Hence for any walk of length L from s to t: φ(s) ≤ L.
    -- So φ(s) ≤ edist s t = sInf of walk lengths.
    set phi : (CGraph.johnson n k).V → ℕ := fun u => (u.val \ t.val).card
    have card_uv : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (u.val \ v.val).card = 1 := by
      intro u v huv
      have huv' := adj_char u v |>.mp huv
      have h1 : (u.val ∩ v.val).card = k - 1 := huv'.2
      by_cases hk0 : k = 0
      · exfalso; apply huv'.1
        have hu : u.val = ∅ := by
          have := Finset.card_eq_zero.mp (by rw [u.property, hk0])
          exact this
        have hv : v.val = ∅ := by
          have := Finset.card_eq_zero.mp (by rw [v.property, hk0])
          exact this
        exact Subtype.ext (by simp [‹u.val = ∅›, ‹v.val = ∅›])
      · have h2 : (u.val \ v.val).card = k - (k - 1) := by
          rw [Finset.card_sdiff, u.property, ← h1, Finset.inter_comm]
        omega
    have card_vu : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (v.val \ u.val).card = 1 := by
      intro u v huv
      have huv2 : G.Adj v u := by
        rw [adj_char] at huv ⊢
        exact ⟨huv.1.symm, by rw [Finset.inter_comm]; exact huv.2⟩
      exact card_uv v u huv2
    have phi_adj : ∀ u v : (CGraph.johnson n k).V, G.Adj u v → (phi u : ℕ∞) ≤ (phi v : ℕ∞) + 1 := by
      intro u v huv
      -- |u\t| = |(u\v) \ t| + |(u∩v)\t|  (disjoint union)
      -- |v\t| = |(v\u) \ t| + |(v∩u)\t| = |(v\u) \ t| + |(u∩v)\t|
      -- So |u\t| ≤ |(u\v)\t| + |(u∩v)\t| ≤ 1 + |(u∩v)\t| ≤ |v\t| + 1
      have hle : (u.val \ t.val).card ≤ (v.val \ t.val).card + 1 := by
        have hunion : (u.val \ t.val) ⊆ (v.val \ t.val) ∪ (u.val \ v.val) := by
          intro x hx
          simp [Finset.mem_sdiff] at hx ⊢
          by_cases hxv : x ∈ v.val
          · exact Or.inl ⟨hxv, hx.2⟩
          · exact Or.inr ⟨hx.1, hxv⟩
        have hcard_union : (u.val \ t.val).card ≤ (v.val \ t.val).card + (u.val \ v.val).card := by
          exact Finset.card_le_card hunion |> (fun h => le_trans h (Finset.card_union_le _ _))
        linarith [card_uv u v huv]
      exact mod_cast hle
    -- Generalize over target
    have phi_walk_le_gen : ∀ (u v : (CGraph.johnson n k).V) (p : G.Walk u v), (phi u : ℕ∞) ≤ (phi v
      : ℕ∞) + ↑p.length := by
      intro u v p
      induction p with
      | nil => simp [phi]
      | cons h p' ih =>
        rename_i u1 u2 u3
        have step := phi_adj u1 u2 h
        have hlen : (SimpleGraph.Walk.cons h p').length = p'.length + 1 := by
          rfl
        rw [hlen]
        have hphi32 : (phi u2 : ℕ∞) ≤ (phi u3 : ℕ∞) + ↑p'.length := by
          rw [← ENat.coe_add]; exact_mod_cast ih
        have heq : (↑(p'.length + 1) : ℕ∞) = ↑p'.length + 1 := by
          rw [ENat.coe_add, ENat.coe_one]
        rw [heq]
        calc (phi u1 : ℕ∞) ≤ (phi u2 : ℕ∞) + 1 := step
          _ ≤ ((phi u3 : ℕ∞) + ↑p'.length) + 1 := by
            have h2 := add_le_add_left hphi32 1
            rw [add_comm] at h2 ⊢; exact h2
          _ = (phi u3 : ℕ∞) + (↑p'.length + 1) := by rw [add_assoc]
    have phi_walk_le : ∀ (u : (CGraph.johnson n k).V) (p : G.Walk u t), (phi u : ℕ∞) ≤ ↑p.length :=
      by
      intro u p
      have := phi_walk_le_gen u t p
      simp [phi] at this
      exact_mod_cast this
    have hphi_s : phi s = k - (s.val ∩ t.val).card := by
      simp only [phi]
      rw [Finset.card_sdiff, s.property, Finset.inter_comm]
    have hc_le_k : (s.val ∩ t.val).card ≤ k :=
        le_trans (Finset.card_le_card Finset.inter_subset_left) s.property.le
    have hcast : ((k - (s.val ∩ t.val).card : ℕ) : ℕ∞) = (k : ℕ∞) - ↑(s.val ∩ t.val).card := by
      set c := (s.val ∩ t.val).card
      have hsum : (k : ℕ∞) = ↑(k - c) + ↑c := by
        calc (k : ℕ∞) = ↑((k - c) + c) := by rw [Nat.sub_add_cancel hc_le_k]
        _ = ↑(k - c) + ↑c := ENat.coe_add _ _
      rw [hsum]
      have key : ∀ (a b : ℕ), ((a : ℕ∞) + (b : ℕ∞)) - (b : ℕ∞) = (a : ℕ∞) := by
        intro a b
        -- In ℕ∞ = WithTop ℕ, coe commutes with + and - (truncated)
        have h1 : ((a : ℕ∞) + (b : ℕ∞) : ℕ∞) = (↑(a + b) : ℕ∞) := by
          rw [← ENat.coe_add]
        have coe_tsub : ∀ (x y : ℕ), y ≤ x → ((x : ℕ∞) - (y : ℕ∞) : ℕ∞) = (↑(x - y) : ℕ∞) := by
          intro x y hxy
          rfl
        have h2 : ((a : ℕ∞) + (b : ℕ∞) - (b : ℕ∞) : ℕ∞) = (a : ℕ∞) := by
          rw [← ENat.coe_add, coe_tsub (a + b) b (by omega), Nat.add_sub_cancel_right]
        exact h2
      exact (key _ _).symm
    rw [← hcast, ← hphi_s]
    rw [SimpleGraph.edist_eq_sInf]
    apply le_sInf
    rintro _ ⟨w, rfl⟩
    exact phi_walk_le _ w
  -- Step 3: edist(s,t) = k - |s∩t|.card (in ℕ∞)
  have edist_eq : ∀ s t : (CGraph.johnson n k).V, G.edist s t = (k : ℕ∞) - ↑(s.val ∩ t.val).card :=
    by
    intro s t
    exact le_antisymm (edist_le_k_inter s t) (inter_le_k_sub_edist s t)
  -- Step 4: ediam = max_{s,t} (k - |s∩t|.card)
  -- Helper: rewrite ℕ∞ subtraction
  have hsub_nk : (n : ℕ∞) - ↑k = ↑(n - k) := by rw [ENat.coe_sub]
  -- Upper bound on edist
  have upper : ∀ s t : (CGraph.johnson n k).V, G.edist s t ≤ (min (↑k) (↑(n - k) : ℕ∞)) := by
    intro s t
    rw [edist_eq s t]
    apply le_min
    · rw [← ENat.coe_sub]
      exact Nat.cast_le.mpr (Nat.sub_le _ _)
    · have hunion : (s.val ∪ t.val).card + (s.val ∩ t.val).card = 2 * k := by
        rw [Finset.card_union_add_card_inter, s.property, t.property]; ring
      have hunion_le_n : (s.val ∪ t.val).card ≤ n := by
        exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
      have hcard_ge : (s.val ∩ t.val).card ≥ 2 * k - n := by omega
      have hle : k - (s.val ∩ t.val).card ≤ n - k := by omega
      rw [ENat.coe_sub]
      exact Nat.cast_le.mpr hle
  -- Lower bound: exhibit s,t with edist = min (↑k) (↑(n-k))
  have edist_le_ediam_aux : min (↑k) (↑(n - k) : ℕ∞) ≤ G.ediam := by
    by_cases hk2 : 2 * k ≤ n
    · -- Disjoint s, t: edist = k = min
      let s_val : Finset (Fin n) := Finset.image (fun i : Fin k => Fin.castLE hk i) (Finset.univ :
        Finset (Fin k))
      let t_val : Finset (Fin n) := Finset.image (fun i : Fin k => ⟨(i : ℕ) + k, by omega⟩ : Fin k →
        Fin n) (Finset.univ : Finset (Fin k))
      have hs_card : s_val.card = k := by
        rw [Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
        simp
      have ht_card : t_val.card = k := by
        rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext
          (by simp [Fin.ext_iff] at h; omega))]
        simp
      let s : (CGraph.johnson n k).V := ⟨s_val, hs_card⟩
      let t : (CGraph.johnson n k).V := ⟨t_val, ht_card⟩
      have hint_empty : s_val ∩ t_val = ∅ := by
        have : ∀ x, x ∉ s_val ∩ t_val := by
          intro x hx
          simp [s_val, t_val, Finset.mem_inter, Finset.mem_image] at hx
          obtain ⟨i, hi⟩ := hx.1
          obtain ⟨j, hj⟩ := hx.2
          simp [Fin.ext_iff] at hi hj
          omega
        exact Finset.not_nonempty_iff_eq_empty.mp (by intro h; obtain ⟨x, hx⟩ := h; exact this x hx)
      have hedist : G.edist s t = (k : ℕ∞) := by
        rw [edist_eq s t, hint_empty, Finset.card_empty, Nat.cast_zero]
        simp
      have hmin : min (↑k) (↑(n - k) : ℕ∞) = (k : ℕ∞) := by
        rw [min_eq_left]
        exact_mod_cast Nat.le_sub_of_add_le (by omega)
      rw [hmin]
      exact hedist.symm ▸ SimpleGraph.edist_le_ediam
    · -- 2k > n: min = n-k
      have h2kn : n < 2 * k := lt_of_not_ge hk2
      have hnk_lt_k : n - k < k := by omega
      let s_val : Finset (Fin n) := Finset.image (fun i : Fin k => Fin.castLE hk i) (Finset.univ :
        Finset (Fin k))
      let t_val : Finset (Fin n) := Finset.image (fun i : Fin k => ⟨(i : ℕ) + (n - k), by omega⟩ :
        Fin k → Fin n) (Finset.univ : Finset (Fin k))
      have hs_card : s_val.card = k := by
        rw [Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
        simp
      have ht_card : t_val.card = k := by
        rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext
          (by simp [Fin.ext_iff] at h; omega))]
        simp
      let s : (CGraph.johnson n k).V := ⟨s_val, hs_card⟩
      let t : (CGraph.johnson n k).V := ⟨t_val, ht_card⟩
      have hint_card : (s_val ∩ t_val).card = 2 * k - n := by
        -- s_val = image of Fin.castLE hk over Fin k, i.e. {0,...,k-1} in Fin n
        -- t_val = image of shift by (n-k), i.e. {n-k,...,n-1} in Fin n
        -- Their intersection = elements of Fin n with value in [n-k, k), size = 2k-n
        -- This set is in bijection with Fin (2*k-n) via i ↦ ⟨n-k + i, by omega⟩
        have hinj : Function.Injective (fun (i : Fin (2 * k - n)) =>
          ⟨(n - k) + i.val, by omega⟩ : Fin (2 * k - n) → Fin n) := by
          intro i j h
          simp [Fin.ext_iff] at h ⊢; exact h
        -- Key lemma: x ∈ s_val ↔ x.val < k, and x ∈ t_val ↔ n-k ≤ x.val
        have hs_mem : ∀ x : Fin n, x ∈ s_val ↔ x.val < k := by
          intro x
          simp only [s_val, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi⟩
            have : x.val = i.val := by
              have := congr_arg Fin.val hi; simp [Fin.castLE] at this; exact this.symm
            rw [this]; exact i.is_lt
          · intro hx
            exact ⟨⟨x.val, hx⟩, Fin.ext (by simp)⟩
        have ht_mem : ∀ x : Fin n, x ∈ t_val ↔ n - k ≤ x.val := by
          intro x
          simp only [t_val, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj⟩
            have hval : x.val = j.val + (n - k) := by
              have := congr_arg Fin.val hj; simp at this ⊢; exact
                this.symm
            rw [hval]; exact Nat.le_add_left _ _
          · intro hx
            exact ⟨⟨x.val - (n - k), by omega⟩, Fin.ext (by simp [Nat.sub_add_cancel hx])⟩
        -- Now: s_val ∩ t_val = {x : Fin n | n-k ≤ x.val ∧ x.val < k}
        -- This equals the image of Fin (2k-n) under i ↦ ⟨n-k + i, by omega⟩
        have hint_eq : s_val ∩ t_val = Finset.image (fun (i : Fin (2 * k - n)) =>
          ⟨(n - k) + i.val, by omega⟩ : Fin (2 * k - n) → Fin n) Finset.univ := by
          ext x
          simp [Finset.mem_inter, hs_mem, ht_mem, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · intro h
            have h1 : n - k ≤ x.val := by omega
            exact ⟨⟨x.val - (n - k), by omega⟩, Fin.ext (by simp [Nat.add_sub_of_le h1])⟩
          · rintro ⟨i, hi⟩
            subst hi
            have : (⟨n - k + i.val, by omega⟩ : Fin n).val = n - k + i.val := by simp
            rw [this]
            exact ⟨by omega, by omega⟩
        rw [hint_eq, Finset.card_image_of_injective _ hinj, Finset.card_univ]
        simp
      have hedist : G.edist s t = (↑(n - k) : ℕ∞) := by
        rw [edist_eq s t, hint_card]
        show (↑k : ℕ∞) - ↑(2 * k - n) = ↑(n - k)
        haveI : 2 * k - n ≤ k := by omega
        rw [← ENat.coe_sub k (2 * k - n)]
        congr 1; omega
      have hmin : min (↑k) (↑(n - k) : ℕ∞) = (↑(n - k) : ℕ∞) := by
        rw [min_eq_right]
        exact_mod_cast Nat.sub_le_of_le_add (by omega)
      rw [hmin]
      exact hedist.symm ▸ SimpleGraph.edist_le_ediam
  have ediam_eq_nn : G.ediam = min (↑k) (↑(n - k) : ℕ∞) :=
    le_antisymm (SimpleGraph.ediam_le_of_edist_le upper) edist_le_ediam_aux
  -- Step 5: conclude
  rw [ediam_eq_nn]
  have hmin_coe : min (↑k) (↑(n - k) : ℕ∞) = ↑(min k (n - k)) := by
    by_cases h : k ≤ n - k
    · rw [min_eq_left (mod_cast h), min_eq_left (mod_cast h)]
    · rw [min_eq_right (mod_cast le_of_not_ge h), min_eq_right (mod_cast le_of_not_ge h)]
  rw [hmin_coe, ENat.toNat_coe]

/-- Johnson graphs are connected: swap the elements of two `k`-sets one at a time. -/
theorem isConnected_johnson {n k : ℕ} (hk : k ≤ n) : IsConnected (johnson n k) := by
  change IsConnected ⟦CGraph.johnson n k⟧
  rw [IsoGraph.isConnected_mk]
  -- Goal: (johnson n k).IsConnected, i.e., (johnson n k).toSimple.Connected
  unfold CGraph.IsConnected
  have hne : Nonempty (CGraph.johnson n k).V := by
    by_cases hkn : k = n
    · subst hkn
      exact ⟨⟨Finset.univ, by simp⟩⟩
    · exact ⟨⟨Finset.Iio ⟨k, lt_of_le_of_ne hk hkn⟩, by simp⟩⟩
  apply SimpleGraph.Connected.mk
  · -- Preconnected: any two vertices reachable
    let johnsonC : CGraph := CGraph.johnson n k
    have reachability : ∀ d : ℕ, ∀ (s t : Finset (Fin n)) (hs : s.card = k) (ht : t.card = k),
        (s \ t).card = d → johnsonC.toSimple.Reachable ⟨s, hs⟩ ⟨t, ht⟩ := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro s t hs ht hdval
        by_cases hst : s = t
        · exact hst ▸ SimpleGraph.Reachable.refl _
        · -- s ≠ t, so (s \ t) is nonempty
          have hd_pos : 0 < (s \ t).card := by
            by_contra h
            have h0 : (s \ t).card = 0 := by omega
            have hsub : s ⊆ t := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h0)
            exact hst (Finset.eq_of_subset_of_card_le hsub (by simp [hs, ht]))
          -- Pick a ∈ s \ t
          obtain ⟨a, has, hat⟩ : ∃ a ∈ s, a ∉ t := by
            obtain ⟨x, hx⟩ := Finset.card_pos.mp hd_pos
            exact ⟨x, Finset.mem_sdiff.mp hx |>.1, Finset.mem_sdiff.mp hx |>.2⟩
          -- Pick b ∈ t \ s
          have hne2 : (t \ s).Nonempty := by
            by_contra h
            have hempty : t \ s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
            have hsub2 : t ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp hempty
            have := Finset.eq_of_subset_of_card_le hsub2 (by simp [ht, hs])
            exact hst this.symm
          obtain ⟨b, hbt, hbs⟩ : ∃ b ∈ t, b ∉ s := by
            obtain ⟨x, hx⟩ := hne2
            exact ⟨x, Finset.mem_sdiff.mp hx |>.1, Finset.mem_sdiff.mp hx |>.2⟩
          -- Construct s'val = insert b (erase s a)
          let s'val : Finset (Fin n) := s.erase a ∪ {b}
          have hb_not_in_erase : b ∉ s.erase a := by intro h; exact hbs (Finset.mem_of_mem_erase h)
          have hs'card : s'val.card = k := by
            have hdisj : Disjoint (s.erase a) {b} := by
              rw [Finset.disjoint_singleton_right]
              exact hb_not_in_erase
            have := Finset.card_union_of_disjoint hdisj
            rw [this, Finset.card_erase_of_mem has, Finset.card_singleton, hs]
            have : 0 < k := hs ▸ Finset.card_pos.mpr ⟨a, has⟩
            omega
          let s' : johnsonC.V := ⟨s'val, hs'card⟩
          have hab : a ≠ b := by intro h; exact hbs (h.symm ▸ has)
          -- Show s' ≠ s (for adjacency)
          have hs'_ne_s : (⟨s, hs⟩ : johnsonC.V) ≠ s' := by
            intro h
            have hval : s = s'val := Subtype.ext_iff.mp h
            have : b ∈ s := by
              rw [hval]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            exact hbs this
          -- Show |s'val ∩ s| = k - 1
          have hinter : (s'val ∩ s).card = k - 1 := by
            have hessa : s'val ∩ s = s.erase a := by
              ext x
              simp [s'val]
              by_cases hx : x = a <;> by_cases hx2 : x = b <;> simp [hx, hx2, hab]
              tauto
            rw [hessa, Finset.card_erase_of_mem has, hs]
          -- Show s' is adjacent to s
          have hadj_adj : johnsonC.Adj ⟨s, hs⟩ s' := by
            show johnsonC.Adj ⟨s, hs⟩ s'
            simp only [johnsonC, CGraph.johnson_adj]
            have hne' : (⟨s, hs⟩ : johnsonC.V) ≠ s' := hs'_ne_s
            have hcard' : (s ∩ s'.val).card = k - 1 := by rw [Finset.inter_comm]; exact hinter
            simp [hne', hcard']
          -- Show (s'val \ t).card < d
          have hcard_lt : (s'val \ t).card < d := by
            have hsub : s'val \ t ⊆ (s \ t) \ {a} := by
              intro x hx
              simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx ⊢
              have hx1 : x ∈ s := by
                dsimp [s'val] at hx
                rcases Finset.mem_union.mp hx.1 with hx1 | hx1
                · exact Finset.mem_of_mem_erase hx1
                · have hxb : x = b := Finset.mem_singleton.mp hx1
                  exact False.elim ((hxb ▸ hx.2) hbt)
              have hxa : x ≠ a := by
                by_contra hx_eq_a
                rw [hx_eq_a] at hx
                have : a ∈ s'val := hx.1
                simp [s'val, Finset.mem_erase] at this
                exact hab this
              exact ⟨⟨hx1, hx.2⟩, hxa⟩
            have hcard_erase : ((s \ t) \ {a}).card = (s \ t).card - 1 := by
              have ha_mem : a ∈ s \ t := Finset.mem_sdiff.mpr ⟨has, hat⟩
              rw [show (s \ t) \ {a} = (s \ t).erase a from by
                ext x; simp [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
                tauto]
              exact Finset.card_erase_of_mem ha_mem
            have : (s'val \ t).card ≤ (s \ t).card - 1 := by
              exact le_trans (Finset.card_le_card hsub) hcard_erase.le
            omega
          -- Use IH for s', t
          have hired : johnsonC.toSimple.Reachable s' ⟨t, ht⟩ :=
            ih _ hcard_lt _ _ hs'card ht rfl
          -- Compose: s → s' → t
          have hreach_edge : johnsonC.toSimple.Reachable ⟨s, hs⟩ s' :=
            (SimpleGraph.Adj.reachable
              (show johnsonC.toSimple.Adj _ _ from by
                simpa [johnsonC, CGraph.toSimple_adj] using hadj_adj))
          exact hreach_edge.trans hired
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact reachability _ _ _ hu hv rfl

/-- The `2 × n` grid has four corners of degree two and `2n - 4` interior vertices of degree
three. -/
theorem degSequence_ladder (n : ℕ) :
    degSequence (ladder (n + 2)) = List.replicate 4 2 ++ List.replicate (2 * n) 3 := by
  unfold ladder
  rw [degSequence_eq_sort]
  rw [degMultiset_cartesianProduct, degMultiset_path, degMultiset_complete]
  simp only [Multiset.bind, Multiset.map_replicate]
  simp (config := { decide := true }) only [show (2 : ℕ) - 1 = 1 from rfl]
  -- Compute map over cons/replicate
  have h1 : Multiset.map (fun x => Multiset.replicate 2 (x + 1)) (1 ::ₘ 1 ::ₘ Multiset.replicate n
    2) =
    Multiset.replicate 2 2 ::ₘ Multiset.replicate 2 2 ::ₘ Multiset.replicate n (Multiset.replicate 2
      3) := by
    simp [Multiset.map_cons, Multiset.map_replicate]
  rw [h1]
  -- Compute join
  simp only [Multiset.join]
  simp (config := { decide := true }) [
    Multiset.sum_replicate]
  -- Step: n • replicate 2 3 = replicate (2 * n) 3
  have hrep : ∀ (m : ℕ) (a : ℕ), m • Multiset.replicate 2 a = Multiset.replicate (2 * m) a := by
    intro m a
    induction m with
    | zero => simp
    | succ p ih =>
      have : 2 * (p + 1) = 2 * p + 2 := by omega
      rw [this]
      rw [succ_nsmul, ih, Multiset.replicate_add]
  -- Now handle the main sort goal
  have h3 : (3 ::ₘ ({3} : Multiset ℕ)) = Multiset.replicate 2 3 := by rfl
  rw [h3, hrep]
  apply List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (Multiset.pairwise_sort _ (fun x1 x2 => x1 ≤ x2))
    (by simp [List.pairwise_cons, List.pairwise_replicate, List.mem_replicate])
    (by
      have hms : ∀ (m : Multiset ℕ), Multiset.ofList (Multiset.sort m (· ≤ ·)) = m := by
        intro m; exact Multiset.sort_eq _ _
      have htarget : (2 ::ₘ 2 ::ₘ 2 ::ₘ 2 ::ₘ Multiset.replicate (2 * n) 3 : Multiset ℕ) =
          ((2 :: 2 :: 2 :: 2 :: List.replicate (2 * n) 3) : Multiset ℕ) := by rfl
      exact Multiset.coe_eq_coe.mp (hms _ ▸ htarget))

/-! ### Consequences of the Johnson graph's connectivity and diameter -/

@[simp] theorem numComponents_johnson {n k : ℕ} (hk : k ≤ n) : (johnson n k).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_johnson hk)

@[simp] theorem isConnected_compl_kneser_two (n : ℕ) : IsConnected (kneser (n + 2) 2)ᶜ := by
  rw [← triangular_eq_compl_kneser]
  exact isConnected_johnson (by omega)

/-- The Johnson graph `J(n, 1)` is the complete graph `Kₙ`, so its diameter is one. -/
example (n : ℕ) : (johnson (n + 2) 1).diameter = 1 := by
  rw [diameter_johnson (by omega)]
  omega

/-! ### The `2 × n` grid, from its degree sequence -/

theorem two_mul_E_ladder (n : ℕ) : 2 * (ladder (n + 2)).E = 8 + 6 * n := by
  have h := sum_degSequence (ladder (n + 2))
  rw [degSequence_ladder, List.sum_append, List.sum_replicate, List.sum_replicate,
    smul_eq_mul, smul_eq_mul] at h
  omega

/-- The radius of a strong product is the maximum of the radii. -/
theorem radius_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ⊠g H).radius = max G.radius H.radius := by
  induction G using Quotient.inductionOn with | _ G
  induction H using Quotient.inductionOn with | _ H
  rw [strongProduct_mk, radius_mk, radius_mk, radius_mk]
  simp [isConnected_mk] at hG hH
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  haveI : Nonempty (G.strongProduct H).V := ⟨(Classical.arbitrary G.V, Classical.arbitrary H.V)⟩
  set Gs := G.toSimple
  set Hs := H.toSimple
  set SPs := (G.strongProduct H).toSimple
  have hSP_adj : ∀ p q : G.V × H.V, SPs.Adj p q ↔ p ≠ q ∧ ((p.1 = q.1 ∨ Gs.Adj p.1 q.1) ∧ (p.2 = q.2
    ∨ Hs.Adj p.2 q.2)) := by
    simp [SPs, CGraph.toSimple, CGraph.strongProduct, Gs, Hs]
  -- For any SP-walk from u to v, there's a G-walk from u.1 to v.1 of ≤ length.
  have projectWalk_G_len : ∀ {u v : G.V × H.V} (W : SPs.Walk u v),
      Gs.edist u.1 v.1 ≤ ↑W.length := by
    intro u v W
    induction W with
    | nil =>
      simp
    | @cons a b c hpq rest ih =>
      rw [SimpleGraph.Walk.length_cons]
      rcases (hSP_adj a b).mp hpq |>.2.1 with heq | hadj
      · -- G coord same: a.1 = b.1, so edist a.1 c.1 = edist b.1 c.1 ≤ rest.length ≤ rest.length + 1
        rw [heq]
        exact le_trans ih (by exact_mod_cast Nat.cast_le.mpr (Nat.le_add_right _ _))
      · -- G coord adjacent: prepend edge a.1-b.1
        have : Gs.edist a.1 b.1 ≤ 1 := by
          exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj
            SimpleGraph.Walk.nil)) (by simp)
        calc Gs.edist a.1 c.1 ≤ Gs.edist a.1 b.1 + Gs.edist b.1 c.1 := SimpleGraph.edist_triangle
          _ ≤ 1 + ↑rest.length := add_le_add this ih
          _ = ↑(rest.length + 1) := by push_cast; ring
  have hedist_ge_G : ∀ h0 : H.V, ∀ g1 g2 : G.V, Gs.edist g1 g2 ≤ SPs.edist (g1, h0) (g2, h0) := by
    intro h0 g1 g2
    have key : ∀ (q : SPs.Walk (g1, h0) (g2, h0)), Gs.edist g1 g2 ≤ ↑q.length := by
      intro q
      exact projectWalk_G_len q
    by_cases hne : Nonempty (SPs.Walk (g1, h0) (g2, h0))
    · exact le_iInf (fun q => key q)
    · push_neg at hne
      have : SPs.edist (g1, h0) (g2, h0) = ⊤ := by
        rw [SimpleGraph.edist_eq_top_of_not_reachable]
        exact fun hr => hne.elim hr.some
      exact this.symm ▸ le_top
  -- H lower bound (symmetric to G)
  have projectWalk_H_len : ∀ {u v : G.V × H.V} (W : SPs.Walk u v), Hs.edist u.2 v.2 ≤ ↑W.length :=
    by
    intro u v W
    induction W with
    | nil => simp
    | @cons a b c hpq rest ih =>
      rw [SimpleGraph.Walk.length_cons]
      rcases (hSP_adj a b).mp hpq |>.2.2 with heq | hadj
      · rw [heq]
        exact le_trans ih (by exact_mod_cast Nat.cast_le.mpr (Nat.le_add_right _ _))
      · calc Hs.edist a.2 c.2 ≤ Hs.edist a.2 b.2 + Hs.edist b.2 c.2 := SimpleGraph.edist_triangle
          _ ≤ 1 + ↑rest.length := add_le_add (by
              exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj
                SimpleGraph.Walk.nil)) (by simp)) ih
          _ = ↑(rest.length + 1) := by push_cast; ring
  have hedist_ge_H : ∀ g0 : G.V, ∀ h1 h2 : H.V, Hs.edist h1 h2 ≤ SPs.edist (g0, h1) (g0, h2) := by
    intro g0 h1 h2
    have key : ∀ (q : SPs.Walk (g0, h1) (g0, h2)), Hs.edist h1 h2 ≤ ↑q.length := by
      intro q; exact projectWalk_H_len q
    by_cases hne : Nonempty (SPs.Walk (g0, h1) (g0, h2))
    · exact le_iInf (fun q => key q)
    · push_neg at hne
      have : SPs.edist (g0, h1) (g0, h2) = ⊤ := by
        rw [SimpleGraph.edist_eq_top_of_not_reachable]
        exact fun hr => hne.elim hr.some
      exact this.symm ▸ le_top
  -- Graph hom G →g SPs fixing H-coordinate
  let toSP_G (h0 : H.V) : Gs →g SPs := {
    toFun := fun g => (g, h0)
    map_rel' := @fun (a b : G.V) hab =>
      hSP_adj (a, h0) (b, h0) |>.mpr ⟨ne_of_apply_ne Prod.fst hab.ne, Or.inr hab, Or.inl rfl⟩
  }
  -- Graph hom H →g SPs fixing G-coordinate
  let toSP_H (g0 : G.V) : Hs →g SPs := {
    toFun := fun h => (g0, h)
    map_rel' := @fun (a b : H.V) hab =>
      hSP_adj (g0, a) (g0, b) |>.mpr ⟨ne_of_apply_ne Prod.snd hab.ne, Or.inl rfl, Or.inr hab⟩
  }
  -- SP walk of length ≤ max WG.length WH.length
  have spWalk_max : ∀ (n : ℕ) {g1 g2 : G.V} {h1 h2 : H.V}
      (WG : Gs.Walk g1 g2) (WH : Hs.Walk h1 h2),
      WG.length + WH.length ≤ n →
      ∃ (W : SPs.Walk (g1, h1) (g2, h2)), W.length ≤ max WG.length WH.length := by
    intro n
    induction n with
    | zero =>
      intro g1 g2 h1 h2 WG WH hle
      have hWG : WG.length = 0 := by omega
      have hWH : WH.length = 0 := by omega
      have hg1g2 : g1 = g2 := by
        have := WG.getVert_zero; have := WG.getVert_length; simp [hWG] at *; exact this
      have hh1h2 : h1 = h2 := by
        have := WH.getVert_zero; have := WH.getVert_length; simp [hWH] at *; exact this
      subst hg1g2; subst hh1h2
      exact ⟨.nil, by simp⟩
    | succ m ih =>
      intro g1 g2 h1 h2 WG WH hle
      by_cases hg : WG.length = 0
      · have hg1g2 : g1 = g2 := by
          have := WG.getVert_zero; have := WG.getVert_length; simp [hg] at *; exact this
        subst hg1g2
        exact ⟨WH.map (toSP_H g1), by simp [hg]⟩
      · by_cases hh : WH.length = 0
        · have hh1h2 : h1 = h2 := by
            have := WH.getVert_zero; have := WH.getVert_length; simp [hh] at *; exact this
          subst hh1h2
          exact ⟨WG.map (toSP_G h1), by simp [hh]⟩
        · cases WG with
          | nil => contradiction
          | cons hab WGtail =>
            cases WH with
            | nil => contradiction
            | cons hcd WHtail =>
              obtain ⟨W', hW'⟩ := ih WGtail WHtail
                (by simp [SimpleGraph.Walk.length_cons] at hle ⊢; omega)
              exact
                ⟨SimpleGraph.Walk.cons (hSP_adj _ _ |>.mpr
                    ⟨by rintro ⟨rfl, rfl⟩; exact hab.ne rfl, Or.inr hab, Or.inr hcd⟩) W', by
                  simp [SimpleGraph.Walk.length_cons] at hW' ⊢
                  omega⟩
  -- Upper bound: SP edist ≤ max of coordinate edists
  have hedist_le_max : ∀ g1 g2 : G.V, ∀ h1 h2 : H.V,
      SPs.edist (g1, h1) (g2, h2) ≤ max (Gs.edist g1 g2) (Hs.edist h1 h2) := by
    intro g1 g2 h1 h2
    by_cases hg : Gs.edist g1 g2 = ⊤
    · simp [hg]
    by_cases hh : Hs.edist h1 h2 = ⊤
    · simp [hh]
    obtain ⟨WG, hWG⟩ := SimpleGraph.exists_walk_of_edist_ne_top hg
    obtain ⟨WH, hWH⟩ := SimpleGraph.exists_walk_of_edist_ne_top hh
    obtain ⟨W, hW⟩ := spWalk_max (WG.length + WH.length) WG WH (le_refl _)
    calc SPs.edist (g1, h1) (g2, h2) ≤ ↑W.length := SimpleGraph.Walk.edist_le W
      _ ≤ ↑(max WG.length WH.length) := WithTop.coe_mono hW
      _ = max (WG.length : ℕ∞) (WH.length : ℕ∞) := by
          show (max WG.length WH.length : ℕ∞) = max (WG.length : ℕ∞) (WH.length : ℕ∞)
          cases le_total WG.length WH.length with
          | inl h => simp
          | inr h => simp
      _ ≤ max (Gs.edist g1 g2) (Hs.edist h1 h2) :=
          max_le_max (hWG.le) (hWH.le)
  -- Eccentricity: SP eccent (g,h) = max(G eccent g, H eccent h)
  have heccent_eq : ∀ g : G.V, ∀ h : H.V,
      SPs.eccent (g, h) = max (Gs.eccent g) (Hs.eccent h) := by
    intro g h
    apply le_antisymm
    · -- Upper bound: SP eccent ≤ max
      simp only [SimpleGraph.eccent]
      refine ciSup_le fun p => le_trans (hedist_le_max g p.1 h p.2) ?_
      apply max_le
      · exact le_trans SimpleGraph.edist_le_eccent (le_max_left _ _)
      · exact le_trans SimpleGraph.edist_le_eccent (le_max_right _ _)
    · -- Lower bound: max ≤ SP eccent
      apply max_le
      · -- Gs.eccent g ≤ SPs.eccent (g, h)
        simp only [SimpleGraph.eccent]
        have hbdd : BddAbove (Set.range (fun q : G.V × H.V => SPs.edist (g, h) q)) := by
          refine ⟨max (Gs.eccent g) (Hs.eccent h), ?_⟩
          intro x hx
          obtain ⟨q, hq⟩ := hx
          dsimp at hq
          rw [← hq]
          exact le_trans (hedist_le_max g q.1 h q.2) (max_le (le_trans SimpleGraph.edist_le_eccent
            (le_max_left _ _)) (le_trans SimpleGraph.edist_le_eccent (le_max_right _ _)))
        apply ciSup_le fun g' => le_trans (hedist_ge_G h g g')
          (le_ciSup hbdd (g', h))
      · -- Hs.eccent h ≤ SPs.eccent (g, h)
        simp only [SimpleGraph.eccent]
        have hbdd : BddAbove (Set.range (fun q : G.V × H.V => SPs.edist (g, h) q)) := by
          refine ⟨max (Gs.eccent g) (Hs.eccent h), ?_⟩
          intro x hx
          obtain ⟨q, hq⟩ := hx
          dsimp at hq
          rw [← hq]
          exact le_trans (hedist_le_max g q.1 h q.2) (max_le (le_trans SimpleGraph.edist_le_eccent
            (le_max_left _ _)) (le_trans SimpleGraph.edist_le_eccent (le_max_right _ _)))
        apply ciSup_le fun h' => le_trans (hedist_ge_H g h h')
          (le_ciSup hbdd (g, h'))
  -- SPs.radius ≤ max Gs.radius Hs.radius
  -- For any g₀ : G.V, SPs.radius ≤ max (Gs.eccent g₀) (Hs.eccent h₀) for any h₀.
  -- So SPs.radius ≤ max (Gs.eccent g₀) Hs.radius (since if SPs.radius > Gs.eccent g₀,
  -- then SPs.radius ≤ Hs.eccent h for all h, so SPs.radius ≤ Hs.radius).
  have h_aux : ∀ g₀ : G.V, SPs.radius ≤ max (Gs.eccent g₀) Hs.radius := by
    intro g₀
    have hle : ∀ h : H.V, SPs.radius ≤ max (Gs.eccent g₀) (Hs.eccent h) := by
      intro h
      exact le_trans SimpleGraph.radius_le_eccent (heccent_eq g₀ h).le
    by_cases hg₀ : SPs.radius ≤ Gs.eccent g₀
    · exact le_max_of_le_left hg₀
    · push_neg at hg₀
      have hleH : ∀ h : H.V, SPs.radius ≤ Hs.eccent h := by
        intro h
        have hle_h := hle h
        rw [le_max_iff] at hle_h
        exact hle_h.resolve_left hg₀.not_ge
      have hleH_radius : SPs.radius ≤ Hs.radius := by
        exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨h, rfl⟩; exact hleH h)
      exact le_max_of_le_right hleH_radius
  -- SPs.radius ≤ max Gs.radius Hs.radius:
  -- For any g₀, SPs.radius ≤ max (Gs.eccent g₀) Hs.radius.
  -- Also SPs.radius ≤ max Gs.radius (Hs.eccent h₀) for any h₀ (symmetric argument).
  -- Pick g₀ arbitrary. If Gs.eccent g₀ < SPs.radius, then SPs.radius ≤ Hs.radius ≤ max ...
  -- If Gs.eccent g₀ ≥ SPs.radius, then SPs.radius ≤ Gs.eccent g₀ ≤ max Gs.radius ... no.
  -- Better: use iInf. SPs.radius ≤ ⨅ g₀, max (Gs.eccent g₀) Hs.radius.
  -- And ⨅ g₀, max (Gs.eccent g₀) Hs.radius = max (⨅ g₀, Gs.eccent g₀) Hs.radius = max Gs.radius
  -- Hs.radius.
  have h_le_max_enat : SPs.radius ≤ max Gs.radius Hs.radius := by
    have h1 : SPs.radius ≤ ⨅ g₀ : G.V, max (Gs.eccent g₀) Hs.radius := by
      apply le_ciInf
      intro g₀; exact h_aux g₀
    have h2 : ⨅ g₀ : G.V, max (Gs.eccent g₀) Hs.radius = max Gs.radius Hs.radius := by
      rw [SimpleGraph.radius]
      apply le_antisymm
      · -- iInf_g max (Gs.eccent g) C ≤ max (iInf Gs.eccent) C
        by_contra hlt
        push_neg at hlt
        -- hlt : max (⨅ g, Gs.eccent g) Hs.radius < ⨅ g, max (Gs.eccent g) Hs.radius
        have hlt_c : Hs.radius < ⨅ g, max (Gs.eccent g) Hs.radius := hlt.trans_le' (le_max_right _
          _)
        -- So for all g, max (Gs.eccent g) Hs.radius ≥ ⨅ ... > Hs.radius, so Gs.eccent g > Hs.radius
        -- ... no.
        -- max(A, C) ≥ D > C implies A ≥ D > C, so A > C.
        have hGs_gt_H : ∀ g : G.V, Hs.radius < Gs.eccent g := by
          intro g
          have hle_g : Hs.radius < max (Gs.eccent g) Hs.radius := hlt_c.trans_le (iInf_le (f := fun
            g' => max (Gs.eccent g') Hs.radius) g)
          rw [lt_max_iff] at hle_g
          exact hle_g.resolve_right (lt_irrefl Hs.radius)
        -- So max (Gs.eccent g) Hs.radius = Gs.eccent g for all g.
        have hmax_eq : ∀ g : G.V, max (Gs.eccent g) Hs.radius = Gs.eccent g := by
          intro g; rw [max_eq_left]; exact le_of_lt (hGs_gt_H g)
        have hGs_radius : Gs.radius = ⨅ g : G.V, Gs.eccent g := by rw [SimpleGraph.radius]
        rw [hGs_radius] at hlt
        have hmax_eq' : ∀ g : G.V, max (Gs.eccent g) (⨅ u : H.V, Hs.eccent u) = Gs.eccent g := by
          intro g
          show max (Gs.eccent g) Hs.radius = Gs.eccent g
          exact hmax_eq g
        simp_rw [hmax_eq'] at hlt
        exact absurd hlt (not_lt_of_ge (le_max_left _ _))
      · -- max (iInf Gs.eccent) C ≤ iInf_g max (Gs.eccent g) C
        apply max_le
        · have hbdd : BddBelow (Set.range (Gs.eccent : G.V → ℕ∞)) :=
            ⟨0, by rintro _ ⟨_, rfl⟩; exact zero_le _⟩
          exact le_ciInf fun a => le_trans (ciInf_le hbdd a) (le_max_left _ _)
        · exact le_ciInf fun _ => le_max_right _ _
    rw [h2] at h1; exact h1
  -- max Gs.radius Hs.radius ≤ SPs.radius
  have h_ge_max_enat : max Gs.radius Hs.radius ≤ SPs.radius := by
    apply max_le
    · -- Gs.radius ≤ SPs.radius
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨p, rfl⟩
      exact le_trans (SimpleGraph.radius_le_eccent) (heccent_eq p.1 p.2 ▸ le_max_left _ _)
    · -- Hs.radius ≤ SPs.radius
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨p, rfl⟩
      exact le_trans (SimpleGraph.radius_le_eccent) (heccent_eq p.1 p.2 ▸ le_max_right _ _)
  have h_radius_eq_enat : SPs.radius = max Gs.radius Hs.radius := by
    exact le_antisymm h_le_max_enat h_ge_max_enat
  simp [CGraph.radius]
  rw [h_radius_eq_enat]
  have key : ∀ (a b : ℕ∞), a ≠ ⊤ → b ≠ ⊤ → (max a b).toNat = max a.toNat b.toNat := by
    intro a b ha hb
    cases le_total a b with
    | inl hab =>
      rw [max_eq_right hab, max_eq_right (ENat.toNat_le_toNat hab hb)]
    | inr hab =>
      rw [max_eq_left hab, max_eq_left (ENat.toNat_le_toNat hab ha)]
  exact key _ _ (SimpleGraph.radius_ne_top_iff.2 hG) (SimpleGraph.radius_ne_top_iff.2 hH)

/-- A wheel has a near-perfect matching. -/
theorem matchNum_wheel (n : ℕ) : (wheel (n + 3)).matchNum = (n + 4) / 2 := by
  apply le_antisymm
  · have h1 := (wheel (n + 3)).two_mul_matchNum_le_V
    rw [V_wheel] at h1
    omega
  · -- Lower bound
    rw [matchNum_eq]
    set G := wheel (n + 3)
    -- We exhibit an independent set of lineGraph G of size (n+4)/2,
    -- corresponding to a matching in G.
    -- Vertices of G = wheel(n+3) = join (complete 1) (cycle (n+3)) live in Fin 1 ⊕ Fin (n+3).
    -- Hub = inl 0, rim vertices = inr i for i : Fin (n+3).
    -- Rim edges: (inr i, inr ((i+1) % (n+3))) for i : Fin (n+3).
    -- Spoke edges: (inl 0, inr i) for i : Fin (n+3).
    -- Construction (parity split on n):
    --   n = 2*k (even): spoke to inr 0, plus rim edges (inr (2*i+1), inr (2*i+2)) for i < k+1.
    --     Size = 1 + (k+1) = k+2 = (2*k+4)/2.
    --   n = 2*k+1 (odd): rim edges (inr (2*i), inr (2*i+1)) for i < k+2.
    --     Size = k+2 = (2*k+3+1)/2 = (n+4)/2.
    -- These edges are pairwise disjoint, so the corresponding vertices of lineGraph G
    -- form an independent set.
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · -- Even case: n = 2*k
      have hconvert : (wheel (2 * k + 3)).lineGraph.indepNum =
          (CGraph.wheel (2 * k + 3)).lineGraph.indepNum := by
        rw [show (wheel (2 * k + 3) : IsoGraph) = ⟦CGraph.wheel (2 * k + 3)⟧ from rfl,
            lineGraph_mk, indepNum_mk]
      rw [hconvert]
      have harith : (2 * k + 4) / 2 = k + 2 := by omega
      rw [harith]
      set m : ℕ := 2 * k + 3
      -- spokes edge: {inl 0, inr 0}
      let mkSpoke : Sym2 (Fin 1 ⊕ Fin m) := Sym2.mk (Sum.inl ⟨0, by omega⟩, Sum.inr ⟨0, by omega⟩)
      -- rim edges for j : Fin (k+1): {inr(2*j+1), inr(2*j+2)}
      let mkRim : Fin (k + 1) → Sym2 (Fin 1 ⊕ Fin m) :=
        fun j => Sym2.mk (Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩, Sum.inr ⟨2 * (j : ℕ) + 2, by omega⟩)
      -- Show spoke is in edgeSet
      have hspoke_mem : mkSpoke ∈ (CGraph.wheel m).toSimple.edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        simp [CGraph.wheel]
        rw [CGraph.join_adj_inl_inr]
      -- Show each rim edge is in edgeSet
      have hrim_mem : ∀ j : Fin (k + 1),
          mkRim j ∈ (CGraph.wheel m).toSimple.edgeSet := by
        intro j
        rw [SimpleGraph.mem_edgeSet]
        simp [CGraph.wheel]
        rw [CGraph.join_adj_inr_inr]
        show (CGraph.cycle m).Adj ⟨2 * (j : ℕ) + 1, by omega⟩ ⟨2 * (j : ℕ) + 2, by omega⟩ = true
        simp [CGraph.cycle, CGraph.ofRel_adj]
        have hj : (j : ℕ) < k + 1 := j.is_lt
        rw [Nat.mod_eq_of_lt (by omega : 2 * (j : ℕ) + 2 < m)]
        simp
      -- mkRim is injective
      have hrim_inj : Function.Injective mkRim := by
        intro j j' hjj'
        simp only [mkRim] at hjj'
        set a : Fin m := ⟨2 * (j : ℕ) + 1, by omega⟩
        set b : Fin m := ⟨2 * (j : ℕ) + 2, by omega⟩
        set a' : Fin m := ⟨2 * (j' : ℕ) + 1, by omega⟩
        set b' : Fin m := ⟨2 * (j' : ℕ) + 2, by omega⟩
        have heq : Sym2.mk (Sum.inr a, Sum.inr b) = Sym2.mk (Sum.inr a', Sum.inr b') := hjj'
        have ha_in_edge' : (Sum.inr a : Fin 1 ⊕ Fin m) ∈ Sym2.mk (Sum.inr a', Sum.inr b') := by
          rw [← heq]
          show Sym2.Mem _ _
          simp [Sym2.Mem]
        simp at ha_in_edge'
        obtain h | h := ha_in_edge'
        · simp [a, a'] at h
          exact Fin.ext (by omega)
        · simp [a, b'] at h
          omega
      let spokeV : (CGraph.lineGraph (CGraph.wheel m)).V := ⟨mkSpoke, hspoke_mem⟩
      let rimV : Fin (k + 1) → (CGraph.lineGraph (CGraph.wheel m)).V :=
        fun j => ⟨mkRim j, hrim_mem j⟩
      -- Charactize spokeV vs rimV: spokeV has inl, rimV edges don't
      -- Charactize mkSpoke membership
      have hmem_spoke_lhs : (Sum.inl ⟨0, by omega⟩ : Fin 1 ⊕ Fin m) ∈ mkSpoke ∧
          (Sum.inr ⟨0, by omega⟩ : Fin 1 ⊕ Fin m) ∈ mkSpoke := by
        simp [mkSpoke]
      have hnotmem_spoke : ∀ (v : Fin 1 ⊕ Fin m) (j : Fin (k + 1)), v ∈ mkSpoke → v ∉ mkRim j := by
        intro v j hvmem
        simp [mkSpoke] at hvmem
        rcases hvmem with rfl | rfl <;> simp [mkRim]
      -- spokeV ≠ rimV j
      have hspoke_ne_rim : ∀ j : Fin (k + 1), spokeV ≠ rimV j := by
        intro j heq
        have hval : mkSpoke = mkRim j := Subtype.ext_iff.mp heq
        have h1 : Sum.inl ⟨0, by omega⟩ ∈ mkSpoke := hmem_spoke_lhs.1
        rw [hval] at h1
        exact absurd h1 (hnotmem_spoke _ j (hmem_spoke_lhs.1))
      -- Charactize mkRim membership
      have hmemRim_char : ∀ j : Fin (k + 1), ∀ y : Fin 1 ⊕ Fin m,
          y ∈ mkRim j ↔ y = Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩ ∨ y = Sum.inr
            ⟨2 * (j : ℕ) + 2, by omega⟩ := by
        intro j y; simp [mkRim]
      -- LineGraph vertices: spokeV and all rimV
      let vertices : Finset (CGraph.lineGraph (CGraph.wheel m)).V :=
        {spokeV} ∪ Finset.univ.image rimV
      have hindependent : SimpleGraph.IsIndepSet (CGraph.lineGraph (CGraph.wheel m)).toSimple
        (vertices : Set _) := by
        unfold SimpleGraph.IsIndepSet
        intro v hv w hw hvw
        have hv' : v = spokeV ∨ ∃ j : Fin (k + 1), rimV j = v := by
          simp [vertices]
            at hv
          exact hv
        have hw' : w = spokeV ∨ ∃ j : Fin (k + 1), rimV j = w := by
          simp [vertices]
            at hw
          exact hw
        rcases hv' with rfl | ⟨j, rfl⟩
        · rcases hw' with rfl | ⟨j', rfl⟩
          · exact absurd rfl hvw
          · intro h
            simp [CGraph.toSimple] at h
            obtain ⟨_, ⟨v, hv1, hv2⟩⟩ := h
            exact hnotmem_spoke v j' hv1 hv2
        · rcases hw' with rfl | ⟨j', rfl⟩
          · intro h
            simp [CGraph.toSimple] at h
            obtain ⟨_, ⟨v, hv1, hv2⟩⟩ := h
            exact hnotmem_spoke v j hv2 hv1
          · by_cases heq : j = j'
            · subst heq; simp [CGraph.toSimple, CGraph.lineGraph_adj]
            · intro h
              simp [CGraph.toSimple, CGraph.lineGraph_adj, rimV, hmemRim_char] at h
              have hne' : (j : ℕ) ≠ (j' : ℕ) := fun hval => heq (Fin.ext hval)
              omega
      have hcard : vertices.card = k + 2 := by
        simp only [vertices]
        have hdisj : Disjoint {spokeV} (Finset.univ.image rimV) := by
          rw [Finset.disjoint_singleton_left]
          intro hv
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
          exact hspoke_ne_rim j (hj.symm)
        rw [Finset.card_union_of_disjoint hdisj]
        simp [Finset.card_singleton]
        rw [Finset.card_image_of_injective _ (fun j j' hj => hrim_inj (Subtype.ext_iff.mp hj))]
        simp; omega
      exact hcard ▸ SimpleGraph.IsIndepSet.card_le_indepNum hindependent
    · -- Odd case: n = 2*k+1
      -- Goal: (2*k+5)/2 ≤ (wheel (2*k+4)).lineGraph.indepNum
      -- We work at CGraph level. wheel (2*k+4) as IsoGraph = ⟦CGraph.wheel (2*k+4)⟧
      -- lineGraph (wheel (2*k+4)) as IsoGraph = ⟦CGraph.lineGraph (CGraph.wheel (2*k+4))⟧
      -- indepNum of that = (CGraph.lineGraph (CGraph.wheel (2*k+4))).indepNum
      have hconvert : (wheel (2 * k + 1 + 3)).lineGraph.indepNum =
          (CGraph.wheel (2 * k + 4)).lineGraph.indepNum := by
        rw [show (wheel (2 * k + 1 + 3) : IsoGraph) = ⟦CGraph.wheel (2 * k + 4)⟧ from rfl,
            lineGraph_mk, indepNum_mk]
      rw [hconvert]
      -- Simplify arithmetic
      have harith : (2 * k + 1 + 4) / 2 = k + 2 := by omega
      rw [harith]
      -- Define the candidate independent set: rim edges E_j = {inr(2j), inr(2j+1)} for j : Fin
      -- (k+2)
      set m : ℕ := 2 * k + 4
      -- Each edge as a Sym2
      let mkEdge : Fin (k + 2) → Sym2 (Fin 1 ⊕ Fin m) :=
        fun j => Sym2.mk (Sum.inr ⟨2 * (j : ℕ), by omega⟩, Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩)
      -- Show each mkEdge j is in the wheel's edgeSet
      have hedge_mem : ∀ j : Fin (k + 2),
          mkEdge j ∈ (CGraph.wheel m).toSimple.edgeSet := by
        intro j
        rw [SimpleGraph.mem_edgeSet]
        simp [CGraph.wheel]
        rw [CGraph.join_adj_inr_inr]
        show (CGraph.cycle m).Adj ⟨2 * (j : ℕ), by omega⟩ ⟨2 * (j : ℕ) + 1, by omega⟩ = true
        simp [CGraph.cycle, CGraph.ofRel_adj]
        have hj : (j : ℕ) < k + 2 := j.is_lt
        rw [Nat.mod_eq_of_lt (by omega : 2 * (j : ℕ) + 1 < m)]
        simp
      -- Build the Finset of lineGraph vertices
      let vertices : Finset (CGraph.lineGraph (CGraph.wheel m)).V :=
        Finset.univ.image (fun j : Fin (k + 2) =>
          ⟨mkEdge j, hedge_mem j⟩)
      -- Show the vertices are pairwise non-adjacent in lineGraph
      have hindependent : SimpleGraph.IsIndepSet (CGraph.lineGraph (CGraph.wheel m)).toSimple
        (vertices : Set _) := by
        unfold SimpleGraph.IsIndepSet
        intro v hv w hw
        -- Get the Fin indices
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (show v ∈ vertices from hv)
        obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp (show w ∈ vertices from hw)
        simp [CGraph.lineGraph_adj]
        intro hne hsym2 x hx
        -- Characterize membership in mkEdge
        have hmem_j : ∀ y, y ∈ mkEdge j ↔ y = Sum.inr ⟨2 * (j : ℕ), by omega⟩ ∨ y = Sum.inr
          ⟨2 * (j : ℕ) + 1, by omega⟩ := by
          simp [mkEdge]
        have hmem_j' : ∀ y, y ∈ mkEdge j' ↔ y = Sum.inr ⟨2 * (j' : ℕ), by omega⟩ ∨ y = Sum.inr
          ⟨2 * (j' : ℕ) + 1, by omega⟩ := by
          simp [mkEdge]
        rw [hmem_j] at hx
        rw [hmem_j']
        rcases hx with hx | hx <;> intro h <;> rw [hx] at h <;> simp at h
        all_goals {
          -- h is of the form inr ... = inr ... implying 2*j = 2*j' or similar as Fin m
          have hne' : j ≠ j' := fun heq => hsym2 (heq ▸ rfl)
          omega
        }
      -- mkEdge is injective
      have hmk_inj : Function.Injective mkEdge := by
        intro j j' hjj'
        simp only [mkEdge] at hjj'
        -- Extract membership from mkEdge j
        set a : Fin m := ⟨2 * (j : ℕ), by omega⟩
        set b : Fin m := ⟨2 * (j : ℕ) + 1, by omega⟩
        set a' : Fin m := ⟨2 * (j' : ℕ), by omega⟩
        set b' : Fin m := ⟨2 * (j' : ℕ) + 1, by omega⟩
        have heq : Sym2.mk (Sum.inr a, Sum.inr b) = Sym2.mk (Sum.inr a', Sum.inr b') := hjj'
        -- From Sym2.mk equality, we know Sum.inr a is in the second mk, so it equals inr a' or inr
        -- b'
        have ha_in_edge' : (Sum.inr a : Fin 1 ⊕ Fin m) ∈ Sym2.mk (Sum.inr a', Sum.inr b') := by
          rw [← heq]
          show Sym2.Mem _ _
          simp [Sym2.Mem]
        simp at ha_in_edge'
        obtain h | h := ha_in_edge'
        · -- inr a = inr a' (h : a = a' as Fin m)
          exact Fin.ext (by simp [a, a'] at h; omega)
        · -- inr a = inr b' (h : a = b' as Fin m)
          simp [a, b'] at h
          omega
      -- Show cardinality
      have hcard : vertices.card = k + 2 := by
        simp only [vertices]
        have hlift_inj : Function.Injective (fun j : Fin (k + 2) => ⟨mkEdge j, hedge_mem j⟩ : Fin (k
          + 2) → (CGraph.lineGraph (CGraph.wheel m)).V) := by
          intro j j' hj
          exact hmk_inj (Subtype.ext_iff.mp hj)
        rw [Finset.card_image_of_injective _ hlift_inj, Finset.card_fin]
      -- Conclude
      exact hcard ▸ SimpleGraph.IsIndepSet.card_le_indepNum hindependent

/-- The line graph of a connected graph with at least one edge is connected. -/
theorem isConnected_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E) :
    IsConnected (lineGraph G) := by
  set H := G.toCGraph with hH_def
  rw [← IsoGraph.mk_toCGraph G]
  rw [lineGraph_mk H]
  rw [isConnected_mk]
  simp only [hH_def] at *
  have hG' : G.toCGraph.IsConnected := by
    rw [← isConnected_mk (G := G.toCGraph), IsoGraph.mk_toCGraph]
    exact hG
  have hE' : 0 < G.toCGraph.E := by
    rw [← E_mk (G := G.toCGraph), IsoGraph.mk_toCGraph]
    exact hE
  -- Theorem: line graph of a connected graph with edges is connected.
  have hedges : G.toCGraph.toSimple.edgeFinset.Nonempty := Finset.card_pos.mp
    (by rwa [CGraph.E] at hE')
  obtain ⟨e₀, he₀⟩ := hedges
  have he₀' : e₀ ∈ G.toCGraph.toSimple.edgeSet := by simpa using he₀
  set e₀' : (CGraph.lineGraph G.toCGraph).V := ⟨e₀, he₀'⟩
  -- For any vertex v of G, if some edge incident to v is reachable from e₀', then all edges
  -- incident to v are reachable from e₀'
  -- (because edges incident to the same vertex form a clique in the line graph)
  -- For any edge f of G, since G is connected, there's a path of vertices from an endpoint of e₀ to
  -- an endpoint of f.
  -- By induction along this path, all edges incident to vertices on the path are reachable. In
  -- particular, edges incident to the other endpoint of f are reachable, so f is reachable.
  -- Step 1: edges incident to a vertex u are pairwise reachable (they form a clique)
  have hclique : ∀ (u : G.toCGraph.V) (f g : (CGraph.lineGraph G.toCGraph).V),
      u ∈ f.1 → u ∈ g.1 → SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple f g := by
    intro u f g huf hug
    by_cases hfg : f = g
    · rw [hfg]
    · have hadj : (CGraph.lineGraph G.toCGraph).Adj f g = true := by
        rw [CGraph.lineGraph_adj]
        simp [hfg]
        exact ⟨u, huf, hug⟩
      exact (CGraph.toSimple_adj _ _ _).mpr hadj |>.reachable
  -- Pick an endpoint a of e₀
  -- Get endpoints of e₀: e₀'.1 is a Sym2 of V, and it's in edgeSet so it's an actual edge.
  -- I need at least one vertex from e₀'.1. I'll use induction on Sym2.
  have h_sym2_mem : ∀ (s : Sym2 (G.toCGraph.V)), ∃ v : G.toCGraph.V, v ∈ s := by
    intro s
    change Quot (Sym2.Rel (G.toCGraph.V)) at s
    obtain ⟨p, rfl⟩ := Quot.exists_rep s
    refine ⟨p.1, ?_⟩
    show Sym2.Mem p.1 (Quot.mk (Sym2.Rel G.toCGraph.V) p)
    simp [Sym2.Mem]
    exact ⟨p.2, Or.inl rfl⟩
  obtain ⟨a, ha_mem⟩ := h_sym2_mem e₀'.1
  -- All edges incident to a are reachable from e₀' (clique at a, using e₀' itself)
  have hreach_a : ∀ f : (CGraph.lineGraph G.toCGraph).V, a ∈ f.1 →
      SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple e₀' f := by
    intro f hf
    exact hclique a e₀' f ha_mem hf
  -- A vertex is "swept" if all edges incident to it are reachable from e₀'
  let Swept (v : G.toCGraph.V) : Prop := ∀ f : (CGraph.lineGraph G.toCGraph).V, v ∈ f.1 →
      SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple e₀' f
  have hswept_a : Swept a := hreach_a
  -- Sweep propagates along adjacencies
  have hsweep_prop : ∀ u v : G.toCGraph.V, G.toCGraph.Adj u v = true → Swept u → Swept v := by
    intro u v huv ih
    -- The edge {u,v} is incident to u, hence reachable
    let fe : (CGraph.lineGraph G.toCGraph).V := ⟨Sym2.mk ⟨u, v⟩, by
      simpa [CGraph.toSimple_adj, SimpleGraph.mem_edgeSet] using huv⟩
    have hfe_u : u ∈ fe.1 := by simp [fe]
    have hfe_v : v ∈ fe.1 := by simp [fe]
    have hfe_reach := ih fe hfe_u
    intro g hg_v
    exact hfe_reach.trans (hclique v fe g hfe_v hg_v)
  -- All vertices are swept (by connectedness, from a)
  have hswept_all : ∀ v : G.toCGraph.V, Swept v := by
    intro v
    have hswept_all' : ∀ {u w : G.toCGraph.V} (w' : G.toCGraph.toSimple.Walk u w), Swept u → Swept w
      := by
      intro u w w'
      induction w' with
      | nil => exact id
      | cons hadj tail ih =>
        intro hu
        exact ih (hsweep_prop _ _ hadj hu)
    have hreach : G.toCGraph.toSimple.Reachable a v := by
      change G.toCGraph.toSimple.Connected at hG'
      exact hG' a v
    obtain ⟨w⟩ := hreach
    exact hswept_all' w hswept_a
  -- All edges of G are reachable
  have hreach_all_edges : ∀ f : (CGraph.lineGraph G.toCGraph).V,
      SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple e₀' f := by
    intro f
    obtain ⟨v, hv⟩ := h_sym2_mem f.1
    exact hswept_all v f hv
  letI : Nonempty (CGraph.lineGraph G.toCGraph).V := ⟨e₀'⟩
  exact SimpleGraph.Connected.mk (fun e f => (hreach_all_edges e).symm.trans (hreach_all_edges f))

/-! ### Consequences of the strong-product radius and of line-graph connectivity -/

/-- A connected graph with an edge has a connected line graph, so its line graph has one
component. -/
@[simp] theorem numComponents_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E) :
    (lineGraph G).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_lineGraph hG hE)

theorem radius_strongProduct_self {G : IsoGraph} (hG : IsConnected G) :
    (G ⊠g G).radius = G.radius := by
  rw [radius_strongProduct hG hG, max_self]

/-- The **king graph** on an `(m+1) × (n+1)` board: a king reaches every square from the middle
of the longer side. -/
@[simp] theorem radius_strongProduct_path (m n : ℕ) :
    (path (m + 1) ⊠g path (n + 1)).radius = max ((m + 1) / 2) ((n + 1) / 2) := by
  rw [radius_strongProduct (isConnected_path m) (isConnected_path n), radius_path, radius_path]

/-- The **toroidal king graph**. -/
@[simp] theorem radius_strongProduct_cycle (m n : ℕ) :
    (cycle (m + 1) ⊠g cycle (n + 1)).radius = max ((m + 1) / 2) ((n + 1) / 2) := by
  rw [radius_strongProduct (isConnected_cycle m) (isConnected_cycle n), radius_cycle, radius_cycle]

@[simp] theorem radius_strongProduct_hypercube (m n : ℕ) :
    (hypercube m ⊠g hypercube n).radius = max m n := by
  rw [radius_strongProduct (isConnected_hypercube m) (isConnected_hypercube n), radius_hypercube,
    radius_hypercube]

/-- In the strong product, distances are the maximum of the two coordinate distances, so the
diameter is the maximum of the two diameters. -/
theorem diameter_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ⊠g H).diameter = max G.diameter H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, diameter_mk, diameter_mk,
    diameter_mk]
  rw [isConnected_mk] at hG hH
  haveI : Nonempty g.V := hG.nonempty
  haveI : Nonempty h.V := hH.nonempty
  set Gs := g.toSimple
  set Hs := h.toSimple
  set SPs := (g.strongProduct h).toSimple
  have hSP_adj : ∀ p q : g.V × h.V,
      SPs.Adj p q ↔ p ≠ q ∧ ((p.1 = q.1 ∨ Gs.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ Hs.Adj p.2 q.2)) := by
    simp [SPs, CGraph.toSimple, CGraph.strongProduct, Gs, Hs]
  --PROJECT WALK LENGTHS TO G COORDINATE
  have projectWalk_G_len : ∀ {u v : g.V × h.V}
      (W : SPs.Walk u v), Gs.edist u.1 v.1 ≤ ↑W.length := by
    intro u v W
    induction W with
    | nil => simp
    | @cons a b c hpq rest ih =>
      rw [SimpleGraph.Walk.length_cons]
      rcases (hSP_adj a b).mp hpq |>.2.1 with heq | hadj
      · rw [heq]
        exact le_trans ih (by exact_mod_cast Nat.cast_le.mpr (Nat.le_add_right _ _))
      · have : Gs.edist a.1 b.1 ≤ 1 := by
          exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj
            SimpleGraph.Walk.nil)) (by simp)
        calc Gs.edist a.1 c.1 ≤ Gs.edist a.1 b.1 + Gs.edist b.1 c.1 := SimpleGraph.edist_triangle
            _ ≤ 1 + ↑rest.length := add_le_add this ih
            _ = ↑(rest.length + 1) := by push_cast; ring
  --PROJECT WALK LENGTHS TO H COORDINATE
  have projectWalk_H_len : ∀ {u v : g.V × h.V}
      (W : SPs.Walk u v), Hs.edist u.2 v.2 ≤ ↑W.length := by
    intro u v W
    induction W with
    | nil => simp
    | @cons a b c hpq rest ih =>
      rw [SimpleGraph.Walk.length_cons]
      rcases (hSP_adj a b).mp hpq |>.2.2 with heq | hadj
      · rw [heq]
        exact le_trans ih (by exact_mod_cast Nat.cast_le.mpr (Nat.le_add_right _ _))
      · have : Hs.edist a.2 b.2 ≤ 1 := by
          exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj
            SimpleGraph.Walk.nil)) (by simp)
        calc Hs.edist a.2 c.2 ≤ Hs.edist a.2 b.2 + Hs.edist b.2 c.2 := SimpleGraph.edist_triangle
            _ ≤ 1 + ↑rest.length := add_le_add this ih
            _ = ↑(rest.length + 1) := by push_cast; ring
  --LOWER BOUND: G distance ≤ SP distance (fixing H-coordinate)
  have hedist_ge_G : ∀ (h0 : h.V) (g1 g2 : g.V),
      Gs.edist g1 g2 ≤ SPs.edist (g1, h0) (g2, h0) := by
    intro h0 g1 g2
    by_cases hne : Nonempty (SPs.Walk (g1, h0) (g2, h0))
    · exact le_iInf (fun q => projectWalk_G_len q)
    · push_neg at hne
      have : SPs.edist (g1, h0) (g2, h0) = ⊤ := by
        rw [SimpleGraph.edist_eq_top_of_not_reachable]
        exact fun hr => hne.elim hr.some
      exact this.symm ▸ le_top
  --LOWER BOUND: H distance ≤ SP distance (fixing G-coordinate)
  have hedist_ge_H : ∀ (g0 : g.V) (h1 h2 : h.V),
      Hs.edist h1 h2 ≤ SPs.edist (g0, h1) (g0, h2) := by
    intro g0 h1 h2
    by_cases hne : Nonempty (SPs.Walk (g0, h1) (g0, h2))
    · exact le_iInf (fun q => projectWalk_H_len q)
    · push_neg at hne
      have : SPs.edist (g0, h1) (g0, h2) = ⊤ := by
        rw [SimpleGraph.edist_eq_top_of_not_reachable]
        exact fun hr => hne.elim hr.some
      exact this.symm ▸ le_top
  --LOWER BOUND on ediam
  have hedist_le_SPdiam_G : ∀ g1 g2 : g.V, Gs.edist g1 g2 ≤ SPs.ediam := by
    intro g1 g2
    exact le_trans (hedist_ge_G (Classical.arbitrary h.V) g1 g2) (SimpleGraph.edist_le_ediam)
  have hedist_le_SPdiam_H : ∀ h1 h2 : h.V, Hs.edist h1 h2 ≤ SPs.ediam := by
    intro h1 h2
    exact le_trans (hedist_ge_H (Classical.arbitrary g.V) h1 h2) (SimpleGraph.edist_le_ediam)
  have hediam_ge_G : Gs.ediam ≤ SPs.ediam := by
    apply SimpleGraph.ediam_le_of_edist_le; intro g1 g2; exact hedist_le_SPdiam_G g1 g2
  have hediam_ge_H : Hs.ediam ≤ SPs.ediam := by
    apply SimpleGraph.ediam_le_of_edist_le; intro h1 h2; exact hedist_le_SPdiam_H h1 h2
  --SP walk of length ≤ max WG.length WH.length (combining walks)
  let toSP_G (h0 : h.V) : Gs →g SPs := {
    toFun := fun g => (g, h0)
    map_rel' := @fun (a b : g.V) hab =>
      hSP_adj (a, h0) (b, h0) |>.mpr ⟨ne_of_apply_ne Prod.fst hab.ne, Or.inr hab, Or.inl rfl⟩
  }
  let toSP_H (g0 : g.V) : Hs →g SPs := {
    toFun := fun h => (g0, h)
    map_rel' := @fun (a b : h.V) hab =>
      hSP_adj (g0, a) (g0, b) |>.mpr ⟨ne_of_apply_ne Prod.snd hab.ne, Or.inl rfl, Or.inr hab⟩
  }
  have spWalk_max : ∀ (n : ℕ) {g1 g2 : g.V} {h1 h2 : h.V}
      (WG : Gs.Walk g1 g2) (WH : Hs.Walk h1 h2),
      WG.length + WH.length ≤ n →
      ∃ (W : SPs.Walk (g1, h1) (g2, h2)), W.length ≤ max WG.length WH.length := by
    intro n
    induction n with
    | zero =>
      intro g1 g2 h1 h2 WG WH hle
      have hWG : WG.length = 0 := by omega
      have hWH : WH.length = 0 := by omega
      have hg1g2 : g1 = g2 := by
        have := WG.getVert_zero; have := WG.getVert_length; simp [hWG] at *; exact this
      have hh1h2 : h1 = h2 := by
        have := WH.getVert_zero; have := WH.getVert_length; simp [hWH] at *; exact this
      subst hg1g2; subst hh1h2
      exact ⟨.nil, by simp⟩
    | succ m ih =>
      intro g1 g2 h1 h2 WG WH hle
      by_cases hg : WG.length = 0
      · have hg1g2 : g1 = g2 := by
          have := WG.getVert_zero; have := WG.getVert_length; simp [hg] at *; exact this
        subst hg1g2
        exact ⟨WH.map (toSP_H g1), by simp [hg]⟩
      · by_cases hh : WH.length = 0
        · have hh1h2 : h1 = h2 := by
            have := WH.getVert_zero; have := WH.getVert_length; simp [hh] at *; exact this
          subst hh1h2
          exact ⟨WG.map (toSP_G h1), by simp [hh]⟩
        · cases WG with
          | nil => contradiction
          | cons hab WGtail =>
            cases WH with
            | nil => contradiction
            | cons hcd WHtail =>
              obtain ⟨W', hW'⟩ := ih WGtail WHtail
                (by simp [SimpleGraph.Walk.length_cons] at hle ⊢; omega)
              exact
                ⟨SimpleGraph.Walk.cons (hSP_adj _ _ |>.mpr
                    ⟨by rintro ⟨rfl, rfl⟩; exact hab.ne rfl, Or.inr hab, Or.inr hcd⟩) W', by
                  simp [SimpleGraph.Walk.length_cons] at hW' ⊢
                  omega⟩
  --UPPER BOUND: SP edist ≤ max of coordinate edists
  have hedist_le_max : ∀ g1 g2 : g.V, ∀ h1 h2 : h.V,
      SPs.edist (g1, h1) (g2, h2) ≤ max (Gs.edist g1 g2) (Hs.edist h1 h2) := by
    intro g1 g2 h1 h2
    by_cases hg : Gs.edist g1 g2 = ⊤
    · simp [hg]
    by_cases hh : Hs.edist h1 h2 = ⊤
    · simp [hh]
    obtain ⟨WG, hWG⟩ := SimpleGraph.exists_walk_of_edist_ne_top hg
    obtain ⟨WH, hWH⟩ := SimpleGraph.exists_walk_of_edist_ne_top hh
    obtain ⟨W, hW⟩ := spWalk_max (WG.length + WH.length) WG WH (le_refl _)
    calc SPs.edist (g1, h1) (g2, h2) ≤ ↑W.length := SimpleGraph.Walk.edist_le W
      _ ≤ ↑(max WG.length WH.length) := WithTop.coe_mono hW
      _ = max (WG.length : ℕ∞) (WH.length : ℕ∞) := by
          cases le_total WG.length WH.length with
          | inl h =>
            rw [show max WG.length WH.length = WH.length from max_eq_right h]
            rw [max_eq_right (ENat.coe_le_coe.mpr h)]
          | inr h =>
            rw [show max WG.length WH.length = WG.length from max_eq_left h]
            rw [max_eq_left (ENat.coe_le_coe.mpr h)]
      _ ≤ max (Gs.edist g1 g2) (Hs.edist h1 h2) :=
          max_le_max (hWG.le) (hWH.le)
  --UPPER BOUND on ediam
  have hediam_le_max : SPs.ediam ≤ max Gs.ediam Hs.ediam := by
    apply SimpleGraph.ediam_le_of_edist_le
    rintro ⟨g1, h1⟩ ⟨g2, h2⟩
    exact le_trans (hedist_le_max g1 g2 h1 h2)
      (max_le_max (SimpleGraph.edist_le_ediam : Gs.edist g1 g2 ≤ Gs.ediam)
                 (SimpleGraph.edist_le_ediam : Hs.edist h1 h2 ≤ Hs.ediam))
  --FINAL: ediam equality
  have h_ediam_eq : SPs.ediam = max Gs.ediam Hs.ediam := by
    exact le_antisymm hediam_le_max (max_le hediam_ge_G hediam_ge_H)
  -- Convert to CGraph.diameter for canonicalize via isomorphism
  have hg_iso : g.toSimple ≃g g.canonicalize.toSimple := CGraph.Iso.toSimpleIso
    (CGraph.isoCanonicalize g)
  have hh_iso : h.toSimple ≃g h.canonicalize.toSimple := CGraph.Iso.toSimpleIso
    (CGraph.isoCanonicalize h)
  have hSP_iso : (g.strongProduct h).toSimple ≃g (g.canonicalize.strongProduct
    h.canonicalize).toSimple :=
    CGraph.Iso.toSimpleIso (CGraph.Iso.strongProduct (CGraph.isoCanonicalize g)
      (CGraph.isoCanonicalize h))
  have hdiam_G : CGraph.diameter g = CGraph.diameter g.canonicalize := by
    rw [CGraph.diameter, CGraph.diameter]
    exact hg_iso.diam_eq
  have hdiam_H : CGraph.diameter h = CGraph.diameter h.canonicalize := by
    rw [CGraph.diameter, CGraph.diameter]
    exact hh_iso.diam_eq
  have hdiam_SP : CGraph.diameter (g.strongProduct h) = CGraph.diameter
    (g.canonicalize.strongProduct h.canonicalize) := by
    rw [CGraph.diameter, CGraph.diameter, hSP_iso.diam_eq]
  rw [← hdiam_SP, ← hdiam_G, ← hdiam_H]
  show CGraph.diameter (g.strongProduct h) = max (CGraph.diameter g) (CGraph.diameter h)
  rw [CGraph.diameter, CGraph.diameter, CGraph.diameter]
  rw [SimpleGraph.diam, SimpleGraph.diam, SimpleGraph.diam]
  rw [h_ediam_eq]
  have hGtop : g.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hG
  have hHtop : h.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hH
  have key : ∀ (a b : ℕ∞), a ≠ ⊤ → b ≠ ⊤ → (max a b).toNat = max a.toNat b.toNat := by
    intro a b ha hb
    cases le_total a b with
    | inl hab =>
      rw [max_eq_right hab, max_eq_right (ENat.toNat_le_toNat hab hb)]
    | inr hab =>
      rw [max_eq_left hab, max_eq_left (ENat.toNat_le_toNat hab ha)]
  rw [key _ _ hGtop hHtop]

@[simp] theorem diameter_strongProduct_cycle (m n : ℕ) :
    (cycle (m + 1) ⊠g cycle (n + 1)).diameter = max ((m + 1) / 2) ((n + 1) / 2) := by
  rw [diameter_strongProduct (isConnected_cycle m) (isConnected_cycle n), diameter_cycle,
    diameter_cycle]

@[simp] theorem diameter_strongProduct_hypercube (m n : ℕ) :
    (hypercube m ⊠g hypercube n).diameter = max m n := by
  rw [diameter_strongProduct (isConnected_hypercube m) (isConnected_hypercube n),
    diameter_hypercube, diameter_hypercube]

/-- A near-perfect matching leaves at most one vertex over, so the wheel is covered by that many
cliques. -/
theorem cliqueCoverNum_wheel_le (n : ℕ) :
    (wheel (n + 3)).cliqueCoverNum ≤ (n + 5) / 2 := by
  have h := cliqueCoverNum_le_V_sub_matchNum (wheel (n + 3))
  rw [V_wheel, matchNum_wheel] at h
  omega

@[simp] theorem isVertexTransitive_johnson (n k : ℕ) : IsVertexTransitive (johnson n k) :=
  CGraph.isVertexTransitive_johnson n k

/-! ### Invariants of the Johnson graphs from vertex transitivity -/

/-- The radius of a Johnson graph equals its diameter, `min k (n - k)`. -/
@[simp] theorem radius_johnson {n k : ℕ} (hk : k ≤ n) : (johnson n k).radius = min k (n - k) := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_johnson n k),
    diameter_johnson hk]

/-- The clique–coclique bound for a Johnson graph. -/
theorem indepNum_mul_cliqueNum_le_johnson (n k : ℕ) :
    (johnson n k).indepNum * (johnson n k).cliqueNum ≤ n.choose k := by
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_johnson n k)
  rwa [V_johnson] at h

/-- A vertex-transitive graph with an edge has an independent set on at most half its vertices. -/
theorem two_mul_indepNum_le_johnson {n k : ℕ} (hE : 0 < (johnson n k).E) :
    2 * (johnson n k).indepNum ≤ n.choose k := by
  have h := two_mul_indepNum_le_V (isVertexTransitive_johnson n k) hE
  rwa [V_johnson] at h

theorem coverNum_johnson (n k : ℕ) :
    (johnson n k).coverNum = n.choose k - (johnson n k).indepNum := by
  rw [coverNum_eq, V_johnson]

/-! ### Graphs that are not vertex transitive, by an irregular degree

A vertex-transitive graph is regular, so exhibiting two vertices of different degrees rules
transitivity out.  This settles the whole "hub plus rim" family, where the hub is the odd one
out, and the paths and ladders, where the ends are. -/

/-- **A graph with two vertices of different degrees is not vertex transitive.** -/
theorem not_isVertexTransitive_of_minDeg_ne_maxDeg {G : IsoGraph} (hV : 0 < G.V)
    (h : G.minDeg ≠ G.maxDeg) : ¬ IsVertexTransitive G := by
  intro hvt
  obtain ⟨k, hk⟩ := exists_isRegularWith_of_isVertexTransitive hvt
  exact h ((hk.minDeg_eq hV).trans (hk.maxDeg_eq hV).symm)

@[simp] theorem not_isVertexTransitive_path (n : ℕ) : ¬ IsVertexTransitive (path (n + 3)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 3 = n + 1 + 2 from rfl, minDeg_path, show n + 1 + 2 = n + 3 from rfl, maxDeg_path]
  omega

@[simp] theorem not_isVertexTransitive_star (n : ℕ) : ¬ IsVertexTransitive (star (n + 2)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 2 = n + 1 + 1 from rfl, minDeg_star, maxDeg_star]
  omega

/-- The hub of a wheel on five or more vertices has degree larger than three. -/
@[simp] theorem not_isVertexTransitive_wheel (n : ℕ) :
    ¬ IsVertexTransitive (wheel (n + 4)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 4 = n + 1 + 3 from rfl, minDeg_wheel, maxDeg_wheel]
  omega

/-- The hub of a fan on five or more vertices has degree larger than two. -/
@[simp] theorem not_isVertexTransitive_fan (n : ℕ) : ¬ IsVertexTransitive (fan (n + 3)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 3 = n + 1 + 2 from rfl, minDeg_fan, show n + 1 + 2 = n + 3 from rfl, maxDeg_fan]
  omega

/-- The spine of a book with two or more pages has degree larger than two. -/
@[simp] theorem not_isVertexTransitive_book (n : ℕ) : ¬ IsVertexTransitive (book (n + 2)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 2 = n + 1 + 1 from rfl, minDeg_book, maxDeg_book]
  omega

/-- The four corners of a ladder have degree two, the rest three. -/
@[simp] theorem not_isVertexTransitive_ladder (n : ℕ) :
    ¬ IsVertexTransitive (ladder (n + 3)) := by
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [show n + 3 = n + 1 + 2 from rfl, minDeg_ladder, show n + 1 + 2 = n + 3 from rfl,
    maxDeg_ladder]
  omega

/-! ### Regularity of the ladder and of the wheel's rim -/

/-- A ladder is not regular for three or more rungs; the two small ones are `K₂` and `C₄`. -/
@[simp] theorem isRegularWith_ladder_two : (ladder 2).IsRegularWith 2 := by
  rw [ladder_two]
  exact isRegularWith_cycle 1

@[simp] theorem isVertexTransitive_ladder_two : IsVertexTransitive (ladder 2) := by
  rw [ladder_two]
  exact isVertexTransitive_cycle 4

@[simp] theorem isVertexTransitive_ladder_one : IsVertexTransitive (ladder 1) := by
  rw [ladder_one]
  exact isVertexTransitive_complete 2

/-! ### The common degree of a vertex-transitive graph -/

theorem isRegularWith_minDeg_of_isVertexTransitive {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) : G.IsRegularWith G.minDeg := by
  obtain ⟨k, hk⟩ := exists_isRegularWith_of_isVertexTransitive h
  rwa [hk.minDeg_eq hV]

@[simp] theorem minDeg_eq_maxDeg_of_isVertexTransitive {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) : G.minDeg = G.maxDeg :=
  (isRegularWith_minDeg_of_isVertexTransitive hV h).maxDeg_eq hV |>.symm

/-- **The handshake lemma for a vertex-transitive graph**: `2|E| = |V| · δ`. -/
theorem two_mul_E_of_isVertexTransitive {G : IsoGraph} (hV : 0 < G.V) (h : IsVertexTransitive G) :
    2 * G.E = G.V * G.minDeg :=
  (isRegularWith_minDeg_of_isVertexTransitive hV h).two_mul_E

theorem degSequence_of_isVertexTransitive_minDeg {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) : degSequence G = List.replicate G.V G.minDeg :=
  (isRegularWith_minDeg_of_isVertexTransitive hV h).degSequence

/-- A vertex-transitive graph on an odd number of vertices has even degree: `|V| · δ` is even. -/
theorem even_minDeg_of_isVertexTransitive_of_odd {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) (hodd : G.V % 2 = 1) : G.minDeg % 2 = 0 := by
  have h2 := two_mul_E_of_isVertexTransitive hV h
  rcases Nat.even_mul.1 (⟨G.E, by omega⟩ : Even (G.V * G.minDeg)) with he | he
  · exact absurd (Nat.even_iff.1 he) (by omega)
  · exact Nat.even_iff.1 he

/-- **The handshake lemma for a circulant**: `2|E| = n · δ`, with no need to count the
connection set. -/
theorem two_mul_E_circulant (n : ℕ) (S : List ℕ) (hn : 0 < n) :
    2 * (circulant n S).E = n * (circulant n S).minDeg := by
  have h := two_mul_E_of_isVertexTransitive (G := circulant n S) (by simpa using hn)
    (isVertexTransitive_circulant n S)
  rwa [V_circulant] at h

/-- A circulant on an odd number of vertices has even degree. -/
theorem even_minDeg_circulant_of_odd {n : ℕ} (S : List ℕ) (hodd : n % 2 = 1) :
    (circulant n S).minDeg % 2 = 0 := by
  refine even_minDeg_of_isVertexTransitive_of_odd (G := circulant n S) (by simp; omega)
    (isVertexTransitive_circulant n S) ?_
  rwa [V_circulant]

/-- A dominating set in `T(n) = L(Kₙ)` is an edge dominating set of `Kₙ`, so it must cover all
but one vertex; a near-perfect matching does it. -/
theorem domNum_triangular (n : ℕ) : (triangular (n + 2)).domNum = (n + 2) / 2 := by
  simp only [triangular, IsoGraph.johnson, IsoGraph.domNum_mk]
  -- goal: (CGraph.johnson (n + 2) 2).domNum = (n + 2) / 2
  apply le_antisymm
  · -- Upper bound: domNum ≤ indepNum ≤ (n+2)/2
    have h1 : (CGraph.johnson (n + 2) (2 : ℕ)).domNum ≤ (CGraph.johnson (n + 2) (2 : ℕ)).indepNum :=
      CGraph.domNum_le_indepNum _
    have h2 : (CGraph.johnson (n + 2) (2 : ℕ)).indepNum ≤ (n + 2) / 2 := by
      unfold CGraph.indepNum
      simp only [SimpleGraph.indepNum]
      apply csSup_le
      · -- nonempty
        exact ⟨0, ⟨∅, SimpleGraph.IsNIndepSet.mk (by simp [SimpleGraph.IsIndepSet]) rfl⟩⟩
      · -- upper bound
        intro b hb
        obtain ⟨S, hS_indep, rfl⟩ := hb
        -- Each pair of distinct vertices in S is disjoint (as Finsets)
        have hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint u.1 v.1 := by
          intro u hu v hv huv
          by_contra hndisj
          have hadj : (CGraph.johnson (n + 2) (2 : ℕ)).Adj u v := by
            simp [CGraph.johnson_adj, huv, beq_iff_eq]
            have hnd := Finset.not_disjoint_iff.mp hndisj
            exact CGraph.card_inter_eq_one_of_ne u v huv
              (by
                intro h
                obtain ⟨x, hxu, hxv⟩ := hnd
                exact absurd (h ▸ Finset.mem_inter_of_mem hxu hxv) (by simp))
          exact absurd hadj (hS_indep hu hv huv)
        have hcard2 : ∀ u ∈ S, u.1.card = 2 := fun u hu => u.2
        have hcard_biUnion : (S.biUnion (fun u => u.1)).card = ∑ u ∈ S, u.1.card :=
          Finset.card_biUnion (fun u hu v hv huv => hdisj u hu v hv huv)
        have hcard_sum : ∑ u ∈ S, u.1.card = 2 * S.card := by
          rw [Finset.sum_congr rfl hcard2]
          simp [Finset.sum_const, mul_comm]
        have hle : 2 * S.card ≤ (n + 2) := by
          have : (S.biUnion (fun u => u.1)).card = 2 * S.card := by rw [hcard_biUnion, hcard_sum]
          have hsub : S.biUnion (fun u => u.1) ⊆ Finset.univ := Finset.subset_univ _
          have := Finset.card_le_card hsub
          simp [Finset.card_univ, Fintype.card_fin] at this
          linarith
        omega
    omega
  · -- Lower bound
    have hlower : ∀ s : Finset (CGraph.johnson (n + 2) (2 : ℕ)).V,
        (CGraph.johnson (n + 2) (2 : ℕ)).IsDominatingSet s → (n + 2) / 2 ≤ s.card := by
      intro s hsdom
      by_contra hcard
      push_neg at hcard
      set covered := Finset.biUnion s (fun u => u.1) with hcovered_def
      have hcovered_size : covered.card ≤ 2 * s.card := by
        have : ∀ u ∈ s, u.1.card = 2 := fun u hu => u.2
        calc covered.card = (s.biUnion (fun u => u.1)).card := congr_arg Finset.card hcovered_def
          _ ≤ ∑ u ∈ s, u.1.card := Finset.card_biUnion_le
          _ = ∑ _ ∈ s, 2 := Finset.sum_congr rfl this
          _ = 2 * s.card := by simp [mul_comm]
      have h2le : 2 * s.card ≤ n := by omega
      have huncovered : (Finset.univ \ covered).card ≥ 2 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ Finset.univ \ covered, ∃ b ∈ Finset.univ \ covered, a ≠ b
        := by
        exact Finset.one_lt_card.mp huncovered
      let v : (CGraph.johnson (n + 2) (2 : ℕ)).V := ⟨{a, b}, Finset.card_pair hab⟩
      have hv_notin : v ∉ s := by
        intro hv
        have : a ∈ covered := hcovered_def ▸ Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_self _
          _⟩
        exact Finset.mem_sdiff.mp ha |>.2 this
      have ha_notin : ∀ u ∈ s, a ∉ u.1 := by
        intro u hu hua
        exact Finset.mem_sdiff.mp ha |>.2 (hcovered_def ▸ Finset.mem_biUnion.mpr ⟨u, hu, hua⟩)
      have hb_notin : ∀ u ∈ s, b ∉ u.1 := by
        intro u hu hub
        exact Finset.mem_sdiff.mp hb |>.2 (hcovered_def ▸ Finset.mem_biUnion.mpr ⟨u, hu, hub⟩)
      have hv_inter_empty : ∀ u ∈ s, (u.1 ∩ v.1) = ∅ := by
        intro u hu
        have hv1 : v.1 = {a, b} := rfl
        have : ∀ x, x ∈ u.1 ∩ v.1 → False := by
          intro x hx
          simp [hv1, Finset.mem_inter] at hx
          rcases hx.2 with rfl | rfl
          · exact ha_notin u hu hx.1
          · exact hb_notin u hu hx.1
        exact Finset.not_nonempty_iff_eq_empty.mp (by rintro ⟨x, hx⟩; exact this x hx)
      have huv_ne : ∀ u ∈ s, u ≠ v := by
        intro u hu huv_eq
        have := congrArg Subtype.val huv_eq
        simp [v] at this
        have ha_in_u : a ∈ u.1 := by rw [this]; simp
        exact Finset.mem_sdiff.mp ha |>.2 (hcovered_def ▸ Finset.mem_biUnion.mpr ⟨u, hu, ha_in_u⟩)
      have hv_not_adj : ∀ u ∈ s, ¬(CGraph.johnson (n + 2) (2 : ℕ)).Adj u v := by
        intro u hu
        simp [CGraph.johnson_adj, huv_ne u hu, hv_inter_empty u hu]
      have hv_not_dom : ¬(v ∈ s ∨ ∃ u ∈ s, (CGraph.johnson (n + 2) (2 : ℕ)).Adj u v) := by
        intro h
        rcases h with hv | ⟨u, hu, hadj⟩
        · exact hv_notin hv
        · exact absurd hadj (hv_not_adj u hu)
      exact hv_not_dom (hsdom v)
    apply le_csInf
    · exact ⟨Fintype.card _, ⟨Finset.univ, rfl, CGraph.isDominatingSet_univ _⟩⟩
    · intro a ⟨s, hs, hsdom⟩; rw [← hs]; exact hlower s hsdom

@[simp] theorem domNum_johnson_two (n : ℕ) : (johnson (n + 2) 2).domNum = (n + 2) / 2 :=
  domNum_triangular n

/-- **A Cartesian product of two triangle-free graphs with an edge each has girth four**: the
two edges span a square, and a triangle in the product would project to one in a factor. -/
theorem girth_cartesianProduct_of_cliqueNum_le_two {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E)
    (hcG : G.cliqueNum ≤ 2) (hcH : H.cliqueNum ≤ 2) : (G □g H).girth = 4 := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [cartesianProduct_mk, girth_mk]
  rw [E_mk] at hG hH
  rw [cliqueNum_mk] at hcG hcH
  exact CGraph.girth_cartesianProduct_of_cliqueNum_le_two hG hH hcG hcH

/-- **A prism over a cycle of length at least four has girth four**, the odd case included:
the square faces are the shortest cycles. -/
@[simp] theorem girth_prism (n : ℕ) : (prism (n + 4)).girth = 4 := by
  refine girth_cartesianProduct_of_cliqueNum_le_two ?_ (by simp) (by rw [cliqueNum_cycle]) (by simp)
  rw [show n + 4 = n + 1 + 3 by ring, E_cycle]
  omega

/-- **A torus is a product of two cycles**, and has girth four once both are long enough. -/
@[simp] theorem girth_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 4) □g cycle (n + 4)).girth = 4 := by
  refine girth_cartesianProduct_of_cliqueNum_le_two ?_ ?_ (by rw [cliqueNum_cycle])
    (by rw [cliqueNum_cycle]) <;>
  · rw [show _ + 4 = _ + 1 + 3 from rfl, E_cycle]
    omega

/-- A cycle crossed with a path: the girth is four whichever parity the cycle has. -/
@[simp] theorem girth_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 4) □g path (n + 2)).girth = 4 := by
  refine girth_cartesianProduct_of_cliqueNum_le_two ?_ (by simp) (by rw [cliqueNum_cycle])
    (by rw [cliqueNum_path])
  rw [show m + 4 = m + 1 + 3 by ring, E_cycle]
  omega

/-- **A grid has girth four.** -/
@[simp] theorem girth_grid (m n : ℕ) :
    (path (m + 2) □g path (n + 2)).girth = 4 :=
  girth_cartesianProduct (by simp) (by simp) (isBipartite_path (m + 2)) (isBipartite_path (n + 2))

/-- The Johnson graph has a triangle, so a clique of size three. -/
theorem three_le_cliqueNum_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    3 ≤ (johnson n k).cliqueNum :=
  girth_eq_three_iff.1 (girth_johnson hk h)

theorem three_le_chromNum_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    3 ≤ (johnson n k).chromNum :=
  (three_le_cliqueNum_johnson hk h).trans (cliqueNum_le_chromNum _)

theorem not_isAcyclic_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    ¬ IsAcyclic (johnson n k) :=
  not_isAcyclic_of_girth_pos (by rw [girth_johnson hk h]; omega)

theorem not_isTree_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) : ¬ IsTree (johnson n k) :=
  not_isTree_of_girth_pos (by rw [girth_johnson hk h]; omega)
/-- **Four codewords dominate the four-cube**: the sphere-covering bound needs at least four,
and four suffice. -/
theorem domNum_hypercube_four : (hypercube 4).domNum = 4 := by
  apply Nat.le_antisymm
  · -- Upper bound: exhibit a dominating set of size 4
    let c0 : (CGraph.hypercube 4).V := fun _ => false
    let c1 : (CGraph.hypercube 4).V := fun i => (i = 3)
    let c2 : (CGraph.hypercube 4).V := fun i => (i ≠ 3)
    let c3 : (CGraph.hypercube 4).V := fun _ => true
    let S : Finset (CGraph.hypercube 4).V :=
      (insert c0 (insert c1 (insert c2 (singleton c3))))
    have hdom : (CGraph.hypercube 4).IsDominatingSet S := by
      intro v
      revert v
      decide
    have hcard : S.card = 4 := by decide
    show CGraph.domNum (CGraph.hypercube 4) ≤ 4
    exact le_trans (CGraph.domNum_le_card_of_isDominatingSet hdom) hcard.le
  · -- Lower bound: 16 ≤ domNum * 5
    show 4 ≤ (hypercube 4).domNum
    simp only [hypercube, domNum_mk]
    have hcard : Fintype.card (CGraph.hypercube 4).V = 16 := by decide
    have hdeg : CGraph.maxDeg (CGraph.hypercube 4) ≤ 4 := by
      apply CGraph.maxDeg_le_of_forall
      intro v
      show (CGraph.hypercube 4).toSimple.degree v ≤ 4
      revert v; native_decide
    have hbound : 16 ≤ CGraph.domNum (CGraph.hypercube 4) *
        (CGraph.maxDeg (CGraph.hypercube 4) + 1) := by
      rw [← hcard]
      apply CGraph.card_le_domNum_mul_maxDeg_add_one
    nlinarith

theorem three_le_cliqueNum_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    3 ≤ (kneser n k).cliqueNum :=
  girth_eq_three_iff.1 (girth_kneser hk h)

theorem three_le_chromNum_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    3 ≤ (kneser n k).chromNum :=
  (three_le_cliqueNum_kneser hk h).trans (cliqueNum_le_chromNum _)

theorem not_isAcyclic_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    ¬ IsAcyclic (kneser n k) :=
  not_isAcyclic_of_girth_pos (by rw [girth_kneser hk h]; omega)

theorem not_isTree_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) : ¬ IsTree (kneser n k) :=
  not_isTree_of_girth_pos (by rw [girth_kneser hk h]; omega)
/-! ### Which named families are trees -/

@[simp] theorem not_isTree_book (n : ℕ) : ¬ IsTree (book (n + 1)) :=
  not_isTree_of_girth_pos (by rw [girth_book]; omega)

@[simp] theorem not_isTree_cocktailParty (n : ℕ) : ¬ IsTree (cocktailParty (n + 3)) :=
  not_isTree_of_girth_pos (by rw [girth_cocktailParty]; omega)

@[simp] theorem not_isTree_triangular (n : ℕ) : ¬ IsTree (triangular (n + 4)) :=
  not_isTree_of_girth_pos (by rw [girth_triangular]; omega)

theorem not_isTree_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : 3 ≤ max m n) :
    ¬ IsTree (rook m n) :=
  not_isTree_of_girth_pos (by rw [girth_rook hm hn h]; omega)

@[simp] theorem not_isTree_completeMultipartite_replicate (m d : ℕ) :
    ¬ IsTree (completeMultipartite (List.replicate (m + 3) (d + 1))) :=
  not_isTree_of_girth_pos (by rw [girth_completeMultipartite_replicate]; omega)

theorem not_isTree_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    ¬ IsTree (paley q) :=
  not_isTree_of_girth_pos (by rw [girth_paley q hq hq9]; omega)

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

@[simp] theorem isAcyclic_star (n : ℕ) : IsAcyclic (star n) :=
  ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_star n)).2

/-! ### Circulants -/

/-- The edge count of a circulant, from its regularity. -/
theorem E_circulant (n : ℕ) (S : List ℕ) (hn : 0 < n) :
    (circulant n S).E = n * (circulant n S).minDeg / 2 := by
  rw [← two_mul_E_circulant n S hn]
  omega

theorem diameter_circulant (n : ℕ) (S : List ℕ) :
    (circulant n S).diameter = (circulant n S).radius := (radius_circulant n S).symm

/-! ### Balanced complete multipartite graphs -/

/-- A balanced complete multipartite graph is regular: every vertex misses exactly its own
part. -/
@[simp] theorem isRegularWith_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m d)).IsRegularWith ((m - 1) * d) := by
  rw [completeMultipartite_replicate]
  simpa using (isRegularWith_complete m).lexProduct (isRegularWith_empty d)

@[simp] theorem isVertexTransitive_completeMultipartite_replicate (m d : ℕ) :
    IsVertexTransitive (completeMultipartite (List.replicate m d)) := by
  rw [completeMultipartite_replicate]
  exact (isVertexTransitive_complete m).lexProduct (isVertexTransitive_empty d)

/-! ### Domination in Kneser graphs -/

/-- **Three pairs dominate a Kneser graph on at least five points**: `{0,1}`, `{1,2}` and
`{0,2}` between them meet or miss every pair. -/
theorem domNum_kneser_two (n : ℕ) : (kneser (n + 5) 2).domNum = 3 := by
  have h01 : (0 : Fin (n + 5)) ≠ 1 := by
    intro h; have := Fin.ext_iff.mp h; simp at this
  have h02 : (0 : Fin (n + 5)) ≠ 2 := by
    intro h; have := Fin.ext_iff.mp h; simp [Nat.mod_eq_of_lt (by omega : 2 < n + 5)] at this
  have h12 : (1 : Fin (n + 5)) ≠ 2 := by
    intro h; have := Fin.ext_iff.mp h; simp [Nat.mod_eq_of_lt (by omega : 2 < n + 5)] at this
  have key_dom : ∀ (t : Finset (Fin (n + 5))), t.card = 2 →
      (t = {0, 1} ∨ t = {1, 2} ∨ t = {0, 2} ∨
       t ∩ {0, 1} = ∅ ∨ t ∩ {1, 2} = ∅ ∨ t ∩ {0, 2} = ∅) := by
    intro t ht
    by_contra h
    push_neg at h
    -- h : t ≠ {0,1} ∧ t ≠ {1,2} ∧ t ≠ {0,2} ∧ t ∩ {0,1} ≠ ∅ ∧ t ∩ {1,2} ≠ ∅ ∧ t ∩ {0,2} ≠ ∅
    obtain ⟨hne01, hne12, hne02, hint01, hint12, hint02⟩ := h
    -- Each nonzero intersection gives an element of t in the corresponding pair.
    have hint01' : (t ∩ {0, 1} : Finset (Fin (n+5))) ≠ ∅ := by
      exact Finset.Nonempty.ne_empty ‹_›
    have hint12' : (t ∩ {1, 2} : Finset (Fin (n+5))) ≠ ∅ := by
      exact Finset.Nonempty.ne_empty ‹_›
    have hint02' : (t ∩ {0, 2} : Finset (Fin (n+5))) ≠ ∅ := by
      exact Finset.Nonempty.ne_empty ‹_›
    have h0 : (0 : Fin (n+5)) ∈ t ∨ 1 ∈ t := by
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hint01'
      simp at hx
      rcases hx with ⟨hxt, rfl | rfl⟩ <;> tauto
    have h1 : (1 : Fin (n+5)) ∈ t ∨ 2 ∈ t := by
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hint12'
      simp at hx
      rcases hx with ⟨hxt, rfl | rfl⟩ <;> tauto
    have h2 : (0 : Fin (n+5)) ∈ t ∨ 2 ∈ t := by
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hint02'
      simp at hx
      rcases hx with ⟨hxt, rfl | rfl⟩ <;> tauto
    have eq_pair_of_mem : ∀ (a b : Fin (n+5)), a ≠ b → a ∈ t → b ∈ t → t = {a, b} := by
      intro a b hab ha hb
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        by_contra hxne
        have hextra : ({a, b, x} : Finset (Fin (n+5))) ⊆ t := by
          intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hextra
        have hcard3 : ({a, b, x} : Finset (Fin (n+5))).card = 3 := by
          have hax : a ≠ x := by intro h; exact hxne (h ▸ Finset.mem_insert_self _ _)
          have hbx : b ≠ x := by
            intro h
            exact hxne (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
          · simp
          · exact fun h => hbx (Finset.mem_singleton.mp h)
          · intro h; rcases Finset.mem_insert.mp h with rfl | h; exact absurd rfl hab; exact hax
              (Finset.mem_singleton.mp h)
        omega
      · rw [ht, Finset.card_pair hab]
    have hcard012 : ({0, 1, 2} : Finset (Fin (n+5))).card = 3 := by
      simp [Finset.card_insert_of_notMem, h01, h02, h12]
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hne01 (eq_pair_of_mem 0 1 h01 h0 h1)
    · have : ({0,1,2} : Finset (Fin (n+5))) ⊆ t := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
      have hcard := Finset.card_le_card this
      rw [hcard012, ht] at hcard; omega
    · exact hne02 (eq_pair_of_mem 0 2 h02 h0 h1)
    · exact hne02 (eq_pair_of_mem 0 2 h02 h0 h2)
    · have := eq_pair_of_mem 1 0 h01.symm h0 h2
      exact hne01 (this.trans (Finset.pair_comm _ _))
    · exact hne12 (eq_pair_of_mem 1 2 h12 h0 h2)
    · have : ({0,1,2} : Finset (Fin (n+5))) ⊆ t := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> [exact h2; exact h0; exact h1]
      have hcard := Finset.card_le_card this
      rw [hcard012, ht] at hcard; omega
    · exact hne12 (eq_pair_of_mem 1 2 h12 h0 h2)
  rw [kneser, IsoGraph.domNum_mk]
  have hcard01 : ({0, 1} : Finset (Fin (n + 5))).card = 2 := Finset.card_pair h01
  have hcard12 : ({1, 2} : Finset (Fin (n + 5))).card = 2 := Finset.card_pair h12
  have hcard02 : ({0, 2} : Finset (Fin (n + 5))).card = 2 := Finset.card_pair h02
  let v01 : (CGraph.kneser (n + 5) 2).V := ⟨{0, 1}, hcard01⟩
  let v12 : (CGraph.kneser (n + 5) 2).V := ⟨{1, 2}, hcard12⟩
  let v02 : (CGraph.kneser (n + 5) 2).V := ⟨{0, 2}, hcard02⟩
  let s : Finset (CGraph.kneser (n + 5) 2).V := {v01, v12, v02}
  have hd01_12 : ({0, 1} : Finset (Fin (n + 5))) ≠ {1, 2} := by
    intro h; have := Finset.ext_iff.mp h 0; simp at this; exact h02 this
  have hd01_02 : ({0, 1} : Finset (Fin (n + 5))) ≠ {0, 2} := by
    intro h; have := Finset.ext_iff.mp h 2; simp at this; rcases this with h' | h' <;> [exact absurd
      h' h02.symm; exact absurd h' h12.symm]
  have hd12_02 : ({1, 2} : Finset (Fin (n + 5))) ≠ {0, 2} := by
    intro h; have := Finset.ext_iff.mp h 1; simp at this; exact h12 this
  have hne01_12 : v01 ≠ v12 := fun h => hd01_12 (Subtype.ext_iff.mp h)
  have hne01_02 : v01 ≠ v02 := fun h => hd01_02 (Subtype.ext_iff.mp h)
  have hne12_02 : v12 ≠ v02 := fun h => hd12_02 (Subtype.ext_iff.mp h)
  have hcard_s : s.card = 3 := by
    show Finset.card ({v01, v12, v02} : Finset _) = 3
    rw [show ({v01, v12, v02} : Finset _) = insert v01 (insert v12 (insert v02 ∅)) from rfl]
    have hv02_not_empty : v02 ∉ (∅ : Finset (CGraph.kneser (n + 5) 2).V) := Finset.notMem_empty v02
    have hv12_not_in_v02 : v12 ∉ insert v02 (∅ : Finset _) := by
      simp [hne12_02]
    have hv01_not_in_v12_v02 : v01 ∉ insert v12 (insert v02 (∅ : Finset _)) := by
      simp [Finset.mem_insert, hne01_12, hne01_02]
    rw [Finset.card_insert_of_notMem hv01_not_in_v12_v02,
        Finset.card_insert_of_notMem hv12_not_in_v02,
        Finset.card_insert_of_notMem hv02_not_empty,
        Finset.card_empty]
  have hdom_s : (CGraph.kneser (n + 5) 2).IsDominatingSet s := by
    unfold CGraph.IsDominatingSet
    intro ⟨t, ht⟩
    by_cases hmem : ⟨t, ht⟩ = v01 ∨ ⟨t, ht⟩ = v12 ∨ ⟨t, ht⟩ = v02
    · rcases hmem with h | h | h
      · rw [h]; simp [s]
      · rw [h]; simp [s]
      · rw [h]; simp [s]
    · push_neg at hmem
      rcases key_dom t ht with h | h | h | h | h | h
      · exact False.elim (hmem.1 (by subst h; rfl))
      · exact False.elim (hmem.2.1 (by subst h; rfl))
      · exact False.elim (hmem.2.2 (by subst h; rfl))
      · right; exact ⟨v01, Finset.mem_insert_self _ _, by
          rw [CGraph.kneser_adj]
          simp [decide_eq_true_eq]
          dsimp [v01]
          exact ⟨hmem.1.symm, h.symm ▸ Eq.symm (Finset.inter_comm t {0, 1})⟩⟩
      · right; exact ⟨v12, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by
          rw [CGraph.kneser_adj]
          simp [decide_eq_true_eq]
          dsimp [v12]
          exact ⟨hmem.2.1.symm, h.symm ▸ Eq.symm (Finset.inter_comm t {1, 2})⟩⟩
      · right; exact ⟨v02, show v02 ∈ s from by simp [s], by
          rw [CGraph.kneser_adj]
          simp [decide_eq_true_eq]
          dsimp [v02]
          exact ⟨hmem.2.2.symm, h.symm ▸ Eq.symm (Finset.inter_comm t {0, 2})⟩⟩
  have hupp : (CGraph.kneser (n + 5) 2).domNum ≤ 3 :=
    le_trans (CGraph.domNum_le_card_of_isDominatingSet hdom_s) (by rw [hcard_s])
  -- Lower bound: domNum ≥ 3
  have hlow : 3 ≤ (CGraph.kneser (n + 5) 2).domNum := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨s, hs_card, hs_dom⟩ := CGraph.exists_isDominatingSet_domNum (CGraph.kneser (n + 5) 2)
    have hscard : s.card ≤ 2 := by linarith
    unfold CGraph.IsDominatingSet at hs_dom
    have hn5 : 5 ≤ n + 5 := by omega
    -- All elements appearing in vertices of s
    set E := s.biUnion (fun u : (CGraph.kneser (n + 5) 2).V => u.val) with hE_def
    have hE_card : E.card ≤ 4 := by
      calc E.card ≤ ∑ u ∈ s, u.val.card := Finset.card_biUnion_le
        _ = s.card * 2 := by
            rw [Finset.sum_congr rfl (fun u hu => u.2), Finset.sum_const, smul_eq_mul]
        _ ≤ 2 * 2 := by gcongr
        _ = 4 := by norm_num
    have hE_lt : E.card < Fintype.card (Fin (n + 5)) := by
      rw [Fintype.card_fin]; omega
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin (n + 5), x₀ ∉ E := by
      by_contra hx₀; push_neg at hx₀
      have : E = Finset.univ := Finset.eq_univ_of_forall hx₀
      rw [this, Finset.card_univ, Fintype.card_fin] at hE_card; omega
    have hx₀_not_in : ∀ u ∈ s, x₀ ∉ u.val := by
      intro u hu hmem; exact hx₀ (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
    interval_cases hscard2 : s.card
    · -- card = 0
      have hs_empty : s = ∅ := Finset.card_eq_zero.mp hscard2; subst hs_empty
      exact absurd (hs_dom v01) (by simp)
    · -- card = 1
      obtain ⟨u, hu⟩ : ∃ u : (CGraph.kneser (n + 5) 2).V, s = {u} := by
        rw [Finset.card_eq_one] at hscard2; exact hscard2
      subst hu
      have hu_ne_zero : u.val ≠ ∅ := by intro h; have := u.2; simp [h] at this
      obtain ⟨a, ha⟩ : ∃ a, a ∈ u.val := Finset.nonempty_iff_ne_empty.mpr hu_ne_zero
      obtain ⟨c, hc⟩ : ∃ c : Fin (n + 5), c ∉ u.val := by
        by_contra hc; push_neg at hc
        have huniv : u.val = Finset.univ := Finset.eq_univ_of_forall hc
        have := u.2
        rw [huniv, Finset.card_univ, Fintype.card_fin] at this
        omega
      have hac : a ≠ c := by intro h; exact hc (h ▸ ha)
      let tval : Finset (Fin (n + 5)) := {a, c}
      have htval_card : tval.card = 2 := Finset.card_pair hac
      let t : (CGraph.kneser (n + 5) 2).V := ⟨tval, htval_card⟩
      have ht_ne_u : t ≠ u := by
        intro h
        have h1 := Subtype.ext_iff.mp h
        exact hc (h1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have ht_not_mem : t ∉ ({u} : Finset _) := by simp [ht_ne_u]
      have ht_not_adj_u : ¬(CGraph.kneser (n + 5) 2).Adj u t := by
        rw [CGraph.kneser_adj]
        have h_mem : a ∈ u.val ∩ tval := Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self _ _⟩
        by_contra h_adj
        simp at h_adj
        exact Finset.notMem_empty a (h_adj.2 ▸ h_mem)
      have hdom_t := hs_dom t
      rcases hdom_t with h | ⟨u_1, hu_1, hadj⟩
      · exact ht_not_mem h
      · simp [Finset.mem_singleton] at hu_1
        subst hu_1
        exact ht_not_adj_u hadj
    · -- card = 2
      obtain ⟨u, v, huv, hs_eq⟩ : ∃ u v : (CGraph.kneser (n + 5) 2).V, u ≠ v ∧ s = {u, v} := by
        rw [Finset.card_eq_two] at hscard2; exact hscard2
      subst hs_eq
      by_cases hint_empty : (u.val ∩ v.val : Finset (Fin (n + 5))) = ∅
      · -- Disjoint case
        obtain ⟨a, ha⟩ : ∃ a, a ∈ u.val := Finset.card_pos.mp (by rw [u.2]; omega)
        obtain ⟨b, hb⟩ : ∃ b, b ∈ v.val := Finset.card_pos.mp (by rw [v.2]; omega)
        have hab_ne : a ≠ b := by
          intro h
          exact Finset.notMem_empty a (hint_empty ▸ Finset.mem_inter.mpr ⟨ha, h ▸ hb⟩)
        let tval : Finset (Fin (n + 5)) := {a, b}
        have htval_card : tval.card = 2 := Finset.card_pair hab_ne
        let t : (CGraph.kneser (n + 5) 2).V := ⟨tval, htval_card⟩
        have ha_not_in_v : a ∉ v.val := by
          intro h
          exact Finset.notMem_empty a (hint_empty ▸ Finset.mem_inter.mpr ⟨ha, h⟩)
        have hb_not_in_u : b ∉ u.val := by
          intro h
          exact Finset.notMem_empty b (hint_empty ▸ Finset.mem_inter.mpr ⟨h, hb⟩)
        have ht_ne_u : t ≠ u := by
          intro h
          have h1 := Subtype.ext_iff.mp h
          have : b ∈ u.val := by
            rw [← h1]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          exact hb_not_in_u this
        have ht_ne_v : t ≠ v := by
          intro h
          have h1 := Subtype.ext_iff.mp h
          have : a ∈ v.val := by rw [← h1]; exact Finset.mem_insert_self _ _
          exact ha_not_in_v this
        have ht_not_mem : t ∉ ({u, v} : Finset _) := by simp [ht_ne_u, ht_ne_v]
        have ht_not_adj_u : ¬(CGraph.kneser (n + 5) 2).Adj u t := by
          rw [CGraph.kneser_adj]
          have h_mem : a ∈ u.val ∩ t.val := Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self _ _⟩
          by_contra h_adj
          simp at h_adj
          exact Finset.notMem_empty a (h_adj.2 ▸ h_mem)
        have ht_not_adj_v : ¬(CGraph.kneser (n + 5) 2).Adj v t := by
          rw [CGraph.kneser_adj]
          have h_mem : b ∈ v.val ∩ t.val := Finset.mem_inter.mpr ⟨hb, Finset.mem_insert_of_mem
            (Finset.mem_singleton_self _)⟩
          by_contra h_adj
          simp at h_adj
          exact Finset.notMem_empty b (h_adj.2 ▸ h_mem)
        have hcontradiction := hs_dom t
        rcases hcontradiction with h | ⟨w, hw, hadj⟩
        · exact ht_not_mem h
        · simp [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> [exact ht_not_adj_u hadj; exact ht_not_adj_v hadj]
      · -- Non-disjoint case
        obtain ⟨a, ha⟩ : ∃ a, a ∈ (u.val ∩ v.val : Finset (Fin (n + 5))) :=
          Finset.nonempty_iff_ne_empty.mpr hint_empty
        have ha_u : a ∈ u.val := Finset.mem_inter.mp ha |>.1
        have ha_v : a ∈ v.val := Finset.mem_inter.mp ha |>.2
        have hdiff_u : (u.val \ v.val : Finset (Fin (n + 5))).Nonempty := by
          by_contra hd; push_neg at hd
          have hsub : u.val ⊆ v.val := Finset.sdiff_eq_empty_iff_subset.mp hd
          have := Finset.card_le_card hsub
          rw [u.2, v.2] at this
          have : u.val = v.val := Finset.eq_of_subset_of_card_le hsub (by rw [u.2, v.2])
          exact huv (Subtype.ext this)
        obtain ⟨b, hb⟩ := hdiff_u
        have hb_u : b ∈ u.val := Finset.mem_sdiff.mp hb |>.1
        have hb_nv : b ∉ v.val := Finset.mem_sdiff.mp hb |>.2
        have hdiff_v : (v.val \ u.val : Finset (Fin (n + 5))).Nonempty := by
          by_contra hd; push_neg at hd
          have hsub : v.val ⊆ u.val := Finset.sdiff_eq_empty_iff_subset.mp hd
          have := Finset.card_le_card hsub
          rw [v.2, u.2] at this
          have : v.val = u.val := Finset.eq_of_subset_of_card_le hsub (by rw [v.2, u.2])
          exact huv.symm (Subtype.ext this)
        obtain ⟨c, hc⟩ := hdiff_v
        have hc_v : c ∈ v.val := Finset.mem_sdiff.mp hc |>.1
        have hc_nu : c ∉ u.val := Finset.mem_sdiff.mp hc |>.2
        have hb_ne_c : b ≠ c := by intro h; exact hc_nu (h ▸ hb_u)
        let tval : Finset (Fin (n + 5)) := {b, c}
        have htval_card : tval.card = 2 := Finset.card_pair hb_ne_c
        let t : (CGraph.kneser (n + 5) 2).V := ⟨tval, htval_card⟩
        have ht_ne_u : t ≠ u := by
          intro h; have := Subtype.ext_iff.mp h
          exact hc_nu (this ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have ht_ne_v : t ≠ v := by
          intro h; have := Subtype.ext_iff.mp h
          exact hb_nv (this ▸ Finset.mem_insert_self _ _)
        have ht_not_mem : t ∉ ({u, v} : Finset _) := by simp [ht_ne_u, ht_ne_v]
        have ht_not_adj_u : ¬(CGraph.kneser (n + 5) 2).Adj u t := by
          rw [CGraph.kneser_adj]
          have h_mem : b ∈ u.val ∩ t.val := Finset.mem_inter.mpr ⟨hb_u, Finset.mem_insert_self _ _⟩
          by_contra h_adj
          simp at h_adj
          exact Finset.notMem_empty b (h_adj.2 ▸ h_mem)
        have ht_not_adj_v : ¬(CGraph.kneser (n + 5) 2).Adj v t := by
          rw [CGraph.kneser_adj]
          have h_mem : c ∈ v.val ∩ t.val := Finset.mem_inter.mpr ⟨hc_v, Finset.mem_insert_of_mem
            (Finset.mem_singleton_self _)⟩
          by_contra h_adj
          simp at h_adj
          exact Finset.notMem_empty c (h_adj.2 ▸ h_mem)
        have hcontradiction := hs_dom t
        rcases hcontradiction with h | ⟨w, hw, hadj⟩
        · exact ht_not_mem h
        · simp [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> [exact ht_not_adj_u hadj; exact ht_not_adj_v hadj]
  exact le_antisymm hupp hlow
/-- **A fan has a near-perfect matching**: pair the hub with one end of the path and match
the rest of the path in pairs. -/
@[simp] theorem matchNum_fan (n : ℕ) : (fan (n + 1)).matchNum = (n + 2) / 2 := by
  apply le_antisymm
  · have h1 := (fan (n + 1)).two_mul_matchNum_le_V
    rw [V_fan] at h1
    omega
  · -- Lower bound: exhibit a matching of size (n+2)/2 in fan (n+1)
    rw [matchNum_eq]
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have join_mk : ∀ (G H : CGraph),
          IsoGraph.join ⟦G⟧ ⟦H⟧ = ⟦CGraph.join G H⟧ := by
        intro G H
        rw [IsoGraph.join, compl_mk, compl_mk, disjUnion_mk, compl_mk]
        rfl
      have hconvert : (fan (2 * k + 1)).lineGraph.indepNum =
          (CGraph.join (CGraph.complete 1) (CGraph.path (2 * k + 1))).lineGraph.indepNum := by
        rw [fan_eq_join, IsoGraph.complete, IsoGraph.path, join_mk, lineGraph_mk, indepNum_mk]
      rw [hconvert]
      have harith : (2 * k + 2) / 2 = k + 1 := by omega
      rw [harith]
      -- Lower bound: exhibit k+1 pairwise disjoint edges in fan (2*k+1) = join K1 P(2k+1)
      -- Edge set of CGraph.join (complete 1) (path (2*k+1)):
      --   - spoke edges: (inl 0, inr j) for all j : Fin (2*k+1)
      --   - path edges: (inr i, inr (i+1)) for i : Fin (2*k)
      -- Matching: spoke to 0, plus path edges (2i-1, 2i) for i=1..k, i.e.,
      -- (1,2),(3,4),...,(2k-1,2k)
      set m : ℕ := 2 * k + 1
      -- spoke edge: {inl 0, inr ⟨0, by omega⟩}
      let e0 : Sym2 (Fin 1 ⊕ Fin m) := Sym2.mk (Sum.inl ⟨0, by omega⟩, Sum.inr ⟨0, by omega⟩)
      -- path edges for j : Fin k: {inr ⟨2*j+1, ...⟩, inr ⟨2*j+2, ...⟩}
      let epath : Fin k → Sym2 (Fin 1 ⊕ Fin m) :=
        fun j => Sym2.mk (Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩, Sum.inr ⟨2 * (j : ℕ) + 2, by omega⟩)
      -- Show e0 is an edge
      have he0 : e0 ∈ (CGraph.join (CGraph.complete 1) (CGraph.path m)).toSimple.edgeSet := by
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.join_adj_inl_inr]
      -- Show each epath j is an edge
      have hepath : ∀ j : Fin k, epath j ∈ (CGraph.join (CGraph.complete 1) (CGraph.path
        m)).toSimple.edgeSet := by
        intro j
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.join_adj_inr_inr, CGraph.path_adj]
        simp [Fin.ext_iff]
      let spokeV : (CGraph.lineGraph (CGraph.join (CGraph.complete 1) (CGraph.path m))).V :=
        ⟨e0, he0⟩
      let rimV : Fin k → (CGraph.lineGraph (CGraph.join (CGraph.complete 1) (CGraph.path m))).V :=
        fun j => ⟨epath j, hepath j⟩
      -- inl 0 is in e0 but not in any epath j
      have hinl0_in_e0 : (Sum.inl ⟨0, by omega⟩ : Fin 1 ⊕ Fin m) ∈ e0 := by
        simp [e0]
      have hinl0_not_in_epath : ∀ j : Fin k, (Sum.inl ⟨0, by omega⟩ : Fin 1 ⊕ Fin m) ∉ epath j := by
        intro j; simp [epath]
      -- spokeV ≠ rimV j (spoke has inl, rim doesn't)
      have hspoke_ne_rim : ∀ j : Fin k, spokeV ≠ rimV j := by
        intro j heq
        have hval : e0 = epath j := Subtype.ext_iff.mp heq
        have := hinl0_in_e0
        rw [hval] at this
        exact hinl0_not_in_epath j this
      -- rim edge membership char
      have hmemRim_char : ∀ j : Fin k, ∀ y : Fin 1 ⊕ Fin m,
          y ∈ epath j ↔ y = Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩ ∨ y = Sum.inr
            ⟨2 * (j : ℕ) + 2, by omega⟩ := by
        intro j y; simp [epath]
      -- vertices in e0: only inl 0 and inr 0
      have hin0_in_e0 : (Sum.inr ⟨0, by omega⟩ : Fin 1 ⊕ Fin m) ∈ e0 := by
        simp [e0]
      have hin0_not_in_epath : ∀ j : Fin k, (Sum.inr ⟨0, by omega⟩ : Fin 1 ⊕ Fin m) ∉ epath j := by
        intro j; simp [epath]
      -- Any vertex in e0 is not in any epath j
      have hnot_in_epath_of_in_e0 : ∀ (v : Fin 1 ⊕ Fin m) (j : Fin k), v ∈ e0 → v ∉ epath j := by
        intro v j hv hv'
        simp [e0] at hv
        rcases hv with rfl | rfl
        · exact hinl0_not_in_epath j hv'
        · exact hin0_not_in_epath j hv'
      -- spokeV ≠ rimV j (alternative proof using vertex membership)
      -- (already have hspoke_ne_rim above, keep it)
      -- vertices in epath j characterised
      -- rimV is injective
      have hrim_inj : Function.Injective rimV := by
        intro j j' hj
        have hval : epath j = epath j' := Subtype.ext_iff.mp hj
        -- inr ⟨2*j+1, ...⟩ ∈ epath j, so ∈ epath j', so by hmemRim_char, 2*j+1 = 2*j'+1 or 2*j+1 =
        -- 2*j'+2
        have hm1 : (Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩ : Fin 1 ⊕ Fin m) ∈ epath j := by
          simp [epath]
        rw [hval] at hm1
        rcases hmemRim_char j' _ |>.mp hm1 with h | h <;> simp [Fin.ext_iff] at h <;> omega
      -- vertices finset
      let vertices : Finset (CGraph.lineGraph (CGraph.join (CGraph.complete 1) (CGraph.path m))).V
        :=
        {spokeV} ∪ Finset.univ.image rimV
      -- Independence
      have hindependent : SimpleGraph.IsIndepSet (CGraph.lineGraph (CGraph.join (CGraph.complete 1)
        (CGraph.path m))).toSimple
          (vertices : Set _) := by
        unfold SimpleGraph.IsIndepSet
        intro v hv w hw hvw
        have hv' : v = spokeV ∨ ∃ j : Fin k, rimV j = v := by
          simp [vertices] at hv; exact hv
        have hw' : w = spokeV ∨ ∃ j : Fin k, rimV j = w := by
          simp [vertices] at hw; exact hw
        rcases hv' with rfl | ⟨j, rfl⟩
        · rcases hw' with rfl | ⟨j', rfl⟩
          · exact absurd rfl hvw
          · intro h
            simp [CGraph.toSimple] at h
            obtain ⟨_, ⟨v, hv1, hv2⟩⟩ := h
            exact hnot_in_epath_of_in_e0 v j' hv1 hv2
        · rcases hw' with rfl | ⟨j', rfl⟩
          · intro h
            simp [CGraph.toSimple] at h
            obtain ⟨_, ⟨v, hv1, hv2⟩⟩ := h
            exact hnot_in_epath_of_in_e0 v j hv2 hv1
          · by_cases heq : j = j'
            · subst heq; simp at hvw
            · intro h
              simp [CGraph.lineGraph_adj] at h
              -- epath j and epath j' share a vertex, but they shouldn't when j≠j'
              obtain ⟨_, ⟨v, hv1, hv2⟩⟩ := h
              simp only [rimV] at hv1 hv2
              rw [hmemRim_char j] at hv1
              rw [hmemRim_char j'] at hv2
              rcases hv1 with h|h <;> rcases hv2 with h'|h' <;> (
                subst h; simp at h'
                omega)
      -- Cardinality
      have hcard : vertices.card = k + 1 := by
        simp only [vertices]
        have hdisj : Disjoint {spokeV} (Finset.univ.image rimV) := by
          rw [Finset.disjoint_singleton_left]
          intro hv
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
          exact hspoke_ne_rim j (hj.symm)
        rw [Finset.card_union_of_disjoint hdisj]
        simp [Finset.card_singleton]
        rw [Finset.card_image_of_injective _ hrim_inj]
        simp
        omega
      exact hcard ▸ SimpleGraph.IsIndepSet.card_le_indepNum hindependent
    · -- Odd case: n = 2*k+1, fan(n+1) = fan(2*k+2)
      have hconvert : (fan (2 * k + 1 + 1)).lineGraph.indepNum =
          (CGraph.join (CGraph.complete 1) (CGraph.path (2 * k + 2))).lineGraph.indepNum := by
        rw [fan_eq_join, IsoGraph.complete, IsoGraph.path, join_mk, lineGraph_mk, indepNum_mk]
      rw [hconvert]
      have harith : (2 * k + 1 + 2) / 2 = k + 1 := by omega
      rw [harith]
      set m : ℕ := 2 * k + 2
      -- path edges for j : Fin (k+1): {inr ⟨2*j, ...⟩, inr ⟨2*j+1, ...⟩}
      let epath : Fin (k + 1) → Sym2 (Fin 1 ⊕ Fin m) :=
        fun j => Sym2.mk (Sum.inr ⟨2 * (j : ℕ), by omega⟩, Sum.inr ⟨2 * (j : ℕ) + 1, by omega⟩)
      -- Show each epath j is an edge (rim-rim, path edges)
      have hepath : ∀ j : Fin (k + 1), epath j ∈ (CGraph.join (CGraph.complete 1) (CGraph.path
        m)).toSimple.edgeSet := by
        intro j
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.join_adj_inr_inr, CGraph.path_adj]
        simp [Fin.ext_iff]
      let rimV : Fin (k + 1) → (CGraph.lineGraph (CGraph.join (CGraph.complete 1) (CGraph.path
        m))).V :=
        fun j => ⟨epath j, hepath j⟩
      -- rim edge membership char
      have hmemRim_char : ∀ j : Fin (k + 1), ∀ y : Fin 1 ⊕ Fin m,
          y ∈ epath j ↔ y = Sum.inr ⟨2 * (j : ℕ), by omega⟩ ∨ y = Sum.inr
            ⟨2 * (j : ℕ) + 1, by omega⟩ := by
        intro j y; simp [epath]
      -- rimV is injective
      have hrim_inj : Function.Injective rimV := by
        intro j j' hj
        have hval : epath j = epath j' := Subtype.ext_iff.mp hj
        have hm1 : (Sum.inr ⟨2 * (j : ℕ), by omega⟩ : Fin 1 ⊕ Fin m) ∈ epath j := by
          simp [epath]
        rw [hval] at hm1
        rcases hmemRim_char j' _ |>.mp hm1 with h | h <;> simp [Fin.ext_iff] at h <;> omega
      -- vertices finset
      let vertices : Finset (CGraph.lineGraph (CGraph.join (CGraph.complete 1) (CGraph.path m))).V
        :=
        Finset.univ.image rimV
      -- Independence: no two epath edges share a vertex
      have hindependent : SimpleGraph.IsIndepSet (CGraph.lineGraph (CGraph.join (CGraph.complete 1)
        (CGraph.path m))).toSimple
          (vertices : Set _) := by
        unfold SimpleGraph.IsIndepSet
        intro v hv w hw hvw
        simp only [vertices, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hv hw
        obtain ⟨j, hj⟩ := hv
        obtain ⟨j', hwj'⟩ := hw
        subst hj hwj'
        by_cases heq : j = j'
        · subst heq; simp at hvw
        · intro h
          simp [CGraph.lineGraph_adj] at h
          obtain ⟨_, ⟨v, hv1, hv2⟩⟩ := h
          simp [rimV] at hv2
          rw [hmemRim_char j] at hv1
          rw [hmemRim_char j'] at hv2
          rcases hv1 with h|h <;> rcases hv2 with h'|h' <;> (
            subst h; simp at h'
            omega)
      -- Cardinality
      have hcard : vertices.card = k + 1 := by
        simp only [vertices]
        rw [Finset.card_image_of_injective _ hrim_inj]
        simp
      exact hcard ▸ SimpleGraph.IsIndepSet.card_le_indepNum hindependent
/-- **A book with at least two pages has matching number two**: one spine vertex pairs
with one page vertex and the other spine vertex with another. -/
theorem matchNum_book (n : ℕ) : (book (n + 2)).matchNum = 2 := by
  set G := book (n + 2)
  apply le_antisymm
  · -- ≤ 2
    calc G.matchNum ≤ G.coverNum := matchNum_le_coverNum G
    _ = 2 := by
        show (book (n + 2)).coverNum = 2
        rw [book_eq_join]
        simp [coverNum_join, coverNum_complete, coverNum_empty, V_complete, V_empty]
        omega
  · -- ≥ 2
    rw [matchNum_eq]
    -- Reduce to CGraph level
    have hG_cgraph : G = ⟦CGraph.completeMultipartite [1, 1, (n + 2)]⟧ := by rfl
    rw [hG_cgraph, lineGraph_mk, indepNum_mk]
    set H : CGraph := CGraph.completeMultipartite [1, 1, n + 2]
    show 2 ≤ (CGraph.lineGraph H).indepNum
    let v00 : H.V := ⟨0, ⟨0, by simp⟩⟩
    let v10 : H.V := ⟨1, ⟨0, by simp⟩⟩
    let v20 : H.V := ⟨2, ⟨0, by simp⟩⟩
    let v21 : H.V := ⟨2, ⟨1, by simp⟩⟩
    let e1 : Sym2 H.V := Sym2.mk (v00, v20)
    let e2 : Sym2 H.V := Sym2.mk (v10, v21)
    have hsua_ne1 : (CGraph.sigmaUnion (fun i => CGraph.complete ([1,1,n+2].get i))).Adj v00 v20 =
      false := by
      exact CGraph.sigmaUnion_adj_ne (fun i => CGraph.complete ([1,1,n+2].get i)) 0 2
        ⟨0, by simp⟩ ⟨0, by simp⟩ (by decide : (0:Fin 3) ≠ 2)
    have hsua_ne2 : (CGraph.sigmaUnion (fun i => CGraph.complete ([1,1,n+2].get i))).Adj v10 v21 =
      false := by
      exact CGraph.sigmaUnion_adj_ne (fun i => CGraph.complete ([1,1,n+2].get i)) 1 2
        ⟨0, by simp⟩ ⟨1, by simp⟩ (by decide : (1:Fin 3) ≠ 2)
    have hv00_ne_v20 : v00 ≠ v20 := by
      intro h; have := congr_arg (fun x : H.V => x.1) h; simp [v00, v20] at this; omega
    have hv10_ne_v21 : v10 ≠ v21 := by
      intro h; have := congr_arg (fun x : H.V => x.1) h; simp [v10, v21] at this; omega
    have hadj1 : H.Adj v00 v20 = true := by
      simp only [H, CGraph.completeMultipartite, CGraph.compl_adj]
      rw [hsua_ne1]
      simp [hv00_ne_v20]
    have hadj2 : H.Adj v10 v21 = true := by
      simp only [H, CGraph.completeMultipartite, CGraph.compl_adj]
      rw [hsua_ne2]
      simp [hv10_ne_v21]
    have he1 : e1 ∈ H.toSimple.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]; exact hadj1
    have he2 : e2 ∈ H.toSimple.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]; exact hadj2
    set e1' : (CGraph.lineGraph H).V := ⟨e1, he1⟩
    set e2' : (CGraph.lineGraph H).V := ⟨e2, he2⟩
    have hne00_10 : v00 ≠ v10 := by
      intro h; have := congr_arg (fun x : H.V => x.1) h; simp [v00, v10] at this
    have hne00_21 : v00 ≠ v21 := by
      intro h; have := congr_arg (fun x : H.V => x.1) h; simp [v00, v21] at this; omega
    have hne20_10 : v20 ≠ v10 := by
      intro h; have := congr_arg (fun x : H.V => x.1) h; simp [v20, v10] at this; omega
    have hne20_21 : v20 ≠ v21 := by
      intro h
      have h' := Sigma.ext_iff.mp h
      simp [v20, v21] at h'
      exact absurd h' (by show (0 : Fin (n + 2)) ≠ 1; simp)
    have he1_ne_he2 : e1 ≠ e2 := by
      intro h'
      rcases Sym2.eq_iff.1 h' with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hne00_10 h1
      · exact hne00_21 h1
    have hmem_e1 : ∀ v, v ∈ e1 → v = v00 ∨ v = v20 := by
      intro v hv; induction e1 using Sym2.ind with
      | _ a b => simpa [e1] using hv
    have hmem_e2 : ∀ v, v ∈ e2 → v = v10 ∨ v = v21 := by
      intro v hv; induction e2 using Sym2.ind with
      | _ a b => simpa [e2] using hv
    have hno_common : ¬ ∃ v, v ∈ (e1 : Sym2 H.V) ∧ v ∈ (e2 : Sym2 H.V) := by
      intro ⟨v, hv1, hv2⟩
      rcases hmem_e1 v hv1 with h | h <;> rcases hmem_e2 v hv2 with j | j
      · exact hne00_10 (h.symm.trans j)
      · exact hne00_21 (h.symm.trans j)
      · exact hne20_10 (h.symm.trans j)
      · exact hne20_21 (h.symm.trans j)
    have he1'_ne_he2' : e1' ≠ e2' := by
      intro h; exact he1_ne_he2 (congr_arg Subtype.val h)
    have hna : ¬ (CGraph.lineGraph H).Adj e1' e2' := by
      rw [CGraph.lineGraph_adj]
      have hdec1 : decide (e1' ≠ e2') = true := by simp [he1'_ne_he2']
      have hdec2 : decide (∃ v : H.V, v ∈ e1'.val ∧ v ∈ e2'.val) = false := by
        simp [e1', e2']
        exact fun v hv1 hv2 => hno_common ⟨v, hv1, hv2⟩
      simp [hdec1, hdec2]
    exact CGraph.two_le_indepNum he1'_ne_he2' hna

/-- **A balanced complete multipartite graph with at least two parts has a near-perfect
matching.** -/
theorem matchNum_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 1))).matchNum
      = (m + 2) * (d + 1) / 2 := by
  apply le_antisymm
  · -- Upper bound
    have h1 := two_mul_matchNum_le_V (completeMultipartite (List.replicate (m + 2) (d + 1)))
    rw [V_completeMultipartite, List.sum_replicate] at h1
    simp at h1
    omega
  · -- Lower bound: explicit matching via global enumeration
    let k := m + 2
    let s := d + 1
    let G : IsoGraph := completeMultipartite (List.replicate k s)
    rw [matchNum_eq]
    let H : CGraph := CGraph.completeMultipartite (List.replicate k s)
    have hGL : G.lineGraph = ⟦CGraph.lineGraph H⟧ := by
      simp [G, IsoGraph.completeMultipartite, IsoGraph.lineGraph_mk]
      rfl
    rw [hGL, indepNum_mk]
    have hlen : (List.replicate k s).length = k := List.length_replicate
    have hget : ∀ (i : Fin k), (List.replicate k s).get ⟨i, by rw [hlen]; exact i.2⟩ = s := by
      intro i; simp [List.getElem_replicate]
    -- vertex (i, a) in H, with i : Fin k, a : Fin s
    let vertex : Fin k → Fin s → H.V := fun i a =>
      ⟨⟨i, by rw [hlen]; exact i.2⟩, Fin.cast (hget i).symm a⟩
    have hadj : ∀ (i j : Fin k) (a : Fin s) (b : Fin s),
        H.Adj (vertex i a) (vertex j b) ↔ i ≠ j := by
      intro i j a b
      simp [vertex, H, CGraph.completeMultipartite_adj]
      simp [Fin.ext_iff]
    -- Key lemma: .2.val of vertex
    have hv_snd_val : ∀ (i : Fin k) (a : Fin s), (vertex i a).2.val = a.val := by
      intro i a; simp [vertex, Fin.cast]
    -- f : Fin (k * s) → H.V, f(j) = vertex (j % k) (j / k)
    let f : Fin (k * s) → H.V := fun ⟨j, hj⟩ =>
      vertex ⟨j % k, Nat.mod_lt _ (by omega : 0 < k)⟩ ⟨j / k, Nat.div_lt_of_lt_mul hj⟩
    have hf_fst_val : ∀ j : Fin (k * s), (f j).1.val = j.val % k := by
      intro j; simp [f, vertex]
    have hf_snd_val : ∀ j : Fin (k * s), (f j).2.val = j.val / k := by
      intro j; simp [f, vertex]
    have hf_inj : Function.Injective f := by
      intro j1 j2 hfeq
      have hmod : j1.val % k = j2.val % k := by
        have h1 := congr_arg (fun v : H.V => v.1.val) hfeq
        simp only [hf_fst_val] at h1
        exact h1
      have hdiv : j1.val / k = j2.val / k := by
        have h2 := congr_arg (fun v : H.V => v.2.val) hfeq
        simp only [hf_snd_val] at h2
        exact h2
      have : j1.val = j2.val := by
        have h1' := Nat.div_add_mod j1.val k
        have h2' := Nat.div_add_mod j2.val k
        rw [hmod, hdiv] at h1'
        linarith [h2']
      exact Fin.ext this
    -- Key bounds for all t : Fin (k * s / 2)
    have hks_ge_2 : 2 ≤ k * s := by unfold k s; nlinarith
    have hbound : ∀ (t : Fin (k * s / 2)), 2 * (t : ℕ) + 1 < k * s := by
      intro t
      have ht : (t : ℕ) < k * s / 2 := t.2
      have := Nat.div_add_mod (k * s) 2
      omega
    have hbound2 : ∀ (t : Fin (k * s / 2)), 2 * (t : ℕ) < k * s := by
      intro t; linarith [hbound t]
    -- Edge for t : Fin (k * s / 2): connect f(2*t) and f(2*t+1)
    let fm1 : Fin (k * s / 2) → Fin (k * s) := fun t => ⟨2 * t.val, hbound2 t⟩
    let fm2 : Fin (k * s / 2) → Fin (k * s) := fun t => ⟨2 * t.val + 1, hbound t⟩
    let edgeFn : Fin (k * s / 2) → (H.lineGraph).V := fun t =>
      ⟨Sym2.mk (f (fm1 t), f (fm2 t)), by
        rw [SimpleGraph.mem_edgeSet]
        show H.Adj _ _ = true
        simp only [f]
        rw [hadj]
        intro h
        have hne : (2 * t.val) % k ≠ (2 * t.val + 1) % k := by
          have hk : 2 ≤ k := by omega
          by_contra heq
          have hmod : (2 * t.val) % k = (2 * t.val + 1) % k := heq
          have := Nat.modEq_iff_dvd.mp hmod.symm
          simp at this
          exact absurd (Int.le_of_dvd (by omega : (0 : ℤ) < 1) this) (by omega)
        exact hne (congr_arg Fin.val h)⟩
    -- edgeFn is injective
    have fin_eq_of_f_eq : ∀ (a b : Fin (k * s)), f a = f b → a = b := hf_inj
    have h_edge_inj : Function.Injective edgeFn := by
      intro t t' h_eq
      dsimp only [edgeFn] at h_eq
      have hsym : Sym2.mk (f (fm1 t), f (fm2 t)) = Sym2.mk (f (fm1 t'), f (fm2 t')) := by
        exact congr_arg Subtype.val h_eq
      rw [Sym2.eq_iff] at hsym
      rcases hsym with h | h
      · -- Same order: f(fm1 t) = f(fm1 t')
        have h1 : f (fm1 t) = f (fm1 t') := h.1
        have hfin : fm1 t = fm1 t' := hf_inj h1
        have := congr_arg Fin.val hfin
        simp [fm1] at this
        exact Fin.ext (by omega)
      · -- Swapped: f(fm1 t) = f(fm2 t'), impossible by parity
        exfalso
        have h1 : f (fm1 t) = f (fm2 t') := h.1
        have hfin : fm1 t = fm2 t' := hf_inj h1
        have := congr_arg Fin.val hfin
        simp [fm1, fm2] at this
        omega
    -- The image is an independent set in the line graph
    let S := Finset.univ.image edgeFn
    have hcard : S.card = k * s / 2 := by
      rw [Finset.card_image_of_injective _ h_edge_inj, Finset.card_fin]
    have hind : SimpleGraph.IsIndepSet (H.lineGraph).toSimple (S : Set (H.lineGraph.V)) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro e he f hf hef
      have he' : e ∈ S := he
      have hf' : f ∈ S := hf
      obtain ⟨t, _, heq⟩ := Finset.mem_image.mp he'
      obtain ⟨t', _, hfq⟩ := Finset.mem_image.mp hf'
      subst heq; subst hfq
      by_cases h : t = t'
      · exact absurd (h ▸ rfl) hef
      · -- edges for t ≠ t' are vertex-disjoint
        rw [show ¬H.lineGraph.toSimple.Adj (edgeFn t) (edgeFn t') ↔ H.lineGraph.Adj (edgeFn t)
          (edgeFn t') = false from by
          rw [CGraph.toSimple_adj]; simp]
        rw [CGraph.lineGraph_adj]
        simp [h_edge_inj.ne h]
        intro v hv1 hv2
        simp [edgeFn, fm1, fm2] at hv1 hv2
        rcases hv1 with hv1 | hv1 <;> rcases hv2 with hv2 | hv2
        · exfalso
          have heq : f (fm1 t) = f (fm1 t') := hv1.symm.trans hv2
          have hfin : fm1 t = fm1 t' := hf_inj heq
          have := congr_arg Fin.val hfin; simp [fm1] at this; omega
        · exfalso
          have heq : f (fm1 t) = f (fm2 t') := hv1.symm.trans hv2
          have hfin : fm1 t = fm2 t' := hf_inj heq
          have := congr_arg Fin.val hfin; simp [fm1, fm2] at this; omega
        · exfalso
          have heq : f (fm2 t) = f (fm1 t') := hv1.symm.trans hv2
          have hfin : fm2 t = fm1 t' := hf_inj heq
          have := congr_arg Fin.val hfin; simp [fm1, fm2] at this; omega
        · exfalso
          have heq : f (fm2 t) = f (fm2 t') := hv1.symm.trans hv2
          have hfin : fm2 t = fm2 t' := hf_inj heq
          have := congr_arg Fin.val hfin; simp [fm2] at this; omega
    exact hcard.ge.trans (hind.card_le_indepNum)

/-- **A complete graph of odd order is class two**: `K_{2m+3}` needs `2m + 3` edge colours,
one more than its maximum degree. -/
theorem edgeChromNum_complete_odd (m : ℕ) :
    (complete (2 * m + 3)).edgeChromNum = 2 * m + 3 := by
  rw [edgeChromNum_eq, lineGraph_complete]
  apply le_antisymm
  · have : johnson (2 * m + 3) 2 = ⟦CGraph.johnson (2 * m + 3) 2⟧ := rfl
    rw [this, chromNum_mk, CGraph.chromNum_le_iff_colorable]
    classical
    let n := 2 * m + 3
    let G : SimpleGraph {s : Finset (Fin n) // s.card = 2} := (CGraph.johnson n 2).toSimple
    have hcolor : ∀ (s t : {s : Finset (Fin n) // s.card = 2}), G.Adj s t →
        ((s.1.sum Fin.val) % n) ≠ ((t.1.sum Fin.val) % n) := by
      intro s t hadj
      simp only [G, CGraph.toSimple_adj, CGraph.johnson_adj] at hadj
      simp at hadj
      have hs_ne_ht' : (s : Finset (Fin n)) ≠ (t : Finset (Fin n)) := by
        intro h; exact hadj.1 (Subtype.ext h)
      have hinter : ((s : Finset (Fin n)) ∩ (t : Finset (Fin n))).card = 1 := hadj.2
      set s1 := (s : Finset (Fin n))
      set t1 := (t : Finset (Fin n))
      have hs1_card : s1.card = 2 := s.property
      have ht1_card : t1.card = 2 := t.property
      have hsdiff_s : (s1 \ t1).card = 1 := by
        have := Finset.card_sdiff_add_card_inter s1 t1
        rw [hs1_card, hinter] at this; omega
      have hsdiff_t : (t1 \ s1).card = 1 := by
        have h1 := Finset.card_sdiff_add_card_inter t1 s1
        rw [Finset.inter_comm, hinter, ht1_card] at h1; omega
      obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hsdiff_s
      obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hsdiff_t
      have ha_mem_s : a ∈ s1 := (ha_eq ▸ Finset.mem_singleton_self a) |> Finset.mem_sdiff.mp |>.1
      have ha_not_t : a ∉ t1 := (ha_eq ▸ Finset.mem_singleton_self a) |> Finset.mem_sdiff.mp |>.2
      have hb_mem_t : b ∈ t1 := (hb_eq ▸ Finset.mem_singleton_self b) |> Finset.mem_sdiff.mp |>.1
      have hb_not_s : b ∉ s1 := (hb_eq ▸ Finset.mem_singleton_self b) |> Finset.mem_sdiff.mp |>.2
      have hsum_s : ∑ x ∈ s1, (x : ℕ) = ∑ x ∈ s1 \ t1, (x : ℕ) + ∑ x ∈ s1 ∩ t1, (x : ℕ) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
      have hsum_inter : ∑ x ∈ s1 ∩ t1, (x : ℕ) = ∑ x ∈ t1 ∩ s1, (x : ℕ) := by
        rw [Finset.inter_comm]
      have hsum_t : ∑ x ∈ t1, (x : ℕ) = ∑ x ∈ t1 \ s1, (x : ℕ) + ∑ x ∈ t1 ∩ s1, (x : ℕ) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter ..), Finset.sdiff_union_inter]
      rw [hsum_s, hsum_t, ha_eq, hb_eq, Finset.sum_singleton, Finset.sum_singleton, hsum_inter]
      by_contra hneq
      have ha_lt : (a : ℕ) < n := a.2
      have hb_lt : (b : ℕ) < n := b.2
      have hab : (a : ℕ) = b := by
        have hmod : (a + ∑ x ∈ t1 ∩ s1, (x : ℕ)) % n = (b + ∑ x ∈ t1 ∩ s1, (x : ℕ)) % n := hneq
        have hv : a.val % n = b.val % n := by
          have h1 : (a.val : ZMod n) = (b.val : ZMod n) := by
            have h2 : (a.val + ∑ x ∈ t1 ∩ s1, x.val : ℕ) ≡ (b.val + ∑ x ∈ t1 ∩ s1, x.val : ℕ) [MOD
              n] := by
              exact hmod
            have h3 : (a.val : ZMod n) + (∑ x ∈ t1 ∩ s1, x.val : ZMod n) =
                       (b.val : ZMod n) + (∑ x ∈ t1 ∩ s1, x.val : ZMod n) := by
              norm_cast
              rw [ZMod.natCast_eq_natCast_iff]
              exact h2
            exact add_right_cancel h3
          exact congr_arg ZMod.val h1
        exact Nat.mod_eq_of_lt ha_lt ▸ hv ▸ Nat.mod_eq_of_lt hb_lt
      exact ha_not_t ((Fin.ext hab) ▸ hb_mem_t)
    refine ⟨SimpleGraph.Coloring.mk
      (fun s : {s : Finset (Fin n) // s.card = 2} ↦
        ⟨(s.1.sum Fin.val) % n, Nat.mod_lt _ (by omega)⟩)
      @fun v w h ↦ fun heq ↦ hcolor v w h (by have := congrArg Fin.val heq; exact this)⟩
  · have h := le_edgeChromNum_complete_odd m
    rw [← chromNum_johnson_two] at h
    exact h

/-- **The line graph does not increase the diameter by more than one.** -/
theorem diameter_lineGraph_le {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E) :
    (lineGraph G).diameter ≤ G.diameter + 1 := by
  induction G using Quotient.inductionOn with | h g =>
  haveI : Nonempty g.V := hG.nonempty
  simp [diameter_mk, lineGraph_mk]
  rw [isConnected_mk] at hG
  rw [E_mk] at hE
  simp only [CGraph.diameter]
  set S := g.toSimple
  let LG : SimpleGraph g.lineGraph.V := (CGraph.lineGraph g).toSimple
  have hadj : ∀ e f : g.lineGraph.V,
      LG.Adj e f ↔ e ≠ f ∧ ∃ v : g.V, v ∈ (e.1 : Sym2 g.V) ∧ v ∈ (f.1 : Sym2 g.V) := by
    intro e f
    simp [LG, CGraph.toSimple, CGraph.lineGraph_adj, Bool.and_eq_true]
  -- Key lemma: walk lifting from S to LG
  have hwalk_lift : ∀ {u v : g.V} (w : S.Walk u v) (e : g.lineGraph.V),
      u ∈ (e.1 : Sym2 g.V) →
      ∃ e' : g.lineGraph.V, v ∈ (e'.1 : Sym2 g.V) ∧ LG.edist e e' ≤ w.length := by
    intro u v w e huv
    induction w using SimpleGraph.Walk.rec generalizing e with
    | nil =>
      exact ⟨e, huv, by rw [SimpleGraph.edist_self]; simp⟩
    | @cons x y z huv_tail wtail ih =>
      let huv_tail' : S.Adj x y := by rwa [CGraph.toSimple_adj]
      let ep : g.lineGraph.V :=
        ⟨Sym2.mk (x, y), by simpa [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] using huv_tail'⟩
      have hev' : y ∈ (ep.1 : Sym2 g.V) := Sym2.mem_mk_right _ _
      have heu' : x ∈ (e.1 : Sym2 g.V) := huv
      have hep_u' : x ∈ (ep.1 : Sym2 g.V) := Sym2.mem_mk_left _ _
      -- Step 1: edist e ep ≤ 1 (they're adjacent or equal)
      have hstep : LG.edist e ep ≤ 1 := by
        by_cases heq : e = ep
        · rw [heq]; simp
        · have hadj_ef : LG.Adj e ep := (hadj e ep).mpr ⟨heq, x, heu', hep_u'⟩
          have : LG.edist e ep ≤ 1 := by
            exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj_ef
              SimpleGraph.Walk.nil)) (by simp)
          exact this
      -- Step 2: use IH from ep to get to an edge incident to z
      obtain ⟨e', hvz', hdist'⟩ := ih ep hev'
      -- Step 3: triangle inequality
      have hels : LG.edist e e' ≤ LG.edist e ep + LG.edist ep e' := LG.edist_triangle
      have hels'' : LG.edist e e' ≤ 1 + ↑wtail.length := hels.trans (add_le_add hstep hdist')
      have hels_final : LG.edist e e' ≤ ↑(wtail.length + 1) := hels''.trans (by
        show (1 : ℕ∞) + ↑wtail.length ≤ ↑(wtail.length + 1)
        simp [Nat.cast_add, add_comm])
      exact ⟨e', hvz', hels_final⟩
  -- Get an endpoint of any line-graph vertex
  have hendpoint : ∀ (e : g.lineGraph.V), ∃ (v : g.V), v ∈ (e.1 : Sym2 g.V) := by
    intro ⟨se, _⟩
    induction se using Sym2.ind with
    | _ a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
  -- Any two edges sharing a vertex are at distance ≤ 1
  have hshared : ∀ (e f : g.lineGraph.V) (v : g.V), v ∈ (e.1 : Sym2 g.V) → v ∈ (f.1 : Sym2 g.V) →
    LG.edist e f ≤ 1 := by
    intro e f v hev hfv
    by_cases heq : e = f
    · rw [heq]; simp
    · have hadj_ef : LG.Adj e f := (hadj e f).mpr ⟨heq, v, hev, hfv⟩
      exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj_ef
        SimpleGraph.Walk.nil)) (by simp)
  -- edist in S between any two vertices ≤ G.diameter (as ℕ∞)
  have hSconn : S.Connected := hG
  have hSnediam : S.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hSconn
  have hSdiam_eq : (g.diameter : ℕ∞) = S.diam := by
    simp [CGraph.diameter, SimpleGraph.diam, S]
  have hSedist : ∀ (u x : g.V), S.edist u x ≤ ↑(CGraph.diameter g) := by
    intro u x
    rw [hSdiam_eq]
    exact SimpleGraph.edist_le_ediam.trans (le_of_eq (by
      rw [show (S.diam : ℕ∞) = S.ediam.toNat from rfl]
      exact (ENat.coe_toNat hSnediam).symm))
  -- Pairwise LG.edist bound
  have hbd : ∀ (e f : g.lineGraph.V), LG.edist e f ≤ ↑S.diam + 1 := by
    intro e f
    obtain ⟨ue, heue⟩ := hendpoint e
    obtain ⟨xf, hxf⟩ := hendpoint f
    have hreach : S.Reachable ue xf := hSconn ue xf
    obtain ⟨p, hp_len_eq_dist⟩ := hreach.exists_walk_length_eq_dist
    have hp_len_le_diam : (p.length : ℕ∞) ≤ ↑S.diam := by
      rw [hp_len_eq_dist]
      exact_mod_cast @SimpleGraph.dist_le_diam _ S hSnediam ue xf
    obtain ⟨e', hvf', hlift⟩ := hwalk_lift p e heue
    have hels'' : LG.edist e f ≤ LG.edist e e' + LG.edist e' f := LG.edist_triangle
    have hels'_le : LG.edist e e' ≤ ↑S.diam := hlift.trans hp_len_le_diam
    have hfinal : LG.edist e f ≤ ↑S.diam + 1 := hels''.trans (add_le_add hels'_le (hshared e' f xf
      hvf' hxf))
    exact hfinal
  -- Get ediam bound
  have hLGediam : LG.ediam ≤ ↑(S.diam + 1) := by
    have := SimpleGraph.ediam_le_of_edist_le (fun e f => by
      calc LG.edist e f ≤ ↑S.diam + 1 := hbd e f
        _ = ↑(S.diam + 1) := by rw [Nat.cast_add, Nat.cast_one])
    exact this
  -- Convert to diam
  have hLGediam_ne_top : LG.ediam ≠ ⊤ := by
    intro h; simp [h] at hLGediam
    exact absurd hLGediam (by
      show (↑(S.diam : ℕ) + 1 : ℕ∞) ≠ ⊤
      have : (↑(S.diam : ℕ) : ℕ∞) + 1 = ↑(S.diam + 1) := by
        simp [Nat.cast_add, Nat.cast_one]
      rw [this]
      exact WithTop.coe_ne_top)
  have hfinal : LG.diam ≤ S.diam + 1 := by
    unfold SimpleGraph.diam
    exact ENat.toNat_le_of_le_coe hLGediam
  exact hfinal

/-- **A clique in a line graph is a star or a triangle**, so once some vertex has degree three
the largest star wins and the clique number of the line graph is the maximum degree. -/
theorem cliqueNum_lineGraph_of_three_le_maxDeg {G : IsoGraph} (h : 3 ≤ maxDeg G) :
    (lineGraph G).cliqueNum = maxDeg G := by
  apply le_antisymm
  · induction G using Quotient.inductionOn with | _ g =>
    have hmax : maxDeg ⟦g⟧ = maxDeg ⟦g.canonicalize⟧ := by rw [mk_canonicalize g]
    rw [maxDeg_mk] at h
    have hcmax : g.maxDeg = g.canonicalize.maxDeg := by
      rw [← maxDeg_mk, hmax, maxDeg_mk]
    rw [hcmax] at h
    rw [← mk_canonicalize g, lineGraph_mk, cliqueNum_mk, maxDeg_mk]
    set H := g.canonicalize
    -- Helper: extract adjacency in L(H) as sharing a vertex
    have lineGraph_adj_def : ∀ e f : (CGraph.lineGraph H).V,
        (CGraph.lineGraph H).Adj e f ↔ e ≠ f ∧ ∃ v : H.V, v ∈ (e.1 : Sym2 H.V) ∧ v ∈ (f.1 : Sym2
          H.V) := by
      intro e f; rw [CGraph.lineGraph_adj]; simp [Bool.and_eq_true]
    -- Helper: elements of S are edges of H
    have key : ∀ (S : Finset (CGraph.lineGraph H).V), (CGraph.lineGraph H).toSimple.IsClique (S :
      Set (CGraph.lineGraph H).V) → S.card ≤ H.maxDeg := by
      intro S hS
      -- From hS, distinct elements of S share a vertex
      have hclique : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ∃ v : H.V, v ∈ (e.1 : Sym2 H.V) ∧ v ∈ (f.1 : Sym2
        H.V) := by
        intro e he f hf hef
        have := hS he hf hef
        rw [CGraph.toSimple_adj, lineGraph_adj_def] at this
        exact this.2
      have hinj : Function.Injective (fun e : (CGraph.lineGraph H).V => e.1) := by
        intro e f hef; exact Subtype.ext hef
      -- Common vertex case: if some v is incident to all edges in S, then |S| ≤ deg(v) ≤ maxDeg
      by_cases hstar : ∃ v : H.V, ∀ e ∈ S, v ∈ (e.1 : Sym2 H.V)
      · -- Star case
        obtain ⟨v, hv⟩ := hstar
        have himage : Finset.image (fun e : (CGraph.lineGraph H).V => e.1) S ⊆
          H.toSimple.incidenceFinset v := by
          intro e he
          simp [Finset.mem_image] at he
          obtain ⟨e₀, he₀, rfl⟩ := he
          simp [SimpleGraph.mem_incidenceFinset]
          exact ⟨e₀.2, hv e₀ he₀⟩
        calc S.card = (Finset.image (fun e : (CGraph.lineGraph H).V => e.1) S).card := by
              rw [Finset.card_image_of_injective _ hinj]
          _ ≤ (H.toSimple.incidenceFinset v).card := Finset.card_le_card himage
          _ = H.toSimple.degree v := SimpleGraph.card_incidenceFinset_eq_degree H.toSimple v
          _ ≤ H.maxDeg := H.degree_le_maxDeg v
      · -- No common vertex: show |S| ≤ 3
        have hcard_le_3 : S.card ≤ 3 := by
          by_contra hcontra
          push_neg at hcontra
          have hge4 : 4 ≤ S.card := by omega
          -- Pick two distinct edges e₁, e₂ in S
          obtain ⟨e₁, he₁, e₂, he₂, hef₁₂⟩ : ∃ e₁ ∈ S, ∃ e₂ ∈ S, e₁ ≠ e₂ := by
            have : 1 < S.card := by omega
            obtain ⟨e₁, he₁, e₂, he₂, hef⟩ := Finset.one_lt_card.mp this
            exact ⟨e₁, he₁, e₂, he₂, hef⟩
          -- e₁ and e₂ share a vertex v (clique property)
          obtain ⟨v, hv_e1, hv_e2⟩ := hclique e₁ he₁ e₂ he₂ hef₁₂
          -- By hstar, some edge e₃ ∈ S does not contain v
          obtain ⟨e₃, he₃, hv_not_e3⟩ : ∃ e₃ ∈ S, v ∉ (e₃.1 : Sym2 H.V) := by
            push_neg at hstar; exact hstar v
          have hef₁₃ : e₁ ≠ e₃ := by intro h; subst h; exact hv_not_e3 hv_e1
          have hef₂₃ : e₂ ≠ e₃ := by intro h; subst h; exact hv_not_e3 hv_e2
          -- e₃ shares u₁ with e₁
          have haj_e1_e3 := hS he₁ he₃ hef₁₃
          rw [CGraph.toSimple_adj, lineGraph_adj_def] at haj_e1_e3
          obtain ⟨u₁, hu₁_e1, hu₁_e3⟩ := haj_e1_e3.2
          have huv₁ : u₁ ≠ v := by intro h; rw [h] at hu₁_e3; exact hv_not_e3 hu₁_e3
          -- e₃ shares u₂ with e₂
          have haj_e2_e3 := hS he₂ he₃ hef₂₃
          rw [CGraph.toSimple_adj, lineGraph_adj_def] at haj_e2_e3
          obtain ⟨u₂, hu₂_e2, hu₂_e3⟩ := haj_e2_e3.2
          have huv₂ : u₂ ≠ v := by intro h; rw [h] at hu₂_e3; exact hv_not_e3 hu₂_e3
          have hne_u : u₁ ≠ u₂ := by
            intro heq
            have : e₁.1 = e₂.1 := by
              have : u₁ ∈ (e₂.1 : Sym2 H.V) := heq.symm ▸ hu₂_e2
              exact Sym2.eq_of_ne_mem huv₁ hu₁_e1 hv_e1 this hv_e2
            exact hef₁₂ (Subtype.ext this)
          -- e₃.1 has exactly members u₁ and u₂ (card 2, no loops)
          have he3_edge : e₃.1 ∈ H.toSimple.edgeSet := e₃.2
          have he3_not_diag : ¬(e₃.1).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he3_edge
          have hcard_e3 : e₃.1.toFinset.card = 2 :=
            Sym2.card_toFinset_of_not_isDiag e₃.1 he3_not_diag
          have hu1_in_e3 : u₁ ∈ e₃.1.toFinset := Sym2.mem_toFinset.mpr hu₁_e3
          have hu2_in_e3 : u₂ ∈ e₃.1.toFinset := Sym2.mem_toFinset.mpr hu₂_e3
          have hne_uv : u₁ ≠ u₂ := hne_u
          -- e₁.1 has exactly members v and u₁
          have he1_edge : e₁.1 ∈ H.toSimple.edgeSet := e₁.2
          have he1_not_diag : ¬(e₁.1).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he1_edge
          have hcard_e1 : e₁.1.toFinset.card = 2 :=
            Sym2.card_toFinset_of_not_isDiag e₁.1 he1_not_diag
          have hv_in_e1 : v ∈ e₁.1.toFinset := Sym2.mem_toFinset.mpr hv_e1
          have hu1_in_e1 : u₁ ∈ e₁.1.toFinset := Sym2.mem_toFinset.mpr hu₁_e1
          -- Similarly for e₂
          have he2_edge : e₂.1 ∈ H.toSimple.edgeSet := e₂.2
          have he2_not_diag : ¬(e₂.1).IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he2_edge
          have hcard_e2 : e₂.1.toFinset.card = 2 :=
            Sym2.card_toFinset_of_not_isDiag e₂.1 he2_not_diag
          have hv_in_e2 : v ∈ e₂.1.toFinset := Sym2.mem_toFinset.mpr hv_e2
          have hu2_in_e2 : u₂ ∈ e₂.1.toFinset := Sym2.mem_toFinset.mpr hu₂_e2
          -- e₁.1.toFinset = {v, u₁}, e₂.1.toFinset = {v, u₂}, e₃.1.toFinset = {u₁, u₂}
          -- There exists e₄ ∈ S \ {e₁, e₂, e₃}
          have hsub : {e₁, e₂, e₃} ⊆ S := by
            simp [Finset.insert_subset_iff, he₁, he₂, he₃]
          have hcard_sub : ({e₁, e₂, e₃} : Finset (CGraph.lineGraph H).V).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [hef₂₃]
            · intro h; simp_all
          have hS_minus_card : (S \ {e₁, e₂, e₃}).card > 0 := by
            have h1 := Finset.card_sdiff_of_subset hsub
            omega
          obtain ⟨e₄, he₄_mem⟩ := Finset.card_pos.mp hS_minus_card
          have he₄_mem' := he₄_mem
          obtain ⟨he₄_in_S, he₄_not_in_triple⟩ := Finset.mem_sdiff.mp he₄_mem'
          simp [Finset.mem_insert, Finset.mem_singleton] at he₄_not_in_triple
          obtain ⟨he₄_ne₁', he₄_ne₂', he₄_ne₃'⟩ := he₄_not_in_triple
          -- e₄.1 is also an edge
          have he4_edge : e₄.1 ∈ H.toSimple.edgeSet := e₄.2
          -- Adjacency gives shared vertices
          have haj_e4_e3 := hS he₄_in_S he₃ he₄_ne₃'
          have haj_e4_e1 := hS he₄_in_S he₁ he₄_ne₁'
          have haj_e4_e2 := hS he₄_in_S he₂ he₄_ne₂'
          rw [CGraph.toSimple_adj, lineGraph_adj_def] at haj_e4_e3 haj_e4_e1 haj_e4_e2
          -- e₄ adjacent to e₃: e₄.1 ≠ e₃.1 and share a vertex
          -- e₄ adjacent to e₁: e₄.1 ≠ e₁.1 and share a vertex
          -- e₄ adjacent to e₂: e₄.1 ≠ e₂.1 and share a vertex
          -- e₁.1 has v, u₁ (v ≠ u₁), e₂.1 has v, u₂ (v ≠ u₂), e₃.1 has u₁, u₂ (u₁ ≠ u₂)
          -- e₄.1 must intersect each of these. With |e₄.1| = 2, this forces e₄.1 = one of them.
          -- Use Sym2.eq_of_ne_mem: if a ≠ b, a ∈ s, b ∈ s, a ∈ t, b ∈ t, and s,t are non-diag
          -- edges, then s = t.
          -- We show e₄.1 = e₁.1, e₂.1, or e₃.1, contradicting he₄_ne.*
          obtain ⟨he4_adj3, w, hw_e4, hw_e3⟩ := haj_e4_e3
          obtain ⟨he4_adj1, z, hz_e4, hz_e1⟩ := haj_e4_e1
          obtain ⟨he4_adj2, y, hy_e4, hy_e2⟩ := haj_e4_e2
          -- e₃.1 contains u₁, u₂ (u₁ ≠ u₂). e₄.1 shares w with e₃.1.
          -- Since e₃.1 is non-diag with u₁,u₂ ∈ e₃.1 and u₁ ≠ u₂,
          -- any vertex in e₃.1 is u₁ or u₂... but we don't need that.
          -- Instead, we directly check: e₄.1 intersects e₃.1 ({u₁,u₂}), e₁.1 ({v,u₁}), e₂.1
          -- ({v,u₂}).
          -- e₄.1 has two endpoints. To intersect all three pairs, it must equal one of them.
          -- Case analysis on which endpoint of e₄.1 lies in e₃.1.
          -- w ∈ e₄.1 ∩ e₃.1. Since u₁,u₂ ∈ e₃.1 and e₃.1 is not diag with those two members,
          -- e₃.1 = Sym2.mk (u₁, u₂). So w = u₁ or w = u₂.
          have hsye_e3 : e₃.1 = Sym2.mk (u₁, u₂) := by
            exact Sym2.eq_of_ne_mem hne_uv hu₁_e3 hu₂_e3 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _
              _)
          have hsye_e1 : e₁.1 = Sym2.mk (v, u₁) := by
            exact Sym2.eq_of_ne_mem huv₁.symm hv_e1 hu₁_e1 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right
              _ _)
          have hsye_e2 : e₂.1 = Sym2.mk (v, u₂) := by
            exact Sym2.eq_of_ne_mem huv₂.symm hv_e2 hu₂_e2 (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right
              _ _)
          have hw_cases : w = u₁ ∨ w = u₂ := by
            rw [hsye_e3] at hw_e3; exact Sym2.mem_iff.mp hw_e3
          -- Now: e₄.1 ≠ e₃.1, e₄.1 ≠ e₁.1, e₄.1 ≠ e₂.1 (from adjacency ≠)
          -- and e₄.1 shares a vertex with each.
          -- w = u₁ or u₂ (from e₃ intersection)
          -- We also know z ∈ e₄.1 ∩ e₁.1, y ∈ e₄.1 ∩ e₂.1
          -- e₁.1 = Sym2.mk (v, u₁), so z = v or z = u₁
          have hz_cases : z = v ∨ z = u₁ := by
            rw [hsye_e1] at hz_e1; exact Sym2.mem_iff.mp hz_e1
          -- e₂.1 = Sym2.mk (v, u₂), so y = v or y = u₂
          have hy_cases : y = v ∨ y = u₂ := by
            rw [hsye_e2] at hy_e2; exact Sym2.mem_iff.mp hy_e2
          -- e₄.1 has two elements, one of which is w ∈ {u₁,u₂}.
          -- If w = u₁ and z = u₁ and y = u₂: e₄.1 has u₁, u₂ → e₄.1 = e₃.1, contradiction.
          -- We go case by case and derive contradiction in each.
          -- Derive concrete Sym2 membership in e₄.1
          have hw'_e4 : w ∈ (e₄.1 : Sym2 H.V) := hw_e4
          have hz'_e4 : z ∈ (e₄.1 : Sym2 H.V) := hz_e4
          have hy'_e4 : y ∈ (e₄.1 : Sym2 H.V) := hy_e4
          rcases hw_cases with hwu₁ | hwu₂
          · -- w = u₁
            have hu1_in_e4 : u₁ ∈ (e₄.1 : Sym2 H.V) := hwu₁ ▸ hw_e4
            rcases hz_cases with hzv | hzv
            · -- z = v
              have hv_in_e4 : v ∈ (e₄.1 : Sym2 H.V) := hzv ▸ hz_e4
              exfalso; apply he4_adj1; exact hinj (Sym2.eq_of_ne_mem huv₁.symm hv_in_e4 hu1_in_e4
                hv_e1 hu₁_e1)
            · -- z = u₁
              rcases hy_cases with hyv | hyu2
              · -- y = v
                have hv_in_e4 : v ∈ (e₄.1 : Sym2 H.V) := hyv ▸ hy_e4
                exfalso; apply he4_adj1; exact hinj (Sym2.eq_of_ne_mem huv₁.symm hv_in_e4 hu1_in_e4
                  hv_e1 hu₁_e1)
              · -- y = u₂
                have hu2_in_e4 : u₂ ∈ (e₄.1 : Sym2 H.V) := hyu2 ▸ hy_e4
                exfalso; apply he4_adj3; exact hinj (Sym2.eq_of_ne_mem hne_uv hu1_in_e4 hu2_in_e4
                  hu₁_e3 hu₂_e3)
          · -- w = u₂
            have hu2_in_e4 : u₂ ∈ (e₄.1 : Sym2 H.V) := hwu₂ ▸ hw_e4
            rcases hz_cases with hzv | hzv
            · -- z = v
              have hv_in_e4 : v ∈ (e₄.1 : Sym2 H.V) := hzv ▸ hz_e4
              exfalso; apply he4_adj2; exact hinj (Sym2.eq_of_ne_mem huv₂ hu2_in_e4 hv_in_e4 hu₂_e2
                hv_e2)
            · -- z = u₁
              have hu1_in_e4 : u₁ ∈ (e₄.1 : Sym2 H.V) := hzv ▸ hz_e4
              exfalso; apply he4_adj3; exact hinj (Sym2.eq_of_ne_mem hne_uv hu1_in_e4 hu2_in_e4
                hu₁_e3 hu₂_e3)
        exact le_trans hcard_le_3 h
    obtain ⟨t, ht, hcard⟩ := (CGraph.lineGraph H).toSimple.exists_isNClique_cliqueNum
    simp only [CGraph.cliqueNum] at hcard ⊢
    exact hcard ▸ key t ht
  · exact G.maxDeg_le_cliqueNum_lineGraph

/-- **The Johnson graph `J(2m+3, 2)` needs `2m + 3` colours**: its chromatic number is the edge
chromatic number of the complete graph `K_{2m+3}`, which is class two. -/
@[simp] theorem chromNum_johnson_two_odd (m : ℕ) :
    (johnson (2 * m + 3) 2).chromNum = 2 * m + 3 := by
  rw [chromNum_johnson_two, edgeChromNum_complete_odd]

/-- **The triangular graph `T(2m+3)` needs `2m + 3` colours.** -/
@[simp] theorem chromNum_triangular_odd (m : ℕ) :
    (triangular (2 * m + 3)).chromNum = 2 * m + 3 := by
  rw [← lineGraph_complete_eq_triangular, lineGraph_complete, chromNum_johnson_two_odd]

/-- **The Kneser graph `K(2m+3, 2)` has clique cover number `2m + 3`**, its complement being the
triangular graph. -/
@[simp] theorem cliqueCoverNum_kneser_two_odd (m : ℕ) :
    (kneser (2 * m + 3) 2).cliqueCoverNum = 2 * m + 3 := by
  rw [cliqueCoverNum_eq, ← triangular_eq_compl_kneser, chromNum_triangular_odd]

/-- **The triangular graph `T(n)` has clique number `n - 1`** for `n ≥ 4`: the largest clique is
the star of all pairs through a fixed point. -/
@[simp] theorem cliqueNum_triangular (n : ℕ) : (triangular (n + 4)).cliqueNum = n + 3 := by
  rw [← lineGraph_complete_eq_triangular,
    cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_complete]; omega), maxDeg_complete]
  omega

/-- **The Johnson graph `J(n, 2)` has clique number `n - 1`** for `n ≥ 4`. -/
@[simp] theorem cliqueNum_johnson_two (n : ℕ) : (johnson (n + 4) 2).cliqueNum = n + 3 := by
  rw [← lineGraph_complete, cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_complete]; omega),
    maxDeg_complete]
  omega

/-- **Erdős--Ko--Rado for pairs**: the largest intersecting family of pairs from `n ≥ 4` points is
a star, of size `n - 1`, so the Kneser graph `K(n, 2)` has independence number `n - 1`. -/
@[simp] theorem indepNum_kneser_two (n : ℕ) : (kneser (n + 4) 2).indepNum = n + 3 := by
  rw [← cliqueNum_compl, ← triangular_eq_compl_kneser, cliqueNum_triangular]

/-- **The line graph of the Petersen graph has clique number three.** -/
@[simp] theorem cliqueNum_lineGraph_petersen : (lineGraph petersen).cliqueNum = 3 := by
  rw [cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_petersen]), maxDeg_petersen]

/-- **The line graph of a hypercube `Q_{n+3}` has clique number `n + 3`.** -/
@[simp] theorem cliqueNum_lineGraph_hypercube (n : ℕ) :
    (lineGraph (hypercube (n + 3))).cliqueNum = n + 3 := by
  rw [cliqueNum_lineGraph_of_three_le_maxDeg (by rw [maxDeg_hypercube]; omega), maxDeg_hypercube]

/-- **A graph of girth three is not bipartite**: a bipartite graph with a cycle has girth at
least four. -/
theorem not_isBipartite_of_girth_eq_three {G : IsoGraph} (h : G.girth = 3) : ¬ IsBipartite G := by
  intro hb
  have := four_le_girth_of_isBipartite hb (not_isAcyclic_of_girth_pos (by omega))
  omega

/-- **A Paley graph on at least nine points is not bipartite.** -/
theorem not_isBipartite_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq9 : 9 ≤ q) :
    ¬ IsBipartite (paley q) :=
  not_isBipartite_of_girth_eq_three (girth_paley q hq hq9)

/-- **The line graph of a graph with a degree-three vertex is not bipartite**: the three edges
at that vertex form a triangle. -/
theorem not_isBipartite_lineGraph {G : IsoGraph} (h : 3 ≤ G.maxDeg) :
    ¬ IsBipartite (lineGraph G) :=
  not_isBipartite_of_girth_eq_three (girth_lineGraph_eq_three h)

/-- **A complete multipartite graph with at least three parts has a cycle.** -/
@[simp] theorem not_isAcyclic_completeMultipartite_replicate (m d : ℕ) :
    ¬ IsAcyclic (completeMultipartite (List.replicate (m + 3) (d + 1))) :=
  not_isAcyclic_of_girth_pos (by rw [girth_completeMultipartite_replicate]; omega)

/-- **The Kneser graph `K(n, 2)` has vertex cover number `C(n, 2) - (n - 1)`**, by Gallai's
identity and the Erdős--Ko--Rado value of its independence number. -/
@[simp] theorem coverNum_kneser_two (n : ℕ) :
    (kneser (n + 4) 2).coverNum = (n + 4).choose 2 - (n + 3) := by
  have h := coverNum_add_indepNum (kneser (n + 4) 2)
  rw [indepNum_kneser_two, V_kneser] at h
  omega

/-- **The triangular graph `T(n)` needs at least `n - 1` colours**, its clique number. -/
theorem le_chromNum_triangular (n : ℕ) : n + 3 ≤ (triangular (n + 4)).chromNum := by
  rw [← cliqueNum_triangular n]
  exact cliqueNum_le_chromNum _

/-- **The Johnson graph `J(n, 2)` needs at least `n - 1` colours.** -/
theorem le_chromNum_johnson_two (n : ℕ) : n + 3 ≤ (johnson (n + 4) 2).chromNum := by
  rw [← cliqueNum_johnson_two n]
  exact cliqueNum_le_chromNum _

end IsoGraph
