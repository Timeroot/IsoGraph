import IsoGraph.SmallGraphs.Grotzsch

/-!
# Trees, decorated cycles and theta graphs

Tadpoles, lollipops, double stars, spiders and theta graphs: the two-parameter families built by
decorating a cycle or a path.
-/

namespace IsoGraph

/-! ### Tadpoles, lollipops, double stars and theta graphs

The four decorated families are all `CGraph.ofEdges` on an explicit edge list, so the
counting lemmas below are all instances of "the list has no duplicates, no self-loops and no
reversed pairs, therefore `E` is its length".  The remaining invariants come from the shape:
a lollipop's clique is its largest, a tadpole's junction is its only degree-three vertex, and a
double star always has a pendant. -/

/-- **The double star has one central edge and `m + n` pendant edges.**  Its edge list is already
in the normal form of `CGraph.E_ofEdges` — every pair `(a, b)` has `a < b` — so all that is left is
to check the three side conditions and measure the list. -/
theorem E_doubleStar (m n : ℕ) : (doubleStar m n).E = m + n + 1 := by
  simp only [doubleStar, IsoGraph.E_mk]
  set es : List (ℕ × ℕ) := (0, 1) :: (((List.range m).map fun i ↦ (0, 2 + i)) ++
    ((List.range n).map fun i ↦ (1, 2 + m + i))) with hes
  have hmem : ∀ p ∈ es, p = (0, 1) ∨ (∃ i < m, p = (0, 2 + i)) ∨ ∃ i < n, p = (1, 2 + m + i) := by
    intro p hp
    simp only [hes, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
  have hlt : ∀ p ∈ es, p.1 < p.2 := by
    intro p hp
    rcases hmem p hp with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> dsimp only <;> omega
  have hbound : ∀ p ∈ es, p.2 < 2 + m + n := by
    intro p hp
    rcases hmem p hp with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> dsimp only <;> omega
  have hnup : es.Nodup := by
    rw [hes]
    refine List.nodup_cons.mpr ⟨by simp; intro x _; omega, List.Nodup.append ?_ ?_ ?_⟩
    · exact List.Nodup.map (fun a b h ↦ by simpa using h) List.nodup_range
    · exact List.Nodup.map (fun a b h ↦ by simpa using h) List.nodup_range
    · simp [List.Disjoint]
  show (CGraph.ofEdges (2 + m + n) es).E = m + n + 1
  rw [CGraph.E_ofEdges _ _ hlt hbound hnup, hes]
  simp

/-- **The lollipop is a clique with a path stuck to it**: its edge list is the clique's followed
by the leg's, and the two share no pair because the leg only ever mentions the fresh vertices. -/
theorem E_lollipop (m k : ℕ) : (lollipop (m + 1) k).E = (m + 1).choose 2 + k := by
  simp only [lollipop, CGraph.lollipop, IsoGraph.E_mk]
  have hlt : ∀ p ∈ CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k, p.1 < p.2 := by
    rintro ⟨a, b⟩ hp
    rcases List.mem_append.1 hp with h | h
    · exact ((CGraph.mem_cliqueEdges _ _ _).1 h).1
    · rcases (CGraph.mem_legEdges _ _ _ _ _).1 h with ⟨rfl, rfl, -⟩ | ⟨-, rfl, -⟩ <;> omega
  have hbound :
      ∀ p ∈ CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k, p.2 < m + 1 + k := by
    rintro ⟨a, b⟩ hp
    rcases List.mem_append.1 hp with h | h
    · have := ((CGraph.mem_cliqueEdges _ _ _).1 h).2; omega
    · rcases (CGraph.mem_legEdges _ _ _ _ _).1 h with ⟨rfl, rfl, hk⟩ | ⟨-, rfl, hlim⟩ <;> omega
  have hdisj : List.Disjoint (CGraph.cliqueEdges (m + 1)) (CGraph.legEdges 0 (m + 1) k) := by
    rintro ⟨a, b⟩ hc hl
    have hb := ((CGraph.mem_cliqueEdges _ _ _).1 hc).2
    rcases (CGraph.mem_legEdges _ _ _ _ _).1 hl with ⟨-, rfl, -⟩ | ⟨ha, rfl, -⟩ <;> omega
  rw [CGraph.E_ofEdges _ _ hlt hbound (List.Nodup.append (CGraph.cliqueEdges_nodup _)
    (CGraph.legEdges_nodup _ _ _) hdisj)]
  simp

/-- **The tadpole is a cycle plus a path**: `m + k` edges on `m + k` vertices.  The cycle edges run
`(i, i + 1)` with one backward wrap, the leg edges run forward from `m + 3`, and no pair occurs
twice or reversed, so the edge count is the length of the concatenated list. -/
theorem E_tadpole (m k : ℕ) : (tadpole (m + 3) k).E = m + 3 + k := by
  simp only [IsoGraph.E_mk, tadpole_def]
  show (CGraph.ofEdges (m + 3 + k)
    (CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).E = m + 3 + k
  have hmem : ∀ p ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k,
      (p.2 = p.1 + 1 ∧ p.1 + 1 < m + 3) ∨ (p.1 + 1 = m + 3 ∧ p.2 = 0) ∨
        (p.1 = 0 ∧ p.2 = m + 3 ∧ 0 < k) ∨ (m + 3 ≤ p.1 ∧ p.2 = p.1 + 1 ∧ p.1 + 1 < m + 3 + k) := by
    intro p hp
    rw [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hp
    tauto
  have hdisj : List.Disjoint (CGraph.cycleEdges (m + 3)) (CGraph.legEdges 0 (m + 3) k) := by
    intro p hpc hpl
    rw [CGraph.mem_cycleEdges] at hpc
    rw [CGraph.mem_legEdges] at hpl
    omega
  rw [CGraph.E_ofEdges_of_nodup (n := m + 3 + k)
    (fun p hp ↦ by rcases hmem p hp with h | h | h | h <;> omega)
    (fun p hp ↦ by rcases hmem p hp with h | h | h | h <;> omega)
    (fun p hp hrev ↦ by
      rcases hmem p hp with h | h | h | h <;> rcases hmem _ hrev with h' | h' | h' | h' <;>
        simp only at h' <;> omega)
    (List.Nodup.append (CGraph.cycleEdges_nodup _) (CGraph.legEdges_nodup _ _ _) hdisj)]
  simp

/-- The theta graph's `i`-th path contributes `xs[i] + 1` edges.  The hypothesis rules out the
repeated pole-to-pole edge that two zeroes in the list would give. -/
theorem E_thetaGraph (xs : List ℕ) (h : ∀ k ∈ xs, 0 < k) :
    (thetaGraph xs).E = xs.sum + xs.length := by
  rw [thetaGraph_def, E_mk, CGraph.thetaGraph,
    CGraph.E_ofEdges_of_nodup (n := 2 + xs.sum)
      (CGraph.thetaEdges_lt 2 xs (by omega) h)
      (CGraph.thetaEdges_ne 2 xs (by omega) h)
      (CGraph.thetaEdges_no_rev 2 xs (by omega) h)
      (CGraph.thetaEdges_nodup 2 xs (by omega) h),
    CGraph.length_thetaEdges 2 xs h]

/-- A lollipop on at least three clique vertices contains a triangle. -/
theorem girth_lollipop (m k : ℕ) : (lollipop (m + 3) k).girth = 3 := by
  simp [IsoGraph.lollipop, IsoGraph.girth_mk]
  set n := m + 3 + k
  have hn3 : 3 ≤ n := by omega
  have h1lt : 1 < n := by omega
  have h2lt : 2 < n := by omega
  have hv0 : (0 : Fin n).1 = 0 := by simp
  have hv1 : (1 : Fin n).1 = 1 := by simp [Nat.mod_eq_of_lt h1lt]
  have hv2 : (2 : Fin n).1 = 2 := by simp [Nat.mod_eq_of_lt h2lt]
  have hmem01 : ((0, 1) : (ℕ × ℕ)) ∈ CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k :=
    List.mem_append_left _ (by simp [CGraph.mem_cliqueEdges])
  have hmem12 : ((1, 2) : (ℕ × ℕ)) ∈ CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k :=
    List.mem_append_left _ (by simp [CGraph.mem_cliqueEdges])
  have hmem02 : ((0, 2) : (ℕ × ℕ)) ∈ CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k :=
    List.mem_append_left _ (by simp [CGraph.mem_cliqueEdges])
  have h01 : (CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).Adj (0
      : Fin n) (1 : Fin n) := by
    rw [CGraph.ofEdges_adj_val]
    rw [hv0, hv1]
    exact ⟨by simp, Or.inl hmem01⟩
  have h12 : (CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).Adj (1
      : Fin n) (2 : Fin n) := by
    rw [CGraph.ofEdges_adj_val, hv1, hv2]
    exact ⟨by simp, Or.inl hmem12⟩
  have h20 : (CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k)).Adj (2
      : Fin n) (0 : Fin n) := by
    rw [CGraph.ofEdges_adj_val, hv2, hv0]
    exact ⟨by simp, Or.inr hmem02⟩
  have : CGraph.lollipop (m + 3) k = CGraph.ofEdges n (CGraph.cliqueEdges (m + 3) ++
      CGraph.legEdges 0 (m + 3) k) := rfl
  rw [this]
  exact CGraph.girth_eq_three_of_triangle h01 h12 h20

/-- A double star always has a vertex of degree one — a pendant, or an endpoint of the central
edge when there are no pendants. -/
theorem minDeg_doubleStar (m n : ℕ) : minDeg (doubleStar m n) = 1 := by
  change (CGraph.doubleStar m n).minDeg = 1
  refine le_antisymm ?_ (CGraph.le_minDeg_of_forall ⟨0, by omega⟩ fun v ↦ ?_)
  · have hlast : ∀ v : (CGraph.doubleStar m n).V, v.1 = 1 + m + n →
        (CGraph.doubleStar m n).toSimple.degree v ≤ 1 := by
      intro v hv
      refine le_trans (CGraph.degree_ofEdges_le (2 + m + n) _ v [if n = 0 then 0 else 1] ?_)
        (by simp)
      intro w hne hw
      simp only [hv, CGraph.mem_doubleStarEdges] at hw hne
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      split_ifs <;> omega
    exact le_trans (CGraph.minDeg_le_degree _ _) (hlast ⟨1 + m + n, by omega⟩ rfl)
  · refine le_trans (by simp) (CGraph.le_degree_ofEdges (2 + m + n) _ v
      [if v.1 = 0 then 1 else if v.1 = 1 then 0 else if v.1 < 2 + m then 0 else 1] (by simp) ?_)
    intro w hw
    have hv : v.1 < 2 + m + n := v.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
    simp only [CGraph.mem_doubleStarEdges]
    split_ifs <;> omega

/-- The coordinate edges alone already connect the cube. -/
theorem isConnected_foldedCube (n : ℕ) : IsConnected (foldedCube (n + 1)) := by
  simp only [IsoGraph.foldedCube, IsoGraph.isConnected_mk, CGraph.IsConnected]
  have key : ∀ x y : Fin (n + 1) → Bool,
      (CGraph.hypercube (n + 1)).Adj x y → (CGraph.foldedCube (n + 1)).Adj x y := by
    intro x y hadj
    simp only [CGraph.hypercube_adj, CGraph.foldedCube_adj] at hadj ⊢
    have hne : x ≠ y := by
      by_contra hxy; simp [hxy] at hadj
    simp [hne, hadj]
  have hle : (CGraph.hypercube (n + 1)).toSimple ≤ (CGraph.foldedCube (n + 1)).toSimple := by
    intro x y h; rw [CGraph.toSimple_adj]; exact key x y h
  have hconn : (CGraph.hypercube (n + 1)).toSimple.Connected := isConnected_hypercube (n + 1)
  show SimpleGraph.Connected (CGraph.foldedCube (n + 1)).toSimple
  haveI hne : Nonempty (CGraph.foldedCube (n + 1)).V := by
    exact ⟨fun _ => false⟩
  exact SimpleGraph.Connected.mk
    (fun u v => by
      have hreach : (CGraph.hypercube (n + 1)).toSimple.Reachable u v := hconn.preconnected u v
      exact hreach.mono hle)

theorem numComponents_foldedCube (n : ℕ) : (foldedCube (n + 1)).numComponents = 1 :=
  (numComponents_eq_one_iff (foldedCube (n + 1))).mpr (isConnected_foldedCube n)

/-- For odd `n` the antipodal map reverses parity, so the folded cube is bipartite and the two
parity classes are the extremal independent sets. -/
theorem chromNum_foldedCube_odd {n : ℕ} (hn : n % 2 = 1) : (foldedCube n).chromNum = 2 := by
  rw [chromNum_eq_two_iff]
  refine ⟨isBipartite_foldedCube_odd hn, ?_⟩
  rw [foldedCube_def, E_mk]
  have hne' : (fun _ : Fin n => Bool.false) ≠ (fun _ : Fin n => Bool.true) := by
    intro h; exact absurd (congr_fun h ⟨0, Nat.pos_of_ne_zero (by omega)⟩) (by simp)
  have hadj : (CGraph.foldedCube n).Adj (fun _ => false) (fun _ => true) := by
    simp [CGraph.foldedCube_adj, hne']
  have hex : Sym2.mk (fun _ => (false : Bool), fun _ => (true : Bool)) ∈ (CGraph.foldedCube
      n).toSimple.edgeFinset := by
    simp [SimpleGraph.mem_edgeFinset, CGraph.toSimple_adj, hne']
  have hne'' : (CGraph.foldedCube n).toSimple.edgeFinset.Nonempty := ⟨_, hex⟩
  unfold CGraph.E
  exact Finset.card_pos.mpr hne''

/-- A connected regular bipartite graph has a perfect matching, so `α = |V| / 2`. -/
theorem indepNum_foldedCube_odd (m : ℕ) : (foldedCube (2 * m + 1)).indepNum = 2 ^ (2 * m) := by
  have hn : (2 * m + 1) % 2 = 1 := by omega
  have hchi := chromNum_foldedCube_odd hn
  have hchi_iff := chromNum_eq_two_iff.mp hchi
  have hE := hchi_iff.2
  have hVT := isVertexTransitive_foldedCube (2 * m + 1)
  have hV := V_foldedCube (2 * m + 1)
  have h1 := V_le_chromNum_mul_indepNum (foldedCube (2 * m + 1))
  rw [hchi, hV] at h1
  have h2 := two_mul_indepNum_le_V hVT hE
  rw [hV] at h2
  ring_nf at h1 h2 ⊢
  omega

theorem matchNum_foldedCube_odd (m : ℕ) : (foldedCube (2 * m + 1)).matchNum = 2 ^ (2 * m) := by
  -- Upper bound: 2 * matchNum ≤ V = 2^(2*m+1)
  have hUB : 2 * (foldedCube (2 * m + 1)).matchNum ≤ 2 ^ (2 * m + 1) := by
    exact le_trans (two_mul_matchNum_le_V _) (V_foldedCube _).le
  rw [pow_succ] at hUB
  -- Lower bound: exhibit antipodal matching of size 2^(2*m)
  rw [matchNum_eq]
  -- Need: 2^(2*m) ≤ indepNum (lineGraph (foldedCube (2*m+1)))
  -- Lower bound via antipodal-style matching... actually use coordinate edge matching
  -- For each x : Fin (2*m) → Bool, v0 x and v1 x differ in exactly bit 0,
  -- so {v0 x, v1 x} is a coordinate edge (Hamming dist 1) in foldedCube (2*m+1).
  -- These 2^(2*m) edges are pairwise disjoint.
  have hUB2 : indepNum (lineGraph (foldedCube (2 * m + 1))) ≤ 2 ^ (2 * m) := by
    rw [matchNum_eq] at hUB; omega
  have hLB_cgraph : 2 ^ (2 * m) ≤ (CGraph.foldedCube (2 * m + 1)).lineGraph.indepNum := by
    let v0 : (Fin (2 * m) → Bool) → (Fin (2 * m + 1) → Bool) := fun x => Fin.cons false x
    let v1 : (Fin (2 * m) → Bool) → (Fin (2 * m + 1) → Bool) := fun x => Fin.cons true x
    have huv_adj : ∀ x : Fin (2 * m) → Bool, (CGraph.foldedCube (2 * m + 1)).Adj (v0 x) (v1 x) := by
      intro x
      rw [CGraph.foldedCube_adj]
      dsimp [v0, v1]
      have hdiff : (Finset.univ.filter (fun i : Fin (2 * m + 1) =>
          ¬(Fin.cons false x : Fin (2 * m + 1) → Bool) i = (Fin.cons true x : Fin (2 * m + 1) →
              Bool) i)) = {0} := by
        ext i
        simp [Fin.cons]
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      rw [hdiff]
      simp
    let edgeVertex : (Fin (2 * m) → Bool) → (CGraph.lineGraph (CGraph.foldedCube (2 * m +
        1))).V := fun x =>
      ⟨Sym2.mk (v0 x, v1 x), by
        rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
        exact huv_adj x⟩
    let S : Finset (CGraph.lineGraph (CGraph.foldedCube (2 * m +
        1))).V := Finset.univ.image edgeVertex
    have hv0_inj : Function.Injective v0 := by
      intro x y h; simp [v0] at h; exact h
    have hdisjoint : ∀ x y : (Fin (2 * m) → Bool), x ≠ y →
        ¬∃ v : Fin (2 * m + 1) → Bool, v ∈ (Sym2.mk (v0 x, v1 x) : Sym2 (Fin (2 * m + 1) → Bool)) ∧
          v ∈ (Sym2.mk (v0 y, v1 y) : Sym2 (Fin (2 * m + 1) → Bool)) := by
      intro x y hxy ⟨v, hv1, hv2⟩
      rw [Sym2.mem_iff] at hv1 hv2
      rcases hv1 with rfl | rfl
      · rcases hv2 with h1 | h1
        · exact hxy (hv0_inj h1)
        · have h2 := congr_fun h1 0; simp [v0, v1] at h2
      · rcases hv2 with h1 | h1
        · have h2 := congr_fun h1 0; simp [v0, v1] at h2
        · exact hxy (by simpa [v1] using h1)
    have hS_indep : (CGraph.lineGraph (CGraph.foldedCube (2 * m + 1))).toSimple.IsIndepSet S := by
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
    have hinj : Function.Injective edgeVertex := by
      intro x y hxy
      have hsym2 : Sym2.mk (v0 x, v1 x) = Sym2.mk (v0 y, v1 y) := Subtype.ext_iff.mp hxy
      rcases Sym2.eq_iff.1 hsym2 with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hv0_inj h1
      · have h2 := congr_fun h1 0; simp [v0, v1] at h2
    have hS_card : S.card = 2 ^ (2 * m) := by
      rw [Finset.card_image_of_injective _ hinj]
      simp [Finset.card_univ]
    exact hS_card ▸ hS_indep.card_le_indepNum
  have hLB : 2 ^ (2 * m) ≤ indepNum (lineGraph (foldedCube (2 * m + 1))) := by
    show 2 ^ (2 * m) ≤ indepNum (lineGraph (foldedCube (2 * m + 1)))
    rw [show (foldedCube (2 * m + 1) : IsoGraph) = ⟦CGraph.foldedCube (2 * m + 1)⟧ from rfl,
      lineGraph_mk, indepNum_mk]
    exact hLB_cgraph
  exact le_antisymm hUB2 hLB

/-- The junction of a tadpole's cycle and its tail is the only vertex of degree three. -/
theorem maxDeg_tadpole (m k : ℕ) : maxDeg (tadpole (m + 3) (k + 1)) = 3 := by
  rw [tadpole_def, maxDeg_mk]
  have hdeg0 : ∀ v : (CGraph.tadpole (m + 3) (k + 1)).V, v.1 = 0 →
      (CGraph.tadpole (m + 3) (k + 1)).toSimple.degree v = 3 := by
    intro v hv
    have h := CGraph.degree_ofEdges (m + 3 + (k + 1)) _ v [1, m + 2, m + 3]
      (by simp) (by simp; omega) (by simp [hv])
      (by
        intro w hne
        simp only [hv, List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges,
          List.mem_cons, List.not_mem_nil, or_false, true_and, and_true]
        omega)
    simpa using h
  refine le_antisymm (CGraph.maxDeg_le_of_forall fun v ↦ ?_)
    (le_of_eq_of_le (hdeg0 ⟨0, by omega⟩ rfl).symm (CGraph.degree_le_maxDeg _ _))
  refine le_trans (CGraph.degree_ofEdges_le (m + 3 + (k + 1)) _ v
    [if v.1 = 0 then m + 2 else v.1 - 1, v.1 + 1, if v.1 = 0 then m + 3 else 0] ?_) (by simp)
  intro w hne hw
  have hv : v.1 < m + 3 + (k + 1) := v.isLt
  simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  split_ifs <;> omega

/-- The two centres of a double star have degrees `m + 1` and `n + 1`; every other vertex is
pendant. -/
theorem maxDeg_doubleStar (m n : ℕ) : maxDeg (doubleStar m n) = max m n + 1 := by
  change (CGraph.doubleStar m n).maxDeg = max m n + 1
  have hdeg0 : ∀ v : (CGraph.doubleStar m n).V, v.1 = 0 →
      (CGraph.doubleStar m n).toSimple.degree v = m + 1 := by
    intro v hv
    have h := CGraph.degree_ofEdges (2 + m + n) _ v (1 :: (List.range m).map fun i ↦ 2 + i)
      (List.nodup_cons.mpr ⟨by simp [List.mem_map_add_range],
        List.Nodup.map (fun a b hab ↦ by omega) List.nodup_range⟩)
      (by
        intro w hw
        simp only [List.mem_cons, List.mem_map_add_range] at hw
        omega)
      (by simp only [hv, List.mem_cons, List.mem_map_add_range]; omega)
      (by
        intro w hne
        rw [hv, CGraph.mem_doubleStarEdges, CGraph.mem_doubleStarEdges]
        simp only [List.mem_cons, List.mem_map_add_range, true_and]
        omega)
    simpa using h
  have hdeg1 : ∀ v : (CGraph.doubleStar m n).V, v.1 = 1 →
      (CGraph.doubleStar m n).toSimple.degree v = n + 1 := by
    intro v hv
    have h := CGraph.degree_ofEdges (2 + m + n) _ v (0 :: (List.range n).map fun i ↦ 2 + m + i)
      (List.nodup_cons.mpr ⟨by simp [List.mem_map_add_range],
        List.Nodup.map (fun a b hab ↦ by omega) List.nodup_range⟩)
      (by
        intro w hw
        simp only [List.mem_cons, List.mem_map_add_range] at hw
        omega)
      (by simp only [hv, List.mem_cons, List.mem_map_add_range]; omega)
      (by
        intro w hne
        rw [hv, CGraph.mem_doubleStarEdges, CGraph.mem_doubleStarEdges]
        simp only [List.mem_cons, List.mem_map_add_range, true_and, and_true]
        omega)
    simpa using h
  refine le_antisymm (CGraph.maxDeg_le_of_forall fun v ↦ ?_) ?_
  · by_cases h0 : v.1 = 0
    · rw [hdeg0 v h0]
      omega
    by_cases h1 : v.1 = 1
    · rw [hdeg1 v h1]
      omega
    refine le_trans (CGraph.degree_ofEdges_le (2 + m + n) _ v
      [if v.1 < 2 + m then 0 else 1] ?_) (by simp)
    intro w hne hw
    simp only [CGraph.mem_doubleStarEdges] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> omega
  · rcases le_total m n with h | h
    · rw [max_eq_right h]
      exact le_of_eq_of_le (hdeg1 ⟨1, by omega⟩ rfl).symm (CGraph.degree_le_maxDeg _ _)
    · rw [max_eq_left h]
      exact le_of_eq_of_le (hdeg0 ⟨0, by omega⟩ rfl).symm (CGraph.degree_le_maxDeg _ _)

/-- The colouring that both `cliqueNum_lollipop` and `chromNum_lollipop` rest on: the clique takes
the `m + 2` colours in order, and the leg alternates between the first two. -/
private theorem chromNum_lollipop_le (m k : ℕ) :
    (CGraph.lollipop (m + 2) k).chromNum ≤ m + 2 := by
  rw [CGraph.chromNum_le_iff_colorable]
  have : (m + 2) ≥ 2 := by omega
  -- Define the coloring: clique vertices get color = their index, path vertices get alternating
  -- colors 1,2
  let f : Fin (m + 2 + k) → Fin (m + 2) := fun v =>
    if h : v.val < m + 2 then ⟨v.val, by omega⟩
    else ⟨1 - ((v.val - (m + 2)) % 2), by omega⟩
  have hproper : ∀ {u v : Fin (m + 2 + k)},
      (CGraph.ofEdges (m + 2 + k) (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges 0 (m + 2)
          k)).Adj u v = true →
      f u ≠ f v := by
    intro u v huv
    rw [CGraph.ofEdges_adj_val] at huv
    obtain ⟨hne, huv' | huv'⟩ := huv
    · -- edge (u, v)
      rw [List.mem_append] at huv'
      rcases huv' with hu' | hv'
      · -- u,v in clique
        rw [CGraph.mem_cliqueEdges] at hu'
        obtain ⟨hlt, hb⟩ := hu'
        simp [f, show (u : ℕ) < m + 2 from hlt.trans hb, show (v : ℕ) < m + 2 from hb]
        exact hne
      · -- edge in legEdges
        rw [CGraph.mem_legEdges] at hv'
        rcases hv' with (⟨hu0, hvleg, hkpos⟩ | ⟨humble, hv_eq, hvbound⟩)
        · -- (0, m+2): f 0 = 0, f (m+2) = 1 - 0 = 1
          have hu0' : u = 0 := Fin.ext hu0
          have hvleg' : v = ⟨m + 2, by omega⟩ := Fin.ext hvleg
          simp [f, hu0', hvleg']
        · -- (u, u+1) in path: both ≥ m+2, offsets j and j+1 have different parities
          have hu_ge : m + 2 ≤ (u : ℕ) := humble
          have hv_eq' : (v : ℕ) = (u : ℕ) + 1 := hv_eq
          simp [f, show ¬((u : ℕ) < m + 2) from by omega,
                show ¬((v : ℕ) < m + 2) from by omega]
          rw [hv_eq']
          set j : ℕ := (u : ℕ) - (m + 2)
          simp [show (↑u + 1 - (m + 2) : ℕ) = j + 1 from by omega]
          have hm2 : 2 ≤ m + 2 := this
          rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega
    · -- edge (v, u): handle symmetrically
      rw [List.mem_append] at huv'
      rcases huv' with hv' | hu'
      · rw [CGraph.mem_cliqueEdges] at hv'
        obtain ⟨hlt, hb⟩ := hv'
        simp [f, show (v : ℕ) < m + 2 from hlt.trans hb, show (u : ℕ) < m + 2 from hb]
        exact hne
      · rw [CGraph.mem_legEdges] at hu'
        rcases hu' with (⟨hu0, hvleg, hkpos⟩ | ⟨humble, hu_eq, hvbound⟩)
        · -- (m+2, 0): f (m+2) = 1, f 0 = 0
          have hv0' : v = 0 := Fin.ext hu0
          have huleg' : u = ⟨m + 2, by omega⟩ := Fin.ext hvleg
          simp [f, hv0', huleg']
        · -- (v, v+1) in path swapped: u = v+1, both ≥ m+2
          have hv_ge : m + 2 ≤ (v : ℕ) := humble
          simp [f, show ¬((v : ℕ) < m + 2) from by omega,
                show ¬((u : ℕ) < m + 2) from by omega]
          rw [hu_eq]
          set j : ℕ := (v : ℕ) - (m + 2)
          simp [show (↑v + 1 - (m + 2) : ℕ) = j + 1 from by omega]
          have hm2 : 2 ≤ m + 2 := this
          rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega
  unfold CGraph.toSimple
  show SimpleGraph.Colorable _ _
  refine ⟨SimpleGraph.Coloring.mk f (fun {u v} huv ↦ hproper ?_)⟩
  simp [CGraph.lollipop] at huv
  exact huv

/-- The clique a lollipop is built from is a clique of it. -/
private theorem le_cliqueNum_lollipop (m k : ℕ) :
    m + 2 ≤ (CGraph.lollipop (m + 2) k).cliqueNum := by
  have h := CGraph.card_le_cliqueNum (G := CGraph.lollipop (m + 2) k)
    (fun i : Fin (m + 2) ↦ (⟨i.val, by omega⟩ : Fin (m + 2 + k))) ?_ ?_
  · simpa using h
  · have key : ∀ (x y : ℕ) (hx : x < m + 2 + k) (hy : y < m + 2 + k),
        (⟨x, hx⟩ : Fin (m + 2 + k)) = ⟨y, hy⟩ → x = y := fun _ _ _ _ h ↦ congrArg Fin.val h
    intro a b hab
    dsimp only at hab
    exact Fin.ext (key _ _ _ _ hab)
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun heq ↦ hij (Fin.ext heq)
    show (CGraph.ofEdges (m + 2 + k)
      (CGraph.cliqueEdges (m + 2) ++ CGraph.legEdges 0 (m + 2) k)).Adj _ _ = true
    rw [CGraph.ofEdges_adj_val]
    refine ⟨fun heq ↦ hne heq, ?_⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨h, j.2⟩))
    · exact Or.inr (List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨h, i.2⟩))

/-- The clique a lollipop is built from is its largest. -/
theorem cliqueNum_lollipop (m k : ℕ) : (lollipop (m + 2) k).cliqueNum = m + 2 := by
  simp only [IsoGraph.lollipop_def, IsoGraph.cliqueNum_mk]
  exact le_antisymm ((CGraph.cliqueNum_le_chromNum _).trans (chromNum_lollipop_le m k))
    (le_cliqueNum_lollipop m k)

/-- Greedily colouring the tail of a lollipop needs no colour beyond the clique's. -/
theorem chromNum_lollipop (m k : ℕ) : (lollipop (m + 2) k).chromNum = m + 2 := by
  simp only [IsoGraph.lollipop_def, IsoGraph.chromNum_mk]
  exact le_antisymm (chromNum_lollipop_le m k)
    ((le_cliqueNum_lollipop m k).trans (CGraph.cliqueNum_le_chromNum _))

/-- Every pendant of a double star, and nothing else. -/
theorem indepNum_doubleStar (m n : ℕ) :
    (doubleStar (m + 1) (n + 1)).indepNum = m + n + 2 := by
  -- Work at CGraph level
  set G := CGraph.doubleStar (m + 1) (n + 1)
  -- V = m + n + 4
  have hV : FinEnum.card G.V = m + n + 4 := by
    simp [G, CGraph.card_doubleStar]; omega
  -- Step A: the pendants, the vertices numbered `2` and up, are independent
  let s : Finset G.V := Finset.univ.filter (fun v : G.V => 2 ≤ v.1)
  have hs_card : s.card = m + n + 2 := by
    have heq : s = Finset.image (fun i : Fin (m + n + 2) => ⟨i.val + 2, by omega⟩ : Fin (m + n + 2)
        → G.V) (Finset.univ : Finset (Fin (m + n + 2))) := by
      ext v
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hv2
        exact ⟨⟨v.1 - 2, by omega⟩, Fin.ext (Nat.sub_add_cancel hv2)⟩
      · rintro ⟨i, rfl⟩
        simp
    rw [heq]
    rw [Finset.card_image_of_injective _ (fun i j h => by
      have := congr_arg Fin.val h; simp at this; exact Fin.ext this)]
    simp
  have hs_indep : G.toSimple.IsIndepSet (s : Set G.V) := by
    intro v hv w hw hvw
    simp [s] at hv hw
    rw [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
    omega
  have hindep_ge : m + n + 2 ≤ G.indepNum := by
    rw [← hs_card]
    exact hs_indep.card_le_indepNum
  -- Step B: `{0, 2}` and `{1, m + 3}` are two disjoint edges, so `2 ≤ ν ≤ τ`
  have hne : ∀ (x y : ℕ) (hx hy), x ≠ y → ((⟨x, hx⟩ : G.V) ≠ ⟨y, hy⟩) :=
    fun _ _ _ _ h he ↦ h (congrArg Fin.val he)
  have hmatch : 2 ≤ G.matchNum := by
    have hkey := CGraph.card_le_matchNum (G := G)
      (Sum.elim (fun _ : Unit ↦ (⟨0, by omega⟩ : G.V)) (fun _ : Unit ↦ (⟨1, by omega⟩ : G.V)))
      (Sum.elim (fun _ : Unit ↦ (⟨2, by omega⟩ : G.V))
        (fun _ : Unit ↦ (⟨2 + (m + 1), by omega⟩ : G.V))) ?_ ?_
    · simpa using hkey
    · rintro (⟨⟩ | ⟨⟩)
      · simp [G, CGraph.doubleStar_adj_val]
      · simp [G, CGraph.doubleStar_adj_val]
        omega
    · rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) hij <;> simp only [Sum.elim_inl, Sum.elim_inr]
      · exact absurd rfl hij
      · exact ⟨hne _ _ _ _ (by omega), hne _ _ _ _ (by omega), hne _ _ _ _ (by omega),
          hne _ _ _ _ (by omega)⟩
      · exact ⟨hne _ _ _ _ (by omega), hne _ _ _ _ (by omega), hne _ _ _ _ (by omega),
          hne _ _ _ _ (by omega)⟩
      · exact absurd rfl hij
  have hcover_ge : 2 ≤ G.coverNum := le_trans hmatch (by
    have := IsoGraph.matchNum_le_coverNum ⟦G⟧
    simpa using this)
  -- Step C: Combine
  have hadd : G.coverNum + G.indepNum = FinEnum.card G.V :=
    CGraph.coverNum_add_indepNum G
  rw [hV] at hadd
  show G.indepNum = m + n + 2
  omega

/-- A cycle with a path glued to it stays connected: the vertex number is a rank in the sense
of `CGraph.isConnected_of_rank`, descending around the cycle and back down the tail. -/
theorem isConnected_tadpole (m k : ℕ) : IsConnected (tadpole (m + 3) k) := by
  unfold IsoGraph.tadpole
  rw [IsoGraph.isConnected_mk]
  refine CGraph.isConnected_of_rank (fun v ↦ (v : Fin (m + 3 + k)).val)
    (⟨0, by omega⟩ : Fin (m + 3 + k)) fun v hv ↦ ?_
  have hlt := (v : Fin (m + 3 + k)).isLt
  have hv0 : 0 < (v : Fin (m + 3 + k)).val := by
    rcases Nat.eq_zero_or_pos (v : Fin (m + 3 + k)).val with h | h
    · exact absurd (Fin.ext h) hv
    · exact h
  set i := (v : Fin (m + 3 + k)).val with hi
  by_cases hmid : i = m + 3
  · -- the first vertex of the tail hangs off the centre `0`
    refine ⟨(⟨0, by omega⟩ : Fin (m + 3 + k)), show 0 < i by omega, ?_⟩
    rw [CGraph.tadpole_adj_val]
    refine ⟨show i ≠ 0 by omega, Or.inr ?_⟩
    show (0, i) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k
    exact List.mem_append_right _
      ((CGraph.mem_legEdges _ _ _ _ _).2 (Or.inl ⟨rfl, hmid, by omega⟩))
  · -- everything else has its predecessor as a neighbour
    refine ⟨(⟨i - 1, by omega⟩ : Fin (m + 3 + k)), show i - 1 < i by omega, ?_⟩
    rw [CGraph.tadpole_adj_val]
    refine ⟨show i ≠ i - 1 by omega, Or.inr ?_⟩
    show (i - 1, i) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.legEdges 0 (m + 3) k
    rcases Nat.lt_or_ge i (m + 3) with hcyc | hcyc
    · exact List.mem_append_left _ ((CGraph.mem_cycleEdges _ _ _).2 (Or.inl ⟨by omega, by omega⟩))
    · exact List.mem_append_right _
        ((CGraph.mem_legEdges _ _ _ _ _).2 (Or.inr ⟨by omega, by omega, by omega⟩))

theorem numComponents_tadpole (m k : ℕ) : (tadpole (m + 3) k).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tadpole m k)

/-- The far end of the tail is the unique pendant. -/
theorem minDeg_tadpole (m k : ℕ) : minDeg (tadpole (m + 3) (k + 1)) = 1 := by
  rw [tadpole_def, minDeg_mk]
  refine le_antisymm ?_ (CGraph.le_minDeg_of_forall ⟨0, by omega⟩ fun v ↦ ?_)
  · have hlast : ∀ v : (CGraph.tadpole (m + 3) (k + 1)).V, v.1 = m + 3 + k →
        (CGraph.tadpole (m + 3) (k + 1)).toSimple.degree v ≤ 1 := by
      intro v hv
      refine le_trans (CGraph.degree_ofEdges_le (m + 3 + (k + 1)) _ v
        [if k = 0 then 0 else m + 2 + k] ?_) (by simp)
      intro w hne hw
      simp only [hv, List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hw hne
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      split_ifs <;> omega
    exact le_trans (CGraph.minDeg_le_degree _ _) (hlast ⟨m + 3 + k, by omega⟩ rfl)
  · refine le_trans (by simp) (CGraph.le_degree_ofEdges (m + 3 + (k + 1)) _ v
      [if v.1 = 0 then 1 else if v.1 = m + 3 then 0 else v.1 - 1] (by simp) ?_)
    intro w hw
    have hv : v.1 < m + 3 + (k + 1) := v.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
    simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges]
    split_ifs <;> omega

/-- A cycle of length four or more is triangle free, and gluing on a path adds no clique. -/
theorem cliqueNum_tadpole (m k : ℕ) : (tadpole (m + 4) k).cliqueNum = 2 := by
  -- Triangle-freeness at IsoGraph level
  unfold IsoGraph.tadpole
  rw [IsoGraph.cliqueNum_mk]
  -- Lower bound: 2 ≤ cliqueNum from E > 0
  have h2 : 2 ≤ (CGraph.tadpole (m + 4) k).cliqueNum := by
    apply CGraph.two_le_cliqueNum_of_E_pos
    show 0 < (CGraph.tadpole (m + 4) k).E
    have hE := IsoGraph.E_tadpole (m + 1) k
    show 0 < (CGraph.tadpole ((m + 1) + 3) k).E
    rw [show m + 4 = (m + 1) + 3 from by omega]
    simp [IsoGraph.tadpole_def] at hE
    rw [hE]
    omega
  -- Upper bound: cliqueNum ≤ 2 from triangle-freeness
  have htri2 : ∀ (x y z : (CGraph.tadpole (m + 4) k).V),
      (CGraph.tadpole (m + 4) k).Adj x y →
      (CGraph.tadpole (m + 4) k).Adj y z →
      (CGraph.tadpole (m + 4) k).Adj z x → False := by
    intro x y z hxy hyz hzx
    rw [CGraph.tadpole_adj_val] at hxy hyz hzx
    simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hxy hyz hzx
    omega
  have hle : (CGraph.tadpole (m + 4) k).cliqueNum ≤ 2 := by
    by_contra hcon
    have hcon2 : 3 ≤ (CGraph.tadpole (m + 4) k).cliqueNum := by omega
    have hg : (CGraph.tadpole (m + 4) k).girth = 3 :=
      CGraph.girth_eq_three_of_cliqueNum hcon2
    have hnac : ¬ (CGraph.tadpole (m + 4) k).IsAcyclic := by
      intro hac; rw [CGraph.girth_eq_zero_iff.mpr hac] at hg; omega
    have := CGraph.four_le_girth htri2 hnac
    omega
  omega

/-- A clique with a path glued to it stays connected: the vertex number is a rank in the sense
of `CGraph.isConnected_of_rank`, and everything in the clique sees vertex `0`. -/
theorem isConnected_lollipop (m k : ℕ) : IsConnected (lollipop (m + 1) k) := by
  unfold IsoGraph.lollipop
  rw [IsoGraph.isConnected_mk]
  refine CGraph.isConnected_of_rank (fun v ↦ (v : Fin (m + 1 + k)).val)
    (⟨0, by omega⟩ : Fin (m + 1 + k)) fun v hv ↦ ?_
  have hlt := (v : Fin (m + 1 + k)).isLt
  have hv0 : 0 < (v : Fin (m + 1 + k)).val := by
    rcases Nat.eq_zero_or_pos (v : Fin (m + 1 + k)).val with h | h
    · exact absurd (Fin.ext h) hv
    · exact h
  set i := (v : Fin (m + 1 + k)).val with hi
  by_cases hin : i ≤ m + 1
  · -- the clique, and the first vertex of the tail, all see the centre `0`
    refine ⟨(⟨0, by omega⟩ : Fin (m + 1 + k)), show 0 < i by omega, ?_⟩
    rw [CGraph.lollipop_adj_val]
    refine ⟨show i ≠ 0 by omega, Or.inr ?_⟩
    show (0, i) ∈ CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · exact List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨by omega, by omega⟩)
    · exact List.mem_append_right _
        ((CGraph.mem_legEdges _ _ _ _ _).2 (Or.inl ⟨rfl, by omega, by omega⟩))
  · -- further along the tail, the predecessor
    refine ⟨(⟨i - 1, by omega⟩ : Fin (m + 1 + k)), show i - 1 < i by omega, ?_⟩
    rw [CGraph.lollipop_adj_val]
    refine ⟨show i ≠ i - 1 by omega, Or.inr ?_⟩
    show (i - 1, i) ∈ CGraph.cliqueEdges (m + 1) ++ CGraph.legEdges 0 (m + 1) k
    exact List.mem_append_right _
      ((CGraph.mem_legEdges _ _ _ _ _).2 (Or.inr ⟨by omega, by omega, by omega⟩))

theorem numComponents_lollipop (m k : ℕ) : (lollipop (m + 1) k).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_lollipop m k)

/-- A double star is connected: every leaf sees its own hub, and the two hubs see each other. -/
theorem isConnected_doubleStar (m n : ℕ) : IsConnected (doubleStar m n) := by
  unfold IsoGraph.doubleStar
  rw [IsoGraph.isConnected_mk]
  refine CGraph.isConnected_of_rank (fun v ↦ (v : Fin (2 + m + n)).val)
    (⟨0, by omega⟩ : Fin (2 + m + n)) fun v hv ↦ ?_
  have hlt := (v : Fin (2 + m + n)).isLt
  have hv0 : 0 < (v : Fin (2 + m + n)).val := by
    rcases Nat.eq_zero_or_pos (v : Fin (2 + m + n)).val with h | h
    · exact absurd (Fin.ext h) hv
    · exact h
  set i := (v : Fin (2 + m + n)).val with hi
  by_cases hleft : i < 2 + m
  · -- the hub `1` and the leaves on its side see `0`
    refine ⟨(⟨0, by omega⟩ : Fin (2 + m + n)), show 0 < i by omega, ?_⟩
    rw [CGraph.doubleStar_adj_val]
    refine ⟨show i ≠ 0 by omega, ?_⟩
    rcases Nat.lt_or_ge i 2 with h | h
    · exact Or.inr (Or.inl ⟨show (0 : ℕ) = 0 from rfl, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨show (0 : ℕ) = 0 from rfl, by omega, by omega⟩))
  · -- the leaves on the other side see the hub `1`
    refine ⟨(⟨1, by omega⟩ : Fin (2 + m + n)), show 1 < i by omega, ?_⟩
    rw [CGraph.doubleStar_adj_val]
    exact ⟨show i ≠ 1 by omega,
      Or.inr (Or.inr (Or.inr ⟨show (1 : ℕ) = 1 from rfl, by omega, by omega⟩))⟩

theorem numComponents_doubleStar (m n : ℕ) : (doubleStar m n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_doubleStar m n)

/-- A double star has `m + n + 1` edges on `m + n + 2` vertices and is connected. -/
theorem isTree_doubleStar (m n : ℕ) : IsTree (doubleStar m n) := by
  exact (IsoGraph.isTree_iff (doubleStar m n)).mpr ⟨isConnected_doubleStar m n,
      by rw [E_doubleStar, V_doubleStar]; omega⟩

theorem girth_doubleStar (m n : ℕ) : (doubleStar m n).girth = 0 := by
  rw [girth_eq_zero_iff]
  exact (isTree_iff_isConnected_and_isAcyclic _).mp (isTree_doubleStar m n) |>.2

/-- The central edge is the largest clique in a tree. -/
theorem cliqueNum_doubleStar (m n : ℕ) : (doubleStar m n).cliqueNum = 2 := by
  apply cliqueNum_of_isTree (h := isTree_doubleStar m n)
  show 2 ≤ (doubleStar m n).V
  simp
  omega

theorem chromNum_doubleStar (m n : ℕ) : (doubleStar m n).chromNum = 2 := by
  simp only [doubleStar, IsoGraph.chromNum_mk]
  rw [CGraph.chromNum_eq_iff]
  -- Goal: (CGraph.doubleStar m n).toSimple.Colorable 2 ∧ ∀ m_1, ... → 2 ≤ m_1
  constructor
  · rw [← CGraph.isBipartite_iff_colorable]
    -- Construct a 2-coloring: vertices 0 and ≥ 2+m get color true,
    -- vertices 1 and 2..2+m-1 get color false.
    set c : (CGraph.doubleStar m
        n).V → Bool := fun v => if v.val = 0 ∨ 2 + m ≤ v.val then true else false
    refine ⟨c, ?_⟩
    intro a b hab
    rw [CGraph.doubleStar_adj_val] at hab
    have ha_val : a.val < 2 + m + n := a.isLt
    have hb_val : b.val < 2 + m + n := b.isLt
    simp only [c]
    -- The goal is about decide on Nat propositions given Nat hypotheses from adj_val.
    -- We case-split on the 6 cases from the disjunction using ` omega`-friendly approach.
    -- First, rewrite the Bool goal into a Prop goal.
    have key : (a.val = 0 ∨ 2 + m ≤ a.val) ↔ ¬(b.val = 0 ∨ 2 + m ≤ b.val) := by
      constructor
      · intro ha; by_contra hb; omega
      · intro hb; by_contra ha; push_neg at ha; omega
    show (if a.val = 0 ∨ 2 + m ≤ a.val then true else
        false) ≠ if b.val = 0 ∨ 2 + m ≤ b.val then true else false
    split <;> simp_all
  · intro m_1 hcol
    have hadj : (CGraph.doubleStar m n).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      simp [CGraph.doubleStar_adj_val]
    have h := CGraph.two_le_chromNum_of_adj hadj
    rw [CGraph.le_chromNum_iff] at h
    exact h m_1 hcol

/-- The two centres dominate, and one vertex cannot. -/
theorem domNum_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).domNum = 2 := by
  simp only [IsoGraph.doubleStar, IsoGraph.domNum_mk]
  let G := CGraph.doubleStar (m + 1) (n + 1)
  -- Upper bound: {0, 1} is dominating
  have hub : G.domNum ≤ 2 := by
    let v0 : G.V := ⟨0, by omega⟩
    let v1 : G.V := ⟨1, by omega⟩
    have hdom : G.IsDominatingSet {v0, v1} := by
      intro v
      simp only [v0, v1]
      by_cases hv0 : v = ⟨0, by omega⟩
      · exact Or.inl (by simp [hv0])
      · by_cases hv1 : v = ⟨1, by omega⟩
        · exact Or.inl (by simp [hv1])
        · right
          have hv0' : v.val ≠ 0 := by intro h; apply hv0; exact Fin.ext h
          have hv1' : v.val ≠ 1 := by intro h; apply hv1; exact Fin.ext h
          by_cases hpend0 : 2 ≤ v.val ∧ v.val < 2 + (m + 1)
          · exact ⟨v0, by simp [v0], by
              rw [CGraph.doubleStar_adj_val]
              simp [v0, hv0']
              omega⟩
          · push_neg at hpend0
            have hpend1 : 2 + (m + 1) ≤ v.val ∧ v.val < 2 + (m + 1) + (n + 1) := by omega
            exact ⟨v1, by simp [v1], by
              rw [CGraph.doubleStar_adj_val]
              simp [v1, hv1']
              omega⟩
    have h1 := CGraph.domNum_le_card_of_isDominatingSet hdom
    have hcard : ({v0, v1} : Finset G.V).card = 2 := by
      rw [Finset.card_pair]
      exact ne_of_apply_ne (fun x => x.val) (by simp [v0, v1])
    rw [hcard] at h1
    exact h1
  -- Helper: compute .val of literal vertices in G
  let mk0 : G.V := ⟨0, by omega⟩
  let mk1 : G.V := ⟨1, by omega⟩
  let mkpend0 : Fin (m + 1) → G.V := fun i => ⟨2 + i.val, by omega⟩
  let mkpend1 : Fin (n + 1) → G.V := fun i => ⟨2 + (m + 1) + i.val, by omega⟩
  have hval_0 : mk0.val = 0 := rfl
  have hval_1 : mk1.val = 1 := rfl
  have hval_pend0 : ∀ (i : Fin (m + 1)), (mkpend0 i).val = 2 + (i : ℕ) := by
    intro i; show (⟨2 + i.val, by omega⟩ : Fin (2 + (m + 1) + (n + 1))).val = 2 + (i : ℕ); rfl
  have hval_pend1 : ∀ (i : Fin (n + 1)), (mkpend1 i).val = 2 + (m + 1) + (i : ℕ) := by
    intro i; show (⟨2 + (m + 1) + i.val, by omega⟩ : Fin (2 + (m + 1) + (n + 1))).val = 2 + (m +
        1) + (i : ℕ); rfl
  -- No vertex is universal in doubleStar (m+1) (n+1)
  have huniv : ∀ v : G.V, ∃ u : G.V, u ≠ v ∧ ¬G.Adj v u := by
    intro v
    by_cases hv0 : v.val = 0
    · -- v = mk0; pick mkpend1 ⟨0,...⟩ which is not adj to mk0... wait, pendants of 1 are not adj to
      -- 0.
      refine ⟨mkpend1 ⟨0, by omega⟩, ?_, ?_⟩
      · intro h; rw [← h] at hv0; simp [hval_pend1] at hv0
      · have hmk10 : (mkpend1 ⟨0, by omega⟩ : G.V).val = 2 + (m + 1) + 0 := by
          simpa using hval_pend1 ⟨0, by omega⟩
        rw [CGraph.doubleStar_adj_val, hmk10, hv0]
        omega
    · by_cases hv1 : v.val = 1
      · -- v = mk1; pick mkpend0 ⟨0,...⟩ not adj to mk1
        refine ⟨mkpend0 ⟨0, by omega⟩, ?_, ?_⟩
        · intro h; rw [← h] at hv1; simp [hval_pend0] at hv1
        · rw [CGraph.doubleStar_adj_val]
          simp [hval_pend0, hv1]
      · -- v is a pendant of 0 or 1, but not 0 or 1 itself. v.val ≥ 2.
        by_cases hvpend0 : v.val < 2 + (m + 1)
        · -- v is a pendant of 0; pick mk1 (center 1) — pendants of 0 are not adj to 1
          refine ⟨mk1, ?_, ?_⟩
          · intro h; rw [← h] at hv1; simp [hval_1] at hv1
          · rw [CGraph.doubleStar_adj_val]
            simp [hval_1, hv0, hv1, hvpend0]
        · -- v.val ≥ 2+(m+1), so v is a pendant of 1; pick mk0
          refine ⟨mk0, ?_, ?_⟩
          · intro h; rw [← h] at hv0; simp [hval_0] at hv0
          · rw [CGraph.doubleStar_adj_val]
            simp [hval_0, hv0]
            omega
  have hlow : G.domNum ≠ 1 := by
    intro h
    rw [CGraph.domNum_eq_one_iff] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨u, hne, hna⟩ := huniv v
    exact hna (hv u hne)
  -- Combine
  have hpos : 0 < G.domNum := by
    apply CGraph.domNum_pos
    exact FinEnum.card_pos_iff.mpr ⟨⟨0, by omega⟩⟩
  have h1 : 1 < G.domNum := by omega
  change G.domNum = 2
  omega

/-- Match each centre to one of its own pendants; a third edge would need a third centre. -/
theorem matchNum_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).matchNum = 2 := by
  apply le_antisymm
  · -- matchNum ≤ 2 via coverNum ≤ 2
    apply le_trans (matchNum_le_coverNum _) _
    simp only [IsoGraph.doubleStar, coverNum_mk]
    -- {0, 1} is a vertex cover of doubleStar (m+1)(n+1)
    let S : Set (CGraph.doubleStar (m + 1) (n + 1)).V := {⟨0, by omega⟩, ⟨1, by omega⟩}
    have hvc : SimpleGraph.IsVertexCover (CGraph.doubleStar (m + 1) (n + 1)).toSimple S := by
      intro u v huv
      rw [CGraph.toSimple_adj] at huv
      rw [CGraph.doubleStar_adj_val] at huv
      rcases huv with ⟨hne, hcases⟩
      -- In all 6 cases, either u.1 ∈ {0,1} or v.1 ∈ {0,1}
      have : u.1 = 0 ∨ u.1 = 1 ∨ v.1 = 0 ∨ v.1 = 1 := by omega
      set e0 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨0, by omega⟩
      set e1 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨1, by omega⟩
      rcases this with h | h | h | h
      · left; rw [Set.mem_insert_iff]; exact Or.inl (Fin.ext (h.trans (by simp)))
      · left; rw [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Fin.ext (h.trans
          (by simp)))
      · right; rw [Set.mem_insert_iff]; exact Or.inl (Fin.ext (h.trans (by simp)))
      · right; rw [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Fin.ext (h.trans
          (by simp)))
    have hne : (⟨0, by omega⟩ : (CGraph.doubleStar (m + 1) (n + 1)).V) ≠ ⟨1, by omega⟩ := by
      intro h; simp at h
    have henc : S.encard = 2 := by
      rw [show S = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Set _) from rfl]
      rw [Set.encard_pair hne]
    rw [CGraph.coverNum]
    have h1 := hvc.vertexCoverNum_le.trans henc.le
    exact ENat.toNat_le_toNat h1 (by simp)
  · -- 2 ≤ matchNum: exhibit two disjoint edges
    rw [matchNum_eq, IsoGraph.doubleStar, lineGraph_mk, indepNum_mk]
    let G := CGraph.doubleStar (m + 1) (n + 1)
    -- Edge e1 = s(⟨0,...⟩, ⟨2,...⟩) is in G
    let ve0 : G.V := ⟨0, by omega⟩
    let ve2 : G.V := ⟨2, by omega⟩
    let ve1 : G.V := ⟨1, by omega⟩
    let ve2m1 : G.V := ⟨2 + (m + 1), by omega⟩
    have he1_mem : s(ve0, ve2) ∈ G.toSimple.edgeSet := by
      simp [G, SimpleGraph.mem_edgeSet, CGraph.toSimple]
      rw [CGraph.doubleStar_adj_val]
      simp [ve0, ve2]
    have he2_mem : s(ve1, ve2m1) ∈ G.toSimple.edgeSet := by
      simp [G, SimpleGraph.mem_edgeSet, CGraph.toSimple]
      rw [CGraph.doubleStar_adj_val]
      simp [ve1, ve2m1]
      omega
    let ev1 : (CGraph.lineGraph G).V := ⟨s(ve0, ve2), he1_mem⟩
    let ev2 : (CGraph.lineGraph G).V := ⟨s(ve1, ve2m1), he2_mem⟩
    -- They're not adjacent in lineGraph: edges are disjoint
    have hve0_ne_ve1 : ve0 ≠ ve1 := by
      intro h; have := congr_arg Fin.val h; simp [ve0, ve1] at this
    have hve0_ne_ve2m1 : ve0 ≠ ve2m1 := by
      intro h; have := congr_arg Fin.val h; simp [ve0, ve2m1] at this; omega
    have hve2_ne_ve1 : ve2 ≠ ve1 := by
      intro h; have := congr_arg Fin.val h; simp [ve2, ve1] at this
    have hve2_ne_ve2m1 : ve2 ≠ ve2m1 := by
      intro h; have := congr_arg Fin.val h; simp [ve2, ve2m1] at this
    have he_disjoint : ¬ ∃ v : G.V, v ∈ (s(ve0, ve2) : Sym2 G.V) ∧ v ∈ (s(ve1, ve2m1) : Sym2
        G.V) := by
      intro ⟨v, hv1, hv2⟩
      simp at hv1 hv2
      rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
      · exact hve0_ne_ve1 h
      · exact hve0_ne_ve2m1 h
      · exact hve2_ne_ve1 h
      · exact hve2_ne_ve2m1 h
    have hve0_not_in_ev2 : ve0 ∉ (s(ve1, ve2m1) : Sym2 G.V) := by
      intro hv
      simp at hv
      rcases hv with h | h <;> [exact hve0_ne_ve1 h; exact hve0_ne_ve2m1 h]
    have hne : ev1 ≠ ev2 := by
      intro h
      have h1 : (s(ve0, ve2) : Sym2 G.V) = s(ve1, ve2m1) := congrArg Subtype.val h
      have hmem1 : ve0 ∈ (s(ve0, ve2) : Sym2 G.V) := Sym2.mem_mk_left _ _
      rw [h1] at hmem1
      exact hve0_not_in_ev2 hmem1
    have hna : ¬ (CGraph.lineGraph G).Adj ev1 ev2 := by
      rw [CGraph.lineGraph_adj]
      have hdisj : ¬ ∃ v : G.V, v ∈ (↑ev1.1 : Sym2 G.V) ∧ v ∈ (↑ev2.1 : Sym2 G.V) := he_disjoint
      simp [hne, hdisj]
    exact CGraph.two_le_indepNum hne hna

/-- The far end of the tail is the unique pendant. -/
theorem minDeg_lollipop (m k : ℕ) : minDeg (lollipop (m + 2) (k + 1)) = 1 := by
  change (CGraph.lollipop (m + 2) (k + 1)).minDeg = 1
  refine le_antisymm ?_ (CGraph.le_minDeg_of_forall ⟨0, by omega⟩ fun v ↦ ?_)
  · have hlast : ∀ v : (CGraph.lollipop (m + 2) (k + 1)).V, v.1 = m + 2 + k →
        (CGraph.lollipop (m + 2) (k + 1)).toSimple.degree v ≤ 1 := by
      intro v hv
      refine le_trans (CGraph.degree_ofEdges_le (m + 2 + (k + 1)) _ v
        [if k = 0 then 0 else m + 1 + k] ?_) (by simp)
      intro w hne hw
      simp only [hv, List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges] at hw hne
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      split_ifs <;> omega
    exact le_trans (CGraph.minDeg_le_degree _ _) (hlast ⟨m + 2 + k, by omega⟩ rfl)
  · refine le_trans (by simp) (CGraph.le_degree_ofEdges (m + 2 + (k + 1)) _ v
      [if v.1 = 0 then 1 else if v.1 ≤ m + 2 then 0 else v.1 - 1] (by simp) ?_)
    intro w hw
    have hlt : v.1 < m + 2 + (k + 1) := v.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
    simp only [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges]
    split_ifs <;> omega

/-- The junction has the `m + 1` clique edges plus the first tail edge. -/
theorem maxDeg_lollipop (m k : ℕ) : maxDeg (lollipop (m + 2) (k + 1)) = m + 2 := by
  change (CGraph.lollipop (m + 2) (k + 1)).maxDeg = m + 2
  have hdeg0 : ∀ v : (CGraph.lollipop (m + 2) (k + 1)).V, v.1 = 0 →
      (CGraph.lollipop (m + 2) (k + 1)).toSimple.degree v = m + 2 := by
    intro v hv
    have hd := CGraph.degree_ofEdges (m + 2 + (k + 1)) _ v
      ((List.range (m + 2)).map fun i ↦ 1 + i)
      (List.Nodup.map (fun a b hab ↦ by omega) List.nodup_range)
      (by
        intro w hw
        rw [List.mem_map_add_range] at hw
        omega)
      (by rw [hv, List.mem_map_add_range]; omega)
      (by
        intro w hne
        rw [hv]
        simp only [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges,
          List.mem_map_add_range, true_and]
        omega)
    simpa using hd
  refine le_antisymm (CGraph.maxDeg_le_of_forall fun v ↦ ?_)
    (le_of_eq_of_le (hdeg0 ⟨0, by omega⟩ rfl).symm (CGraph.degree_le_maxDeg _ _))
  rcases Nat.lt_or_ge v.1 (m + 2) with hv | hv
  · refine le_trans (CGraph.degree_ofEdges_le (m + 2 + (k + 1)) _ v
      (((List.range (m + 2)).erase v.1) ++ [m + 2]) ?_) ?_
    · intro w hne hw
      simp only [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges] at hw
      rw [List.mem_append, List.mem_erase_of_ne hne, List.mem_range, List.mem_singleton]
      omega
    · rw [List.length_append, List.length_erase_of_mem (List.mem_range.2 hv), List.length_range,
        List.length_singleton]
      omega
  · refine le_trans (CGraph.degree_ofEdges_le (m + 2 + (k + 1)) _ v
      [if v.1 = m + 2 then 0 else v.1 - 1, v.1 + 1] ?_) (by simp)
    intro w hne hw
    have hlt : v.1 < m + 2 + (k + 1) := v.isLt
    simp only [List.mem_append, CGraph.mem_cliqueEdges, CGraph.mem_legEdges] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> omega

/-- An even cycle with a tail is bipartite, and it has an edge. -/
theorem chromNum_tadpole_even (m k : ℕ) : (tadpole (2 * m + 4) k).chromNum = 2 := by
  refine chromNum_eq_two_iff.mpr ⟨?_, ?_⟩
  · have := isBipartite_tadpole_even (m + 2) k
    rwa [show 2 * (m + 2) = 2 * m + 4 from by ring] at this
  · have := E_tadpole (2 * m + 1) k
    rw [show 2 * m + 1 + 3 = 2 * m + 4 from by ring] at this
    omega

/-- A spider is a tree, so it has one edge fewer than it has vertices. -/
theorem E_spider (legs : List ℕ) : (spider legs).E = legs.sum := by
  rw [spider_def, E_mk]
  -- Helper: pathEdges length
  have hpath_edges_len : ∀ (l : List ℕ), l.length ≥ 1 → (CGraph.pathEdges
      l).length = l.length - 1 := by
    intro l hl
    induction l with
    | nil => exfalso; simp at hl
    | cons a l ih =>
      cases l with
      | nil => simp [CGraph.pathEdges]
      | cons b l' =>
        simp [CGraph.pathEdges]
        have ih2 := ih (by simp)
        simp [List.length_cons] at ih2 ⊢
        omega
  have hleg_edges_len : ∀ (v off k : ℕ), (CGraph.legEdges v off k).length = k := by
    intro v off k
    simp only [CGraph.legEdges]
    have : (v :: (List.range k).map (fun x => x + off)).length = k + 1 := by
      simp [List.length_cons, List.length_map, List.length_range]
    rw [hpath_edges_len _ (by omega)]
    omega
  have hlen : ∀ (off : ℕ) (ks : List ℕ), (CGraph.spiderEdges off ks).length = ks.sum := by
    intro off ks; induction ks generalizing off with
    | nil => simp [CGraph.spiderEdges]
    | cons k rest ih =>
      simp [CGraph.spiderEdges, List.length_append, hleg_edges_len, ih, List.sum_cons]
  have hlts : ∀ (off : ℕ) (ks : List ℕ), 0 < off →
      (∀ p ∈ CGraph.spiderEdges off ks, p.1 < p.2) := by
    intro off ks hoff
    induction ks generalizing off with
    | nil => simp [CGraph.spiderEdges]
    | cons k rest ih =>
      simp [CGraph.spiderEdges, List.mem_append]
      intro a b hp
      rcases hp with h | h
      · rcases h with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩
        · omega
        · omega
      · exact ih (off + k) (by omega) (a, b) h
  have hbounds2 : ∀ (off : ℕ) (ks : List ℕ), 0 < off →
      (∀ p ∈ CGraph.spiderEdges off ks, p.2 < off + ks.sum) := by
    intro off ks hoff p hpq
    exact (CGraph.mem_spiderEdges_bound off ks p.1 p.2 hpq).2.2
  -- legEdges 0 off k is nodup for any off, k (from mem_legEdges, edges are (0,off) and (p,p+1) for
  -- off≤p<off+k-1, all distinct)
  have hleg_nodup : ∀ (off k : ℕ), (CGraph.legEdges 0 off k).Nodup := by
    intro off k
    induction k with
    | zero => simp [CGraph.legEdges_zero]
    | succ j ih =>
      simp [CGraph.legEdges_succ]
      have inj : Function.Injective (fun i : ℕ => (i + off, i + 1 + off)) :=
        fun a b h => by injection h with h1 h2; omega
      exact List.Nodup.map inj List.nodup_range
  have hnoup : ∀ (off : ℕ) (ks : List ℕ), 0 < off →
      (CGraph.spiderEdges off ks).Nodup := by
    intro off ks hoff
    induction ks generalizing off with
    | nil => simp [CGraph.spiderEdges]
    | cons k rest ih =>
      rw [CGraph.spiderEdges]
      apply List.Nodup.append (hleg_nodup off k) (ih (off + k) (by omega))
      intro p hmem_leg hmem_spider
      rw [CGraph.mem_legEdges] at hmem_leg
      have hb := CGraph.mem_spiderEdges_bound (off + k) rest p.1 p.2 hmem_spider
      rcases hmem_leg with ⟨h1, h2, hk⟩ | ⟨h1, h2, h3⟩
      · omega
      · omega
  unfold CGraph.spider
  rw [CGraph.E_ofEdges (1 + legs.sum) (CGraph.spiderEdges 1 legs)
    (hlts 1 legs (by omega))
    (hbounds2 1 legs (by omega))
    (hnoup 1 legs (by omega))]
  rw [hlen 1 legs]

/-- **Hanging pendant vertices off a cycle adds one edge per pendant.**  A cycle edge keeps both
endpoints below `m + 3`, a pendant edge runs from below `m + 3` to a fresh vertex at or above it,
so the two lists are disjoint and neither contains a reversed pair. -/
theorem E_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    (cyclePendant (m + 3) ks).E = m + 3 + ks.sum := by
  simp only [IsoGraph.cyclePendant, IsoGraph.E_mk, CGraph.cyclePendant]
  have hcyc : ∀ p ∈ CGraph.cycleEdges (m + 3), p.1 < m + 3 ∧ p.2 < m + 3 := by
    intro p hp
    rw [CGraph.mem_cycleEdges] at hp
    omega
  have hpen : ∀ p ∈ CGraph.pendantEdges 0 (m + 3) ks,
      p.1 < m + 3 ∧ m + 3 ≤ p.2 ∧ p.2 < m + 3 + ks.sum := by
    intro p hp
    have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p.1 p.2 hp
    omega
  have hdisj : List.Disjoint (CGraph.cycleEdges (m + 3)) (CGraph.pendantEdges 0 (m + 3) ks) := by
    intro p hp hq
    have := hcyc p hp
    have := hpen p hq
    omega
  rw [CGraph.E_ofEdges_of_nodup (n := m + 3 + ks.sum)
    (fun p hp ↦ by
      rcases List.mem_append.mp hp with hp | hp
      · have := hcyc p hp; omega
      · have := hpen p hp; omega)
    (fun p hp ↦ by
      rcases List.mem_append.mp hp with hp | hp
      · rw [CGraph.mem_cycleEdges] at hp; omega
      · have := hpen p hp; omega)
    (fun p hp hrev ↦ by
      rcases List.mem_append.mp hp with hp | hp <;>
        rcases List.mem_append.mp hrev with hrev | hrev
      · rw [CGraph.mem_cycleEdges] at hp hrev; omega
      · have := hcyc p hp; have := hpen _ hrev; omega
      · have := hpen p hp; have := hcyc _ hrev; omega
      · have := hpen p hp; have := hpen _ hrev; omega)
    (List.Nodup.append (CGraph.cycleEdges_nodup _) (CGraph.pendantEdges_nodup _ _ _) hdisj)]
  simp

/-- A cycle with pendant vertices stays connected: each pendant hangs off a cycle vertex, whose
number is smaller, and the cycle descends to `0`. -/
theorem isConnected_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    IsConnected (cyclePendant (m + 3) ks) := by
  unfold IsoGraph.cyclePendant
  rw [IsoGraph.isConnected_mk]
  refine CGraph.isConnected_of_rank (fun v ↦ (v : Fin (m + 3 + ks.sum)).val)
    (⟨0, by omega⟩ : Fin (m + 3 + ks.sum)) fun v hv ↦ ?_
  have hlt := (v : Fin (m + 3 + ks.sum)).isLt
  have hv0 : 0 < (v : Fin (m + 3 + ks.sum)).val := by
    rcases Nat.eq_zero_or_pos (v : Fin (m + 3 + ks.sum)).val with h | h
    · exact absurd (Fin.ext h) hv
    · exact h
  set i := (v : Fin (m + 3 + ks.sum)).val with hi
  by_cases hcyc : i < m + 3
  · -- around the cycle, the predecessor
    refine ⟨(⟨i - 1, by omega⟩ : Fin (m + 3 + ks.sum)), show i - 1 < i by omega, ?_⟩
    rw [CGraph.cyclePendant_adj_val]
    refine ⟨show i ≠ i - 1 by omega, Or.inr ?_⟩
    show (i - 1, i) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m + 3) ks
    exact List.mem_append_left _ ((CGraph.mem_cycleEdges _ _ _).2 (Or.inl ⟨by omega, by omega⟩))
  · -- a pendant vertex hangs off a cycle vertex, which has the smaller number
    obtain ⟨p, hp⟩ := CGraph.exists_mem_pendantEdges 0 (m + 3) ks i (by omega) (by omega)
    have hb := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p i hp
    refine ⟨(⟨p, by omega⟩ : Fin (m + 3 + ks.sum)), show p < i by omega, ?_⟩
    rw [CGraph.cyclePendant_adj_val]
    refine ⟨show i ≠ p by omega, Or.inr ?_⟩
    show (p, i) ∈ CGraph.cycleEdges (m + 3) ++ CGraph.pendantEdges 0 (m + 3) ks
    exact List.mem_append_right _ hp

theorem numComponents_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    (cyclePendant (m + 3)
        ks).numComponents = 1 := numComponents_eq_one_of_isConnected (isConnected_cyclePendant m ks
            h)

/-- The far end of any leg is a pendant. -/
theorem minDeg_spider (legs : List ℕ) (h : 0 < legs.sum) : minDeg (spider legs) = 1 := by
  simp only [IsoGraph.spider, IsoGraph.minDeg_mk]
  refine le_antisymm ?_ (CGraph.le_minDeg_of_forall ⟨0, by omega⟩ fun v ↦ ?_)
  · obtain ⟨p, hp⟩ := CGraph.exists_mem_spiderEdges_snd 1 legs legs.sum (by omega) (by omega)
    have hlast : ∀ v : (CGraph.spider legs).V, v.1 = legs.sum →
        (CGraph.spider legs).toSimple.degree v ≤ 1 := by
      intro v hv
      refine le_trans (CGraph.degree_ofEdges_le (1 + legs.sum) _ v [p] ?_) (by simp)
      intro w hne hw
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hw with hw | hw
      · exfalso
        have h1 := CGraph.spiderEdges_lt 1 legs (by omega) _ _ hw
        have h2 := CGraph.mem_spiderEdges_bound 1 legs _ _ hw
        omega
      · exact CGraph.spiderEdges_snd_unique 1 legs (by omega) w p _ (hv ▸ hw) hp
    exact le_trans (CGraph.minDeg_le_degree _ _) (hlast ⟨legs.sum, by omega⟩ rfl)
  · rcases Nat.eq_zero_or_pos v.1 with hv | hv
    · obtain ⟨q, hq⟩ := CGraph.exists_mem_spiderEdges_zero 1 legs h
      have hb := CGraph.mem_spiderEdges_bound 1 legs 0 q hq
      refine le_trans (by simp) (CGraph.le_degree_ofEdges (1 + legs.sum) _ v [q] (by simp) ?_)
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact ⟨by omega, by omega, Or.inl (by rw [hv]; exact hq)⟩
    · have hlt : v.1 < 1 + legs.sum := v.isLt
      obtain ⟨p, hp⟩ := CGraph.exists_mem_spiderEdges_snd 1 legs v.1 (by omega) (by omega)
      have hb := CGraph.mem_spiderEdges_bound 1 legs p v.1 hp
      have hpv := CGraph.spiderEdges_lt 1 legs (by omega) p v.1 hp
      refine le_trans (by simp) (CGraph.le_degree_ofEdges (1 + legs.sum) _ v [p] (by simp) ?_)
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact ⟨by omega, by omega, Or.inr hp⟩

/-- A pendant vertex has degree one. -/
theorem minDeg_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) (h2 : 0 < ks.sum) :
    minDeg (cyclePendant (m + 3) ks) = 1 := by
  simp only [IsoGraph.cyclePendant, IsoGraph.minDeg_mk]
  refine le_antisymm ?_ (CGraph.le_minDeg_of_forall ⟨0, by omega⟩ fun v ↦ ?_)
  · obtain ⟨p, hp⟩ := CGraph.exists_mem_pendantEdges 0 (m + 3) ks (m + 3 + ks.sum - 1)
      (by omega) (by omega)
    have hlast : ∀ v : (CGraph.cyclePendant (m + 3) ks).V, v.1 = m + 3 + ks.sum - 1 →
        (CGraph.cyclePendant (m + 3) ks).toSimple.degree v ≤ 1 := by
      intro v hv
      refine le_trans (CGraph.degree_ofEdges_le (m + 3 + ks.sum) _ v [p] ?_) (by simp)
      intro w hne hw
      simp only [hv, List.mem_append] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hw with hw | hw <;> rcases hw with hw | hw
      · rw [CGraph.mem_cycleEdges] at hw
        omega
      · have := CGraph.mem_pendantEdges_bound 0 (m + 3) ks _ _ hw
        omega
      · rw [CGraph.mem_cycleEdges] at hw
        omega
      · exact CGraph.pendantEdges_snd_unique 0 (m + 3) ks w p _ hw hp
    exact le_trans (CGraph.minDeg_le_degree _ _) (hlast ⟨m + 3 + ks.sum - 1, by omega⟩ rfl)
  · rcases Nat.lt_or_ge v.1 (m + 3) with hv | hv
    · refine le_trans (by simp) (CGraph.le_degree_ofEdges (m + 3 + ks.sum) _ v
        [if v.1 + 1 < m + 3 then v.1 + 1 else 0] (by simp) ?_)
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
      refine Or.inl (List.mem_append_left _ ?_)
      rw [CGraph.mem_cycleEdges]
      split_ifs <;> omega
    · have hlt : v.1 < m + 3 + ks.sum := v.isLt
      obtain ⟨p, hp⟩ := CGraph.exists_mem_pendantEdges 0 (m + 3) ks v.1 hv (by omega)
      have hb := CGraph.mem_pendantEdges_bound 0 (m + 3) ks p v.1 hp
      refine le_trans (by simp) (CGraph.le_degree_ofEdges (m + 3 + ks.sum) _ v [p]
        (by simp) ?_)
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact ⟨by omega, by omega, Or.inr (List.mem_append_right _ hp)⟩

/-- The two centres are a vertex cover, and one vertex is not. -/
theorem coverNum_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).coverNum = 2 := by
  rw [coverNum_eq, V_doubleStar, indepNum_doubleStar]
  omega

/-- Only the two centres carry any edges, so the rest of a clique cover is singletons. -/
theorem cliqueCoverNum_doubleStar (m n : ℕ) :
    (doubleStar (m + 1) (n + 1)).cliqueCoverNum = m + n + 2 := by
  have hlow : m + n + 2 ≤ (doubleStar (m + 1) (n + 1)).cliqueCoverNum := by
    rw [← indepNum_doubleStar]
    exact indepNum_le_cliqueCoverNum _
  have h.high : (doubleStar (m + 1) (n + 1)).cliqueCoverNum ≤ m + n + 2 := by
    have hV : (doubleStar (m + 1) (n + 1)).V = m + n + 4 := by
      simp [IsoGraph.doubleStar, IsoGraph.V_mk, CGraph.card_doubleStar]; omega
    have hm := matchNum_doubleStar m n
    have h1 := cliqueCoverNum_le_V_sub_matchNum (doubleStar (m + 1) (n + 1))
    rw [hV, hm] at h1
    omega
  exact le_antisymm h.high hlow

/-- An odd cycle needs three colours, and the tail needs no more. -/
theorem chromNum_tadpole_odd (m k : ℕ) : (tadpole (2 * m + 3) k).chromNum = 3 := by
  rw [tadpole_def, chromNum_mk]
  rw [CGraph.chromNum_eq_iff]
  set G := CGraph.tadpole (2 * m + 3) k
  refine ⟨?_, ?_⟩
  · -- Colorable with 3 colors
    -- Coloring function: 0 ↦ 2, i (1 ≤ i < 2m+3) ↦ i%2, path vertices ↦ alternating 0,1
    let c : Fin (2 * m + 3 + k) → Fin 3 := fun i =>
      if hi : i.val < 2 * m + 3 then
        if hi0 : i.val = 0 then
          Fin.last 2
        else
          Fin.mk (i.val % 2) (by omega)
      else
        Fin.mk ((i.val - (2 * m + 3)) % 2) (by omega)
    refine ⟨c, ?_⟩
    have hc_ne_cycle : ∀ u v : Fin (2 * m + 3 + k),
        (u.val, v.val) ∈ CGraph.cycleEdges (2 * m + 3) → (c u).val ≠ (c v).val := by
      intro u v hmem
      simp only [c]
      rw [CGraph.mem_cycleEdges] at hmem
      rcases hmem with ⟨hv1, hu1⟩ | ⟨hu1, hv0⟩
      · simp only [hv1, hu1]
        split_ifs <;> simp <;> omega
      · simp only [hv0]
        have hu_val : (u : ℕ) = 2 * m + 2 := by omega
        simp [hu_val]
    have hc_ne_leg : ∀ u v : Fin (2 * m + 3 + k),
        (u.val, v.val) ∈ CGraph.legEdges 0 (2 * m + 3) k → (c u).val ≠ (c v).val := by
      intro u v hmem
      simp only [c]
      rw [CGraph.mem_legEdges] at hmem
      rcases hmem with ⟨hu0, hv_off, hkpos⟩ | ⟨hlop, hv_eq, hunil⟩
      · -- (u,v) = (0, 2*m+3), edge from cycle center to path start
        simp only [hu0, hv_off]
        split_ifs <;> simp <;> omega
      · -- (u,v) = (p, p+1) on the path, p ≥ 2*m+3
        simp only [hv_eq]
        split_ifs <;> simp <;> omega
    have hc_ne : ∀ u v : Fin (2 * m + 3 + k),
        (u ≠ v) → ((u.val, v.val) ∈ CGraph.cycleEdges (2 * m + 3) ++ CGraph.legEdges 0 (2 * m + 3)
            k ∨
          (v.val, u.val) ∈ CGraph.cycleEdges (2 * m + 3) ++ CGraph.legEdges 0 (2 * m + 3) k) →
        (c u).val ≠ (c v).val := by
      intro u v hne hmem
      rcases hmem with hmem | hmem
      · rcases List.mem_append.mp hmem with hmem | hmem
        · exact hc_ne_cycle u v hmem
        · exact hc_ne_leg u v hmem
      · rcases List.mem_append.mp hmem with hmem | hmem
        · exact fun h => (hc_ne_cycle v u hmem) (by rw [h])
        · exact fun h => (hc_ne_leg v u hmem) (by rw [h])
    intro u v huv
    rw [CGraph.toSimple_adj] at huv
    unfold G at huv
    rw [CGraph.tadpole_adj_val] at huv
    have hn := huv.1
    have hm := huv.2
    intro h
    exact (hc_ne u v (fun heq => hn (by rw [heq])) hm) (by rw [h])
  · -- Lower bound
    intro m_1 hm_1
    by_contra h
    push_neg at h
    have h2 : G.toSimple.Colorable 2 := by
      have : m_1 ≤ 2 := by omega
      exact hm_1.mono this
    have hbip : G.IsBipartite := (CGraph.isBipartite_iff_colorable G).mpr h2
    exact CGraph.not_isBipartite_ofEdges_of_odd_cycle
      (2 * m + 3 + k) (2 * m + 3) (CGraph.cycleEdges (2 * m + 3) ++ CGraph.legEdges 0 (2 * m + 3) k)
      (by omega) (by omega) (by omega)
      (fun p q h => Or.inl (List.mem_append_left _ h)) hbip

/-- An even cycle with pendants hung on it is bipartite and has an edge. -/
theorem chromNum_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t + 2) :
    (cyclePendant (2 * t + 2) ks).chromNum = 2 := by
  have hcgh : IsoGraph.chromNum (cyclePendant (2 * t + 2) ks) =
      (CGraph.cyclePendant (2 * t + 2) ks).chromNum := IsoGraph.chromNum_mk _
  rw [hcgh]
  -- Colorability (upper bound)
  have hc2 : (CGraph.cyclePendant (2 * t + 2) ks).toSimple.Colorable 2 := by
    refine ⟨fun i => ⟨CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks (i : Fin (2 * t + 2 +
        ks.sum)).1 % 2,
      Nat.mod_lt _ (by omega)⟩, ?_⟩
    intro x y hxy
    rw [CGraph.toSimple_adj] at hxy
    rw [CGraph.cyclePendant_adj_val] at hxy
    show ¬_ = _
    simp only [Fin.ext_iff]
    have key : ∀ p q : ℕ, (p, q) ∈ CGraph.cycleEdges (2 * t + 2) ++ CGraph.pendantEdges 0 (2 * t +
        2) ks →
        (CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks p
          + CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks q) % 2 = 1 := by
      intro p q hpq
      rw [List.mem_append] at hpq
      rcases hpq with hpq | hpq
      · rw [CGraph.mem_cycleEdges] at hpq
        rw [CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega),
          CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega)]
        omega
      · exact CGraph.pendantOwner_parity (2 * t + 2) 0 (2 * t + 2) ks p q (by omega) (by omega) hpq
    rcases hxy.2 with hm | hm
    · have hk := key x.1 y.1 hm
      intro heq
      have : (CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks x.1 +
        CGraph.pendantOwner (2 * t + 2) 0 (2 * t + 2) ks y.1) % 2 = 0 := by omega
      omega
    · have hk := key y.1 x.1 hm
      intro heq; omega
  -- Edge (lower bound)
  have hmem : (0, 1) ∈ CGraph.cycleEdges (2 * t + 2) := by
    rw [CGraph.mem_cycleEdges]
    left; omega
  have hadj : (CGraph.cyclePendant (2 * t + 2) ks).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    rw [CGraph.cyclePendant_adj_val]
    simp [hmem]
  have hge : 2 ≤ (CGraph.cyclePendant (2 * t + 2) ks).chromNum :=
    CGraph.two_le_chromNum_of_adj hadj
  exact le_antisymm (CGraph.chromNum_le_iff_colorable.mpr hc2) hge

/-- Every vertex of a spider walks down its own leg to the centre: the vertex number is a rank
in the sense of `CGraph.isConnected_of_rank`, and `CGraph.exists_mem_spiderEdges_snd` supplies
the descending neighbour. -/
theorem isConnected_spider (legs : List ℕ) : IsConnected (spider legs) := by
  unfold IsoGraph.spider
  rw [IsoGraph.isConnected_mk]
  refine CGraph.isConnected_of_rank (fun v ↦ (v : Fin (1 + legs.sum)).val)
    (⟨0, by omega⟩ : Fin (1 + legs.sum)) ?_
  intro v hv
  have hv0 : 0 < (v : Fin (1 + legs.sum)).val := by
    rcases Nat.eq_zero_or_pos (v : Fin (1 + legs.sum)).val with h | h
    · exact absurd (Fin.ext h) hv
    · exact h
  obtain ⟨p, hp⟩ :=
    CGraph.exists_mem_spiderEdges_snd 1 legs (v : Fin (1 + legs.sum)).val (by omega)
      (by have := (v : Fin (1 + legs.sum)).isLt; omega)
  have hlt : p < (v : Fin (1 + legs.sum)).val := CGraph.spiderEdges_lt 1 legs one_pos _ _ hp
  refine ⟨(⟨p, by have := (v : Fin (1 + legs.sum)).isLt; omega⟩ : Fin (1 + legs.sum)), hlt, ?_⟩
  rw [CGraph.spider_adj_val]
  exact ⟨(Nat.ne_of_lt hlt).symm, Or.inr hp⟩

theorem numComponents_spider (legs : List ℕ) : (spider legs).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_spider legs)

/-- A spider is a tree: connected, with `legs.sum` edges on `1 + legs.sum` vertices. -/
theorem isTree_spider (legs : List ℕ) : IsTree (spider legs) := by
  rw [IsoGraph.isTree_iff]
  refine ⟨isConnected_spider legs, ?_⟩
  rw [V_spider]
  suffices hE : (spider legs).E = legs.sum by omega
  show (CGraph.spider legs).E = legs.sum
  rw [CGraph.spider]
  have spider_spiderEdges_facts : ∀ (offs : ℕ) (hoffs : 1 ≤ offs) (ks : List ℕ),
      List.Nodup (CGraph.spiderEdges offs ks) ∧
      (∀ p ∈ CGraph.spiderEdges offs ks, p.1 < p.2) ∧
      (∀ p ∈ CGraph.spiderEdges offs ks, p.2 < offs + ks.sum) ∧
      List.length (CGraph.spiderEdges offs ks) = ks.sum := by
    intro offs _ks_h ks
    induction ks generalizing offs with
    | nil =>
      simp [CGraph.spiderEdges, List.sum_nil, List.length_nil]
    | cons k rest ih =>
      -- IH at offset offs+k for rest
      have hoffs_k : 1 ≤ offs + k := by omega
      obtain ⟨hnup', hlt', hbound', hlen'⟩ := ih (offs + k) hoffs_k
      -- spiderEdges offs (k :: rest) = legEdges 0 offs k ++ spiderEdges (offs + k) rest
      simp [CGraph.spiderEdges, List.sum_cons]
      -- legEdges 0 offs k properties
      have hleg_nodup : (CGraph.legEdges 0 offs k).Nodup := by
        induction k with
        | zero => simp [CGraph.legEdges_zero]
        | succ j ih' =>
          simp [CGraph.legEdges_succ]
          have : (List.range j).Nodup := List.nodup_range
          exact List.Nodup.map (fun x y h => by injection h with h1 h2; omega) this
      have hleg_lt : ∀ p ∈ CGraph.legEdges 0 offs k, p.1 < p.2 := by
        intro p hp
        rw [CGraph.mem_legEdges] at hp
        rcases hp with ⟨h1, h2, hk⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2]
        omega
      have hleg_bound : ∀ p ∈ CGraph.legEdges 0 offs k, p.2 < offs + k := by
        intro p hp
        rw [CGraph.mem_legEdges] at hp
        rcases hp with ⟨h1, h2, hk⟩ | ⟨h1, h2, h3⟩ <;> simp [h2] <;> omega
      have hleg_len : List.length (CGraph.legEdges 0 offs k) = k := by
        induction k with
        | zero => simp [CGraph.legEdges_zero]
        | succ j ih' => simp [CGraph.legEdges_succ, List.length_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Nodup
        apply List.Nodup.append hleg_nodup hnup'
        intro x hx_leg hx_spider
        have hq_lt := hleg_bound x hx_leg
        have ⟨_, hq_ge, _⟩ := CGraph.mem_spiderEdges_bound (offs + k) rest x.1 x.2 hx_spider
        omega
      · -- p.1 < p.2
        intro a b hp
        rcases hp with hp | hp
        · rcases hp with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩ <;> omega
        · exact hlt' _ hp
      · -- p.2 < offs + (k + rest.sum)
        intro a b hp
        rcases hp with hp | hp
        · rcases hp with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩ <;> omega
        · have := hbound' _ hp; omega
      · -- length
        exact hlen'
  -- Now close the main goal
  have ⟨hnup, hlt, hbound, hlen⟩ := spider_spiderEdges_facts 1 (by omega) legs
  rw [CGraph.E_ofEdges _ _ hlt hbound hnup, hlen]

theorem girth_spider (legs : List ℕ) : (spider legs).girth = 0 := by
  rw [girth_eq_zero_iff]
  exact (isTree_spider legs).2

/-- The centre and the first vertex of any nonempty leg. -/
theorem cliqueNum_spider (legs : List ℕ) (h : 0 < legs.sum) : (spider legs).cliqueNum = 2 :=
  cliqueNum_of_isTree (h := isTree_spider legs) (by simp [V_spider]; omega)

theorem chromNum_spider (legs : List ℕ) (h : 0 < legs.sum) : (spider legs).chromNum = 2 := by
  simp only [IsoGraph.spider, IsoGraph.chromNum_mk, CGraph.chromNum]
  let SE := CGraph.spiderEdges
  -- Helper: for k > 0, (0,1) ∈ legEdges 0 1 k
  have hlist_start : ∀ k, 0 < k → ∃ L, (List.range k).map (· + 1) = 1 :: L := by
    intro k hk
    have : ∀ n, 0 < n → ∃ L, (List.range n).map (· + 1) = 1 :: L := by
      intro n hn
      induction n with
      | zero => contradiction
      | succ m ih =>
        cases m with
        | zero => exact ⟨[], by rfl⟩
        | succ p =>
          obtain ⟨L, hL⟩ := ih (by omega)
          exact ⟨L ++ [p + 1 + 1],
              by rw [List.range_succ, List.map_append, List.map_cons, hL]; simp⟩
    exact this k hk
  have hleg : ∀ k, 0 < k → (0, 1) ∈ CGraph.legEdges 0 1 k := by
    intro k hk
    show (0, 1) ∈ CGraph.pathEdges (0 :: (List.range k).map (· + 1))
    obtain ⟨L, hL⟩ := hlist_start k hk
    rw [hL, CGraph.pathEdges]
    exact List.mem_cons_self
  have hedge_first : ∀ (k : ℕ) (rest : List ℕ), 0 < k →
      (0, 1) ∈ CGraph.spiderEdges 1 (k :: rest) := by
    intro k rest hk
    rw [CGraph.spiderEdges]
    exact List.mem_append_left _ (hleg k hk)
  have hSE_zero_head : ∀ (rest : List ℕ), CGraph.spiderEdges 1 (0 ::
      rest) = CGraph.spiderEdges 1 rest := by
    intro rest
    simp [CGraph.spiderEdges, CGraph.legEdges]
  have hedge_all : (0, 1) ∈ CGraph.spiderEdges 1 legs := by
    have key : ∀ (ls : List ℕ), 0 < ls.sum → (0, 1) ∈ CGraph.spiderEdges 1 ls := by
      intro ls hls
      induction ls with
      | nil => simp at hls
      | cons k rest ih =>
        simp only [List.sum_cons] at hls
        by_cases hk : 0 < k
        · exact hedge_first k rest hk
        · push_neg at hk
          have hk0 : k = 0 := by omega
          rw [hk0] at hls
          simp at hls
          rw [hk0, hSE_zero_head]
          exact ih hls
    exact key legs h
  have htree : (CGraph.spider legs).toSimple.IsTree := isTree_spider legs
  have hchrom_le : (CGraph.spider legs).toSimple.chromaticNumber ≤ 2 :=
    htree.isBipartite.chromaticNumber_le
  have hchrom_ge : 2 ≤ (CGraph.spider legs).toSimple.chromaticNumber := by
    have hadj : (CGraph.spider legs).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ := by
      rw [CGraph.spider_adj_val]
      refine ⟨?_, Or.inl hedge_all⟩
      show ((⟨0, by omega⟩ : (CGraph.spider legs).V) : ℕ) ≠ ((⟨1, by omega⟩ : (CGraph.spider
          legs).V) : ℕ)
      simp
    exact SimpleGraph.two_le_chromaticNumber_of_adj hadj
  have hchrom_eq : (CGraph.spider
      legs).toSimple.chromaticNumber = 2 := le_antisymm hchrom_le hchrom_ge
  simp [hchrom_eq]

/-- Pendant, centre, centre, pendant. -/
theorem diameter_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).diameter = 3 := by
  rw [IsoGraph.doubleStar_def, diameter_mk]
  let c0 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨0, by omega⟩
  let c1 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨1, by omega⟩
  let a : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨2, by omega⟩
  let b : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨m + 3, by omega⟩
  have hv0 : c0.1 = 0 := rfl
  have hv1 : c1.1 = 1 := rfl
  have hva : a.1 = 2 := rfl
  have hvb : b.1 = m + 3 := rfl
  have hadj : ∀ x y : (CGraph.doubleStar (m + 1) (n + 1)).V,
      (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj x y ↔
        (x.1 ≠ y.1 ∧
          (((x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + (m + 1)) ∨
              (x.1 = 1 ∧ 2 + (m + 1) ≤ y.1 ∧ y.1 < 2 + (m + 1) + (n + 1))) ∨
            ((y.1 = 0 ∧ x.1 = 1) ∨ (y.1 = 0 ∧ 2 ≤ x.1 ∧ x.1 < 2 + (m + 1)) ∨
              (y.1 = 1 ∧ 2 + (m + 1) ≤ x.1 ∧ x.1 < 2 + (m + 1) + (n + 1))))) := by
    intro x y
    rw [CGraph.toSimple_adj]
    exact CGraph.doubleStar_adj_val (m + 1) (n + 1) x y
  have hc01 : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj c0 c1 := by
    rw [hadj, hv0, hv1]
    omega
  -- Every vertex is a centre, or a leaf one step from a centre.
  have key : ∀ w : (CGraph.doubleStar (m + 1) (n + 1)).V, ∃ c, (c = c0 ∨ c = c1) ∧
      ∃ p : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Walk w c, p.length ≤ 1 := by
    intro w
    by_cases hw : w.1 < 2 + (m + 1)
    · refine ⟨c0, Or.inl rfl, ?_⟩
      by_cases h0 : w = c0
      · subst h0
        exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hw0 : w.1 ≠ 0 := fun h ↦ h0 (Fin.ext (by rw [hv0]; omega))
        have hwc : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj w c0 := by
          rw [hadj, hv0]; omega
        exact ⟨SimpleGraph.Walk.cons hwc SimpleGraph.Walk.nil, by simp⟩
    · have hwc : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj w c1 := by
        have := w.isLt
        rw [hadj, hv1]
        omega
      exact ⟨c1, Or.inr rfl, SimpleGraph.Walk.cons hwc SimpleGraph.Walk.nil, by simp⟩
  have link : ∀ x y : (CGraph.doubleStar (m + 1) (n + 1)).V, (x = c0 ∨ x = c1) →
      (y = c0 ∨ y = c1) →
      ∃ p : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Walk x y, p.length ≤ 1 := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨SimpleGraph.Walk.cons hc01 SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨SimpleGraph.Walk.cons hc01.symm SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  refine CGraph.diameter_eq_of_walks _ 3 (a := a) (b := b) (fun u v ↦ ?_) fun p ↦ ?_
  · obtain ⟨cu, hcu, pu, hpu⟩ := key u
    obtain ⟨cv, hcv, pv, hpv⟩ := key v
    obtain ⟨q, hq⟩ := link cu cv hcu hcv
    refine ⟨(pu.append q).append pv.reverse, ?_⟩
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega
  · -- A leaf of one centre and a leaf of the other are three steps apart: they are distinct,
    -- non-adjacent, and their only neighbours are the two distinct centres.
    refine SimpleGraph.three_le_length_of_no_common_neighbour ?_ ?_ ?_ p
    · exact fun h ↦ by have h' := congrArg Fin.val h; rw [hva, hvb] at h'; omega
    · rw [hadj, hva, hvb]; omega
    · intro x hx hx'
      have e0 : x = c0 := Fin.ext (by rw [hadj, hva] at hx; rw [hv0]; omega)
      have e1 : x = c1 := Fin.ext (by rw [hadj, hvb] at hx'; rw [hv1]; omega)
      have h' := congrArg Fin.val (e0.symm.trans e1)
      rw [hv0, hv1] at h'
      omega

/-- Either centre reaches everything in two steps. -/
theorem radius_doubleStar (m n : ℕ) : (doubleStar (m + 1) (n + 1)).radius = 2 := by
  rw [IsoGraph.doubleStar_def, radius_mk]
  -- Lower bound: 2 ≤ radius, from diameter = 3 and diameter ≤ 2 * radius
  have hdia : (CGraph.doubleStar (m + 1) (n + 1)).diameter = 3 := by
    have := diameter_doubleStar m n
    simp [IsoGraph.doubleStar_def, diameter_mk] at this
    exact this
  have hlow : 2 ≤ (CGraph.doubleStar (m + 1) (n + 1)).radius := by
    have := CGraph.diameter_le_two_mul_radius (CGraph.doubleStar (m + 1) (n + 1))
    simp [hdia] at this
    omega
  -- Upper bound: radius ≤ 2, from eccent(0) ≤ 2
  set v0 : (CGraph.doubleStar (m + 1) (n + 1)).V := ⟨0, by omega⟩
  have hecc0 : (CGraph.doubleStar (m + 1) (n + 1)).toSimple.eccent v0 ≤ 2 := by
    rw [SimpleGraph.eccent_le_iff]
    intro u
    have hlk : u.val < 2 + (m + 1) + (n + 1) := u.isLt
    -- It suffices to show v0 = u or adj v0 u or ∃ w, adj v0 w ∧ adj w u
    suffices h : v0 = u ∨ (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj v0 u ∨
      ∃ w, (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj v0 w ∧
        (CGraph.doubleStar (m + 1) (n + 1)).toSimple.Adj w u by
      rcases h with rfl | hadj | ⟨w, h1, h2⟩
      · simp
      · rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj]; norm_num
      · exact le_trans (SimpleGraph.edist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
          SimpleGraph.Walk.nil))) (by simp)
    by_cases h0 : u.val = 0
    · left; exact Fin.ext (by simp [v0]; omega)
    · by_cases h1 : u.val = 1
      · right; left
        simp [v0, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
        omega
      · by_cases h2 : u.val < 2 + (m + 1)
        · right; left
          simp [v0, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
          omega
        · right; right
          refine ⟨⟨1, by omega⟩, ?_, ?_⟩
          · simp [v0, CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
          · simp [CGraph.toSimple_adj, CGraph.doubleStar_adj_val]
            omega
  have hup : (CGraph.doubleStar (m + 1) (n + 1)).radius ≤ 2 := by
    rw [CGraph.radius]
    apply ENat.toNat_le_of_le_coe
    exact le_trans (SimpleGraph.radius_le_eccent (u := v0)) hecc0
  exact le_antisymm hup hlow

/-- A clique on three or more vertices already has more edges than a tree may. -/
theorem not_isAcyclic_lollipop (m k : ℕ) : ¬ IsAcyclic (lollipop (m + 3) k) := by
  intro hac
  have htree : IsTree (lollipop (m + 3) k) :=
    (isTree_iff_isConnected_and_isAcyclic _).mpr ⟨isConnected_lollipop (m + 2) k, hac⟩
  have h := ((isTree_iff _).mp htree).2
  have hE : (lollipop (m + 3) k).E = (m + 3).choose 2 + k := E_lollipop (m + 2) k
  have hch : m + 3 ≤ (m + 3).choose 2 := by
    have hc : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
      rw [Nat.choose_two_right]; simp
    rw [hc, Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  rw [hE, V_lollipop] at h
  omega

/-- Hanging pendants off a cycle leaves the edge and vertex counts equal. -/
theorem not_isAcyclic_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    ¬ IsAcyclic (cyclePendant (m + 3) ks) := by
  intro hac
  have htree : IsTree (cyclePendant (m + 3) ks) :=
    (isTree_iff_isConnected_and_isAcyclic _).mpr ⟨isConnected_cyclePendant m ks h, hac⟩
  have h2 := (isTree_iff _).mp htree
  rw [E_cyclePendant m ks h, V_cyclePendant] at h2
  omega

/-- Every path the same parity means two colours, once each path is genuinely subdivided. -/
theorem chromNum_thetaGraph_of_parity {xs : List ℕ} (b : ℕ) (hne : xs ≠ [])
    (h0 : ∀ k ∈ xs, 0 < k) (h : ∀ k ∈ xs, (k + b) % 2 = 1) : (thetaGraph xs).chromNum = 2 := by
  refine chromNum_eq_two_iff.mpr ⟨isBipartite_thetaGraph_of_parity b h, ?_⟩
  have hlen : 0 < xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons a t => simp
  rw [E_thetaGraph xs h0]
  omega

/-- All the paths odd is the `b = 0` case, and odd paths are automatically subdivided. -/
theorem chromNum_thetaGraph_odd {xs : List ℕ} (hne : xs ≠ []) (h : ∀ k ∈ xs, k % 2 = 1) :
    (thetaGraph xs).chromNum = 2 :=
  chromNum_thetaGraph_of_parity 0 hne (fun k hk ↦ by have := h k hk; omega) (by simpa using h)

/-- All the paths even is the `b = 1` case, and there positivity has to be asked for. -/
theorem chromNum_thetaGraph_even {xs : List ℕ} (hne : xs ≠ []) (h0 : ∀ k ∈ xs, 0 < k)
    (h : ∀ k ∈ xs, k % 2 = 0) : (thetaGraph xs).chromNum = 2 :=
  chromNum_thetaGraph_of_parity 1 hne h0 (fun k hk ↦ by have := h k hk; omega)

/-- A spider is a tree, so it has no cycle. -/
@[simp] theorem isAcyclic_spider (legs : List ℕ) : IsAcyclic (spider legs) :=
  ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_spider legs)).2

/-- A double star is a tree, so it has no cycle. -/
@[simp] theorem isAcyclic_doubleStar (m n : ℕ) : IsAcyclic (doubleStar m n) :=
  ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_doubleStar m n)).2

/-- Covering the triangular graph by cliques is colouring the Kneser graph on the same pairs. -/
theorem cliqueCoverNum_triangular (n : ℕ) :
    (triangular n).cliqueCoverNum = (kneser n 2).chromNum := by
  rw [cliqueCoverNum_eq, compl_triangular]

/-- Lovász' bound for `K(n, 2)` transported through the complement. -/
theorem cliqueCoverNum_triangular_le (n : ℕ) :
    (triangular (n + 4)).cliqueCoverNum ≤ n + 2 := by
  have h := chromNum_kneser_le (n + 4) 2 (by norm_num)
  rw [cliqueCoverNum_triangular]
  omega

/-- `L(K₅)` is covered by three cliques, since its complement is the Petersen graph. -/
theorem cliqueCoverNum_triangular_five : (triangular 5).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_eq, ← compl_petersen, compl_compl, chromNum_petersen]

/-- **Paley graphs are class two.**  They are regular of odd order, so `Δ` colours leave an edge
uncoloured. -/
theorem maxDeg_lt_edgeChromNum_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1)
    (h5 : 5 ≤ q) : maxDeg (paley q) < (paley q).edgeChromNum := by
  refine maxDeg_lt_edgeChromNum_of_isRegularWith_odd (isRegularWith_paley q hq) (by omega) ?_
  rw [V_paley]
  omega

/-- Spelling the previous bound out: `χ'(Paley q) ≥ (q + 1) / 2`. -/
theorem edgeChromNum_paley_ge (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (h5 : 5 ≤ q) :
    (q + 1) / 2 ≤ (paley q).edgeChromNum := by
  have h := maxDeg_lt_edgeChromNum_paley q hq h5
  rw [maxDeg_paley q hq] at h
  omega

/-- **Rook graphs of odd order are class two.**  `R(2m+3, 2n+3)` is regular on an odd number of
vertices. -/
theorem edgeChromNum_rook_odd_ge (m n : ℕ) :
    2 * m + 2 * n + 5 ≤ (rook (2 * m + 3) (2 * n + 3)).edgeChromNum := by
  have hodd : (rook (2 * m + 3) (2 * n + 3)).V % 2 = 1 := by
    rw [V_rook, Nat.mul_mod, show (2 * m + 3) % 2 = 1 by omega, show (2 * n + 3) % 2 = 1 by omega]
  have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd
    (isRegularWith_rook (2 * m + 3) (2 * n + 3)) (by omega) hodd
  have hd : maxDeg (rook (2 * m + 3) (2 * n + 3)) = 2 * m + 2 * n + 4 := by
    have hr := maxDeg_rook (2 * m + 2) (2 * n + 2)
    rw [show 2 * m + 2 + 1 = 2 * m + 3 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring] at hr
    omega
  rw [hd] at h
  omega

/-- **Balanced complete multipartite graphs of odd order are class two.** -/
theorem edgeChromNum_completeMultipartite_replicate_ge {m d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hodd : m * d % 2 = 1) :
    (m - 1) * d + 1 ≤ (completeMultipartite (List.replicate m d)).edgeChromNum := by
  have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd
    (isRegularWith_completeMultipartite_replicate m d)
    (Nat.mul_pos (by omega) hd)
    (by rw [V_completeMultipartite_replicate]; exact hodd)
  rw [maxDeg_completeMultipartite_replicate (by omega) hd] at h
  omega

/-- `α(Paley 13) ≤ 3` leaves at least ten vertices for the cover. -/
theorem ten_le_coverNum_paley_thirteen : 10 ≤ (paley 13).coverNum := by
  have h := coverNum_add_indepNum (paley 13)
  have h2 := indepNum_paley_thirteen_le
  rw [V_paley] at h
  omega

/-- `α(Paley 17) ≤ 4` leaves at least thirteen vertices for the cover. -/
theorem thirteen_le_coverNum_paley_seventeen : 13 ≤ (paley 17).coverNum := by
  have h := coverNum_add_indepNum (paley 17)
  have h2 := indepNum_paley_seventeen_le
  rw [V_paley] at h
  omega

/-- **Triangular graphs of odd order are class two.**  `L(Kₙ)` is `(2n - 4)`-regular on
`C(n, 2)` vertices, so an odd binomial coefficient forces an extra edge colour. -/
theorem maxDeg_lt_edgeChromNum_triangular {n : ℕ} (hn : 3 ≤ n) (hodd : n.choose 2 % 2 = 1) :
    maxDeg (triangular n) < (triangular n).edgeChromNum := by
  refine maxDeg_lt_edgeChromNum_of_isRegularWith_odd (isRegularWith_triangular n) (by omega) ?_
  rw [V_triangular]
  exact hodd

/-- The same bound with the maximum degree evaluated. -/
theorem edgeChromNum_triangular_ge (n : ℕ) (hodd : (n + 4).choose 2 % 2 = 1) :
    2 * n + 5 ≤ (triangular (n + 4)).edgeChromNum := by
  have h := maxDeg_lt_edgeChromNum_triangular (n := n + 4) (by omega) hodd
  have hd : maxDeg (triangular (n + 4)) = 2 * n + 4 := by
    have hr := maxDeg_triangular (n + 2)
    rw [show n + 2 + 2 = n + 4 by ring] at hr
    omega
  omega

/-- `T(6)` is `8`-regular on `15` vertices. -/
theorem edgeChromNum_triangular_six_ge : 9 ≤ (triangular 6).edgeChromNum := by
  have h := edgeChromNum_triangular_ge 2 (by decide)
  norm_num at h
  exact h

/-- `T(7)` is `10`-regular on `21` vertices. -/
theorem edgeChromNum_triangular_seven_ge : 11 ≤ (triangular 7).edgeChromNum := by
  have h := edgeChromNum_triangular_ge 3 (by decide)
  norm_num at h
  exact h

end IsoGraph
