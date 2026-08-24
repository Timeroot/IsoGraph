import IsoGraph.SmallGraphs.Identifications

/-!
# The tables of invariant values

The tables of invariant values for the named graphs, and everything read off them: derived edge
counts, chromatic numbers, clique and independence numbers, transitivity and strong regularity.
-/

namespace IsoGraph

/-! ## Lifts held over from `Constructions.lean`

`@[toIsoGraph]` can only state a fact once every constant in it has a bridge, and
`Constructions.lean` runs before `Quotient.lean`: the order and the products have none there yet.
These eight are tagged here instead, which lifts them exactly as the attribute would have. -/

attribute [toIsoGraph] CGraph.E_compl

attribute [toIsoGraph] CGraph.not_isConnected_disjUnion

attribute [toIsoGraph IsVertexTransitive.cartesianProduct]
  CGraph.isVertexTransitive_cartesianProduct

attribute [toIsoGraph IsVertexTransitive.tensorProduct] CGraph.isVertexTransitive_tensorProduct

attribute [toIsoGraph IsVertexTransitive.strongProduct] CGraph.isVertexTransitive_strongProduct

attribute [toIsoGraph IsVertexTransitive.lexProduct] CGraph.isVertexTransitive_lexProduct

attribute [toIsoGraph IsArcTransitive.lineGraph] CGraph.isVertexTransitive_lineGraph

attribute [toIsoGraph] CGraph.isSRGWith_triangular

/-- Every edge of a star contains the centre, so any two of them meet: the line graph of a star
is complete. -/
@[simp] theorem lineGraph_star (n : ℕ) : lineGraph (star n) = complete n := by
  obtain ⟨c, hcentre⟩ : ∃ c : (CGraph.star n).V, ∀ e : (CGraph.lineGraph (CGraph.star n)).V,
      c ∈ (e.1 : Sym2 (CGraph.star n).V) := by
    refine ⟨(Sum.inl 0 : Fin 1 ⊕ Fin n), ?_⟩
    rintro ⟨e, he⟩
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [SimpleGraph.mem_edgeSet] at he
      rcases a with x | x <;> rcases b with y | y
      · exact absurd he (by simp [CGraph.toSimple, CGraph.star])
      · exact (Subsingleton.elim (0 : Fin 1) x) ▸ Sym2.mem_mk_left _ _
      · exact (Subsingleton.elim (0 : Fin 1) y) ▸ Sym2.mem_mk_right _ _
      · exact absurd he (by simp [CGraph.toSimple, CGraph.star])
  have h : ∀ e f : (CGraph.lineGraph (CGraph.star n)).V, e ≠ f →
      (CGraph.lineGraph (CGraph.star n)).Adj e f = true := by
    intro e f hef
    rw [CGraph.lineGraph_adj, decide_eq_true hef, Bool.true_and, decide_eq_true_eq]
    exact ⟨c, hcentre e, hcentre f⟩
  rw [star_def, lineGraph_mk, mk_eq_complete h, CGraph.card_lineGraph, CGraph.E_star]

end IsoGraph

namespace CGraph

/-- **The line graph of a complete graph is the triangular graph.**  An edge of `Kₙ` is a
two-element subset of `Fin n`, and two distinct such subsets meet exactly when they meet in
*one* point — which is the adjacency of `J(n, 2)`. -/
@[toIsoGraph simp lineGraph_complete]
def lineGraphComplete (n : ℕ) : lineGraph (complete n) ≃cg johnson n 2 := by
  have hcard : ∀ e : (CGraph.lineGraph (CGraph.complete n)).V,
      (e.1 : Sym2 (Fin n)).toFinset.card = 2 := by
    rintro ⟨e, he⟩
    exact Sym2.card_toFinset_of_not_isDiag e (SimpleGraph.not_isDiag_of_mem_edgeSet _ he)
  set F : (CGraph.lineGraph (CGraph.complete n)).V → (CGraph.johnson n 2).V :=
    fun e ↦ ⟨(e.1 : Sym2 (Fin n)).toFinset, hcard e⟩ with hF
  have hmem : ∀ (e : (CGraph.lineGraph (CGraph.complete n)).V) (v : Fin n),
      v ∈ (F e).1 ↔ v ∈ (e.1 : Sym2 (Fin n)) := fun _ _ ↦ Sym2.mem_toFinset
  have hinj : Function.Injective F := by
    rintro ⟨e, he⟩ ⟨f, hf⟩ hef
    refine Subtype.ext ?_
    revert he hf hef
    induction e using Sym2.ind with
    | _ a b =>
      induction f using Sym2.ind with
      | _ c d =>
        intro he hf hef
        have hab : a ≠ b := by
          simpa [CGraph.toSimple] using SimpleGraph.not_isDiag_of_mem_edgeSet _ he
        have hset : ({a, b} : Finset (Fin n)) = {c, d} := by
          simpa [hF, Sym2.toFinset_mk_eq] using congrArg Subtype.val hef
        have ha : a = c ∨ a = d := by
          have hmem : a ∈ ({c, d} : Finset (Fin n)) := by rw [← hset]; simp
          simpa using hmem
        have hb : b = c ∨ b = d := by
          have hmem : b ∈ ({c, d} : Finset (Fin n)) := by rw [← hset]; simp
          simpa using hmem
        rcases ha with rfl | rfl
        · rcases hb with rfl | rfl
          · exact absurd rfl hab
          · rfl
        · rcases hb with rfl | rfl
          · exact Sym2.eq_swap
          · exact absurd rfl hab
  have hsurj : Function.Surjective F := by
    rintro ⟨s, hs⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
    refine ⟨⟨s(a, b), ?_⟩, ?_⟩
    · show (CGraph.complete n).toSimple.Adj a b
      simpa [CGraph.toSimple] using hab
    · exact Subtype.ext (by simpa [hF] using Sym2.toFinset_mk_eq (x := a) (y := b))
  have hadj : ∀ e f, (CGraph.johnson n 2).Adj (F e) (F f)
      = (CGraph.lineGraph (CGraph.complete n)).Adj e f := by
    intro e f
    rw [CGraph.johnson_adj, CGraph.lineGraph_adj]
    by_cases hef : e = f
    · subst hef
      simp
    · rw [decide_eq_true hef, decide_eq_true (show F e ≠ F f from fun h ↦ hef (hinj h)),
        Bool.true_and, Bool.true_and,
        show (((F e).1 ∩ (F f).1).card == 2 - 1)
          = decide (((F e).1 ∩ (F f).1).card = 1) from
          Bool.beq_eq_decide_eq _ _]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · intro hone
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
        have hv' : v ∈ (F e).1 ∩ (F f).1 := by rw [hv]; simp
        rw [Finset.mem_inter] at hv'
        exact ⟨v, (hmem e v).1 hv'.1, (hmem f v).1 hv'.2⟩
      · rintro ⟨v, hv1, hv2⟩
        have hvmem : v ∈ (F e).1 ∩ (F f).1 :=
          Finset.mem_inter.2 ⟨(hmem e v).2 hv1, (hmem f v).2 hv2⟩
        have hpos : 1 ≤ ((F e).1 ∩ (F f).1).card := Finset.card_pos.2 ⟨v, hvmem⟩
        have hle : ((F e).1 ∩ (F f).1).card ≤ 2 :=
          le_of_le_of_eq (Finset.card_le_card Finset.inter_subset_left) (F e).2
        have hne2 : ((F e).1 ∩ (F f).1).card ≠ 2 := by
          intro htwo
          have h1 : (F e).1 ∩ (F f).1 = (F e).1 :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [htwo, (F e).2])
          have h2 : (F e).1 ∩ (F f).1 = (F f).1 :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [htwo, (F f).2])
          exact hef (hinj (Subtype.ext (h1.symm.trans h2)))
        omega
  exact isoOfAdj (equivOfBijective ⟨hinj, hsurj⟩) hadj

end CGraph

namespace IsoGraph

/-- The same statement under the other name for `J(n, 2)`. -/
theorem lineGraph_complete_eq_triangular (n : ℕ) : lineGraph (complete n) = triangular n :=
  lineGraph_complete n

@[simp] theorem E_bipartite (m n : ℕ) : (bipartite m n).E = m * n := CGraph.E_bipartite m n

@[simp] theorem E_star (n : ℕ) : (star n).E = n := CGraph.E_star n

/-! Derived edge counts. -/

@[simp] theorem E_wheel (n : ℕ) : (wheel (n + 3)).E = 2 * (n + 3) := by
  rw [wheel_eq_join, E_join, E_complete, E_cycle, V_complete, V_cycle]
  norm_num
  omega

theorem E_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).E + (ds.map (·.choose 2)).sum = ds.sum.choose 2 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [completeMultipartite_cons, E_join, V_empty, V_completeMultipartite, E_empty,
      List.map_cons, List.sum_cons, List.sum_cons, choose_two_add]
    omega

/-- The hypercube is `n`-regular on `2 ^ n` vertices. -/
theorem E_hypercube (n : ℕ) : 2 * (hypercube n).E = n * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hypercube_succ, E_cartesianProduct, V_hypercube, V_complete, E_complete]
    norm_num
    ring_nf
    ring_nf at ih
    omega

@[simp] theorem E_ladder (n : ℕ) : (ladder (n + 1)).E = 3 * n + 1 := by
  show (path (n + 1) □g complete 2).E = _
  rw [E_cartesianProduct, V_path, V_complete, E_path, E_complete]
  norm_num
  omega

@[simp] theorem E_prism (n : ℕ) : (prism (n + 3)).E = 3 * (n + 3) := by
  show (cycle (n + 3) □g complete 2).E = _
  rw [E_cartesianProduct, V_cycle, V_complete, E_cycle, E_complete]
  norm_num
  omega

@[simp] theorem E_rook (m n : ℕ) : (rook m n).E = m * n.choose 2 + n * m.choose 2 := by
  show (complete m □g complete n).E = _
  rw [E_cartesianProduct, V_complete, V_complete, E_complete, E_complete]

@[simp] theorem isConnected_bipartite (m n : ℕ) : IsConnected (bipartite (m + 1) (n + 1)) :=
  CGraph.isConnected_bipartite m n

@[simp] theorem isConnected_star (n : ℕ) : IsConnected (star n) := by
  cases n with
  | zero => rw [star_zero]; exact isConnected_empty_one
  | succ n => exact isConnected_bipartite 0 n

@[simp] theorem isConnected_wheel (n : ℕ) : IsConnected (wheel (n + 1)) := by
  rw [wheel_eq_join]
  exact isConnected_join (by simp) (by simp)

@[simp] theorem isConnected_hypercube (n : ℕ) : IsConnected (hypercube n) := by
  induction n with
  | zero => rw [hypercube_zero]; exact isConnected_empty_one
  | succ n ih =>
    rw [hypercube_succ, isConnected_cartesianProduct]
    exact ⟨ih, isConnected_complete 1⟩

@[simp] theorem isConnected_ladder (n : ℕ) : IsConnected (ladder (n + 1)) := by
  show IsConnected (path (n + 1) □g complete 2)
  rw [isConnected_cartesianProduct]
  exact ⟨isConnected_path n, isConnected_complete 1⟩

@[simp] theorem isConnected_prism (n : ℕ) : IsConnected (prism (n + 1)) := by
  show IsConnected (cycle (n + 1) □g complete 2)
  rw [isConnected_cartesianProduct]
  exact ⟨isConnected_cycle n, isConnected_complete 1⟩

@[simp] theorem isConnected_rook (m n : ℕ) : IsConnected (rook (m + 1) (n + 1)) := by
  show IsConnected (complete (m + 1) □g complete (n + 1))
  rw [isConnected_cartesianProduct]
  exact ⟨isConnected_complete m, isConnected_complete n⟩

@[simp] theorem isTree_star (n : ℕ) : IsTree (star n) := by
  rw [isTree_iff, E_star, V_star]
  exact ⟨isConnected_star n, by omega⟩

@[simp] theorem not_isTree_wheel (n : ℕ) : ¬ IsTree (wheel (n + 3)) := by
  rw [isTree_iff, E_wheel, V_wheel]
  rintro ⟨-, h⟩
  omega

@[simp] theorem not_isTree_prism (n : ℕ) : ¬ IsTree (prism (n + 3)) := by
  rw [isTree_iff, E_prism]
  rintro ⟨-, h⟩
  rw [show prism (n + 3) = cycle (n + 3) □g complete 2 from rfl,
    V_cartesianProduct, V_cycle, V_complete] at h
  omega

@[simp] theorem not_isTree_ladder (n : ℕ) : ¬ IsTree (ladder (n + 2)) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, isTree_iff, E_ladder]
  rintro ⟨-, h⟩
  rw [show ladder (n + 1 + 1) = path (n + 2) □g complete 2 from rfl,
    V_cartesianProduct, V_path, V_complete] at h
  omega

@[simp] theorem not_isAcyclic_wheel (n : ℕ) : ¬ IsAcyclic (wheel (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_wheel (n + 2)) (not_isTree_wheel n)

@[simp] theorem not_isAcyclic_prism (n : ℕ) : ¬ IsAcyclic (prism (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_prism (n + 2)) (not_isTree_prism n)

@[simp] theorem not_isAcyclic_ladder (n : ℕ) : ¬ IsAcyclic (ladder (n + 2)) :=
  not_isAcyclic_of_isConnected (isConnected_ladder (n + 1)) (not_isTree_ladder n)

/-! ### Connectivity of the join families -/

/-- A complete multipartite graph with two nonempty parts is connected. -/
theorem isConnected_completeMultipartite (a b : ℕ) (ds : List ℕ) :
    IsConnected (completeMultipartite ((a + 1) :: (b + 1) :: ds)) := by
  rw [completeMultipartite_cons]
  exact isConnected_join (by simp) (by simp)

@[simp] theorem isConnected_book (n : ℕ) : IsConnected (book n) :=
  isConnected_completeMultipartite 0 0 [n]

@[simp] theorem isConnected_cocktailParty (n : ℕ) : IsConnected (cocktailParty (n + 2)) := by
  show IsConnected (completeMultipartite (List.replicate (n + 2) 2))
  rw [List.replicate_succ, List.replicate_succ]
  exact isConnected_completeMultipartite 1 1 _

@[simp] theorem isConnected_fan (n : ℕ) : IsConnected (fan (n + 1)) := by
  show IsConnected (complete 1 ∇g path (n + 1))
  exact isConnected_join (by simp) (by simp)

@[simp] theorem indepNum_bipartite (m n : ℕ) : (bipartite m n).indepNum = max m n :=
  CGraph.indepNum_bipartite m n

@[simp] theorem cliqueNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).cliqueNum = 2 :=
  CGraph.cliqueNum_bipartite m n

@[simp] theorem diameter_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).diameter = 2 :=
  CGraph.diameter_bipartite m n

@[simp] theorem indepNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (ds.max?).getD 0 :=
  CGraph.indepNum_completeMultipartite ds

/-- A maximum clique of a rook graph is a full row or a full column. -/
@[simp] theorem cliqueNum_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (rook m n).cliqueNum = max m n := by
  rw [show rook m n = complete m □g complete n from rfl,
    cliqueNum_cartesianProduct (by simpa using hm) (by simpa using hn), cliqueNum_complete,
    cliqueNum_complete]

/-! Derived clique and independence numbers. -/

@[simp] theorem cliqueNum_star (n : ℕ) : (star (n + 1)).cliqueNum = 2 :=
  cliqueNum_bipartite 0 n

@[simp] theorem indepNum_star (n : ℕ) : (star n).indepNum = max 1 n := indepNum_bipartite 1 n

@[simp] theorem indepNum_wheel (n : ℕ) : (wheel (n + 3)).indepNum = (n + 3) / 2 := by
  rw [wheel_eq_join, indepNum_join, indepNum_complete, indepNum_cycle]
  omega

@[simp] theorem cliqueNum_book (n : ℕ) : (book n).cliqueNum = 2 + min n 1 := by
  rw [book_eq_join, cliqueNum_join, cliqueNum_complete, cliqueNum_empty]

@[simp] theorem indepNum_book (n : ℕ) : (book n).indepNum = max 1 n := by
  rw [book_eq_join, indepNum_join, indepNum_complete, indepNum_empty]
  norm_num

private theorem max?_replicate (a n : ℕ) : (List.replicate (n + 1) a).max? = some a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.max?_cons, ih]; simp

@[simp] theorem indepNum_cocktailParty (n : ℕ) : (cocktailParty (n + 1)).indepNum = 2 := by
  show (completeMultipartite (List.replicate (n + 1) 2)).indepNum = 2
  rw [indepNum_completeMultipartite, max?_replicate]
  rfl

@[simp] theorem cliqueNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).cliqueNum = (ds.map (min · 1)).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [completeMultipartite_cons, cliqueNum_join, cliqueNum_empty, ih, List.map_cons,
      List.sum_cons]

@[simp] theorem cliqueNum_cocktailParty (n : ℕ) : (cocktailParty n).cliqueNum = n := by
  show (completeMultipartite (List.replicate n 2)).cliqueNum = n
  rw [cliqueNum_completeMultipartite, List.map_replicate]
  simp

@[simp] theorem E_hypercube_pos (n : ℕ) : 0 < (hypercube (n + 1)).E := by
  have h := E_hypercube (n + 1)
  have hp : 0 < (n + 1) * 2 ^ (n + 1) := by positivity
  omega

@[simp] theorem isVertexTransitive_hypercube (n : ℕ) : IsVertexTransitive (hypercube n) :=
  CGraph.isVertexTransitive_hypercube n

@[simp] theorem isArcTransitive_hypercube (n : ℕ) : IsArcTransitive (hypercube n) :=
  CGraph.isArcTransitive_hypercube n

@[simp] theorem isVertexTransitive_foldedCube (n : ℕ) : IsVertexTransitive (foldedCube n) :=
  CGraph.isVertexTransitive_foldedCube n

@[simp] theorem isArcTransitive_bipartite_self (n : ℕ) : IsArcTransitive (bipartite n n) :=
  CGraph.isArcTransitive_bipartite_self n

@[simp] theorem isVertexTransitive_bipartite_self (n : ℕ) : IsVertexTransitive (bipartite n n) :=
  CGraph.isVertexTransitive_bipartite_self n

@[simp] theorem isArcTransitive_kneser (n k : ℕ) : IsArcTransitive (kneser n k) :=
  CGraph.isArcTransitive_kneser n k

@[simp] theorem isVertexTransitive_kneser (n k : ℕ) : IsVertexTransitive (kneser n k) :=
  CGraph.isVertexTransitive_kneser n k

/-! Derived transitivity. -/

@[simp] theorem isVertexTransitive_petersen : IsVertexTransitive petersen :=
  isVertexTransitive_kneser 5 2

@[simp] theorem isArcTransitive_petersen : IsArcTransitive petersen := isArcTransitive_kneser 5 2

@[simp] theorem isVertexTransitive_triangular (n : ℕ) : IsVertexTransitive (triangular n) := by
  rw [triangular_eq_compl_kneser, isVertexTransitive_compl]
  exact isVertexTransitive_kneser n 2

@[simp] theorem isVertexTransitive_rook (m n : ℕ) : IsVertexTransitive (rook m n) :=
  (isVertexTransitive_complete m).cartesianProduct (isVertexTransitive_complete n)

@[simp] theorem isVertexTransitive_prism (n : ℕ) : IsVertexTransitive (prism n) :=
  (isVertexTransitive_cycle n).cartesianProduct (isVertexTransitive_complete 2)

@[simp] theorem isVertexTransitive_cocktailParty (n : ℕ) :
    IsVertexTransitive (cocktailParty n) := by
  rw [cocktailParty_eq_lexProduct]
  exact (isVertexTransitive_complete n).lexProduct (isVertexTransitive_empty 2)

@[simp] theorem isVertexTransitive_lineGraph_cycle (n : ℕ) :
    IsVertexTransitive (lineGraph (cycle n)) := (isArcTransitive_cycle n).lineGraph

/-! ### Strong regularity -/

theorem isSRGWith_petersen : IsSRGWith petersen 10 3 0 1 := isSRGWith_kneser_two 5

/-- **The rook's graph is strongly regular.**  This one is written out rather than generated:
`rook` is an abbreviation for a Cartesian product, and `@[toIsoGraph]` would state it for the
product and leave the later `rook` calculations with nothing to match. -/
theorem isSRGWith_rook (k : ℕ) : IsSRGWith (rook k k) (k * k) (2 * (k - 1)) (k - 2) 2 := by
  show IsSRGWith (complete k □g complete k) _ _ _ _
  rw [complete_def, cartesianProduct_mk, isSRGWith_mk]
  exact CGraph.isSRGWith_rook k

/-- **The hypercube `Q_n` has diameter `n`**: flipping the bits one at a time is optimal. -/
@[simp] theorem diameter_hypercube (n : ℕ) : (hypercube n).diameter = n := by
  induction n with
  | zero => rw [hypercube_zero, diameter_empty]
  | succ n ih =>
    rw [hypercube_succ, diameter_cartesianProduct (isConnected_hypercube n)
      (isConnected_complete 1), ih, diameter_complete 0]

@[simp] theorem diameter_ladder (n : ℕ) : (ladder (n + 1)).diameter = n + 1 := by
  show (path (n + 1) □g complete 2).diameter = n + 1
  rw [diameter_cartesianProduct (isConnected_path n) (isConnected_complete 1), diameter_path n,
    diameter_complete 0]

@[simp] theorem diameter_prism (n : ℕ) : (prism (n + 1)).diameter = (n + 1) / 2 + 1 := by
  show (cycle (n + 1) □g complete 2).diameter = (n + 1) / 2 + 1
  rw [diameter_cartesianProduct (isConnected_cycle n) (isConnected_complete 1), diameter_cycle n,
    diameter_complete 0]

@[simp] theorem diameter_rook (m n : ℕ) : (rook (m + 2) (n + 2)).diameter = 2 := by
  show (complete (m + 2) □g complete (n + 2)).diameter = 2
  rw [diameter_cartesianProduct (isConnected_complete (m + 1)) (isConnected_complete (n + 1)),
    diameter_complete m, diameter_complete n]

@[simp] theorem degSequence_petersen : degSequence petersen = List.replicate 10 3 :=
  isSRGWith_petersen.degSequence

@[simp] theorem degSequence_kneser_two (n : ℕ) :
    degSequence (kneser n 2) = List.replicate (n.choose 2) ((n - 2).choose 2) :=
  (isSRGWith_kneser_two n).degSequence

@[simp] theorem degSequence_cocktailParty (n : ℕ) :
    degSequence (cocktailParty n) = List.replicate (2 * n) (2 * n - 2) :=
  (isSRGWith_cocktailParty n).degSequence

@[simp] theorem degSequence_bipartite_self (n : ℕ) :
    degSequence (bipartite n n) = List.replicate (2 * n) n :=
  (isSRGWith_bipartite n).degSequence

theorem degSequence_triangular (n : ℕ) (hn : 4 ≤ n) :
    degSequence (triangular n) = List.replicate (n.choose 2) (2 * (n - 2)) :=
  (isSRGWith_triangular n hn).degSequence

/-! ### Edge counts of the complement and the line graph -/

@[simp] theorem E_compl_eq (G : IsoGraph) : Gᶜ.E = G.V.choose 2 - G.E := by
  have := G.E_compl
  omega

theorem E_le_choose_two (G : IsoGraph) : G.E ≤ G.V.choose 2 := by
  have := G.E_compl
  omega

@[simp] theorem E_triangular (n : ℕ) : (triangular n).E = n * (n - 1).choose 2 := by
  rw [← lineGraph_complete_eq_triangular, E_lineGraph, degSequence_complete, List.map_replicate,
    List.sum_replicate, smul_eq_mul]

/-! ### More vertex counts -/

@[simp] theorem V_rook (m n : ℕ) : (rook m n).V = m * n := by
  show (complete m □g complete n).V = _
  rw [V_cartesianProduct, V_complete, V_complete]

@[simp] theorem V_triangular (n : ℕ) : (triangular n).V = n.choose 2 := V_johnson n 2

@[simp] theorem V_ladder (n : ℕ) : (ladder n).V = n * 2 := by
  show (path n □g complete 2).V = _
  rw [V_cartesianProduct, V_path, V_complete]

@[simp] theorem V_prism (n : ℕ) : (prism n).V = n * 2 := by
  show (cycle n □g complete 2).V = _
  rw [V_cartesianProduct, V_cycle, V_complete]

@[simp] theorem V_fan (n : ℕ) : (fan n).V = 1 + n := by
  show (complete 1 ∇g path n).V = _
  rw [V_join, V_complete, V_path]

@[simp] theorem V_book (n : ℕ) : (book n).V = 2 + n := by
  show (completeMultipartite [1, 1, n]).V = _
  rw [V_completeMultipartite]
  simp
  omega

@[simp] theorem V_cocktailParty (n : ℕ) : (cocktailParty n).V = 2 * n := by
  show (completeMultipartite (List.replicate n 2)).V = _
  rw [V_completeMultipartite, List.sum_replicate, smul_eq_mul]
  omega

@[simp] theorem degSequence_rook (m n : ℕ) :
    degSequence (rook m n) = List.replicate (m * n) ((n - 1) + (m - 1)) := by
  show degSequence (complete m □g complete n) = _
  rw [complete_def m, complete_def n, cartesianProduct_mk, degSequence_mk]
  exact CGraph.degSequence_rook m n

theorem two_mul_E_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    2 * (kneser n k).E = n.choose k * (n - k).choose k :=
  two_mul_E_of_degSequence_replicate (degSequence_kneser (n := n) hk)

theorem degSequence_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    degSequence (paley q) = List.replicate q ((q - 1) / 2) :=
  (isSRGWith_paley q hq).degSequence

@[simp] theorem degSequence_hypercube (n : ℕ) :
    degSequence (hypercube n) = List.replicate (2 ^ n) n := by
  induction n with
  | zero => rw [hypercube_zero, degSequence_empty]; rfl
  | succ n ih =>
    rw [hypercube_succ, degSequence_cartesianProduct ih (degSequence_complete 2)]
    congr 1

theorem two_mul_E_hypercube (n : ℕ) : 2 * (hypercube n).E = 2 ^ n * n :=
  two_mul_E_of_degSequence_replicate (degSequence_hypercube n)

@[simp] theorem degSequence_prism (n : ℕ) :
    degSequence (prism (n + 3)) = List.replicate ((n + 3) * 2) 3 := by
  show degSequence (cycle (n + 3) □g complete 2) = _
  rw [degSequence_cartesianProduct (degSequence_cycle n) (degSequence_complete 2)]

theorem two_mul_E_prism (n : ℕ) : 2 * (prism (n + 3)).E = (n + 3) * 2 * 3 :=
  two_mul_E_of_degSequence_replicate (degSequence_prism n)

@[simp] theorem star_inj {m n : ℕ} : star m = star n ↔ m = n :=
  ⟨fun h ↦ by have h2 := congrArg V h; simp only [V_star] at h2; omega, fun h ↦ by rw [h]⟩

theorem star_ne_cycle (m n : ℕ) : star m ≠ cycle (n + 3) :=
  ne_of_isTree (isTree_star m) (not_isTree_cycle n)

theorem bipartite_ne_complete (m n k : ℕ) : bipartite m n ≠ complete (k + 3) :=
  ne_of_isBipartite (isBipartite_bipartite m n) (not_isBipartite_complete k)

theorem hypercube_ne_complete (n k : ℕ) : hypercube (n + 2) ≠ complete (k + 3) :=
  ne_of_isBipartite (isBipartite_hypercube (n + 2)) (not_isBipartite_complete k)

/-! ### Diameter two, connectivity and strong regularity -/

private theorem lt_choose_two_aux (m : ℕ) : 2 * (m + 2) + 1 < (m + 4).choose 2 := by
  induction m with
  | zero => decide
  | succ p ih =>
    have hc : (p + 1 + 4).choose 2 = (p + 4) + (p + 4).choose 2 := by
      rw [show p + 1 + 4 = (p + 4) + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    omega

private theorem lt_choose_two {n : ℕ} (hn : 4 ≤ n) : 2 * (n - 2) + 1 < n.choose 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h2 : m + 4 - 2 = m + 2 := by omega
  rw [h2]
  exact lt_choose_two_aux m

@[simp] theorem diameter_petersen : petersen.diameter = 2 :=
  isSRGWith_petersen.diameter_eq_two (by norm_num) (by norm_num)

@[simp] theorem isConnected_petersen : IsConnected petersen :=
  isSRGWith_petersen.isConnected (by norm_num) (by norm_num)

@[simp] theorem diameter_cocktailParty (n : ℕ) : (cocktailParty (n + 2)).diameter = 2 :=
  (isSRGWith_cocktailParty (n + 2)).diameter_eq_two (by omega) (by omega)

theorem diameter_triangular {n : ℕ} (hn : 4 ≤ n) : (triangular n).diameter = 2 :=
  (isSRGWith_triangular n hn).diameter_eq_two (by norm_num) (lt_choose_two hn)

theorem isConnected_triangular {n : ℕ} (hn : 4 ≤ n) : IsConnected (triangular n) :=
  (isSRGWith_triangular n hn).isConnected (by norm_num) (Nat.choose_pos (by omega))

theorem diameter_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).diameter = 2 :=
  (isSRGWith_paley q hq).diameter_eq_two (by omega) (by omega)

theorem isConnected_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    IsConnected (paley q) :=
  (isSRGWith_paley q hq).isConnected (by omega) (by omega)

theorem diameter_bipartite_self (n : ℕ) : (bipartite (n + 2) (n + 2)).diameter = 2 :=
  (isSRGWith_bipartite (n + 2)).diameter_eq_two (by omega) (by omega)

theorem isConnected_bipartite_self (n : ℕ) : IsConnected (bipartite (n + 1) (n + 1)) :=
  (isSRGWith_bipartite (n + 1)).isConnected (by omega) (by omega)

@[simp] theorem diameter_star (n : ℕ) : (star (n + 2)).diameter = 2 := by
  rw [star_eq_bipartite, bipartite_eq_join]
  refine diameter_join_right (by simp) ?_
  rw [E_empty, V_empty]
  exact Nat.choose_pos (by omega)

@[simp] theorem diameter_book (n : ℕ) : (book (n + 2)).diameter = 2 := by
  rw [book_eq_join]
  refine diameter_join_right (by simp) ?_
  rw [E_empty, V_empty]
  exact Nat.choose_pos (by omega)

@[simp] theorem diameter_wheel (n : ℕ) : (wheel (n + 4)).diameter = 2 := by
  rw [wheel_eq_join]
  refine diameter_join_right (by simp) ?_
  rw [show n + 4 = n + 1 + 3 from rfl, E_cycle, V_cycle]
  have := lt_choose_two (n := n + 1 + 3) (by omega)
  omega

@[simp] theorem diameter_fan (n : ℕ) : (fan (n + 4)).diameter = 2 := by
  refine diameter_join_right (by simp) ?_
  rw [show n + 4 = n + 3 + 1 from rfl, E_path, V_path]
  have := lt_choose_two (n := n + 3 + 1) (by omega)
  omega

/-! ### Complements of disconnected graphs -/

/-- At least one of a graph and its complement is connected. -/
theorem isConnected_or_isConnected_compl {G : IsoGraph} (hV : 0 < G.V) :
    IsConnected G ∨ IsConnected Gᶜ := by
  by_cases h : IsConnected G
  · exact Or.inl h
  · exact Or.inr (isConnected_compl_of_not_isConnected hV h)

theorem diameter_compl_le_two {G : IsoGraph} (hV : 0 < G.V) (h : ¬ IsConnected G) :
    Gᶜ.diameter ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at hV
  rw [isConnected_mk] at h
  rw [compl_mk, diameter_mk]
  haveI := FinEnum.card_pos_iff.1 hV
  exact CGraph.diameter_compl_le_two _ fun hp ↦ h ⟨hp⟩

/-- A disconnected graph with an edge has a complement of diameter exactly two. -/
theorem diameter_compl {G : IsoGraph} (h : ¬ IsConnected G) (hE : 0 < G.E) :
    Gᶜ.diameter = 2 := by
  have hV : 0 < G.V := by
    rcases Nat.eq_zero_or_pos G.V with h0 | hp
    · have hle := E_le_choose_two G
      rw [h0] at hle
      simp at hle
      omega
    · exact hp
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at hV
  rw [E_mk] at hE
  rw [isConnected_mk] at h
  rw [compl_mk, diameter_mk]
  haveI := FinEnum.card_pos_iff.1 hV
  exact CGraph.diameter_compl_eq_two _ (fun hp ↦ h ⟨hp⟩) hE

@[simp] theorem isConnected_compl_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (G ⊕g H)ᶜ :=
  isConnected_compl_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

theorem diameter_compl_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < G.E + H.E) : (G ⊕g H)ᶜ.diameter = 2 :=
  diameter_compl (not_isConnected_disjUnion hG hH) (by rw [E_disjUnion]; omega)

/-! ### The Petersen graph -/

@[simp] theorem V_petersen : petersen.V = 10 := by
  rw [V_kneser]
  rfl

/-- The complement of the Petersen graph is the triangular graph `T(5)`, the Johnson graph
`J(5, 2)`. -/
theorem compl_petersen : petersenᶜ = triangular 5 := by
  rw [triangular_eq_compl_kneser]

/-- `L(K₃) = K₃`. -/
theorem lineGraph_complete_three : lineGraph (complete 3) = complete 3 := by
  rw [lineGraph_complete_eq_triangular, triangular_three]

/-- `L(K₄) = T(4)` is the octahedron. -/
@[simp] theorem lineGraph_complete_four : lineGraph (complete 4) = cocktailParty 3 := by
  rw [lineGraph_complete_eq_triangular, triangular_four]

end IsoGraph

namespace CGraph

private theorem bipartiteEdge_adj (m n : ℕ) (p : Fin m × Fin n) :
    s(Sum.inl p.1, Sum.inr p.2) ∈ (CGraph.bipartite m n).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
  exact CGraph.bipartite_adj_inl_inr m n p.1 p.2

/-- The edge of `K_{m,n}` joining the `i`-th left vertex to the `j`-th right vertex — that is,
the square `(i, j)` of the board. -/
private def bipartiteEdge (m n : ℕ) (p : Fin m × Fin n) :
    (CGraph.lineGraph (CGraph.bipartite m n)).V :=
  ⟨s(Sum.inl p.1, Sum.inr p.2), bipartiteEdge_adj m n p⟩

private theorem mem_bipartiteEdge (m n : ℕ) (v : Fin m ⊕ Fin n) (p : Fin m × Fin n) :
    v ∈ ((bipartiteEdge m n p).1 : Sym2 (Fin m ⊕ Fin n))
      ↔ v = Sum.inl p.1 ∨ v = Sum.inr p.2 := Sym2.mem_iff

private theorem bipartiteEdge_inj (m n : ℕ) : Function.Injective (bipartiteEdge m n) := by
  intro p q h
  have h1 : s(Sum.inl p.1, Sum.inr p.2) = s(Sum.inl q.1, Sum.inr q.2) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, h3⟩ | ⟨h2, _⟩
  · exact Prod.ext_iff.2 ⟨by simpa using h2, by simpa using h3⟩
  · exact absurd h2 (by simp)

/-- **The line graph of a complete bipartite graph is the rook's graph**: `L(K_{m,n}) = Kₘ □ Kₙ`.
An edge of `K_{m,n}` *is* a square `(i, j)` of the `m × n` board, and two squares share a vertex
exactly when they share a row or a column. -/
def lineGraphBipartite (m n : ℕ) : lineGraph (bipartite m n) ≃cg rook m n := by
  have hcard : FinEnum.card (Fin m × Fin n)
      = FinEnum.card (CGraph.lineGraph (CGraph.bipartite m n)).V := by
    rw [CGraph.card_lineGraph, CGraph.E_bipartite, FinEnum.card_prod', FinEnum.card_fin',
      FinEnum.card_fin']
  have hbij : Function.Bijective (bipartiteEdge m n) :=
    FinEnum.bijective_iff_injective_and_card _ |>.2 ⟨bipartiteEdge_inj m n, hcard⟩
  have hadj : ∀ p q : Fin m × Fin n,
      (CGraph.lineGraph (CGraph.bipartite m n)).Adj (bipartiteEdge m n p) (bipartiteEdge m n q)
        = (CGraph.rook m n).Adj p q := by
    intro p q
    rw [CGraph.lineGraph_adj, CGraph.rook_adj]
    by_cases hpq : p = q
    · subst hpq; simp
    · have hne : ¬(p.1 = q.1 ∧ p.2 = q.2) := fun h ↦ hpq (Prod.ext_iff.2 h)
      rw [decide_eq_true (show bipartiteEdge m n p ≠ bipartiteEdge m n q from
          fun h ↦ hpq (bipartiteEdge_inj m n h)),
        Bool.true_and, ← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_or]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_bipartiteEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
        · have : p.1 = q.1 := by simpa using h1.symm.trans h2
          exact Or.inl ⟨this, fun hd ↦ hne ⟨this, hd⟩⟩
        · exact absurd (h1.symm.trans h2) (by simp)
        · exact absurd (h1.symm.trans h2) (by simp)
        · have : p.2 = q.2 := by simpa using h1.symm.trans h2
          exact Or.inr ⟨fun hc ↦ hne ⟨hc, this⟩, this⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact ⟨Sum.inl p.1, (mem_bipartiteEdge m n _ p).2 (Or.inl rfl),
            (mem_bipartiteEdge m n _ q).2 (Or.inl (by rw [h]))⟩
        · exact ⟨Sum.inr p.2, (mem_bipartiteEdge m n _ p).2 (Or.inr rfl),
            (mem_bipartiteEdge m n _ q).2 (Or.inr (by rw [h]))⟩
  exact (isoOfAdj (equivOfBijective hbij) hadj).symm

end CGraph

namespace IsoGraph

/-- **The line graph of a complete bipartite graph is the rook's graph**: `L(K_{m,n}) = Kₘ □ Kₙ`.
This one is restated by hand: `rook` is an abbreviation for a cartesian product, and
`@[toIsoGraph]` would state it for the product and leave the later rewrites with no `rook` to
find. -/
@[simp] theorem lineGraph_bipartite (m n : ℕ) : lineGraph (bipartite m n) = rook m n := by
  show lineGraph (bipartite m n) = complete m □g complete n
  simp only [isoTransfer]
  exact Quotient.sound ⟨CGraph.lineGraphBipartite m n⟩

end IsoGraph

namespace CGraph

/-- Relabelling for `mycielskianEmpty`: the apex becomes the centre of the star, the shadow
vertices become its leaves, and the original vertices are the isolated part. -/
private def mycielskianEmptyEquiv (n : ℕ) :
    (Fin 1 ⊕ Fin n) ⊕ Fin n ≃ Option (Fin n ⊕ Fin n) where
  toFun x := match x with
    | .inl (.inl _) => none
    | .inl (.inr i) => some (.inr i)
    | .inr i => some (.inl i)
  invFun x := match x with
    | none => .inl (.inl 0)
    | some (.inr i) => .inl (.inr i)
    | some (.inl i) => .inr i
  left_inv := by
    rintro ((j | i) | i)
    · rw [Subsingleton.elim (0 : Fin 1) j]
    · rfl
    · rfl
  right_inv := by rintro (_ | (i | i)) <;> rfl

/-- The Mycielskian of an edgeless graph: the apex together with the `n` shadow vertices forms a
star, and the `n` original vertices stay isolated. -/
@[toIsoGraph mycielskian_empty]
def mycielskianEmpty (n : ℕ) :
    mycielskian (empty n) ≃cg star n ⊕g empty n :=
  (CGraph.isoOfAdj
    (G := CGraph.star n ⊕g CGraph.empty n)
    (H := CGraph.mycielskian (CGraph.empty n))
    (mycielskianEmptyEquiv n)
    (by
      rintro ((j | i) | i) ((k | i') | i')
      · show (CGraph.mycielskian (CGraph.empty n)).Adj none none = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj none (some (.inr i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj none (some (.inl i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inr i)) none = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inr i)) (some (.inr i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inr i)) (some (.inl i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inl i)) none = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inl i)) (some (.inr i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inl i)) (some (.inl i')) = _
        simp [CGraph.star])).symm

end CGraph

namespace IsoGraph

/-! ### Bipartiteness of the Mycielskian

The Mycielskian raises the chromatic number by one, so the only way for it to be bipartite is for
it to start from nothing at all. -/

theorem not_isBipartite_mycielskian_mk {G : CGraph} {a b : G.V}
    (hab : G.Adj a b) : ¬ IsBipartite (mycielskian ⟦G⟧) := by
  rw [mycielskian_mk, isBipartite_mk]
  exact CGraph.not_isBipartite_mycielskian hab

/-- The Mycielskian is bipartite only in the degenerate edgeless case, where it is a star beside
some isolated vertices. -/
@[simp] theorem isBipartite_mycielskian_empty (n : ℕ) : IsBipartite (mycielskian (empty n)) := by
  rw [mycielskian_empty]
  exact isBipartite_disjUnion (isBipartite_star n) (isBipartite_empty n)

@[simp] theorem not_isBipartite_mycielskian_complete (n : ℕ) :
    ¬ IsBipartite (mycielskian (complete (n + 2))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.complete (n + 2)) (a := ⟨0, by omega⟩)
    (b := ⟨1, by omega⟩) (by simp)

/-- Mycielski's construction really does leave the bipartite world: even applied to a complete
bipartite graph it produces something with an odd cycle. -/
@[simp] theorem not_isBipartite_mycielskian_bipartite (m n : ℕ) :
    ¬ IsBipartite (mycielskian (bipartite (m + 1) (n + 1))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.bipartite (m + 1) (n + 1)) (a := .inl ⟨0, by omega⟩)
    (b := .inr ⟨0, by omega⟩) (by simp)

@[simp] theorem not_isBipartite_mycielskian_cycle (n : ℕ) :
    ¬ IsBipartite (mycielskian (cycle (n + 2))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.cycle (n + 2)) (a := ⟨0, by omega⟩)
    (b := ⟨1, by omega⟩) (by
      rw [CGraph.cycle_adj_val]
      show (0 : ℕ) ≠ 1 ∧ ((0 + 1) % (n + 2) = 1 ∨ (1 + 1) % (n + 2) = 0)
      exact ⟨by omega, Or.inl (Nat.mod_eq_of_lt (by omega))⟩)

@[simp] theorem not_isBipartite_mycielskian_path (n : ℕ) :
    ¬ IsBipartite (mycielskian (path (n + 2))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.path (n + 2)) (a := ⟨0, by omega⟩)
    (b := ⟨1, by omega⟩) (by simp [CGraph.path])

@[simp] theorem not_isBipartite_mycielskian_star (n : ℕ) :
    ¬ IsBipartite (mycielskian (star (n + 1))) := by
  rw [star_eq_bipartite]
  exact not_isBipartite_mycielskian_bipartite 0 n

attribute [simp] IsoGraph.degMultiset_disjUnion

@[simp] theorem degMultiset_petersen : degMultiset petersen = Multiset.replicate 10 3 :=
  degMultiset_of_degSequence degSequence_petersen

@[simp] theorem degMultiset_bipartite (m n : ℕ) :
    degMultiset (bipartite m n) = Multiset.replicate m n + Multiset.replicate n m := by
  rw [bipartite_eq_join, degMultiset_join, degMultiset_empty, degMultiset_empty, V_empty, V_empty,
    Multiset.map_replicate, Multiset.map_replicate]
  simp

@[simp] theorem degMultiset_star (n : ℕ) :
    degMultiset (star n) = n ::ₘ Multiset.replicate n 1 := by
  rw [star_eq_bipartite, degMultiset_bipartite, Multiset.replicate_one, Multiset.singleton_add]

@[simp] theorem degMultiset_wheel (n : ℕ) :
    degMultiset (wheel (n + 3)) = (n + 3) ::ₘ Multiset.replicate (n + 3) 3 := by
  rw [wheel_eq_join, degMultiset_join, degMultiset_complete, degMultiset_cycle, V_complete,
    V_cycle, Multiset.map_replicate, Multiset.map_replicate,
    show 1 - 1 + (n + 3) = n + 3 from by omega, show 2 + 1 = 3 from rfl,
    Multiset.replicate_one, Multiset.singleton_add]

@[simp] theorem degMultiset_book (n : ℕ) :
    degMultiset (book n) = Multiset.replicate 2 (n + 1) + Multiset.replicate n 2 := by
  rw [book_eq_join, degMultiset_join, degMultiset_complete, degMultiset_empty, V_complete,
    V_empty, Multiset.map_replicate, Multiset.map_replicate,
    show 2 - 1 + n = n + 1 from by omega, Nat.zero_add]

/-- The sorted form of a multiset made of `m` copies of a small value `a` and a list `l` of larger
ones.  This is exactly the shape of the degree multisets of the join-built families: a large hub
and a lot of small vertices. -/
private theorem sort_replicate_append {m a : ℕ} {l : List ℕ} (hl : l.Pairwise (· ≤ ·))
    (hab : ∀ x ∈ List.replicate m a, ∀ b ∈ l, x ≤ b) :
    ((l : Multiset ℕ) + Multiset.replicate m a).sort (· ≤ ·) = List.replicate m a ++ l := by
  refine sort_eq_of_pairwise ?_ ?_
  · exact List.pairwise_append.2 ⟨List.pairwise_replicate.2 (Or.inr le_rfl), hl, hab⟩
  · rw [← Multiset.coe_add, Multiset.coe_replicate, add_comm]

@[simp] theorem degSequence_star (n : ℕ) :
    degSequence (star n) = List.replicate n 1 ++ [n] := by
  rw [degSequence_eq_sort, degMultiset_star, ← Multiset.singleton_add,
    show ({n} : Multiset ℕ) = (([n] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (List.pairwise_singleton _ _) fun x hx b hb ↦ ?_
  have hx' := List.eq_of_mem_replicate hx
  have hn := List.ne_nil_of_mem hx
  rw [List.mem_singleton] at hb
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · simp [hn0] at hn
  · omega

@[simp] theorem degSequence_wheel (n : ℕ) :
    degSequence (wheel (n + 3)) = List.replicate (n + 3) 3 ++ [n + 3] := by
  rw [degSequence_eq_sort, degMultiset_wheel, ← Multiset.singleton_add,
    show ({n + 3} : Multiset ℕ) = (([n + 3] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (List.pairwise_singleton _ _) fun x hx b hb ↦ ?_
  rw [List.eq_of_mem_replicate hx, List.mem_singleton] at *
  omega

@[simp] theorem degSequence_book (n : ℕ) :
    degSequence (book n) = List.replicate n 2 ++ [n + 1, n + 1] := by
  rw [degSequence_eq_sort, degMultiset_book,
    show Multiset.replicate 2 (n + 1) = (([n + 1, n + 1] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (by simp [List.pairwise_cons]) fun x hx b hb ↦ ?_
  have hx' := List.eq_of_mem_replicate hx
  have hn := List.ne_nil_of_mem hx
  have hb' : b = n + 1 := by simpa using hb
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · simp [hn0] at hn
  · omega

/-! ### The chromatic number of an `IsoGraph` -/

attribute [simp] IsoGraph.chromNum_eq_zero_iff

/-! Values. -/

attribute [simp] IsoGraph.chromNum_cycle_even IsoGraph.chromNum_cycle_odd

/-! Derived chromatic numbers: everything bipartite with an edge. -/

@[simp] theorem chromNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_bipartite _ _, by rw [E_bipartite]; positivity⟩

@[simp] theorem chromNum_star (n : ℕ) : (star (n + 1)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_star _, by rw [E_star]; omega⟩

/-- **The hypercube `Q_{n+1}` is 2-chromatic.** -/
@[simp] theorem chromNum_hypercube (n : ℕ) : (hypercube (n + 1)).chromNum = 2 := by
  refine chromNum_eq_two_iff.2 ⟨isBipartite_hypercube _, ?_⟩
  have h := E_hypercube (n + 1)
  have hp : 0 < (n + 1) * 2 ^ (n + 1) := Nat.mul_pos n.succ_pos (Nat.two_pow_pos _)
  omega

@[simp] theorem chromNum_ladder (n : ℕ) : (ladder (n + 1)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_ladder _, by rw [E_ladder]; omega⟩

@[simp] theorem chromNum_prism_even (m : ℕ) : (prism (2 * m + 4)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨by rw [show 2 * m + 4 = 2 * (m + 2) by ring]; exact isBipartite_prism_even _,
    by rw [show 2 * m + 4 = (2 * m + 1) + 3 by ring, E_prism]; omega⟩

/-- **A grid is 2-chromatic.** -/
@[simp] theorem chromNum_grid (m n : ℕ) :
    (path (m + 2) □g path (n + 2)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_cartesianProduct (isBipartite_path _) (isBipartite_path _),
    by rw [E_cartesianProduct, E_path, E_path, V_path, V_path]; positivity⟩

/-! ### Complete multipartite graphs -/

/-- **A complete multipartite graph needs one colour per nonempty part.** -/
@[simp] theorem chromNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).chromNum = (ds.map fun d ↦ min d 1).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [completeMultipartite_cons, chromNum_join, ih, List.map_cons, List.sum_cons]
    cases d with
    | zero => simp
    | succ k => rw [chromNum_empty, Nat.min_eq_right (by omega)]

@[simp] theorem chromNum_cocktailParty (n : ℕ) : (cocktailParty n).chromNum = n := by
  show (completeMultipartite (List.replicate n 2)).chromNum = n
  rw [chromNum_completeMultipartite, List.map_replicate]
  simp

@[simp] theorem chromNum_book (n : ℕ) : (book (n + 1)).chromNum = 3 := by
  show (completeMultipartite [1, 1, n + 1]).chromNum = 3
  rw [chromNum_completeMultipartite]
  simp

@[simp] theorem chromNum_wheel_even (m : ℕ) : (wheel (2 * m + 4)).chromNum = 3 := by
  rw [wheel_eq_join, chromNum_join, chromNum_complete,
    show 2 * m + 4 = 2 * (m + 1) + 2 by ring, chromNum_cycle_even]

@[simp] theorem chromNum_wheel_odd (m : ℕ) : (wheel (2 * m + 3)).chromNum = 4 := by
  rw [wheel_eq_join, chromNum_join, chromNum_complete, chromNum_cycle_odd]

/-- **The Petersen graph is 3-chromatic**: the Kneser bound gives three colours, and it is not
bipartite. -/
@[simp] theorem chromNum_petersen : petersen.chromNum = 3 :=
  le_antisymm (chromNum_kneser_le 5 2 (by norm_num)) (three_le_chromNum not_isBipartite_petersen)

/- The Grötzsch graph: triangle-free and 4-chromatic. -/

example : (mycielskian (cycle 5)).chromNum = 4 := by
  rw [chromNum_mycielskian, show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]

example : (mycielskian (mycielskian (cycle 5))).chromNum = 5 := by
  rw [chromNum_mycielskian, chromNum_mycielskian,
    show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]

example : (kneser 7 3).chromNum ≤ 3 := by
  have h := chromNum_kneser_le 7 3 (by norm_num)
  omega

/- The complement of the Petersen graph is the triangular graph `T(5)`, which needs five colours;
the product bound is tight here. -/

example : 10 ≤ 3 * petersenᶜ.chromNum := by
  have h := V_le_chromNum_mul_chromNum_compl petersen
  rwa [V_petersen, chromNum_petersen] at h

@[simp] theorem girth_star (n : ℕ) : (star n).girth = 0 :=
  girth_eq_zero_iff.2 ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_star n)).2

@[simp] theorem girth_cocktailParty (n : ℕ) : (cocktailParty (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

@[simp] theorem girth_book (n : ℕ) : (book (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

@[simp] theorem girth_wheel (n : ℕ) : (wheel (n + 3)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [wheel_eq_join, cliqueNum_join]
  have : 2 ≤ (cycle (n + 3)).cliqueNum := two_le_cliqueNum_of_E_pos (by simp)
  simp only [cliqueNum_complete]
  omega

attribute [simp] IsoGraph.girth_bipartite

@[simp] theorem girth_hypercube (n : ℕ) : (hypercube (n + 2)).girth = 4 := by
  rw [hypercube_succ]
  refine girth_cartesianProduct ?_ (by simp) (isBipartite_hypercube (n + 1)) isBipartite_complete_two
  have h := E_hypercube (n + 1)
  have : 0 < (n + 1) * 2 ^ (n + 1) := by positivity
  omega

@[simp] theorem girth_cycle_four : (cycle 4).girth = 4 := by
  rw [← hypercube_two]; exact girth_hypercube 0

@[simp] theorem girth_ladder (n : ℕ) : (ladder (n + 2)).girth = 4 :=
  girth_cartesianProduct (by simp) (by simp) (isBipartite_path (n + 2)) isBipartite_complete_two

attribute [simp] IsoGraph.girth_cycle_five

theorem girth_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : 3 ≤ max m n) :
    (rook m n).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_rook hm hn]; exact h)

theorem girth_prism_even (m : ℕ) : (prism (2 * m + 4)).girth = 4 := by
  have hb : IsBipartite (cycle (2 * m + 4)) := by
    have h := isBipartite_cycle_even (m + 2)
    rwa [show 2 * (m + 2) = 2 * m + 4 by ring] at h
  refine girth_cartesianProduct ?_ (by simp) hb isBipartite_complete_two
  rw [show 2 * m + 4 = (2 * m + 1) + 3 by ring, E_cycle]
  omega

@[simp] theorem girth_petersen : petersen.girth = 5 := by
  show (kneser 5 2).girth = 5
  rw [kneser_def, girth_mk]
  exact CGraph.girth_kneser_five_two

example : (rook 3 4).girth = 3 := girth_rook (by norm_num) (by norm_num) (by norm_num)

example : (wheel 7).girth = 3 := girth_wheel 4

example : (hypercube 4).girth = 4 := girth_hypercube 2

example : cycle 5 ≠ cycle 4 := ne_of_girth_ne (by simp)

example : petersen ≠ hypercube 4 := ne_of_girth_ne (by simp)

example : ¬ IsAcyclic (cycle 5) := by
  intro h
  have := girth_eq_zero_iff.2 h
  simp at this

/-! ### The disjoint union, the join and the complement -/

attribute [simp] IsoGraph.maxDeg_disjUnion

@[simp] theorem maxDeg_petersen : maxDeg petersen = 3 :=
  maxDeg_of_degMultiset_replicate (n := 10) (by omega) (by simp)

@[simp] theorem minDeg_petersen : minDeg petersen = 3 :=
  minDeg_of_degMultiset_replicate (n := 10) (by omega) (by simp)

@[simp] theorem maxDeg_star (n : ℕ) : maxDeg (star (n + 1)) = n + 1 := by
  refine maxDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_star] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

@[simp] theorem minDeg_star (n : ℕ) : minDeg (star (n + 1)) = 1 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_star] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem maxDeg_wheel (n : ℕ) : maxDeg (wheel (n + 3)) = n + 3 := by
  refine maxDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_wheel] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

@[simp] theorem minDeg_wheel (n : ℕ) : minDeg (wheel (n + 3)) = 3 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_wheel] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem maxDeg_hypercube (n : ℕ) : maxDeg (hypercube n) = n := by
  induction n with
  | zero => rw [hypercube_zero, maxDeg_empty]
  | succ m ih =>
    rw [hypercube_succ, maxDeg_cartesianProduct (by simp) (by simp), ih, maxDeg_complete]

@[simp] theorem minDeg_hypercube (n : ℕ) : minDeg (hypercube n) = n := by
  induction n with
  | zero => rw [hypercube_zero, minDeg_empty]
  | succ m ih =>
    rw [hypercube_succ, minDeg_cartesianProduct (by simp) (by simp), ih, minDeg_complete]

example : maxDeg (bipartite 3 5) = 5 := by
  refine maxDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_bipartite] at hd
  rcases Multiset.mem_add.1 hd with h | h
  · rw [Multiset.eq_of_mem_replicate h]
  · rw [Multiset.eq_of_mem_replicate h]; omega

example : maxDeg (rook 3 4) = 5 := by
  rw [show rook 3 4 = complete 3 □g complete 4 from rfl,
    maxDeg_cartesianProduct (by simp) (by simp), maxDeg_complete, maxDeg_complete]

/- A graph with `Δ = δ` is regular, and the handshake bounds then pin down the edge count. -/

example : 2 * (petersen.E) = 30 := by
  have h1 := V_mul_minDeg_le petersen
  have h2 := two_mul_E_le_V_mul_maxDeg petersen
  rw [V_petersen, minDeg_petersen] at h1
  rw [V_petersen, maxDeg_petersen] at h2
  omega

/- The complement of the `5`-cycle is the `5`-cycle, so both extremes are `2`. -/

example : maxDeg (cycle 5)ᶜ = 2 := by
  rw [maxDeg_compl (by simp)]
  simp

/-! ### The bounds at work -/

/-- The greedy bound is tight on complete graphs. -/
example (n : ℕ) : (complete (n + 1)).chromNum = (complete (n + 1)).maxDeg + 1 := by
  rw [chromNum_complete, maxDeg_complete]
  omega

/-- And on odd cycles, where two colours are not enough. -/
example : (cycle 5).chromNum = (cycle 5).maxDeg + 1 := by
  rw [show (5 : ℕ) = 2 * 1 + 3 from rfl, chromNum_cycle_odd, maxDeg_cycle]

/-- Nordhaus–Gaddum is tight on complete graphs: `n + 1 = |V| + 1`. -/
example (n : ℕ) : (complete (n + 1)).chromNum + (complete (n + 1))ᶜ.chromNum
    = (complete (n + 1)).V + 1 := by
  rw [compl_complete, chromNum_complete, chromNum_empty, V_complete]

/-- The complement of the Petersen graph needs at least four colours. -/
example : 4 ≤ petersenᶜ.chromNum := by
  have h := V_le_chromNum_mul_chromNum_compl petersen
  rw [V_petersen, chromNum_petersen] at h
  omega

/-- Petersen has an independent set of size at least three, because it is `3`-regular. -/
example : 3 ≤ petersen.indepNum := by
  have h := V_le_maxDeg_add_one_mul_indepNum petersen
  rw [V_petersen, maxDeg_petersen] at h
  omega

/-! ### Turán in the complement: few independent vertices means many edges -/

/-- Turán applied to `Gᶜ`: a graph with independence number at most `r` has few *non*-edges. -/
theorem two_mul_mul_E_compl_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.indepNum ≤ r) :
    2 * r * Gᶜ.E ≤ (r - 1) * G.V ^ 2 := by
  have hV : Gᶜ.V = G.V := V_compl G
  have := Gᶜ.two_mul_mul_E_le hr (by rwa [cliqueNum_compl])
  rwa [hV] at this

/-- Consequently a graph with independence number at most `r` has *many* edges: the `Gᶜ` bound
turns into a lower bound on `G.E` through `|E(G)| + |EGᶜ| = C(|V|, 2)`. -/
theorem two_mul_mul_choose_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.indepNum ≤ r) :
    2 * r * G.V.choose 2 ≤ (r - 1) * G.V ^ 2 + 2 * r * G.E := by
  have hsum := G.E_compl
  have hb := G.two_mul_mul_E_compl_le hr h
  calc 2 * r * G.V.choose 2 = 2 * r * Gᶜ.E + 2 * r * G.E := by
        rw [← Nat.mul_add, hsum]
    _ ≤ (r - 1) * G.V ^ 2 + 2 * r * G.E := Nat.add_le_add_right hb _

/-- **Mantel in the complement**: a graph with no three pairwise non-adjacent vertices has at
least `C(n, 2) - n²/4` edges. -/
theorem four_mul_choose_le (G : IsoGraph) (h : G.indepNum ≤ 2) :
    4 * G.V.choose 2 ≤ G.V ^ 2 + 4 * G.E := by
  have := G.two_mul_mul_choose_le (r := 2) (by omega) h
  omega

/-- A self-complementary graph owns exactly half of the possible edges. -/
theorem two_mul_E_of_compl_eq {G : IsoGraph} (h : Gᶜ = G) : 2 * G.E = G.V.choose 2 := by
  have h1 := G.E_compl
  rw [h] at h1
  omega

private theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Nat.choose_two_right, Nat.succ_sub_one]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    have h : (m + 1) * m = 2 * k := by rw [Nat.mul_comm]; omega
    rw [h]
    omega

/-- **A self-complementary graph has `|V| ≡ 0` or `1 (mod 4)`**: it owns half of the `C(|V|, 2)`
possible edges, so `4` divides `|V| · (|V| - 1)`. -/
theorem V_mod_four_of_compl_eq {G : IsoGraph} (h : Gᶜ = G) :
    G.V % 4 = 0 ∨ G.V % 4 = 1 := by
  have h1 := two_mul_E_of_compl_eq h
  have h2 := two_mul_choose_two G.V
  have h3 : 4 * G.E = G.V * (G.V - 1) := by omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk⟩ : ∃ k, G.V = 4 * k + G.V % 4 := ⟨G.V / 4, by omega⟩
  have hr : G.V % 4 = 2 ∨ G.V % 4 = 3 := by omega
  rcases hr with hr | hr <;> rw [hr] at hk
  · have hexp : G.V * (G.V - 1) = 16 * (k * k) + 12 * k + 2 := by
      rw [hk, show 4 * k + 2 - 1 = 4 * k + 1 from by omega]; ring
    omega
  · have hexp : G.V * (G.V - 1) = 16 * (k * k) + 20 * k + 6 := by
      rw [hk, show 4 * k + 3 - 1 = 4 * k + 2 from by omega]; ring
    omega

/-! ### The clique-count table -/

@[simp] theorem cliqueCount_cycle_even (m : ℕ) : (cycle (2 * m)).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_cycle_even m)

@[simp] theorem cliqueCount_cycle_four : (cycle 4).cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_cycle_four]
  omega

@[simp] theorem cliqueCount_cycle_five : (cycle 5).cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_cycle_five]
  omega

/-- The complement of a disconnected graph — in particular of any disjoint union of two
nonempty graphs — is dominated by two vertices. -/
theorem domNum_compl_disjUnion_le_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H)ᶜ.domNum ≤ 2 :=
  domNum_compl_le_two_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

/-! ### Degrees in the line graph -/

/-- Two edge counts of a regular graph: `L(G)` is `(2k - 2)`-regular on `|E|` vertices. -/
theorem IsRegularWith.two_mul_E_lineGraph {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    2 * (IsoGraph.lineGraph G).E = G.E * (2 * k - 2) := by
  have h2 := h.lineGraph.two_mul_E
  rwa [V_lineGraph] at h2

/-- Counting the pairs of edges at each vertex: `|E(L(G))| = n * C(k, 2)` for a `k`-regular
graph on `n` vertices.  This drops the strong regularity hypothesis of `IsSRGWith.E_lineGraph`. -/
theorem IsRegularWith.E_lineGraph {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    (IsoGraph.lineGraph G).E = G.V * k.choose 2 := by
  rw [IsoGraph.E_lineGraph, h.degSequence, List.map_replicate, List.sum_replicate, smul_eq_mul]

/-! ### Matchings and edge colourings of the named families

Whenever the line graph of a family is itself a named graph, the matching number and the
chromatic index of that family are read off from the independence and chromatic numbers of
the line graph, which are already known. -/

@[toIsoGraph simp]
theorem _root_.CGraph.edgeChromNum_eq_zero_iff {G : CGraph} : G.edgeChromNum = 0 ↔ G.E = 0 := by
  show G.lineGraph.chromNum = 0 ↔ G.E = 0
  rw [CGraph.chromNum_eq_zero_iff, CGraph.card_lineGraph]

@[toIsoGraph]
theorem _root_.CGraph.edgeChromNum_pos {G : CGraph} (h : 0 < G.E) : 0 < G.edgeChromNum := by
  rcases Nat.eq_zero_or_pos G.edgeChromNum with h0 | h0
  · rw [CGraph.edgeChromNum_eq_zero_iff] at h0; omega
  · exact h0

/-- The line graph of a cycle is that same cycle, so a maximum matching of `C_n` is a maximum
independent set of `C_n`. -/
@[simp] theorem matchNum_cycle (n : ℕ) : (cycle (n + 3)).matchNum = (n + 3) / 2 := by
  rw [matchNum_eq, lineGraph_cycle, indepNum_cycle]

@[simp] theorem matchNum_complete_three : (complete 3).matchNum = 1 := by
  rw [matchNum_eq, lineGraph_complete_three, indepNum_complete]
  omega

/-- `L(K₄)` is the octahedron, whose independence number is `2`: `K₄` has a perfect matching. -/
@[simp] theorem matchNum_complete_four : (complete 4).matchNum = 2 := by
  rw [matchNum_eq, lineGraph_complete_four]
  exact indepNum_cocktailParty 2

/-- An even cycle is `2`-edge-colourable. -/
@[simp] theorem edgeChromNum_cycle_even (m : ℕ) : (cycle (2 * m + 4)).edgeChromNum = 2 := by
  rw [edgeChromNum_eq, show 2 * m + 4 = 2 * m + 1 + 3 by ring, lineGraph_cycle,
    show 2 * m + 1 + 3 = 2 * (m + 1) + 2 by ring, chromNum_cycle_even]

/-- An odd cycle needs three edge colours. -/
@[simp] theorem edgeChromNum_cycle_odd (m : ℕ) : (cycle (2 * m + 3)).edgeChromNum = 3 := by
  rw [edgeChromNum_eq, lineGraph_cycle, chromNum_cycle_odd]

/-- `L(P_n)` is `P_{n-1}`, so a path with at least two edges is `2`-edge-colourable. -/
@[simp] theorem edgeChromNum_path (n : ℕ) : (path (n + 3)).edgeChromNum = 2 := by
  rw [edgeChromNum_eq, lineGraph_path, chromNum_path]

@[simp] theorem edgeChromNum_complete_three : (complete 3).edgeChromNum = 3 := by
  rw [edgeChromNum_eq, lineGraph_complete_three, chromNum_complete]

/-- `χ'(K₄) = 3`: its line graph is the octahedron `K_{2,2,2}`, which is `3`-chromatic. -/
@[simp] theorem edgeChromNum_complete_four : (complete 4).edgeChromNum = 3 := by
  rw [edgeChromNum_eq, lineGraph_complete_four, chromNum_cocktailParty]

/-! ### Consequences of self-complementarity -/

/-- A self-complementary graph has exactly half of all possible edges. -/
theorem IsSelfComplementary.two_mul_E {G : IsoGraph} (h : IsSelfComplementary G) :
    2 * G.E = G.V.choose 2 := by
  have h2 := E_compl G
  rw [h.compl_eq] at h2
  omega

theorem IsSelfComplementary.cliqueNum_eq_indepNum {G : IsoGraph} (h : IsSelfComplementary G) :
    G.cliqueNum = G.indepNum := by
  have h2 := cliqueNum_compl G
  rwa [h.compl_eq] at h2

theorem IsSelfComplementary.chromNum_eq_cliqueCoverNum {G : IsoGraph}
    (h : IsSelfComplementary G) : G.chromNum = G.cliqueCoverNum := by
  have h2 := chromNum_compl G
  rwa [h.compl_eq] at h2

/-- Since `V ≤ χ(G) * χ(Gᶜ)`, a self-complementary graph needs at least `√V` colours. -/
theorem IsSelfComplementary.V_le_chromNum_sq {G : IsoGraph} (h : IsSelfComplementary G) :
    G.V ≤ G.chromNum * G.chromNum := by
  have h2 := V_le_chromNum_mul_chromNum_compl G
  rwa [h.compl_eq] at h2

/-- The Nordhaus–Gaddum upper bound, specialised to a self-complementary graph. -/
theorem IsSelfComplementary.two_mul_chromNum_le {G : IsoGraph} (h : IsSelfComplementary G) :
    2 * G.chromNum ≤ G.V + 1 := by
  have h2 := four_mul_chromNum_mul_chromNum_compl_le G
  rw [h.compl_eq, show (G.V + 1) ^ 2 = G.V * G.V + 2 * G.V + 1 from by ring] at h2
  by_contra hc
  have hle : (G.V + 2) * (G.V + 2) ≤ 2 * G.chromNum * (2 * G.chromNum) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [show (G.V + 2) * (G.V + 2) = G.V * G.V + 4 * G.V + 4 from by ring,
    show 2 * G.chromNum * (2 * G.chromNum) = 4 * (G.chromNum * G.chromNum) from by ring] at hle
  omega

theorem IsSelfComplementary.three_le_chromNum {G : IsoGraph} (h : IsSelfComplementary G)
    (hV : 5 ≤ G.V) : 3 ≤ G.chromNum := by
  have h2 := h.V_le_chromNum_sq
  by_contra hc
  have h3 : G.chromNum * G.chromNum ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem IsSelfComplementary.not_isBipartite {G : IsoGraph} (h : IsSelfComplementary G)
    (hV : 5 ≤ G.V) : ¬ IsBipartite G := by
  intro hb
  have h2 := isBipartite_iff_chromNum_le_two.1 hb
  have h3 := h.three_le_chromNum hV
  omega

theorem IsSelfComplementary.E_pos {G : IsoGraph} (h : IsSelfComplementary G) (hV : 2 ≤ G.V) :
    0 < G.E := by
  have h2 := h.two_mul_E
  have h3 := Nat.choose_pos hV
  omega

/-- A self-complementary graph is connected: otherwise its complement, which is the graph
itself, would have diameter two. -/
theorem IsSelfComplementary.isConnected {G : IsoGraph} (h : IsSelfComplementary G)
    (hV : 2 ≤ G.V) : IsConnected G := by
  by_contra hc
  have hd := diameter_compl hc (h.E_pos hV)
  rw [h.compl_eq] at hd
  exact hc (isConnected_of_diameter_ne_zero (by omega))

/-- A self-complementary graph has `0` or `1` vertices mod `4`, since it has half of all
`V.choose 2` possible edges. -/
theorem IsSelfComplementary.V_mod_four {G : IsoGraph} (h : IsSelfComplementary G) :
    G.V % 4 = 0 ∨ G.V % 4 = 1 := by
  have h2 := h.two_mul_E
  exact (choose_two_mod_two_eq_zero_iff G.V).1 (by omega)

/-! ### Graphs that are not self-complementary -/

theorem not_isSelfComplementary_empty (n : ℕ) : ¬ IsSelfComplementary (empty (n + 2)) := by
  intro h
  have h2 := h.two_mul_E
  rw [E_empty, V_empty] at h2
  have h3 := Nat.choose_pos (show 2 ≤ n + 2 by omega)
  omega

theorem not_isSelfComplementary_complete (n : ℕ) : ¬ IsSelfComplementary (complete (n + 2)) := by
  intro h
  have h2 := h.two_mul_E
  rw [E_complete, V_complete] at h2
  have h3 := Nat.choose_pos (show 2 ≤ n + 2 by omega)
  omega

/-! ### Line graphs of regular graphs -/

theorem pos_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) : 0 < n := by
  have h2 := two_mul_E_of_degSequence_replicate h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_mul] at h2
    omega
  · exact hn

theorem maxDeg_eq_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degSequence G = List.replicate n k) : maxDeg G = k :=
  maxDeg_of_degMultiset_replicate hn (degMultiset_of_degSequence h)

theorem minDeg_eq_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degSequence G = List.replicate n k) : minDeg G = k :=
  minDeg_of_degMultiset_replicate hn (degMultiset_of_degSequence h)

/-- A `k`-regular graph on `n` vertices has a line graph with `n * k.choose 2` edges: one for
each pair of edges meeting at a common vertex. -/
theorem E_lineGraph_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : (lineGraph G).E = n * k.choose 2 := by
  rw [E_lineGraph, h, List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- Counting the same edges through `|E| = n * k / 2`. -/
theorem two_mul_E_lineGraph_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) :
    2 * (lineGraph G).E = 2 * G.E * (k - 1) := by
  have h1 := E_lineGraph_of_degSequence_replicate h
  have h2 := two_mul_E_of_degSequence_replicate h
  calc 2 * (lineGraph G).E = n * (2 * k.choose 2) := by rw [h1]; ring
    _ = n * (k * (k - 1)) := by rw [two_mul_choose_two]
    _ = n * k * (k - 1) := by rw [Nat.mul_assoc]
    _ = 2 * G.E * (k - 1) := by rw [h2]

/-- **The line graph of a `k`-regular graph is `(2k - 2)`-regular.** -/
theorem isRegularWith_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    (lineGraph G).IsRegularWith (2 * k - 2) := by
  have hn := pos_of_degSequence_replicate hE h
  refine isRegularWith_of_maxDeg_le_of_le_minDeg ?_ ?_
  · have h3 := maxDeg_lineGraph_le G
    rwa [maxDeg_eq_of_degSequence_replicate hn h] at h3
  · have h3 := le_minDeg_lineGraph hE
    rwa [minDeg_eq_of_degSequence_replicate hn h] at h3

theorem maxDeg_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) : maxDeg (lineGraph G) = 2 * k - 2 := by
  have hn := pos_of_degSequence_replicate hE h
  have h1 := maxDeg_lineGraph_le G
  rw [maxDeg_eq_of_degSequence_replicate hn h] at h1
  have h2 := le_minDeg_lineGraph hE
  rw [minDeg_eq_of_degSequence_replicate hn h] at h2
  have h3 := minDeg_le_maxDeg (lineGraph G)
  omega

theorem minDeg_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) : minDeg (lineGraph G) = 2 * k - 2 := by
  have hn := pos_of_degSequence_replicate hE h
  have h1 := maxDeg_lineGraph_le G
  rw [maxDeg_eq_of_degSequence_replicate hn h] at h1
  have h2 := le_minDeg_lineGraph hE
  rw [minDeg_eq_of_degSequence_replicate hn h] at h2
  have h3 := minDeg_le_maxDeg (lineGraph G)
  omega

/-! ### Matchings, radii and clique covers

The four statements below give the matching number of the hypercube and of the cocktail party
graph, the radius of a path, and the matching bound on the clique cover number. -/

/-- Cover the vertices by the edges of a maximum matching plus the leftover singletons. -/
@[toIsoGraph cliqueCoverNum_le_V_sub_matchNum]
theorem _root_.CGraph.cliqueCoverNum_le_card_sub_matchNum (g : CGraph) :
    g.cliqueCoverNum ≤ FinEnum.card g.V - g.matchNum := by
  classical
  show CGraph.chromNum gᶜ ≤ FinEnum.card g.V - (CGraph.lineGraph g).indepNum
  -- Get a max independent set in CGraph.lineGraph g (a max matching)
  obtain ⟨S, hS_indep, hS_card⟩ := (CGraph.lineGraph g).toSimple.exists_isNIndepSet_indepNum
  have hcard : S.card = (CGraph.lineGraph g).indepNum := hS_card
  -- S is an indep set in CGraph.lineGraph g, i.e., a matching in g.
  -- Build the set of vertices covered by edges in S.
  set matchedS := S.biUnion (fun e : (CGraph.lineGraph g).V => e.1.toFinset) with hmatchedS_def
  -- The edges in S are pairwise vertex-disjoint (indep set in lineGraph)
  have hdisjoint : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (e.1.toFinset) (f.1.toFinset) := by
    intro e he f hf hef
    exact CGraph.disjoint_of_not_adj_lineGraph g hef
      (hS_indep (by simpa using he) (by simpa using hf) hef)
  -- Each edge in S has exactly 2 vertices
  have heap_edge : ∀ e ∈ S, e.1.toFinset.card = 2 := by
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e.1 (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)
  -- matchedS.card = 2 * S.card
  have hmatched_card : matchedS.card = 2 * S.card := by
    rw [hmatchedS_def, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun e _ => heap_edge e ‹_›]
      simp [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    · exact fun e he f hf hef => hdisjoint e he f hf hef
  -- Equivalently, 2 * indepNum ≤ V
  have h2le : 2 * (CGraph.lineGraph g).indepNum ≤ FinEnum.card g.V :=
    CGraph.two_mul_indepNum_lineGraph_le_card g
  -- Unmatched vertices
  set unmatchedS := Finset.univ \ matchedS with hunmatchedS_def
  have hunmatched_card :
      unmatchedS.card = FinEnum.card g.V - 2 * (CGraph.lineGraph g).indepNum := by
    have : unmatchedS.card = FinEnum.card g.V - matchedS.card := by
      rw [hunmatchedS_def, Finset.card_sdiff_of_subset (Finset.subset_univ matchedS),
        FinEnum.card_univ]
    rw [this, hmatched_card, hcard]
  -- Build coloring
  rw [CGraph.chromNum_le_iff_colorable]
  -- Coloring of gᶜ.toSimple with (V - S.card) colors.
  -- Matched vertices (in edges of S) get colors 0..S.card-1, the same colour for both
  -- endpoints of an edge.
  -- Unmatched vertices get colors S.card..V-S.card-1 (each unique).
  -- Since S.card + (V - 2*S.card) = V - S.card, this uses V-S.card colors.
  -- Valid: same-color vertices are either in the same edge of S (adjacent in g, so not in
  --   the complement) or are the same unmatched vertex.
  set equivS' : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp) with hequivS'_def
  -- For each matched vertex, identify its edge in S
  have hvedge : ∀ v ∈ matchedS, ∃ e ∈ S, v ∈ e.1.toFinset := by
    simp [hmatchedS_def, Finset.mem_biUnion]
  let edgeOf : {v : g.V // v ∈ matchedS} → S := fun p =>
    ⟨Classical.choose (hvedge p.val p.property),
      (Classical.choose_spec (hvedge p.val p.property)).1⟩
  have hedge_mem : ∀ v hv, v ∈ (edgeOf ⟨v, hv⟩ : (CGraph.lineGraph g).V).1.toFinset :=
    fun v hv => (Classical.choose_spec (hvedge v hv)).2
  -- The color function
  -- For unmatched vertices, we need an equiv with Fin (V - 2*S.card)
  have hcard_unmatched :
      Fintype.card {v : g.V // v ∉ matchedS} = FinEnum.card g.V - 2 * S.card := by
    have h1 : Fintype.card {v : g.V // v ∉ matchedS} = FinEnum.card g.V - matchedS.card := by
      rw [Fintype.card_subtype_compl]
      simp
    rw [h1, hmatched_card, hcard]
  let unmatchedEmb : {v : g.V // v ∉ matchedS} ≃ Fin (FinEnum.card g.V - 2 * S.card) :=
    Fintype.equivFinOfCardEq hcard_unmatched
  let f : g.V → ℕ := fun v =>
    if hv : v ∈ matchedS then
      equivS' (edgeOf ⟨v, hv⟩)
    else
      S.card + (unmatchedEmb ⟨v, hv⟩ : ℕ)
  -- Show f is a valid coloring of gᶜ.toSimple
  refine SimpleGraph.colorable_iff_exists_bdd_nat_coloring _ |>.2 ?_
  refine ⟨SimpleGraph.Coloring.mk f ?_, fun v => ?_⟩
  · -- Adjacent in the complement → different colors
    intro u v huv
    simp at huv
    -- huv : ¬ g.toSimple.Adj u v (and u ≠ v implied)
    by_cases hu : u ∈ matchedS
    · by_cases hv : v ∈ matchedS
      · -- Both matched
        set e₁ := edgeOf ⟨u, hu⟩
        set e₂ := edgeOf ⟨v, hv⟩
        simp [f, hu, hv, hequivS'_def]
        by_cases hsame : e₁ = e₂
        · -- Same edge: u, v are both in e₁.1.toFinset, so u = v or Adj in g. Contradiction.
          exfalso
          have hu' : u ∈ (e₁ : (CGraph.lineGraph g).V).1.toFinset := hedge_mem u hu
          have hv' : v ∈ (e₁ : (CGraph.lineGraph g).V).1.toFinset := by
            simpa [hsame] using hedge_mem v hv
          have he_edgeSet : (e₁ : (CGraph.lineGraph g).V).1 ∈ g.toSimple.edgeSet := e₁.1.2
          have hadj : g.Adj u v := by
            generalize (e₁ : (CGraph.lineGraph g).V).1 = se at hu' hv' he_edgeSet ⊢
            induction se using Sym2.ind with
            | _ a b =>
              simp [Sym2.mem_toFinset, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
                at hu' hv' he_edgeSet ⊢
              rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> simp_all
              exact absurd (huv.2 ▸ g.symm u v ▸ he_edgeSet) (by decide)
          exact absurd (huv.2 ▸ hadj) (by decide)
        · -- Different edges: colors are equivS' e₁ and equivS' e₂, different.
          intro heq
          apply hsame
          exact equivS'.injective (Fin.ext heq)
      · -- u matched, v unmatched
        simp [f, hu, hv]
        intro heq
        have : (equivS' (edgeOf ⟨u, hu⟩) : ℕ) < S.card := Fin.isLt _
        omega
    · by_cases hv : v ∈ matchedS
      · -- u unmatched, v matched
        simp [f, hu, hv]
        intro heq
        have : (equivS' (edgeOf ⟨v, hv⟩) : ℕ) < S.card := Fin.isLt _
        omega
      · -- Both unmatched
        simp [f, hu, hv]
        intro heq
        have huv' : u ≠ v := huv.1
        apply huv'
        exact Subtype.ext_iff.mp (unmatchedEmb.injective (Fin.ext heq))
  · -- Color bound
    by_cases hv : v ∈ matchedS
    · show f v < FinEnum.card g.V - g.lineGraph.indepNum
      simp [f, hv]
      have h1 : (equivS' (edgeOf ⟨v, hv⟩) : ℕ) < S.card := Fin.isLt _
      have h2le' : 2 * S.card ≤ FinEnum.card g.V := by rw [← hcard] at h2le; exact h2le
      have hle : S.card ≤ FinEnum.card g.V - S.card := by omega
      have : FinEnum.card g.V - g.lineGraph.indepNum = FinEnum.card g.V - S.card := by rw [hcard]
      rw [this]
      exact lt_of_lt_of_le h1 hle
    · show f v < FinEnum.card g.V - g.lineGraph.indepNum
      simp [f, hv]
      have h1 : (unmatchedEmb ⟨v, hv⟩ : ℕ) < FinEnum.card g.V - 2 * S.card := Fin.isLt _
      have h2le' : 2 * S.card ≤ FinEnum.card g.V := by rw [← hcard] at h2le; exact h2le
      have hle : S.card ≤ FinEnum.card g.V - S.card := by omega
      have hbound : FinEnum.card g.V - g.lineGraph.indepNum = FinEnum.card g.V - S.card := by
        rw [hcard]
      rw [hbound]
      omega

/-- **The clique cover number of a cycle**: `θ(Cₙ) = ⌈n/2⌉` once the cycle has no triangle. -/
@[simp] theorem cliqueCoverNum_cycle (n : ℕ) :
    (cycle (n + 4)).cliqueCoverNum = (n + 5) / 2 := by
  have hm : (cycle (n + 4)).matchNum = (n + 4) / 2 := matchNum_cycle (n + 1)
  have h1 := cliqueCoverNum_le_V_sub_matchNum (cycle (n + 4))
  rw [V_cycle, hm] at h1
  have h2 := V_le_cliqueCoverNum_mul_cliqueNum (cycle (n + 4))
  rw [V_cycle, cliqueNum_cycle] at h2
  omega

@[simp] theorem cliqueCoverNum_cycle_three : (cycle 3).cliqueCoverNum = 1 := by
  rw [cycle_three, cliqueCoverNum_complete]

/-- The radius of a strong product is the maximum of the radii. -/
theorem radius_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ⊠g H).radius = max G.radius H.radius := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [strongProduct_mk, radius_mk, radius_mk, radius_mk]
  rw [isConnected_mk] at hG hH
  haveI : Nonempty g.V := hG.nonempty
  haveI : Nonempty h.V := hH.nonempty
  simp only [CGraph.radius, CGraph.radius_strongProduct_enat]
  exact ENat.toNat_max _ _ (SimpleGraph.radius_ne_top_iff.2 hG)
    (SimpleGraph.radius_ne_top_iff.2 hH)

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

/-- In the strong product, distances are the maximum of the two coordinate distances, so the
diameter is the maximum of the two diameters. -/
theorem diameter_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ⊠g H).diameter = max G.diameter H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [strongProduct_mk, diameter_mk, diameter_mk, diameter_mk]
  rw [isConnected_mk] at hG hH
  haveI : Nonempty g.V := hG.nonempty
  haveI : Nonempty h.V := hH.nonempty
  simp only [CGraph.diameter, SimpleGraph.diam, CGraph.ediam_strongProduct]
  exact ENat.toNat_max _ _ (SimpleGraph.connected_iff_ediam_ne_top.1 hG)
    (SimpleGraph.connected_iff_ediam_ne_top.1 hH)

@[simp] theorem diameter_strongProduct_cycle (m n : ℕ) :
    (cycle (m + 1) ⊠g cycle (n + 1)).diameter = max ((m + 1) / 2) ((n + 1) / 2) := by
  rw [diameter_strongProduct (isConnected_cycle m) (isConnected_cycle n), diameter_cycle,
    diameter_cycle]

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

theorem radius_lineGraph_le {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E) :
    (lineGraph G).radius ≤ G.radius + 1 := by
  induction G using Quotient.inductionOn with | h g =>
  haveI : Nonempty g.V := hG.nonempty
  simp [radius_mk, lineGraph_mk]
  rw [isConnected_mk] at hG
  rw [E_mk] at hE
  set S : SimpleGraph g.V := g.toSimple
  set LG_def : SimpleGraph g.lineGraph.V := (CGraph.lineGraph g).toSimple
  --LG_def is LG
  simp only [CGraph.radius, CGraph.toSimple]
  have hSconn : S.Connected := hG
  by_cases hLGconn : LG_def.Connected
  · show LG_def.radius.toNat ≤ S.radius.toNat + 1
    have hSnediam : S.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hSconn
    obtain ⟨v, hv⟩ := SimpleGraph.exists_eccent_eq_radius (G := S)
    have hne : Nontrivial g.V := by
      have hEc : 0 < g.toSimple.edgeFinset.card := by simpa [CGraph.E] using hE
      obtain ⟨e, he⟩ := Finset.card_pos.mp hEc
      simp only [SimpleGraph.mem_edgeFinset] at he
      have hek := he
      have hne' : ∃ a b : g.V, a ≠ b := by
        induction e using Sym2.ind with
        | _ a b =>
          rw [SimpleGraph.mem_edgeSet] at hek
          by_cases hab : a = b
          · rw [hab] at hek; simp at hek
          · exact ⟨a, b, hab⟩
      exact ⟨hne'.choose, hne'.choose_spec.choose, hne'.choose_spec.choose_spec⟩
    have hvadj : ∃ w : g.V, S.Adj v w := by
      obtain ⟨u, hu⟩ := exists_ne v
      have hr : S.Reachable v u := hSconn v u
      have := g.exists_adj_dist_lt (r := u) (show g.toSimple.Reachable v u from hr) (Ne.symm hu)
      exact ⟨this.choose, this.choose_spec.1⟩
    obtain ⟨w, hw⟩ : ∃ w : g.V, g.Adj v w := by simpa [CGraph.toSimple_adj] using hvadj
    let e0 : g.lineGraph.V :=
      ⟨Sym2.mk (v, w), by simpa [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] using hw⟩
    -- Adjacency in LG_def
    have hadjLG : ∀ e f : g.lineGraph.V,
        LG_def.Adj e f ↔ e ≠ f ∧ ∃ x : g.V, x ∈ (e.1 : Sym2 g.V) ∧ x ∈ (f.1 : Sym2 g.V) := by
      intro e f
      simp [LG_def, CGraph.toSimple, CGraph.lineGraph_adj, Bool.and_eq_true]
    -- endpoint of any linegraph vertex
    have hendpoint : ∀ (e : g.lineGraph.V), ∃ (x : g.V), x ∈ (e.1 : Sym2 g.V) := by
      intro ⟨se, _⟩
      induction se using Sym2.ind with
      | _ a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
    -- shared vertex => edist ≤ 1
    have hshared : ∀ (e f : g.lineGraph.V) (x : g.V), x ∈ (e.1 : Sym2 g.V) → x ∈ (f.1 : Sym2 g.V) →
        LG_def.edist e f ≤ 1 := by
      intro e f x hev hfx
      by_cases heq : e = f
      · rw [heq]; simp
      · have hadj_ef : LG_def.Adj e f := (hadjLG e f).mpr ⟨heq, x, hev, hfx⟩
        exact le_trans
          (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj_ef SimpleGraph.Walk.nil)) (by simp)
    -- walk lifting from S to LG_def
    have hwalk_lift : ∀ (v : g.V) {u : g.V} (p : S.Walk v u) (e : g.lineGraph.V),
        v ∈ (e.1 : Sym2 g.V) →
        ∃ e' : g.lineGraph.V, u ∈ (e'.1 : Sym2 g.V) ∧ LG_def.edist e e' ≤ ↑p.length := by
      intro v u p e hev
      induction p using SimpleGraph.Walk.rec generalizing e with
      | nil =>
        exact ⟨e, hev, by rw [SimpleGraph.edist_self]; simp⟩
      | @cons x y z huv_tail wtail ih =>
        let huv_tail' : S.Adj x y := by rwa [CGraph.toSimple_adj]
        let ep : g.lineGraph.V :=
          ⟨Sym2.mk (x, y), by simpa [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] using huv_tail'⟩
        have hev' : y ∈ (ep.1 : Sym2 g.V) := Sym2.mem_mk_right _ _
        have heu' : x ∈ (e.1 : Sym2 g.V) := hev
        have hep_u' : x ∈ (ep.1 : Sym2 g.V) := Sym2.mem_mk_left _ _
        have hstep : LG_def.edist e ep ≤ 1 := by
          by_cases heq : e = ep
          · rw [heq]; simp
          · have hadj_ef : LG_def.Adj e ep := (hadjLG e ep).mpr ⟨heq, x, heu', hep_u'⟩
            exact le_trans
              (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hadj_ef SimpleGraph.Walk.nil))
              (by simp)
        obtain ⟨e', hvz', hdist'⟩ := ih ep hev'
        have hels : LG_def.edist e e' ≤ LG_def.edist e ep + LG_def.edist ep e' :=
          LG_def.edist_triangle
        have hels'' : LG_def.edist e e' ≤ 1 + ↑wtail.length := hels.trans (add_le_add hstep hdist')
        have hels_final : LG_def.edist e e' ≤ ↑(wtail.length + 1) := hels''.trans (by
          show (1 : ℕ∞) + ↑wtail.length ≤ ↑(wtail.length + 1)
          simp [Nat.cast_add, add_comm])
        exact ⟨e', hvz', hels_final⟩
    -- eccent LG(e0) ≤ S.radius + 1
    have hecc_e0 : LG_def.eccent e0 ≤ ↑S.radius.toNat + 1 := by
      haveI : Nonempty g.lineGraph.V := by
        have hcard : 0 < FinEnum.card (g.lineGraph).V := by rw [CGraph.card_lineGraph]; exact hE
        exact FinEnum.card_pos_iff.mp hcard
      unfold SimpleGraph.eccent
      apply ciSup_le
      intro f
      obtain ⟨u, hu⟩ := hendpoint f
      have hreach : S.Reachable v u := hSconn v u
      obtain ⟨p, hp_len⟩ := hreach.exists_walk_length_eq_dist
      obtain ⟨e', hue', hlift⟩ := hwalk_lift v p e0 (Sym2.mem_mk_left _ _)
      have hels : LG_def.edist e0 f ≤ ↑(S.dist v u) + 1 := by
        calc LG_def.edist e0 f ≤ LG_def.edist e0 e' + LG_def.edist e' f := LG_def.edist_triangle
          _ ≤ ↑p.length + 1 := add_le_add hlift (hshared e' f u hue' hu)
          _ = ↑(S.dist v u) + 1 := by rw [hp_len]
      have hdist_le_radius : (S.dist v u : ℕ∞) ≤ ↑S.radius.toNat := by
        have h1 := @SimpleGraph.edist_le_eccent g.V S v u
        rw [hv] at h1
        have h2 : S.edist v u = ↑(S.dist v u) := by
          have key : ∀ (q : S.Walk v u), S.dist v u ≤ q.length := fun q => SimpleGraph.dist_le q
          apply le_antisymm
          · have := SimpleGraph.Walk.edist_le p; simp [hp_len] at this; exact this
          · rw [SimpleGraph.edist]
            exact le_iInf fun q => mod_cast key q
        rw [h2] at h1
        have hradius_ne_top : S.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hSconn
        have h1' : S.edist v u ≤ S.radius := by rw [h2]; exact h1
        have h3 : S.dist v u ≤ S.radius.toNat := ENat.toNat_le_toNat h1' hradius_ne_top
        exact_mod_cast h3
      exact hels.trans (add_le_add hdist_le_radius le_rfl)
    -- radius ≤ eccent
    have hradius_le : LG_def.radius ≤ LG_def.eccent e0 := SimpleGraph.radius_le_eccent
    exact ENat.toNat_le_of_le_coe (hradius_le.trans hecc_e0)
  · -- LG disconnected
    have hLGtop : LG_def.radius = ⊤ := SimpleGraph.radius_eq_top_of_not_connected hLGconn
    show LG_def.radius.toNat ≤ S.radius.toNat + 1
    rw [hLGtop]; simp

@[simp] theorem cliqueCoverNum_cycle_odd (m : ℕ) : (cycle (2 * m + 5)).cliqueCoverNum = m + 3 := by
  rw [show 2 * m + 5 = (2 * m + 1) + 4 from by omega, cliqueCoverNum_cycle]
  omega

/-- **A complete graph of even order is class one.**  Label the vertices by `ℤ/(2m+3)` together
with an extra point; colour the edge `{i, j}` by `i + j` and the edge from the extra point to `i`
by `2i`, a round-robin schedule with `2m+3` colours. -/
theorem edgeChromNum_complete_even_add_four (m : ℕ) :
    (complete (2 * m + 4)).edgeChromNum = 2 * m + 3 := by
  have hlower : 2 * m + 3 ≤ (complete (2 * m + 4)).edgeChromNum := by
    have hE := E_complete (2 * m + 4)
    have hm := matchNum_complete (2 * m + 4)
    have h1 := E_le_edgeChromNum_mul_matchNum (complete (2 * m + 4))
    rw [hE, hm] at h1
    rw [Nat.choose_two_right] at h1
    rw [show (2 * m + 4) / 2 = m + 2 from by omega] at h1
    simp only [show 2 * m + 4 - 1 = 2 * m + 3 from by omega] at h1
    have hdiv : (2 * m + 4) * (2 * m + 3) / 2 = (m + 2) * (2 * m + 3) := by
      rw [show 2 * m + 4 = 2 * (m + 2) from by omega]
      simp [mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    rw [hdiv] at h1
    nlinarith
  have hupper : (complete (2 * m + 4)).edgeChromNum ≤ 2 * m + 3 := by
    simp only [complete]
    set n := 2 * m + 3 with hn_def
    set inv2 := m + 2 with hinv2_def
    have hmod : 2 * (m + 2) = (2 * m + 3) + 1 := by ring
    have hmul_inv2 (k : ℕ) : 2 * (k * inv2 % n) % n = k % n := by
      have h2inv : 2 * inv2 = n + 1 := hmod
      set q := k * inv2 / n
      set r := k * inv2 % n
      have hdiv : n * q + r = k * inv2 := Nat.div_add_mod _ _
      have hkey : 2 * (n * q + r) = n * k + k := by
        calc 2 * (n * q + r) = 2 * (k * inv2) := by rw [hdiv]
          _ = (n + 1) * k := by rw [← h2inv]; ring
          _ = n * k + k := by ring
      -- 2*r ≡ k (mod n)
      have hmod2 : (2 * r : ℤ) % (n : ℤ) = (k : ℤ) % (n : ℤ) := by
        have : (2 * r : ℤ) = (n : ℤ) * (↑k - 2 * ↑q) + (k : ℤ) := by linarith
        rw [this, Int.add_emod, Int.mul_emod]
        simp
      exact_mod_cast hmod2
    let colorFn : Fin (n + 1) → Fin (n + 1) → Fin n := fun a b =>
      if ha : (a : ℕ) = n then ⟨(b : ℕ) % n, Nat.mod_lt _ (by omega)⟩
      else if hb : (b : ℕ) = n then ⟨(a : ℕ) % n, Nat.mod_lt _ (by omega)⟩
      else ⟨((a : ℕ) + (b : ℕ)) * inv2 % n, Nat.mod_lt _ (by omega)⟩
    have hsym : ∀ a b, colorFn a b = colorFn b a := by
      intro a b; dsimp [colorFn]
      split_ifs with ha hb <;> simp_all
      · rw [show (↑b + ↑a : ℕ) = ↑a + ↑b from by omega]
    have hcolorFn_ne : ∀ (v x y : Fin (n + 1)), x ≠ y → x ≠ v → y ≠ v →
        colorFn v x ≠ colorFn v y := by
      intro v x y hxy hxv hyv
      dsimp [colorFn]
      by_cases hv : (v : ℕ) = n
      · -- v = last n: x, y ≠ last n
        have hxne_n : (x : ℕ) ≠ n := by intro h; exact hxv (Fin.ext (by omega))
        have hyne_n : (y : ℕ) ≠ n := by intro h; exact hyv (Fin.ext (by omega))
        simp [hv]
        intro h
        have hxlt : (x : ℕ) < n := Nat.lt_of_le_of_ne (Fin.is_le x) hxne_n
        have hylt : (y : ℕ) < n := Nat.lt_of_le_of_ne (Fin.is_le y) hyne_n
        have h2 : (x : ℕ) % n = (y : ℕ) % n := h
        exact hxy (Fin.ext (by simp [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at h2; exact h2))
      · push_neg at hv
        have hvlt : (v : ℕ) < n := Nat.lt_of_le_of_ne (Fin.is_le v) hv
        -- Helper: from 2*a % n = (a + b) % n with a,b < n, deduce a = b
        have heq_of_double : ∀ (a b : ℕ), a < n → b < n → 2 * a % n = (a + b) % n → a = b := by
          intro a b ha hb h
          have h1 : ((2 * a : ℤ) % (n : ℤ)) = ((a + b : ℤ) % (n : ℤ)) := by exact_mod_cast h
          have h2 : ((a : ℤ) - (b : ℤ)) % (n : ℤ) = 0 := by
            rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h1
            ring_nf at h1 ⊢; exact h1
          obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h2
          have : (a : ℤ) = (b : ℤ) := by nlinarith [show k = 0 from by nlinarith]
          exact_mod_cast this
        by_cases hx : (x : ℕ) = n
        · have hyne_n : (y : ℕ) ≠ n := by intro h; exact hxy (Fin.ext (by omega))
          simp [hv, hx, hyne_n]
          intro h
          have this := hmul_inv2 (v + y)
          rw [h.symm] at this
          rw [Nat.mod_eq_of_lt hvlt] at this
          exact hyv (Fin.ext (heq_of_double v y hvlt
            (Nat.lt_of_le_of_ne (Fin.is_le y) hyne_n) this).symm)
        · push_neg at hx
          have hxlt : (x : ℕ) < n := Nat.lt_of_le_of_ne (Fin.is_le x) hx
          by_cases hy : (y : ℕ) = n
          · simp [hv, hx, hy]
            intro h
            have key := hmul_inv2 (v + x)
            rw [h] at key
            rw [Nat.mod_eq_of_lt hvlt] at key
            exact hxv (Fin.ext (heq_of_double v x hvlt hxlt key).symm)
          · push_neg at hy
            have hylt : (y : ℕ) < n := Nat.lt_of_le_of_ne (Fin.is_le y) hy
            simp [hv, hx, hy]
            intro h
            have keyx := hmul_inv2 (v + x)
            have keyy := hmul_inv2 (v + y)
            rw [h] at keyx
            rw [keyy] at keyx
            have h_eq : (x : ℕ) = (y : ℕ) := by
              have h1 : ((v + y : ℤ) % (n : ℤ)) = ((v + x : ℤ) % (n : ℤ)) := by exact_mod_cast keyx
              have h2 : ((y : ℤ) - (x : ℤ)) % (n : ℤ) = 0 := by
                rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h1
                ring_nf at h1 ⊢; exact h1
              obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h2
              have : (y : ℤ) = (x : ℤ) := by nlinarith [show k = 0 from by nlinarith]
              exact_mod_cast this.symm
            exact hxy (Fin.ext h_eq)
    refine edgeChromNum_mk_le_of_colouring colorFn hsym fun u v w huv huw hvw ↦
      hcolorFn_ne u v w hvw ?_ ?_
    · rintro rfl; simp [CGraph.loopless] at huv
    · rintro rfl; simp [CGraph.loopless] at huw
  exact le_antisymm hupper hlower

/-- Every even complete graph beyond the single edge is class one. -/
@[simp] theorem edgeChromNum_complete_even (m : ℕ) :
    (complete (2 * m + 2)).edgeChromNum = 2 * m + 1 := by
  cases m with
  | zero =>
    refine le_antisymm ?_ (edgeChromNum_pos ?_)
    · simpa using edgeChromNum_complete_le 2
    · rw [E_complete]; decide
  | succ k =>
    rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
    exact edgeChromNum_complete_even_add_four k

/-- The radius of a disconnected graph is `0`, matching the convention already used for the
diameter: the true value is `⊤`, and `⊤` truncates to `0`. -/
@[simp] theorem radius_eq_zero_of_not_isConnected {G : IsoGraph} (h : ¬ IsConnected G) :
    G.radius = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [isConnected_mk] at h
  rw [radius_mk]
  show (g.toSimple.radius).toNat = 0
  rw [SimpleGraph.radius_eq_top_of_not_connected h]
  rfl

@[simp] theorem radius_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).radius = 0 :=
  radius_eq_zero_of_not_isConnected (not_isConnected_disjUnion hG hH)

/-- **Domination costs exactly one more in the Mycielskian**: dominate `G`, take the shadows of a
dominating set, and add the apex. -/
theorem domNum_mycielskian (G : IsoGraph) (h : 0 < G.V) :
    (mycielskian G).domNum = G.domNum + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g]
  simp only [IsoGraph.domNum_mk, IsoGraph.V_mk, mycielskian_mk] at h ⊢
  have hlower : ∀ (H : CGraph) [Fintype H.V], 0 < FinEnum.card H.V →
      H.domNum + 1 ≤ H.mycielskian.domNum := by
    intro H _ hH
    -- For any DS D of μ(H), |D| ≥ domNum(H) + 1
    have hlbound : ∀ (D : Finset (Option (H.V ⊕ H.V))),
        (CGraph.mycielskian H).IsDominatingSet D → H.domNum + 1 ≤ D.card := by
      intro D hDDom
      -- Helper: project Option (H.V ⊕ H.V) to H.V, sending none to an arbitrary vertex
      let decode : Option (H.V ⊕ H.V) → H.V := fun x =>
        match x with
        | none => Classical.choice (FinEnum.card_pos_iff.mp hH)
        | some (Sum.inl v) => v
        | some (Sum.inr v) => v
      have hdecode_inl : ∀ v, decode (some (Sum.inl v)) = v := fun v => rfl
      have hdecode_inr : ∀ v, decode (some (Sum.inr v)) = v := fun v => rfl
      let f_inl : H.V → Option (H.V ⊕ H.V) := fun v => some (Sum.inl v)
      let f_inr : H.V → Option (H.V ⊕ H.V) := fun v => some (Sum.inr v)
      have hinj_inl : Function.Injective f_inl := fun a b h => Sum.inl_injective
          (Option.some_injective _ h)
      have hinj_inr : Function.Injective f_inr := fun a b h => Sum.inr_injective
          (Option.some_injective _ h)
      -- O' = originals in D (as Finset H.V)
      let O' : Finset H.V := Finset.univ.filter (fun v => some (Sum.inl v) ∈ D)
      have hinl_mem : ∀ v, v ∈ O' ↔ some (Sum.inl v) ∈ D := by intro v; simp [O']
      let R' : Finset H.V := Finset.univ.filter (fun v => some (Sum.inr v) ∈ D)
      have hinr_mem : ∀ v, v ∈ R' ↔ some (Sum.inr v) ∈ D := by intro v; simp [R']
      by_cases hnone : none ∈ D
      · -- Case none ∈ D: project D \ {none} to get DS of H
        let S := Finset.image decode (D.erase none)
        have hSdom : H.IsDominatingSet S := by
          intro a
          have hadj := hDDom (some (Sum.inl a))
          rcases hadj with hDal | ⟨u, huD, huAdj⟩
          · left
            apply Finset.mem_image.mpr
            exact ⟨some (Sum.inl a), Finset.mem_erase_of_ne_of_mem (by simp [Option.some_ne_none])
                hDal, hdecode_inl a⟩
          · -- u ≠ none
            have hu_ne : u ≠ none := by
              rintro rfl; simp [CGraph.mycielskian] at huAdj
            right
            refine ⟨decode u, Finset.mem_image_of_mem _
                (by exact Finset.mem_erase_of_ne_of_mem hu_ne huD), ?_⟩
            rcases u with _ | (b | b) <;> simp [hdecode_inl, hdecode_inr] at huAdj ⊢
            · exact huAdj
            · exact huAdj
        have hSsize : S.card ≤ D.card - 1 := by
          exact Finset.card_image_le.trans (by simp [Finset.card_erase_of_mem hnone])
        have hDpos : 1 ≤ D.card := Finset.card_pos.mpr ⟨none, hnone⟩
        have h1 := CGraph.domNum_le_card_of_isDominatingSet hSdom
        omega
      · -- Case none ∉ D
        have hR'nonempty : R'.Nonempty := by
          rcases hDDom none with h | ⟨u, huD, huAdj⟩
          · exact absurd h hnone
          · rcases u with _ | (a | a)
            · exact absurd huD hnone
            · simp [CGraph.mycielskian] at huAdj
            · exact ⟨a, hinr_mem a |>.mpr huD⟩
        obtain ⟨r, hr⟩ := hR'nonempty
        let T := R' \ {r}
        let S2 := O' ∪ T
        have hS2dom : H.IsDominatingSet S2 := by
          intro v
          have hadjR := hDDom (some (Sum.inr v))
          have hadjL := hDDom (some (Sum.inl v))
          by_cases hvR : v ∈ R'
          · by_cases hvr : v = r
            · by_cases hvO : v ∈ O'
              · exact Or.inl (Finset.mem_union_left _ hvO)
              · rcases hadjL with h | ⟨u, huD, huAdj⟩
                · exfalso; simp [hinl_mem] at hvO; exact hvO h
                · rcases u with _ | (a | a)
                  · simp at huAdj
                  · dsimp only [S2]
                    exact Or.inr ⟨a, Finset.mem_union.mpr (Or.inl (hinl_mem a |>.mpr huD)),
                        by simp [CGraph.mycielskian_adj_inl_inl] at huAdj; exact huAdj⟩
                  · right
                    dsimp only [S2]
                    have ha_ne_v : a ≠ v :=
                        by intro heq; rw [heq] at huAdj; exact H.loopless v huAdj
                    have haT : a ∈ T := Finset.mem_sdiff.mpr ⟨hinr_mem a |>.mpr huD, fun h =>
                        ha_ne_v (hvr ▸ Finset.mem_singleton.mp h)⟩
                    exact ⟨a, Finset.mem_union_right _ haT,
                        by simp [CGraph.mycielskian_adj_inr_inl] at huAdj; exact huAdj⟩
            · left
              dsimp only [S2]
              have : v ∈ T := Finset.mem_sdiff.mpr ⟨hvR, fun h => hvr (Finset.mem_singleton.mp h)⟩
              exact Finset.mem_union_right _ this
          · have hnotinR : some (Sum.inr v) ∉ D := fun h => hvR (hinr_mem v |>.mpr h)
            rcases hadjR with h | ⟨u, huD, huAdj⟩
            · exact absurd h hnotinR
            · rcases u with _ | (a | a)
              · exact absurd huD hnone
              · right
                dsimp only [S2]
                exact ⟨a, Finset.mem_union_left _ (hinl_mem a |>.mpr huD),
                    by simp [CGraph.mycielskian_adj_inl_inr] at huAdj; exact huAdj⟩
              · simp [CGraph.mycielskian_adj_inr_inr] at huAdj
        have hOR : O'.card + R'.card ≤ D.card := by
          have hsub : (Finset.image (fun v => some (Sum.inl v)) O') ∪ (Finset.image (fun v => some
              (Sum.inr v)) R') ⊆ D := by
            intro x hx
            simp [Finset.mem_image] at hx
            rcases hx with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
            · exact hinl_mem v |>.mp hv
            · exact hinr_mem v |>.mp hv
          have hdisj : Disjoint (Finset.image (fun v => some (Sum.inl v)) O') (Finset.image (fun v
              => some (Sum.inr v)) R') := by
            simp [Finset.disjoint_left]
          have hcard : ((Finset.image (fun v => some (Sum.inl v)) O') ∪ (Finset.image (fun v =>
              some (Sum.inr v)) R')).card = O'.card + R'.card := by
            rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj_inl,
                Finset.card_image_of_injective _ hinj_inr]
          have := Finset.card_le_card hsub
          rw [hcard] at this; exact this
        have hR'pos : 1 ≤ R'.card := Finset.card_pos.mpr ⟨r, hr⟩
        have hDpos : 1 ≤ D.card := by
          have hsub : Finset.image (fun v => some (Sum.inr v)) R' ⊆ D := by
            intro x hx; simp [Finset.mem_image] at hx; obtain ⟨v, hv,
                rfl⟩ := hx; exact hinr_mem v |>.mp hv
          have := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ hinj_inr] at this
          omega
        have hdomS2 : H.domNum ≤ S2.card := CGraph.domNum_le_card_of_isDominatingSet hS2dom
        have hS2size : S2.card + 1 ≤ D.card := by
          have hTcard : T.card + 1 = R'.card := by
            dsimp only [T]
            rw [Finset.card_sdiff]
            simp [hr]
            omega
          have h1 : S2.card ≤ O'.card + T.card := by
            simpa only [S2] using Finset.card_union_le O' T
          have hTcard' : T.card = R'.card - 1 := by omega
          rw [hTcard'] at h1
          omega
        omega
    obtain ⟨D, hDcard, hDDom⟩ := H.mycielskian.exists_isDominatingSet_domNum
    exact le_trans (hlbound D hDDom) hDcard.le
  have hupper : ∀ (H : CGraph) [Fintype H.V], 0 < FinEnum.card H.V →
      H.mycielskian.domNum ≤ H.domNum + 1 := by
    intro H _ hH
    obtain ⟨S, hScard, hSDS⟩ := H.exists_isDominatingSet_domNum
    let D : Finset (Option (H.V ⊕ H.V)) := {none} ∪ Finset.image (fun v => some (Sum.inl v)) S
    have h_inj :
        Function.Injective (fun v : H.V => some (Sum.inl v) : H.V → Option (H.V ⊕ H.V)) := by
      intro a b h; exact Sum.inl_injective (Option.some_injective _ h)
    have hDsize : D.card = S.card + 1 := by
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_singleton, Finset.card_image_of_injective _ h_inj]
        omega
      · simp
    have hDdom : (CGraph.mycielskian H).IsDominatingSet D := by
      intro w
      match w with
      | none => exact Or.inl (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      | some (Sum.inl a) =>
        rcases hSDS a with ha | ⟨b, hb, hab⟩
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
        · exact
            Or.inr ⟨some (Sum.inl b), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), by
            simp [CGraph.mycielskian] at hab ⊢
            exact hab⟩
      | some (Sum.inr b) =>
        exact Or.inr ⟨none, Finset.mem_union_left _ (Finset.mem_singleton_self _),
            by simp [CGraph.mycielskian]⟩
    calc H.mycielskian.domNum ≤ D.card := CGraph.domNum_le_card_of_isDominatingSet hDdom
      _ = S.card + 1 := hDsize
      _ = H.domNum + 1 := by rw [hScard]
  have h' : 0 < FinEnum.card g.canonicalize.V := by
    simp [CGraph.canonicalize_V]
    exact h
  exact le_antisymm (hupper _ h') (hlower _ h')

/-- If `G` has a perfect matching then `μ(G)` has a near-perfect one: match each vertex with the
shadow of its partner and leave the apex out. -/
@[toIsoGraph matchNum_mycielskian]
theorem _root_.CGraph.matchNum_mycielskian (G : CGraph)
    (h : 2 * G.matchNum = FinEnum.card G.V) :
    (CGraph.mycielskian G).matchNum = FinEnum.card G.V := by
  classical
  refine le_antisymm ?_ ?_
  · have := CGraph.two_mul_matchNum_le_card (CGraph.mycielskian G)
    rw [CGraph.card_mycielskian] at this
    omega
  -- A perfect matching of `G`, read as a maximum independent set `S` of its line graph, with the
  -- two endpoints of each of its edges named.
  obtain ⟨S, hS_indep, hS_card⟩ := (CGraph.lineGraph G).toSimple.exists_isNIndepSet_indepNum
  choose pep hpep using fun e : (CGraph.lineGraph G).V ↦ Sym2.mk_surjective e.1
  let ue : (CGraph.lineGraph G).V → G.V := fun e ↦ (pep e).1
  let ve : (CGraph.lineGraph G).V → G.V := fun e ↦ (pep e).2
  have hend : ∀ e : (CGraph.lineGraph G).V, e.1 = Sym2.mk (ue e, ve e) := fun e ↦ (hpep e).symm
  have hadj : ∀ e : (CGraph.lineGraph G).V, G.Adj (ue e) (ve e) := by
    intro e
    have he : e.1 ∈ G.toSimple.edgeSet := e.2
    rw [hend e, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at he
    exact he
  have hne : ∀ e : (CGraph.lineGraph G).V, ue e ≠ ve e := by
    intro e hval
    have hadje := hadj e
    rw [hval] at hadje
    exact G.loopless _ hadje
  have hmem_ue : ∀ e : (CGraph.lineGraph G).V, ue e ∈ e.1.toFinset := fun e ↦ by
    rw [hend e]; exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)
  have hmem_ve : ∀ e : (CGraph.lineGraph G).V, ve e ∈ e.1.toFinset := fun e ↦ by
    rw [hend e]; exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _)
  -- distinct edges of a matching share no endpoint
  have hdisco : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      ue e ≠ ue f ∧ ue e ≠ ve f ∧ ve e ≠ ue f ∧ ve e ≠ ve f := by
    intro e he f hf hef
    have hd := Finset.disjoint_left.mp (CGraph.disjoint_of_not_adj_lineGraph G hef
      (hS_indep (by simpa using he) (by simpa using hf) hef))
    exact ⟨fun hh ↦ hd (hmem_ue e) (by rw [hh]; exact hmem_ue f),
      fun hh ↦ hd (hmem_ue e) (by rw [hh]; exact hmem_ve f),
      fun hh ↦ hd (hmem_ve e) (by rw [hh]; exact hmem_ue f),
      fun hh ↦ hd (hmem_ve e) (by rw [hh]; exact hmem_ve f)⟩
  -- Each matching edge `{x, y}` of `G` gives two disjoint edges `x—y'` and `y—x'` of the
  -- Mycielskian, joining a vertex to the shadow of its partner.
  let p : {e : (CGraph.lineGraph G).V // e ∈ S} × Bool → G.V × G.V := fun i ↦
    if i.2 then (ve i.1.1, ue i.1.1) else (ue i.1.1, ve i.1.1)
  have hp : ∀ i j, i ≠ j → (p i).1 ≠ (p j).1 ∧ (p i).2 ≠ (p j).2 := by
    rintro ⟨⟨e, heS⟩, be⟩ ⟨⟨f, hfS⟩, bf⟩ hij
    by_cases hef : e = f
    · subst hef
      have hbb : be ≠ bf := by rintro rfl; exact hij rfl
      have h1 := hne e
      cases be <;> cases bf <;> simp only [p, if_true] <;>
        first
          | exact absurd rfl hbb
          | exact ⟨h1, h1.symm⟩
          | exact ⟨h1.symm, h1⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hdisco e heS f hfS hef
      cases be <;> cases bf <;>
        simp only [p, if_true] <;>
        first
          | exact ⟨h1, h4⟩
          | exact ⟨h2, h3⟩
          | exact ⟨h3, h2⟩
          | exact ⟨h4, h1⟩
  have hcard : Fintype.card ({e : (CGraph.lineGraph G).V // e ∈ S} × Bool) = FinEnum.card G.V := by
    replace h : 2 * (CGraph.lineGraph G).toSimple.indepNum = FinEnum.card G.V := h
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, hS_card]
    omega
  rw [← hcard]
  refine CGraph.card_le_matchNum (fun i ↦ some (Sum.inl (p i).1)) (fun i ↦ some (Sum.inr (p i).2))
    ?_ ?_
  · rintro ⟨⟨e, heS⟩, be⟩
    rw [CGraph.mycielskian_adj_inl_inr]
    cases be
    · exact hadj e
    · simpa only [p, if_true] using (G.symm (ue e) (ve e)) ▸ hadj e
  · intro i j hij
    obtain ⟨h1, h2⟩ := hp i j hij
    exact ⟨fun hh ↦ h1 (Sum.inl_injective (Option.some_injective _ hh)),
      fun hh ↦ Sum.inl_ne_inr (Option.some_injective _ hh),
      fun hh ↦ Sum.inl_ne_inr (Option.some_injective _ hh).symm,
      fun hh ↦ h2 (Sum.inr_injective (Option.some_injective _ hh))⟩

/-- The apex is at distance one from the shadows and two from everything else. -/
theorem radius_mycielskian (G : IsoGraph) (h : 0 < G.minDeg) : (mycielskian G).radius = 2 := by
  have hGV : 0 < G.V := by
    induction G using Quotient.inductionOn with | _ g =>
    rw [IsoGraph.minDeg_mk] at h
    rw [IsoGraph.V_mk]
    by_contra hp
    push_neg at hp
    have hc : FinEnum.card g.V = 0 := by omega
    have : g.minDeg = 0 := by
      show g.minDeg = 0
      haveI : IsEmpty g.V := by
        rw [FinEnum.card_eq_zero_iff] at hc; exact hc
      show g.minDeg = 0
      show g.toSimple.minDegree = 0
      rw [SimpleGraph.minDegree]
      simp [Finset.image_empty]
    omega
  -- Helper: for any CGraph H with 0 < H.minDeg, eccent none of mycielskian H ≤ 2
  have hecc_mycielskian_apex (H : CGraph) (hH : 0 < H.minDeg) :
      (CGraph.mycielskian H).toSimple.eccent none ≤ 2 := by
    rw [SimpleGraph.eccent_le_iff]
    intro u
    cases u with
    | none => simp [SimpleGraph.edist_self]
    | some w =>
      cases w with
      | inr b =>
        have hadj : (CGraph.mycielskian H).Adj none (some (.inr
            b)) = true := CGraph.mycielskian_adj_none_inr H b
        show (CGraph.mycielskian H).toSimple.edist none (some (.inr b)) ≤ 2
        calc (CGraph.mycielskian H).toSimple.edist none (some (.inr b))
            ≤ (SimpleGraph.Walk.cons (by exact hadj)
                SimpleGraph.Walk.nil).length := SimpleGraph.edist_le _
          _ = 1 := by simp
          _ ≤ 2 := by decide
      | inl a =>
        -- Need a neighbor of a in H
        have hdeg : 0 < H.toSimple.degree a := by
          exact lt_of_lt_of_le hH (H.minDeg_le_degree a)
        rw [SimpleGraph.degree] at hdeg
        rw [Finset.card_pos] at hdeg
        obtain ⟨d, hd⟩ := hdeg
        simp [SimpleGraph.mem_neighborFinset] at hd
        have h1 : (CGraph.mycielskian H).Adj none (some (.inr
            d)) = true := CGraph.mycielskian_adj_none_inr H d
        have h2 : (CGraph.mycielskian H).Adj (some (.inr d)) (some (.inl a)) = true := by
          rw [CGraph.mycielskian_adj_inr_inl H d a]
          exact (H.symm d a).trans hd
        show (CGraph.mycielskian H).toSimple.edist none (some (.inl a)) ≤ 2
        calc (CGraph.mycielskian H).toSimple.edist none (some (.inl a))
            ≤ (SimpleGraph.Walk.cons (by exact h1) (SimpleGraph.Walk.cons (by exact h2)
                SimpleGraph.Walk.nil)).length := SimpleGraph.edist_le _
          _ = 2 := by simp
          _ ≤ 2 := by decide
  -- Step 1: radius ≤ 2 (apex has eccent ≤ 2)
  have hradius_le : (mycielskian G).radius ≤ 2 := by
    induction G using Quotient.inductionOn with | _ g =>
    show (mycielskian (Quotient.mk _ g)).radius ≤ 2
    rw [IsoGraph.mycielskian_mk, IsoGraph.radius_mk]
    have hcg_minDeg : 0 < g.minDeg := by rwa [IsoGraph.minDeg_mk] at h
    have hecc_le : (CGraph.mycielskian g).toSimple.eccent none ≤ 2 :=
      hecc_mycielskian_apex g hcg_minDeg
    have hradius_eccent : (CGraph.mycielskian g).toSimple.radius ≤
        (CGraph.mycielskian g).toSimple.eccent none :=
      SimpleGraph.radius_le_eccent
    have hradius_le_two : (CGraph.mycielskian g).toSimple.radius ≤ 2 :=
      le_trans hradius_eccent hecc_le
    have hconn : (CGraph.mycielskian g).toSimple.Connected := by
      have := isConnected_mycielskian (Quotient.mk _ g) h
      simp [IsoGraph.IsConnected, IsoGraph.mycielskian_mk] at this
      exact this
    have hne : Nonempty g.mycielskian.V := ⟨none⟩
    have hradius_ne_top : (CGraph.mycielskian g).toSimple.radius ≠ ⊤ :=
      SimpleGraph.radius_ne_top_iff.2 hconn
    show (CGraph.mycielskian g).radius ≤ 2
    rw [CGraph.radius]
    exact ENat.toNat_le_toNat hradius_le_two (by simp)
  -- Step 2: radius ≠ 1 (no universal vertex, domNum ≠ 1)
  have hpos := radius_pos (isConnected_mycielskian G h) (by rw [V_mycielskian]; omega)
  have hdom_ne : (mycielskian G).domNum ≠ 1 := by
    rw [domNum_mycielskian G hGV]
    have := domNum_pos hGV; omega
  have hradius_ne_one : (mycielskian G).radius ≠ 1 := by
    intro h_eq_one
    rw [radius_eq_one_iff_domNum_eq_one (by rw [V_mycielskian]; omega)] at h_eq_one
    exact hdom_ne h_eq_one
  have hr_eq : (mycielskian G).radius = 2 := by
    have hle : (mycielskian G).radius ≤ 2 := hradius_le
    have hne1 : (mycielskian G).radius ≠ 1 := hradius_ne_one
    have hne0 : (mycielskian G).radius ≠ 0 := ne_of_gt hpos
    omega
  exact hr_eq

/-- The contrapositive: an odd cycle somewhere means a cycle somewhere. -/
theorem not_isAcyclic_of_not_isBipartite {G : IsoGraph} (h : ¬ IsBipartite G) : ¬ IsAcyclic G :=
  fun hac ↦ h (isBipartite_of_isAcyclic hac)

/-- One edge of `G` is enough to put a five-cycle inside `μ G`. -/
theorem not_isBipartite_mycielskian_of_E_pos (G : IsoGraph) (h : 0 < G.E) :
    ¬ IsBipartite (mycielskian G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [E_mk] at h
  obtain ⟨a, b, hab⟩ := CGraph.exists_adj_of_E_pos h
  exact not_isBipartite_mycielskian_mk hab

/-- An edge of `G` closes into a pentagon of `μ G`. -/
theorem not_isAcyclic_mycielskian (G : IsoGraph) (h : 0 < G.E) :
    ¬ IsAcyclic (mycielskian G) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_mycielskian_of_E_pos G h)

/-- A triangle-free graph with a perfect matching has a Mycielskian whose clique cover number is
one more than the original vertex count: the cover is by edges, and one vertex is left over. -/
theorem cliqueCoverNum_mycielskian (G : IsoGraph) (hV : 0 < G.V) (hc : G.cliqueNum ≤ 2)
    (hm : 2 * G.matchNum = G.V) : (mycielskian G).cliqueCoverNum = G.V + 1 := by
  have hlb := V_le_cliqueCoverNum_mul_cliqueNum (mycielskian G)
  rw [V_mycielskian, cliqueNum_mycielskian_eq_two hV hc] at hlb
  have hub := cliqueCoverNum_le_V_sub_matchNum (mycielskian G)
  rw [V_mycielskian, matchNum_mycielskian (G := G) hm] at hub
  omega

/-- The apex reaches every shadow and every shadow reaches its original. -/
theorem numComponents_mycielskian (G : IsoGraph) (h : 0 < G.minDeg) :
    (mycielskian G).numComponents = 1 :=
  (numComponents_eq_one_iff _).mpr (isConnected_mycielskian G h)

/-- An edge in each factor gives a triangle in the strong product. -/
theorem not_isAcyclic_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsAcyclic (G ⊠g H) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_strongProduct hG hH)

/-- An edge in each factor gives a triangle in the lexicographic product. -/
theorem not_isAcyclic_lexProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsAcyclic (G ·g H) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_lexProduct hG hH)

/-- A join with a non-bipartite factor keeps that factor's odd cycle. -/
theorem not_isAcyclic_join_left {G H : IsoGraph} (hG : ¬ IsBipartite G) :
    ¬ IsAcyclic (G ∇g H) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_join_left hG)

/-- Three nonempty graphs joined together contain a triangle. -/
theorem not_isAcyclic_join_join {G H K : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) (hK : 0 < K.V) :
    ¬ IsAcyclic (G ∇g (H ∇g K)) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_join_join hG hH hK)

/-- The Mycielskian's diameter is bracketed by its radius: at least two and at most four. -/
theorem two_le_diameter_mycielskian (G : IsoGraph) (h : 0 < G.minDeg) :
    2 ≤ (mycielskian G).diameter := by
  have h1 := radius_le_diameter (mycielskian G)
  rw [radius_mycielskian G h] at h1
  exact h1

/-- The other half of the bracket, from `diam ≤ 2 · rad`. -/
theorem diameter_mycielskian_le_four (G : IsoGraph) (h : 0 < G.minDeg) :
    (mycielskian G).diameter ≤ 4 := by
  have h1 := diameter_le_two_mul_radius (mycielskian G)
  rw [radius_mycielskian G h] at h1
  omega

/-- In a triangle-free graph every clique of a clique cover is a vertex or an edge, so a cover
needs at least half the vertices. -/
theorem le_cliqueCoverNum_of_cliqueNum_le_two {G : IsoGraph} (hc : G.cliqueNum ≤ 2) :
    (G.V + 1) / 2 ≤ G.cliqueCoverNum := by
  have hlb := V_le_cliqueCoverNum_mul_cliqueNum G
  have h2 : G.cliqueCoverNum * G.cliqueNum ≤ G.cliqueCoverNum * 2 := Nat.mul_le_mul_left _ hc
  omega

/-- A triangle-free graph with a near-perfect matching has the smallest clique cover its vertex
count allows: the matching edges cover everything but at most one vertex, and no clique can do
better than an edge. -/
theorem cliqueCoverNum_of_cliqueNum_le_two {G : IsoGraph} (hc : G.cliqueNum ≤ 2)
    (hm : G.V ≤ 2 * G.matchNum + 1) : G.cliqueCoverNum = (G.V + 1) / 2 := by
  have hlb := le_cliqueCoverNum_of_cliqueNum_le_two hc
  have hub := cliqueCoverNum_le_V_sub_matchNum G
  have h2 := two_mul_matchNum_le_V G
  omega

/-- A triangle is a cycle, so a graph with a large clique cannot be a forest. -/
theorem not_isAcyclic_of_three_le_cliqueNum {G : IsoGraph} (h : 3 ≤ G.cliqueNum) :
    ¬ IsAcyclic G :=
  not_isAcyclic_of_girth_pos (by rw [girth_eq_three_of_cliqueNum h]; omega)

/-- A triangle-free graph that is not a forest has a shortest cycle of length at least four. -/
theorem four_le_girth_of_cliqueNum_le_two {G : IsoGraph} (hc : G.cliqueNum ≤ 2)
    (h : ¬ IsAcyclic G) : 4 ≤ G.girth := by
  have h3 := three_le_girth h
  have h4 : G.girth ≠ 3 := fun he ↦ by have := girth_eq_three_iff.1 he; omega
  omega

/-- The Mycielskian of a triangle-free graph with an edge is triangle-free and has a cycle, so
its girth is at least four. -/
theorem four_le_girth_mycielskian (G : IsoGraph) (hc : G.cliqueNum ≤ 2) (hE : 0 < G.E) :
    4 ≤ (mycielskian G).girth := by
  have hV : 0 < G.V := by have := indepNum_lt_V_of_E_pos hE; omega
  exact four_le_girth_of_cliqueNum_le_two (cliqueNum_mycielskian_eq_two hV hc).le
    (not_isAcyclic_mycielskian G hE)

/-- Two edges, one from each factor, span a four-cycle in the Cartesian product; if a factor has
a triangle the product inherits it. -/
theorem not_isAcyclic_cartesianProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsAcyclic (G □g H) := by
  have hVG : 0 < G.V := by have := indepNum_lt_V_of_E_pos hG; omega
  have hVH : 0 < H.V := by have := indepNum_lt_V_of_E_pos hH; omega
  rcases Nat.lt_or_ge G.cliqueNum 3 with h1 | h1
  · rcases Nat.lt_or_ge H.cliqueNum 3 with h2 | h2
    · exact not_isAcyclic_of_girth_pos
        (by rw [girth_cartesianProduct_of_cliqueNum_le_two hG hH (by omega) (by omega)]; omega)
    · exact not_isAcyclic_of_three_le_cliqueNum
        (by rw [cliqueNum_cartesianProduct hVG hVH]; omega)
  · exact not_isAcyclic_of_three_le_cliqueNum
      (by rw [cliqueNum_cartesianProduct hVG hVH]; omega)

/-- A triangle in each factor gives a triangle in the tensor product. -/
theorem girth_tensorProduct {G H : IsoGraph} (hG : 3 ≤ G.cliqueNum) (hH : 3 ≤ H.cliqueNum) :
    (G ⊗g H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_tensorProduct]
  omega

theorem not_isAcyclic_tensorProduct {G H : IsoGraph} (hG : 3 ≤ G.cliqueNum)
    (hH : 3 ≤ H.cliqueNum) : ¬ IsAcyclic (G ⊗g H) :=
  not_isAcyclic_of_girth_pos (by rw [girth_tensorProduct hG hH]; omega)

/-- The tensor product of two connected graphs, one of them non-bipartite, is connected. -/
theorem numComponents_tensorProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H)
    (hb : ¬ IsBipartite G) (hE : 0 < H.E) : (G ⊗g H).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_tensorProduct hG hH hb hE)

/-- The complement of a disconnected graph has diameter two, hence radius at most two. -/
theorem radius_compl_le_two {G : IsoGraph} (h : ¬ IsConnected G) (hE : 0 < G.E) :
    Gᶜ.radius ≤ 2 := by
  have h1 := radius_le_diameter Gᶜ
  rw [diameter_compl h hE] at h1
  exact h1

/-- The line graph of `Kₙ` has one vertex per edge, and it inherits vertex-transitivity from the
arc-transitivity of `Kₙ`. -/
theorem le_autCount_lineGraph_complete (n : ℕ) :
    (n + 2).choose 2 ≤ (lineGraph (complete (n + 2))).autCount := by
  have hE : (complete (n + 2)).E = (n + 2).choose 2 := E_complete (n + 2)
  have h := V_le_autCount_of_isVertexTransitive (G := lineGraph (complete (n + 2)))
    (by rw [V_lineGraph, hE]; exact Nat.choose_pos (by omega))
    ((isArcTransitive_complete (n + 2)).lineGraph)
  rwa [V_lineGraph, hE] at h

theorem le_autCount_lineGraph_cycle (n : ℕ) :
    n + 3 ≤ (lineGraph (cycle (n + 3))).autCount := by
  have hE : (cycle (n + 3)).E = n + 3 := E_cycle n
  have h := V_le_autCount_of_isVertexTransitive (G := lineGraph (cycle (n + 3)))
    (by rw [V_lineGraph, hE]; omega) (isVertexTransitive_lineGraph_cycle (n + 3))
  rwa [V_lineGraph, hE] at h

/-- The line graph of a `k`-regular graph is `(2k - 2)`-regular, so its edge chromatic number is
bracketed by the usual sandwich. -/
theorem le_edgeChromNum_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    2 * k - 2 ≤ (lineGraph G).edgeChromNum := by
  have h1 := maxDeg_le_edgeChromNum (lineGraph G)
  rwa [maxDeg_lineGraph hE h] at h1

theorem edgeChromNum_lineGraph_le {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    (lineGraph G).edgeChromNum ≤ 2 * (2 * k - 2) - 1 := by
  have h1 := edgeChromNum_le_two_mul_maxDeg_sub_one (lineGraph G)
  rwa [maxDeg_lineGraph hE h] at h1

/-! ### Graphs that are not self-complementary, by bipartiteness

A self-complementary graph on five or more vertices needs at least three colours, so it is never
bipartite.  That refutes self-complementarity for every bipartite family in the library once it
is large enough — the exceptions `path 4` and `empty 1` below the threshold are exactly the two
small self-complementary bipartite graphs.
-/

theorem not_isSelfComplementary_of_isBipartite {G : IsoGraph} (hb : IsBipartite G)
    (hV : 5 ≤ G.V) : ¬ IsSelfComplementary G :=
  fun h ↦ h.not_isBipartite hV hb

@[simp] theorem not_isSelfComplementary_path (n : ℕ) :
    ¬ IsSelfComplementary (path (n + 5)) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_path _) (by rw [V_path]; omega)

theorem not_isSelfComplementary_cycle_even (m : ℕ) :
    ¬ IsSelfComplementary (cycle (2 * (m + 3))) :=
  not_isSelfComplementary_of_isBipartite (isBipartite_cycle_even _) (by rw [V_cycle]; omega)

/-! ### More graphs that are not self-complementary

Beyond bipartiteness there are three cheap obstructions: the vertex count must be `0` or `1`
mod `4`, the clique and independence numbers must agree, and the graph must be connected.  Each
one is a one-line consequence of a lemma already in the file, and between them they refute
self-complementarity for almost every remaining family.
-/

theorem not_isSelfComplementary_of_V_mod_four {G : IsoGraph} (h : G.V % 4 = 2 ∨ G.V % 4 = 3) :
    ¬ IsSelfComplementary G := by
  intro hs
  rcases hs.V_mod_four with h' | h' <;> omega

theorem not_isSelfComplementary_of_cliqueNum_ne_indepNum {G : IsoGraph}
    (h : G.cliqueNum ≠ G.indepNum) : ¬ IsSelfComplementary G :=
  fun hs ↦ h hs.cliqueNum_eq_indepNum

theorem not_isSelfComplementary_of_not_isConnected {G : IsoGraph} (hV : 2 ≤ G.V)
    (h : ¬ IsConnected G) : ¬ IsSelfComplementary G :=
  fun hs ↦ h (hs.isConnected hV)

theorem not_isSelfComplementary_of_two_mul_E_ne {G : IsoGraph} (h : 2 * G.E ≠ G.V.choose 2) :
    ¬ IsSelfComplementary G :=
  fun hs ↦ h hs.two_mul_E

theorem not_isSelfComplementary_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ IsSelfComplementary (G ⊕g H) :=
  not_isSelfComplementary_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

theorem not_isSelfComplementary_cycle_three_mod_four (m : ℕ) :
    ¬ IsSelfComplementary (cycle (4 * m + 3)) :=
  not_isSelfComplementary_of_V_mod_four (by rw [V_cycle]; omega)

/-- The Mycielskian of a triangle-free graph on at least three vertices has clique number two
but independence number at least three. -/
theorem not_isSelfComplementary_mycielskian {G : IsoGraph} (hV : 3 ≤ G.V)
    (h : G.cliqueNum ≤ 2) : ¬ IsSelfComplementary (mycielskian G) :=
  not_isSelfComplementary_of_cliqueNum_ne_indepNum (by
    have h1 := V_le_indepNum_mycielskian G
    rw [cliqueNum_mycielskian_eq_two (by omega) h]
    omega)

/-! ### Complements of the named families

Cliques and independent sets swap under complementation, as do the chromatic number and the
clique cover number, and the automorphism group is unchanged.  Together with the degree and edge
identities that gives a complement column for every family whose four counting invariants are
known, even when the complement itself has no name.
-/

theorem chromNum_compl_cycle (n : ℕ) : ((cycle (n + 4))ᶜ).chromNum = (n + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_cycle]

theorem maxDeg_compl_cycle (n : ℕ) : maxDeg ((cycle (n + 3))ᶜ) = n := by
  have h := maxDeg_compl (G := cycle (n + 3)) (by rw [V_cycle]; omega)
  rw [V_cycle, minDeg_cycle] at h
  omega

theorem minDeg_compl_cycle (n : ℕ) : minDeg ((cycle (n + 3))ᶜ) = n := by
  have h := minDeg_compl (G := cycle (n + 3)) (by rw [V_cycle]; omega)
  rw [V_cycle, maxDeg_cycle] at h
  omega

theorem E_compl_cycle (n : ℕ) : ((cycle (n + 3))ᶜ).E = (n + 3).choose 2 - (n + 3) := by
  have h := E_compl (cycle (n + 3))
  rw [E_cycle, V_cycle] at h
  omega

theorem maxDeg_compl_path (n : ℕ) : maxDeg ((path (n + 3))ᶜ) = n + 1 := by
  have h := maxDeg_compl (G := path (n + 3)) (by rw [V_path]; omega)
  have h2 : minDeg (path (n + 3)) = 1 := by
    rw [show n + 3 = n + 1 + 2 from by ring, minDeg_path]
  rw [V_path, h2] at h
  omega

theorem minDeg_compl_path (n : ℕ) : minDeg ((path (n + 3))ᶜ) = n := by
  have h := minDeg_compl (G := path (n + 3)) (by rw [V_path]; omega)
  rw [V_path, maxDeg_path] at h
  omega

theorem E_compl_path (n : ℕ) : ((path (n + 1))ᶜ).E = (n + 1).choose 2 - n := by
  have h := E_compl (path (n + 1))
  rw [E_path, V_path] at h
  omega

/-! ### Complements of the Mycielskian, the Grötzsch graph and the odd folded cubes -/

theorem indepNum_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    ((mycielskian G)ᶜ).indepNum = max G.cliqueNum 2 := by
  rw [indepNum_compl, cliqueNum_mycielskian G hV]

theorem chromNum_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) (hc : G.cliqueNum ≤ 2)
    (hm : 2 * G.matchNum = G.V) : ((mycielskian G)ᶜ).chromNum = G.V + 1 := by
  rw [chromNum_compl, cliqueCoverNum_mycielskian G hV hc hm]

theorem cliqueNum_compl_mycielskian_le (G : IsoGraph) (hV : 0 < G.V) :
    ((mycielskian G)ᶜ).cliqueNum ≤ G.V + G.indepNum := by
  rw [cliqueNum_compl]
  exact indepNum_mycielskian_le G hV

theorem maxDeg_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    maxDeg ((mycielskian G)ᶜ) = 2 * G.V - min (min (2 * G.minDeg) (G.minDeg + 1)) G.V := by
  have h := maxDeg_compl (G := mycielskian G) (by rw [V_mycielskian]; omega)
  rw [V_mycielskian, minDeg_mycielskian G hV] at h
  omega

theorem minDeg_compl_mycielskian (G : IsoGraph) :
    minDeg ((mycielskian G)ᶜ) = 2 * G.V - max (2 * maxDeg G) G.V := by
  have h := minDeg_compl (G := mycielskian G) (by rw [V_mycielskian]; omega)
  rw [V_mycielskian, maxDeg_mycielskian G] at h
  omega

theorem E_compl_mycielskian (G : IsoGraph) :
    ((mycielskian G)ᶜ).E = (2 * G.V + 1).choose 2 - (3 * G.E + G.V) := by
  have h := E_compl (mycielskian G)
  rw [E_mycielskian, V_mycielskian] at h
  omega

/-! ### Complements of line graphs -/

theorem maxDeg_compl_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    maxDeg ((lineGraph G)ᶜ) = G.E - 1 - (2 * k - 2) := by
  have hd := maxDeg_compl (G := lineGraph G) (by rwa [V_lineGraph])
  rw [V_lineGraph, minDeg_lineGraph hE h] at hd
  omega

theorem minDeg_compl_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) :
    minDeg ((lineGraph G)ᶜ) = G.E - 1 - (2 * k - 2) := by
  have hd := minDeg_compl (G := lineGraph G) (by rwa [V_lineGraph])
  rw [V_lineGraph, maxDeg_lineGraph hE h] at hd
  omega

theorem E_compl_lineGraph (G : IsoGraph) :
    ((lineGraph G)ᶜ).E = G.E.choose 2 - ((degSequence G).map fun d ↦ d.choose 2).sum := by
  have hd := E_compl (lineGraph G)
  rw [E_lineGraph, V_lineGraph] at hd
  omega

@[simp] theorem isVertexTransitive_cartesianProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m □g cycle n) :=
  (isVertexTransitive_cycle m).cartesianProduct (isVertexTransitive_cycle n)

/-! ### The chromatic index of a grid, a cylinder and a torus -/

/-- **`χ'(G □ H) ≤ χ'(G) + χ'(H)`.**  An edge of a product moves exactly one coordinate, so the
two factors' edge colourings can be laid side by side.  Each factor needs an edge, since a
colouring with no colours has nowhere to send the values it is never asked for. -/
@[toIsoGraph]
theorem _root_.CGraph.edgeChromNum_cartesianProduct_le {G H : CGraph} (hG : 0 < G.E)
    (hH : 0 < H.E) :
    (G □g H).edgeChromNum ≤ G.edgeChromNum + H.edgeChromNum :=
  CGraph.chromNum_lineGraph_cartesianProduct_le_add (CGraph.edgeChromNum_pos hG)
    (CGraph.edgeChromNum_pos hH)

/-- **The chromatic index of a cylinder over an even cycle is four.** -/
theorem edgeChromNum_cartesianProduct_cycle_even_path (m n : ℕ) :
    (cycle (2 * m + 4) □g path (n + 3)).edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := path (n + 3))
      (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega)
      (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
    rwa [edgeChromNum_cycle_even, edgeChromNum_path] at h
  · have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g path (n + 3))
    rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, maxDeg_cartesianProduct_cycle_path] at h

/-- **The chromatic index of a torus with both sides even is four.** -/
theorem edgeChromNum_cartesianProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) □g cycle (2 * n + 4)).edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := cycle (2 * n + 4))
      (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega)
      (by rw [show 2 * n + 4 = (2 * n + 1) + 3 by omega, E_cycle]; omega)
    rwa [edgeChromNum_cycle_even, edgeChromNum_cycle_even] at h
  · have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g cycle (2 * n + 4))
    rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, show 2 * n + 4 = (2 * n + 1) + 3 by omega,
      maxDeg_cartesianProduct_cycle] at h

/-! An odd cycle costs a third colour, so the composition only brackets the remaining cases.  A
cylinder or a torus with an odd side is still `4`-regular where it is regular at all, and Vizing's
theorem — which is not in the library — would pin every case with an even side down to `4`. -/

/-- A cylinder over an odd cycle needs at least four colours and at most five. -/
theorem le_edgeChromNum_cartesianProduct_cycle_odd_path (m n : ℕ) :
    4 ≤ (cycle (2 * m + 3) □g path (n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (cycle (2 * m + 3) □g path (n + 3))
  rwa [maxDeg_cartesianProduct_cycle_path] at h

theorem edgeChromNum_cartesianProduct_cycle_odd_path_le (m n : ℕ) :
    (cycle (2 * m + 3) □g path (n + 3)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 3)) (H := path (n + 3))
    (by rw [E_cycle]; omega) (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
  rwa [edgeChromNum_cycle_odd, edgeChromNum_path] at h

/-- A torus with one even side and one odd side needs at least four colours and at most five. -/
theorem le_edgeChromNum_cartesianProduct_cycle_even_odd (m n : ℕ) :
    4 ≤ (cycle (2 * m + 4) □g cycle (2 * n + 3)).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (cycle (2 * m + 4) □g cycle (2 * n + 3))
  rwa [show 2 * m + 4 = (2 * m + 1) + 3 by omega, maxDeg_cartesianProduct_cycle] at h

theorem edgeChromNum_cartesianProduct_cycle_even_odd_le (m n : ℕ) :
    (cycle (2 * m + 4) □g cycle (2 * n + 3)).edgeChromNum ≤ 5 := by
  have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 4)) (H := cycle (2 * n + 3))
    (by rw [show 2 * m + 4 = (2 * m + 1) + 3 by omega, E_cycle]; omega)
    (by rw [E_cycle]; omega)
  rwa [edgeChromNum_cycle_even, edgeChromNum_cycle_odd] at h

/-- **A torus with two odd sides needs a fifth colour**: it is `4`-regular on an odd number of
vertices, so no colour class can be a perfect matching. -/
theorem le_edgeChromNum_cartesianProduct_cycle_odd (m n : ℕ) :
    5 ≤ (cycle (2 * m + 3) □g cycle (2 * n + 3)).edgeChromNum := by
  have hreg : (cycle (2 * m + 3) □g cycle (2 * n + 3)).IsRegularWith 4 :=
    (isRegularWith_cycle (2 * m)).cartesianProduct (isRegularWith_cycle (2 * n))
  have hodd : (cycle (2 * m + 3) □g cycle (2 * n + 3)).V % 2 = 1 := by
    have h1 : (2 * m + 3) % 2 = 1 := by omega
    have h2 : (2 * n + 3) % 2 = 1 := by omega
    rw [V_cartesianProduct, V_cycle, V_cycle, Nat.mul_mod, h1, h2]
  have h := maxDeg_lt_edgeChromNum_of_isRegularWith_odd hreg (by omega) hodd
  rwa [maxDeg_cartesianProduct_cycle] at h

theorem edgeChromNum_cartesianProduct_cycle_odd_le (m n : ℕ) :
    (cycle (2 * m + 3) □g cycle (2 * n + 3)).edgeChromNum ≤ 6 := by
  have h := edgeChromNum_cartesianProduct_le (G := cycle (2 * m + 3)) (H := cycle (2 * n + 3))
    (by rw [E_cycle]; omega) (by rw [E_cycle]; omega)
  rwa [edgeChromNum_cycle_odd, edgeChromNum_cycle_odd] at h

@[simp] theorem isVertexTransitive_tensorProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m ⊗g cycle n) :=
  (isVertexTransitive_cycle m).tensorProduct (isVertexTransitive_cycle n)

@[simp] theorem isVertexTransitive_strongProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m ⊠g cycle n) :=
  (isVertexTransitive_cycle m).strongProduct (isVertexTransitive_cycle n)

@[simp] theorem isVertexTransitive_lexProduct_cycle (m n : ℕ) :
    IsVertexTransitive (cycle m ·g cycle n) :=
  (isVertexTransitive_cycle m).lexProduct (isVertexTransitive_cycle n)

@[simp] theorem girth_tensorProduct_complete (m n : ℕ) :
    (complete (m + 3) ⊗g complete (n + 3)).girth = 3 :=
  girth_tensorProduct (by rw [cliqueNum_complete]; omega) (by rw [cliqueNum_complete]; omega)

theorem isConnected_tensorProduct_complete (m n : ℕ) :
    IsConnected (complete (m + 3) ⊗g complete (n + 2)) :=
  isConnected_tensorProduct (isConnected_complete (m + 2)) (isConnected_complete (n + 1))
    (not_isBipartite_complete m) (E_complete_pos n)

theorem numComponents_tensorProduct_complete (m n : ℕ) :
    (complete (m + 3) ⊗g complete (n + 2)).numComponents = 1 :=
  numComponents_tensorProduct (isConnected_complete (m + 2)) (isConnected_complete (n + 1))
    (not_isBipartite_complete m) (E_complete_pos n)

@[simp] theorem isVertexTransitive_tensorProduct_complete (m n : ℕ) :
    IsVertexTransitive (complete m ⊗g complete n) :=
  (isVertexTransitive_complete m).tensorProduct (isVertexTransitive_complete n)

theorem not_isConnected_disjUnion_cycle (m n : ℕ) :
    ¬ IsConnected (cycle (m + 1) ⊕g cycle (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)

theorem not_isConnected_disjUnion_path (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g path (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_path]; omega)

@[simp] theorem girth_disjUnion_complete (m n : ℕ) :
    (complete (m + 3) ⊕g complete (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_disjUnion, cliqueNum_complete, cliqueNum_complete]; omega)

theorem not_isConnected_disjUnion_complete (m n : ℕ) :
    ¬ IsConnected (complete (m + 1) ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_complete]; omega) (by rw [V_complete]; omega)

theorem E_compl_cartesianProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) □g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2 - 2 * ((m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) □g cycle (n + 3))
  rw [E_cartesianProduct_cycle, V_cartesianProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_cartesianProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) □g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := maxDeg_compl (G := cycle (m + 3) □g cycle (n + 3))
    (by rw [V_cartesianProduct, V_cycle, V_cycle]; positivity)
  rw [V_cartesianProduct, V_cycle, V_cycle, minDeg_cartesianProduct_cycle] at h
  omega

theorem minDeg_compl_cartesianProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) □g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := cycle (m + 3) □g cycle (n + 3))
    (by rw [V_cartesianProduct, V_cycle, V_cycle]; positivity)
  rw [V_cartesianProduct, V_cycle, V_cycle, maxDeg_cartesianProduct_cycle] at h
  omega

theorem E_compl_cartesianProduct_cycle_path (m n : ℕ) :
    ((cycle (m + 3) □g path (n + 1))ᶜ).E
      = ((m + 3) * (n + 1)).choose 2 - ((m + 3) * n + (n + 1) * (m + 3)) := by
  have h := E_compl (cycle (m + 3) □g path (n + 1))
  rw [E_cartesianProduct, E_cycle, E_path, V_cycle, V_path, V_cartesianProduct, V_cycle,
      V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_cartesianProduct_cycle_path (m n : ℕ) :
    maxDeg ((cycle (m + 3) □g path (n + 2))ᶜ) = (m + 3) * (n + 2) - 4 := by
  have h := maxDeg_compl (G := cycle (m + 3) □g path (n + 2))
    (by rw [V_cartesianProduct, V_cycle, V_path]; positivity)
  rw [V_cartesianProduct, V_cycle, V_path, minDeg_cartesianProduct_cycle_path] at h
  omega

theorem minDeg_compl_cartesianProduct_cycle_path (m n : ℕ) :
    minDeg ((cycle (m + 3) □g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := cycle (m + 3) □g path (n + 3))
    (by rw [V_cartesianProduct, V_cycle, V_path]; positivity)
  rw [V_cartesianProduct, V_cycle, V_path, maxDeg_cartesianProduct_cycle_path] at h
  omega

/-! ### Complements of the tensor, strong and lexicographic products of two cycles -/

theorem E_compl_tensorProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊗g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2 - 2 * (m + 3) * (n + 3) := by
  have h := E_compl (cycle (m + 3) ⊗g cycle (n + 3))
  rw [E_tensorProduct, E_cycle, E_cycle, V_tensorProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_tensorProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ⊗g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := maxDeg_compl (G := cycle (m + 3) ⊗g cycle (n + 3))
    (by rw [V_tensorProduct, V_cycle, V_cycle]; positivity)
  rw [V_tensorProduct, V_cycle, V_cycle, minDeg_tensorProduct_cycle] at h
  omega

theorem minDeg_compl_tensorProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ⊗g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := cycle (m + 3) ⊗g cycle (n + 3))
    (by rw [V_tensorProduct, V_cycle, V_cycle]; positivity)
  rw [V_tensorProduct, V_cycle, V_cycle, maxDeg_tensorProduct_cycle] at h
  omega

theorem E_compl_strongProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊠g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2
          - ((m + 3) * (n + 3) + (n + 3) * (m + 3) + 2 * (m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) ⊠g cycle (n + 3))
  rw [E_strongProduct, E_cycle, E_cycle, V_cycle, V_cycle, V_strongProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_strongProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ⊠g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 9 := by
  have h := maxDeg_compl (G := cycle (m + 3) ⊠g cycle (n + 3))
    (by rw [V_strongProduct, V_cycle, V_cycle]; positivity)
  rw [V_strongProduct, V_cycle, V_cycle, minDeg_strongProduct_cycle] at h
  omega

theorem minDeg_compl_strongProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ⊠g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 9 := by
  have h := minDeg_compl (G := cycle (m + 3) ⊠g cycle (n + 3))
    (by rw [V_strongProduct, V_cycle, V_cycle]; positivity)
  rw [V_strongProduct, V_cycle, V_cycle, maxDeg_strongProduct_cycle] at h
  omega

theorem E_compl_lexProduct_cycle (m n : ℕ) :
    ((cycle (m + 3) ·g cycle (n + 3))ᶜ).E
      = ((m + 3) * (n + 3)).choose 2 - ((n + 3) * (n + 3) * (m + 3) + (m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) ·g cycle (n + 3))
  rw [E_lexProduct, E_cycle, E_cycle, V_cycle, V_cycle, V_lexProduct, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_lexProduct_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ·g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 2 * (n + 3) - 3 := by
  have h := maxDeg_compl (G := cycle (m + 3) ·g cycle (n + 3))
    (by rw [V_lexProduct, V_cycle, V_cycle]; positivity)
  rw [V_lexProduct, V_cycle, V_cycle, minDeg_lexProduct_cycle] at h
  omega

theorem minDeg_compl_lexProduct_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ·g cycle (n + 3))ᶜ) = (m + 3) * (n + 3) - 2 * (n + 3) - 3 := by
  have h := minDeg_compl (G := cycle (m + 3) ·g cycle (n + 3))
    (by rw [V_lexProduct, V_cycle, V_cycle]; positivity)
  rw [V_lexProduct, V_cycle, V_cycle, maxDeg_lexProduct_cycle] at h
  omega

/-! ### Complements of the products of two paths and of the tensor product of complete graphs -/

theorem E_compl_tensorProduct_path (m n : ℕ) :
    ((path (m + 1) ⊗g path (n + 1))ᶜ).E = ((m + 1) * (n + 1)).choose 2 - 2 * m * n := by
  have h := E_compl (path (m + 1) ⊗g path (n + 1))
  rw [E_tensorProduct, E_path, E_path, V_tensorProduct, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_tensorProduct_path (m n : ℕ) :
    maxDeg ((path (m + 2) ⊗g path (n + 2))ᶜ) = (m + 2) * (n + 2) - 2 := by
  have h := maxDeg_compl (G := path (m + 2) ⊗g path (n + 2))
    (by rw [V_tensorProduct, V_path, V_path]; positivity)
  rw [V_tensorProduct, V_path, V_path, minDeg_tensorProduct_path] at h
  omega

theorem minDeg_compl_tensorProduct_path (m n : ℕ) :
    minDeg ((path (m + 3) ⊗g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 5 := by
  have h := minDeg_compl (G := path (m + 3) ⊗g path (n + 3))
    (by rw [V_tensorProduct, V_path, V_path]; positivity)
  rw [V_tensorProduct, V_path, V_path, maxDeg_tensorProduct_path] at h
  omega

theorem E_compl_lexProduct_path (m n : ℕ) :
    ((path (m + 1) ·g path (n + 1))ᶜ).E
      = ((m + 1) * (n + 1)).choose 2 - ((n + 1) * (n + 1) * m + (m + 1) * n) := by
  have h := E_compl (path (m + 1) ·g path (n + 1))
  rw [E_lexProduct, E_path, E_path, V_path, V_path, V_lexProduct, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_lexProduct_path (m n : ℕ) :
    maxDeg ((path (m + 2) ·g path (n + 2))ᶜ) = (m + 2) * (n + 2) - n - 4 := by
  have h := maxDeg_compl (G := path (m + 2) ·g path (n + 2))
    (by rw [V_lexProduct, V_path, V_path]; positivity)
  rw [V_lexProduct, V_path, V_path, minDeg_lexProduct_path] at h
  omega

theorem minDeg_compl_lexProduct_path (m n : ℕ) :
    minDeg ((path (m + 3) ·g path (n + 3))ᶜ) = (m + 3) * (n + 3) - 2 * n - 9 := by
  have h := minDeg_compl (G := path (m + 3) ·g path (n + 3))
    (by rw [V_lexProduct, V_path, V_path]; positivity)
  rw [V_lexProduct, V_path, V_path, maxDeg_lexProduct_path] at h
  omega

theorem E_compl_tensorProduct_complete (m n : ℕ) :
    ((complete m ⊗g complete n)ᶜ).E = (m * n).choose 2 - 2 * m.choose 2 * n.choose 2 := by
  have h := E_compl (complete m ⊗g complete n)
  rw [E_tensorProduct, E_complete, E_complete, V_tensorProduct, V_complete, V_complete] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_tensorProduct_complete (m n : ℕ) :
    maxDeg ((complete (m + 1) ⊗g complete (n + 1))ᶜ) = (m + 1) * (n + 1) - 1 - m * n := by
  have h := maxDeg_compl (G := complete (m + 1) ⊗g complete (n + 1))
    (by rw [V_tensorProduct, V_complete, V_complete]; positivity)
  rw [V_tensorProduct, V_complete, V_complete, minDeg_tensorProduct_complete] at h
  omega

theorem minDeg_compl_tensorProduct_complete (m n : ℕ) :
    minDeg ((complete (m + 1) ⊗g complete (n + 1))ᶜ) = (m + 1) * (n + 1) - 1 - m * n := by
  have h := minDeg_compl (G := complete (m + 1) ⊗g complete (n + 1))
    (by rw [V_tensorProduct, V_complete, V_complete]; positivity)
  rw [V_tensorProduct, V_complete, V_complete, maxDeg_tensorProduct_complete] at h
  omega

/-! ### Complements of disjoint unions and joins of two named families -/

theorem E_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ).E = ((m + 3) + (n + 3)).choose 2 - ((m + 3) + (n + 3)) := by
  have h := E_compl (cycle (m + 3) ⊕g cycle (n + 3))
  rw [E_disjUnion, E_cycle, E_cycle, V_disjUnion, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_disjUnion_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ) = m + n + 3 := by
  have h := maxDeg_compl (G := cycle (m + 3) ⊕g cycle (n + 3))
    (by rw [V_disjUnion, V_cycle, V_cycle]; omega)
  rw [V_disjUnion, V_cycle, V_cycle, minDeg_disjUnion_cycle] at h
  omega

theorem minDeg_compl_disjUnion_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ) = m + n + 3 := by
  have h := minDeg_compl (G := cycle (m + 3) ⊕g cycle (n + 3))
    (by rw [V_disjUnion, V_cycle, V_cycle]; omega)
  rw [V_disjUnion, V_cycle, V_cycle, maxDeg_disjUnion, maxDeg_cycle, maxDeg_cycle, max_self] at h
  omega

theorem E_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 1) ⊕g path (n + 1))ᶜ).E = ((m + 1) + (n + 1)).choose 2 - (m + n) := by
  have h := E_compl (path (m + 1) ⊕g path (n + 1))
  rw [E_disjUnion, E_path, E_path, V_disjUnion, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_disjUnion_path (m n : ℕ) :
    maxDeg ((path (m + 2) ⊕g path (n + 2))ᶜ) = m + n + 2 := by
  have h := maxDeg_compl (G := path (m + 2) ⊕g path (n + 2))
    (by rw [V_disjUnion, V_path, V_path]; omega)
  rw [V_disjUnion, V_path, V_path, minDeg_disjUnion_path] at h
  omega

theorem minDeg_compl_disjUnion_path (m n : ℕ) :
    minDeg ((path (m + 3) ⊕g path (n + 3))ᶜ) = m + n + 3 := by
  have h := minDeg_compl (G := path (m + 3) ⊕g path (n + 3))
    (by rw [V_disjUnion, V_path, V_path]; omega)
  rw [V_disjUnion, V_path, V_path, maxDeg_disjUnion, maxDeg_path, maxDeg_path, max_self] at h
  omega

theorem E_compl_disjUnion_complete (m n : ℕ) :
    ((complete m ⊕g complete n)ᶜ).E = (m + n).choose 2 - (m.choose 2 + n.choose 2) := by
  have h := E_compl (complete m ⊕g complete n)
  rw [E_disjUnion, E_complete, E_complete, V_disjUnion, V_complete, V_complete] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_disjUnion_complete (m n : ℕ) :
    maxDeg ((complete (m + 1) ⊕g complete (n + 1))ᶜ) = m + n + 1 - min m n := by
  have h := maxDeg_compl (G := complete (m + 1) ⊕g complete (n + 1))
    (by rw [V_disjUnion, V_complete, V_complete]; omega)
  rw [V_disjUnion, V_complete, V_complete, minDeg_disjUnion_complete] at h
  omega

theorem minDeg_compl_disjUnion_complete (m n : ℕ) :
    minDeg ((complete (m + 1) ⊕g complete (n + 1))ᶜ) = m + n + 1 - max m n := by
  have h := minDeg_compl (G := complete (m + 1) ⊕g complete (n + 1))
    (by rw [V_disjUnion, V_complete, V_complete]; omega)
  rw [V_disjUnion, V_complete, V_complete, maxDeg_disjUnion, maxDeg_complete, maxDeg_complete] at h
  omega

theorem E_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 3) ∇g cycle (n + 3))ᶜ).E
      = ((m + 3) + (n + 3)).choose 2 - ((m + 3) + (n + 3) + (m + 3) * (n + 3)) := by
  have h := E_compl (cycle (m + 3) ∇g cycle (n + 3))
  rw [E_join, E_cycle, E_cycle, V_cycle, V_cycle, V_join, V_cycle, V_cycle] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_join_cycle (m n : ℕ) :
    maxDeg ((cycle (m + 3) ∇g cycle (n + 3))ᶜ) = max m n := by
  have h := maxDeg_compl (G := cycle (m + 3) ∇g cycle (n + 3))
    (by rw [V_join, V_cycle, V_cycle]; omega)
  rw [V_join, V_cycle, V_cycle, minDeg_join_cycle] at h
  omega

theorem minDeg_compl_join_cycle (m n : ℕ) :
    minDeg ((cycle (m + 3) ∇g cycle (n + 3))ᶜ) = min m n := by
  have h := minDeg_compl (G := cycle (m + 3) ∇g cycle (n + 3))
    (by rw [V_join, V_cycle, V_cycle]; omega)
  rw [V_join, V_cycle, V_cycle, maxDeg_join_cycle] at h
  omega

theorem E_compl_join_path (m n : ℕ) :
    ((path (m + 1) ∇g path (n + 1))ᶜ).E
      = ((m + 1) + (n + 1)).choose 2 - (m + n + (m + 1) * (n + 1)) := by
  have h := E_compl (path (m + 1) ∇g path (n + 1))
  rw [E_join, E_path, E_path, V_path, V_path, V_join, V_path, V_path] at h
  rw [← h, Nat.add_sub_cancel]

theorem maxDeg_compl_join_path (m n : ℕ) :
    maxDeg ((path (m + 2) ∇g path (n + 2))ᶜ) = max m n := by
  have h := maxDeg_compl (G := path (m + 2) ∇g path (n + 2)) (by rw [V_join, V_path, V_path]; omega)
  rw [V_join, V_path, V_path, minDeg_join_path] at h
  omega

theorem minDeg_compl_join_path (m n : ℕ) :
    minDeg ((path (m + 3) ∇g path (n + 3))ᶜ) = min m n := by
  have h := minDeg_compl (G := path (m + 3) ∇g path (n + 3)) (by rw [V_join, V_path, V_path]; omega)
  rw [V_join, V_path, V_path, maxDeg_join_path] at h
  omega

theorem chromNum_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 4) ∇g cycle (n + 4))ᶜ).chromNum = max ((m + 5) / 2) ((n + 5) / 2) := by
  rw [chromNum_compl, cliqueCoverNum_join, cliqueCoverNum_cycle, cliqueCoverNum_cycle]

theorem chromNum_compl_join_path (m n : ℕ) :
    ((path m ∇g path n)ᶜ).chromNum = max ((m + 1) / 2) ((n + 1) / 2) := by
  rw [chromNum_compl, cliqueCoverNum_join, cliqueCoverNum_path, cliqueCoverNum_path]

theorem chromNum_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊕g cycle (n + 4))ᶜ).chromNum = (m + 5) / 2 + (n + 5) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_disjUnion, cliqueCoverNum_cycle, cliqueCoverNum_cycle]

theorem chromNum_compl_disjUnion_path (m n : ℕ) :
    ((path m ⊕g path n)ᶜ).chromNum = (m + 1) / 2 + (n + 1) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_disjUnion, cliqueCoverNum_path, cliqueCoverNum_path]

theorem E_compl_lexProduct_complete (m n : ℕ) :
    ((complete m ·g complete n)ᶜ).E
      = (m * n).choose 2 - (n * n * m.choose 2 + m * n.choose 2) := by
  have h := E_compl (complete m ·g complete n)
  rw [E_lexProduct_complete, V_lexProduct, V_complete, V_complete] at h
  rw [← h, Nat.add_sub_cancel]

theorem E_compl_strongProduct_complete (m n : ℕ) :
    ((complete m ⊠g complete n)ᶜ).E
      = (m * n).choose 2 - (m * n.choose 2 + n * m.choose 2 + 2 * m.choose 2 * n.choose 2) := by
  have h := E_compl (complete m ⊠g complete n)
  rw [E_strongProduct_complete, V_strongProduct, V_complete, V_complete] at h
  rw [← h, Nat.add_sub_cancel]

theorem girth_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊕g cycle (n + 4))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_disjUnion, indepNum_cycle, indepNum_cycle]; omega)

theorem girth_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 4) ⊕g path (n + 4))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_disjUnion, indepNum_path, indepNum_path]; omega)

theorem girth_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 6) ∇g cycle (n + 3))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_join, indepNum_cycle, indepNum_cycle]; omega)

theorem girth_compl_join_path (m n : ℕ) :
    ((path (m + 5) ∇g path n)ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum
    (by rw [cliqueNum_compl, indepNum_join, indepNum_path, indepNum_path]; omega)

theorem girth_compl_lineGraph (G : IsoGraph) (h : 3 ≤ G.matchNum) :
    ((lineGraph G)ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_lineGraph]; omega)

theorem diameter_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 3) ⊕g cycle (n + 3))ᶜ).diameter = 2 :=
  diameter_compl_disjUnion (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
    (by rw [E_cycle, E_cycle]; omega)

theorem diameter_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 2) ⊕g path (n + 2))ᶜ).diameter = 2 :=
  diameter_compl_disjUnion (by rw [V_path]; omega) (by rw [V_path]; omega)
    (by rw [E_path, E_path]; omega)

theorem diameter_compl_disjUnion_complete (m n : ℕ) :
    ((complete (m + 2) ⊕g complete (n + 2))ᶜ).diameter = 2 := by
  refine diameter_compl_disjUnion (by rw [V_complete]; omega) (by rw [V_complete]; omega) ?_
  rw [E_complete, E_complete]
  have := Nat.choose_pos (show 2 ≤ m + 2 by omega)
  omega

theorem diameter_strongProduct_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 2)).diameter = 1 := by
  rw [diameter_strongProduct (isConnected_complete (m + 1)) (isConnected_complete (n + 1)),
    diameter_complete, diameter_complete, max_self]

theorem radius_strongProduct_complete (m n : ℕ) :
    (complete (m + 2) ⊠g complete (n + 2)).radius = 1 := by
  rw [radius_strongProduct (isConnected_complete (m + 1)) (isConnected_complete (n + 1)),
    radius_complete, radius_complete, max_self]

theorem numComponents_strongProduct_complete (m n : ℕ) :
    (complete (m + 1) ⊠g complete (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_strongProduct_complete m n)

theorem numComponents_lexProduct_complete (m n : ℕ) :
    (complete (m + 1) ·g complete (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_lexProduct_complete m n)

theorem chromNum_tensorProduct_complete_path (m n : ℕ) :
    (complete m ⊗g path (n + 2)).chromNum = min m 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_path n)
  rwa [cliqueNum_complete, cliqueNum_path] at h

theorem chromNum_tensorProduct_complete_cycle_even (m n : ℕ) :
    (complete m ⊗g cycle (2 * n + 4)).chromNum = min m 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_cycle_even n)
  rwa [cliqueNum_complete, cliqueNum_cycle] at h

theorem chromNum_strongProduct_complete_path (m n : ℕ) :
    (complete m ⊠g path (n + 2)).chromNum = m * 2 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_path n)
  rwa [cliqueNum_complete, cliqueNum_path] at h

theorem chromNum_lexProduct_complete_path (m n : ℕ) :
    (complete m ·g path (n + 2)).chromNum = m * 2 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_path n)
  rwa [cliqueNum_complete, cliqueNum_path] at h

theorem chromNum_strongProduct_complete_cycle_even (m n : ℕ) :
    (complete m ⊠g cycle (2 * n + 4)).chromNum = m * 2 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_cycle_even n)
  rwa [cliqueNum_complete, cliqueNum_cycle] at h

theorem chromNum_strongProduct_path_cycle_even (m n : ℕ) :
    (path (m + 2) ⊠g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_path m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_path, cliqueNum_cycle] at h
  omega

theorem chromNum_lexProduct_path_cycle_even (m n : ℕ) :
    (path (m + 2) ·g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_path m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_path, cliqueNum_cycle] at h
  omega

/-- The clique cover dual: independent sets multiply in a lexicographic product and clique covers
multiply at worst, so factors with `κ = α` force equality. -/
theorem cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum {G H : IsoGraph}
    (hG : G.cliqueCoverNum = G.indepNum) (hH : H.cliqueCoverNum = H.indepNum) :
    (G ·g H).cliqueCoverNum = G.indepNum * H.indepNum := by
  have h1 := cliqueCoverNum_lexProduct_le G H
  have h2 := indepNum_le_cliqueCoverNum (G ·g H)
  rw [indepNum_lexProduct] at h2
  rw [hG, hH] at h1
  omega

theorem cliqueCoverNum_eq_indepNum_path (n : ℕ) :
    (path n).cliqueCoverNum = (path n).indepNum := by
  rw [cliqueCoverNum_path, indepNum_path]

theorem cliqueCoverNum_eq_indepNum_complete (n : ℕ) :
    (complete (n + 1)).cliqueCoverNum = (complete (n + 1)).indepNum := by
  rw [cliqueCoverNum_complete, indepNum_complete]
  omega

theorem cliqueCoverNum_eq_indepNum_cycle_even (m : ℕ) :
    (cycle (2 * m + 4)).cliqueCoverNum = (cycle (2 * m + 4)).indepNum := by
  rw [cliqueCoverNum_cycle, indepNum_cycle]
  omega

theorem cliqueCoverNum_lexProduct_path (m n : ℕ) :
    (path m ·g path n).cliqueCoverNum = (m + 1) / 2 * ((n + 1) / 2) := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_path m) (cliqueCoverNum_eq_indepNum_path n)
  rwa [indepNum_path, indepNum_path] at h

theorem cliqueCoverNum_lexProduct_complete (m n : ℕ) :
    (complete (m + 1) ·g complete (n + 1)).cliqueCoverNum = 1 := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_complete m) (cliqueCoverNum_eq_indepNum_complete n)
  rw [indepNum_complete, indepNum_complete, Nat.min_eq_right (by omega : 1 ≤ m + 1),
    Nat.min_eq_right (by omega : 1 ≤ n + 1)] at h
  simpa using h

theorem cliqueCoverNum_lexProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ·g cycle (2 * n + 4)).cliqueCoverNum = (m + 2) * (n + 2) := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_cycle_even m) (cliqueCoverNum_eq_indepNum_cycle_even n)
  rw [indepNum_cycle, indepNum_cycle, show (2 * m + 4) / 2 = m + 2 from by omega,
    show (2 * n + 4) / 2 = n + 2 from by omega] at h
  exact h

theorem cliqueCoverNum_lexProduct_path_complete (m n : ℕ) :
    (path m ·g complete (n + 1)).cliqueCoverNum = (m + 1) / 2 := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_path m) (cliqueCoverNum_eq_indepNum_complete n)
  rw [indepNum_path, indepNum_complete, Nat.min_eq_right (by omega : 1 ≤ n + 1)] at h
  simpa using h

theorem isVertexTransitive_cartesianProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m □g cycle n) :=
  (isVertexTransitive_complete m).cartesianProduct (isVertexTransitive_cycle n)

theorem isVertexTransitive_tensorProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m ⊗g cycle n) :=
  (isVertexTransitive_complete m).tensorProduct (isVertexTransitive_cycle n)

theorem isVertexTransitive_strongProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m ⊠g cycle n) :=
  (isVertexTransitive_complete m).strongProduct (isVertexTransitive_cycle n)

theorem isVertexTransitive_lexProduct_complete_cycle (m n : ℕ) :
    IsVertexTransitive (complete m ·g cycle n) :=
  (isVertexTransitive_complete m).lexProduct (isVertexTransitive_cycle n)

theorem isRegularWith_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 1) □g cycle (n + 3)).IsRegularWith (m + 2) := by
  have h := (isRegularWith_complete (m + 1)).cartesianProduct (isRegularWith_cycle n)
  rwa [show m + 1 - 1 + 2 = m + 2 from by omega] at h

/-! ### Class-one cartesian products

`χ'(G □ H) ≤ χ'(G) + χ'(H)` meets the maximum degree exactly when both factors do, so a product of
two class-one graphs is class one.  Every case below has an even complete graph or an even cycle
on each side, since those are the class-one members of their families. -/

/-- **`K_{2m+2} □ Pₙ` is class one.** -/
theorem edgeChromNum_cartesianProduct_complete_even_path (m n : ℕ) :
    (complete (2 * m + 2) □g path (n + 3)).edgeChromNum = 2 * m + 3 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := complete (2 * m + 2)) (H := path (n + 3))
      (E_complete_pos (2 * m))
      (by rw [show n + 3 = (n + 2) + 1 from rfl, E_path]; omega)
    rwa [edgeChromNum_complete_even, edgeChromNum_path, show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h
  · have h := maxDeg_le_edgeChromNum (complete (2 * m + 2) □g path (n + 3))
    rwa [show 2 * m + 2 = (2 * m + 1) + 1 by omega, maxDeg_cartesianProduct_complete_path,
      show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h

/-- **`K_{2m+2} □ C_{2n+4}` is class one.** -/
theorem edgeChromNum_cartesianProduct_complete_even_cycle_even (m n : ℕ) :
    (complete (2 * m + 2) □g cycle (2 * n + 4)).edgeChromNum = 2 * m + 3 := by
  refine le_antisymm ?_ ?_
  · have h := edgeChromNum_cartesianProduct_le (G := complete (2 * m + 2))
      (H := cycle (2 * n + 4)) (E_complete_pos (2 * m))
      (by rw [show 2 * n + 4 = (2 * n + 1) + 3 by omega, E_cycle]; omega)
    rwa [edgeChromNum_complete_even, edgeChromNum_cycle_even,
      show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h
  · have h := maxDeg_le_edgeChromNum (complete (2 * m + 2) □g cycle (2 * n + 4))
    rwa [show 2 * m + 2 = (2 * m + 1) + 1 by omega, show 2 * n + 4 = (2 * n + 1) + 3 by omega,
      maxDeg_cartesianProduct_complete_cycle, show 2 * m + 1 + 2 = 2 * m + 3 by ring] at h

/-! ### The strong product of a complete graph with a cycle -/

theorem isConnected_strongProduct_complete_cycle (m n : ℕ) :
    IsConnected (complete (m + 1) ⊠g cycle (n + 1)) :=
  isConnected_strongProduct (isConnected_complete m) (isConnected_cycle n)

theorem diameter_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ⊠g cycle (n + 1)).diameter = max 1 ((n + 1) / 2) := by
  rw [diameter_strongProduct (isConnected_complete (m + 1)) (isConnected_cycle n),
    diameter_complete, diameter_cycle]

theorem radius_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) ⊠g cycle (n + 1)).radius = max 1 ((n + 1) / 2) := by
  rw [radius_strongProduct (isConnected_complete (m + 1)) (isConnected_cycle n), radius_complete,
    radius_cycle]

theorem isRegularWith_strongProduct_complete_cycle (m n : ℕ) :
    (complete (m + 1) ⊠g cycle (n + 3)).IsRegularWith (3 * m + 2) := by
  have h := (isRegularWith_complete (m + 1)).strongProduct (isRegularWith_cycle n)
  rwa [show (m + 1 - 1 + 1) * (2 + 1) - 1 = 3 * m + 2 from by omega] at h

theorem isRegularWith_lexProduct_complete_cycle (m n : ℕ) :
    (complete (m + 1) ·g cycle (n + 3)).IsRegularWith (m * (n + 3) + 2) := by
  have h := (isRegularWith_complete (m + 1)).lexProduct (isRegularWith_cycle n)
  rw [V_cycle, show m + 1 - 1 = m from by omega] at h
  exact h

theorem cliqueCoverNum_lexProduct_complete_cycle_even (m n : ℕ) :
    (complete (m + 1) ·g cycle (2 * n + 4)).cliqueCoverNum = n + 2 := by
  have h := cliqueCoverNum_lexProduct_of_cliqueCoverNum_eq_indepNum
    (cliqueCoverNum_eq_indepNum_complete m) (cliqueCoverNum_eq_indepNum_cycle_even n)
  rw [indepNum_complete, indepNum_cycle, Nat.min_eq_right (by omega : 1 ≤ m + 1),
    Nat.one_mul] at h
  omega

/-! ### The strong product of a complete graph with a path -/

theorem isConnected_strongProduct_complete_path (m n : ℕ) :
    IsConnected (complete (m + 1) ⊠g path (n + 1)) :=
  isConnected_strongProduct (isConnected_complete m) (isConnected_path n)

theorem diameter_strongProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ⊠g path (n + 1)).diameter = max 1 n := by
  rw [diameter_strongProduct (isConnected_complete (m + 1)) (isConnected_path n),
    diameter_complete, diameter_path]

theorem radius_strongProduct_complete_path (m n : ℕ) :
    (complete (m + 2) ⊠g path (n + 1)).radius = max 1 ((n + 1) / 2) := by
  rw [radius_strongProduct (isConnected_complete (m + 1)) (isConnected_path n), radius_complete,
    radius_path]

theorem domNum_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 3))).domNum = (m + 5) / 3 + 1 := by
  have h := domNum_mycielskian (cycle (m + 3)) (by rw [V_cycle]; omega)
  rw [domNum_cycle] at h
  omega

theorem isConnected_mycielskian_cycle (m : ℕ) :
    IsConnected (mycielskian (cycle (m + 3))) :=
  isConnected_mycielskian _ (by rw [minDeg_cycle]; omega)

theorem numComponents_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 3))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_cycle]; omega)

theorem radius_mycielskian_cycle (m : ℕ) : (mycielskian (cycle (m + 3))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_cycle]; omega)

theorem four_le_girth_mycielskian_cycle (m : ℕ) :
    4 ≤ (mycielskian (cycle (m + 4))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_cycle]) (by rw [E_cycle]; omega)

theorem matchNum_mycielskian_cycle_even (m : ℕ) :
    (mycielskian (cycle (2 * m + 4))).matchNum = 2 * m + 4 := by
  have h := matchNum_mycielskian (G := cycle (2 * m + 4)) (by rw [matchNum_cycle, V_cycle]; omega)
  rwa [V_cycle] at h

theorem cliqueCoverNum_mycielskian_cycle_even (m : ℕ) :
    (mycielskian (cycle (2 * m + 4))).cliqueCoverNum = 2 * m + 5 := by
  have h := cliqueCoverNum_mycielskian (cycle (2 * m + 4)) (by rw [V_cycle]; omega)
    (by rw [cliqueNum_cycle]) (by rw [matchNum_cycle, V_cycle]; omega)
  rw [V_cycle] at h
  omega

theorem domNum_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 1))).domNum = (m + 3) / 3 + 1 := by
  have h := domNum_mycielskian (path (m + 1)) (by rw [V_path]; omega)
  rw [domNum_path] at h
  omega

theorem isConnected_mycielskian_path (m : ℕ) :
    IsConnected (mycielskian (path (m + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_path]; omega)

theorem numComponents_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_path]; omega)

theorem radius_mycielskian_path (m : ℕ) : (mycielskian (path (m + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_path]; omega)

theorem four_le_girth_mycielskian_path (m : ℕ) :
    4 ≤ (mycielskian (path (m + 2))).girth :=
  four_le_girth_mycielskian _ (by rw [cliqueNum_path]) (by rw [E_path]; omega)

theorem matchNum_mycielskian_path_even (m : ℕ) :
    (mycielskian (path (2 * m + 2))).matchNum = 2 * m + 2 := by
  have h := matchNum_mycielskian (G := path (2 * m + 2)) (by rw [matchNum_path, V_path]; omega)
  rwa [V_path] at h

theorem cliqueCoverNum_mycielskian_path_even (m : ℕ) :
    (mycielskian (path (2 * m + 2))).cliqueCoverNum = 2 * m + 3 := by
  have h := cliqueCoverNum_mycielskian (path (2 * m + 2)) (by rw [V_path]; omega)
    (by rw [cliqueNum_path]) (by rw [matchNum_path, V_path]; omega)
  rw [V_path] at h
  omega

theorem domNum_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 1))).domNum = 2 := by
  have h := domNum_mycielskian (complete (m + 1)) (by rw [V_complete]; omega)
  rw [domNum_complete] at h
  omega

theorem isConnected_mycielskian_complete (m : ℕ) :
    IsConnected (mycielskian (complete (m + 2))) :=
  isConnected_mycielskian _ (by rw [minDeg_complete]; omega)

theorem numComponents_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 2))).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_complete]; omega)

theorem radius_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 2))).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_complete]; omega)

theorem girth_mycielskian_complete (m : ℕ) :
    (mycielskian (complete (m + 3))).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  have h := cliqueNum_mycielskian (complete (m + 3)) (by rw [V_complete]; omega)
  rw [cliqueNum_complete] at h
  omega

theorem matchNum_mycielskian_complete_even (m : ℕ) :
    (mycielskian (complete (2 * m))).matchNum = 2 * m := by
  have h := matchNum_mycielskian (G := complete (2 * m))
    (by rw [matchNum_complete, V_complete]; omega)
  rwa [V_complete] at h

/-! ### The join of a cycle and a complete graph -/

theorem cliqueCoverNum_join_cycle_complete (m n : ℕ) :
    (cycle (m + 4) ∇g complete (n + 1)).cliqueCoverNum = (m + 5) / 2 := by
  have h := cliqueCoverNum_join (cycle (m + 4)) (complete (n + 1))
  rw [cliqueCoverNum_cycle, cliqueCoverNum_complete] at h
  omega

/-! ### The disjoint union of a path and a cycle -/

theorem chromNum_disjUnion_path_cycle_odd (m n : ℕ) :
    (path (m + 2) ⊕g cycle (2 * n + 3)).chromNum = 3 := by
  have h := chromNum_disjUnion (path (m + 2)) (cycle (2 * n + 3))
  rw [chromNum_path, chromNum_cycle_odd] at h
  omega

theorem edgeChromNum_disjUnion_path_cycle_odd (m n : ℕ) :
    (path (m + 3) ⊕g cycle (2 * n + 3)).edgeChromNum = 3 := by
  have h := edgeChromNum_disjUnion (path (m + 3)) (cycle (2 * n + 3))
  rw [edgeChromNum_path, edgeChromNum_cycle_odd] at h
  omega

theorem not_isConnected_disjUnion_path_cycle (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g cycle (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_cycle]; omega)

theorem not_isConnected_disjUnion_path_complete (m n : ℕ) :
    ¬ IsConnected (path (m + 1) ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_path]; omega) (by rw [V_complete]; omega)

theorem not_isConnected_disjUnion_cycle_complete (m n : ℕ) :
    ¬ IsConnected (cycle (m + 1) ⊕g complete (n + 1)) :=
  not_isConnected_disjUnion (by rw [V_cycle]; omega) (by rw [V_complete]; omega)

theorem isConnected_lineGraph_mycielskian {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    IsConnected (lineGraph (mycielskian G)) :=
  isConnected_lineGraph (isConnected_mycielskian G h) (E_pos_mycielskian hV)

theorem numComponents_lineGraph_mycielskian {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    (lineGraph (mycielskian G)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_mycielskian G h) (E_pos_mycielskian hV)

theorem radius_lineGraph_mycielskian_le {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    (lineGraph (mycielskian G)).radius ≤ 3 := by
  have hr := radius_lineGraph_le (G := mycielskian G) (isConnected_mycielskian G h)
    (E_pos_mycielskian hV)
  rw [radius_mycielskian G h] at hr
  omega

theorem diameter_lineGraph_mycielskian_le {G : IsoGraph} (h : 0 < G.minDeg) (hV : 0 < G.V) :
    (lineGraph (mycielskian G)).diameter ≤ 5 := by
  have hd := diameter_lineGraph_le (G := mycielskian G) (isConnected_mycielskian G h)
    (E_pos_mycielskian hV)
  have h4 := diameter_mycielskian_le_four G h
  omega

theorem isConnected_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    IsConnected (mycielskian (lineGraph G)) :=
  isConnected_mycielskian _ h

theorem numComponents_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    (mycielskian (lineGraph G)).numComponents = 1 :=
  numComponents_mycielskian _ h

theorem radius_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    (mycielskian (lineGraph G)).radius = 2 :=
  radius_mycielskian _ h

theorem two_le_diameter_mycielskian_lineGraph {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    2 ≤ (mycielskian (lineGraph G)).diameter :=
  two_le_diameter_mycielskian _ h

theorem diameter_mycielskian_lineGraph_le_four {G : IsoGraph} (h : 0 < minDeg (lineGraph G)) :
    (mycielskian (lineGraph G)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ h

theorem domNum_mycielskian_lineGraph {G : IsoGraph} (hE : 0 < G.E) :
    (mycielskian (lineGraph G)).domNum = (lineGraph G).domNum + 1 :=
  domNum_mycielskian _ (by rw [V_lineGraph]; exact hE)

theorem matchNum_mycielskian_lineGraph {G : IsoGraph} (h : 2 * (lineGraph G).matchNum = G.E) :
    (mycielskian (lineGraph G)).matchNum = G.E := by
  have hm := matchNum_mycielskian (G := lineGraph G) (by rw [V_lineGraph]; exact h)
  rwa [V_lineGraph] at hm

/-! ### The iterated line graph -/

theorem isRegularWith_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) (h : degSequence G = List.replicate n k) :
    (lineGraph (lineGraph G)).IsRegularWith (2 * (2 * k - 2) - 2) :=
  isRegularWith_lineGraph hE2 (isRegularWith_lineGraph hE h).degSequence

theorem maxDeg_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) (h : degSequence G = List.replicate n k) :
    maxDeg (lineGraph (lineGraph G)) = 2 * (2 * k - 2) - 2 :=
  maxDeg_lineGraph hE2 (isRegularWith_lineGraph hE h).degSequence

theorem minDeg_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) (h : degSequence G = List.replicate n k) :
    minDeg (lineGraph (lineGraph G)) = 2 * (2 * k - 2) - 2 :=
  minDeg_lineGraph hE2 (isRegularWith_lineGraph hE h).degSequence

theorem maxDeg_lineGraph_lineGraph_le (G : IsoGraph) :
    maxDeg (lineGraph (lineGraph G)) ≤ 2 * (2 * maxDeg G - 2) - 2 := by
  have h1 := maxDeg_lineGraph_le (lineGraph G)
  have h2 := maxDeg_lineGraph_le G
  omega

theorem isConnected_lineGraph_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : IsConnected (lineGraph (lineGraph G)) :=
  isConnected_lineGraph (isConnected_lineGraph hG hE) hE2

theorem numComponents_lineGraph_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : (lineGraph (lineGraph G)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_lineGraph hG hE) hE2

theorem radius_lineGraph_lineGraph_le {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : (lineGraph (lineGraph G)).radius ≤ G.radius + 2 := by
  have h1 := radius_lineGraph_le (G := lineGraph G) (isConnected_lineGraph hG hE) hE2
  have h2 := radius_lineGraph_le (G := G) hG hE
  omega

theorem diameter_lineGraph_lineGraph_le {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E)
    (hE2 : 0 < (lineGraph G).E) : (lineGraph (lineGraph G)).diameter ≤ G.diameter + 2 := by
  have h1 := diameter_lineGraph_le (G := lineGraph G) (isConnected_lineGraph hG hE) hE2
  have h2 := diameter_lineGraph_le (G := G) hG hE
  omega

theorem cliqueNum_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    (lineGraph (lineGraph G)).cliqueNum = 2 * k - 2 := by
  have hm := cliqueNum_lineGraph_of_three_le_maxDeg (G := lineGraph G)
    (by rw [maxDeg_lineGraph hE h]; exact h3)
  rwa [maxDeg_lineGraph hE h] at hm

theorem girth_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    (lineGraph (lineGraph G)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_lineGraph hE h]; exact h3)

theorem not_isBipartite_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    ¬ IsBipartite (lineGraph (lineGraph G)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_lineGraph hE h]; exact h3)

theorem not_isTree_lineGraph_lineGraph {G : IsoGraph} {n k : ℕ} (hE : 0 < G.E)
    (h : degSequence G = List.replicate n k) (h3 : 3 ≤ 2 * k - 2) :
    ¬ IsTree (lineGraph (lineGraph G)) :=
  not_isTree_lineGraph (by rw [maxDeg_lineGraph hE h]; exact h3)

theorem isConnected_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    IsConnected (mycielskian (mycielskian G)) :=
  isConnected_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem numComponents_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    (mycielskian (mycielskian G)).numComponents = 1 :=
  numComponents_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem radius_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    (mycielskian (mycielskian G)).radius = 2 :=
  radius_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem two_le_diameter_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V)
    (h : 0 < G.minDeg) : 2 ≤ (mycielskian (mycielskian G)).diameter :=
  two_le_diameter_mycielskian _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem diameter_mycielskian_mycielskian_le_four {G : IsoGraph} (hV : 0 < G.V)
    (h : 0 < G.minDeg) : (mycielskian (mycielskian G)).diameter ≤ 4 :=
  diameter_mycielskian_le_four _ (by rw [minDeg_mycielskian_of_pos hV h]; omega)

theorem four_le_girth_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V)
    (hc : G.cliqueNum ≤ 2) : 4 ≤ (mycielskian (mycielskian G)).girth := by
  refine four_le_girth_mycielskian _ ?_ (by rw [E_mycielskian]; omega)
  rw [cliqueNum_mycielskian G hV]
  omega

theorem domNum_mycielskian_mycielskian {G : IsoGraph} (hV : 0 < G.V) :
    (mycielskian (mycielskian G)).domNum = G.domNum + 2 := by
  have h1 := domNum_mycielskian (mycielskian G) (by rw [V_mycielskian]; omega)
  rw [domNum_mycielskian G hV] at h1
  omega

theorem coverNum_mycielskian_mycielskian_le (G : IsoGraph) :
    (mycielskian (mycielskian G)).coverNum ≤ 2 * G.V + 2 := by
  have h := coverNum_mycielskian_le (mycielskian G)
  rw [V_mycielskian] at h
  omega

theorem isConnected_lineGraph_cartesianProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) : IsConnected (lineGraph (G □g H)) :=
  isConnected_lineGraph (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE

theorem numComponents_lineGraph_cartesianProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) : (lineGraph (G □g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE

theorem diameter_lineGraph_cartesianProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) :
    (lineGraph (G □g H)).diameter ≤ G.diameter + H.diameter + 1 := by
  have h := diameter_lineGraph_le (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE
  rw [diameter_cartesianProduct hG hH] at h
  omega

theorem radius_lineGraph_cartesianProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G □g H).E) :
    (lineGraph (G □g H)).radius ≤ G.radius + H.radius + 1 := by
  have h := radius_lineGraph_le (isConnected_cartesianProduct.2 ⟨hG, hH⟩) hE
  rw [radius_cartesianProduct hG hH] at h
  omega

theorem isConnected_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (lineGraph (G ∇g H)) :=
  isConnected_lineGraph (isConnected_join hG hH) (E_pos_join hG hH)

theorem numComponents_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (lineGraph (G ∇g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_join hG hH) (E_pos_join hG hH)

theorem diameter_lineGraph_join_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (lineGraph (G ∇g H)).diameter ≤ 3 := by
  have h := diameter_lineGraph_le (isConnected_join hG hH) (E_pos_join hG hH)
  have h2 := diameter_join_le_two _ _ hG hH
  omega

theorem numComponents_lineGraph_disjUnion {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    (lineGraph (G ⊕g H)).numComponents = 2 := by
  rw [lineGraph_disjUnion, numComponents_disjUnion, numComponents_lineGraph hG hE,
    numComponents_lineGraph hH hE2]

theorem not_isConnected_lineGraph_disjUnion {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    ¬ IsConnected (lineGraph (G ⊕g H)) := by
  intro h
  have h1 := numComponents_eq_one_of_isConnected h
  rw [numComponents_lineGraph_disjUnion hG hH hE hE2] at h1
  omega

theorem isConnected_lineGraph_strongProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ⊠g H).E) : IsConnected (lineGraph (G ⊠g H)) :=
  isConnected_lineGraph (isConnected_strongProduct hG hH) hE

theorem diameter_lineGraph_strongProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ⊠g H).E) :
    (lineGraph (G ⊠g H)).diameter ≤ max G.diameter H.diameter + 1 := by
  have h := diameter_lineGraph_le (isConnected_strongProduct hG hH) hE
  rw [diameter_strongProduct hG hH] at h
  omega

theorem radius_lineGraph_strongProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ⊠g H).E) :
    (lineGraph (G ⊠g H)).radius ≤ max G.radius H.radius + 1 := by
  have h := radius_lineGraph_le (isConnected_strongProduct hG hH) hE
  rw [radius_strongProduct hG hH] at h
  omega

/-! ### The line graph of a complement -/

theorem V_lineGraph_compl (G : IsoGraph) : (lineGraph Gᶜ).V + G.E = G.V.choose 2 := by
  rw [V_lineGraph]
  exact E_compl G

theorem maxDeg_lineGraph_compl_le {G : IsoGraph} (hG : 0 < G.V) :
    maxDeg (lineGraph Gᶜ) ≤ 2 * (G.V - 1 - minDeg G) - 2 := by
  have h := maxDeg_lineGraph_le Gᶜ
  rwa [maxDeg_compl hG] at h

theorem le_minDeg_lineGraph_compl {G : IsoGraph} (hG : 0 < G.V) (hE : 0 < Gᶜ.E) :
    2 * (G.V - 1 - maxDeg G) - 2 ≤ minDeg (lineGraph Gᶜ) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_compl hG] at h

theorem isConnected_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (mycielskian (G ∇g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_join hG hH]
  omega

theorem radius_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (mycielskian (G ∇g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_join hG hH]
  omega

theorem isConnected_mycielskian_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) : IsConnected (mycielskian (G □g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_cartesianProduct hG hH]
  omega

theorem radius_mycielskian_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) : (mycielskian (G □g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_cartesianProduct hG hH]
  omega

theorem matchNum_mycielskian_disjUnion {G H : IsoGraph}
    (h : 2 * (G.matchNum + H.matchNum) = G.V + H.V) :
    (mycielskian (G ⊕g H)).matchNum = G.V + H.V := by
  have hm := matchNum_mycielskian (G := G ⊕g H) (by rw [matchNum_disjUnion, V_disjUnion]; exact h)
  rwa [V_disjUnion] at hm

theorem domNum_mycielskian_disjUnion {G H : IsoGraph} (hG : 0 < G.V) :
    (mycielskian (G ⊕g H)).domNum = G.domNum + H.domNum + 1 := by
  have hm := domNum_mycielskian (G ⊕g H) (by rw [V_disjUnion]; omega)
  rwa [domNum_disjUnion] at hm

/-! ### The Mycielskian of a complement -/

theorem E_mycielskian_compl (G : IsoGraph) :
    (mycielskian Gᶜ).E + 3 * G.E = 3 * (G.V.choose 2) + G.V := by
  have h := E_compl G
  rw [E_mycielskian, V_compl]
  omega

theorem maxDeg_mycielskian_compl {G : IsoGraph} (hG : 0 < G.V) :
    maxDeg (mycielskian Gᶜ) = max (2 * (G.V - 1 - minDeg G)) G.V := by
  rw [maxDeg_mycielskian, maxDeg_compl hG, V_compl]

theorem isConnected_lineGraph_tensorProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hb : ¬ IsBipartite G) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    IsConnected (lineGraph (G ⊗g H)) :=
  isConnected_lineGraph (isConnected_tensorProduct hG hH hb hE2) (E_pos_tensorProduct hE hE2)

theorem numComponents_lineGraph_tensorProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hb : ¬ IsBipartite G) (hE : 0 < G.E) (hE2 : 0 < H.E) :
    (lineGraph (G ⊗g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_tensorProduct hG hH hb hE2) (E_pos_tensorProduct hE hE2)

theorem isConnected_lineGraph_lexProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ·g H).E) : IsConnected (lineGraph (G ·g H)) :=
  isConnected_lineGraph (isConnected_lexProduct hG hH) hE

theorem numComponents_lineGraph_lexProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ·g H).E) : (lineGraph (G ·g H)).numComponents = 1 :=
  numComponents_lineGraph (isConnected_lexProduct hG hH) hE

theorem diameter_lineGraph_lexProduct_le {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) (hE : 0 < (G ·g H).E) :
    (lineGraph (G ·g H)).diameter ≤ G.diameter + H.diameter + 1 := by
  have h := diameter_lineGraph_le (isConnected_lexProduct hG hH) hE
  have h2 := diameter_lexProduct_le hG hH
  omega

theorem isConnected_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) (h2 : 0 < minDeg H) : IsConnected (mycielskian (G ⊗g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_tensorProduct hG hH]
  exact Nat.mul_pos h h2

theorem radius_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg G) (h2 : 0 < minDeg H) : (mycielskian (G ⊗g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_tensorProduct hG hH]
  exact Nat.mul_pos h h2

theorem isConnected_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg H) : IsConnected (mycielskian (G ·g H)) := by
  refine isConnected_mycielskian _ ?_
  rw [minDeg_lexProduct hG hH]
  omega

theorem radius_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h : 0 < minDeg H) : (mycielskian (G ·g H)).radius = 2 := by
  refine radius_mycielskian _ ?_
  rw [minDeg_lexProduct hG hH]
  omega

end IsoGraph
