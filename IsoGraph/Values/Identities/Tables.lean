import IsoGraph.Values.Identities.Identifications
import IsoGraph.ForMathlib.Nat

/-!
# Line graphs, Mycielskians, and the first of the tables

The line graph and the Mycielskian of each family, and then the beginning of the invariant
tables: the degree multisets, the chromatic numbers, the girths and the maximum degrees of every
construction, each as a `simp` lemma about the isomorphism class.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ## Lifts held over from `Constructions.lean`

`@[toIsoGraph]` can only state a fact once every constant in it has a bridge, and
`Constructions.lean` runs before `Quotient.lean`: the order and the products have none there yet.
These five are tagged here instead, which lifts them exactly as the attribute would have. -/

attribute [toIsoGraph] CGraph.E_compl
attribute [toIsoGraph] CGraph.not_isConnected_disjUnion
attribute [toIsoGraph IsVertexTransitive.cartesianProduct]
  CGraph.isVertexTransitive_cartesianProduct
attribute [toIsoGraph IsVertexTransitive.tensorProduct] CGraph.isVertexTransitive_tensorProduct
attribute [toIsoGraph IsVertexTransitive.strongProduct] CGraph.isVertexTransitive_strongProduct

/-! ## Line graphs and Mycielskians

The line graph turns a graph's edges into vertices, so the identities here are counted by `E`
rather than `V`: `lineGraph (star n)` is complete on `E (star n) = n` vertices, and
`lineGraph (complete n)` is the triangular graph `T(n) = J(n, 2)` on `C(n, 2)` of them. -/

/-- **The line graph of a disjoint union is the disjoint union of the line graphs.** -/
@[simp] theorem lineGraph_disjUnion (G H : IsoGraph) :
    lineGraph (G ⊕g H) = lineGraph G ⊕g lineGraph H := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      rw [← mk_canonicalize g, ← mk_canonicalize h, disjUnion_mk, lineGraph_mk, lineGraph_mk,
        lineGraph_mk, disjUnion_mk]
      exact Quotient.sound ⟨CGraph.Iso.lineGraphDisjUnion _ _⟩

@[simp] theorem lineGraph_empty (n : ℕ) : lineGraph (empty n) = empty 0 := by
  have hbot : (CGraph.empty n).toSimple = ⊥ := by
    ext a b
    simp [CGraph.toSimple]
  have h : ∀ e f : (CGraph.lineGraph (CGraph.empty n)).V,
      (CGraph.lineGraph (CGraph.empty n)).Adj e f = false := by
    rintro ⟨e, he⟩ f
    rw [hbot] at he
    simp at he
  rw [empty_def, lineGraph_mk, mk_eq_empty h, CGraph.card_lineGraph, CGraph.E_empty]

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

/-- **The line graph of a complete graph is the triangular graph.**  An edge of `Kₙ` is a
two-element subset of `Fin n`, and two distinct such subsets meet exactly when they meet in
*one* point — which is the adjacency of `J(n, 2)`. -/
@[simp] theorem lineGraph_complete (n : ℕ) : lineGraph (complete n) = johnson n 2 := by
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
  rw [complete_def, lineGraph_mk, johnson_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj (Equiv.ofBijective F ⟨hinj, hsurj⟩) hadj⟩

/-- The same statement under the other name for `J(n, 2)`. -/
theorem lineGraph_complete_eq_triangular (n : ℕ) : lineGraph (complete n) = triangular n :=
  lineGraph_complete n

/-! ### Edge counts

`V_*` reads the vertex count of every family off its `CGraph` counterpart; these do the same for
the edge count.  The operations all follow the same script: push the quotient through with
`mk_canonicalize`, replace the constructor by its `CGraph` form, and apply the `CGraph` lemma. -/

@[simp] theorem E_empty (n : ℕ) : (empty n).E = 0 := CGraph.E_empty n

@[simp] theorem E_complete (n : ℕ) : (complete n).E = n.choose 2 := CGraph.E_complete n

@[simp] theorem E_path (n : ℕ) : (path (n + 1)).E = n := CGraph.E_path n

@[simp] theorem E_cycle (n : ℕ) : (cycle (n + 3)).E = n + 3 := CGraph.E_cycle n

@[simp] theorem E_bipartite (m n : ℕ) : (bipartite m n).E = m * n := CGraph.E_bipartite m n

@[simp] theorem E_star (n : ℕ) : (star n).E = n := CGraph.E_star n

@[simp] theorem E_disjUnion (G H : IsoGraph) : (G ⊕g H).E = G.E + H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.E_disjUnion g h

@[simp] theorem E_join (G H : IsoGraph) : (G ∇g H).E = G.E + H.E + G.V * H.V := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_join _ _

@[simp] theorem E_cartesianProduct (G H : IsoGraph) :
    (G □g H).E = G.V * H.E + H.V * G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_cartesianProduct _ _

@[simp] theorem E_tensorProduct (G H : IsoGraph) : (G ⊗g H).E = 2 * G.E * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, E_mk, E_mk, E_mk]
  exact CGraph.E_tensorProduct _ _

@[simp] theorem E_mycielskian (G : IsoGraph) : (mycielskian G).E = 3 * G.E + G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, E_mk, E_mk, V_mk]
  exact CGraph.E_mycielskian _

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

/-! ### Connectivity -/

@[simp] theorem isConnected_empty_one : IsConnected (empty 1) := CGraph.isConnected_empty_one

@[simp] theorem isConnected_complete (n : ℕ) : IsConnected (complete (n + 1)) :=
  CGraph.isConnected_complete n

@[simp] theorem isConnected_path (n : ℕ) : IsConnected (path (n + 1)) := CGraph.isConnected_path n

@[simp] theorem isConnected_cycle (n : ℕ) : IsConnected (cycle (n + 1)) :=
  CGraph.isConnected_cycle n

@[simp] theorem isConnected_bipartite (m n : ℕ) : IsConnected (bipartite (m + 1) (n + 1)) :=
  CGraph.isConnected_bipartite m n

@[simp] theorem isAcyclic_empty (n : ℕ) : IsAcyclic (empty n) := CGraph.isAcyclic_empty n

@[simp] theorem isAcyclic_path (n : ℕ) : IsAcyclic (path n) := CGraph.isAcyclic_path n

@[simp] theorem isTree_path (n : ℕ) : IsTree (path (n + 1)) := CGraph.isTree_path n

@[simp] theorem not_isAcyclic_cycle (n : ℕ) : ¬ IsAcyclic (cycle (n + 3)) :=
  CGraph.not_isAcyclic_cycle n

@[simp] theorem isConnected_star (n : ℕ) : IsConnected (star n) := by
  cases n with
  | zero => rw [star_zero]; exact isConnected_empty_one
  | succ n => exact isConnected_bipartite 0 n

/-- A join of two nonempty graphs is connected, whatever the two graphs are. -/
@[simp] theorem isConnected_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (G ∇g H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, isConnected_mk]
  rw [V_mk] at hG hH
  exact CGraph.isConnected_join _ _ hG hH

/-- The Cartesian product is connected exactly when both factors are. -/
@[simp] theorem isConnected_cartesianProduct {G H : IsoGraph} :
    IsConnected (G □g H) ↔ IsConnected G ∧ IsConnected H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, isConnected_mk,
    isConnected_mk, isConnected_mk]
  exact CGraph.isConnected_cartesianProduct_iff _ _

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

/-! ### Trees, and Euler's count -/

theorem isTree_iff_isConnected_and_isAcyclic (G : IsoGraph) :
    IsTree G ↔ IsConnected G ∧ IsAcyclic G := by
  induction G using Quotient.inductionOn with | _ g =>
  exact SimpleGraph.isTree_iff _

theorem IsTree.E_add_one {G : IsoGraph} (h : IsTree G) : G.E + 1 = G.V :=
  ((isTree_iff G).1 h).2

/-- Too few edges to be connected. -/
theorem not_isConnected_of_E_add_one_lt {G : IsoGraph} (h : G.E + 1 < G.V) : ¬ IsConnected G :=
  fun hc ↦ absurd hc.V_le_E_add_one (by omega)

@[simp] theorem not_isConnected_empty (n : ℕ) : ¬ IsConnected (empty (n + 2)) :=
  not_isConnected_of_E_add_one_lt (by simp)

@[simp] theorem isTree_star (n : ℕ) : IsTree (star n) := by
  rw [isTree_iff, E_star, V_star]
  exact ⟨isConnected_star n, by omega⟩

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

/-- Anything connected that is not a tree has a cycle. -/
theorem not_isAcyclic_of_isConnected {G : IsoGraph} (hc : IsConnected G) (h : ¬ IsTree G) :
    ¬ IsAcyclic G :=
  fun ha ↦ h ((isTree_iff_isConnected_and_isAcyclic G).2 ⟨hc, ha⟩)

@[simp] theorem not_isAcyclic_complete (n : ℕ) : ¬ IsAcyclic (complete (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_complete (n + 2)) (not_isTree_complete n)

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

/-! ### Cliques, independent sets and diameter -/

@[simp] theorem indepNum_empty (n : ℕ) : (empty n).indepNum = n := CGraph.indepNum_empty n

@[simp] theorem cliqueNum_empty (n : ℕ) : (empty n).cliqueNum = min n 1 :=
  CGraph.cliqueNum_empty n

@[simp] theorem cliqueNum_complete (n : ℕ) : (complete n).cliqueNum = n :=
  CGraph.cliqueNum_complete n

@[simp] theorem indepNum_complete (n : ℕ) : (complete n).indepNum = min n 1 :=
  CGraph.indepNum_complete n

@[simp] theorem indepNum_cycle (n : ℕ) : (cycle (n + 3)).indepNum = (n + 3) / 2 :=
  CGraph.indepNum_cycle n

@[simp] theorem indepNum_bipartite (m n : ℕ) : (bipartite m n).indepNum = max m n :=
  CGraph.indepNum_bipartite m n

@[simp] theorem cliqueNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).cliqueNum = 2 :=
  CGraph.cliqueNum_bipartite m n

@[simp] theorem diameter_complete (n : ℕ) : (complete (n + 2)).diameter = 1 :=
  CGraph.diameter_complete n

@[simp] theorem diameter_path (n : ℕ) : (path (n + 1)).diameter = n := CGraph.diameter_path n

@[simp] theorem diameter_cycle (n : ℕ) : (cycle (n + 1)).diameter = (n + 1) / 2 :=
  CGraph.diameter_cycle n

@[simp] theorem diameter_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).diameter = 2 :=
  CGraph.diameter_bipartite m n

@[simp] theorem indepNum_compl (G : IsoGraph) : Gᶜ.indepNum = G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, indepNum_mk, cliqueNum_mk]
  exact CGraph.indepNum_compl _

@[simp] theorem cliqueNum_compl (G : IsoGraph) : Gᶜ.cliqueNum = G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, indepNum_mk, cliqueNum_mk]
  exact CGraph.cliqueNum_compl _

@[simp] theorem indepNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).indepNum = G.indepNum + H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.indepNum_disjUnion _ _

@[simp] theorem cliqueNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.cliqueNum_disjUnion _ _

@[simp] theorem cliqueNum_join (G H : IsoGraph) :
    (G ∇g H).cliqueNum = G.cliqueNum + H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_join _ _

@[simp] theorem indepNum_join (G H : IsoGraph) :
    (G ∇g H).indepNum = max G.indepNum H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, indepNum_mk, indepNum_mk, indepNum_mk]
  exact CGraph.indepNum_join _ _

@[simp] theorem indepNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (ds.max?).getD 0 :=
  CGraph.indepNum_completeMultipartite ds

@[simp] theorem indepNum_lexProduct (G H : IsoGraph) :
    (G ·g H).indepNum = G.indepNum * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_lexProduct _ _

@[simp] theorem cliqueNum_strongProduct (G H : IsoGraph) :
    (G ⊠g H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_strongProduct _ _

/-! ### Clique numbers of the cartesian, tensor and lexicographic products -/

theorem cliqueNum_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G □g H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, cliqueNum_mk, cliqueNum_mk, cliqueNum_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.cliqueNum_cartesianProduct _ _ a b

@[simp] theorem cliqueNum_tensorProduct (G H : IsoGraph) :
    (G ⊗g H).cliqueNum = min G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_tensorProduct _ _

@[simp] theorem cliqueNum_lexProduct (G H : IsoGraph) :
    (G ·g H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_lexProduct _ _

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

/-! ### Connectivity and triangles in the strong and lexicographic products -/

theorem not_isBipartite_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsBipartite (G ⊠g H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, isBipartite_mk]
  rw [E_mk] at hG hH
  obtain ⟨a, b, hab⟩ := CGraph.exists_adj_of_E_pos hG
  obtain ⟨c, d, hcd⟩ := CGraph.exists_adj_of_E_pos hH
  exact CGraph.not_isBipartite_strongProduct hab hcd

theorem not_isBipartite_lexProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsBipartite (G ·g H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, isBipartite_mk]
  rw [E_mk] at hG hH
  obtain ⟨a, b, hab⟩ := CGraph.exists_adj_of_E_pos hG
  obtain ⟨c, d, hcd⟩ := CGraph.exists_adj_of_E_pos hH
  exact CGraph.not_isBipartite_lexProduct hab hcd

@[simp] theorem E_complete_pos (n : ℕ) : 0 < (complete (n + 2)).E := by
  rw [E_complete]
  exact Nat.choose_pos (by omega)

@[simp] theorem E_hypercube_pos (n : ℕ) : 0 < (hypercube (n + 1)).E := by
  have h := E_hypercube (n + 1)
  have hp : 0 < (n + 1) * 2 ^ (n + 1) := by positivity
  omega

/-! ### Vertex- and arc-transitivity -/

@[simp] theorem isVertexTransitive_empty (n : ℕ) : IsVertexTransitive (empty n) :=
  CGraph.isVertexTransitive_empty n

@[simp] theorem isArcTransitive_empty (n : ℕ) : IsArcTransitive (empty n) :=
  CGraph.isArcTransitive_empty n

@[simp] theorem isVertexTransitive_complete (n : ℕ) : IsVertexTransitive (complete n) :=
  CGraph.isVertexTransitive_complete n

@[simp] theorem isArcTransitive_complete (n : ℕ) : IsArcTransitive (complete n) :=
  CGraph.isArcTransitive_complete n

@[simp] theorem isVertexTransitive_cycle (n : ℕ) : IsVertexTransitive (cycle n) :=
  CGraph.isVertexTransitive_cycle n

@[simp] theorem isArcTransitive_cycle (n : ℕ) : IsArcTransitive (cycle n) :=
  CGraph.isArcTransitive_cycle n

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

@[simp] theorem isVertexTransitive_compl (G : IsoGraph) :
    IsVertexTransitive Gᶜ ↔ IsVertexTransitive G :=
  ⟨fun h ↦ by simpa using h.compl, IsVertexTransitive.compl⟩

theorem IsVertexTransitive.lexProduct {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : IsVertexTransitive H) : IsVertexTransitive (IsoGraph.lexProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, isVertexTransitive_mk]
  rw [isVertexTransitive_mk] at hG hH
  exact CGraph.isVertexTransitive_lexProduct _ _ hG hH

/-- Arcs of `G` are vertices of its line graph, so arc-transitivity becomes vertex-transitivity. -/
theorem IsArcTransitive.lineGraph {G : IsoGraph} (h : IsArcTransitive G) :
    IsVertexTransitive (IsoGraph.lineGraph G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [lineGraph_mk, isVertexTransitive_mk]
  rw [isArcTransitive_mk] at h
  exact CGraph.isVertexTransitive_lineGraph _ h

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

theorem isSRGWith_triangular (n : ℕ) (hn : 4 ≤ n) :
    IsSRGWith (triangular n) (n.choose 2) (2 * (n - 2)) (n - 2) 4 :=
  isSRGWith_johnson_two n hn

theorem isSRGWith_petersen : IsSRGWith petersen 10 3 0 1 := isSRGWith_kneser_two 5

/-- **The rook's graph is strongly regular.**  This one is written out rather than generated:
`rook` is an abbreviation for a Cartesian product, and `@[toIsoGraph]` would state it for the
product and leave the later `rook` calculations with nothing to match. -/
theorem isSRGWith_rook (k : ℕ) : IsSRGWith (rook k k) (k * k) (2 * (k - 1)) (k - 2) 2 := by
  show IsSRGWith (complete k □g complete k) _ _ _ _
  rw [complete_def, cartesianProduct_mk, isSRGWith_mk]
  exact CGraph.isSRGWith_rook k

/-! ### The diameter of a Cartesian product -/

@[simp] theorem diameter_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).diameter = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [disjUnion_mk, diameter_mk]
  rw [V_mk] at hG hH
  exact CGraph.diameter_disjUnion _ _ hG hH

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

/-- The `m × n` torus, a Cartesian product of two cycles. -/
theorem diameter_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 1) □g cycle (n + 1)).diameter = (m + 1) / 2 + (n + 1) / 2 := by
  rw [diameter_cartesianProduct (isConnected_cycle m) (isConnected_cycle n), diameter_cycle m,
    diameter_cycle n]

/-! ### Degree sequences -/

@[simp] theorem degSequence_empty (n : ℕ) : degSequence (empty n) = List.replicate n 0 :=
  CGraph.degSequence_empty n

@[simp] theorem degSequence_complete (n : ℕ) :
    degSequence (complete n) = List.replicate n (n - 1) := CGraph.degSequence_complete n

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

/-- The handshake lemma for a strongly regular graph: `n` vertices of degree `k` give `n * k / 2`
edges. -/
theorem IsSRGWith.two_mul_E {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    2 * G.E = n * k := by
  rw [← sum_degSequence, h.degSequence, List.sum_replicate, smul_eq_mul]

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

/-- The line graph has one vertex per edge, and one edge per pair of edges meeting at a vertex:
`∑ v, C(deg v, 2)`, written over the degree sequence so as not to name a vertex. -/
theorem E_lineGraph (G : IsoGraph) :
    (lineGraph G).E = ((degSequence G).map fun d ↦ d.choose 2).sum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, lineGraph_mk, E_mk, degSequence_mk]
  exact CGraph.E_lineGraph_eq_sum_degSequence _

/-- A regular graph's line graph has `n * C(k, 2)` edges. -/
theorem IsSRGWith.E_lineGraph {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    (lineGraph G).E = n * k.choose 2 := by
  rw [IsoGraph.E_lineGraph, h.degSequence, List.map_replicate, List.sum_replicate, smul_eq_mul]

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

/-! ### Regular families beyond the strongly regular ones -/

/-- The handshake lemma for any graph whose degree sequence is constant. -/
theorem two_mul_E_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : 2 * G.E = n * k := by
  rw [← sum_degSequence, h, List.sum_replicate, smul_eq_mul]

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

/-! ### Degree sequences of the products

A product of regular graphs is regular, and on the quotient "regular of degree `k`" is exactly
"the degree sequence is `List.replicate _ k`". -/

private theorem card_eq_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : n = G.V := by
  rw [← length_degSequence, h, List.length_replicate]

theorem degSequence_cartesianProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G □g H) = List.replicate (m * n) (k + l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_cartesianProduct hG hH

theorem degSequence_tensorProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G ⊗g H) = List.replicate (m * n) (k * l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_tensorProduct hG hH

theorem degSequence_lexProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G ·g H) = List.replicate (m * n) (k * n + l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_lexProduct hG hH

theorem degSequence_strongProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (G ⊠g H) = List.replicate (m * n) ((k + 1) * (l + 1) - 1) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_strongProduct hG hH

@[simp] theorem degSequence_hypercube (n : ℕ) :
    degSequence (hypercube n) = List.replicate (2 ^ n) n := by
  induction n with
  | zero => rw [hypercube_zero, degSequence_empty]; rfl
  | succ n ih =>
    rw [hypercube_succ, degSequence_cartesianProduct ih (degSequence_complete 2)]
    congr 1

theorem two_mul_E_hypercube (n : ℕ) : 2 * (hypercube n).E = 2 ^ n * n :=
  two_mul_E_of_degSequence_replicate (degSequence_hypercube n)

/-! ### Vertex-transitive graphs are regular -/

/-- A vertex-transitive graph is regular, so the vertex and edge counts already pin down its
degree sequence. -/
theorem degSequence_of_isVertexTransitive {G : IsoGraph} {k : ℕ} (h : IsVertexTransitive G)
    (hV : 0 < G.V) (hk : G.V * k = 2 * G.E) : degSequence G = List.replicate G.V k := by
  obtain ⟨k', hk'⟩ := exists_degSequence_replicate_of_isVertexTransitive h
  have h2 := two_mul_E_of_degSequence_replicate hk'
  have : k = k' := Nat.eq_of_mul_eq_mul_left hV (hk.trans h2)
  rwa [this]

@[simp] theorem degSequence_cycle (n : ℕ) :
    degSequence (cycle (n + 3)) = List.replicate (n + 3) 2 := by
  have h := degSequence_of_isVertexTransitive (k := 2) (isVertexTransitive_cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle, E_cycle]; omega)
  rwa [V_cycle] at h

@[simp] theorem degSequence_prism (n : ℕ) :
    degSequence (prism (n + 3)) = List.replicate ((n + 3) * 2) 3 := by
  show degSequence (cycle (n + 3) □g complete 2) = _
  rw [degSequence_cartesianProduct (degSequence_cycle n) (degSequence_complete 2)]

theorem two_mul_E_prism (n : ℕ) : 2 * (prism (n + 3)).E = (n + 3) * 2 * 3 :=
  two_mul_E_of_degSequence_replicate (degSequence_prism n)

/-! ### Distinguishing graphs

Because `IsoGraph` is the quotient of `CGraph` by isomorphism, `G ≠ H` *is* the assertion that
`G` and `H` are non-isomorphic. Every invariant therefore doubles as a tool for proving
non-isomorphism: if it takes different values on the two graphs, they are different. -/

theorem ne_of_V_ne {G H : IsoGraph} (h : G.V ≠ H.V) : G ≠ H := ne_of_apply_ne V h

theorem ne_of_E_ne {G H : IsoGraph} (h : G.E ≠ H.E) : G ≠ H := ne_of_apply_ne E h

theorem ne_of_degSequence_ne {G H : IsoGraph} (h : degSequence G ≠ degSequence H) : G ≠ H :=
  ne_of_apply_ne degSequence h

theorem ne_of_diameter_ne {G H : IsoGraph} (h : G.diameter ≠ H.diameter) : G ≠ H :=
  ne_of_apply_ne diameter h

theorem ne_of_indepNum_ne {G H : IsoGraph} (h : G.indepNum ≠ H.indepNum) : G ≠ H :=
  ne_of_apply_ne indepNum h

theorem ne_of_cliqueNum_ne {G H : IsoGraph} (h : G.cliqueNum ≠ H.cliqueNum) : G ≠ H :=
  ne_of_apply_ne cliqueNum h

/-- The same principle for predicates: any property of `IsoGraph`s that holds of `G` but fails
for `H` separates them. -/
theorem ne_of_pred {p : IsoGraph → Prop} {G H : IsoGraph} (hG : p G) (hH : ¬ p H) : G ≠ H :=
  fun he ↦ hH (he ▸ hG)

theorem ne_of_isConnected {G H : IsoGraph} (hG : IsConnected G) (hH : ¬ IsConnected H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isAcyclic {G H : IsoGraph} (hG : IsAcyclic G) (hH : ¬ IsAcyclic H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isTree {G H : IsoGraph} (hG : IsTree G) (hH : ¬ IsTree H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isBipartite {G H : IsoGraph} (hG : IsBipartite G) (hH : ¬ IsBipartite H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isVertexTransitive {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : ¬ IsVertexTransitive H) : G ≠ H := ne_of_pred hG hH

theorem ne_of_isArcTransitive {G H : IsoGraph} (hG : IsArcTransitive G)
    (hH : ¬ IsArcTransitive H) : G ≠ H := ne_of_pred hG hH

private theorem replicate_ne {k a b : ℕ} (hk : 0 < k) (hab : a ≠ b) :
    List.replicate k a ≠ List.replicate k b := fun h ↦
  hab (List.eq_of_mem_replicate (h ▸ List.mem_replicate.2 ⟨hk.ne', rfl⟩))

/-- Two regular graphs on the same (positive) number of vertices but of different degree are
non-isomorphic. -/
theorem ne_of_degree_ne {G H : IsoGraph} {n k l : ℕ} (hG : degSequence G = List.replicate n k)
    (hH : degSequence H = List.replicate n l) (hn : 0 < n) (hkl : k ≠ l) : G ≠ H :=
  ne_of_degSequence_ne (by rw [hG, hH]; exact replicate_ne hn hkl)

/-! Each of the standard families is determined by its parameter. -/

@[simp] theorem empty_inj {m n : ℕ} : empty m = empty n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem complete_inj {m n : ℕ} : complete m = complete n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem path_inj {m n : ℕ} : path m = path n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem cycle_inj {m n : ℕ} : cycle m = cycle n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem star_inj {m n : ℕ} : star m = star n ↔ m = n :=
  ⟨fun h ↦ by have h2 := congrArg V h; simp only [V_star] at h2; omega, fun h ↦ by rw [h]⟩

/-! Some non-isomorphisms between the families. -/

theorem empty_ne_complete (n : ℕ) : empty (n + 2) ≠ complete (n + 2) :=
  ne_of_E_ne (by rw [E_empty]; exact (E_complete_pos n).ne)

theorem path_ne_cycle (m n : ℕ) : path (m + 1) ≠ cycle (n + 3) :=
  ne_of_isTree (isTree_path m) (not_isTree_cycle n)

theorem star_ne_cycle (m n : ℕ) : star m ≠ cycle (n + 3) :=
  ne_of_isTree (isTree_star m) (not_isTree_cycle n)

theorem complete_ne_cycle (n : ℕ) : complete (n + 4) ≠ cycle (n + 4) :=
  ne_of_degree_ne (degSequence_complete (n + 4)) (degSequence_cycle (n + 1)) (by omega) (by omega)

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

/-! ### The diameter of a join -/

/-- A join whose left factor is not complete has diameter two. -/
theorem diameter_join_left {G H : IsoGraph} (hH : 0 < H.V) (h : G.E < G.V.choose 2) :
    (G ∇g H).diameter = 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h' =>
  rw [← mk_canonicalize g, ← mk_canonicalize h'] at *
  rw [V_mk] at hH
  rw [E_mk, V_mk] at h
  haveI := Fintype.card_pos_iff.1 hH
  rw [join_mk, diameter_mk]
  obtain ⟨a, c, hne, hadj⟩ := CGraph.exists_not_adj_of_E_lt _ h
  exact CGraph.diameter_join_of_not_adj _ _ hne hadj

/-- A join whose right factor is not complete has diameter two. -/
theorem diameter_join_right {G H : IsoGraph} (hG : 0 < G.V) (h : H.E < H.V.choose 2) :
    (G ∇g H).diameter = 2 := by
  rw [join_comm]
  exact diameter_join_left hG h

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

/-- **The complement of a disconnected graph is connected.** -/
theorem isConnected_compl_of_not_isConnected {G : IsoGraph} (hV : 0 < G.V)
    (h : ¬ IsConnected G) : IsConnected Gᶜ := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at hV
  rw [isConnected_mk] at h
  rw [compl_mk, isConnected_mk]
  haveI := Fintype.card_pos_iff.1 hV
  exact CGraph.isConnected_compl_of_not_preconnected _ fun hp ↦ h ⟨hp⟩

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
  haveI := Fintype.card_pos_iff.1 hV
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
  haveI := Fintype.card_pos_iff.1 hV
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

/-- Successor mod `n + 3`, the "next vertex" map along the cycle. -/
private def cyc (n : ℕ) (i : Fin (n + 3)) : Fin (n + 3) :=
  ⟨(i.1 + 1) % (n + 3), Nat.mod_lt _ (by omega)⟩

private theorem cyc_val (n : ℕ) (i : Fin (n + 3)) : (cyc n i).1 = (i.1 + 1) % (n + 3) := rfl

private theorem cyc_ne (n : ℕ) (i : Fin (n + 3)) : cyc n i ≠ i := by
  intro h
  have h1 : (i.1 + 1) % (n + 3) = i.1 := congrArg Fin.val h
  have hi := i.2
  rcases Nat.lt_or_ge (i.1 + 1) (n + 3) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1; omega
  · rw [show i.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega

private theorem cyc_inj (n : ℕ) : Function.Injective (cyc n) := by
  intro i j h
  have h1 : (i.1 + 1) % (n + 3) = (j.1 + 1) % (n + 3) := congrArg Fin.val h
  have hi := i.2
  have hj := j.2
  refine Fin.ext ?_
  rcases Nat.lt_or_ge (i.1 + 1) (n + 3) with h2 | h2 <;>
    rcases Nat.lt_or_ge (j.1 + 1) (n + 3) with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
  · rw [Nat.mod_eq_of_lt h2, show j.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · rw [Nat.mod_eq_of_lt h3, show i.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · omega

/-- Two steps along the cycle never return to where they started — this is the only place
`n ≥ 3` is used, and it is what rules out `L(C₂) = C₂`. -/
private theorem cyc_cyc_ne (n : ℕ) (j : Fin (n + 3)) : cyc n (cyc n j) ≠ j := by
  intro h
  have h1 : ((j.1 + 1) % (n + 3) + 1) % (n + 3) = j.1 := congrArg Fin.val h
  have hj := j.2
  rcases Nat.lt_or_ge (j.1 + 1) (n + 3) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1
    rcases Nat.lt_or_ge (j.1 + 1 + 1) (n + 3) with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h1; omega
    · rw [show j.1 + 1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · rw [show j.1 + 1 = n + 3 by omega, Nat.mod_self,
      Nat.mod_eq_of_lt (by omega : 0 + 1 < n + 3)] at h1
    omega

/-- Cycle adjacency in terms of `cyc`. -/
private theorem cycle_adj_cyc (n : ℕ) (i j : Fin (n + 3)) :
    (CGraph.cycle (n + 3)).Adj i j = decide (i ≠ j ∧ (cyc n i = j ∨ cyc n j = i)) := by
  have key : ∀ a b : Fin (n + 3), ((a.1 + 1) % (n + 3) == b.1) = decide (cyc n a = b) := by
    intro a b
    rw [Bool.beq_eq_decide_eq]
    exact decide_eq_decide.2 (by rw [Fin.ext_iff, cyc_val])
  show (decide (i ≠ j) && (((i.1 + 1) % (n + 3) == j.1) || ((j.1 + 1) % (n + 3) == i.1))) = _
  rw [key i j, key j i, Bool.decide_and, Bool.decide_or]

private theorem cyc_adj (n : ℕ) (i : Fin (n + 3)) :
    s(i, cyc n i) ∈ (CGraph.cycle (n + 3)).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, cycle_adj_cyc]
  exact decide_eq_true ⟨Ne.symm (cyc_ne n i), Or.inl rfl⟩

/-- The edge of `Cₙ` running from `i` to its successor.  Every edge is of this form, so this is
the bijection `Fin n ≃ E(Cₙ)` witnessing `L(Cₙ) = Cₙ`. -/
private def cycEdge (n : ℕ) (i : Fin (n + 3)) : (CGraph.lineGraph (CGraph.cycle (n + 3))).V :=
  ⟨s(i, cyc n i), cyc_adj n i⟩

private theorem mem_cycEdge (n : ℕ) (v i : Fin (n + 3)) :
    v ∈ ((cycEdge n i).1 : Sym2 (Fin (n + 3))) ↔ v = i ∨ v = cyc n i := Sym2.mem_iff

private theorem cycEdge_inj (n : ℕ) : Function.Injective (cycEdge n) := by
  intro i j h
  have h1 : s(i, cyc n i) = s(j, cyc n j) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
  · exact h2
  · exact absurd (h2 ▸ h3) (cyc_cyc_ne n j)

/-- **The cycle is its own line graph**, for `n ≥ 3`.  The edges of `Cₙ` are the consecutive pairs
`{i, i+1}`, and two of them share a vertex exactly when their indices are consecutive.  Injectivity
is where `n ≥ 3` enters: for `n = 2` the two "edges" `{0, 1}` and `{1, 0}` coincide. -/
@[simp] theorem lineGraph_cycle (n : ℕ) : lineGraph (cycle (n + 3)) = cycle (n + 3) := by
  have hcard : Fintype.card (Fin (n + 3))
      = Fintype.card (CGraph.lineGraph (CGraph.cycle (n + 3))).V := by
    rw [CGraph.card_lineGraph, CGraph.E_cycle, Fintype.card_fin]
  have hbij : Function.Bijective (cycEdge n) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨cycEdge_inj n, hcard⟩
  have hadj : ∀ i j : Fin (n + 3),
      (CGraph.lineGraph (CGraph.cycle (n + 3))).Adj (cycEdge n i) (cycEdge n j)
        = (CGraph.cycle (n + 3)).Adj i j := by
    intro i j
    rw [CGraph.lineGraph_adj, cycle_adj_cyc]
    by_cases hij : i = j
    · subst hij; simp
    · rw [decide_eq_true (show cycEdge n i ≠ cycEdge n j from fun h ↦ hij (cycEdge_inj n h)),
        Bool.true_and, Bool.decide_and, decide_eq_true hij, Bool.true_and]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_cycEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
        · exact absurd (h1.symm.trans h2) hij
        · exact Or.inr (h2.symm.trans h1)
        · exact Or.inl (h1.symm.trans h2)
        · exact absurd (cyc_inj n (h1.symm.trans h2)) hij
      · rintro (h | h)
        · exact ⟨j, (mem_cycEdge n j i).2 (Or.inr h.symm), (mem_cycEdge n j j).2 (Or.inl rfl)⟩
        · exact ⟨i, (mem_cycEdge n i i).2 (Or.inl rfl), (mem_cycEdge n i j).2 (Or.inr h.symm)⟩
  rw [cycle_def, lineGraph_mk]
  exact Quotient.sound ⟨(CGraph.isoOfAdj (Equiv.ofBijective (cycEdge n) hbij) hadj).symm⟩

/-- Path adjacency at the level of the underlying naturals.  Note that `i ≠ j` is implied by
either disjunct, so it drops out. -/
private theorem path_adj_val (n : ℕ) (i j : Fin n) :
    (CGraph.path n).Adj i j = decide (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  show (decide (i ≠ j) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) = _
  by_cases h : i = j
  · subst h; simp
  · rw [decide_eq_true h, Bool.true_and, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq,
      ← Bool.decide_or]

private theorem pathEdge_adj (n : ℕ) (i : Fin n) :
    s(i.castSucc, i.succ) ∈ (CGraph.path (n + 1)).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, path_adj_val]
  exact decide_eq_true (Or.inl (by simp))

/-- The `i`-th edge of the path `0 — 1 — ⋯ — n`. -/
private def pathEdge (n : ℕ) (i : Fin n) : (CGraph.lineGraph (CGraph.path (n + 1))).V :=
  ⟨s(i.castSucc, i.succ), pathEdge_adj n i⟩

private theorem mem_pathEdge (n : ℕ) (v : Fin (n + 1)) (i : Fin n) :
    v ∈ ((pathEdge n i).1 : Sym2 (Fin (n + 1))) ↔ v = i.castSucc ∨ v = i.succ := Sym2.mem_iff

private theorem pathEdge_inj (n : ℕ) : Function.Injective (pathEdge n) := by
  intro i j h
  have h1 : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
  · exact Fin.ext (by simpa using congrArg Fin.val h2)
  · have hv2 := congrArg Fin.val h2
    have hv3 := congrArg Fin.val h3
    simp only [Fin.val_castSucc, Fin.val_succ] at hv2 hv3
    omega

/-- **The line graph of a path is the shorter path**: `L(Pₙ₊₁) = Pₙ`.  Unlike the cycle this needs
no size hypothesis — `L(P₁) = P₀` is the empty graph. -/
@[simp] theorem lineGraph_path (n : ℕ) : lineGraph (path (n + 1)) = path n := by
  have hcard : Fintype.card (Fin n)
      = Fintype.card (CGraph.lineGraph (CGraph.path (n + 1))).V := by
    rw [CGraph.card_lineGraph, CGraph.E_path, Fintype.card_fin]
  have hbij : Function.Bijective (pathEdge n) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨pathEdge_inj n, hcard⟩
  have hadj : ∀ i j : Fin n,
      (CGraph.lineGraph (CGraph.path (n + 1))).Adj (pathEdge n i) (pathEdge n j)
        = (CGraph.path n).Adj i j := by
    intro i j
    rw [CGraph.lineGraph_adj, path_adj_val]
    by_cases hij : i = j
    · subst hij; simp
    · have hval : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
      rw [decide_eq_true (show pathEdge n i ≠ pathEdge n j from fun h ↦ hij (pathEdge_inj n h)),
        Bool.true_and]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_pathEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2 <;>
          · have h3 := congrArg Fin.val (h1.symm.trans h2)
            simp only [Fin.val_castSucc, Fin.val_succ] at h3
            omega
      · rintro (h | h)
        · exact ⟨i.succ, (mem_pathEdge n _ i).2 (Or.inr rfl),
            (mem_pathEdge n _ j).2 (Or.inl (Fin.ext (by simpa using h)))⟩
        · exact ⟨i.castSucc, (mem_pathEdge n _ i).2 (Or.inl rfl),
            (mem_pathEdge n _ j).2 (Or.inr (Fin.ext (by simpa using h.symm)))⟩
  rw [path_def, lineGraph_mk]
  exact Quotient.sound ⟨(CGraph.isoOfAdj (Equiv.ofBijective (pathEdge n) hbij) hadj).symm⟩

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
@[simp] theorem lineGraph_bipartite (m n : ℕ) : lineGraph (bipartite m n) = rook m n := by
  have hcard : Fintype.card (Fin m × Fin n)
      = Fintype.card (CGraph.lineGraph (CGraph.bipartite m n)).V := by
    rw [CGraph.card_lineGraph, CGraph.E_bipartite, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have hbij : Function.Bijective (bipartiteEdge m n) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨bipartiteEdge_inj m n, hcard⟩
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
  have hrook : (rook m n : IsoGraph) = ⟦CGraph.rook m n⟧ := by
    rw [show (rook m n : IsoGraph) = complete m □g complete n from rfl,
      complete_def, complete_def, cartesianProduct_mk]
  rw [bipartite_def, lineGraph_mk, hrook]
  exact Quotient.sound ⟨(CGraph.isoOfAdj (Equiv.ofBijective (bipartiteEdge m n) hbij) hadj).symm⟩

@[simp] theorem mycielskian_empty_zero : mycielskian (empty 0) = empty 1 := by
  have h : ∀ x y : (CGraph.mycielskian (CGraph.empty 0)).V,
      (CGraph.mycielskian (CGraph.empty 0)).Adj x y = false := by
    haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
    rintro (_ | (a | a)) (_ | (b | b)) <;> first | rfl | exact isEmptyElim a | exact isEmptyElim b
  rw [empty_def, mycielskian_mk, mk_eq_empty h]
  simp

/-- Relabelling for `mycielskian_empty`: the apex becomes the centre of the star, the shadow
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
theorem mycielskian_empty (n : ℕ) :
    mycielskian (empty n) = star n ⊕g empty n := by
  rw [empty_def, mycielskian_mk, star_def, disjUnion_mk]
  refine Quotient.sound ⟨(CGraph.isoOfAdj
    (G := CGraph.disjUnion (CGraph.star n) (CGraph.empty n))
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
        simp [CGraph.star])).symm⟩

/-- **The Mycielskian of `K₂` is the 5-cycle**: two vertices, their two shadows and the apex,
strung together as `u₀ — u₁ — w₀ — z — w₁ — u₀`. -/
theorem mycielskian_complete_two : mycielskian (complete 2) = cycle 5 := by
  rw [complete_def, mycielskian_mk, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.mycielskian (CGraph.complete 2)) (H := CGraph.cycle 5)
    (⟨fun x ↦ match x with
        | none => 3
        | some (.inl a) => if a = 0 then 0 else 1
        | some (.inr a) => if a = 0 then 2 else 4,
      ![some (.inl 0), some (.inl 1), some (.inr 0), none, some (.inr 1)],
      by decide, by decide⟩ : Option (Fin 2 ⊕ Fin 2) ≃ Fin 5)
    (by decide)⟩

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

/-! ### Degree multisets

`degSequence` is a sorted list, which makes it awkward to combine: the degree sequence of a
disjoint union is a *merge* of the two sequences, not a concatenation.  The underlying multiset
`degMultiset` has no such problem, and since `degSequence` is literally its `sort`
(`coe_degSequence`) nothing is lost by working with it. -/

@[simp] theorem card_degMultiset (G : IsoGraph) : Multiset.card (degMultiset G) = G.V := by
  rw [← coe_degSequence, Multiset.coe_card, length_degSequence]

/-- The handshake lemma, for the degree multiset. -/
theorem sum_degMultiset (G : IsoGraph) : (degMultiset G).sum = 2 * G.E := by
  rw [← coe_degSequence, Multiset.sum_coe, sum_degSequence]

theorem ne_of_degMultiset_ne {G H : IsoGraph} (h : degMultiset G ≠ degMultiset H) : G ≠ H :=
  ne_of_apply_ne degMultiset h

/-- Reading a degree multiset off a constant degree sequence. -/
theorem degMultiset_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : degMultiset G = Multiset.replicate n k := by
  rw [← coe_degSequence, h, Multiset.coe_replicate]

attribute [simp] IsoGraph.degMultiset_disjUnion

@[simp] theorem degMultiset_join (G H : IsoGraph) :
    degMultiset (G ∇g H) = (degMultiset G).map (· + H.V) + (degMultiset H).map (· + G.V) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, degMultiset_mk, degMultiset_mk,
    degMultiset_mk, V_mk, V_mk]
  exact CGraph.degMultiset_join _ _

@[simp] theorem degMultiset_compl (G : IsoGraph) :
    degMultiset Gᶜ = (degMultiset G).map (fun d ↦ G.V - 1 - d) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, degMultiset_mk, degMultiset_mk, V_mk]
  exact CGraph.degMultiset_compl _

/-! ### Degree multisets of the named graphs -/

@[simp] theorem degMultiset_empty (n : ℕ) : degMultiset (empty n) = Multiset.replicate n 0 :=
  degMultiset_of_degSequence (degSequence_empty n)

@[simp] theorem degMultiset_complete (n : ℕ) :
    degMultiset (complete n) = Multiset.replicate n (n - 1) :=
  degMultiset_of_degSequence (degSequence_complete n)

@[simp] theorem degMultiset_cycle (n : ℕ) :
    degMultiset (cycle (n + 3)) = Multiset.replicate (n + 3) 2 :=
  degMultiset_of_degSequence (degSequence_cycle n)

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

/-! ### The degrees of a path

The path is the first named graph whose degrees are not all equal, so it is the first whose degree
multiset needs `degMultiset_path` rather than the strong-regularity machinery.  Sorting the
resulting multiset is easy enough that the degree *sequence* comes out too. -/

@[simp] theorem degMultiset_path (n : ℕ) :
    degMultiset (path (n + 2)) = 1 ::ₘ 1 ::ₘ Multiset.replicate n 2 := by
  rw [degMultiset_path_eq]
  set g : ℕ → ℕ := fun k ↦ (if k + 1 < n + 2 then 1 else 0) + (if 0 < k then 1 else 0) with hg
  have hmid : ∀ m, m ≤ n → (Multiset.range (m + 1)).map g = 1 ::ₘ Multiset.replicate m 2 := by
    intro m
    induction m with
    | zero => intro _; simp [hg]
    | succ p ih =>
      intro hp
      have hgp : g (p + 1) = 2 := by simp only [hg]; split_ifs <;> omega
      rw [Multiset.range_succ, Multiset.map_cons, ih (by omega), hgp, Multiset.cons_swap,
        ← Multiset.replicate_succ]
  have hgn : g (n + 1) = 1 := by simp only [hg]; split_ifs <;> omega
  rw [Multiset.range_succ, Multiset.map_cons, hmid n le_rfl, hgn]

/-- Sorting a multiset whose sorted form we can guess. -/
private theorem sort_eq_of_pairwise {s : Multiset ℕ} {l : List ℕ} (hl : l.Pairwise (· ≤ ·))
    (h : (l : Multiset ℕ) = s) : s.sort (· ≤ ·) = l :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba ↦ le_antisymm hab hba)
    (Multiset.pairwise_sort s (· ≤ ·)) hl
    (Multiset.coe_eq_coe.mp (by rw [Multiset.sort_eq, h]))

@[simp] theorem degSequence_path (n : ℕ) :
    degSequence (path (n + 2)) = 1 :: 1 :: List.replicate n 2 := by
  rw [degSequence_eq_sort]
  refine sort_eq_of_pairwise ?_ ?_
  · simp [List.pairwise_cons, List.mem_replicate]
  · rw [degMultiset_path]
    rfl

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

/-! ### Degree multisets of the four products

The vertex set of a product is a product, so its degree multiset is a `Multiset.bind`: run over
the degrees of the left factor, and for each of them map the degrees of the right factor through
whatever the product does to a pair of degrees. -/

@[simp] theorem degMultiset_cartesianProduct (G H : IsoGraph) :
    degMultiset (G □g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d + e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_cartesianProduct _ _

@[simp] theorem degMultiset_tensorProduct (G H : IsoGraph) :
    degMultiset (G ⊗g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d * e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_tensorProduct _ _

@[simp] theorem degMultiset_lexProduct (G H : IsoGraph) :
    degMultiset (G ·g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d * H.V + e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk, V_mk]
  exact CGraph.degMultiset_lexProduct _ _

@[simp] theorem degMultiset_strongProduct (G H : IsoGraph) :
    degMultiset (G ⊠g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ (d + 1) * (e + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_strongProduct _ _

/-! ### The chromatic number of an `IsoGraph` -/

attribute [simp] IsoGraph.chromNum_eq_zero_iff

/-- Two graphs with different chromatic numbers are different graphs. -/
theorem ne_of_chromNum_ne {G H : IsoGraph} (h : G.chromNum ≠ H.chromNum) : G ≠ H :=
  ne_of_apply_ne chromNum h

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

/-! ### The chromatic number of a join and of the products -/

/-- **The chromatic numbers of a join add.** -/
@[simp] theorem chromNum_join (G H : IsoGraph) :
    (G ∇g H).chromNum = G.chromNum + H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, chromNum_mk, chromNum_mk, chromNum_mk]
  exact CGraph.chromNum_join _ _

/-- **Sabidussi's theorem** for the cartesian product. -/
theorem chromNum_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G □g H).chromNum = max G.chromNum H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, chromNum_mk, chromNum_mk, chromNum_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.chromNum_cartesianProduct _ _ a b

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

/-! ### The Mycielskian and the Kneser bound -/

/-- **Mycielski's construction raises the chromatic number by exactly one.** -/
@[simp] theorem chromNum_mycielskian (G : IsoGraph) :
    (mycielskian G).chromNum = G.chromNum + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, chromNum_mk, chromNum_mk]
  exact CGraph.chromNum_mycielskian _

/-- **The Petersen graph is 3-chromatic**: the Kneser bound gives three colours, and it is not
bipartite. -/
@[simp] theorem chromNum_petersen : petersen.chromNum = 3 :=
  le_antisymm (chromNum_kneser_le 5 2 (by norm_num)) (three_le_chromNum not_isBipartite_petersen)

/-- **Nordhaus–Gaddum, product form**: `|V| ≤ χ(G)·χ(Gᶜ)`, since an independent set of `G` is a
clique of `Gᶜ`. -/
theorem V_le_chromNum_mul_chromNum_compl (G : IsoGraph) :
    G.V ≤ G.chromNum * Gᶜ.chromNum :=
  le_trans (V_le_chromNum_mul_indepNum G)
    (Nat.mul_le_mul_left _ (by rw [← cliqueNum_compl]; exact cliqueNum_le_chromNum _))

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

/-! ### Girth -/

theorem one_le_cliqueNum {G : IsoGraph} (h : 0 < G.V) : 1 ≤ G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [V_mk] at h
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 h
  exact CGraph.one_le_cliqueNum_of_vertex a

theorem ne_of_girth_ne {G H : IsoGraph} (h : G.girth ≠ H.girth) : G ≠ H := fun hgh ↦ h (hgh ▸ rfl)

/-! ### Girth of the named graphs -/

@[simp] theorem girth_empty (n : ℕ) : (empty n).girth = 0 := girth_eq_zero_iff.2 (isAcyclic_empty n)

@[simp] theorem girth_path (n : ℕ) : (path n).girth = 0 := girth_eq_zero_iff.2 (isAcyclic_path n)

@[simp] theorem girth_star (n : ℕ) : (star n).girth = 0 :=
  girth_eq_zero_iff.2 ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_star n)).2

@[simp] theorem girth_complete (n : ℕ) : (complete (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

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

/-! ### Maximum and minimum degree -/

/-! ### Basic API -/

theorem maxDeg_lt_V {G : IsoGraph} (h : 0 < G.V) : maxDeg G < G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at h ⊢
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 h
  exact CGraph.maxDeg_lt_card _ v

theorem maxDeg_le_of_degMultiset {G : IsoGraph} {k : ℕ} (h : ∀ d ∈ degMultiset G, d ≤ k) :
    maxDeg G ≤ k := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.maxDeg_le_of_forall fun v ↦ h _ (CGraph.mem_degMultiset.2 ⟨v, rfl⟩)

/-- A regular graph, read off its degree multiset: both extremes are the common degree. -/
theorem maxDeg_of_degMultiset_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degMultiset G = Multiset.replicate n k) : maxDeg G = k :=
  maxDeg_eq_of_degMultiset (h ▸ Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)
    fun _ hd ↦ le_of_eq (Multiset.eq_of_mem_replicate (h ▸ hd))

theorem minDeg_of_degMultiset_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degMultiset G = Multiset.replicate n k) : minDeg G = k :=
  minDeg_eq_of_degMultiset (h ▸ Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)
    fun _ hd ↦ ge_of_eq (Multiset.eq_of_mem_replicate (h ▸ hd))

/-- **`Δ ≤ 2|E|`**: an edgeless graph has maximum degree `0`. -/
theorem maxDeg_le_two_mul_E {G : IsoGraph} (hG : 0 < G.V) : maxDeg G ≤ 2 * G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [V_mk] at hG
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hG
  rw [maxDeg_mk, E_mk]
  exact g.maxDeg_le_two_mul_E v

theorem ne_of_maxDeg_ne {G H : IsoGraph} (h : maxDeg G ≠ maxDeg H) : G ≠ H :=
  ne_of_apply_ne maxDeg h

theorem ne_of_minDeg_ne {G H : IsoGraph} (h : minDeg G ≠ minDeg H) : G ≠ H :=
  ne_of_apply_ne minDeg h

/-! ### The disjoint union, the join and the complement -/

attribute [simp] IsoGraph.maxDeg_disjUnion

theorem minDeg_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (G ⊕g H) = min (minDeg G) (minDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [disjUnion_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_disjUnion _ _ a b

theorem maxDeg_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (G ∇g H) = max (maxDeg G + H.V) (G.V + maxDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk, V_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_join _ _ a b

theorem minDeg_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (G ∇g H) = min (minDeg G + H.V) (G.V + minDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, minDeg_mk, minDeg_mk, minDeg_mk, V_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_join _ _ a b

/-- **Complementation swaps the two extreme degrees.** -/
theorem maxDeg_compl {G : IsoGraph} (hG : 0 < G.V) :
    maxDeg Gᶜ = G.V - 1 - minDeg G := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [compl_mk, maxDeg_mk, minDeg_mk, V_mk]
  rw [V_mk] at hG
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hG
  exact CGraph.maxDeg_compl _ v

theorem minDeg_compl {G : IsoGraph} (hG : 0 < G.V) :
    minDeg Gᶜ = G.V - 1 - maxDeg G := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [compl_mk, minDeg_mk, maxDeg_mk, V_mk]
  rw [V_mk] at hG
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hG
  exact CGraph.minDeg_compl _ v

/-! ### The four products -/

theorem maxDeg_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (G □g H) = maxDeg G + maxDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_cartesianProduct _ _ a b

theorem minDeg_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (G □g H) = minDeg G + minDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_cartesianProduct _ _ a b

theorem maxDeg_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (G ⊗g H) = maxDeg G * maxDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_tensorProduct _ _ a b

theorem minDeg_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (G ⊗g H) = minDeg G * minDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_tensorProduct _ _ a b

theorem maxDeg_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (G ·g H) = maxDeg G * H.V + maxDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_lexProduct _ _ a b

theorem minDeg_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (G ·g H) = minDeg G * H.V + minDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_lexProduct _ _ a b

theorem maxDeg_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (G ⊠g H) = (maxDeg G + 1) * (maxDeg H + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_strongProduct _ _ a b

theorem minDeg_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (G ⊠g H) = (minDeg G + 1) * (minDeg H + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_strongProduct _ _ a b

/-! ### The named graphs -/

@[simp] theorem maxDeg_empty (n : ℕ) : maxDeg (empty n) = 0 :=
  Nat.le_zero.1 (maxDeg_le_of_degMultiset fun d hd ↦ by
    rw [degMultiset_empty] at hd
    exact le_of_eq (Multiset.eq_of_mem_replicate hd))

@[simp] theorem minDeg_empty (n : ℕ) : minDeg (empty n) = 0 :=
  Nat.le_zero.1 (le_trans (minDeg_le_maxDeg _) (le_of_eq (maxDeg_empty n)))

@[simp] theorem maxDeg_complete (n : ℕ) : maxDeg (complete n) = n - 1 := by
  cases n with
  | zero =>
    refine Nat.le_zero.1 (maxDeg_le_of_degMultiset fun d hd ↦ ?_)
    rw [degMultiset_complete] at hd
    exact le_of_eq (Multiset.eq_of_mem_replicate hd)
  | succ m => exact maxDeg_of_degMultiset_replicate (n := m + 1) (Nat.succ_pos m) (by simp)

@[simp] theorem minDeg_complete (n : ℕ) : minDeg (complete n) = n - 1 := by
  cases n with
  | zero => exact Nat.le_zero.1 (le_trans (minDeg_le_maxDeg _) (by simp))
  | succ m => exact minDeg_of_degMultiset_replicate (n := m + 1) (Nat.succ_pos m) (by simp)

@[simp] theorem maxDeg_cycle (n : ℕ) : maxDeg (cycle (n + 3)) = 2 :=
  maxDeg_of_degMultiset_replicate (n := n + 3) (by omega) (by simp)

@[simp] theorem minDeg_cycle (n : ℕ) : minDeg (cycle (n + 3)) = 2 :=
  minDeg_of_degMultiset_replicate (n := n + 3) (by omega) (by simp)

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

@[simp] theorem maxDeg_path (n : ℕ) : maxDeg (path (n + 3)) = 2 := by
  refine maxDeg_eq_of_degMultiset ?_ fun d hd ↦ ?_
  · rw [show n + 3 = (n + 1) + 2 from rfl, degMultiset_path]
    simp
  · rw [show n + 3 = (n + 1) + 2 from rfl, degMultiset_path] at hd
    rcases Multiset.mem_cons.1 hd with h | h
    · omega
    rcases Multiset.mem_cons.1 h with h | h
    · omega
    · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem minDeg_path (n : ℕ) : minDeg (path (n + 2)) = 1 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_path] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  rcases Multiset.mem_cons.1 h with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

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

/-! ### Greedy colouring and Nordhaus–Gaddum -/

/-! ### Greedy colouring -/

/-- A `k`-chromatic graph has a vertex of degree at least `k - 1`. -/
theorem chromNum_sub_one_le_maxDeg (G : IsoGraph) : G.chromNum - 1 ≤ G.maxDeg := by
  have := G.chromNum_le_maxDeg_add_one
  omega

/-- **Nordhaus–Gaddum, sum form**: `4·|V| ≤ (χ(G) + χ(Gᶜ))²`, i.e. `χ(G) + χ(Gᶜ) ≥ 2√|V|`.
This is the product form together with `4ab ≤ (a + b)²`. -/
theorem four_mul_V_le_chromNum_add_chromNum_compl_sq (G : IsoGraph) :
    4 * G.V ≤ (G.chromNum + Gᶜ.chromNum) ^ 2 := by
  have h := V_le_chromNum_mul_chromNum_compl G
  nlinarith [sq_nonneg (G.chromNum - Gᶜ.chromNum : ℤ)]

/-- The product counterpart of the sum bound, by AM–GM: `4·χ(G)·χ(Gᶜ) ≤ (|V| + 1)²`. -/
theorem four_mul_chromNum_mul_chromNum_compl_le (G : IsoGraph) :
    4 * (G.chromNum * Gᶜ.chromNum) ≤ (G.V + 1) ^ 2 := by
  have h := G.chromNum_add_chromNum_compl_le_V_add_one
  nlinarith [sq_nonneg (G.chromNum - Gᶜ.chromNum : ℤ)]

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

end IsoGraph
