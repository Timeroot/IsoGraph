import IsoGraph.SmallGraphs.TuranGraphs

/-!
# The Grötzsch graph and its neighbours

The Grötzsch graph, the Möbius ladders and the Paley graphs.
-/

namespace IsoGraph

/-! ### The Grötzsch graph

The Mycielskian of the pentagon: eleven vertices, twenty edges, no triangle, and four colours
needed.  It is the smallest triangle-free graph with chromatic number four, so it is the first
interesting output of `exists_cliqueNum_le_two_and_le_chromNum`. -/

/-- The **Grötzsch graph**, the Mycielskian of the pentagon. -/
abbrev grotzsch : IsoGraph := mycielskian (cycle 5)

@[simp] theorem V_grotzsch : grotzsch.V = 11 := by
  rw [grotzsch, V_mycielskian, V_cycle]

@[simp] theorem E_grotzsch : grotzsch.E = 20 := by
  rw [grotzsch, E_mycielskian, E_cycle, V_cycle]

/-- **Grötzsch's graph needs four colours**: the pentagon needs three and the Mycielskian adds
one. -/
@[simp] theorem chromNum_grotzsch : grotzsch.chromNum = 4 := by
  rw [grotzsch, chromNum_mycielskian, show (5 : ℕ) = 2 * 1 + 3 from rfl, chromNum_cycle_odd]

/-- **Grötzsch's graph is triangle free**: the Mycielskian never creates a triangle out of a
pentagon. -/
@[simp] theorem cliqueNum_grotzsch : grotzsch.cliqueNum = 2 := by
  refine cliqueNum_mycielskian_eq_two ?_ ?_
  · rw [V_cycle]; omega
  · rw [show (5 : ℕ) = 1 + 4 from rfl, cliqueNum_cycle]

@[simp] theorem not_isBipartite_grotzsch : ¬ IsBipartite grotzsch := by
  rw [isBipartite_iff_chromNum_le_two, chromNum_grotzsch]
  omega

/-- The Grötzsch graph is not the Petersen graph: they have different orders. -/
theorem grotzsch_ne_petersen : grotzsch ≠ petersen := by
  intro h
  have := congrArg IsoGraph.V h
  rw [V_grotzsch, V_petersen] at this
  omega

end IsoGraph

namespace CGraph

/-- The two-rung Möbius ladder is `K₄`: the square plus both diagonals. -/
@[toIsoGraph]
theorem circulant_four_one_two : circulant 4 [1, 2] = complete 4 :=
  ext' rfl (heq_of_eq (by decide))

/-- The three-rung Möbius ladder is `K_{3,3}`: the hexagon's odd differences are exactly `1`,
`3` and `5`, so every even vertex meets every odd one. -/
@[toIsoGraph circulant_six_one_three]
def circulantSixOneThree : circulant 6 [1, 3] ≃cg bipartite 3 3 :=
  isoOfAdj
    (⟨![.inl 0, .inr 0, .inl 1, .inr 1, .inl 2, .inr 2],
      Sum.elim ![0, 2, 4] ![1, 3, 5], by decide, by decide⟩ : Fin 6 ≃ (Fin 3 ⊕ Fin 3))
    (by decide)

end CGraph

namespace IsoGraph

/-- The three-rung Möbius ladder is bipartite, unlike every other one. -/
@[simp] theorem isBipartite_circulant_six_one_three : IsBipartite (circulant 6 [1, 3]) := by
  rw [circulant_six_one_three]
  exact isBipartite_bipartite 3 3

/-- A vertex of a Turán graph misses exactly its own part, so the degree sequence takes two
values: the `n % r` big parts contribute the small degree and the rest the large one. -/
theorem degSequence_turan {n r : ℕ} (hr : 0 < r) :
    degSequence (turan n r)
      = List.replicate (n % r * (n / r + 1)) (n - n / r - 1)
          ++ List.replicate ((r - n % r) * (n / r)) (n - n / r) := by
  set m := n % r with hm_def
  set k := n / r with hk_def
  have hm_lt : m < r := Nat.mod_lt n hr
  have hsum_n : n = r * k + m := by rw [hk_def, hm_def, Nat.div_add_mod]
  -- turan = join of two completeMultipartite(replicate ...) graphs
  have hturan : turan n r = completeMultipartite (List.replicate m (k + 1)) ∇g
      completeMultipartite (List.replicate (r - m) k) := by
    rw [turan, completeMultipartite_append]
  rw [hturan, degSequence_eq_sort, degMultiset_join]
  -- Compute degMultiset of each chunk via degMultiset_of_degSequence
  have hdseq1 : degSequence (completeMultipartite (List.replicate m (k + 1))) =
      List.replicate (m * (k + 1)) ((m - 1) * (k + 1)) :=
    degSequence_completeMultipartite_replicate m (k + 1)
  have hdseq2 : degSequence (completeMultipartite (List.replicate (r - m) k)) =
      List.replicate ((r - m) * k) ((r - m - 1) * k) :=
    degSequence_completeMultipartite_replicate (r - m) k
  have hdmm1 : degMultiset (completeMultipartite (List.replicate m (k + 1))) =
      Multiset.replicate (m * (k + 1)) ((m - 1) * (k + 1)) :=
    degMultiset_of_degSequence hdseq1
  have hdmm2 : degMultiset (completeMultipartite (List.replicate (r - m) k)) =
      Multiset.replicate ((r - m) * k) ((r - m - 1) * k) :=
    degMultiset_of_degSequence hdseq2
  rw [hdmm1, hdmm2, V_completeMultipartite_replicate, V_completeMultipartite_replicate]
  simp only [Multiset.map_replicate]
  have hr_gt_m : r > m := hm_lt
  have hrep1 : Multiset.replicate (m * (k + 1)) ((m - 1) * (k + 1) + (r - m) * k) =
      Multiset.replicate (m * (k + 1)) (n - k - 1) := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hval : (m - 1) * (k + 1) + (r - m) * k + (k + 1) = n := by
        have h1 : (m - 1) + 1 = m := Nat.sub_add_cancel hmpos
        have h2 : (m - 1) * (k + 1) + (k + 1) = m * (k + 1) := by
          rw [show (m - 1) * (k + 1) + (k + 1) = ((m - 1) + 1) * (k + 1) from by ring, h1]
        rw [show (m - 1) * (k + 1) + (r - m) * k + (k + 1) =
            ((m - 1) * (k + 1) + (k + 1)) + (r - m) * k from by ring, h2]
        have hthis : m * (k + 1) + (r - m) * k = r * k + m := by
          have hsub : (r - m) + m = r := Nat.sub_add_cancel (le_of_lt hr_gt_m)
          rw [show m * (k + 1) + (r - m) * k = m * k + m + (r - m) * k from by ring]
          have : r * k + m = ((r - m) + m) * k + m := by rw [hsub]
          rw [this]; ring
        rw [hthis, hsum_n]
      have : (m - 1) * (k + 1) + (r - m) * k = n - (k + 1) := by
        exact Nat.eq_sub_of_add_eq hval
      rw [this]; simp [Nat.sub_sub]
  have hrep2 : Multiset.replicate ((r - m) * k) ((r - m - 1) * k + m * (k + 1)) =
      Multiset.replicate ((r - m) * k) (n - k) := by
    have hval : (r - m - 1) * k + m * (k + 1) + k = n := by
      have h1 : (r - m - 1) + 1 = r - m := Nat.sub_add_cancel (Nat.sub_pos_of_lt hr_gt_m)
      have h2 : (r - m - 1) * k + k = (r - m) * k := by
        rw [show (r - m - 1) * k + k = ((r - m - 1) + 1) * k from by ring, h1]
      rw [show (r - m - 1) * k + m * (k + 1) + k =
          ((r - m - 1) * k + k) + m * (k + 1) from by ring, h2]
      have hthis : (r - m) * k + m * (k + 1) = r * k + m := by
        have hsub : (r - m) + m = r := Nat.sub_add_cancel (le_of_lt hr_gt_m)
        rw [show (r - m) * k + m * (k + 1) = (r - m) * k + m * k + m from by ring]
        have : r * k + m = ((r - m) + m) * k + m := by rw [hsub]
        rw [this]; ring
      rw [hthis, hsum_n]
    have : (r - m - 1) * k + m * (k + 1) = n - k := by
      exact Nat.eq_sub_of_add_eq hval
    rw [this]
  rw [hrep1, hrep2]
  rw [add_comm]
  set a := n - k - 1
  set b := n - k
  set m' := m * (k + 1)
  set l' := List.replicate ((r - m) * k) b
  have hl_pairwise : l'.Pairwise (· ≤ ·) := List.pairwise_replicate.2 (by omega)
  have hle : ∀ x ∈ List.replicate m' a, ∀ b' ∈ l', x ≤ b' := by
    intro x hx b' hb'
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hb']
    omega
  have hsort_perm :
      (Multiset.sort ((l' : Multiset ℕ) + Multiset.replicate m' a) (· ≤ ·) : Multiset ℕ) =
      ((l' : Multiset ℕ) + Multiset.replicate m' a : Multiset ℕ) :=
    Multiset.sort_eq _ _
  have hl_sorted : List.Pairwise (fun x1 x2 => x1 ≤ x2) (List.replicate m' a ++ l') := by
    exact List.pairwise_append.2 ⟨List.pairwise_replicate.2 (by omega), hl_pairwise, hle⟩
  have hperm4 :
      (Multiset.sort ((l' : Multiset ℕ) + Multiset.replicate m' a) (· ≤ ·) : List ℕ).Perm
      (List.replicate m' a ++ l') := by
    have : (l' : Multiset ℕ) + Multiset.replicate m' a =
        (List.replicate m' a ++ l' : Multiset ℕ) := by
      rw [Multiset.add_comm]
      have heq : ∀ x : ℕ, Multiset.count x (Multiset.replicate m' a + ↑l')
          = Multiset.count x (↑(List.replicate m' a ++ l')) := by
        intro x
        simp [Multiset.count_add, Multiset.count_replicate, List.count_append,
          List.count_replicate]
      exact (Multiset.ext (α := ℕ)).mpr heq
    apply Multiset.coe_eq_coe.mp
    rw [hsort_perm, this]
  have hsort_pairwise : List.Pairwise (fun x1 x2 => x1 ≤ x2)
      (Multiset.sort ((l' : Multiset ℕ) + Multiset.replicate m' a) (· ≤ ·)) :=
    Multiset.pairwise_sort _ _
  exact List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => le_antisymm hxy hyx)
    hsort_pairwise hl_sorted hperm4

/-! ### Paley graphs

**Paley graphs are self-complementary**: multiplying by a fixed non-residue is a bijection that
swaps the squares with the non-squares, so it is an isomorphism onto the complement.  The
isomorphism itself is `CGraph.Iso.complPaley`; here it is only lifted to `IsoGraph`. -/

attribute [toIsoGraph simp compl_paley] CGraph.Iso.complPaley

/-- The complement of a Paley graph of prime order is itself. -/
theorem isSelfComplementary_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    IsSelfComplementary (paley q) := compl_paley q hq

end IsoGraph

namespace CGraph

/-- Dropping the diameters from `C₆` leaves the complement of a perfect matching. -/
theorem circulant_six_one_two_eq_compl : circulant 6 [1, 2] = (circulant 6 [3])ᶜ :=
  ext' rfl (heq_of_eq (by decide))

/-- The octahedron as a circulant: the complement of a perfect matching is the three-pair cocktail
party graph. -/
noncomputable def circulantSixOneTwo : circulant 6 [1, 2] ≃cg cocktailParty 3 := by
  rw [circulant_six_one_two_eq_compl, ← compl_compl (cocktailParty 3)]
  exact Iso.compl (complCocktailPartyEqCirculant 2).symm

/-- The triangular prism as a circulant: the even and odd residues each span a triangle and the
diameters match them up. -/
def circulantSixTwoThree : circulant 6 [2, 3] ≃cg prism 3 :=
  isoOfAdj
    (⟨![(0, 0), (2, 1), (1, 0), (0, 1), (2, 0), (1, 1)],
      fun p ↦ ![![0, 3], ![2, 5], ![4, 1]] p.1 p.2, by decide, by decide⟩ :
        Fin 6 ≃ (Fin 3 × Fin 2))
    (by decide)

/-- The three-vertex fan is the two-page book: both are `K₄` with one edge removed. -/
noncomputable def fanThree : fan 3 ≃cg book 2 :=
  (isoOfAdj
    (⟨Sum.elim ![.inl 0] ![.inr 0, .inl 1, .inr 1],
      Sum.elim ![.inl 0, .inr 1] ![.inr 0, .inr 2], by decide, by decide⟩ :
        (Fin 1 ⊕ Fin 3) ≃ (Fin 2 ⊕ Fin 2))
    (by decide) : fan 3 ≃cg complete 2 ∇g empty 2).trans (bookEqJoin 2).symm

end CGraph

namespace IsoGraph

/-- The octahedron as a circulant: dropping the diameters from `C₆` leaves the complement of a
perfect matching, which is the three-pair cocktail party graph. -/
theorem circulant_six_one_two : circulant 6 [1, 2] = cocktailParty 3 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.circulantSixOneTwo⟩

/-- The triangular prism as a circulant: the even and odd residues each span a triangle and the
diameters match them up. -/
theorem circulant_six_two_three : circulant 6 [2, 3] = prism 3 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.circulantSixTwoThree⟩

/-- The three-vertex fan is the two-page book: both are `K₄` with one edge removed. -/
theorem fan_three : fan 3 = book 2 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.fanThree⟩

/-- Covering the triangular graph `T(n)` by cliques is edge colouring `K_n`. -/
theorem cliqueCoverNum_kneser_two_even (m : ℕ) :
    (kneser (2 * m + 4) 2).cliqueCoverNum = 2 * m + 3 := by
  rw [cliqueCoverNum_eq, ← triangular_eq_compl_kneser,
    show triangular (2 * m + 4) = lineGraph (complete (2 * m + 4)) from
      (lineGraph_complete_eq_triangular (2 * m + 4)).symm,
    ← edgeChromNum_eq, edgeChromNum_complete_even_add_four]

@[simp] theorem chromNum_triangular_even (m : ℕ) :
    (triangular (2 * m + 4)).chromNum = 2 * m + 3 := by
  rw [chromNum_triangular, edgeChromNum_complete_even_add_four]

/-- Covering the Kneser graph `K(n, 2)` by cliques is edge colouring `K_n`, since the complement
of `K(n, 2)` is the triangular graph and that is the line graph of `K_n`. -/
theorem cliqueCoverNum_kneser_two (n : ℕ) :
    (kneser n 2).cliqueCoverNum = (complete n).edgeChromNum := by
  rw [cliqueCoverNum_eq, ← triangular_eq_compl_kneser, chromNum_triangular]

theorem edgeChromNum_hypercube (n : ℕ) : (hypercube (n + 1)).edgeChromNum = n + 1 := by
  apply le_antisymm
  · -- Upper bound: edgeChromNum ≤ n+1
    rw [edgeChromNum_eq]
    rw [show lineGraph (hypercube (n + 1)) = ⟦(lineGraph (hypercube (n + 1))).toCGraph⟧ from
      (IsoGraph.mk_toCGraph _).symm]
    rw [chromNum_mk, CGraph.chromNum_le_iff_colorable]
    rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
    -- Work with CGraph.hypercube directly
    have hhc : lineGraph (hypercube (n + 1)) = ⟦CGraph.lineGraph (CGraph.hypercube (n + 1))⟧ := by
      rw [hypercube_def, lineGraph_mk]
    rw [hhc, IsoGraph.toCGraph_mk]
    let V := Fin (n + 1) → Bool
    -- Edge coloring: color edge {x,y} by the unique coordinate where x and y differ.
    let diffSet : V → V → Finset (Fin (n + 1)) := fun x y => Finset.univ.filter (fun i => x i ≠ y i)
    have hdiff_symm : ∀ x y, diffSet x y = diffSet y x := by
      intro x y; ext i; simp [diffSet, ne_comm]
    let colorPair : V → V → Fin (n + 1) := fun x y =>
      if h : (diffSet x y).card = 1 then
        Classical.choose (Finset.card_eq_one.mp h)
      else 0
    have hcolor_symm : ∀ x y : V, colorPair x y = colorPair y x := by
      intro x y; simp [colorPair, hdiff_symm]
    let colorOnEdges : Sym2 V → Fin (n + 1) :=
      Quot.lift (fun p : V × V => colorPair p.1 p.2)
        (fun p q hpq => by
          simp at hpq
          rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact hcolor_symm _ _)
    let C : (CGraph.lineGraph (CGraph.hypercube (n + 1))).V → Fin (n + 1) :=
      fun e => colorOnEdges e.1
    have hcolor_bound : ∀ e : (CGraph.lineGraph (CGraph.hypercube (n + 1))).V,
        (C e : ℕ) < n + 1 := by
      intro e
      show (colorOnEdges e.1 : ℕ) < n + 1
      exact Fin.isLt (colorOnEdges e.1)
    have hcolor_adj : ∀ e f : (CGraph.lineGraph (CGraph.hypercube (n + 1))).V,
        (CGraph.lineGraph (CGraph.hypercube (n + 1))).Adj e f → C e ≠ C f := by
      intro e f hef hCEq
      rw [CGraph.lineGraph_adj] at hef
      simp at hef
      obtain ⟨hne, v, hv_e, hv_f⟩ := hef
      obtain ⟨e_edge, he_mem⟩ := e
      obtain ⟨f_edge, hf_mem⟩ := f
      obtain ⟨⟨u, w⟩, he1⟩ := Sym2.mk_surjective e_edge
      obtain ⟨⟨x, y⟩, hf1⟩ := Sym2.mk_surjective f_edge
      rw [he1.symm] at he_mem; rw [hf1.symm] at hf_mem
      have he_adj : (CGraph.hypercube (n + 1)).Adj u w := by
        simpa [CGraph.toSimple_adj] using he_mem
      have hf_adj : (CGraph.hypercube (n + 1)).Adj x y := by
        simpa [CGraph.toSimple_adj] using hf_mem
      rw [CGraph.hypercube_adj] at he_adj hf_adj
      have he_adj1 : (Finset.univ.filter (fun i => u i ≠ w i)).card = 1 := by simpa using he_adj
      have hf_adj1 : (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 := by simpa using hf_adj
      obtain ⟨ie, hie⟩ := Finset.card_eq_one.mp he_adj1
      obtain ⟨idf, hif⟩ := Finset.card_eq_one.mp hf_adj1
      have hCEq' : colorPair u w = colorPair x y := by
        have : colorOnEdges e_edge = colorOnEdges f_edge := hCEq
        rw [← he1, ← hf1] at this
        exact this
      have huel_ne_wiel : u ie ≠ w ie := by
        by_contra h
        have : ie ∈ ({ie} : Finset (Fin (n+1))) := Finset.mem_singleton_self ie
        rw [← hie] at this
        simp [h] at this
      have hxel_ne_yiel : x idf ≠ y idf := by
        by_contra h
        have : idf ∈ ({idf} : Finset (Fin (n+1))) := Finset.mem_singleton_self idf
        rw [← hif] at this
        simp [h] at this
      have hu_eq_w : ∀ i, i ≠ ie → u i = w i := by
        intro i hi
        by_contra hne'
        have hmem_i : i ∈ ({i | u i ≠ w i} : Finset (Fin (n+1))) := by simp [hne']
        have hi_eq : i = ie := Finset.mem_singleton.mp ((Finset.ext_iff.mp hie i).mp hmem_i)
        exact hi hi_eq
      have hx_eq_y : ∀ i, i ≠ idf → x i = y i := by
        intro i hi
        by_contra hne'
        have hmem_i : i ∈ ({i | x i ≠ y i} : Finset (Fin (n+1))) := by simp [hne']
        have hi_eq : i = idf := Finset.mem_singleton.mp ((Finset.ext_iff.mp hif i).mp hmem_i)
        exact hi hi_eq
      have hwiel : w ie = !u ie := by
        rcases hu_ie : u ie with true | false <;>
        rcases hw_ie : w ie with true | false <;>
        simp [hu_ie, hw_ie] at huel_ne_wiel ⊢
      have hyiel : y idf = !x idf := by
        rcases hx_ie : x idf with true | false <;>
        rcases hy_ie : y idf with true | false <;>
        simp [hx_ie, hy_ie] at hxel_ne_yiel ⊢
      have hw_def : w = Function.update u ie (!u ie) := by
        funext i
        by_cases hi : i = ie
        · subst hi; rw [hwiel, Function.update_self]
        · simp [hi, Function.update_of_ne, hu_eq_w i hi]
      have hy_def : y = Function.update x idf (!x idf) := by
        funext i
        by_cases hi : i = idf
        · subst hi; rw [hyiel, Function.update_self]
        · simp [hi, Function.update_of_ne, hx_eq_y i hi]
      -- hmem_uw and hmem_xy from hv_e, hv_f
      have hv_e' : v ∈ (e_edge : Sym2 (CGraph.hypercube (n + 1)).V) := hv_e
      have hv_f' : v ∈ (f_edge : Sym2 (CGraph.hypercube (n + 1)).V) := hv_f
      rw [← he1] at hv_e'; rw [← hf1] at hv_f'
      have hmem_uw : v = u ∨ v = w := by
        have := Sym2.mem_iff.mp hv_e'
        exact this
      have hmem_xy : v = x ∨ v = y := by
        have := Sym2.mem_iff.mp hv_f'
        exact this
      have hx_when_y : v = y → x = Function.update v idf (!v idf) := by
        intro hvx
        rw [hvx]
        funext i
        by_cases hi : i = idf
        · rw [hi]
          rcases hx_2 : x idf with true | false <;>
          rcases hy_2 : y idf with true | false <;>
          simp [hx_2, hy_2] at hxel_ne_yiel ⊢
        · rw [hx_eq_y i hi, Function.update_of_ne hi]
      have hu_when_w : v = w → u = Function.update v ie (!v ie) := by
        intro hvw
        rw [hvw]
        funext i
        by_cases hi : i = ie
        · rw [hi]
          rcases hu_2 : u ie with true | false <;>
          rcases hw_2 : w ie with true | false <;>
          simp [hu_2, hw_2] at huel_ne_wiel ⊢
        · rw [hu_eq_w i hi, Function.update_of_ne hi]
      have hCEF_uw : colorPair u w = ie := by
        show colorPair u w = ie
        have key : diffSet u w = {ie} := hie
        simp [colorPair, key]
      have hCEF_xy : colorPair x y = idf := by
        show colorPair x y = idf
        have key : diffSet x y = {idf} := hif
        simp [colorPair, key]
      rw [hCEF_uw, hCEF_xy] at hCEq'
      -- hCEq' : ie = idf
      subst hCEq'
      -- Now w = update u ie (!u ie), y = update x ie (!x ie)
      -- Both edges contain v and update v ie (!v ie), so e_edge = f_edge
      -- = s(v, update v ie (!v ie))
      have he1' : e_edge = s(v, Function.update v ie (!v ie)) := by
        rcases hmem_uw with rfl | rfl
        · rw [← he1, hw_def]
        · rw [← he1, hu_when_w rfl]
          exact Sym2.eq_swap
      have hf1' : f_edge = s(v, Function.update v ie (!v ie)) := by
        rcases hmem_xy with rfl | rfl
        · rw [← hf1, hy_def]
        · rw [← hf1, hx_when_y rfl]
          exact Sym2.eq_swap
      have hedge_eq : e_edge = f_edge := by rw [he1', hf1']
      exact hne (Subtype.ext hedge_eq)
    let isoLinG := (CGraph.lineGraph (CGraph.hypercube (n + 1))).isoCanonicalize
    let colorFun : (CGraph.lineGraph (CGraph.hypercube (n + 1))).canonicalize.V → ℕ :=
      fun v => (C (isoLinG.symm v) : ℕ)
    have hcolorFun_valid : ∀ {u v : (CGraph.lineGraph (CGraph.hypercube (n + 1))).canonicalize.V},
        (CGraph.lineGraph (CGraph.hypercube (n + 1))).canonicalize.toSimple.Adj u v →
          colorFun u ≠ colorFun v := by
      intro u v huv
      have hadj : (CGraph.lineGraph (CGraph.hypercube (n + 1))).Adj
          (isoLinG.symm u) (isoLinG.symm v) = true :=
        isoLinG.symm.map_rel_iff.mpr huv
      show (C (isoLinG.symm u) : ℕ) ≠ (C (isoLinG.symm v) : ℕ)
      exact Fin.val_injective.ne (hcolor_adj _ _ hadj)
    refine ⟨⟨colorFun, hcolorFun_valid⟩, fun v => hcolor_bound _⟩
  · -- Lower bound: n+1 ≤ edgeChromNum
    have : 0 < (hypercube (n + 1)).V := by
      rw [V_hypercube]; exact Nat.pos_of_ne_zero (by positivity)
    exact (isRegularWith_hypercube (n + 1)).le_edgeChromNum this

theorem edgeChromNum_wheel (n : ℕ) : (wheel (n + 4)).edgeChromNum = n + 4 := by
  rw [edgeChromNum_eq]
  apply le_antisymm
  · -- Upper bound: chromNum (lineGraph (wheel (n+4))) ≤ n+4
    set m := n + 4 with hm_def
    rw [wheel_def, lineGraph_mk, chromNum_mk]
    have chromNum_le_iff_colorable_local {G : CGraph} {n : ℕ} :
        G.chromNum ≤ n ↔ G.toSimple.Colorable n := CGraph.chromNum_le_iff_colorable
    rw [chromNum_le_iff_colorable_local]
    -- Goal: (CGraph.wheel m).lineGraph.toSimple.Colorable m
    -- Construct an m-coloring of the line graph of wheel(m).
    -- Vertices of lineGraph(wheel(m)) = edges of wheel(m) = Sym2 edges of (Fin 1 ⊕ Fin m).
    -- Hub = inl ⟨0, _⟩. Spoke edge to rim vertex i: {hub, inr i}. Rim edge i: {inr i, inr (i+1)}.
    -- Coloring: spoke i → color i; rim edge i (anchor at i, the "first" endpoint in
    -- cyclic order) → color (i+2) mod m.
    have hm_pos : 0 < m := by omega
    have hm_ge_4 : 4 ≤ m := by omega
    -- Hub vertex
    let hub : Fin 1 ⊕ Fin m := Sum.inl ⟨0, by omega⟩
    -- rimVertex i
    let rim : Fin m → Fin 1 ⊕ Fin m := fun i => Sum.inr i
    -- spoke edge to rim i
    let spokeEdge : Fin m → Sym2 (Fin 1 ⊕ Fin m) := fun i => Sym2.mk (hub, rim i)
    -- rim edge from i to i+1 (canonical orientation)
    let rimEdge : Fin m → Sym2 (Fin 1 ⊕ Fin m) := fun i => Sym2.mk (rim i, rim (i + 1))
    -- Characterize spoke edges as those containing hub
    have spoke_mem : ∀ i : Fin m, hub ∈ spokeEdge i := by
      intro i; simp [spokeEdge, hub, rim]
    have spoke_not_in_rim : ∀ (i : Fin m) (j : Fin m), hub ∈ spokeEdge i → hub ∉ rimEdge j := by
      intro i j _; simp [rimEdge, hub, rim]
    have spoke_ne_rim : ∀ (i j : Fin m), spokeEdge i ≠ rimEdge j := by
      intro i j h
      exact spoke_not_in_rim i j (spoke_mem i) (h ▸ spoke_mem i)
    -- Characterize spoke edge membership of inr
    have inr_mem_spoke : ∀ i : Fin m, rim i ∈ spokeEdge i := by
      intro i; simp [spokeEdge, rim, hub]
    --Hub is in every spoke edge
    --hub ∉ any rim edge (done above)
    -- Edge set of wheel m
    -- spokes are edges
    have spoke_edge_mem : ∀ i : Fin m, spokeEdge i ∈ (CGraph.wheel m).toSimple.edgeSet := by
      intro i
      rw [SimpleGraph.mem_edgeSet]
      show (CGraph.wheel m).Adj hub (rim i)
      change (CGraph.wheel (n + 4)).Adj (Sum.inl ⟨0, by omega⟩) (Sum.inr i)
      dsimp [CGraph.wheel]
      simp [CGraph.join_adj_inl_inr]
    -- rim edges are edges
    have rim_edge_mem : ∀ i : Fin m, rimEdge i ∈ (CGraph.wheel m).toSimple.edgeSet := by
      intro i
      rw [SimpleGraph.mem_edgeSet]
      show (CGraph.wheel m).Adj (rim i) (rim (i + 1))
      change (CGraph.wheel (n + 4)).Adj (Sum.inr i) (Sum.inr (i + 1))
      dsimp [CGraph.wheel, rim]
      simp [CGraph.join_adj_inr_inr, CGraph.cycle_adj_val]
      have hval : (i + 1 : Fin (n + 4)).val = (i.val + 1) % (n + 4) := Fin.val_add i 1
      simp [hval]
      have hlt : (i : ℕ) < n + 4 := by show (i : ℕ) < m; exact i.isLt
      by_cases h : (i : ℕ) + 1 < n + 4
      · rw [Nat.mod_eq_of_lt h]
        omega
      · push_neg at h
        have h2 : (i : ℕ) + 1 = n + 4 := by omega
        rw [h2, Nat.mod_self]
        omega
    -- The goal is to show Colorable m for the line graph of wheel m.
    -- We construct an explicit m-coloring of edges of wheel m.
    -- Colors: spoke to rim i gets color i; rim edge {rim i, rim(i+1)} gets color (i+2) % m.
    -- We define the coloring using spokeEdge and rimEdge maps.
    -- First we need to show every edge is of one of these two forms.
    -- Then we define color on the line graph vertex set.
    -- Then we prove it's a proper coloring.
    -- Hub and rim as Fin 1 ⊕ Fin m
    let fin1_zero : ∀ (x : Fin 1), x = ⟨0, by omega⟩ := fun x => Fin.eq_zero x
    let colorPair : (Fin 1 ⊕ Fin m) → (Fin 1 ⊕ Fin m) → Fin m :=
      fun a b =>
      match a, b with
      | Sum.inl _, Sum.inl _ => ⟨0, hm_pos⟩
      | Sum.inl _, Sum.inr i => i
      | Sum.inr i, Sum.inl _ => i
      | Sum.inr a, Sum.inr b =>
        if b = a + 1 then a + 2
        else if a = b + 1 then b + 2
        else ⟨0, hm_pos⟩
    -- colorPair is symmetric
    have h_two_ne_zero : (2 : Fin m) ≠ 0 := by
      intro h
      have h1 : (2 : Fin m).val = (0 : Fin m).val := congr_arg Fin.val h
      simp at h1
      have hlt : 2 < m := by omega
      have : 2 % m = 2 := Nat.mod_eq_of_lt hlt
      omega
    have h_not_self_plus_two : ∀ x : Fin m, x ≠ x + 1 + 1 := by
      intro x h
      have : (1 + 1 : Fin m) = 0 := by simpa [add_assoc] using h
      exact h_two_ne_zero this
    have one_ne_two : (1 : Fin m) ≠ 2 := by
      intro h
      have : (0 : Fin m) = 1 := by
        have := h; rw [show (2 : Fin m) = 1 + 1 from rfl] at this; simp at this
      exact one_ne_zero this.symm
    have hsym : ∀ a b : Fin 1 ⊕ Fin m, colorPair a b = colorPair b a := by
      intro a b
      rcases a with x | ⟨a0, ha0⟩ <;> rcases b with y | ⟨b0, hb0⟩
      · fin_cases x; fin_cases y; rfl
      · rfl
      · rfl
      · simp only [colorPair]
        by_cases h1 : (⟨b0, hb0⟩ : Fin m) = (⟨a0, ha0⟩ : Fin m) + 1
        · rw [h1]
          simp [h_not_self_plus_two]
        · by_cases h2 : (⟨a0, ha0⟩ : Fin m) = (⟨b0, hb0⟩ : Fin m) + 1
          · rw [h2]
            simp; exact h_not_self_plus_two _
          · simp [h1, h2]
    -- Lift colorPair to Sym2
    let colorOnSym2 : Sym2 (Fin 1 ⊕ Fin m) → Fin m :=
      Quot.lift (fun p => colorPair p.1 p.2) (fun p q hpq => by
        simp at hpq
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact hsym _ _)
    -- Coloring of line graph
    let c : (CGraph.lineGraph (CGraph.wheel m)).V → Fin m := fun e => colorOnSym2 e.1
    -- Show every edge is spoke or rim
    have edge_is_spoke_or_rim : ∀ e : Sym2 (Fin 1 ⊕ Fin m),
        e ∈ (CGraph.wheel m).toSimple.edgeSet →
        (∃ i : Fin m, e = spokeEdge i) ∨ (∃ i : Fin m, e = rimEdge i) := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        simp at he
        rcases a with a | ⟨a0, ha0⟩ <;> rcases b with b | ⟨b0, hb0⟩
        · -- inl-inl: impossible (loopless)
          fin_cases a; fin_cases b
          simp [CGraph.wheel, CGraph.join] at he
        · -- inl-inr: spoke edge
          fin_cases a
          left; exact ⟨⟨b0, hb0⟩, by simp [spokeEdge, hub, rim]⟩
        · -- inr-inl: spoke edge
          fin_cases b
          left; exact ⟨⟨a0, ha0⟩, by
            simp [spokeEdge, hub, rim]⟩
        · -- inr-inr: rim edge from cycle
          dsimp [CGraph.wheel] at he
          rw [CGraph.join_adj_inr_inr] at he
          have h_adj := CGraph.cycle_adj_val m ⟨a0, ha0⟩ ⟨b0, hb0⟩ |>.mp he
          obtain ⟨hne, hab | hba⟩ := h_adj
          · -- b = a + 1 (mod m): edge is rimEdge a0
            right
            have hb_eq : (⟨b0, hb0⟩ : Fin m) = (⟨a0, ha0⟩ : Fin m) + 1 := by
              exact Fin.ext (by simpa [Fin.val_add] using hab.symm)
            refine ⟨⟨a0, ha0⟩, ?_⟩
            show s(Sum.inr ⟨a0, ha0⟩, Sum.inr ⟨b0, hb0⟩) = rimEdge ⟨a0, ha0⟩
            dsimp only [rimEdge]
            rw [hb_eq]
          · -- a = b + 1 (mod m): edge is rimEdge b0 (after swap)
            right
            have ha_eq : (⟨a0, ha0⟩ : Fin m) = (⟨b0, hb0⟩ : Fin m) + 1 := by
              exact Fin.ext (by simpa [Fin.val_add] using hba.symm)
            refine ⟨⟨b0, hb0⟩, ?_⟩
            show s(Sum.inr ⟨a0, ha0⟩, Sum.inr ⟨b0, hb0⟩) = rimEdge ⟨b0, hb0⟩
            dsimp only [rimEdge]
            rw [ha_eq]
            exact Quot.sound (Sym2.Rel.swap _ _)
    -- rimEdge membership (need these for spoke_rim_shared below)
    have rimEdge_mem_left : ∀ j : Fin m, (rim j : Fin 1 ⊕ Fin m) ∈ rimEdge j := by
      intro j; simp [rimEdge, rim]
    have rimEdge_mem_right : ∀ j : Fin m, (rim (j + 1) : Fin 1 ⊕ Fin m) ∈ rimEdge j := by
      intro j; simp [rimEdge, rim]
    have rim_injective : ∀ i j : Fin m, rim i = rim j → i = j := by
      intro i j h; simp [rim] at h; exact h
    have one_ne_zero : (1 : Fin m) ≠ 0 := by
      intro h
      have h1 : (1 : ℕ) % m = 0 := by
        simp at h
      rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at h1
      omega
    -- Color computations
    have color_spoke : ∀ i : Fin m, colorOnSym2 (spokeEdge i) = i := by
      intro i; simp [colorOnSym2, spokeEdge, colorPair, hub, rim]
    have color_rim : ∀ i : Fin m, colorOnSym2 (rimEdge i) = i + 2 := by
      intro i; simp [colorOnSym2, rimEdge, colorPair, rim]
    -- Vertex ∈ spoke/rim edge characterization
    have spoke_mem_hub : ∀ i : Fin m, hub ∈ spokeEdge i := spoke_mem
    have spoke_mem_rim : ∀ i : Fin m, rim i ∈ spokeEdge i := inr_mem_spoke
    have rim_not_hub : ∀ (i j : Fin m), ¬(hub ∈ rimEdge i) := by
      intro i j; exact spoke_not_in_rim j i (spoke_mem_hub j)
    -- spoke_rim_shared: if v is in spokeEdge i and rimEdge j, then i = j or i = j+1
    have spoke_rim_shared : ∀ (i j : Fin m) (v : Fin 1 ⊕ Fin m),
        v ∈ spokeEdge i → v ∈ rimEdge j → (i = j ∨ i = j + 1) := by
      intro i j v hvi hvj
      have hv_spoke : v = hub ∨ v = rim i := by
        simp [spokeEdge] at hvi; exact hvi
      have hv_rim : v = rim j ∨ v = rim (j + 1) := by
        simp [rimEdge] at hvj; exact hvj
      rcases hv_spoke with rfl | rfl
      · exact absurd hvj (rim_not_hub j i)
      · rcases hv_rim with h | h
        · left; exact rim_injective _ _ h
        · right; exact rim_injective _ _ h
    -- spoke-rim color incompatibility
    have spoke_rim_color : ∀ (i j : Fin m), i = j ∨ i = j + 1 → (i : Fin m) ≠ (j + 2 : Fin m) := by
      intro i j hij
      rcases hij with rfl | rfl
      · intro h; exact h_two_ne_zero (by simpa using h)
      · intro h
        have h12 : (1 : ℕ) % m = (2 : ℕ) % m := by
          simpa [Fin.ext_iff] using h
        rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt (by omega : 2 < m)] at h12
        omega
    -- rimEdge injectivity (needed for rim-rim case)
    have rimEdge_inj : ∀ (a b : Fin m), rimEdge a = rimEdge b → a = b := by
      intro a b heq
      have hi1 := rimEdge_mem_left a
      have hi2 := rimEdge_mem_right a
      rw [heq] at hi1 hi2
      have hj_options : ∀ x : Fin 1 ⊕ Fin m, x ∈ rimEdge b → x = rim b ∨ x = rim (b + 1) := by
        intro x hx; simp [rimEdge] at hx; exact hx
      rcases hj_options _ hi1 with h1 | h1 <;> rcases hj_options _ hi2 with h2 | h2
      · exfalso
        have h3 : rim (a + 1) = rim a := by rw [← h1] at h2; exact h2
        have h4 : (1 : Fin m) = 0 := by
          have := rim_injective _ _ h3
          simp at this
        exact one_ne_zero h4
      · exact rim_injective _ _ h1
      · exfalso
        have ha_fb : a = b + 1 := rim_injective _ _ h1
        have ha1_b : a + 1 = b := rim_injective _ _ h2
        have h2eq : (2 : Fin m) = 0 := by
          have h : b + 1 + 1 = b := by rw [ha_fb] at ha1_b; exact ha1_b
          have : (2 + b : Fin m) = b := by simpa [add_comm, add_left_comm, add_assoc] using h
          simpa using this
        exact h_two_ne_zero h2eq
      · exfalso
        have ha1_b : a + 1 = b + 1 := rim_injective _ _ h2
        have ha_b : a = b := by simpa using ha1_b
        have : (1 : Fin m) = 0 := by
          have := rim_injective _ _ h1
          simp [ha_b] at this
        exact one_ne_zero this
    -- Main coloring proof
    refine ⟨c, fun {e f} hef => ?_⟩
    simp [CGraph.toSimple, SimpleGraph.completeGraph] at hef ⊢
    obtain ⟨hef_ne, v, hv_e, hv_f⟩ := hef
    obtain ⟨e_val, he_mem⟩ := e
    obtain ⟨f_val, hf_mem⟩ := f
    simp at hv_e hv_f hef_ne
    have he_split := edge_is_spoke_or_rim e_val he_mem
    have hf_split := edge_is_spoke_or_rim f_val hf_mem
    rcases he_split with ⟨ie, he_eq⟩ | ⟨ie, he_eq⟩
    · -- e is spoke
      rcases hf_split with ⟨jf, hf_eq⟩ | ⟨jf, hf_eq⟩
      · -- spoke-spoke
        simp only [he_eq, hf_eq, c, color_spoke]
        intro h; exact hef_ne (by simp [he_eq, hf_eq, h])
      · -- spoke-rim
        simp only [he_eq, hf_eq, c, color_spoke, color_rim]
        have hmem_e : v ∈ spokeEdge ie := by rw [he_eq] at hv_e; exact hv_e
        have hmem_f : v ∈ rimEdge jf := by rw [hf_eq] at hv_f; exact hv_f
        rcases spoke_rim_shared ie jf v hmem_e hmem_f with rfl | h
        · -- ie = jf, colors: ie vs ie+2, need ie ≠ ie+2
          intro h'
          have : ie = ie + 1 + 1 := by simpa [add_assoc] using h'
          exact h_not_self_plus_two ie this
        · -- ie = jf + 1, colors: ie vs jf+2 = ie+1, need ie ≠ ie+1
          intro h'
          rw [h] at h'
          have h' : jf + 1 = jf + 2 := h'
          have : (1 : Fin m) = 2 := by simpa [add_assoc] using h'
          exact one_ne_two this
    · -- e is rim
      rcases hf_split with ⟨jf, hf_eq⟩ | ⟨jf, hf_eq⟩
      · -- rim-spoke
        simp only [he_eq, hf_eq, c, color_spoke, color_rim]
        have hmem_e : v ∈ rimEdge ie := by rw [he_eq] at hv_e; exact hv_e
        have hmem_f : v ∈ spokeEdge jf := by rw [hf_eq] at hv_f; exact hv_f
        rcases spoke_rim_shared jf ie v hmem_f hmem_e with h|h
        · -- h : jf = ie, colors: ie+2 vs ie
          intro h'
          rw [h] at h'
          have : ie + 1 + 1 = ie := by simpa [add_assoc] using h'
          exact h_not_self_plus_two ie this.symm
        · -- h : jf = ie + 1, colors: ie+2 vs ie+1
          intro h'
          rw [h] at h'
          -- h' : ie + 2 = ie + 1, so 2 = 1, so 1 = 0
          have h12 : (2 : Fin m) = 1 := by simpa using h'
          have : (1 : Fin m) = 0 := by
            have := h12; rw [show (2 : Fin m) = 1 + 1 from rfl] at this; simp at this
          exact one_ne_zero this
      · -- rim-rim
        simp only [he_eq, hf_eq, c, color_rim]
        have hmem_e : v ∈ rimEdge ie := by rw [he_eq] at hv_e; exact hv_e
        have hmem_f : v ∈ rimEdge jf := by rw [hf_eq] at hv_f; exact hv_f
        have hv_ie : v = rim ie ∨ v = rim (ie + 1) := by
          simp [rimEdge] at hmem_e; exact hmem_e
        have hv_jf : v = rim jf ∨ v = rim (jf + 1) := by
          simp [rimEdge] at hmem_f; exact hmem_f
        rcases hv_ie with h1 | h1 <;> rcases hv_jf with h2 | h2
        · exfalso
          exact hef_ne (by rw [he_eq, hf_eq, show ie = jf from rim_injective _ _ (h1 ▸ h2)])
        · intro h'
          have hiej : ie = jf + 1 := rim_injective _ _ (h1 ▸ h2)
          rw [hiej] at h'
          have : (1 : Fin m) = 0 := by simp [add_assoc] at h'
          exact one_ne_zero this
        · intro h'
          have hfiej : jf = ie + 1 := rim_injective _ _ (h2 ▸ h1)
          rw [hfiej] at h'
          have : (1 : Fin m) = 0 := by simp [add_assoc] at h'
          exact one_ne_zero this
        · exfalso
          have : ie = jf := by
            have h3 : ie + 1 = jf + 1 := rim_injective _ _ (h1 ▸ h2)
            simpa using h3
          rw [he_eq, hf_eq, this] at hef_ne; exact hef_ne rfl
  · -- Lower bound: n+4 ≤ chromNum (lineGraph (wheel (n+4)))
    have h := maxDeg_le_edgeChromNum (wheel (n + 4))
    rw [edgeChromNum_eq] at h
    have : maxDeg (wheel (n + 4)) = n + 4 := by
      rw [show n + 4 = (n + 1) + 3 from rfl, maxDeg_wheel]
    rw [this] at h
    exact h

/-- **Turán's theorem**: among the graphs on `n` vertices with no clique of size `r + 1`, the
Turán graph `T(n, r)` has the most edges. -/
theorem E_le_E_turan {G : IsoGraph} {r : ℕ} (hr : 0 < r) (h : G.cliqueNum ≤ r) :
    G.E ≤ (turan G.V r).E := by
  induction G using Quotient.inductionOn with | _ g => ?_
  simp only [cliqueNum_mk, E_mk, V_mk] at h ⊢
  -- Step 1: Get CliqueFree (r+1) for g.toSimple
  have hcf : g.toSimple.CliqueFree (r + 1) := by
    intro s hs
    have h2 : s.card ≤ g.toSimple.cliqueNum := hs.isClique.card_le_cliqueNum
    rw [CGraph.cliqueNum] at h
    rw [hs.card_eq] at h2; omega
  -- Step 2: Get Turán-maximal graph on g.V
  classical
  obtain ⟨H, _, maxH⟩ := SimpleGraph.exists_isTuranMaximal (V := g.V) hr
  -- Step 3: g's edge count ≤ H's edge count
  have hle1 : g.toSimple.edgeFinset.card ≤ H.edgeFinset.card := maxH.2 hcf
  -- Step 4: H ≅ turanGraph, so same edge count
  have hiso := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp maxH
  obtain ⟨i⟩ := hiso
  have hle2 : H.edgeFinset.card = (SimpleGraph.turanGraph (FinEnum.card g.V) r).edgeFinset.card := by
    rw [FinEnum.card_eq_fintypeCard]; exact i.card_edgeFinset_eq
  -- Step 5: relate (turan (FinEnum.card g.V) r).E to turanGraph
  set n := FinEnum.card g.V
  -- Both turanGraph n r and turan n r have the same edge count.
  have key : (SimpleGraph.turanGraph n r).edgeFinset.card = (turan n r).E := by
    have hturanGraph_E := @SimpleGraph.card_edgeFinset_turanGraph n r
    have hturan_E := E_turan n r
    set q := n / r
    set s := n % r
    have hq : r * q + s = n := Nat.div_add_mod n r
    have hs_lt : s < r := Nat.mod_lt n hr
    have hsle : s ≤ r := hs_lt.le
    let corr := s * Nat.choose (q + 1) 2 + (r - s) * Nat.choose q 2
    -- From E_turan: (turan n r).E + corr = n.choose 2
    -- Goal: turanGraph.card + corr = n.choose 2 (then omega)
    rw [hturanGraph_E]
    -- Need: (n^2 - s^2) * (r-1) / (2*r) + s.choose 2 + corr = n.choose 2
    -- Equivalently, 2 * lhs + 2 * corr = 2 * n.choose 2 = n*(n-1)
    -- It suffices to show turanGraph.card + corr = n.choose 2
    suffices h : (n ^ 2 - s ^ 2) * (r - 1) / (2 * r) + s.choose 2 + corr = n.choose 2 by
      omega
    -- Multiply by 2 to avoid Nat division
    have h2choose_s : 2 * s.choose 2 = s * (s - 1) := by
      rw [Nat.choose_two_right, mul_comm,
          Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self s))]
    have h2choose_q1 : 2 * ((q + 1).choose 2) = (q + 1) * q := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self (q + 1)))
    have h2choose_q : 2 * (q.choose 2) = q * (q - 1) := by
      rw [Nat.choose_two_right]
      rw [mul_comm, Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self q))]
    have h2E0 : 2 * n.choose 2 = n * (n - 1) := by
      rw [Nat.choose_two_right, mul_comm,
          Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))]
    have h2corr : 2 * corr = s * ((q + 1) * q) + (r - s) * (q * (q - 1)) := by
      unfold corr
      have : 2 * (s * ((q + 1).choose 2) + (r - s) * (q.choose 2)) =
        s * (2 * ((q + 1).choose 2)) + (r - s) * (2 * (q.choose 2)) := by ring
      rw [this, h2choose_q1, h2choose_q]
    -- Key: 2 * turanGraph term
    -- (n^2 - s^2) = r * q * (r * q + 2 * s)
    have hsq : n ^ 2 - s ^ 2 = r * q * (r * q + 2 * s) := by
      rw [← hq]; ring_nf; omega
    have h2turan : 2 * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r)) = q * (r * q + 2 * s) * (r - 1) := by
      rw [hsq]
      have : r * q * (r * q + 2 * s) * (r - 1) = r * (q * (r * q + 2 * s) * (r - 1)) := by ring
      rw [this]
      rw [show 2 * r = r * 2 from mul_comm _ _]
      rw [Nat.mul_div_mul_left _ _ hr]
      rw [mul_comm, Nat.div_mul_cancel]
      by_cases hq2 : Even q
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (even_iff_two_dvd.mp hq2) _) _
      · by_cases hr2 : Even r
        · have hmid : 2 ∣ r * q + 2 * s := by
            exact dvd_add (dvd_mul_of_dvd_left (even_iff_two_dvd.mp hr2) q) (dvd_mul_right 2 s)
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hmid q) (r - 1)
        · have hrd : Even (r - 1) := by
            rw [Nat.even_sub (show 1 ≤ r from hr)]
            simp [Nat.even_iff] at hr2 ⊢
            omega
          exact dvd_mul_of_dvd_right hrd.two_dvd _
    -- Now: 2*(LHS + corr) = 2*n.choose 2  ↔  LHS + corr = n.choose 2
    have : 2 * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r) + s.choose 2 + corr) = 2 * n.choose 2 := by
      calc 2 * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r) + s.choose 2 + corr)
          = 2 * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r)) + 2 * s.choose 2 + 2 * corr := by ring
        _ = q * (r * q + 2 * s) * (r - 1) + s * (s - 1) + (s * ((q + 1) * q) + (r - s) * (q * (q -
            1))) := by
            rw [h2turan, h2choose_s, h2corr]
        _ = n * (n - 1) := by
            by_cases hq0 : q = 0
            · simp only [hq0] at hq ⊢; rw [show n = s from by omega]; simp [mul_zero, zero_mul,
                  add_zero]
            · have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq0
              by_cases hs0 : s = 0
              · rw [hs0] at hq ⊢; ring_nf at *
                have : ∀ x : ℕ, x - 0 = x := fun x => Nat.sub_zero x
                rw [this r] at *
                rw [show n = q * r from hq.symm]
                have : q * r * (q * r - 1) = q * r * (q - 1) + q ^ 2 * r * (r - 1) := by
                  zify [Nat.cast_sub (show 1 ≤ q from hq1), Nat.cast_sub (show 1 ≤ r from hr),
                      Nat.cast_sub (show 1 ≤ q * r from by nlinarith)]
                  ring
                rw [this]
              · have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs0
                have hpos_n : 1 ≤ n := by omega

                have hsub_r1 : (r - 1 : ℤ) = ↑r - 1 := by omega
                have hsub_s1 : (s - 1 : ℤ) = ↑s - 1 := by omega
                have hsub_q1 : (q - 1 : ℤ) = ↑q - 1 := by omega
                have hsub_rs : (r - s : ℤ) = ↑r - ↑s := by omega
                have hsub_n1 : (n - 1 : ℤ) = ↑n - 1 := by omega
                have hn_int : (n : ℤ) = ↑r * ↑q + ↑s := by norm_cast; omega
                have hgoal : q * (r * q + 2 * s) * (r - 1) + s * (s - 1) + (s * ((q + 1) * q) + (r
                    - s) * (q * (q - 1))) = n * (n - 1) := by
                  have hcast : (q * (r * q + 2 * s) * (r - 1) + s * (s - 1) + (s * ((q + 1) * q) +
                      (r - s) * (q * (q - 1))) : ℤ) =
                      (n * (n - 1) : ℤ) := by
                    rw [hn_int]
                    ring
                  have hup_lhs : (↑(q * (r * q + 2 * s) * (r - 1) + s * (s - 1) + (s * ((q + 1) *
                      q) + (r - s) * (q * (q - 1))) : ℕ) : ℤ) =
                      (q * (r * q + 2 * s) * (r - 1) + s * (s - 1) + (s * ((q + 1) * q) + (r - s) *
                          (q * (q - 1))) : ℤ) := by
                    push_cast [Nat.cast_sub (show 1 ≤ r from hr), Nat.cast_sub hsle,
                        Nat.cast_sub hq1, Nat.cast_sub hs1, Nat.cast_sub (show s ≤ r from hsle),
                        Nat.cast_sub (show 1 ≤ q from hq1)]
                    rfl
                  have hup_rhs : (↑(n * (n - 1)) : ℤ) = (n * (n - 1) : ℤ) := by
                    push_cast [Nat.cast_sub (show 1 ≤ n from hpos_n)]
                    rfl
                  exact Nat.cast_injective (hup_lhs.trans (hcast.trans hup_rhs.symm))
                exact hgoal
        _ = 2 * n.choose 2 := h2E0.symm
    omega
  rw [CGraph.E]
  exact le_trans (hle1.trans hle2.le) key.le

/-- An odd circulant with a nonzero connection is not bipartite, so it has a cycle. -/
theorem not_isAcyclic_circulant_of_odd {n : ℕ} {S : List ℕ} (hn : n % 2 = 1) (d : ℕ) (hd : d ∈ S)
    (h0 : 0 < d) (hdn : d < n) : ¬ IsAcyclic (circulant n S) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_circulant_of_odd hn d hd h0 hdn)

/-- Every vertex of `K_{m,n}` sees the whole of the other side. -/
@[simp] theorem maxDeg_bipartite (m n : ℕ) :
    maxDeg (bipartite (m + 1) (n + 1)) = max (m + 1) (n + 1) := by
  rw [bipartite_eq_join, maxDeg_join (by simp) (by simp), maxDeg_empty, maxDeg_empty, V_empty,
    V_empty]
  omega

/-- The smaller side is the one whose vertices have the larger degree, so the minimum is the
smaller of the two sizes. -/
@[simp] theorem minDeg_bipartite (m n : ℕ) :
    minDeg (bipartite (m + 1) (n + 1)) = min (m + 1) (n + 1) := by
  rw [bipartite_eq_join, minDeg_join (by simp) (by simp), minDeg_empty, minDeg_empty, V_empty,
    V_empty]
  omega

/-- The odd prism misses one vertex of a perfect independent set, so its cover needs one more. -/
theorem coverNum_prism_odd (m : ℕ) : (prism (2 * m + 3)).coverNum = 2 * m + 4 := by
  have h1 := indepNum_prism_odd m
  have h2 := coverNum_add_indepNum (prism (2 * m + 3))
  rw [V_prism] at h2
  omega

/-! ### The rest of the Grötzsch row

These need the general Mycielskian invariants proved above, so they sit here rather than
with the other Grötzsch facts. -/

/-- The apex has degree `5`, the pentagon vertices `2 · 2 = 4`, the shadows `2 + 1 = 3`. -/
@[simp] theorem degMultiset_grotzsch :
    grotzsch.degMultiset
      = Multiset.replicate 5 4 + Multiset.replicate 5 3 + {5} := by
    unfold grotzsch
    rw [degMultiset_mycielskian, degMultiset_cycle (n := 2)]
    simp [V_cycle]

/-- The shadows are the vertices of least degree. -/
theorem minDeg_grotzsch : grotzsch.minDeg = 3 := by
  refine minDeg_eq_of_degMultiset ?_ ?_
  · rw [degMultiset_grotzsch]; simp
  · intro d hd
    rw [degMultiset_grotzsch] at hd
    simp (config := { decide := true }) only [Multiset.mem_add, Multiset.mem_replicate,
        Multiset.mem_singleton] at hd
    rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega

/-- The apex is the vertex of greatest degree. -/
theorem maxDeg_grotzsch : maxDeg grotzsch = 5 := by
  rw [grotzsch, maxDeg_mycielskian, maxDeg_cycle, V_cycle]
  decide

/-- The Mycielskian of a graph with no isolated vertex is connected. -/
theorem isConnected_grotzsch : IsConnected grotzsch := by
  rw [grotzsch]
  apply isConnected_mycielskian
  rw [minDeg_cycle 2]
  norm_num

theorem numComponents_grotzsch : grotzsch.numComponents = 1 := (numComponents_eq_one_iff
    grotzsch).2 isConnected_grotzsch

/-- `γ(C₅) = 2` and the Mycielskian adds exactly one. -/
theorem domNum_grotzsch : grotzsch.domNum = 3 := by
  rw [show grotzsch = mycielskian (cycle 5) from rfl]
  rw [domNum_mycielskian (cycle 5) (by simp)]
  rw [show (5 : ℕ) = 2 + 3 from rfl]
  rw [domNum_cycle 2]

/-- No vertex sees all ten others, but every pair is joined by a path of length two. -/
theorem diameter_grotzsch : grotzsch.diameter = 2 := by
  rw [grotzsch, show cycle 5 = (⟦CGraph.cycle 5⟧ : IsoGraph) from rfl, IsoGraph.mycielskian_mk,
      IsoGraph.diameter_mk]
  exact @CGraph.diameter_eq_two (CGraph.mycielskian (CGraph.cycle 5)) (by decide) none (some
      (Sum.inl (0 : Fin 5))) (Ne.symm (Option.some_ne_none _)) (by decide)

theorem radius_grotzsch : grotzsch.radius = 2 := by
  set G : CGraph := CGraph.mycielskian (CGraph.cycle 5)
  have hgrotzsch : grotzsch = Quotient.mk _ G := by
    rw [grotzsch, cycle_def, mycielskian_mk]
  -- Transfer IsoGraph facts to CGraph level
  have hG_maxDeg : G.maxDeg = 5 := by
    rw [← maxDeg_grotzsch, hgrotzsch, maxDeg_mk]
  have hG_V : FinEnum.card G.V = 11 := by
    rw [← V_grotzsch, hgrotzsch, V_mk]
  -- No universal vertex in G (degree ≤ 5 < 10)
  have hno_univ_G : ¬ ∃ v : G.V, ∀ u : G.V, u ≠ v → G.Adj v u := by
    decide
  -- Radius of G (CGraph) is 2
  have hG_connected : G.IsConnected := by
    have := isConnected_grotzsch
    rw [hgrotzsch, IsoGraph.isConnected_mk] at this
    exact this
  have h_radius_G : G.radius = 2 := by
    -- Two-step property for G
    have h_two_step_G : ∀ u v : G.V, u ≠ v →
        G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v := by
      decide
    -- diameter ≤ 2
    have hdiam_G : G.diameter ≤ 2 := CGraph.diameter_le_two G h_two_step_G
    -- radius ≤ diameter ≤ 2
    have hrad_le_G : G.radius ≤ 2 := le_trans (CGraph.radius_le_diameter G) hdiam_G
    -- radius ≠ 1: no universal vertex → domNum ≠ 1 → radius ≠ 1
    have hdom_ne_one_G : G.domNum ≠ 1 := by
      intro h
      rw [CGraph.domNum_eq_one_iff G] at h
      exact hno_univ_G h
    have hpos_G : 0 < G.radius := CGraph.radius_pos G hG_connected (by omega : 1 < FinEnum.card G.V)
    have hne1_G : G.radius ≠ 1 := by
      intro h
      rw [CGraph.radius_eq_one_iff_domNum_eq_one G (by omega : 1 < FinEnum.card G.V)] at h
      exact hdom_ne_one_G h
    omega
  rw [hgrotzsch, IsoGraph.radius_mk, h_radius_G]

/-- The Mycielskian creates no triangle out of a pentagon, but `vᵢ uⱼ vₖ uₗ` closes up. -/
theorem girth_grotzsch : grotzsch.girth = 4 := by
  rw [show grotzsch = mycielskian (cycle 5) from rfl]
  simp only [cycle, mycielskian_mk]
  rw [girth_mk]
  let G := CGraph.cycle 5
  set M := G.mycielskian
  let a : M.V := some (Sum.inl (0 : Fin 5))
  let b : M.V := some (Sum.inr (1 : Fin 5))
  let c : M.V := (none : Option (Fin 5 ⊕ Fin 5))
  let d : M.V := some (Sum.inr (4 : Fin 5))
  have hab : M.Adj a b := by decide
  have hbc : M.Adj b c := by decide
  have hcd : M.Adj c d := by decide
  have hda : M.Adj d a := by decide
  have hac : a ≠ c := Option.some_ne_none _
  have hbd : b ≠ d :=
    fun h ↦ absurd (Sum.inr.inj (Option.some.inj h)) (Fin.ne_of_val_ne (by decide))
  have hle : M.girth ≤ 4 := CGraph.girth_le_four_of_square hab hbc hcd hda hac hbd
  have hnac : ¬ M.IsAcyclic := CGraph.not_isAcyclic_of_square hab hbc hcd hda hac hbd
  have htri : ∀ x y z : M.V, M.Adj x y → M.Adj y z → M.Adj z x → False := by
    decide
  exact le_antisymm hle (CGraph.four_le_girth htri hnac)

/-- Eleven vertices admit a matching missing only one of them. -/
theorem matchNum_grotzsch : grotzsch.matchNum = 5 := by
  have hub : grotzsch.matchNum ≤ 5 := by
    have h := grotzsch.two_mul_matchNum_le_V
    rw [V_grotzsch] at h; omega
  have hequindep : 5 ≤ grotzsch.lineGraph.indepNum := by
    rw [grotzsch, IsoGraph.cycle, mycielskian_mk]
    simp only [lineGraph_mk, indepNum_mk]
    -- the five edges `vᵢ uᵢ₊₁` are pairwise disjoint, so they are independent in the line graph
    have h_exists : ∃ S : Finset (CGraph.lineGraph (CGraph.mycielskian (CGraph.cycle 5))).V,
        S.card = 5 ∧
        (CGraph.lineGraph (CGraph.mycielskian (CGraph.cycle 5))).toSimple.IsIndepSet
          (S : Set (CGraph.lineGraph (CGraph.mycielskian (CGraph.cycle 5))).V) := by
      refine ⟨{⟨s(some (Sum.inl (0 : Fin 5)), some (Sum.inr (1 : Fin 5))), by decide⟩,
        ⟨s(some (Sum.inl (1 : Fin 5)), some (Sum.inr (2 : Fin 5))), by decide⟩,
        ⟨s(some (Sum.inl (2 : Fin 5)), some (Sum.inr (3 : Fin 5))), by decide⟩,
        ⟨s(some (Sum.inl (3 : Fin 5)), some (Sum.inr (4 : Fin 5))), by decide⟩,
        ⟨s(some (Sum.inl (4 : Fin 5)), some (Sum.inr (0 : Fin 5))), by decide⟩},
        ?_, ?_⟩
      · decide
      · decide
    obtain ⟨S, hS_card, hS_indep⟩ := h_exists
    have h1 := hS_indep.card_le_indepNum
    rw [hS_card] at h1
    exact h1
  have h_eq := matchNum_eq grotzsch
  omega

/-- Twenty edges on eleven vertices is far too many for a forest. -/
theorem not_isAcyclic_grotzsch : ¬ IsAcyclic grotzsch :=
  not_isAcyclic_of_not_isBipartite not_isBipartite_grotzsch

/-- The shadows have degree three and the apex degree five. -/
theorem not_isVertexTransitive_grotzsch : ¬ IsVertexTransitive grotzsch :=
  not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp)
    (by rw [minDeg_grotzsch, maxDeg_grotzsch]; omega)

/-- A triangle-free graph's cliques are its vertices and edges, so `κ = |V| - ν`. -/
theorem cliqueCoverNum_grotzsch : grotzsch.cliqueCoverNum = 6 := by
  have h1 := V_grotzsch
  have h2 := matchNum_grotzsch
  have h3 := cliqueCoverNum_of_cliqueNum_le_two cliqueNum_grotzsch.le (by omega)
  omega

end IsoGraph
