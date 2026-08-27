import IsoGraph.SmallGraphs.TuranGraphs

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

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
  rw [add_comm, ← Multiset.coe_replicate]
  refine sort_replicate_append (List.pairwise_replicate.2 (Or.inr le_rfl)) fun x hx y hy ↦ ?_
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  omega

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

/-- **The hypercube is class one.**  Colour an edge by the coordinate its two ends disagree on:
two edges at a common vertex flip different coordinates, so they get different colours.  That is
`n + 1` colours, and the graph is `(n + 1)`-regular, so no fewer will do. -/
theorem edgeChromNum_hypercube (n : ℕ) : (hypercube (n + 1)).edgeChromNum = n + 1 := by
  refine le_antisymm ?_ ?_
  · rw [hypercube_def]
    refine edgeChromNum_mk_le_of_colouring
      (fun x y ↦ (Finset.univ.filter fun i ↦ x i ≠ y i).sup id) (fun x y ↦ by simp [ne_comm])
      ?_
    intro u v w huv huw hvw hc
    obtain ⟨i, rfl⟩ := (CGraph.hypercube_adj_update_iff _ _ _).1 huv
    obtain ⟨j, rfl⟩ := (CGraph.hypercube_adj_update_iff _ _ _).1 huw
    simp only [filter_ne_update_not, Finset.sup_singleton, id] at hc
    exact hvw (by rw [hc])
  · exact (isRegularWith_hypercube (n + 1)).le_edgeChromNum
      (by rw [V_hypercube]; positivity)

/-- **The wheel is class one.**  Give the spoke at rim vertex `i` the colour `i`, and the rim edge
`{i, i + 1}` the colour `i + 2`.  At the hub the spokes are all differently coloured; at a rim
vertex `i` the spoke, the rim edge going forward and the rim edge coming back get `i`, `i + 2`
and `i + 1`, which are three distinct colours because the rim has at least four vertices. -/
theorem edgeChromNum_wheel (n : ℕ) : (wheel (n + 4)).edgeChromNum = n + 4 := by
  refine le_antisymm ?_ ?_
  · -- The three colours meeting at a rim vertex are distinct because the rim is long.
    have hmod : 2 % (n + 4) = 2 := Nat.mod_eq_of_lt (by omega)
    have hone_ne_zero : (1 : Fin (n + 4)) ≠ 0 := Fin.ne_of_val_ne (by simp)
    have htwo_ne_zero : (2 : Fin (n + 4)) ≠ 0 := Fin.ne_of_val_ne (by simp [hmod])
    have hone_ne_two : (1 : Fin (n + 4)) ≠ 2 := Fin.ne_of_val_ne (by simp [hmod])
    have h11 : (1 : Fin (n + 4)) + 1 = 2 := by apply Fin.ext; simp [Fin.val_add]
    have hne1 : ∀ x : Fin (n + 4), x ≠ x + 1 :=
      fun x hx ↦ hone_ne_zero (add_left_cancel (a := x) (by rw [add_zero, ← hx]))
    have hne2 : ∀ x : Fin (n + 4), x ≠ x + 2 :=
      fun x hx ↦ htwo_ne_zero (add_left_cancel (a := x) (by rw [add_zero, ← hx]))
    have hne12 : ∀ x : Fin (n + 4), x + 1 ≠ x + 2 := fun x h ↦ hone_ne_two (add_left_cancel h)
    rw [wheel_def]
    -- The colouring, on ordered pairs of vertices of `complete 1 ∇g cycle (n + 4)`.
    let col : (Fin 1 ⊕ Fin (n + 4)) → (Fin 1 ⊕ Fin (n + 4)) → Fin (n + 4) := fun a b ↦
      match a, b with
      | Sum.inl _, Sum.inl _ => 0
      | Sum.inl _, Sum.inr i => i
      | Sum.inr i, Sum.inl _ => i
      | Sum.inr a, Sum.inr b => if b = a + 1 then a + 2 else if a = b + 1 then b + 2 else 0
    have hsym : ∀ a b, col a b = col b a := by
      rintro (x | a) (y | b)
      · rfl
      · rfl
      · rfl
      · show (if b = a + 1 then a + 2 else if a = b + 1 then b + 2 else 0)
            = (if a = b + 1 then b + 2 else if b = a + 1 then a + 2 else 0)
        by_cases h1 : b = a + 1
        · have h2 : a ≠ b + 1 := by rw [h1, add_assoc, h11]; exact hne2 a
          rw [if_pos h1, if_neg h2, if_pos h1]
        · by_cases h2 : a = b + 1
          · rw [if_neg h1, if_pos h2, if_pos h2]
          · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
    -- Two rim vertices are adjacent only if they are cyclically consecutive…
    have hrim : ∀ a b : Fin (n + 4), (CGraph.wheel (n + 4)).Adj (Sum.inr a) (Sum.inr b) = true →
        b = a + 1 ∨ a = b + 1 := by
      intro a b hab
      simp only [CGraph.wheel, CGraph.join_adj_inr_inr] at hab
      rw [CGraph.cycle_adj_val] at hab
      obtain ⟨-, h | h⟩ := hab
      · exact Or.inl (Fin.ext (by simpa [Fin.val_add] using h.symm))
      · exact Or.inr (Fin.ext (by simpa [Fin.val_add] using h.symm))
    -- …and then the rim edge gets the colour of its forward end plus one.
    have hcol_rim : ∀ a b : Fin (n + 4),
        (CGraph.wheel (n + 4)).Adj (Sum.inr a) (Sum.inr b) = true →
        (b = a + 1 ∧ col (Sum.inr a) (Sum.inr b) = a + 2) ∨
          (b + 1 = a ∧ col (Sum.inr a) (Sum.inr b) = a + 1) := by
      intro a b hab
      rcases hrim a b hab with h | h
      · refine Or.inl ⟨h, ?_⟩
        show (if b = a + 1 then a + 2 else if a = b + 1 then b + 2 else 0) = a + 2
        rw [if_pos h]
      · refine Or.inr ⟨h.symm, ?_⟩
        show (if b = a + 1 then a + 2 else if a = b + 1 then b + 2 else 0) = a + 1
        by_cases h1 : b = a + 1
        · refine absurd ?_ (hne2 a)
          calc a = b + 1 := h
            _ = a + 1 + 1 := by rw [h1]
            _ = a + 2 := by rw [add_assoc, h11]
        · rw [if_neg h1, if_pos h, h, add_assoc, h11]
    -- The hub is a single vertex, so it is adjacent to nothing on its own side.
    have hhub : ∀ x y : Fin 1, (CGraph.wheel (n + 4)).Adj (Sum.inl x) (Sum.inl y) = false := by
      intro x y
      rw [Subsingleton.elim x y]
      exact Bool.eq_false_iff.2 ((CGraph.wheel (n + 4)).loopless _)
    refine edgeChromNum_mk_le_of_colouring col hsym ?_
    rintro (x | a) (y | b) (z | c) huv huw hvw
    · rw [hhub] at huv; exact absurd huv (by simp)
    · rw [hhub] at huv; exact absurd huv (by simp)
    · rw [hhub] at huw; exact absurd huw (by simp)
    · exact fun h ↦ hvw (congrArg Sum.inr h)
    · exact absurd (congrArg Sum.inl (Subsingleton.elim (α := Fin 1) y z)) hvw
    · rcases hcol_rim a c huw with ⟨-, hc⟩ | ⟨-, hc⟩ <;> rw [hc]
      · exact hne2 a
      · exact hne1 a
    · rcases hcol_rim a b huv with ⟨-, hb⟩ | ⟨-, hb⟩ <;> rw [hb]
      · exact fun h ↦ hne2 a h.symm
      · exact fun h ↦ hne1 a h.symm
    · rcases hcol_rim a b huv with ⟨hb, hbc⟩ | ⟨hb, hbc⟩ <;>
        rcases hcol_rim a c huw with ⟨hc, hcc⟩ | ⟨hc, hcc⟩ <;> rw [hbc, hcc]
      · exact absurd (congrArg Sum.inr (hb.trans hc.symm)) hvw
      · exact fun h ↦ hne12 a h.symm
      · exact hne12 a
      · exact absurd (congrArg Sum.inr (add_right_cancel (hb.trans hc.symm))) hvw
  · have h := maxDeg_le_edgeChromNum (wheel (n + 4))
    rwa [show maxDeg (wheel (n + 4)) = n + 4 from by
      rw [show n + 4 = (n + 1) + 3 from rfl, maxDeg_wheel]] at h

/-- **The Turán count**: writing `n = r * q + s` with `s ≤ r`, the number of edges of the Turán
graph, the `s` parts of size `q + 1` and the `r - s` parts of size `q` together account for every
pair of vertices.  Stated for `Nat` division and subtraction, which is why it is not a `ring`. -/
private theorem turan_card_identity {r q s n : ℕ} (hr : 0 < r) (hs : s ≤ r) (hn : r * q + s = n) :
    (n ^ 2 - s ^ 2) * (r - 1) / (2 * r) + s.choose 2
      + (s * (q + 1).choose 2 + (r - s) * q.choose 2) = n.choose 2 := by
  have hdouble : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := fun m ↦ by
    rw [Nat.choose_two_right,
      Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))]
  -- the division is exact: `n² - s² = r * q * (r * q + 2 * s)`
  have hsq : n ^ 2 - s ^ 2 = r * q * (r * q + 2 * s) := by rw [← hn]; ring_nf; omega
  have hdvd : 2 ∣ q * (r * q + 2 * s) * (r - 1) := by
    rcases Nat.even_or_odd q with hq2 | hq2
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hq2.two_dvd _) _
    · rcases Nat.even_or_odd r with hr2 | hr2
      · exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (dvd_add (dvd_mul_of_dvd_left hr2.two_dvd q) ⟨s, rfl⟩) q) _
      · exact dvd_mul_of_dvd_right (Nat.Odd.sub_odd hr2 odd_one).two_dvd _
  have hdiv : 2 * ((n ^ 2 - s ^ 2) * (r - 1) / (2 * r)) = q * (r * q + 2 * s) * (r - 1) := by
    rw [hsq, show r * q * (r * q + 2 * s) * (r - 1) = r * (q * (r * q + 2 * s) * (r - 1)) by ring,
      show 2 * r = r * 2 from mul_comm _ _, Nat.mul_div_mul_left _ _ hr, mul_comm,
      Nat.div_mul_cancel hdvd]
  refine Nat.eq_of_mul_eq_mul_left two_pos ?_
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, hdiv, hdouble, mul_left_comm 2 s,
    mul_left_comm 2 (r - s), hdouble, hdouble, hdouble]
  simp only [Nat.add_sub_cancel]
  -- a polynomial identity, once the truncated subtractions are known not to truncate
  rcases Nat.eq_zero_or_pos q with rfl | hq1
  · subst hn; simp
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · subst hn
    have hn1 : 1 ≤ r * q := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hr.ne' hq1.ne')
    simp only [Nat.sub_zero, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    zify [hr, hq1, hn1]
    ring
  · have hn1 : 1 ≤ r * q + s := by omega
    subst hn
    zify [hr, hs, hq1, hs1, hn1]
    ring

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
  have key : (SimpleGraph.turanGraph n r).edgeFinset.card = (turan n r).E :=
    Nat.add_right_cancel (m := n % r * ((n / r + 1).choose 2) + (r - n % r) * ((n / r).choose 2))
      (by rw [SimpleGraph.card_edgeFinset_turanGraph,
        turan_card_identity hr (Nat.mod_lt n hr).le (Nat.div_add_mod n r), E_turan])
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
