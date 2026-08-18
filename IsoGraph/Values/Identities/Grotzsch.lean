import IsoGraph.Values.Identities.TuranGraphs

/-!
# The Grötzsch graph and the Möbius ladders

Two rows that take a module between them.  The Grötzsch graph is the Mycielskian of the 5-cycle,
so most of its entries come from the Mycielskian lemmas, but the ones that do not — its
independence number, its automorphism count — are individual computations.  The Möbius ladders are
the circulants `C_{2n}(1, n)`, and their entries are proved from that description.
-/

set_option autoImplicit false

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

/-! ### Möbius ladders

`circulant (2 * m) [1, m]` is the Möbius ladder: a `2m`-cycle with every pair of opposite
vertices joined.  The two smallest ones are graphs we already know.

Both live on `CGraph` first: the four-vertex one is an equality of graphs, since the two sides
carry the same adjacency on the same `Fin 4`, and the six-vertex one is a genuine relabelling. -/

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
    rw [edgeChromNum_eq]
    simp only [complete]
    rw [lineGraph_mk, chromNum_mk, CGraph.chromNum_le_iff_colorable]
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
    let colorOnSym2 : Sym2 (Fin (n + 1)) → Fin n := Sym2.lift ⟨colorFn, hsym⟩
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
    -- The goal is Colorable n for the line graph. Build a Coloring.
    -- colorOnSym2 is defined on all Sym2; we restrict to edges of complete (n+1).
    -- Adjacent edges share a vertex and are distinct; with distinct endpoints this gives
    -- different colors.
    -- Build Coloring for the line graph
    -- The line graph vertices are edges of complete (2*m+4), that is, pairs in
    -- Sym2 (Fin (2*m+4)) with distinct endpoints
    -- n = 2*m+3, so Fin (n+1) = Fin (2*m+4)
    show (CGraph.lineGraph (CGraph.complete (2 * m + 4))).toSimple.Colorable n
    let coloring : (CGraph.lineGraph (CGraph.complete (2 * m + 4))).V → Fin n :=
      fun x => colorOnSym2 x.val
    have hcolor_valid : ∀ (x y : (CGraph.lineGraph (CGraph.complete (2 * m + 4))).V),
        (CGraph.lineGraph (CGraph.complete (2 * m + 4))).toSimple.Adj x y →
          coloring x ≠ coloring y := by
      intro x y hadj
      rw [CGraph.toSimple_adj] at hadj
      rw [CGraph.lineGraph_adj] at hadj
      simp at hadj
      obtain ⟨hef, v, hv_e, hv_f⟩ := hadj
      obtain ⟨e, he⟩ := x
      obtain ⟨f, hf⟩ := y
      obtain ⟨p, rfl⟩ := Sym2.mk_surjective e
      obtain ⟨q, rfl⟩ := Sym2.mk_surjective f
      set a := p.1; set b := p.2
      set c := q.1; set d := q.2
      have hef' : Sym2.mk (a, b) ≠ Sym2.mk (c, d) := by
        intro h; exact hef (Subtype.ext h)
      rw [CGraph.complete_toSimple] at he hf
      have hab : a ≠ b := by
        intro h
        have he' : Sym2.mk (a, a) ∈ (CGraph.complete (2 * m + 4)).toSimple.edgeSet := by
          simp [show p = (a, a) from Prod.ext rfl h.symm] at he
        simp [CGraph.complete_toSimple] at he'
      have hcd : c ≠ d := by
        intro h
        have hf' : Sym2.mk (c, c) ∈ (CGraph.complete (2 * m + 4)).toSimple.edgeSet := by
          simp [show q = (c, c) from Prod.ext rfl h.symm] at hf
        simp [CGraph.complete_toSimple] at hf'
      -- Key helper: for an edge {x,y} of complete and v in {x,y},
      -- colorOnSym2 {x,y} = colorFn v (other)
      -- where "other" is y if v=x, and x if v=y.
      -- In all cases, colorOnSym2 e = colorFn v (other endpoint of e at v)
      -- and colorOnSym2 f = colorFn v (other endpoint of f at v).
      -- Then hcolorFn_ne gives inequality since e ≠ f implies the other endpoints differ and
      -- neither equals v.
      -- First, relate colorOnSym2 to colorFn v (other)
      have colorOnSym2_eq : ∀ (x y : Fin (n + 1)), Sym2.Mem v (Sym2.mk (x, y)) →
          colorOnSym2 (Sym2.mk (x, y)) = colorFn v (if v = x then y else x) := by
        intro x y hmem
        simp only [colorOnSym2, Sym2.lift_mk]
        simp [Sym2.Mem] at hmem
        rcases hmem with ⟨z, hz|hz⟩
        · -- inl: x = z, y = v
          simp [hz]
        · -- inr: x = v, y = z (or similar)
          simp [hz]
          rw [hsym]
          by_cases h : v = z <;> simp [h]
      have hv_e' : Sym2.Mem v (Sym2.mk (a, b)) := by
        change Sym2.Mem v (Sym2.mk p) at hv_e
        simpa [show a = p.1 from rfl, show b = p.2 from rfl] using hv_e
      have hv_f' : Sym2.Mem v (Sym2.mk (c, d)) := by
        change Sym2.Mem v (Sym2.mk q) at hv_f
        simpa [show c = q.1 from rfl, show d = q.2 from rfl] using hv_f
      show colorOnSym2 (Sym2.mk (a, b)) ≠ colorOnSym2 (Sym2.mk (c, d))
      rw [colorOnSym2_eq a b hv_e', colorOnSym2_eq c d hv_f']
      have mem_or : ∀ (w x y : Fin (n+1)), Sym2.Mem w (Sym2.mk (x, y)) → w = x ∨ w = y := by
        intro w x y hmem; simp [Sym2.Mem] at hmem
        rcases hmem with ⟨z, hz|hz⟩ <;> [left; right] <;> tauto
      rcases mem_or v a b hv_e' with hv_a | hv_b
      · -- v = a
        rw [hv_a] at hv_e' hv_f' ⊢
        have hba : b ≠ a := hab.symm
        rcases mem_or a c d hv_f' with hv_c | hv_d
        · -- v = a = c
          rw [hv_c] at hv_f' ⊢
          simp
          have hbd : b ≠ d := fun h' => hef' (by rw [h', hv_c])
          have hbc : b ≠ c := fun h' => hba (h'.trans hv_c.symm)
          have hdc : d ≠ c := fun h' => hcd h'.symm
          exact hcolorFn_ne c b d
            (fun h => hef' (by rw [hv_c, h]))
            hbc
            hdc
        · -- v = a, v = d
          rw [hv_d] at hv_f' ⊢
          have hbc : b ≠ c := fun h' => hef' (by
            rw [hv_d, h']; exact Quot.sound (Sym2.Rel.swap _ _))
          have hbd : b ≠ d := fun h' => hba (h' ▸ hv_d.symm)
          simp [hcd.symm]
          exact hcolorFn_ne d b c
            (fun h => hef' (by rw [h, hv_d]; exact Quot.sound (Sym2.Rel.swap _ _)))
            hbd
            (fun h' => hcd h')
      · -- v = b
        rw [hv_b] at hv_e' hv_f' ⊢
        have hba : a ≠ b := hab
        rcases mem_or b c d hv_f' with hv_c | hv_d
        · -- v = b = c
          rw [hv_c] at hv_f' ⊢
          have hac' : a ≠ c := fun h' => hba (h'.trans hv_c.symm)
          simp [hac'.symm]
          have had : a ≠ d := fun h' => hef' (by
            rw [h', hv_c]; exact Quot.sound (Sym2.Rel.swap _ _))
          have hdc : d ≠ c := fun h' => hcd h'.symm
          exact hcolorFn_ne c a d
            (fun h => hef' (by rw [h, hv_c]; exact Quot.sound (Sym2.Rel.swap _ _)))
            hac'
            hdc
        · -- v = b = d
          rw [hv_d] at hv_f' ⊢
          have had' : a ≠ d := fun h' => hba (h' ▸ hv_d.symm)
          simp [had'.symm, hcd.symm]
          exact hcolorFn_ne d a c
            (fun h => hef' (by rw [h, hv_d]))
            had'
            hcd
    exact ⟨SimpleGraph.Coloring.mk coloring (fun {x y} h => hcolor_valid x y h)⟩
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

/-- Covering the triangular graph `T(n)` by cliques is edge colouring `K_n`. -/
theorem cliqueCoverNum_kneser_two_even (m : ℕ) :
    (kneser (2 * m + 4) 2).cliqueCoverNum = 2 * m + 3 := by
  rw [cliqueCoverNum_eq, ← triangular_eq_compl_kneser,
    show triangular (2 * m + 4) = lineGraph (complete (2 * m + 4)) from
      (lineGraph_complete_eq_triangular (2 * m + 4)).symm,
    ← edgeChromNum_eq, edgeChromNum_complete_even_add_four]

/-- The edge chromatic number of a complete graph on at least two vertices: `Δ` when the order is
even and `Δ + 1` when it is odd. -/
theorem edgeChromNum_complete (n : ℕ) :
    (complete (n + 2)).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    rw [if_pos (by omega), edgeChromNum_complete_even]
  · subst hm
    rw [if_neg (by omega), show 2 * m + 1 + 2 = 2 * m + 3 by ring, edgeChromNum_complete_odd]

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

/-- **A regular graph of odd order is class two**: each colour class misses a vertex, so `Δ`
colours cover fewer than `E` edges. -/
theorem maxDeg_lt_edgeChromNum_of_isRegularWith_odd {G : IsoGraph} {k : ℕ}
    (h : G.IsRegularWith k) (hk : 0 < k) (hodd : G.V % 2 = 1) : maxDeg G < G.edgeChromNum := by
  have hV : 0 < G.V := by omega
  rw [h.maxDeg_eq hV]
  -- Key facts:
  -- 2 * E = V * k
  -- E ≤ edgeChromNum * matchNum
  -- 2 * matchNum ≤ V
  -- V % 2 = 1
  -- From these: V * k ≤ 2 * edgeChromNum * matchNum, and matchNum ≤ (V-1)/2
  -- So V * k ≤ edgeChromNum * (V-1), so edgeChromNum > k when k > 0 and V odd.
  have h2E := h.two_mul_E
  have hE_le := G.E_le_edgeChromNum_mul_matchNum
  have hmatch_bound := G.two_mul_matchNum_le_V
  -- matchNum ≤ (V - 1) / 2
  have hm_le : G.matchNum ≤ (G.V - 1) / 2 := by
    omega
  -- V * k ≤ edgeChromNum * (V - 1)
  have hm_le2 : 2 * G.matchNum ≤ G.V - 1 := by omega
  have hV1 : G.V - 1 ≥ 0 := Nat.zero_le _
  -- From 2*E = V*k and E ≤ edgeChromNum * matchNum:
  -- V * k ≤ 2 * (edgeChromNum * matchNum)
  -- With 2*matchNum ≤ V-1:
  -- V * k ≤ edgeChromNum * (V - 1)
  have hVk : G.V * k ≤ G.edgeChromNum * (G.V - 1) := by nlinarith
  -- If edgeChromNum ≤ k, contradiction (for k > 0, G.V ≥ 1, V odd so V-1 < V)
  by_contra hle
  push_neg at hle
  have : G.V * k ≤ k * (G.V - 1) := by nlinarith
  nlinarith [Nat.sub_add_cancel hV]

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

/-- Each original vertex of `μ(G)` has its degree doubled, each shadow gains the apex, and the
apex sees every shadow. -/
@[simp] theorem degMultiset_mycielskian (G : IsoGraph) :
    (mycielskian G).degMultiset
      = G.degMultiset.map (fun d ↦ 2 * d) + G.degMultiset.map (fun d ↦ d + 1) + {G.V} := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, degMultiset_mk, degMultiset_mk, V_mk]
  set F := g.canonicalize
  let H := (CGraph.mycielskian F).toSimple
  -- Neighbor finset lemmas from Constructions.lean
  have h_neighborFinset_inl : ∀ a : F.V,
      H.neighborFinset (some (Sum.inl a)) =
        (Finset.image (fun b : F.V => some (Sum.inl b)) (F.toSimple.neighborFinset a) ∪
          Finset.image (fun b : F.V => some (Sum.inr b)) (F.toSimple.neighborFinset a)) := by
    intro a; ext y; simp [H, CGraph.mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
    rcases y with _ | y | y <;> simp
  have h_neighborFinset_inr : ∀ a : F.V,
      H.neighborFinset (some (Sum.inr a)) =
        Finset.image (fun b : F.V => some (Sum.inl b)) (F.toSimple.neighborFinset a) ∪ {none} := by
    intro a; ext y; simp [H, CGraph.mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
    rcases y with _ | y | y <;> simp
  have h_neighborFinset_none :
      H.neighborFinset none = Finset.image (fun b : F.V => some (Sum.inr b)) Finset.univ := by
    ext y; simp [H, CGraph.mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
    rcases y with _ | y | y <;> simp
  -- Degree lemmas
  have hinjl : Function.Injective (fun b : F.V => some (Sum.inl b) : F.V → Option (F.V ⊕ F.V)) :=
    fun x y h => Sum.inl_injective (Option.some_injective _ h)
  have hinjr : Function.Injective (fun b : F.V => some (Sum.inr b) : F.V → Option (F.V ⊕ F.V)) :=
    fun x y h => Sum.inr_injective (Option.some_injective _ h)
  have hdeg_inl : ∀ a : F.V, H.degree (some (Sum.inl a)) = 2 * F.toSimple.degree a := by
    intro a
    rw [SimpleGraph.degree, h_neighborFinset_inl, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ hinjl, Finset.card_image_of_injective _ hinjr,
        SimpleGraph.degree]; ring
    · rw [Finset.disjoint_left]; simp [Finset.mem_image]
  have hdeg_inr : ∀ a : F.V, H.degree (some (Sum.inr a)) = F.toSimple.degree a + 1 := by
    intro a
    rw [SimpleGraph.degree, h_neighborFinset_inr, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ hinjl]; rfl
    · simp [Finset.disjoint_singleton_right]
  have hdeg_none : H.degree none = FinEnum.card F.V := by
    rw [SimpleGraph.degree, h_neighborFinset_none, Finset.card_image_of_injective _ hinjr]; simp
  -- Now compute degMultiset.  Unfolding leaves the goal talking about
  -- `(CGraph.mycielskian F).toSimple` and counting with the `Fintype` the graph's own `FinEnum`
  -- induces; the `show` folds the graph back to `H`, and the rewrite moves to Mathlib's `Fintype`
  -- on `Option`, which is the instance the split below is `rfl` for.
  unfold CGraph.degMultiset
  show Multiset.map (fun v => H.degree v) (Finset.univ : Finset (CGraph.mycielskian F).V).val = _
  rw [show (Finset.univ : Finset (CGraph.mycielskian F).V) =
      (Finset.univ : Finset (Option (F.V ⊕ F.V))) from Finset.univ_inst_eq _ _]
  have option_split_FV_FV :
      Multiset.map (fun v => H.degree v) (Finset.univ : Finset (Option (F.V ⊕ F.V))).val =
        [(fun v => H.degree v) none] +
        Multiset.map (fun v => H.degree v) ((Finset.univ : Finset (F.V ⊕ F.V)).map ⟨some,
            Option.some_injective (F.V ⊕ F.V)⟩).val := by
    have : (Finset.univ : Finset (Option (F.V ⊕ F.V))).val =
        none ::ₘ ((Finset.univ : Finset (F.V ⊕ F.V)).map ⟨some, Option.some_injective (F.V ⊕
            F.V)⟩).val := by
      rfl
    rw [this]; simp [Multiset.map_cons]
  rw [option_split_FV_FV]
  -- univ(F.V ⊕ F.V).val = univ(F.V).val.map inl + univ(F.V).val.map inr
  have hsum_univ : (Finset.univ : Finset (F.V ⊕ F.V)).val =
      (Finset.univ : Finset F.V).val.map Sum.inl + (Finset.univ : Finset F.V).val.map Sum.inr := by
    rfl
  simp only [hdeg_none]
  -- Rewrite the Finset.map over Option (F.V ⊕ F.V) to expose inl/inr
  have hmap_split : (Finset.univ : Finset (F.V ⊕ F.V)).map ⟨some, Option.some_injective _⟩ =
      ((Finset.univ : Finset F.V).map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V))) ∪
      ((Finset.univ : Finset F.V).map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V))) := by
    ext x; simp
  have hdisjoint : Disjoint
      ((Finset.univ : Finset F.V).map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V)))
      ((Finset.univ : Finset F.V).map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V))) := by
    rw [Finset.disjoint_left]
    simp
  rw [hmap_split]
  have hcoe_union :
      ((Finset.map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕
          F.V)) Finset.univ ∪
        Finset.map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕
            F.V)) Finset.univ : Finset (Option (F.V ⊕ F.V))).val
      = (Finset.map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V
          ⊕ F.V)) Finset.univ).val +
        (Finset.map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V
            ⊕ F.V)) Finset.univ).val) := by
    set S1 := (Finset.univ : Finset F.V).map (⟨fun a => some (Sum.inl a), fun x y h =>
        by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕ F.V))
    set S2 := (Finset.univ : Finset F.V).map (⟨fun b => some (Sum.inr b), fun x y h =>
        by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕ F.V))
    have : (S1 ∪ S2 : Finset (Option (F.V ⊕ F.V))) = S1.disjUnion S2 hdisjoint := by
      simp [Finset.disjUnion_eq_union]
    rw [this]
    simp [Finset.disjUnion]
  rw [hcoe_union, Multiset.map_add]
  have hmap_inl : Multiset.map (fun v => H.degree v)
      (Finset.map (⟨fun a => some (Sum.inl a), fun x y h => Sum.inl_injective
          (Option.some_injective _ h)⟩ : F.V ↪ Option (F.V ⊕ F.V)) Finset.univ).val =
      Multiset.map (fun a => H.degree (some (Sum.inl a))) Finset.univ.val := by
    simp [Finset.map_val, Multiset.map_map]
  have hmap_inr : Multiset.map (fun v => H.degree v)
      (Finset.map (⟨fun b => some (Sum.inr b), fun x y h => Sum.inr_injective
          (Option.some_injective _ h)⟩ : F.V ↪ Option (F.V ⊕ F.V)) Finset.univ).val =
      Multiset.map (fun b => H.degree (some (Sum.inr b))) Finset.univ.val := by
    simp [Finset.map_val, Multiset.map_map]
  rw [hmap_inl, hmap_inr]
  rw [Multiset.map_congr rfl fun x _ => hdeg_inl x, Multiset.map_congr rfl fun x _ => hdeg_inr x]
  simp only [F]
  simp
  -- What is left is the apex's degree, on the left as the head of the multiset and on the right
  -- as a singleton summand.
  rw [add_comm _ ({FinEnum.card g.V} : Multiset ℕ), Multiset.singleton_add]

/-- The minimum degree of a Mycielskian: the three kinds of vertex give `2δ`, `δ + 1` and `n`. -/
theorem minDeg_mycielskian (G : IsoGraph) (h : 0 < G.V) :
    (mycielskian G).minDeg = min (min (2 * G.minDeg) (G.minDeg + 1)) G.V := by
  induction G using Quotient.inductionOn' with | _ G0
  let H := G0.canonicalize
  have hG : (⟦G0⟧ : IsoGraph) = ⟦H⟧ := (mk_canonicalize G0).symm
  have hmyci : mycielskian (⟦G0⟧ : IsoGraph) = ⟦H.mycielskian⟧ := by
    rw [hG, IsoGraph.mycielskian_mk]
  have hmindeg : (mycielskian (⟦G0⟧ : IsoGraph)).minDeg = H.mycielskian.minDeg := by
    rw [hmyci, minDeg_mk]
  have hv : IsoGraph.V ⟦G0⟧ = FinEnum.card H.V := by
    simp [V_mk, H, CGraph.canonicalize_V]
  rw [hmindeg, hv, minDeg_mk]
  have hmindeg_eq : G0.minDeg = H.minDeg := by
    unfold CGraph.minDeg H
    exact SimpleGraph.Iso.minDegree_eq (CGraph.Iso.toSimpleIso G0.isoCanonicalize)
  rw [hmindeg_eq]
  have hDM_iso := degMultiset_mycielskian ⟦H⟧
  rw [degMultiset_mk] at hDM_iso
  -- `degMultiset_mk` again, to read `(mycielskian ⟦H⟧).degMultiset` as
  -- `H.mycielskian.degMultiset`
  rw [IsoGraph.mycielskian_mk, degMultiset_mk] at hDM_iso
  have hVH : V ⟦H⟧ = FinEnum.card H.V := by simp [IsoGraph.V]
  have hVH_pos : 0 < V ⟦H⟧ := hG.symm ▸ h
  have hHpos : 0 < FinEnum.card H.V := hVH.symm ▸ hVH_pos
  haveI : Nonempty H.V := FinEnum.card_pos_iff.mp hHpos
  have hmin_mem : H.minDeg ∈ H.degMultiset := by
    obtain ⟨v, hv⟩ := H.exists_degree_eq_minDeg (Classical.choice ‹Nonempty H.V›)
    exact CGraph.mem_degMultiset.2 ⟨v, hv⟩
  have hge_min : ∀ d ∈ H.degMultiset, H.minDeg ≤ d := by
    intro d hd
    obtain ⟨v, hv⟩ := CGraph.mem_degMultiset.1 hd
    exact hv ▸ H.minDeg_le_degree v
  have h2min_mem : 2 * H.minDeg ∈ H.mycielskian.degMultiset := by
    rw [hDM_iso]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr
        ⟨H.minDeg, hmin_mem, rfl⟩))))
  have hmin1_mem : H.minDeg + 1 ∈ H.mycielskian.degMultiset := by
    rw [hDM_iso]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr
        ⟨H.minDeg, hmin_mem, rfl⟩))))
  have hcard_mem : FinEnum.card H.V ∈ H.mycielskian.degMultiset := by
    rw [hDM_iso, hVH]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
  have hkmem :
      min (min (2 * H.minDeg) (H.minDeg + 1)) (FinEnum.card H.V) ∈ H.mycielskian.degMultiset := by
    have : min (2 * H.minDeg) (H.minDeg + 1) ∈ H.mycielskian.degMultiset := by
      rcases le_total (2 * H.minDeg) (H.minDeg + 1) with h | h
      · rw [min_eq_left h]
        exact h2min_mem
      · rw [min_eq_right h]
        exact hmin1_mem
    rcases le_total (min (2 * H.minDeg) (H.minDeg + 1)) (FinEnum.card H.V) with h | h
    · rw [min_eq_left h]
      exact this
    · rw [min_eq_right h]
      exact hcard_mem
  have hlower : ∀ d ∈ H.mycielskian.degMultiset, min (min (2 * H.minDeg) (H.minDeg +
      1)) (FinEnum.card H.V) ≤ d := by
    intro d hd
    rw [hDM_iso] at hd
    simp only [Multiset.mem_add, Multiset.mem_map, Multiset.mem_singleton] at hd
    rcases hd with h | h
    · rcases h with h | h
      · -- 2 * a = d
        obtain ⟨a, ha, rfl⟩ := h
        exact min_le_of_left_le (min_le_of_left_le (by linarith [hge_min a ha]))
      · -- a + 1 = d
        obtain ⟨a, ha, hd_eq⟩ := h
        rw [← hd_eq]
        exact min_le_of_left_le (min_le_of_right_le (by linarith [hge_min a ha]))
    · -- d = V ⟦H⟧
      subst h
      exact min_le_right _ _
  exact CGraph.minDeg_eq_of_degMultiset hkmem hlower

/-- In the Mycielskian each original vertex has its degree doubled, each shadow vertex has one
more neighbour than its original, and the apex sees every shadow. -/
@[simp] theorem maxDeg_mycielskian (G : IsoGraph) :
    maxDeg (mycielskian G) = max (2 * maxDeg G) G.V := by
  induction G using Quotient.inductionOn with
  | h g =>
    simp [maxDeg_mk, mycielskian_mk, IsoGraph.V]
    set H : CGraph := g.mycielskian
    set Hs := H.toSimple
    -- Neighbor finset lemmas (copying E_mycielskian proof pattern)
    have h_adj_inl_inl :
        ∀ a b : g.V, Hs.Adj (some (Sum.inl a)) (some (Sum.inl b)) ↔ g.Adj a b = true := by
      intro a b; dsimp [Hs, H, mycielskian, CGraph.toSimple]; tauto
    have h_adj_inl_inr :
        ∀ a b : g.V, Hs.Adj (some (Sum.inl a)) (some (Sum.inr b)) ↔ g.Adj a b = true := by
      intro a b; dsimp [Hs, H, mycielskian, CGraph.toSimple]; tauto
    have h_adj_inl_none : ∀ a : g.V, ¬Hs.Adj (some (Sum.inl a)) none := by
      intro a; dsimp [Hs, H, mycielskian, CGraph.toSimple]; simp
    have h_adj_inr_inl :
        ∀ a b : g.V, Hs.Adj (some (Sum.inr a)) (some (Sum.inl b)) ↔ g.Adj a b = true := by
      intro a b; dsimp [Hs, H, mycielskian, CGraph.toSimple]; tauto
    have h_adj_inr_inr : ∀ a b : g.V, ¬Hs.Adj (some (Sum.inr a)) (some (Sum.inr b)) := by
      intro a b; dsimp [Hs, H, mycielskian, CGraph.toSimple]; simp
    have h_adj_inr_none : ∀ a : g.V, Hs.Adj (some (Sum.inr a)) none := by
      intro a; dsimp [Hs, H, mycielskian, CGraph.toSimple]
    have h_adj_none_inr : ∀ b : g.V, Hs.Adj none (some (Sum.inr b)) := by
      intro b; dsimp [Hs, H, mycielskian, CGraph.toSimple]
    have h_adj_none_inl : ∀ b : g.V, ¬Hs.Adj none (some (Sum.inl b)) := by
      intro b; dsimp [Hs, H, mycielskian, CGraph.toSimple]; simp
    have h_adj_none_none : ¬Hs.Adj none none := by
      dsimp [Hs, H, mycielskian, CGraph.toSimple]; simp
    have h_inl_ne_inr : ∀ (x y : g.V), ¬some (Sum.inl x) = some (Sum.inr y) :=
      fun x y h => by
        injection h with h'
        cases h'
    have h_neighborFinset_inl : ∀ a : g.V,
        Hs.neighborFinset (some (Sum.inl a)) =
          (Finset.image (fun b : g.V => some (Sum.inl b)) (g.toSimple.neighborFinset a) ∪
            Finset.image (fun b : g.V => some (Sum.inr b)) (g.toSimple.neighborFinset a)) := by
      intro a
      ext y
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image]
      rcases y with _ | y
      · simp [h_adj_inl_none a]
      · rcases y with (y | y)
        · rw [h_adj_inl_inl a y]
          simp
          constructor
          · intro h; exact Or.inl ⟨y, h, rfl⟩
          · intro h; rcases h with (⟨b, hb, hb2⟩ | ⟨b, hb, hb2⟩)
            · exact (Sum.inl_injective (Option.some_injective _ hb2)) ▸ hb
            · exact absurd hb2.symm (h_inl_ne_inr y b)
        · rw [h_adj_inl_inr a y]
          simp [CGraph.toSimple]
          constructor
          · intro h; exact Or.inr ⟨y, h, rfl⟩
          · intro h; rcases h with (⟨b, hb, hb2⟩ | ⟨b, hb, hb2⟩)
            · exact absurd hb2 (h_inl_ne_inr b y)
            · exact (Sum.inr_injective (Option.some_injective _ hb2)) ▸ hb
    have h_neighborFinset_inr : ∀ a : g.V,
        Hs.neighborFinset (some (Sum.inr a)) =
          Finset.image (fun b : g.V => some (Sum.inl b)) (g.toSimple.neighborFinset
              a) ∪ {none} := by
      intro a
      ext y
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image,
          Finset.mem_singleton]
      rcases y with _ | y
      · simp [h_adj_inr_none a]
      · rcases y with (y | y)
        · rw [h_adj_inr_inl a y]
          simp
          exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨b, hb, hb2⟩ => (Sum.inl_injective
              (Option.some_injective _ hb2)) ▸ hb⟩
        · show Hs.Adj (some (Sum.inr a)) (some (Sum.inr y)) ↔ _
          simp [h_adj_inr_inr a y, CGraph.toSimple]
          exact fun x _ hx => h_inl_ne_inr x y hx
    have h_neighborFinset_none :
        Hs.neighborFinset none = Finset.image (fun b : g.V => some (Sum.inr b)) Finset.univ := by
      ext y
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
      rcases y with _ | y
      · simp
      · rcases y with (y | y)
        · simp [h_adj_none_inl y]
          intro x; exact fun h => h_inl_ne_inr y x h.symm
        · simp [h_adj_none_inr y]
    -- Injectivity helpers
    have hinjl : Function.Injective (fun b : g.V => some (Sum.inl b) : g.V → H.V) :=
      fun x y h => Sum.inl_injective (Option.some_injective (g.V ⊕ g.V) h)
    have hinjr : Function.Injective (fun b : g.V => some (Sum.inr b) : g.V → H.V) :=
      fun x y h => Sum.inr_injective (Option.some_injective (g.V ⊕ g.V) h)
    -- Degree lemmas
    have hdeg_inl : ∀ a : g.V, Hs.degree (some (Sum.inl a)) = 2 * g.toSimple.degree a := by
      intro a
      rw [SimpleGraph.degree, h_neighborFinset_inl, Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ hinjl, Finset.card_image_of_injective _ hinjr,
            SimpleGraph.degree]
        ring
      · rw [Finset.disjoint_left]; simp [Finset.mem_image]
    have hdeg_inr : ∀ a : g.V, Hs.degree (some (Sum.inr a)) = g.toSimple.degree a + 1 := by
      intro a
      rw [SimpleGraph.degree, h_neighborFinset_inr, Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ hinjl]
        rfl
      · simp [Finset.disjoint_singleton_right]
    have hdeg_none : Hs.degree none = FinEnum.card g.V := by
      rw [SimpleGraph.degree, h_neighborFinset_none]
      rw [Finset.card_image_of_injective _ hinjr]
      simp
    -- Now prove maxDeg ≤ ...
    apply le_antisymm
    · -- All vertices of H have degree ≤ max (2 * maxDeg g) |V(g)|
      apply CGraph.maxDeg_le_of_forall
      intro v
      rcases v with _ | (v | v)
      · rw [hdeg_none]
        exact le_max_of_le_right (le_refl _)
      · rw [hdeg_inl]
        exact le_max_of_le_left (by linarith [CGraph.degree_le_maxDeg g v])
      · rw [hdeg_inr]
        have h1 : g.toSimple.degree v + 1 ≤ FinEnum.card g.V := by
          linarith [CGraph.degree_le_maxDeg g v, @CGraph.maxDeg_lt_card g ⟨v⟩]
        exact le_max_of_le_right h1
    · -- Reverse: max (2 * maxDeg g) |V(g)| ≤ maxDeg H
      have hnone : FinEnum.card g.V ≤ H.maxDeg := by
        rw [← hdeg_none]
        exact CGraph.degree_le_maxDeg H none
      have hinl_maxdeg : 2 * g.maxDeg ≤ H.maxDeg := by
        rcases isEmpty_or_nonempty g.V with hempty | ⟨v₀⟩
        · simp [CGraph.maxDeg, SimpleGraph.maxDegree_of_isEmpty]
        · obtain ⟨v, hv⟩ := CGraph.exists_degree_eq_maxDeg g (v₀.some)
          rw [← hv, ← hdeg_inl]
          exact CGraph.degree_le_maxDeg H (some (Sum.inl v))
      exact max_le hinl_maxdeg hnone

/-- With no isolated vertex every original reaches a shadow, and every shadow reaches the apex. -/
theorem isConnected_mycielskian (G : IsoGraph) (h : 0 < G.minDeg) :
    IsConnected (mycielskian G) := by
  induction G using Quotient.inductionOn with | _ H =>
  classical
  have hH : 0 < H.minDeg := by rwa [minDeg_mk] at h
  rw [mycielskian_mk, isConnected_mk]
  -- Goal: H.mycielskian.IsConnected
  show SimpleGraph.Connected (H.mycielskian.toSimple)
  rw [SimpleGraph.connected_iff]
  have hab : ∀ a : H.V, ∃ b : H.V, H.Adj a b = true := by
    intro a
    have hmin : H.minDeg = H.toSimple.minDegree := rfl
    have hdeg_ge : H.toSimple.minDegree ≤ H.toSimple.degree a :=
      SimpleGraph.minDegree_le_degree _ a
    have hdeg : 0 < H.toSimple.degree a := by omega
    rw [SimpleGraph.degree, Finset.card_pos] at hdeg
    obtain ⟨b, hb⟩ := hdeg
    simp [SimpleGraph.mem_neighborFinset] at hb
    exact ⟨b, hb⟩
  constructor
  · -- Preconnected: everyone reaches everyone via apex `none`
    intro u v
    -- Everyone reaches none, none reaches everyone → everyone reaches everyone
    have hto_apex : ∀ w : (H.mycielskian).V, (H.mycielskian).toSimple.Reachable w none := by
      intro w
      cases w with
      | none => rfl
      | some w =>
        cases w with
        | inl a =>
          obtain ⟨b, hb⟩ := hab a
          show (H.mycielskian.toSimple).Reachable _ _
          have h1 : H.mycielskian.Adj (some (.inl a)) (some (.inr b)) = true := by
            rw [CGraph.mycielskian_adj_inl_inr H a b, hb]
          have h2 : H.mycielskian.Adj (some (.inr
              b)) none = true := CGraph.mycielskian_adj_inr_none H b
          exact ((SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h1)
            (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h2)
                SimpleGraph.Walk.nil)).reachable)
        | inr b =>
          show (H.mycielskian.toSimple).Reachable _ _
          have : H.mycielskian.Adj (some (.inr
              b)) none = true := CGraph.mycielskian_adj_inr_none H b
          exact (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact this)
              SimpleGraph.Walk.nil).reachable
    have h_apex_to : ∀ w : (H.mycielskian).V, (H.mycielskian).toSimple.Reachable none w := by
      intro w
      cases w with
      | none => exact SimpleGraph.Reachable.refl none
      | some w =>
        cases w with
        | inl c =>
          obtain ⟨d, hd⟩ := hab c
          show (H.mycielskian.toSimple).Reachable none _
          have h1 : H.mycielskian.Adj none (some (.inr
              d)) = true := CGraph.mycielskian_adj_none_inr H d
          have h2 : H.mycielskian.Adj (some (.inr d)) (some (.inl c)) = true := by
            rw [CGraph.mycielskian_adj_inr_inl H d c]
            exact (H.symm d c).trans hd
          exact ((SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h1)
            (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h2)
                SimpleGraph.Walk.nil)).reachable)
        | inr b =>
          show (H.mycielskian.toSimple).Reachable none _
          have : H.mycielskian.Adj none (some (.inr
              b)) = true := CGraph.mycielskian_adj_none_inr H b
          exact (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact this)
              SimpleGraph.Walk.nil).reachable
    exact (hto_apex u).trans (h_apex_to v)
  · -- Nonempty
    exact ⟨none⟩

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
  have upper : (CGraph.mycielskian G).matchNum ≤ FinEnum.card G.V := by
    have := CGraph.two_mul_matchNum_le_card (CGraph.mycielskian G)
    rw [CGraph.card_mycielskian] at this
    omega
  have lower : FinEnum.card G.V ≤ (CGraph.mycielskian G).matchNum := by
    show FinEnum.card G.V ≤ (CGraph.lineGraph (CGraph.mycielskian G)).indepNum
    replace h : 2 * (CGraph.lineGraph G).indepNum = FinEnum.card G.V := h
    rw [← h]
    obtain ⟨S, hS_indep, hS_card⟩ := (CGraph.lineGraph G).toSimple.exists_isNIndepSet_indepNum
    -- Key idea: for each edge e={u,v} in S (a matching), add edges (inl u, inr v) and (inl v, inr
    -- u)
    -- to lineGraph(mycielskian G). These 2*|S| edges are pairwise disjoint, forming an indep set of
    -- size 2*|S|.
    -- Build a function from S to lineGraph(mycielskian G).V
    -- For e = ⟨s(u,v), huv⟩ ∈ lineGraph G with s(u,v) ∈ G.toSimple.edgeSet:
    --   f1 e = ⟨s(some (inl u), some (inr v)), edge_mem_cross_inl_inr u v huv.2⟩
    --   f2 e = ⟨s(some (inl v), some (inr u)), edge_mem_cross_inl_inr_symm u v huv.2⟩
    -- T = S.bind (fun e => {f1 e, f2 e})
    -- Need: T.card = 2 * S.card, T.IsIndepSet, then card_le_indepNum.
    have edge_mem_cross_inl_inr : ∀ a b : G.V, G.Adj a b = true →
        Sym2.mk (some (Sum.inl a), some (Sum.inr b)) ∈ (CGraph.mycielskian G).toSimple.edgeSet := by
      intro a b hab
      rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.mycielskian_adj_inl_inr G]
      exact hab
    have edge_mem_cross_inl_inr_symm : ∀ a b : G.V, G.Adj a b = true →
        Sym2.mk (some (Sum.inl b), some (Sum.inr a)) ∈ (CGraph.mycielskian G).toSimple.edgeSet := by
      intro a b hab
      rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, CGraph.mycielskian_adj_inl_inr G b a]
      have := SimpleGraph.Adj.symm (G := G.toSimple) (CGraph.toSimple_adj G a b |>.mp hab)
      exact (CGraph.toSimple_adj G b a).mp this
    -- For each e ∈ S, pick endpoints (u_e, v_e) with e.1 = s(u_e, v_e)
    choose pep hpep using fun e : (CGraph.lineGraph G).V => Sym2.mk_surjective e.1
    let ue : (CGraph.lineGraph G).V → G.V := fun e => (pep e).1
    let ve : (CGraph.lineGraph G).V → G.V := fun e => (pep e).2
    have hueve : ∀ e : (CGraph.lineGraph G).V, e.1 = Sym2.mk (pep e) := fun e => (hpep e).symm
    have hueve' : ∀ e : (CGraph.lineGraph G).V, e.1 = Sym2.mk (ue e, ve e) := fun e => by
      rw [hueve e]
    -- Build T = biUnion S (fun e => {v1 e, v2 e})
    let v1 : (CGraph.lineGraph G).V → (CGraph.lineGraph (CGraph.mycielskian G)).V := fun e =>
      ⟨Sym2.mk (some (Sum.inl (ue e)), some (Sum.inr (ve e))),
       edge_mem_cross_inl_inr (ue e) (ve e) (by
  have he : e.1 ∈ G.toSimple.edgeSet := e.2
  simp [hueve' e] at he
  exact he)⟩
    let v2 : (CGraph.lineGraph G).V → (CGraph.lineGraph (CGraph.mycielskian G)).V := fun e =>
      ⟨Sym2.mk (some (Sum.inl (ve e)), some (Sum.inr (ue e))),
       edge_mem_cross_inl_inr_symm (ue e) (ve e) (by
  have he : e.1 ∈ G.toSimple.edgeSet := e.2
  simp [hueve' e, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at he
  exact he)⟩
    let T : Finset (CGraph.lineGraph (CGraph.mycielskian G)).V := S.biUnion (fun e => {v1 e, v2 e})
    -- Step 1: Show T.card = 2 * S.card
    have hue_ne_ve : ∀ e : (CGraph.lineGraph G).V, ue e ≠ ve e := by
      intro e hne
      have hered : Sym2.IsDiag e.1 := by
        rw [hueve' e, hne]
        simp [Sym2.IsDiag]
      exact SimpleGraph.not_isDiag_of_mem_edgeSet G.toSimple e.2 hered
    have hv1ne_v2 : ∀ e ∈ S, v1 e ≠ v2 e := by
      intro e he heq
      have := Subtype.ext_iff.mp heq
      simp [v1, v2] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hue_ne_ve e (Sum.inl_injective (Option.some_injective (Sum G.V G.V) h1))
      · have := Option.some_injective (Sum G.V G.V) h1
        exact absurd this Sum.inl_ne_inr
    -- Pairwise disjointness of {v1 e, v2 e} over e ∈ S
    -- e.1 and f.1 are disjoint for e ≠ f in S (edges in a matching)
    have hdisco : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e.1.toFinset f.1.toFinset := by
      intro e he f hf hef
      exact CGraph.disjoint_of_not_adj_lineGraph G hef (hS_indep (by simpa using he)
          (by simpa using hf) hef)
    have he1_ne_he2 := hue_ne_ve
    -- Helper: if Sym2.mk (some (inl a), some (inr b)) = Sym2.mk (some (inl a'), some (inr b')),
    -- then a = a' and b = b'
    have sym2_inl_inr_inj : ∀ a b a' b' : G.V,
        Sym2.mk (some (Sum.inl a), some (Sum.inr b)) = Sym2.mk (some (Sum.inl a'), some (Sum.inr
            b')) →
        a = a' ∧ b = b' := by
      intro a b a' b' h
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Sum.inl_injective (Option.some_injective (Sum G.V G.V) h1), Sum.inr_injective
          (Option.some_injective (Sum G.V G.V) h2)⟩
      · exact absurd (Option.some_injective (Sum G.V G.V) h1) Sum.inl_ne_inr
    -- Extract component equalities from v1/v2 equalities via sym2_inl_inr_inj
    have eq_v1_v1 : ∀ e f : (CGraph.lineGraph G).V, v1 e = v1 f → ue e = ue f ∧ ve e = ve f := by
      intro e f heq
      have h1 : Sym2.mk (some (Sum.inl (ue e)), some (Sum.inr (ve e))) =
          Sym2.mk (some (Sum.inl (ue f)), some (Sum.inr (ve f))) := congrArg Subtype.val heq
      exact sym2_inl_inr_inj _ _ _ _ h1
    have eq_v2_v2 : ∀ e f : (CGraph.lineGraph G).V, v2 e = v2 f → ve e = ve f ∧ ue e = ue f := by
      intro e f heq
      have h1 : Sym2.mk (some (Sum.inl (ve e)), some (Sum.inr (ue e))) =
          Sym2.mk (some (Sum.inl (ve f)), some (Sum.inr (ue f))) := congrArg Subtype.val heq
      exact sym2_inl_inr_inj _ _ _ _ h1
    have eq_v1_v2 : ∀ e f : (CGraph.lineGraph G).V, v1 e = v2 f → ue e = ve f ∧ ve e = ue f := by
      intro e f heq
      have h1 : Sym2.mk (some (Sum.inl (ue e)), some (Sum.inr (ve e))) =
          Sym2.mk (some (Sum.inl (ve f)), some (Sum.inr (ue f))) := congrArg Subtype.val heq
      exact sym2_inl_inr_inj _ _ _ _ h1
    have eq_v2_v1 : ∀ e f : (CGraph.lineGraph G).V, v2 e = v1 f → ve e = ue f ∧ ue e = ve f := by
      intro e f heq
      have h1 : Sym2.mk (some (Sum.inl (ve e)), some (Sum.inr (ue e))) =
          Sym2.mk (some (Sum.inl (ue f)), some (Sum.inr (ve f))) := congrArg Subtype.val heq
      exact sym2_inl_inr_inj _ _ _ _ h1
    have edge_eq_of_val_eq : ∀ e f : (CGraph.lineGraph
        G).V, e.1 = f.1 → e = f := fun e f h => Subtype.ext h
    have hv1_ne_v1 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → v1 e ≠ v1 f := by
      intro e he f hf hef heq
      have ⟨heu, hev⟩ := eq_v1_v1 e f heq
      have : e.1 = f.1 := by rw [hueve' e, hueve' f, heu, hev]
      exact hef (edge_eq_of_val_eq e f this)
    have hv1_ne_v2 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → v1 e ≠ v2 f := by
      intro e he f hf hef heq
      have ⟨heu, hev⟩ := eq_v1_v2 e f heq
      have : e.1 = f.1 := by
        rw [hueve' e, hueve' f, heu, hev]
        exact (Quot.sound (Sym2.Rel.swap (ue f) (ve f))).symm
      exact hef (edge_eq_of_val_eq e f this)
    have hv2_ne_v1 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → v2 e ≠ v1 f := by
      intro e he f hf hef heq
      have ⟨heu, hev⟩ := eq_v2_v1 e f heq
      have : e.1 = f.1 := by
        rw [hueve' e, hueve' f, heu, hev]
        exact (Quot.sound (Sym2.Rel.swap (ue f) (ve f))).symm
      exact hef (edge_eq_of_val_eq e f this)
    have hv2_ne_v2 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → v2 e ≠ v2 f := by
      intro e he f hf hef heq
      have ⟨heu, hev⟩ := eq_v2_v2 e f heq
      have : e.1 = f.1 := by rw [hueve' e, hueve' f, heu, hev]
      exact hef (edge_eq_of_val_eq e f this)
    have hdisj : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint ({v1 e, v2 e} : Finset (CGraph.lineGraph
        (CGraph.mycielskian G)).V) ({v1 f, v2 f} : Finset (CGraph.lineGraph (CGraph.mycielskian
            G)).V) := by
      intro e he f hf hef
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx1 | hx2
      · rcases hy with hy1 | hy2
        · exact absurd (hx1.symm.trans hy1) (hv1_ne_v1 e he f hf hef)
        · exact absurd (hx1.symm.trans hy2) (hv1_ne_v2 e he f hf hef)
      · rcases hy with hy1 | hy2
        · exact absurd (hx2.symm.trans hy1) (hv2_ne_v1 e he f hf hef)
        · exact absurd (hx2.symm.trans hy2) (hv2_ne_v2 e he f hf hef)
    have hT_card : T.card = 2 * S.card := by
      have hcard_pair : ∀ e ∈ S, ({v1 e, v2 e} : Finset (CGraph.lineGraph (CGraph.mycielskian
          G)).V).card = 2 := by
        intro e he
        rw [Finset.card_pair (hv1ne_v2 e he)]
      rw [Finset.card_biUnion (fun e he f hf hef => hdisj e he f hf hef)]
      rw [Finset.sum_congr rfl hcard_pair, Finset.sum_const, smul_eq_mul, mul_comm]
    -- Step 3: Show T is independent in lineGraph(mycielskian G)
    have hT_mem : ∀ x, x ∈ (T : Set (CGraph.lineGraph (CGraph.mycielskian G)).V) →
        ∃ e ∈ S, x = v1 e ∨ x = v2 e := by
      simp [T, Finset.coe_biUnion]
    -- Endpoint disjointness helpers
    have hnd_same : ∀ e ∈ S,
        ∀ w : Option (G.V ⊕ G.V), w ∉ (v1 e).1 ∨ w ∉ (v2 e).1 := by
      intro e heS w
      unfold v1 v2
      simp only []
      by_contra h
      push_neg at h
      obtain ⟨hw1, hw2⟩ := h
      rcases Sym2.mem_iff.mp hw1 with h1 | h1 <;> rcases Sym2.mem_iff.mp hw2 with h2 | h2
      · -- h1: w = some (inl (ue e)), h2: w = some (inl (ve e))
        have := Option.some_injective (Sum G.V G.V) (h1.symm.trans h2)
        exact he1_ne_he2 e (Sum.inl_injective this)
      · -- h1: inl (ue e), h2: inr (ue e)
        have heq : Sum.inl (ue e) = Sum.inr (ue e) := Option.some_injective (Sum G.V
            G.V) (h1.symm.trans h2)
        exact Sum.inl_ne_inr heq
      · -- h1: inr (ve e), h2: inl (ve e)
        have heq : Sum.inl (ve e) = Sum.inr (ve e) := Option.some_injective (Sum G.V
            G.V) (h2.symm.trans h1)
        exact absurd heq Sum.inl_ne_inr
      · -- h1: inr (ve e), h2: inr (ue e)
        have := Option.some_injective (Sum G.V G.V) (h1.symm.trans h2)
        exact he1_ne_he2 e (Sum.inr_injective this).symm
    -- Endpoint elements of v1/v2
    have hve1 : ∀ e ∈ S, (v1 e).1 = Sym2.mk (some (Sum.inl (ue e)), some (Sum.inr (ve e))) := by
      intro e he; simp [v1]
    have hve2 : ∀ e ∈ S, (v2 e).1 = Sym2.mk (some (Sum.inl (ve e)), some (Sum.inr (ue e))) := by
      intro e he; simp [v2]
    -- Disjointness of endpoint Finsets in G.V
    have hdisco_finset : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ue e ≠ ue f ∧ ue e ≠ ve f ∧ ve e ≠ ue f ∧ ve e ≠ ve f := by
      intro e heS f hfS hef
      have hd := hdisco e heS f hfS hef
      have he1 : e.1 = Sym2.mk (ue e, ve e) := hueve' e
      have hf1 : f.1 = Sym2.mk (ue f, ve f) := hueve' f
      have hm1 : (ue
          e) ∈ e.1.toFinset := by rw [he1]; exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)
      have hm2 : (ve
          e) ∈ e.1.toFinset := by rw [he1]; exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _)
      have hm3 : (ue
          f) ∈ f.1.toFinset := by rw [hf1]; exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)
      have hm4 : (ve
          f) ∈ f.1.toFinset := by rw [hf1]; exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _)
      exact ⟨fun h => Finset.disjoint_left.mp hd hm1 (h ▸ hm3),
             fun h => Finset.disjoint_left.mp hd hm1 (h ▸ hm4),
             fun h => Finset.disjoint_left.mp hd hm2 (h ▸ hm3),
             fun h => Finset.disjoint_left.mp hd hm2 (h ▸ hm4)⟩
    -- Cross endpoint disjointness for Option level
    -- Helper for inl=inr contradictions
    have h_inl_inr_absurd : ∀ {a b : G.V}, Sum.inl a = Sum.inr b → False :=
      Sum.inl_ne_inr
    have hnd_cross : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ w : Option (G.V ⊕ G.V), w ∉ (v1 e).1 ∨ w ∉ (v1 f).1 := by
      intro e heS f hfS hef w
      rw [hve1 e heS, hve1 f hfS]
      by_contra h; push_neg at h
      obtain ⟨hw1, hw2⟩ := h
      rcases Sym2.mem_iff.mp hw1 with h1 | h1 <;> rcases Sym2.mem_iff.mp hw2 with h2 | h2
      · exact hdisco_finset e heS f hfS hef |>.1 (Sum.inl_injective (Option.some_injective (Sum G.V
          G.V) (h1.symm.trans h2)))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h1.symm.trans h2))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h2.symm.trans h1))
      · exact hdisco_finset e heS f hfS hef |>.2.2.2 (Sum.inr_injective (Option.some_injective (Sum
          G.V G.V) (h1.symm.trans h2)))
    have hnd_cross2 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ w : Option (G.V ⊕ G.V), w ∉ (v1 e).1 ∨ w ∉ (v2 f).1 := by
      intro e heS f hfS hef w
      rw [hve1 e heS, hve2 f hfS]
      by_contra h; push_neg at h
      obtain ⟨hw1, hw2⟩ := h
      rcases Sym2.mem_iff.mp hw1 with h1 | h1 <;> rcases Sym2.mem_iff.mp hw2 with h2 | h2
      · exact hdisco_finset e heS f hfS hef |>.2.1 (Sum.inl_injective (Option.some_injective (Sum
          G.V G.V) (h1.symm.trans h2)))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h1.symm.trans h2))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h2.symm.trans h1))
      · exact hdisco_finset e heS f hfS hef |>.2.2.1 (Sum.inr_injective (Option.some_injective (Sum
          G.V G.V) (h1.symm.trans h2)))
    have hnd_cross3 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ w : Option (G.V ⊕ G.V), w ∉ (v2 e).1 ∨ w ∉ (v1 f).1 := by
      intro e heS f hfS hef w
      rw [hve2 e heS, hve1 f hfS]
      by_contra h; push_neg at h
      obtain ⟨hw1, hw2⟩ := h
      rcases Sym2.mem_iff.mp hw1 with h1 | h1 <;> rcases Sym2.mem_iff.mp hw2 with h2 | h2
      · exact hdisco_finset e heS f hfS hef |>.2.2.1 (Sum.inl_injective (Option.some_injective (Sum
          G.V G.V) (h1.symm.trans h2)))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h1.symm.trans h2))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h2.symm.trans h1))
      · exact hdisco_finset e heS f hfS hef |>.2.1 (Sum.inr_injective (Option.some_injective (Sum
          G.V G.V) (h1.symm.trans h2)))
    have hnd_cross4 : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
        ∀ w : Option (G.V ⊕ G.V), w ∉ (v2 e).1 ∨ w ∉ (v2 f).1 := by
      intro e heS f hfS hef w
      rw [hve2 e heS, hve2 f hfS]
      by_contra h; push_neg at h
      obtain ⟨hw1, hw2⟩ := h
      rcases Sym2.mem_iff.mp hw1 with h1 | h1 <;> rcases Sym2.mem_iff.mp hw2 with h2 | h2
      · exact hdisco_finset e heS f hfS hef |>.2.2.2 (Sum.inl_injective (Option.some_injective (Sum
          G.V G.V) (h1.symm.trans h2)))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h1.symm.trans h2))
      · exact h_inl_inr_absurd (Option.some_injective (Sum G.V G.V) (h2.symm.trans h1))
      · exact hdisco_finset e heS f hfS hef |>.1 (Sum.inr_injective (Option.some_injective (Sum G.V
          G.V) (h1.symm.trans h2)))
    have hT_indep : (CGraph.lineGraph (CGraph.mycielskian G)).toSimple.IsIndepSet (T : Set
        (CGraph.lineGraph (CGraph.mycielskian G)).V) := by
      intro x hx y hy hxy
      rw [CGraph.toSimple_adj, CGraph.lineGraph_adj]
      simp [hxy]
      obtain ⟨e, heS, hx'⟩ := hT_mem x hx
      obtain ⟨f, hfS, hy'⟩ := hT_mem y hy
      rcases hx' with rfl | rfl
      · rcases hy' with rfl | rfl
        · intro w hw
          by_cases hef : e = f
          · subst hef; exact absurd rfl hxy
          · rcases hnd_cross e heS f hfS hef w with h | h <;> [exact absurd hw h; exact h]
        · intro w hw
          by_cases hef : e = f
          · subst hef; rcases hnd_same e heS w with h | h <;> [exact absurd hw h; exact h]
          · rcases hnd_cross2 e heS f hfS hef w with h | h <;> [exact absurd hw h; exact h]
      · rcases hy' with rfl | rfl
        · intro w hw
          by_cases hef : e = f
          · subst hef; rcases hnd_same e heS w with h | h <;> [exact h; exact absurd hw h]
          · rcases hnd_cross3 e heS f hfS hef w with h | h <;> [exact absurd hw h; exact h]
        · intro w hw
          by_cases hef : e = f
          · subst hef; exact absurd rfl hxy
          · rcases hnd_cross4 e heS f hfS hef w with h | h <;> [exact absurd hw h; exact h]
    have hle : T.card ≤ (CGraph.lineGraph (CGraph.mycielskian
        G)).indepNum := hT_indep.card_le_indepNum
    rw [hT_card] at hle
    have hLG : G.lineGraph.indepNum = G.lineGraph.toSimple.indepNum := by rfl
    rw [hLG] at ⊢
    rw [hS_card] at hle
    exact hle
  exact le_antisymm upper lower

/-- All `n` shadows are pairwise non-adjacent. -/
theorem V_le_indepNum_mycielskian (G : IsoGraph) : G.V ≤ (mycielskian G).indepNum := by
  induction G using Quotient.inductionOn with
  | h g =>
    simp [V, indepNum, mycielskian]
    -- Goal: FinEnum.card g.V ≤ g.mycielskian.indepNum
    -- The shadows form an independent set of size FinEnum.card g.V
    let n := FinEnum.card g.V
    let shadows : Finset (CGraph.mycielskian g).V := Finset.image (some ∘
        Sum.inr) Finset.univ
    have hind : (CGraph.mycielskian g).toSimple.IsIndepSet (shadows : Set _) := by
      intro x hx y hy hne hadj
      simp [shadows] at hx hy
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      subst hi hj
      simp [CGraph.toSimple_adj] at hadj
    have hcard : shadows.card = n := by
      have hinj : Function.Injective (some ∘ Sum.inr : g.V → (CGraph.mycielskian g).V) := by
        intro a b h
        have := Option.some_injective _ h
        exact Sum.inr_injective this
      simp [shadows, Finset.card_image_of_injective _ hinj]
      rfl
    show n ≤ (CGraph.mycielskian g).indepNum
    exact hcard ▸ hind.card_le_indepNum

/-- An independent set of `μ G` meets the shadows in at most everything and the original copy in
an independent set. -/
theorem indepNum_mycielskian_le (G : IsoGraph) (hV : 0 < G.V) :
    (mycielskian G).indepNum ≤ G.V + G.indepNum := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g] at *
    simp only [indepNum_mk, V_mk]
    rw [mycielskian_mk, indepNum_mk]
    set G' := g.canonicalize
    set n := FinEnum.card G'.V

    -- Helper embeddings
    let inlEmb : G'.V → (G'.mycielskian).V := fun a => some (Sum.inl a)
    let inrEmb : G'.V → (G'.mycielskian).V := fun a => some (Sum.inr a)
    have hinl_inj : Function.Injective inlEmb := by
      intro a b h; exact Sum.inl_injective (Option.some_injective _ h)
    have hinr_inj : Function.Injective inrEmb := by
      intro a b h; exact Sum.inr_injective (Option.some_injective _ h)
    have hinl_adj : ∀ a b : G'.V, (G'.mycielskian).Adj (inlEmb a) (inlEmb b) = G'.Adj a b := by
      intro a b; rfl
    have hnone_inr_adj : ∀ a : G'.V, (G'.mycielskian).Adj none (inrEmb a) = true := by
      intro a; rfl
    -- inr vertices are pairwise non-adjacent in μG'
    have hinr_not_adj : ∀ a b : G'.V, (G'.mycielskian).Adj (inrEmb a) (inrEmb b) = false := by
      intro a b; simp [inrEmb, CGraph.mycielskian_adj_inr_inr]
    --key: any indep set s of μG' has |s| ≤ n + α(G')
    have key : ∀ (s : Finset ((G'.mycielskian).V)), (G'.mycielskian).toSimple.IsIndepSet (↑s) →
        s.card ≤ n + G'.indepNum := by
      intro s hs_ind
      -- The inl-vertices of s, as a Finset of G'.V
      let A : Finset G'.V := Finset.univ.filter (fun a => inlEmb a ∈ s)
      -- The inr-vertices of s, as a Finset of G'.V  
      let B : Finset G'.V := Finset.univ.filter (fun a => inrEmb a ∈ s)
      -- Key facts about A and B
      -- A is an indep set in G'
      have hA_indep : G'.toSimple.IsIndepSet (A : Set G'.V) := by
        intro a ha b hb hab
        simp [A] at ha hb
        intro hadj
        have hnot_adj := hs_ind ha hb (hinl_inj.ne hab)
        simp [CGraph.toSimple_adj] at hnot_adj
        rw [hinl_adj] at hnot_adj
        simp [CGraph.toSimple_adj] at hadj
        simp [hnot_adj] at hadj
      have hA_card : A.card ≤ G'.indepNum := hA_indep.card_le_indepNum
      -- B.card ≤ n
      have hB_card : B.card ≤ n := by
        have : B.card ≤ FinEnum.card G'.V := FinEnum.card_le B
        exact this
      -- The inlEmb image of A has size |A|
      have himage_inl : (Finset.image inlEmb
          A).card = A.card := Finset.card_image_of_injective _ hinl_inj
      -- The inrEmb image of B has size |B|
      have himage_inr : (Finset.image inrEmb
          B).card = B.card := Finset.card_image_of_injective _ hinr_inj
      -- none is not in any inlEmb or inrEmb image
      have hnone_not_inl : none ∉ Finset.image inlEmb A := by simp [inlEmb]
      have hnone_not_inr : none ∉ Finset.image inrEmb B := by simp [inrEmb]
      -- inlEmb images and inrEmb images are disjoint
      have hdisl : Disjoint (Finset.image inlEmb A) (Finset.image inrEmb B) := by
        rw [Finset.disjoint_left]
        intro v hvl hvr
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hvl
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hvr
        simp [inlEmb, inrEmb] at hb
        have := Option.some_injective _ hb
        exact Sum.inl_ne_inr this.symm
      -- Case split on none ∈ s
      -- Subset relations
      have hs_sub_caseA : none ∈ s → s ⊆ {none} ∪ Finset.image inlEmb A := by
        intro hnone v hv
        cases v with
        | none => simp
        | some x =>
          cases x with
          | inl a =>
            have : some (Sum.inl a) ∈ Finset.image inlEmb A := by
              simp [Finset.mem_image, A]
              exact ⟨a, hv, rfl⟩
            rw [Finset.mem_union]
            exact Or.inr this
          | inr a =>
            exfalso
            have hne : (none : G'.mycielskian.V) ≠ some (Sum.inr a) := by simp
            have := hs_ind hnone hv hne
            simp [inrEmb, hnone_inr_adj a] at this
      have hs_sub_caseB : none ∉ s → s ⊆ Finset.image inlEmb A ∪ Finset.image inrEmb B := by
        intro hnone v hv
        cases v with
        | none => exact absurd hv hnone
        | some x =>
          cases x with
          | inl a =>
            have : some (Sum.inl a) ∈ Finset.image inlEmb A := by
              simp [Finset.mem_image, A]
              exact ⟨a, hv, rfl⟩
            rw [Finset.mem_union]
            exact Or.inl this
          | inr a =>
            have : some (Sum.inr a) ∈ Finset.image inrEmb B := by
              simp [Finset.mem_image, B]
              exact ⟨a, hv, rfl⟩
            rw [Finset.mem_union]
            exact Or.inr this
      -- B = ∅ when none ∈ s
      have hB_empty : none ∈ s → B = ∅ := by
        intro hnone
        ext a; simp [B]
        intro ha_mem
        exfalso
        have hne : (none : G'.mycielskian.V) ≠ some (Sum.inr a) := by simp
        have := hs_ind hnone ha_mem hne
        simp [inrEmb, hnone_inr_adj a] at this
      -- Case split on none ∈ s
      by_cases hnone : none ∈ s
      · have hs_subA := hs_sub_caseA hnone
        have hcard : s.card ≤ 1 + A.card := by
          calc s.card ≤ ({none} ∪ Finset.image inlEmb A).card := Finset.card_le_card hs_subA
            _ = 1 + A.card := by
              rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hnone_not_inl)]
              simp [himage_inl]
        have hn : 0 < n := hV
        omega
      · have hs_subB' := hs_sub_caseB hnone
        have hcardB' : s.card ≤ A.card + B.card := by
          calc s.card ≤ (Finset.image inlEmb A ∪ Finset.image inrEmb B).card :=
              Finset.card_le_card hs_subB'
            _ = A.card + B.card := by
              rw [Finset.card_union_of_disjoint hdisl, himage_inl, himage_inr]
        linarith

    have goal : (CGraph.mycielskian G').indepNum ≤ n + G'.indepNum := by
      unfold CGraph.indepNum
      rw [SimpleGraph.indepNum]
      have hbdd : BddAbove {n | ∃ s : Finset ((G'.mycielskian).V),
          (G'.mycielskian).toSimple.IsNIndepSet n s} :=
        ⟨Fintype.card _, fun k ⟨s, hs⟩ => by
          rw [← hs.card_eq]
          exact Finset.card_le_univ s⟩
      apply csSup_le'
      · intro k hk
        obtain ⟨s, hs⟩ := hk
        rcases hs with ⟨hs_ind, hs_card⟩
        rw [← hs_card]
        unfold CGraph.indepNum at key
        exact key s hs_ind
    exact goal


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

/-- The `|V(G)|` shadows are an independent set, so the complementary cover is small. -/
theorem coverNum_mycielskian_le (G : IsoGraph) : (mycielskian G).coverNum ≤ G.V + 1 := by
  have h1 := coverNum_add_indepNum (mycielskian G)
  have h2 := V_le_indepNum_mycielskian G
  rw [V_mycielskian] at h1
  omega

/-- Covering `μ G` costs at least one more than covering `G`. -/
theorem coverNum_lt_coverNum_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    G.coverNum + 1 ≤ (mycielskian G).coverNum := by
  have h1 := coverNum_add_indepNum (mycielskian G)
  have h2 := coverNum_add_indepNum G
  have h3 := indepNum_mycielskian_le G hV
  rw [V_mycielskian] at h1
  omega

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

/-- An odd circulant with a nonzero connection is not bipartite, so it has a cycle. -/
theorem not_isAcyclic_circulant_of_odd {n : ℕ} {S : List ℕ} (hn : n % 2 = 1) (d : ℕ) (hd : d ∈ S)
    (h0 : 0 < d) (hdn : d < n) : ¬ IsAcyclic (circulant n S) :=
  not_isAcyclic_of_not_isBipartite (not_isBipartite_circulant_of_odd hn d hd h0 hdn)

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

/-- A bipartite graph with a near-perfect matching has the largest independent set its vertex
count allows: one colour class already has `⌈|V| / 2⌉` vertices, and the matching stops anything
bigger. -/
theorem indepNum_of_isBipartite_of_matchNum {G : IsoGraph} (h : IsBipartite G) (hE : 0 < G.E)
    (hm : G.V ≤ 2 * G.matchNum + 1) : G.indepNum = (G.V + 1) / 2 := by
  have hlb := V_le_chromNum_mul_indepNum G
  rw [chromNum_eq_two_iff.mpr ⟨h, hE⟩] at hlb
  have hsum := coverNum_add_indepNum G
  have hcov := matchNum_le_coverNum G
  have h2 := two_mul_matchNum_le_V G
  omega

/-- The complementary statement: the cover takes the other half. -/
theorem coverNum_of_isBipartite_of_matchNum {G : IsoGraph} (h : IsBipartite G) (hE : 0 < G.E)
    (hm : G.V ≤ 2 * G.matchNum + 1) : G.coverNum = G.V / 2 := by
  have h1 := indepNum_of_isBipartite_of_matchNum h hE hm
  have hsum := coverNum_add_indepNum G
  omega

/-- The odd prism misses one vertex of a perfect independent set, so its cover needs one more. -/
theorem coverNum_prism_odd (m : ℕ) : (prism (2 * m + 3)).coverNum = 2 * m + 4 := by
  have h1 := indepNum_prism_odd m
  have h2 := coverNum_add_indepNum (prism (2 * m + 3))
  rw [V_prism] at h2
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

/-- Greedy colouring bounds the clique number too, since `ω ≤ χ ≤ Δ + 1`. -/
theorem cliqueNum_le_maxDeg_add_one (G : IsoGraph) : G.cliqueNum ≤ maxDeg G + 1 :=
  le_trans (cliqueNum_le_chromNum G) (chromNum_le_maxDeg_add_one G)

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
