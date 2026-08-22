import IsoGraph.SmallGraphs.Circulants
import Mathlib.Combinatorics.SetFamily.KruskalKatona

/-!
# The Kneser graphs, by Erdős–Ko–Rado

`kneser n k` is the graph on the `k`-subsets of `Fin n` in which two subsets are adjacent when
they are disjoint.  Three of its invariants are settled here, all of them out of the *stars*: for
`i : Fin n`, the star `kneserStar n k i` is the family of `k`-sets through `i`, an independent set
of `K(n, k)` of size `C(n - 1, k - 1)` and a clique of the complement, and the `n` stars cover
each vertex exactly `k` times.

* `indepNum_kneser` — `α(K(n, k)) = C(n - 1, k - 1)` for `2k ≤ n`.  A star is one extremal
  family; that no larger one exists is the Erdős–Ko–Rado theorem, `Finset.erdos_ko_rado`.
* `fracChromNum_kneser` — `χ_f(K(n, k)) = n / k` for `2k ≤ n`.  The stars, each weighted `1 / k`,
  are a fractional clique cover of weight `n / k`; the matching lower bound is `|V| / α` with the
  two counts `C(n, k)` and `C(n - 1, k - 1)`.
* `chromNum_kneser_two_mul` and `chromNum_kneser_two_mul_add_one` — `χ(K(2k, k)) = 2` and
  `χ(K(2k + 1, k)) = 3`.

The last two are the cases of the **Lovász–Kneser theorem** `χ(K(n, k)) = n - 2k + 2` that the
fractional value settles: `χ ≥ ⌈χ_f⌉ = ⌈n / k⌉` agrees with `n - 2k + 2` exactly when
`n ∈ {2k, 2k + 1}` (or `k = 1`).  Beyond that the theorem needs the Borsuk–Ulam theorem, which
Mathlib does not have; the upper bound `chromNum_kneser_le` holds for every `n` and `k`.
-/

namespace CGraph

variable {n k : ℕ}

/-! ### The stars -/

/-- The *star* at `i`: the `k`-subsets of `Fin n` that contain `i`. -/
def kneserStar (n k : ℕ) (i : Fin n) : Finset (kneser n k).V :=
  Finset.univ.filter fun A ↦ i ∈ A.1

@[simp] theorem mem_kneserStar {i : Fin n} {A : (kneser n k).V} :
    A ∈ kneserStar n k i ↔ i ∈ A.1 := by
  simp [kneserStar]

/-- Deleting `i` matches the star at `i` with the `(k-1)`-subsets of the other `n - 1` points. -/
theorem card_kneserStar (hk : 0 < k) (i : Fin n) :
    (kneserStar n k i).card = (n - 1).choose (k - 1) := by
  classical
  have h : (kneserStar n k i).card =
      (Finset.powersetCard (k - 1) (Finset.univ.erase i)).card := by
    refine Finset.card_nbij (fun A ↦ A.1.erase i) ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_coe, mem_kneserStar] at hA
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset_erase _ (Finset.subset_univ _),
        by rw [Finset.card_erase_of_mem hA, A.2]⟩
    · intro A hA B hB hAB
      rw [Finset.mem_coe, mem_kneserStar] at hA hB
      refine Subtype.ext ?_
      rw [← Finset.insert_erase hA, ← Finset.insert_erase hB]
      exact congrArg (insert i) hAB
    · intro B hB
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hB
      have hiB : i ∉ B := fun h ↦ (Finset.mem_erase.1 (hB.1 h)).1 rfl
      have hcard : (insert i B).card = k := by
        rw [Finset.card_insert_of_notMem hiB, hB.2]; omega
      refine ⟨⟨insert i B, hcard⟩, ?_, ?_⟩
      · rw [Finset.mem_coe, mem_kneserStar]
        exact Finset.mem_insert_self i B
      · exact Finset.erase_insert hiB
  rw [h, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-! ### The independence number

An independent set of `K(n, k)` is an intersecting family of `k`-sets, so `α` is exactly what the
Erdős–Ko–Rado theorem bounds. -/

theorem indepNum_kneser_le (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneser n k).indepNum ≤ (n - 1).choose (k - 1) := by
  classical
  obtain ⟨S, hS⟩ := (kneser n k).toSimple.exists_isNIndepSet_indepNum
  have himg : (S.image Subtype.val).card = S.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hint : ((S.image Subtype.val : Finset (Finset (Fin n))) :
      Set (Finset (Fin n))).Intersecting := by
    intro A hA B hB hdisj
    rw [Finset.mem_coe, Finset.mem_image] at hA hB
    obtain ⟨a, ha, rfl⟩ := hA
    obtain ⟨b, hb, rfl⟩ := hB
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    by_cases hab : a = b
    · subst hab
      rw [Finset.inter_self] at hdisj
      have hcard := a.2
      rw [hdisj, Finset.card_empty] at hcard
      omega
    · have hadj : (kneser n k).Adj a b = true := by
        simp [kneser_adj, hab, hdisj]
      exact hS.isIndepSet ha hb hab ((toSimple_adj _ _ _).2 hadj)
  have hsz : ((S.image Subtype.val : Finset (Finset (Fin n))) :
      Set (Finset (Fin n))).Sized k := by
    intro A hA
    rw [Finset.mem_coe, Finset.mem_image] at hA
    obtain ⟨a, _, rfl⟩ := hA
    exact a.2
  have hekr := Finset.erdos_ko_rado hint hsz (by omega)
  rw [himg, hS.card_eq] at hekr
  exact hekr

theorem le_indepNum_kneser (hk : 0 < k) (hn : 0 < n) :
    (n - 1).choose (k - 1) ≤ (kneser n k).indepNum := by
  classical
  have hind : (kneser n k).toSimple.IsIndepSet
      (↑(kneserStar n k ⟨0, hn⟩) : Set (kneser n k).V) := by
    intro u hu v hv huv hadj
    rw [Finset.mem_coe, mem_kneserStar] at hu hv
    rw [toSimple_adj, kneser_adj] at hadj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hadj
    have hmem : (⟨0, hn⟩ : Fin n) ∈ u.1 ∩ v.1 := Finset.mem_inter.2 ⟨hu, hv⟩
    rw [hadj.2] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  have h := hind.card_le_indepNum
  rwa [card_kneserStar hk] at h

/-- **The Erdős–Ko–Rado theorem**, as the independence number of a Kneser graph: for `2k ≤ n` an
intersecting family of `k`-subsets of an `n`-set is no larger than a star. -/
@[toIsoGraph]
theorem indepNum_kneser (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneser n k).indepNum = (n - 1).choose (k - 1) :=
  le_antisymm (indepNum_kneser_le hk h) (le_indepNum_kneser hk (by omega))

/-! ### The fractional chromatic number -/

/-- **`χ_f(K(n, k)) = n / k`.**  The `n` stars, each weighted `1 / k`, are a fractional clique
cover: a star is a clique of the complement, and each `k`-set lies in exactly `k` of them.  That
gives `χ_f ≤ n / k`, and `|V| / α = C(n, k) / C(n - 1, k - 1)` is the same number. -/
theorem fracChromNum_kneser (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneser n k).fracChromNum = (n : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine le_antisymm ?_ ?_
  · have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [fracChromNum_eq_compl]
    refine le_trans (fracIndepNum_le_of_cover (G := (kneser n k)ᶜ) (kneserStar n k)
      (fun _ ↦ (1 / k : ℚ)) (fun _ ↦ by positivity) ?_ ?_) (le_of_eq ?_)
    · intro i _ u hu v hv huv
      have hu' := mem_kneserStar.1 hu
      have hv' := mem_kneserStar.1 hv
      have hne : u.1 ∩ v.1 ≠ ∅ := by
        intro hemp
        have hmem : i ∈ u.1 ∩ v.1 := Finset.mem_inter.2 ⟨hu', hv'⟩
        rw [hemp] at hmem
        exact absurd hmem (Finset.notMem_empty i)
      show ((kneser n k)ᶜ).Adj u v = true
      simp [compl_adj, kneser_adj, huv, hne]
    · intro A
      have hstep : ∀ i : Fin n, (if A ∈ kneserStar n k i then (1 / k : ℚ) else 0)
          = (if i ∈ A.1 then (1 / k : ℚ) else 0) := by
        intro i
        by_cases hi : i ∈ A.1
        · rw [if_pos (mem_kneserStar.2 hi), if_pos hi]
        · rw [if_neg (fun h ↦ hi (mem_kneserStar.1 h)), if_neg hi]
      have hsum : ∑ i : Fin n, (if A ∈ kneserStar n k i then (1 / k : ℚ) else 0)
          = ∑ _i ∈ A.1, (1 / k : ℚ) := by
        simp only [hstep]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hsum, Finset.sum_const, A.2, nsmul_eq_mul, mul_one_div, div_self hkq]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [mul_one_div]
  · have hpos : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
    have hle := card_div_le_fracChromNum (G := kneser n k) hpos
      (le_of_eq (indepNum_kneser hk h))
    rw [card_kneser] at hle
    refine le_trans (le_of_eq ?_) hle
    have hmul : n * ((n - 1).choose (k - 1)) = (n.choose k) * k := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simpa using Nat.add_one_mul_choose_eq m j
    have hpos' : (0 : ℝ) < ((n - 1).choose (k - 1) : ℕ) := by exact_mod_cast hpos
    rw [div_eq_div_iff hk'.ne' hpos'.ne']
    exact_mod_cast hmul

/-- The Petersen graph is `K(5, 2)`: the value the simplex of `IsoGraph.Fractional` computes for
it, out of the theory instead. -/
theorem fracChromNum_petersen : petersen.fracChromNum = 5 / 2 := by
  have h := fracChromNum_kneser (n := 5) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-! ### Two cases of the Lovász–Kneser theorem

`χ_f ≤ χ` rounds up, so `⌈n / k⌉ ≤ χ(K(n, k))`.  That meets the colouring of
`chromNum_kneser_le` exactly at `n = 2k` and `n = 2k + 1`, where `n - 2k + 2` is `2` and `3`. -/

/-- **`χ(K(2k, k)) = 2`.**  The `k`-sets and their complements are the two colour classes. -/
@[toIsoGraph]
theorem chromNum_kneser_two_mul (hk : 0 < k) : (kneser (2 * k) k).chromNum = 2 := by
  have hub := chromNum_kneser_le (2 * k) k hk
  rw [show 2 * k - 2 * k + 2 = 2 from by omega] at hub
  refine le_antisymm hub ?_
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfc := fracChromNum_kneser hk (le_refl (2 * k))
  refine lt_chromNum_of_lt_fracChromNum (k := 1) ?_ (le_of_eq hfc.symm)
  rw [lt_div_iff₀ hk']
  push_cast
  linarith

/-- **`χ(K(2k + 1, k)) = 3`**: the odd graph `O(k + 1)` is three-chromatic.  It is triangle-free
for `k ≥ 2`, so this is not the bound of `three_le_chromNum_kneser` — it is `χ_f = 2 + 1 / k`
rounding up. -/
@[toIsoGraph]
theorem chromNum_kneser_two_mul_add_one (hk : 0 < k) :
    (kneser (2 * k + 1) k).chromNum = 3 := by
  have hub := chromNum_kneser_le (2 * k + 1) k hk
  rw [show 2 * k + 1 - 2 * k + 2 = 3 from by omega] at hub
  refine le_antisymm hub ?_
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfc := fracChromNum_kneser hk (show 2 * k ≤ 2 * k + 1 by omega)
  refine lt_chromNum_of_lt_fracChromNum (k := 2) ?_ (le_of_eq hfc.symm)
  rw [lt_div_iff₀ hk']
  push_cast
  linarith

/-! ### Three values reproved

`α(K(7, 3)) = 15` costs a SAT certificate in `IsoGraph.Sat` and `χ(K(5, 2)) = 3` a bracket in
`SmallGraphs.Tables`; both are instances of the theorems above. -/

example : (kneser 7 3).indepNum = 15 := by
  rw [indepNum_kneser (by norm_num) (by norm_num)]
  decide

example : (kneser 7 3).chromNum = 3 := chromNum_kneser_two_mul_add_one (k := 3) (by norm_num)

example : petersen.chromNum = 3 := chromNum_kneser_two_mul_add_one (k := 2) (by norm_num)

end CGraph
