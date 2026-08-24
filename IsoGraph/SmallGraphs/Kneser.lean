import IsoGraph.SmallGraphs.TreesAndCycles
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
  `χ(K(2k + 1, k)) = 3`, collected as `chromNum_kneser_of_le` in the form `n - 2k + 2`.
* `chromNum_kneser_two` — `χ(K(n, 2)) = n - 2` for `n ≥ 4`, the **Lovász–Kneser theorem** for
  pairs, proved by counting rather than by topology.

The middle two are the cases of the theorem `χ(K(n, k)) = n - 2k + 2` that the fractional value
settles: `χ ≥ ⌈χ_f⌉ = ⌈n / k⌉` agrees with `n - 2k + 2` exactly when `n ∈ {2k, 2k + 1}` (or
`k = 1`).  Beyond that the general theorem needs the Borsuk–Ulam theorem, which Mathlib does not
have — but `k = 2` is elementary, and the last bullet proves it in full.  The upper bound
`chromNum_kneser_le` holds for every `n` and `k`, and below the range `n < 2k` leaves the graph
edgeless and `chromNum_kneser_of_lt` gives `1`, so what remains open here is `n ≥ 2k + 2` with
`k ≥ 3`.
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

/-- **The Lovász–Kneser value over the range the library reaches**, in a shape that fires on a
numeral.  The two theorems above are stated of `2 * k` and `2 * k + 1`, and no amount of `simp`
will match either against `kneser 7 3`; the same content with the range as two inequalities is
discharged by `norm_num` at any pair of numerals, and gives the general formula `n - 2k + 2` where
it is known. -/
@[toIsoGraph]
theorem chromNum_kneser_of_le (hk : 0 < k) (h₁ : 2 * k ≤ n) (h₂ : n ≤ 2 * k + 1) :
    (kneser n k).chromNum = n - 2 * k + 2 := by
  rcases (by omega : n = 2 * k ∨ n = 2 * k + 1) with rfl | rfl
  · rw [chromNum_kneser_two_mul hk]
    omega
  · rw [chromNum_kneser_two_mul_add_one hk]
    omega

/-! ### The Lovász–Kneser theorem for pairs

For `k = 2` the theorem is elementary, and the proof below is the classical counting one.  Fix a
proper colouring of `K(n, 2)`.  A colour class is a family of pairs no two of which are disjoint,
and such a family is either a *star* — all its pairs through one point — or a *triangle*, the
three pairs inside a `3`-set: that is `exists_triple_of_intersecting`.  Let `S` be the set of the
star centres, one per star colour, so `|S|` is at most the number of star colours.  Every pair
inside the complement of `S` misses all the centres, so it carries a triangle colour, and a
triangle colour owns at most three pairs.  With `u = n - |S|` free points and `d` triangle
colours, `C(u, 2) ≤ 3d` and `u ≥ d + 3`, which forces `(u - 3)(u - 4) < 0` unless `n ≤ m + 2`.
-/

/-- The other element of a two-element finset. -/
private theorem exists_pair_eq {N : ℕ} {d : Finset (Fin N)} {p : Fin N}
    (hd : d.card = 2) (hp : p ∈ d) : ∃ q, q ≠ p ∧ d = {p, q} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hd
  rcases Finset.mem_insert.1 hp with rfl | hb
  · exact ⟨b, Ne.symm hab, rfl⟩
  · rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨a, hab, Finset.pair_comm a p⟩

/-- An intersecting family of pairs with no common point is a triangle. -/
private theorem exists_triple_of_intersecting (hn : 0 < n)
    (F : Finset (Finset (Fin n)))
    (h2 : ∀ a ∈ F, a.card = 2)
    (hint : ∀ a ∈ F, ∀ b ∈ F, (a ∩ b).Nonempty)
    (hns : ¬ ∃ v : Fin n, ∀ a ∈ F, v ∈ a) :
    ∃ T : Finset (Fin n), T.card = 3 ∧ ∀ a ∈ F, a ⊆ T := by
  classical
  obtain ⟨a0, ha0⟩ : F.Nonempty := by
    rcases F.eq_empty_or_nonempty with rfl | h
    · exact absurd ⟨⟨0, hn⟩, by simp⟩ hns
    · exact h
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 (h2 a0 ha0)
  obtain ⟨b, hbF, hxb⟩ : ∃ b ∈ F, x ∉ b := by
    by_contra h
    push_neg at h
    exact hns ⟨x, h⟩
  obtain ⟨c, hcF, hyc⟩ : ∃ c ∈ F, y ∉ c := by
    by_contra h
    push_neg at h
    exact hns ⟨y, h⟩
  have hyb : y ∈ b := by
    obtain ⟨w, hw⟩ := hint _ ha0 _ hbF
    rw [Finset.mem_inter] at hw
    rcases Finset.mem_insert.1 hw.1 with rfl | hw'
    · exact absurd hw.2 hxb
    · rw [Finset.mem_singleton] at hw'
      subst hw'
      exact hw.2
  obtain ⟨z, hzy, hb⟩ := exists_pair_eq (h2 b hbF) hyb
  have hxz : x ≠ z := by
    rintro rfl
    exact hxb (hb ▸ by simp)
  have hxc : x ∈ c := by
    obtain ⟨w, hw⟩ := hint _ ha0 _ hcF
    rw [Finset.mem_inter] at hw
    rcases Finset.mem_insert.1 hw.1 with rfl | hw'
    · exact hw.2
    · rw [Finset.mem_singleton] at hw'
      subst hw'
      exact absurd hw.2 hyc
  have hzc : z ∈ c := by
    obtain ⟨w, hw⟩ := hint _ hbF _ hcF
    rw [Finset.mem_inter, hb, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw.1 with rfl | rfl
    · exact absurd hw.2 hyc
    · exact hw.2
  have hcxz : c = {x, z} :=
    (Finset.eq_of_subset_of_card_le (by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hxc
      · rw [Finset.mem_singleton] at hw; subst hw; exact hzc)
      (by rw [h2 c hcF, Finset.card_pair hxz])).symm
  refine ⟨{x, y, z}, Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, Ne.symm hzy, rfl⟩, ?_⟩
  intro d hd p hp
  by_contra hpT
  obtain ⟨q, hqp, hdq⟩ := exists_pair_eq (h2 d hd) hp
  have key : ∀ e ∈ F, p ∉ e → q ∈ e := by
    intro e he hpe
    obtain ⟨w, hw⟩ := hint _ hd _ he
    rw [Finset.mem_inter, hdq, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw.1 with rfl | rfl
    · exact absurd hw.2 hpe
    · exact hw.2
  have h1 : q ∈ ({x, y} : Finset (Fin n)) :=
    key _ ha0 fun h => hpT (by simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
  have h2b : q ∈ b :=
    key _ hbF fun h => hpT (by
      rw [hb] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
  have h3 : q ∈ c :=
    key _ hcF fun h => hpT (by
      rw [hcxz] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
  rw [hb, Finset.mem_insert, Finset.mem_singleton] at h2b
  rw [hcxz, Finset.mem_insert, Finset.mem_singleton] at h3
  rw [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl
  · rcases h2b with h | h
    · exact hxy h
    · exact hxz h
  · rcases h3 with h | h
    · exact hxy h.symm
    · exact hzy h.symm

/-- **The counting half of Lovász–Kneser at `k = 2`**, stated without any graph theory: if the
`2`-element subsets of `Fin n` are coloured so that disjoint pairs get different colours, then
`n ≤ m + 2`. -/
private theorem card_le_of_colouring_pairs {m : ℕ} (col : Finset (Fin n) → Fin m)
    (hcol : ∀ a b : Finset (Fin n), a.card = 2 → b.card = 2 → a ∩ b = ∅ → col a ≠ col b) :
    n ≤ m + 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  have hn : 0 < n := by omega
  -- a centre for every colour class that has one
  have hpick : ∀ j : Fin m, ∃ v : Fin n,
      (∃ w : Fin n, ∀ a : Finset (Fin n), a.card = 2 → col a = j → w ∈ a) →
        ∀ a : Finset (Fin n), a.card = 2 → col a = j → v ∈ a := by
    intro j
    by_cases h : ∃ w : Fin n, ∀ a : Finset (Fin n), a.card = 2 → col a = j → w ∈ a
    · obtain ⟨w, hw⟩ := h
      exact ⟨w, fun _ ↦ hw⟩
    · exact ⟨⟨0, hn⟩, fun h' ↦ absurd h' h⟩
  choose ctr hctr using hpick
  set star : Finset (Fin m) := Finset.univ.filter
    (fun j ↦ ∃ w : Fin n, ∀ a : Finset (Fin n), a.card = 2 → col a = j → w ∈ a) with hstar
  have hmem_star : ∀ j, j ∈ star ↔
      ∃ w : Fin n, ∀ a : Finset (Fin n), a.card = 2 → col a = j → w ∈ a := by
    intro j
    rw [hstar, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ j)
  set S : Finset (Fin n) := star.image ctr with hS
  set P : Finset (Finset (Fin n)) := Sᶜ.powersetCard 2 with hP
  have hmemP : ∀ a ∈ P, a.card = 2 ∧ a ⊆ Sᶜ := by
    intro a ha
    rw [hP, Finset.mem_powersetCard] at ha
    exact ⟨ha.2, ha.1⟩
  -- no pair avoiding every centre can carry a star colour
  have hnostar : ∀ a ∈ P, col a ∉ star := by
    intro a ha hmem
    obtain ⟨hcard, hsub⟩ := hmemP a ha
    have hin : ctr (col a) ∈ a := hctr _ ((hmem_star _).1 hmem) a hcard rfl
    exact absurd (Finset.mem_image_of_mem ctr hmem) (Finset.mem_compl.1 (hsub hin))
  -- every non-star colour class is a triangle, so it owns at most three of those pairs
  have hfib : ∀ j ∈ P.image col, (P.filter (fun a ↦ col a = j)).card ≤ 3 := by
    intro j hj
    obtain ⟨a0, ha0P, ha0⟩ := Finset.mem_image.1 hj
    set F : Finset (Finset (Fin n)) :=
      ((Finset.univ : Finset (Fin n)).powersetCard 2).filter (fun a ↦ col a = j) with hF
    have hFmem : ∀ a, a ∈ F ↔ (a.card = 2 ∧ col a = j) := by
      intro a
      rw [hF, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        exact ⟨⟨Finset.subset_univ _, h2⟩, h3⟩
    obtain ⟨T, hT3, hTsub⟩ := exists_triple_of_intersecting hn F
      (fun a ha ↦ ((hFmem a).1 ha).1)
      (by
        intro a ha b hb
        rcases Finset.eq_empty_or_nonempty (a ∩ b) with he | h
        · exact absurd (((hFmem a).1 ha).2.trans ((hFmem b).1 hb).2.symm)
            (hcol a b ((hFmem a).1 ha).1 ((hFmem b).1 hb).1 he)
        · exact h)
      (by
        rintro ⟨v, hv⟩
        refine hnostar a0 ha0P ?_
        rw [ha0, hmem_star]
        exact ⟨v, fun a hcard hcolj ↦ hv a ((hFmem a).2 ⟨hcard, hcolj⟩)⟩)
    calc (P.filter (fun a ↦ col a = j)).card
        ≤ (T.powersetCard 2).card := by
          refine Finset.card_le_card ?_
          intro a ha
          rw [Finset.mem_filter] at ha
          rw [Finset.mem_powersetCard]
          exact ⟨hTsub a ((hFmem a).2 ⟨(hmemP a ha.1).1, ha.2⟩), (hmemP a ha.1).1⟩
      _ = 3 := by rw [Finset.card_powersetCard, hT3]; decide
  have hcount : P.card ≤ 3 * (P.image col).card := Finset.card_le_mul_card_image P 3 hfib
  have himg : P.image col ⊆ starᶜ := by
    intro j hj
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_compl.2 (hnostar a haP)
  have himgcard : (P.image col).card ≤ m - star.card := by
    have h := Finset.card_le_card himg
    rwa [Finset.card_compl, Fintype.card_fin] at h
  have hSle : S.card ≤ star.card := Finset.card_image_le
  have hstar_le : star.card ≤ m := by simpa using Finset.card_le_univ star
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hPcard : P.card = ((Sᶜ : Finset (Fin n)).card).choose 2 := Finset.card_powersetCard 2 _
  have hUcard : (Sᶜ : Finset (Fin n)).card = n - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  -- arithmetic: with `u` free vertices and `d` non-star colours, `C(u, 2) ≤ 3d` and `u ≥ d + 3`
  obtain ⟨d, hd⟩ : ∃ d, m = S.card + d := ⟨m - S.card, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, n = S.card + u := ⟨n - S.card, by omega⟩
  have hchoose : u.choose 2 ≤ 3 * d := by
    have h1 : P.card ≤ 3 * (m - star.card) := le_trans hcount (Nat.mul_le_mul_left 3 himgcard)
    rw [hPcard, hUcard] at h1
    have h2 : n - S.card = u := by omega
    rw [h2] at h1
    exact le_trans h1 (Nat.mul_le_mul_left 3 (by omega))
  have hud : d + 3 ≤ u := by omega
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 3 := ⟨u - 3, by omega⟩
  rw [Nat.choose_two_right] at hchoose
  have hprod : (w + 3) * (w + 3 - 1) = (w + 3) * (w + 2) := by norm_num
  rw [hprod] at hchoose
  obtain ⟨X, hX⟩ : ∃ X, X = (w + 3) * (w + 2) := ⟨_, rfl⟩
  rw [← hX] at hchoose
  have hXle : X ≤ 6 * d + 1 := by omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = w * w := ⟨_, rfl⟩
  have hexp : X = Y + 5 * w + 6 := by rw [hX, hY]; ring
  have hYw : w ≤ Y := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp [hY]
    · calc w = 1 * w := (one_mul w).symm
        _ ≤ w * w := Nat.mul_le_mul_right w hw
        _ = Y := hY.symm
  omega

/-- **`χ(K(n, 2)) ≥ n - 2`.**  Every proper colouring of the Kneser graph `K(n, 2)` uses at least
`n - 2` colours: each colour class is an intersecting family of pairs, hence a star or a triangle,
and the triangles are too small to cover the pairs the stars miss. -/
theorem le_chromNum_kneser_two (n : ℕ) : n - 2 ≤ (kneser n 2).chromNum := by
  classical
  rw [le_chromNum_iff]
  intro m hm
  obtain ⟨C⟩ := hm
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · by_contra hc
    have hn2 : 2 ≤ n := by omega
    have hcard : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)).card = 2 :=
      Finset.card_pair (Fin.ne_of_val_ne (by simp))
    exact (C (⟨_, hcard⟩ : (kneser n 2).V)).elim0
  · have hle : n ≤ m + 2 := by
      refine card_le_of_colouring_pairs
        (fun a ↦ if h : a.card = 2 then C (⟨a, h⟩ : (kneser n 2).V) else ⟨0, hm0⟩) ?_
      intro a b ha hb hab
      simp only [dif_pos ha, dif_pos hb]
      refine C.valid ?_
      rw [CGraph.toSimple_adj, kneser_adj]
      have hne : (⟨a, ha⟩ : (kneser n 2).V) ≠ ⟨b, hb⟩ := by
        rintro h
        rw [Subtype.mk.injEq] at h
        rw [h, Finset.inter_self] at hab
        rw [hab] at hb
        simp at hb
      simp [hne, hab]
    omega

/-- **The Lovász–Kneser theorem at `k = 2`**: `χ(K(n, 2)) = n - 2` for `n ≥ 4`. -/
@[toIsoGraph]
theorem chromNum_kneser_two {n : ℕ} (hn : 4 ≤ n) : (kneser n 2).chromNum = n - 2 := by
  refine le_antisymm ?_ (le_chromNum_kneser_two n)
  have h := chromNum_kneser_le n 2 (by norm_num)
  omega

/-! ### Three values reproved

`α(K(7, 3)) = 15` costs a SAT certificate in `IsoGraph.Sat` and `χ(K(5, 2)) = 3` a bracket in
`SmallGraphs.Tables`; both are instances of the theorems above. -/

example : (kneser 7 3).indepNum = 15 := by
  rw [indepNum_kneser (by norm_num) (by norm_num)]
  decide

example : (kneser 7 3).chromNum = 3 := chromNum_kneser_two_mul_add_one (k := 3) (by norm_num)

example : petersen.chromNum = 3 := chromNum_kneser_two_mul_add_one (k := 2) (by norm_num)

/-- `K(6, 2)` is the complement of the triangular graph `T(6)` and needs four colours; that is
outside the range the fractional bound reaches, and is the first new value of
`chromNum_kneser_two`. -/
example : (kneser 6 2).chromNum = 4 := chromNum_kneser_two (by norm_num)

end CGraph

namespace IsoGraph

/-- **The clique cover number of `T(n) = L(Kₙ)` is `n - 2`.**  The bound of
`cliqueCoverNum_triangular_le` is met, because `χ(K(n, 2)) = n - 2` is the Lovász–Kneser theorem
for pairs and `T(n)` is the complement of `K(n, 2)`.  Read on the line graph: the edges of `Kₙ`
split into `n - 2` classes of pairwise-meeting edges, and no fewer. -/
theorem cliqueCoverNum_triangular_eq {n : ℕ} (hn : 4 ≤ n) :
    (triangular n).cliqueCoverNum = n - 2 := by
  rw [cliqueCoverNum_triangular, chromNum_kneser_two hn]

end IsoGraph
