import IsoGraph.SmallGraphs.Structure

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Automorphisms of the named graphs

Regularity, transitivity, self-complementarity and automorphism counts of the named graphs.
-/

namespace CGraph

section
open Fintype
variable {m n : ℕ}

/-- **The `k × k` rook's graph is strongly regular**, with parameters `(k², 2(k-1), k-2, 2)`.

Only the *square* rook's graphs qualify: in `rook m n` two squares in a row have `n - 2` common
neighbours and two in a column have `m - 2`, so `ℓ` is well defined exactly when `m = n`. -/
theorem isSRGWith_rook (k : ℕ) : (rook k k).IsSRGWith (k * k) (2 * (k - 1)) (k - 2) 2 := by
  refine isSRGWith_of _ ?_ ?_ ?_ ?_
  · show FinEnum.card (complete k).V * FinEnum.card (complete k).V = k * k
    rw [card_complete]
  · rintro ⟨a, b⟩
    rw [card_nbrs_rook]
    omega
  · rintro ⟨a, b⟩ ⟨c, d⟩ hadj
    rw [rook_adj] at hadj
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
    obtain ⟨rfl, h⟩ | ⟨h, rfl⟩ := hadj
    · exact card_nbrs_inter_rook_row a b d h
    · exact card_nbrs_inter_rook_col a c b h
  · rintro ⟨a, b⟩ ⟨c, d⟩ hne hadj
    rw [rook_adj] at hadj
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      not_not] at hadj
    refine card_nbrs_inter_rook_diag a c b d ?_ ?_ <;> grind [Prod.ext_iff]

/-- A triangle of the rook's graph lies in one row or one column, and is any three squares of
it. -/
@[simp, toIsoGraph]
theorem cliqueCount_rook (k : ℕ) : (rook k k).cliqueCount 3 = 2 * k * k.choose 3 := by
  have h := (isSRGWith_rook k).six_mul_cliqueCount_three
  have hB := six_mul_choose_three k
  refine (Nat.eq_of_mul_eq_mul_left (show 0 < 6 by norm_num) ?_).symm
  calc 6 * (2 * k * k.choose 3) = 2 * k * (6 * k.choose 3) := by ring
    _ = 2 * k * (k * (k - 1) * (k - 2)) := by rw [hB]
    _ = k * k * (2 * (k - 1)) * (k - 2) := by ring
    _ = 6 * (rook k k).cliqueCount 3 := h.symm

/-- Three squares of the board with no two in a row or a column: three non-attacking rooks.  Pick
the three rows, the three columns, and the bijection between them. -/
@[simp, toIsoGraph]
theorem indepCount_rook (k : ℕ) : (rook k k).indepCount 3 = 6 * (k.choose 3) ^ 2 := by
  have h := (isSRGWith_rook k).six_mul_indepCount_three
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 6 by norm_num) ?_
  rw [h]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have hB := six_mul_choose_three (m + 3)
    rw [show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl] at hB
    rw [show (m + 3) * (m + 3) - 2 * (m + 3 - 1) - 1 = (m + 2) * (m + 2) from by
        have : (m + 3) * (m + 3) = (m + 2) * (m + 2) + 2 * (m + 2) + 1 := by ring
        omega,
      show (m + 3) * (m + 3) - (2 * (2 * (m + 3 - 1)) - 2) - 2 = (m + 1) * (m + 1) from by
        have : (m + 3) * (m + 3) = (m + 1) * (m + 1) + 4 * m + 8 := by ring
        omega]
    calc (m + 3) * (m + 3) * ((m + 2) * (m + 2)) * ((m + 1) * (m + 1))
        = ((m + 3) * (m + 2) * (m + 1)) * ((m + 3) * (m + 2) * (m + 1)) := by ring
      _ = (6 * (m + 3).choose 3) * (6 * (m + 3).choose 3) := by rw [hB]
      _ = 6 * (6 * ((m + 3).choose 3) ^ 2) := by ring

/-- **Kneser graphs on pairs are strongly regular**, with parameters
`(C(n,2), C(n-2,2), C(n-4,2), C(n-3,2))`.  For `n = 5` this is the Petersen graph, `(10,3,0,1)`.
-/
@[toIsoGraph]
theorem isSRGWith_kneser_two (n : ℕ) :
    (kneser n 2).IsSRGWith (n.choose 2) ((n - 2).choose 2) ((n - 4).choose 2)
      ((n - 3).choose 2) := by
  refine isSRGWith_of _ (card_kneser n 2) (fun s ↦ card_nbrs_kneser one_le_two s) ?_ ?_
  · intro s t hadj
    simp only [kneser_adj, Bool.and_eq_true, decide_eq_true_eq] at hadj
    rw [card_nbrs_inter_kneser one_le_two, hadj.2, Finset.card_empty]
    norm_num
  · intro s t hne hadj
    simp only [kneser_adj, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not] at hadj
    rw [card_nbrs_inter_kneser one_le_two,
      card_inter_eq_one_of_ne s t hne (hadj.resolve_left (by simpa using hne))]
    norm_num

/-- A triangle of a Kneser graph on pairs is three disjoint pairs, so a perfect matching on six of
the `n` points; there are fifteen of those on each six. -/
@[simp, toIsoGraph]
theorem cliqueCount_kneser_two (n : ℕ) : (kneser n 2).cliqueCount 3 = 15 * n.choose 6 := by
  have h := (isSRGWith_kneser_two n).six_mul_cliqueCount_three
  rw [choose_two_mul_choose_two_mul_choose_two] at h
  omega

/-- **The complete bipartite graph `K_{n,n}` is strongly regular** with parameters
`(2n, n, 0, n)`.

`bipartite m n` is the complement of `Kₘ ⊔ Kₙ`, so this could go through `isSRGWith_compl`, but
the counts are more direct read off the graph itself: a vertex on one side sees all of the other
side, two vertices on the same side see all of the other side in common, and two adjacent
vertices see nothing in common.  Doing it directly also avoids the `2 ≤ n` side condition that
the truncated subtraction in `isSRGWith_compl`'s parameters would force. -/
@[toIsoGraph]
theorem isSRGWith_bipartite (n : ℕ) : (bipartite n n).IsSRGWith (2 * n) n 0 n := by
  have hnbrs : ∀ x : (bipartite n n).V, ((bipartite n n).nbrs x).card = n := by
    rintro (a | b)
    · rw [nbrs_bipartite_inl]; simp
    · rw [nbrs_bipartite_inr]; simp
  refine isSRGWith_of _ ?_ hnbrs (fun (x y : (bipartite n n).V) hadj ↦ ?_)
    (fun (x y : (bipartite n n).V) hne _ ↦ ?_)
  · rw [card_bipartite, two_mul]
  · -- adjacent: one vertex on each side, and the two neighbourhoods are the two sides
    rcases x with a | b <;> rcases y with c | d <;> simp_all [nbrs_bipartite_inl,
      nbrs_bipartite_inr, Finset.eq_empty_iff_forall_notMem]
  · -- non-adjacent and distinct: both on the same side, with the same neighbourhood
    rcases x with a | b <;> rcases y with c | d <;>
      simp_all [nbrs_bipartite_inl, nbrs_bipartite_inr]

/-- **The complete multipartite graph with `n` parts of size `a` is strongly regular** with
parameters `(na, (n-1)a, (n-2)a, (n-1)a)`.

A vertex misses only its own part; two vertices in different parts miss both of theirs; two
distinct vertices in the same part have the same neighbourhood.  The truncated subtractions are
correct in the degenerate cases too: for `n ≤ 1` there are no edges and `(n-1)a = 0`, and for
`n = 2` no two adjacent vertices have a common neighbour and `(n-2)a = 0`. -/
@[toIsoGraph]
theorem isSRGWith_completeMultipartite_replicate (n a : ℕ) :
    (completeMultipartite (List.replicate n a)).IsSRGWith (n * a) ((n - 1) * a) ((n - 2) * a)
      ((n - 1) * a) := by
  refine isSRGWith_of _ ?_
    (fun (x : Σ i : Fin (List.replicate n a).length,
      (complete ((List.replicate n a).get i)).V) ↦ ?_)
    (fun (x y : Σ i : Fin (List.replicate n a).length,
      (complete ((List.replicate n a).get i)).V) hadj ↦ ?_)
    (fun (x y : Σ i : Fin (List.replicate n a).length,
      (complete ((List.replicate n a).get i)).V) hne hadj ↦ ?_)
  · rw [card_completeMultipartite, List.sum_replicate, smul_eq_mul]
  · rw [nbrs_completeMultipartite, card_filter_fst_notMem, sum_compl_replicate,
      Finset.card_singleton]
    simp
  · rw [nbrs_inter_completeMultipartite, card_filter_fst_notMem, sum_compl_replicate]
    rw [completeMultipartite_adj] at hadj
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hadj
    rw [Finset.card_insert_of_notMem (by simpa using hadj), Finset.card_singleton]
    simp
  · rw [nbrs_inter_completeMultipartite, card_filter_fst_notMem, sum_compl_replicate]
    rw [completeMultipartite_adj] at hadj
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq] at hadj
    rw [hadj, Finset.pair_eq_singleton, Finset.card_singleton]
    simp

/-- **The cocktail party graph `K_{n×2}` is strongly regular** with parameters
`(2n, 2n-2, 2n-4, 2n-2)`: it is `n` parts of size two. -/
@[toIsoGraph]
theorem isSRGWith_cocktailParty (n : ℕ) :
    (cocktailParty n).IsSRGWith (2 * n) (2 * n - 2) (2 * n - 4) (2 * n - 2) := by
  have h := isSRGWith_completeMultipartite_replicate n 2
  rwa [show n * 2 = 2 * n from by ring, show (n - 1) * 2 = 2 * n - 2 from by omega,
    show (n - 2) * 2 = 2 * n - 4 from by omega] at h

/-- A triangle of the cocktail party graph is three of the `n` parts, one vertex from each. -/
@[simp, toIsoGraph]
theorem cliqueCount_cocktailParty (n : ℕ) :
    (cocktailParty n).cliqueCount 3 = 8 * n.choose 3 := by
  have h := (isSRGWith_cocktailParty n).six_mul_cliqueCount_three
  rw [show 2 * n - 2 = 2 * (n - 1) from by omega,
    show 2 * n - 4 = 2 * (n - 2) from by omega] at h
  have hB := six_mul_choose_three n
  refine (Nat.eq_of_mul_eq_mul_left (show 0 < 6 by norm_num) ?_).symm
  calc 6 * (8 * n.choose 3) = 8 * (6 * n.choose 3) := by ring
    _ = 8 * (n * (n - 1) * (n - 2)) := by rw [hB]
    _ = 2 * n * (2 * (n - 1)) * (2 * (n - 2)) := by ring
    _ = 6 * (cocktailParty n).cliqueCount 3 := h.symm

/-- No three vertices of the cocktail party graph are pairwise non-adjacent: two of them would
have to share a part, and the parts hold two vertices each. -/
@[simp, toIsoGraph]
theorem indepCount_cocktailParty (n : ℕ) : (cocktailParty n).indepCount 3 = 0 := by
  have h := (isSRGWith_cocktailParty n).six_mul_indepCount_three
  rw [show 2 * n - (2 * (2 * n - 2) - (2 * n - 2)) - 2 = 0 from by omega, Nat.mul_zero] at h
  omega

end

section
open Fintype
variable {m n : ℕ}
variable {F : Type} [Field F] [FinEnum F]

/-- **Paley graphs are strongly regular.**  For a finite field with `q ≡ 1 mod 4` elements the
Paley graph has parameters `(q, (q-1)/2, (q-5)/4, (q-1)/4)`. -/
@[toIsoGraph]
theorem isSRGWith_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).IsSRGWith (Fintype.card F) ((Fintype.card F - 1) / 2)
      ((Fintype.card F - 5) / 4) ((Fintype.card F - 1) / 4) := by
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  refine isSRGWith_of _ card_paleyField (fun (x : F) ↦ card_nbrs_paleyField hq x)
    (fun (x y : F) hadj ↦ ?_) (fun (x y : F) hxy hadj ↦ ?_)
  · -- adjacent: `χ (y - x) = 1`
    rw [paleyField_adj hq] at hadj
    simp only [decide_eq_true_eq] at hadj
    have hxy : x ≠ y := by
      rintro rfl
      rw [sub_self, quadraticChar_zero] at hadj
      exact absurd hadj (by norm_num)
    have := card_nbrs_inter_paleyField hq hxy
    rw [hadj] at this
    omega
  · -- distinct and non-adjacent: `χ (y - x) = -1`
    have ha : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
    rw [paleyField_adj hq] at hadj
    simp only [decide_eq_false_iff_not] at hadj
    have hneg : quadraticChar F (y - x) = -1 := (quadraticChar_dichotomy ha).resolve_left hadj
    have := card_nbrs_inter_paleyField hq hxy
    rw [hneg] at this
    omega

/-- The Paley graph of a field with `q ≡ 1 mod 4` elements has `q(q-1)(q-5)/48` triangles; the
division is exact. -/
@[toIsoGraph]
theorem cliqueCount_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).cliqueCount 3
      = Fintype.card F * (Fintype.card F - 1) * (Fintype.card F - 5) / 48 := by
  have h := (isSRGWith_paleyField (F := F) hq).six_mul_cliqueCount_three
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = 4 * m + 1 := ⟨Fintype.card F / 4, by omega⟩
  rw [hm] at h ⊢
  rw [show (4 * m + 1 - 1) / 2 = 2 * m from by omega,
    show (4 * m + 1 - 5) / 4 = m - 1 from by omega] at h
  have h48 : 48 * (paleyField F).cliqueCount 3
      = (4 * m + 1) * (4 * m + 1 - 1) * (4 * m + 1 - 5) := by
    rw [show 4 * m + 1 - 1 = 4 * m from by omega,
      show 4 * m + 1 - 5 = 4 * (m - 1) from by omega]
    calc 48 * (paleyField F).cliqueCount 3
        = 8 * (6 * (paleyField F).cliqueCount 3) := by ring
      _ = 8 * ((4 * m + 1) * (2 * m) * (m - 1)) := by rw [h]
      _ = (4 * m + 1) * (4 * m) * (4 * (m - 1)) := by ring
  rw [← h48, Nat.mul_div_cancel_left _ (by norm_num : 0 < 48)]

/-- A Paley graph is isomorphic to its own complement, so it has as many independent triples as
triangles. -/
@[toIsoGraph]
theorem indepCount_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).indepCount 3
      = Fintype.card F * (Fintype.card F - 1) * (Fintype.card F - 5) / 48 := by
  have h := (isSRGWith_paleyField (F := F) hq).six_mul_indepCount_three
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = 4 * m + 1 := ⟨Fintype.card F / 4, by omega⟩
  rw [hm] at h ⊢
  rw [show (4 * m + 1 - 1) / 2 = 2 * m from by omega,
    show (4 * m + 1 - 1) / 4 = m from by omega,
    show 4 * m + 1 - 2 * m - 1 = 2 * m from by omega,
    show 4 * m + 1 - (2 * (2 * m) - m) - 2 = m - 1 from by omega] at h
  have h48 : 48 * (paleyField F).indepCount 3
      = (4 * m + 1) * (4 * m + 1 - 1) * (4 * m + 1 - 5) := by
    rw [show 4 * m + 1 - 1 = 4 * m from by omega,
      show 4 * m + 1 - 5 = 4 * (m - 1) from by omega]
    calc 48 * (paleyField F).indepCount 3
        = 8 * (6 * (paleyField F).indepCount 3) := by ring
      _ = 8 * ((4 * m + 1) * (2 * m) * (m - 1)) := by rw [h]
      _ = (4 * m + 1) * (4 * m) * (4 * (m - 1)) := by ring
  rw [← h48, Nat.mul_div_cancel_left _ (by norm_num : 0 < 48)]

end

section
open Fintype
variable {m n : ℕ}

/-- **`paley q` is strongly regular** for every prime `q ≡ 1 mod 4`. -/
@[toIsoGraph]
theorem isSRGWith_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).IsSRGWith q ((q - 1) / 2) ((q - 5) / 4) ((q - 1) / 4) := by
  have h := isSRGWith_paleyField (F := ZMod q) (by
    rw [← @FinEnum.card_eq_fintypeCard (ZMod q) _ FinEnum.instFintype]; exact hq)
  rw [← @FinEnum.card_eq_fintypeCard (ZMod q) _ FinEnum.instFintype] at h
  exact SimpleGraph.Iso.isSRGWith_of_iso (CGraph.Iso.toSimpleIso (paleyIso q)) h

@[inherit_doc cliqueCount_paleyField, toIsoGraph]
theorem cliqueCount_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).cliqueCount 3 = q * (q - 1) * (q - 5) / 48 := by
  have h := (isSRGWith_paley q hq).six_mul_cliqueCount_three
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  rw [show (4 * m + 1 - 1) / 2 = 2 * m from by omega,
    show (4 * m + 1 - 5) / 4 = m - 1 from by omega] at h
  have h48 : 48 * (paley (4 * m + 1)).cliqueCount 3
      = (4 * m + 1) * (4 * m + 1 - 1) * (4 * m + 1 - 5) := by
    rw [show 4 * m + 1 - 1 = 4 * m from by omega,
      show 4 * m + 1 - 5 = 4 * (m - 1) from by omega]
    calc 48 * (paley (4 * m + 1)).cliqueCount 3
        = 8 * (6 * (paley (4 * m + 1)).cliqueCount 3) := by ring
      _ = 8 * ((4 * m + 1) * (2 * m) * (m - 1)) := by rw [h]
      _ = (4 * m + 1) * (4 * m) * (4 * (m - 1)) := by ring
  rw [← h48, Nat.mul_div_cancel_left _ (by norm_num : 0 < 48)]

@[inherit_doc indepCount_paleyField, toIsoGraph]
theorem indepCount_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).indepCount 3 = q * (q - 1) * (q - 5) / 48 := by
  have h := (isSRGWith_paley q hq).six_mul_indepCount_three
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  rw [show (4 * m + 1 - 1) / 2 = 2 * m from by omega,
    show (4 * m + 1 - 1) / 4 = m from by omega,
    show 4 * m + 1 - 2 * m - 1 = 2 * m from by omega,
    show 4 * m + 1 - (2 * (2 * m) - m) - 2 = m - 1 from by omega] at h
  have h48 : 48 * (paley (4 * m + 1)).indepCount 3
      = (4 * m + 1) * (4 * m + 1 - 1) * (4 * m + 1 - 5) := by
    rw [show 4 * m + 1 - 1 = 4 * m from by omega,
      show 4 * m + 1 - 5 = 4 * (m - 1) from by omega]
    calc 48 * (paley (4 * m + 1)).indepCount 3
        = 8 * (6 * (paley (4 * m + 1)).indepCount 3) := by ring
      _ = 8 * ((4 * m + 1) * (2 * m) * (m - 1)) := by rw [h]
      _ = (4 * m + 1) * (4 * m) * (4 * (m - 1)) := by ring
  rw [← h48, Nat.mul_div_cancel_left _ (by norm_num : 0 < 48)]

end

section
open Fintype
variable (G : CGraph)

/-- Right translation is an automorphism of a Cayley graph. -/
theorem isVertexTransitive_cayleyAdd (A : Type) [FinEnum A] [AddGroup A]
    (S : A → Bool) : (cayleyAdd A S).IsVertexTransitive :=
  isVertexTransitive_ofRel A _ fun u v ↦
    ⟨Equiv.addRight (-u + v), fun x y ↦ by simp [add_sub_add_right_eq_sub], by simp⟩

/-- The Paley graph of a finite field is a Cayley graph, hence vertex-transitive. -/
@[toIsoGraph]
theorem isVertexTransitive_paleyField (F : Type) [Field F] [FinEnum F] :
    (paleyField F).IsVertexTransitive :=
  isVertexTransitive_cayleyAdd F _

theorem isVertexTransitive_paley (q : ℕ) [NeZero q] [Fact q.Prime] :
    (paley q).IsVertexTransitive :=
  isVertexTransitive_of_iso (paleyIso q) (isVertexTransitive_paleyField (ZMod q))

/-- **The Paley graph of a finite field is arc-transitive.**  Translation alone only moves
vertices; to move an arc `u → v` onto an arc `u' → v'` we scale as well, by the ratio
`(v' - u') / (v - u)`.  Both differences are squares, so the ratio is a square, and multiplying by
a square preserves the quadratic character — hence adjacency. -/
@[toIsoGraph]
theorem isArcTransitive_paleyField (F : Type) [Field F] [FinEnum F]
    (hq : Fintype.card F % 4 = 1) : (paleyField F).IsArcTransitive := by
  have key : ∀ u v u' v' : F, quadraticChar F (v - u) = 1 → quadraticChar F (v' - u') = 1 →
      ∃ σ : paleyField F ≃cg paleyField F, σ u = u' ∧ σ v = v' := by
    intro u v u' v' huv hu'v'
    have hvu : v - u ≠ 0 := by
      rintro h
      rw [h, quadraticChar_zero] at huv
      norm_num at huv
    have hinv : quadraticChar F (v - u)⁻¹ = 1 := by
      have h : quadraticChar F ((v - u)⁻¹ * (v - u)) = 1 := by
        rw [inv_mul_cancel₀ hvu, map_one]
      rwa [map_mul, huv, mul_one] at h
    set a : F := (v' - u') * (v - u)⁻¹ with ha
    have hχa : quadraticChar F a = 1 := by rw [ha, map_mul, hu'v', hinv, mul_one]
    have ha0 : a ≠ 0 := by
      rintro h
      rw [h, quadraticChar_zero] at hχa
      norm_num at hχa
    have hadj : ∀ x y : F,
        (paleyField F).Adj (a * (x - u) + u') (a * (y - u) + u') = (paleyField F).Adj x y := by
      intro x y
      rw [paleyField_adj hq, paleyField_adj hq,
        show a * (y - u) + u' - (a * (x - u) + u') = a * (y - x) from by ring, map_mul, hχa,
        one_mul]
    refine ⟨autoOfPerm (G := paleyField F)
      (((Equiv.subRight u).trans (Equiv.mulLeft₀ a ha0)).trans (Equiv.addRight u'))
      (fun x y ↦ hadj x y), ?_, ?_⟩
    · show a * (u - u) + u' = u'
      rw [sub_self, mul_zero, zero_add]
    · show a * (v - u) + u' = v'
      rw [ha, mul_assoc, inv_mul_cancel₀ hvu, mul_one, sub_add_cancel]
  intro u v u' v' huv hu'v'
  rw [paleyField_adj hq] at huv hu'v'
  simp only [decide_eq_true_eq] at huv hu'v'
  exact key u v u' v' huv hu'v'

@[inherit_doc isArcTransitive_paleyField, toIsoGraph]
theorem isArcTransitive_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).IsArcTransitive :=
  isArcTransitive_of_iso (paleyIso q) (isArcTransitive_paleyField (ZMod q)
    (by rw [← @FinEnum.card_eq_fintypeCard (ZMod q) _ FinEnum.instFintype]; exact hq))

/-! ### Hypercubes

Adding a fixed bit-string is an automorphism of both the hypercube and the folded cube: it does
not change *which* coordinates two strings differ in. -/

theorem xorPerm_involutive (n : ℕ) (d : Fin n → Bool) :
    Function.Involutive (fun x : Fin n → Bool ↦ fun i ↦ x i ^^ d i) := fun x ↦ by
  funext i
  simp

theorem filter_xor_eq (n : ℕ) (d x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ (x i ^^ d i) ≠ (y i ^^ d i)) =
      (Finset.univ.filter fun i ↦ x i ≠ y i) :=
  Finset.filter_congr fun i _ ↦ by
    simp only [ne_eq]
    constructor
    · intro h he; exact h (by rw [he])
    · intro h he; exact h (Bool.xor_left_inj.1 he)

/-- The same, for the count the cube families are defined by. -/
theorem countP_xor_eq (n : ℕ) (d x y : Fin n → Bool) :
    ((List.finRange n).countP fun i ↦ (x i ^^ d i) != (y i ^^ d i))
      = (List.finRange n).countP fun i ↦ x i != y i :=
  List.countP_congr fun i _ ↦ by cases x i <;> cases y i <;> cases d i <;> rfl

/-- The same again, in the form the two `Adj` fields are actually written in. -/
theorem hammingBelow_xor (n : ℕ) (d x y : Fin n → Bool) :
    hammingBelow (fun i ↦ x i ^^ d i) (fun i ↦ y i ^^ d i) n = hammingBelow x y n := by
  rw [hammingBelow_self, hammingBelow_self, countP_xor_eq]

theorem isVertexTransitive_hypercube (n : ℕ) : (hypercube n).IsVertexTransitive := by
  rw [hypercube_eq_ofRel]
  refine isVertexTransitive_ofRel _ _ fun u v ↦
    ⟨(xorPerm_involutive n fun i ↦ u i ^^ v i).toPerm _, fun x y ↦ ?_, ?_⟩
  · show ((Finset.univ.filter fun i ↦ (x i ^^ _) ≠ (y i ^^ _)).card == 1 ||
      (Finset.univ.filter fun i ↦ (y i ^^ _) ≠ (x i ^^ _)).card == 1) = _
    rw [filter_xor_eq, filter_xor_eq]
  · funext i
    show (u i ^^ (u i ^^ v i)) = v i
    simp

theorem isArcTransitive_bipartite_self (n : ℕ) : (bipartite n n).IsArcTransitive := by
  rintro u v u' v' huv hu'v'
  rcases bipartite_arc n n u v huv with ⟨a, b, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ <;>
    rcases bipartite_arc n n u' v' hu'v' with ⟨a', b', rfl, rfl⟩ | ⟨a', b', rfl, rfl⟩
  · exact ⟨bipartiteCongr n (Equiv.swap a a') (Equiv.swap b b'), by simp, by simp⟩
  · exact ⟨(bipartiteCongr n (Equiv.swap a b') (Equiv.swap b a')).trans (bipartiteSwap n),
      by simp, by simp⟩
  · exact ⟨(bipartiteSwap n).trans (bipartiteCongr n (Equiv.swap b a') (Equiv.swap a b')),
      by simp, by simp⟩
  · exact ⟨bipartiteCongr n (Equiv.swap a a') (Equiv.swap b b'), by simp, by simp⟩

theorem isVertexTransitive_bipartite_self (n : ℕ) : (bipartite n n).IsVertexTransitive := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rintro (u | u) <;> exact (u : Fin 0).elim0
  · refine isVertexTransitive_of_isArcTransitive _ (fun u ↦ ?_) (isArcTransitive_bipartite_self n)
    rcases u with a | b
    · exact ⟨.inr ⟨0, hn⟩, by simp⟩
    · exact ⟨.inl ⟨0, hn⟩, by simp⟩

/-- An arc-transitive graph has a vertex-transitive line graph. -/
theorem isVertexTransitive_lineGraph (h : G.IsArcTransitive) :
    (lineGraph G).IsVertexTransitive := by
  have key : ∀ (u v u' v' : G.V) (huv : s(u, v) ∈ G.toSimple.edgeSet)
      (hu'v' : s(u', v') ∈ G.toSimple.edgeSet),
      ∃ σ : lineGraph G ≃cg lineGraph G,
        σ (⟨s(u, v), huv⟩ : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) = ⟨s(u', v'), hu'v'⟩ := by
    intro u v u' v' huv hu'v'
    obtain ⟨σ, h₁, h₂⟩ := h u v u' v' (by simpa using huv) (by simpa using hu'v')
    refine ⟨G.lineGraphAuto σ, ?_⟩
    show G.edgePerm σ ⟨s(u, v), huv⟩ = _
    exact Subtype.ext (by simp [edgePerm_coe, h₁, h₂])
  rintro ⟨e, he⟩ ⟨f, hf⟩
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ u' v' => exact key u v u' v' he hf

theorem isArcTransitive_kneser (n k : ℕ) : (kneser n k).IsArcTransitive := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨A', hA'⟩ ⟨B', hB'⟩ h h'
  simp only [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at h h'
  obtain ⟨π, hπA, hπB⟩ := exists_perm_image₂
    (Finset.disjoint_iff_inter_eq_empty.2 h.2) (Finset.disjoint_iff_inter_eq_empty.2 h'.2)
    (hA.trans hA'.symm) (hB.trans hB'.symm)
  exact ⟨kneserAuto n k π, Subtype.ext hπA, Subtype.ext hπB⟩

/-- Kneser graphs are vertex-transitive.  This does not go through
`isVertexTransitive_of_isArcTransitive`, which would need `kneser n k` to have an arc at all:
`exists_perm_image₂` with both second components empty does it directly. -/
theorem isVertexTransitive_kneser (n k : ℕ) : (kneser n k).IsVertexTransitive := by
  rintro ⟨A, hA⟩ ⟨A', hA'⟩
  obtain ⟨π, hπ, -⟩ := exists_perm_image₂ (Finset.disjoint_empty_right A)
    (Finset.disjoint_empty_right A') (hA.trans hA'.symm) rfl
  exact ⟨kneserAuto n k π, Subtype.ext hπ⟩

/-- The two ends of an edge of a Johnson graph share all but one of their points: `A` is the
common part with one point of its own added, and so is `B`. -/
private theorem johnson_arc_decomp {n k : ℕ} {A B : Finset (Fin n)}
    (hA : A.card = k) (hB : B.card = k) (hne : A ≠ B) (hcap : (A ∩ B).card = k - 1) :
    ∃ a b, a ∉ B ∧ b ∉ A ∧ A = insert a (A ∩ B) ∧ B = insert b (A ∩ B) := by
  classical
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd ((Finset.card_eq_zero.1 hA).trans (Finset.card_eq_zero.1 hB).symm) hne
    · exact h
  have hAB : (A \ B).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter A B
    omega
  have hBA : (B \ A).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at h
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hAB
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hBA
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · exact (Finset.mem_sdiff.1 (ha ▸ Finset.mem_singleton_self a)).2
  · exact (Finset.mem_sdiff.1 (hb ▸ Finset.mem_singleton_self b)).2
  · rw [Finset.insert_eq, ← ha]
    exact (Finset.sdiff_union_inter A B).symm
  · rw [Finset.insert_eq, ← hb, Finset.inter_comm A B]
    exact (Finset.sdiff_union_inter B A).symm

/-- **Johnson graphs are arc-transitive.**  Write the two ends of an arc as `C ∪ {a}` and
`C ∪ {b}`.  A permutation carrying `C` to `C'` and `a` to `a'` exists by `exists_perm_image₂`,
and it must send `b` outside `A'`; composing with the transposition of its image and `b'` fixes
`A'` pointwise and lands `b` on `b'`. -/
theorem isArcTransitive_johnson (n k : ℕ) : (johnson n k).IsArcTransitive := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨A', hA'⟩ ⟨B', hB'⟩ h h'
  simp only [johnson_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Subtype.mk.injEq,
    beq_iff_eq] at h h'
  obtain ⟨a, b, haB, hbA, hAeq, hBeq⟩ := johnson_arc_decomp hA hB h.1 h.2
  obtain ⟨a', b', ha'B', hb'A', hA'eq, hB'eq⟩ := johnson_arc_decomp hA' hB' h'.1 h'.2
  obtain ⟨π, hπC, hπa⟩ := exists_perm_image₂
    (Finset.disjoint_singleton_right.2 fun hm ↦ haB (Finset.mem_inter.1 hm).2)
    (Finset.disjoint_singleton_right.2 fun hm ↦ ha'B' (Finset.mem_inter.1 hm).2)
    (h.2.trans h'.2.symm) rfl
  rw [Finset.image_singleton, Finset.singleton_inj] at hπa
  have himA : A.image π = A' := by
    rw [hAeq, Finset.image_insert, hπC, hπa, ← hA'eq]
  have hπbA' : π b ∉ A' := by
    rw [← himA]
    intro hm
    obtain ⟨c, hc, hcb⟩ := Finset.mem_image.1 hm
    exact hbA (π.injective hcb ▸ hc)
  have hfix : ∀ x ∈ A', Equiv.swap (π b) b' x = x := fun x hx ↦
    Equiv.swap_apply_of_ne_of_ne (fun hh ↦ hπbA' (hh ▸ hx)) (fun hh ↦ hb'A' (hh ▸ hx))
  have hfixS : ∀ S : Finset (Fin n), S ⊆ A' → S.image (Equiv.swap (π b) b') = S := by
    intro S hS
    refine Finset.ext fun x ↦ ?_
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hfix y (hS hy)]
    · exact fun hx ↦ ⟨x, hx, hfix x (hS hx)⟩
  refine ⟨johnsonAuto n k (π.trans (Equiv.swap (π b) b')), Subtype.ext ?_, Subtype.ext ?_⟩
  · show A.image (⇑(π.trans (Equiv.swap (π b) b'))) = A'
    rw [Equiv.coe_trans, ← Finset.image_image, himA, hfixS A' Finset.Subset.rfl]
  · show B.image (⇑(π.trans (Equiv.swap (π b) b'))) = B'
    rw [Equiv.coe_trans, ← Finset.image_image, hBeq, Finset.image_insert, hπC,
      Finset.image_insert, Equiv.swap_apply_left, hfixS (A' ∩ B') Finset.inter_subset_left,
      ← hB'eq]

/-- Johnson graphs are vertex-transitive.  As for `isVertexTransitive_kneser`, this does not go
through `isVertexTransitive_of_isArcTransitive`: `exists_perm_image₂` with both second
components empty produces the permutation directly. -/
theorem isVertexTransitive_johnson (n k : ℕ) : (johnson n k).IsVertexTransitive := by
  rintro ⟨A, hA⟩ ⟨A', hA'⟩
  obtain ⟨π, hπ, -⟩ := exists_perm_image₂ (Finset.disjoint_empty_right A)
    (Finset.disjoint_empty_right A') (hA.trans hA'.symm) rfl
  exact ⟨johnsonAuto n k π, Subtype.ext hπ⟩

end

section
variable {G H : CGraph}

/-- A graph with `α · ω > |V|` cannot be vertex-transitive. -/
theorem not_isVertexTransitive_of_card_lt (G : CGraph)
    (h : FinEnum.card G.V < G.indepNum * G.cliqueNum) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.indepNum_mul_cliqueNum_le_card hvt) (by omega)

end

end CGraph

namespace IsoGraph

/-- A regular graph's line graph has `n * C(k, 2)` edges. -/
theorem IsSRGWith.E_lineGraph {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    (lineGraph G).E = n * k.choose 2 := by
  rw [IsoGraph.E_lineGraph, h.degSequence, List.map_replicate, List.sum_replicate, smul_eq_mul]

/-! ### The clique–coclique bound -/

/-- Contrapositive: `α · ω > |V|` is a certificate of *non*-vertex-transitivity, and one that is
independent of the usual degree-sequence obstruction. -/
theorem not_isVertexTransitive_of_V_lt {G : IsoGraph} (h : G.V < G.indepNum * G.cliqueNum) :
    ¬ IsVertexTransitive G := fun hvt ↦ absurd (indepNum_mul_cliqueNum_le_V hvt) (by omega)

/-! ### Regular graphs -/

/-- **The handshake lemma for regular graphs**: `2|E| = k|V|`. -/
theorem IsRegularWith.two_mul_E {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    2 * G.E = G.V * k := two_mul_E_of_degSequence_replicate h.degSequence

/-- **A vertex-transitive graph is regular**, of degree its common vertex degree. -/
theorem exists_isRegularWith_of_isVertexTransitive {G : IsoGraph} (h : IsVertexTransitive G) :
    ∃ k, G.IsRegularWith k := by
  obtain ⟨k, hk⟩ := exists_degSequence_replicate_of_isVertexTransitive h
  exact ⟨k, isRegularWith_of_degSequence hk⟩

/-! #### Regularity of the constructions -/

/-- **The Cartesian product of a `k`-regular and an `l`-regular graph is `(k + l)`-regular.** -/
theorem IsRegularWith.cartesianProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G □g H).IsRegularWith (k + l) :=
  isRegularWith_of_degSequence (degSequence_cartesianProduct hG.degSequence hH.degSequence)

/-- **The tensor product multiplies the degrees.** -/
theorem IsRegularWith.tensorProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G ⊗g H).IsRegularWith (k * l) :=
  isRegularWith_of_degSequence (degSequence_tensorProduct hG.degSequence hH.degSequence)

/-- **The strong product**, being the union of the other two, has degree `(k+1)(l+1) - 1`. -/
theorem IsRegularWith.strongProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G ⊠g H).IsRegularWith ((k + 1) * (l + 1) - 1) :=
  isRegularWith_of_degSequence (degSequence_strongProduct hG.degSequence hH.degSequence)

/-- **The lexicographic product**: a vertex sees `k` whole copies of `H` plus its `l` neighbours
inside its own copy. -/
theorem IsRegularWith.lexProduct {G H : IsoGraph} {k l : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith l) : (G ·g H).IsRegularWith (k * H.V + l) :=
  isRegularWith_of_degSequence (degSequence_lexProduct hG.degSequence hH.degSequence)

/-! #### The regularity table -/

@[simp] theorem isRegularWith_empty (n : ℕ) : (empty n).IsRegularWith 0 :=
  isRegularWith_of_degSequence (degSequence_empty n)

@[simp] theorem isRegularWith_complete (n : ℕ) : (complete n).IsRegularWith (n - 1) :=
  isRegularWith_of_degSequence (degSequence_complete n)

@[simp] theorem isRegularWith_cycle (n : ℕ) : (cycle (n + 3)).IsRegularWith 2 :=
  isRegularWith_of_degSequence (degSequence_cycle n)

/-- The chromatic index of a `k`-regular graph is at least `k`. -/
theorem IsRegularWith.le_edgeChromNum {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : k ≤ G.edgeChromNum := by
  rw [← h.maxDeg_eq hV]
  exact maxDeg_le_edgeChromNum G

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

/-! ### The common degree of a vertex-transitive graph -/

theorem isRegularWith_minDeg_of_isVertexTransitive {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) : G.IsRegularWith G.minDeg := by
  obtain ⟨k, hk⟩ := exists_isRegularWith_of_isVertexTransitive h
  rwa [hk.minDeg_eq hV]

/-- The cycle is arc-transitive with `n` edges; its automorphism group is in fact exactly the
dihedral group of that order. -/
theorem two_mul_le_autCount_cycle (n : ℕ) : 2 * (n + 3) ≤ (cycle (n + 3)).autCount := by
  have h := two_mul_E_le_autCount_of_isArcTransitive (isArcTransitive_cycle (n + 3))
  rw [E_cycle] at h
  omega

/-- **The Mycielskian of a `k`-regular graph is never vertex-transitive for `k ≥ 2`.**  The
shadow of a vertex keeps degree `k`, but the apex is joined to all `|V|` shadows and the
original vertices double their degree to `2k`; since `k + 1 ≤ |V|` and `k + 2 ≤ 2k`, the
minimum degree `k + 1` falls short of the maximum. -/
theorem not_isVertexTransitive_mycielskian {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hk : 2 ≤ k) (hV : 0 < G.V) : ¬ IsVertexTransitive (mycielskian G) := by
  have hlt : maxDeg G < G.V := maxDeg_lt_V hV
  have hmax : maxDeg G = k := h.maxDeg_eq hV
  have hmin : minDeg G = k := h.minDeg_eq hV
  refine not_isVertexTransitive_of_minDeg_ne_maxDeg (by simp) ?_
  rw [minDeg_mycielskian G hV, maxDeg_mycielskian G, hmax, hmin]
  omega

/-- In particular the Grötzsch graph's parent `C₅` is `2`-regular; the same argument covers every
Mycielskian tower step. -/
theorem not_isVertexTransitive_mycielskian_cycle (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (cycle (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_cycle n) (by omega) (by simp)

/-! ### The negative entries of the arc-transitivity column

Arc-transitivity implies vertex-transitivity as soon as there are no isolated vertices, so every
negative vertex-transitivity entry is also a negative arc-transitivity entry.  The lift of
`CGraph.isVertexTransitive_of_isArcTransitive_of_minDeg_pos` to the quotient states "no isolated
vertices" as `0 < δ`.
-/

/-- The contrapositive, which is how the whole column below is filled. -/
theorem not_isArcTransitive_of_not_isVertexTransitive {G : IsoGraph} (hδ : 0 < G.minDeg)
    (h : ¬ IsVertexTransitive G) : ¬ IsArcTransitive G :=
  fun ha ↦ h (ha.isVertexTransitive hδ)

@[simp] theorem not_isArcTransitive_path (n : ℕ) : ¬ IsArcTransitive (path (n + 3)) :=
  not_isArcTransitive_of_not_isVertexTransitive
    (by rw [show n + 3 = n + 1 + 2 from rfl, minDeg_path]; omega) (not_isVertexTransitive_path n)

theorem two_mul_le_autCount_compl_cycle (n : ℕ) :
    2 * (n + 3) ≤ ((cycle (n + 3))ᶜ).autCount := by
  rw [autCount_compl]
  exact two_mul_le_autCount_cycle n

theorem not_isArcTransitive_mycielskian {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hk : 2 ≤ k) (hV : 0 < G.V) : ¬ IsArcTransitive (mycielskian G) := by
  refine not_isArcTransitive_of_not_isVertexTransitive ?_
    (not_isVertexTransitive_mycielskian h hk hV)
  refine minDeg_mycielskian_pos hV ?_
  rw [h.minDeg_eq hV]
  omega

theorem not_isArcTransitive_mycielskian_cycle (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (cycle (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_cycle n) (by omega) (by simp)

theorem not_isVertexTransitive_mycielskian_complete (n : ℕ) :
    ¬ IsVertexTransitive (mycielskian (complete (n + 3))) :=
  not_isVertexTransitive_mycielskian (isRegularWith_complete (n + 3)) (by omega)
    (by rw [V_complete]; omega)

theorem not_isArcTransitive_mycielskian_complete (n : ℕ) :
    ¬ IsArcTransitive (mycielskian (complete (n + 3))) :=
  not_isArcTransitive_mycielskian (isRegularWith_complete (n + 3)) (by omega)
    (by rw [V_complete]; omega)

/-! ### Which of the named families are regular

Every family whose minimum and maximum degree are already known can be settled at once: a
`k`-regular graph on a nonempty vertex set has `minDeg = k = maxDeg`, so the two being different
rules out regularity of *every* degree.  The positive entries (`isRegularWith_cycle`,
`isRegularWith_petersen`, …) are already in the library; these are the negative ones. -/

theorem not_isRegularWith_of_minDeg_ne_maxDeg {G : IsoGraph} (hV : 0 < G.V)
    (h : G.minDeg ≠ G.maxDeg) (k : ℕ) : ¬ G.IsRegularWith k := by
  intro hreg
  exact h ((hreg.minDeg_eq hV).trans (hreg.maxDeg_eq hV).symm)

theorem not_isRegularWith_path (n k : ℕ) : ¬ IsRegularWith (path (n + 3)) k := by
  have hmin : minDeg (path (n + 3)) = 1 := minDeg_path (n + 1)
  have hmax : maxDeg (path (n + 3)) = 2 := maxDeg_path n
  exact not_isRegularWith_of_minDeg_ne_maxDeg (by rw [V_path]; omega) (by omega) k

end IsoGraph
