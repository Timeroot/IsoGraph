import Mathlib.InformationTheory.Hamming

/-!
# Hamming distance between bit-strings

`hammingDist x y` counts the coordinates at which `x` and `y` differ.  Mathlib develops it for an
arbitrary family of types; the cube-like graphs need the Boolean case, where the two extreme
values of the distance have a closed description — `0` means `x = y`, and `Fintype.card ι` means
`x` is the pointwise negation of `y` — and where the elementary move is a single coordinate flip.

The lemmas below are exactly that: the characterisation of the maximal distance, the effect of
negating one argument, and the facts about `Function.update x i (!x i)` that make a coordinate
flip a step of length one — including the converse, that distance one is *always* a coordinate
flip.
-/

open Finset

section Bool

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem bool_ne_iff (a b : Bool) : a ≠ b ↔ a = !b := by decide +revert

omit [DecidableEq ι] in
/-- Two bit-strings are at the maximal Hamming distance exactly when each is the pointwise
negation of the other. -/
theorem hammingDist_eq_card_iff {x y : ι → Bool} :
    hammingDist x y = Fintype.card ι ↔ ∀ i, x i = !y i := by
  constructor
  · intro h i
    have hu : Finset.univ.filter (fun j ↦ x j ≠ y j) = Finset.univ :=
      Finset.eq_univ_of_card _ h
    have hi : i ∈ Finset.univ.filter (fun j ↦ x j ≠ y j) := by rw [hu]; exact Finset.mem_univ i
    exact (bool_ne_iff _ _).1 (Finset.mem_filter.1 hi).2
  · intro h
    rw [hammingDist, Finset.filter_true_of_mem fun i _ ↦ (bool_ne_iff _ _).2 (h i),
      Finset.card_univ]

/-- Negating the first argument complements the set of differing coordinates. -/
theorem hammingDist_not_left (x y : ι → Bool) :
    hammingDist (fun i ↦ !x i) y = Fintype.card ι - hammingDist x y := by
  simp only [hammingDist]
  rw [show Finset.univ.filter (fun i ↦ (!x i) ≠ y i) =
      (Finset.univ.filter fun i ↦ x i ≠ y i)ᶜ by
    ext i; cases hx : x i <;> cases hy : y i <;> simp [hx, hy]]
  exact Finset.card_compl _

/-- Negating the second argument complements the set of differing coordinates. -/
theorem hammingDist_not_right (x y : ι → Bool) :
    hammingDist x (fun i ↦ !y i) = Fintype.card ι - hammingDist x y := by
  rw [hammingDist_comm, hammingDist_not_left, hammingDist_comm]

/-- Flipping a coordinate at which `x` and `y` already differ brings them one step closer. -/
theorem hammingDist_update_not_left {x y : ι → Bool} {i : ι} (h : x i ≠ y i) :
    hammingDist (Function.update x i (!x i)) y = hammingDist x y - 1 := by
  simp only [hammingDist]
  rw [show Finset.univ.filter (fun j ↦ Function.update x i (!x i) j ≠ y j) =
      (Finset.univ.filter fun j ↦ x j ≠ y j).erase i by
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [Function.update_self, (bool_ne_iff _ _).1 h]
    · simp [hj]]
  rw [Finset.card_erase_of_mem (by simpa using h)]

/-- Flipping coordinate `i` changes `x` at `i` and nowhere else. -/
theorem filter_ne_update_not (x : ι → Bool) (i : ι) :
    Finset.univ.filter (fun j ↦ x j ≠ Function.update x i (!x i) j) = {i} := by
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp [Function.update_self, bool_ne_iff]
  · simp [hj]

/-- A single coordinate flip is one Hamming step. -/
@[simp] theorem hammingDist_update_not_self (x : ι → Bool) (i : ι) :
    hammingDist x (Function.update x i (!x i)) = 1 := by
  rw [hammingDist, filter_ne_update_not, Finset.card_singleton]

/-- Two bit-strings are one apart exactly when one is the other with a single coordinate
flipped. -/
theorem hammingDist_eq_one_iff {x y : ι → Bool} :
    hammingDist x y = 1 ↔ ∃ i, y = Function.update x i (!x i) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h
    refine ⟨i, funext fun j ↦ ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · have hmem : j ∈ Finset.univ.filter (fun j ↦ x j ≠ y j) := by
        rw [hi]; exact Finset.mem_singleton_self j
      have hne := (Finset.mem_filter.1 hmem).2
      rw [Function.update_self]
      revert hne; cases x j <;> cases y j <;> simp
    · have hmem : j ∉ Finset.univ.filter (fun j ↦ x j ≠ y j) := by
        rw [hi]; simpa using hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] at hmem
      rw [Function.update_of_ne hj, hmem]
  · rintro ⟨i, rfl⟩
    exact hammingDist_update_not_self x i

end Bool
