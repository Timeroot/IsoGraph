import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Common

/-!
# Permutations moving prescribed points

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

/-- Any two ordered pairs of distinct points are matched by some permutation: swap `u` with `u'`,
then swap the image of `v` with `v'`.  (On a *complete* graph every such permutation is an
automorphism, which is why this gives arc-transitivity there.) -/
theorem exists_perm_apply_apply {α : Type} [DecidableEq α] {u v u' v' : α} (h : u ≠ v)
    (h' : u' ≠ v') : ∃ σ : Equiv.Perm α, σ u = u' ∧ σ v = v' := by
  have key : Equiv.swap u u' v ≠ u' := by
    intro e
    exact h ((Equiv.swap u u').injective (by rw [e, Equiv.swap_apply_left])).symm
  refine ⟨(Equiv.swap u u').trans (Equiv.swap (Equiv.swap u u' v) v'), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm key) h'
  · simp

/-- Two disjoint pairs of finsets of matching sizes are related by a permutation of the whole
(finite) type: match up the two parts, and the two complements with each other. -/
theorem exists_perm_image₂ {α : Type} [Fintype α] [DecidableEq α] {A B A' B' : Finset α}
    (hAB : Disjoint A B) (hA'B' : Disjoint A' B') (hA : A.card = A'.card)
    (hB : B.card = B'.card) : ∃ π : Equiv.Perm α, A.image π = A' ∧ B.image π = B' := by
  classical
  set C : Finset α := (A ∪ B)ᶜ with hC
  set C' : Finset α := (A' ∪ B')ᶜ with hC'
  have hCcard : C.card = C'.card := by
    rw [hC, hC', Finset.card_compl, Finset.card_compl, Finset.card_union_of_disjoint hAB,
      Finset.card_union_of_disjoint hA'B', hA, hB]
  let eA := Finset.equivOfCardEq hA
  let eB := Finset.equivOfCardEq hB
  let eC := Finset.equivOfCardEq hCcard
  set f : α → α := fun x ↦
      if h : x ∈ A then (eA ⟨x, h⟩ : α)
      else if h' : x ∈ B then (eB ⟨x, h'⟩ : α)
      else (eC ⟨x, by simp [hC, h, h']⟩ : α) with hf
  have hfA : ∀ x (h : x ∈ A), f x = eA ⟨x, h⟩ := fun x h ↦ by simp [hf, h]
  have hfB : ∀ x (h : x ∉ A) (h' : x ∈ B), f x = eB ⟨x, h'⟩ := fun x h h' ↦ by simp [hf, h, h']
  have hfC : ∀ x (h : x ∉ A) (h' : x ∉ B), f x ∈ C' := fun x h h' ↦ by
    rw [hf]; simp only [h, h', dite_false]
    exact (eC ⟨x, by simp [hC, h, h']⟩).2
  have hmemA : ∀ x, x ∈ A → f x ∈ A' := fun x h ↦ by rw [hfA x h]; exact (eA ⟨x, h⟩).2
  have hmemB : ∀ x, x ∈ B → f x ∈ B' := fun x h ↦ by
    have hxA : x ∉ A := Finset.disjoint_right.1 hAB h
    rw [hfB x hxA h]; exact (eB ⟨x, h⟩).2
  have hC'mem : ∀ x, x ∈ C' → x ∉ A' ∧ x ∉ B' := by
    intro x hx
    rw [hC', Finset.mem_compl, Finset.mem_union] at hx
    exact ⟨fun h ↦ hx (Or.inl h), fun h ↦ hx (Or.inr h)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · have : (eA ⟨x, hxA⟩ : α) = eA ⟨y, hyA⟩ := by rw [← hfA x hxA, ← hfA y hyA, hxy]
      simpa using congrArg Subtype.val (eA.injective (Subtype.ext this))
    · by_cases hyB : y ∈ B
      · have h1 : f y ∈ A' := by rw [← hxy]; exact hmemA x hxA
        exact absurd (hmemB y hyB) (Finset.disjoint_left.1 hA'B' h1)
      · have h1 : f y ∈ A' := by rw [← hxy]; exact hmemA x hxA
        exact absurd h1 (hC'mem _ (hfC y hyA hyB)).1
    · by_cases hxB : x ∈ B
      · have h1 : f x ∈ A' := by rw [hxy]; exact hmemA y hyA
        exact absurd (hmemB x hxB) (Finset.disjoint_left.1 hA'B' h1)
      · have h1 : f x ∈ A' := by rw [hxy]; exact hmemA y hyA
        exact absurd h1 (hC'mem _ (hfC x hxA hxB)).1
    · by_cases hxB : x ∈ B <;> by_cases hyB : y ∈ B
      · have : (eB ⟨x, hxB⟩ : α) = eB ⟨y, hyB⟩ := by
          rw [← hfB x hxA hxB, ← hfB y hyA hyB, hxy]
        simpa using congrArg Subtype.val (eB.injective (Subtype.ext this))
      · have h1 : f y ∈ B' := by rw [← hxy]; exact hmemB x hxB
        exact absurd h1 (hC'mem _ (hfC y hyA hyB)).2
      · have h1 : f x ∈ B' := by rw [hxy]; exact hmemB y hyB
        exact absurd h1 (hC'mem _ (hfC x hxA hxB)).2
      · have hx : f x = eC ⟨x, by simp [hC, hxA, hxB]⟩ := by
          rw [hf]; simp only [hxA, hxB, dite_false]
        have hy : f y = eC ⟨y, by simp [hC, hyA, hyB]⟩ := by
          rw [hf]; simp only [hyA, hyB, dite_false]
        have : (eC ⟨x, by simp [hC, hxA, hxB]⟩ : α) = eC ⟨y, by simp [hC, hyA, hyB]⟩ := by
          rw [← hx, ← hy, hxy]
        simpa using congrArg Subtype.val (eC.injective (Subtype.ext this))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ?_, ?_⟩
  · show A.image f = A'
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmemA x hx
    · rw [Finset.card_image_of_injective _ hinj, hA]
  · show B.image f = B'
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmemB x hx
    · rw [Finset.card_image_of_injective _ hinj, hB]
