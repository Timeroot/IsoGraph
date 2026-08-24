import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Common

/-!
# Lemmas about lists

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

/-- Extend a bijection of index sets to lists with one more element in front. -/
def List.consFinEquiv {m n : ℕ} (σ : Fin m ≃ Fin n) : Fin (m + 1) ≃ Fin (n + 1) where
  toFun := Fin.cases 0 fun i ↦ (σ i).succ
  invFun := Fin.cases 0 fun j ↦ (σ.symm j).succ
  left_inv i := by induction i using Fin.cases <;> simp
  right_inv j := by induction j using Fin.cases <;> simp

/-- Two lists that are permutations of one another admit a bijection of index sets matching their
entries.  There is no `Nodup` hypothesis: the bijection is read off the derivation of the
permutation, not off the elements. -/
theorem List.Perm.exists_finEquiv {α : Type*} {l₁ l₂ : List α} (h : List.Perm l₁ l₂) :
    ∃ σ : Fin l₁.length ≃ Fin l₂.length, ∀ i, l₂.get (σ i) = l₁.get i := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i ↦ i.elim0⟩
  | cons x _ ih =>
      obtain ⟨σ, hσ⟩ := ih
      refine ⟨List.consFinEquiv σ, fun i ↦ ?_⟩
      induction i using Fin.cases with
      | zero => rfl
      | succ i => simpa [List.consFinEquiv] using hσ i
  | swap x y l =>
      refine ⟨Equiv.swap 0 1, fun i ↦ ?_⟩
      induction i using Fin.cases with
      | zero => simp
      | succ i =>
          induction i using Fin.cases with
          | zero => simp
          | succ i =>
              have h : (Equiv.swap (0 : Fin (l.length + 1 + 1)) 1) i.succ.succ = i.succ.succ := by
                apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff]
              exact congrArg (List.get (x :: y :: l)) h
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨σ₁, h₁⟩ := ih₁
      obtain ⟨σ₂, h₂⟩ := ih₂
      exact ⟨σ₁.trans σ₂, fun i ↦ by rw [Equiv.trans_apply, h₂, h₁]⟩

/-- A member of a list that differs from `y` is still a member after `y` is erased.  This is
`List.mem_erase_of_ne` with the arguments in the order the girth wrappers below need them. -/
theorem mem_erase_of_ne_of_mem {α : Type*} [DecidableEq α] {x y : α} {l : List α} (hne : x ≠ y)
    (hx : x ∈ l) : x ∈ l.erase y :=
  (List.mem_erase_of_ne hne).2 hx

/-- The third entry of a list without duplicates differs from the first. -/
theorem ne_of_nodup_cons₂ {α : Type*} {x y z : α} {l : List α}
    (h : (x :: y :: z :: l).Nodup) : z ≠ x := by
  rintro rfl
  exact (List.nodup_cons.1 h).1 (by simp)

theorem getLastD_eq_getElem {α : Type*} (vs : List α) (u : α) :
    vs.getLastD u = (u :: vs)[vs.length]'(by simp) := by
  induction vs generalizing u with
  | nil => rfl
  | cons a t ih => rw [List.getLastD_cons, ih a]; simp

theorem getLastD_map {α β : Type*} (f : α → β) (l : List α) (d : α) :
    (l.map f).getLastD (f d) = f (l.getLastD d) := by
  induction l generalizing d with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.getLastD_cons]; exact ih a

/-- Some element of a nonempty list maximises a given weight. -/
theorem exists_max_weight {V : Type*} (f : V → ℕ) (u : V) (vs : List V) :
    ∃ x ∈ u :: vs, ∀ y ∈ u :: vs, f y ≤ f x := by
  induction vs generalizing u with
  | nil => exact ⟨u, by simp, by simp⟩
  | cons a t ih =>
      obtain ⟨x, hx, hmax⟩ := ih a
      rcases Nat.lt_or_ge (f u) (f x) with h | h
      · refine ⟨x, List.mem_cons_of_mem u hx, fun y hy ↦ ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy'
        · omega
        · exact hmax y hy'
      · refine ⟨u, by simp, fun y hy ↦ ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax y hy') h

/-- The shifted range `[c, c + 1, …, c + m - 1]`, as a membership test. -/
theorem List.mem_map_add_range (c m w : ℕ) :
    w ∈ (List.range m).map (fun i ↦ c + i) ↔ c ≤ w ∧ w < c + m := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨w - c, by omega, by omega⟩
