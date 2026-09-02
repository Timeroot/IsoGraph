import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Common

/-!
# Real sums and a sum-to-product identity

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

theorem sum_ite_eq_fin (n : ℕ) (g : ℕ → ℝ) (k : ℕ) (hk : n ≤ k → g k = 0) :
    ∑ j : Fin n, (if k = j.1 then g j.1 else 0) = g k := by
  rcases lt_or_ge k n with hkn | hkn
  · rw [Finset.sum_eq_single (⟨k, hkn⟩ : Fin n)]
    · simp
    · intro b _ hb
      exact ite_eq_right fun h ↦ hb (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hk hkn]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have := j.isLt
    exact ite_eq_right (by omega)

theorem sum_ite_succ_fin (n : ℕ) (c : ℝ) (k : ℕ) (hk : k = 0 → c = 0) (hkn : k < n) :
    ∑ j : Fin n, (if j.1 + 1 = k then c else 0) = c := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk hk0]
    refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by omega)
  · have hk1 : k - 1 < n := by omega
    rw [Finset.sum_eq_single (⟨k - 1, hk1⟩ : Fin n)]
    · exact ite_eq_left (by show k - 1 + 1 = k; omega)
    · intro b _ hb
      exact ite_eq_right fun h ↦ hb (Fin.ext (by show b.1 = k - 1; omega))
    · intro h; exact absurd (Finset.mem_univ _) h

theorem sin_sub_add_sin_add (a t : ℝ) :
    Real.sin (t - a) + Real.sin (t + a) = 2 * Real.cos a * Real.sin t := by
  rw [Real.sin_sub, Real.sin_add]; ring
