import Mathlib.Tactic.Common

/-!
# Lemmas about `decide`

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

/-- `decide` of an equality is symmetric.  Stated as a `Bool` equation rather than reached
through `eq_comm`, so that `rw` can use it inside a `decide` without a motive problem. -/
theorem decide_eq_comm {α : Type} [DecidableEq α] (a b : α) :
    decide (a = b) = decide (b = a) := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- `decide` of a disequality is symmetric; the companion of `decide_eq_comm`. -/
theorem decide_ne_comm {α : Type} [DecidableEq α] (a b : α) :
    decide (a ≠ b) = decide (b ≠ a) := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- Equality of pairs, as a `Bool`: it splits into the two component tests. -/
theorem decide_prod_eq {α β : Type} [DecidableEq α] [DecidableEq β] (p q : α × β) :
    decide (p = q) = (decide (p.1 = q.1) && decide (p.2 = q.2)) :=
  (decide_eq_decide.2 Prod.ext_iff).trans (Bool.decide_and _ _)
