import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arithmetic lemmas

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [Nat.choose_succ_succ]
  show j.choose 1 + j.choose 2 = j.choose 2 + j
  rw [Nat.choose_one_right, Nat.add_comm]

/-- Splitting `a + b` points into two groups splits the pairs into three kinds. -/
theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, choose_two_succ, choose_two_succ, ih]
    ring

theorem choose_two_two_mul (n : ℕ) : (2 * n).choose 2 = n * (2 * n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem choose_two_two_mul_add_one (n : ℕ) : (2 * n + 1).choose 2 = n * (2 * n + 1) := by
  rw [Nat.choose_two_right, show 2 * n + 1 - 1 = 2 * n from rfl,
    show (2 * n + 1) * (2 * n) = 2 * (n * (2 * n + 1)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have h : n.descFactorial 2 = Nat.factorial 2 * n.choose 2 :=
    Nat.descFactorial_eq_factorial_mul_choose n 2
  rw [show n.descFactorial 2 = (n - 1) * (n * 1) from rfl,
    show Nat.factorial 2 = 2 from rfl] at h
  rw [← h]
  ring

theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h : n.descFactorial 3 = Nat.factorial 3 * n.choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose n 3
  rw [show n.descFactorial 3 = (n - 2) * ((n - 1) * (n * 1)) from rfl,
    show Nat.factorial 3 = 6 from rfl] at h
  rw [← h]
  ring

/-- Three disjoint pairs out of `n` points, picked one after another.  The `90` is `6!/(2!)³`,
the number of ways to cut six points into an ordered triple of pairs. -/
theorem choose_two_mul_choose_two_mul_choose_two (n : ℕ) :
    n.choose 2 * (n - 2).choose 2 * (n - 4).choose 2 = 90 * n.choose 6 := by
  have h1 := two_mul_choose_two n
  have h2 := two_mul_choose_two (n - 2)
  have h3 := two_mul_choose_two (n - 4)
  rw [show n - 2 - 1 = n - 3 from by omega] at h2
  rw [show n - 4 - 1 = n - 5 from by omega] at h3
  have h6 : n.descFactorial 6 = Nat.factorial 6 * n.choose 6 :=
    Nat.descFactorial_eq_factorial_mul_choose n 6
  rw [show n.descFactorial 6
        = (n - 5) * ((n - 4) * ((n - 3) * ((n - 2) * ((n - 1) * (n * 1))))) from rfl,
    show Nat.factorial 6 = 720 from rfl] at h6
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 8 by norm_num) ?_
  calc 8 * (n.choose 2 * (n - 2).choose 2 * (n - 4).choose 2)
      = 2 * n.choose 2 * (2 * (n - 2).choose 2) * (2 * (n - 4).choose 2) := by ring
    _ = n * (n - 1) * ((n - 2) * (n - 3)) * ((n - 4) * (n - 5)) := by rw [h1, h2, h3]
    _ = (n - 5) * ((n - 4) * ((n - 3) * ((n - 2) * ((n - 1) * (n * 1))))) := by ring
    _ = 720 * n.choose 6 := h6
    _ = 8 * (90 * n.choose 6) := by ring

/-- An arithmetic helper: `n.choose 2` is even exactly when `n` is `0` or `1` mod `4`. -/
theorem choose_two_mod_two_eq_zero_iff (n : ℕ) :
    n.choose 2 % 2 = 0 ↔ n % 4 = 0 ∨ n % 4 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]
    omega

theorem div_pred_of_not_dvd {k r : ℕ} (h : ¬ r ∣ (k + 1)) : k / r = (k + 1) / r := by
  rw [Nat.succ_div, if_neg h, Nat.add_zero]

theorem ceilDiv_of_not_dvd {n r : ℕ} (hr : 0 < r) (h : ¬ r ∣ n) :
    (n + r - 1) / r = n / r + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (dvd_zero r) h
    · exact ⟨n - 1, by omega⟩
  have he : k + 1 + r - 1 = k + r := by omega
  have h2 : (k + r) / r = k / r + 1 := Nat.add_div_right k hr
  rw [he, h2, div_pred_of_not_dvd h]

/-- Reduction mod `d` below `2 * d`, again as a disjunction `omega` can use. -/
theorem mod_of_lt_two_mul {d x : ℕ} (hx : x < 2 * d) :
    (x < d ∧ x % d = x) ∨ (d ≤ x ∧ x % d = x - d) := by
  rcases Nat.lt_or_ge x d with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- The difference `y - x` around a cycle of length `d`, again as a disjunction: `(y + d - x) % d`
is `y - x` going forwards and `d - (x - y)` going backwards.  This is the third member of the
`succ_mod_eq_iff` / `mod_of_lt_two_mul` family of "`omega` cannot divide" workarounds, and it is
what makes circulant differences tractable. -/
theorem sub_mod_cases {d x y : ℕ} (hx : x < d) (hy : y < d) :
    (x ≤ y ∧ (y + d - x) % d = y - x) ∨ (y < x ∧ (y + d - x) % d = d - (x - y)) := by
  rcases Nat.lt_or_ge y x with h | h
  · refine Or.inr ⟨h, ?_⟩
    rw [show y + d - x = d - (x - y) by omega, Nat.mod_eq_of_lt (by omega)]
  · refine Or.inl ⟨h, ?_⟩
    rw [show y + d - x = (y - x) + d by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The successor relation of a cycle, with the wrap-around split off.  `omega` cannot see through
a `%` whose modulus is a variable, so every step around a `cycle n` is turned into this
disjunction before the arithmetic starts. -/
theorem succ_mod_eq_iff {d x y : ℕ} (hx : x < d) :
    (x + 1) % d = y ↔ (x + 1 = d ∧ y = 0) ∨ (x + 1 < d ∧ y = x + 1) := by
  rcases Nat.lt_or_ge (x + 1) d with h | h
  · rw [Nat.mod_eq_of_lt h]
    constructor
    · rintro rfl; exact Or.inr ⟨h, rfl⟩
    · rintro (⟨h1, h2⟩ | ⟨-, h2⟩) <;> omega
  · have hd : x + 1 = d := by omega
    rw [hd, Nat.mod_self]
    constructor
    · rintro rfl; exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩) <;> omega

/-- A step around a cycle of length at least two never stands still. -/
theorem succ_mod_ne {d x : ℕ} (h2 : 2 ≤ d) (hx : x < d) : (x + 1) % d ≠ x := by
  by_cases h : x + 1 = d
  · rw [h, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem mod_succ_norm {N a : ℕ} (h : a < N) : (a + 1) % N = if a + 1 = N then 0 else a + 1 := by
  rcases Nat.lt_or_ge (a + 1) N with hq | hq
  · rw [if_neg (by omega), Nat.mod_eq_of_lt hq]
  · have hEq : a + 1 = N := by omega
    rw [if_pos hEq, hEq, Nat.mod_self]

/-- With an odd modulus `2a + 3` bigger than both, `2i + 1` and `2i'` are already reduced, so
they are congruent only if they are equal — and they have opposite parities. -/
theorem two_mul_succ_not_modEq (a i i' : ℕ) (hi : i ≤ a) (hi' : i' ≤ a) :
    ¬ (2 * i + 1 ≡ 2 * i' [MOD 2 * a + 3]) := by
  intro h
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

/-- Division with remainder, read off a pair of digits: `x * n + y` determines `x` and `y` once
`y < n`. -/
theorem row_col_eq {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + y = x' * n + y') : x = x' ∧ y = y' := by
  rcases Nat.lt_trichotomy x x' with hx | hx | hx
  · exact absurd h (by
      have h1 : (x + 1) * n ≤ x' * n := Nat.mul_le_mul_right n hx
      have h2 : (x + 1) * n = x * n + n := by ring
      omega)
  · exact ⟨hx, by rw [hx] at h; omega⟩
  · exact absurd h (by
      have h1 : (x' + 1) * n ≤ x * n := Nat.mul_le_mul_right n hx
      have h2 : (x' + 1) * n = x' * n + n := by ring
      omega)

/-- Stepping the row-major numbering by one either moves along a row or wraps to the next one. -/
theorem row_col_step {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + y + 1 = x' * n + y') :
    (x = x' ∧ y + 1 = y') ∨ (x + 1 = x' ∧ y + 1 = n ∧ y' = 0) := by
  rcases Nat.lt_or_ge (y + 1) n with hlt | hge
  · exact Or.inl (row_col_eq hlt hy' (by omega))
  · have hxn : (x + 1) * n = x * n + n := by ring
    obtain ⟨h1, h2⟩ := row_col_eq (show (0 : ℕ) < n by omega) hy'
      (show (x + 1) * n + 0 = x' * n + y' by omega)
    exact Or.inr ⟨h1, by omega, h2.symm⟩

/-- `ENat.toNat` commutes with `max` away from `⊤`. -/
theorem ENat.toNat_max (a b : ℕ∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (max a b).toNat = max a.toNat b.toNat := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (ENat.toNat_le_toNat h hb)]
  · rw [max_eq_left h, max_eq_left (ENat.toNat_le_toNat h ha)]
