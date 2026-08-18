import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Common
import IsoGraph.ForMathlib.FinEnum

/-!
# Lemmas about `ZMod`

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

/-- `ZMod q` and `Fin q`, matched up by `ZMod.val`. -/
def zmodEquivFin (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun a := ⟨a.val, ZMod.val_lt a⟩
  invFun i := (i.1 : ZMod q)
  left_inv a := ZMod.natCast_rightInverse a
  right_inv i := Fin.ext (ZMod.val_cast_of_lt i.2)

/-- `ZMod q` is enumerated by `ZMod.val`, with `FinEnum.card (ZMod q)` *definitionally* `q`.
Mathlib has no `FinEnum (ZMod q)` at all; the `Fintype` it does have goes through `Fin q` for
`q ≠ 0` and `ℤ`'s (empty) one otherwise, so it cannot be reused here. -/
instance (priority := 2000) instFinEnumZMod (q : ℕ) [NeZero q] : FinEnum (ZMod q) where
  card := q
  equiv := zmodEquivFin q

/-- The `Fin q` arithmetic `paley` does to find the offset of `y` from `x` is subtraction in
`ZMod q`. -/
theorem zmod_val_sub {q : ℕ} [NeZero q] (x y : ZMod q) :
    (y.val + q - x.val) % q = (y - x).val := by
  rw [show y.val + q - x.val = y.val + (q - x.val) from by
    have := ZMod.val_lt x; omega, ← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_add, Nat.cast_sub (le_of_lt (ZMod.val_lt x)), ZMod.natCast_self,
    ZMod.natCast_rightInverse x, ZMod.natCast_rightInverse y, zero_sub, ← sub_eq_add_neg]

/-- The lookup table records exactly the nonzero squares of `ZMod q`. -/
theorem exists_sq_iff_val {q : ℕ} [NeZero q] (a : ZMod q) :
    (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = a.val) ↔ ∃ r : ZMod q, r ≠ 0 ∧ r * r = a := by
  constructor
  · rintro ⟨i, hi, hia⟩
    have hr : ((i.1 : ℕ) : ZMod q).val = i.1 := ZMod.val_cast_of_lt i.2
    refine ⟨(i.1 : ℕ), fun h0 ↦ hi (by rw [← hr, h0, ZMod.val_zero]), ZMod.val_injective q ?_⟩
    rw [ZMod.val_mul, hr, hia]
  · rintro ⟨r, hr0, rfl⟩
    refine ⟨⟨r.val, ZMod.val_lt r⟩, ?_, ?_⟩
    · simpa using fun h ↦ hr0 ((ZMod.val_eq_zero r).1 h)
    · rw [ZMod.val_mul]
