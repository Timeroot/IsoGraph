import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Character sums over a finite field

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

section CardModFour

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- For `a ≠ 0`, the quadratic character sum `∑ u, χ (u * (u - a))` is `-1`.

`u ↦ 1 - a * u⁻¹` is a bijection from the nonzero elements to the elements other than `1`, and
`χ (u * (u - a)) = χ (u²) * χ (1 - a * u⁻¹) = χ (1 - a * u⁻¹)`, so the sum is `∑_{w ≠ 1} χ w`. -/
theorem quadraticChar_sum_mul_sub (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ u : F, quadraticChar F (u * (u - a)) = -1 := by
  have h0 : ∑ u : F, quadraticChar F (u * (u - a))
      = ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (u * (u - a)) := by
    rw [Finset.sum_erase]
    simp
  have key : ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (u * (u - a))
      = ∑ w ∈ Finset.univ.erase (1 : F), quadraticChar F w := by
    refine Finset.sum_nbij' (i := fun u ↦ 1 - a * u⁻¹) (j := fun w ↦ a * (1 - w)⁻¹)
      ?_ ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu ⊢
      intro h
      rcases mul_eq_zero.mp (sub_eq_self.mp h) with h3 | h3
      · exact ha h3
      · exact hu (inv_eq_zero.mp h3)
    · intro w hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw ⊢
      exact mul_ne_zero ha (inv_ne_zero (sub_ne_zero.2 (Ne.symm hw)))
    · intro u hu
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
      show a * (1 - (1 - a * u⁻¹))⁻¹ = u
      rw [sub_sub_cancel, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    · intro w hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
      have h1 : (1 : F) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
      show 1 - a * (a * (1 - w)⁻¹)⁻¹ = w
      rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_sub_cancel]
    · intro u hu
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
      have : u * (u - a) = u ^ 2 * (1 - a * u⁻¹) := by field_simp
      rw [this, map_mul, quadraticChar_sq_one' hu, one_mul]
  rw [h0, key, Finset.sum_erase_eq_sub (Finset.mem_univ _), quadraticChar_sum_zero hF]
  simp

variable (hq : Fintype.card F % 4 = 1)
include hq

omit [DecidableEq F] in
theorem ringChar_ne_two_of_card_mod_four : ringChar F ≠ 2 := fun h ↦ by
  have := FiniteField.even_card_iff_char_two.1 h
  omega

theorem quadraticChar_neg_one_eq_one : quadraticChar F (-1) = 1 :=
  (quadraticChar_one_iff_isSquare (by simp)).2 (FiniteField.isSquare_neg_one_iff.2 (by omega))

/-- Over a field with `q ≡ 1 mod 4` elements the quadratic character is even, which is why the
Paley graph is a graph and not a tournament. -/
theorem quadraticChar_neg' (a : F) : quadraticChar F (-a) = quadraticChar F a := by
  rw [show -a = -1 * a by ring, map_mul, quadraticChar_neg_one_eq_one hq, one_mul]

omit hq in
theorem quadraticChar_sum_sub_zero (hF : ringChar F ≠ 2) (a : F) :
    ∑ u : F, quadraticChar F (u - a) = 0 := by
  rw [Fintype.sum_equiv (Equiv.subRight a) (fun u ↦ quadraticChar F (u - a))
    (fun w ↦ quadraticChar F w) (fun u ↦ rfl)]
  exact quadraticChar_sum_zero hF

/-- **The degree count**: exactly half of the nonzero elements are squares. -/
theorem card_quadraticChar_eq_one :
    2 * ((Finset.univ.filter fun u : F ↦ quadraticChar F u = 1).card : ℤ)
      = Fintype.card F - 1 := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  have hsplit : ∑ u ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F u)
      = 2 * (((Finset.univ.erase (0 : F)).filter fun u ↦ quadraticChar F u = 1).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase (0 : F))
      (fun u ↦ quadraticChar F u = 1)]
    rw [Finset.sum_congr rfl (g := fun _ ↦ (2 : ℤ)) fun u hu ↦ by
        simp only [Finset.mem_filter] at hu; rw [hu.2]; norm_num,
      Finset.sum_eq_zero
        (s := (Finset.univ.erase (0 : F)).filter fun u ↦ ¬ quadraticChar F u = 1) fun u hu ↦ by
          simp only [Finset.mem_filter, Finset.mem_erase] at hu
          rcases quadraticChar_dichotomy hu.1.1 with h | h
          · exact absurd h hu.2
          · rw [h]; ring]
    simp [mul_comm]
  have hfe : ((Finset.univ.erase (0 : F)).filter fun u ↦ quadraticChar F u = 1)
      = Finset.univ.filter fun u : F ↦ quadraticChar F u = 1 := by
    refine Finset.ext fun u ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun h0 ↦ by rw [h0] at h; simp at h, h⟩⟩
  rw [hfe] at hsplit
  rw [← hsplit, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_erase_eq_sub (Finset.mem_univ _), quadraticChar_sum_zero hF,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
  have h2 : 1 ≤ Fintype.card F := Fintype.card_pos
  simp only [nsmul_eq_mul, mul_one, quadraticChar_zero, sub_zero]
  omega

/-- **The common-neighbour count**: for `a ≠ 0` the number of `u` with both `u` and `u - a`
nonzero squares is `(q - 3 - 2 * χ a) / 4`. -/
theorem card_common_quadraticChar {a : F} (ha : a ≠ 0) :
    4 * ((Finset.univ.filter fun u : F ↦
          quadraticChar F u = 1 ∧ quadraticChar F (u - a) = 1).card : ℤ)
      = Fintype.card F - 3 - 2 * quadraticChar F a := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  have ha' : a ∈ Finset.univ.erase (0 : F) := Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩
  set S : Finset F := (Finset.univ.erase (0 : F)).erase a with hS
  set P : F → Prop := fun u ↦ quadraticChar F u = 1 ∧ quadraticChar F (u - a) = 1 with hP
  have hfe : S.filter P = Finset.univ.filter P := by
    refine Finset.ext fun u ↦ ?_
    simp only [hS, hP, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩, h⟩⟩
    · rw [h0, sub_self] at h; simp at h
    · rw [h0] at h; simp at h
  have hsplit : ∑ u ∈ S, (1 + quadraticChar F u) * (1 + quadraticChar F (u - a))
      = 4 * ((S.filter P).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S P]
    rw [Finset.sum_congr rfl (g := fun _ ↦ (4 : ℤ)) fun u hu ↦ by
        simp only [Finset.mem_filter, hP] at hu; rw [hu.2.1, hu.2.2]; norm_num,
      Finset.sum_eq_zero (s := S.filter fun u ↦ ¬ P u) fun u hu ↦ by
        simp only [Finset.mem_filter, hS, Finset.mem_erase, hP, not_and] at hu
        rcases quadraticChar_dichotomy hu.1.2.1 with h | h
        · rcases quadraticChar_dichotomy (sub_ne_zero.2 hu.1.1) with h' | h'
          · exact absurd h' (hu.2 h)
          · rw [h']; ring
        · rw [h]; ring]
    simp [mul_comm]
  have hexp : ∑ u ∈ S, (1 + quadraticChar F u) * (1 + quadraticChar F (u - a))
      = (∑ _u ∈ S, (1 : ℤ)) + (∑ u ∈ S, quadraticChar F u)
        + (∑ u ∈ S, quadraticChar F (u - a)) + ∑ u ∈ S, quadraticChar F (u * (u - a)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [map_mul]
    ring
  have e1 : (∑ _u ∈ S, (1 : ℤ)) = (Fintype.card F : ℤ) - 2 := by
    rw [Finset.sum_const, hS, Finset.card_erase_of_mem ha',
      Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    simp only [nsmul_eq_mul, mul_one]
    omega
  have e2 : (∑ u ∈ S, quadraticChar F u) = -quadraticChar F a := by
    rw [hS, Finset.sum_erase_eq_sub ha', Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
      quadraticChar_sum_zero hF]
    simp
  have e3 : (∑ u ∈ S, quadraticChar F (u - a)) = -quadraticChar F a := by
    rw [hS, Finset.sum_erase_eq_sub ha', Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
      quadraticChar_sum_sub_zero hF]
    simp [quadraticChar_neg' hq]
  have e4 : (∑ u ∈ S, quadraticChar F (u * (u - a))) = -1 := by
    rw [hS, Finset.sum_erase_eq_sub ha', Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
      quadraticChar_sum_mul_sub hF ha]
    simp
  rw [← hfe, ← hsplit, hexp, e1, e2, e3, e4]
  ring

end CardModFour
