import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Common

/-!
# Deciding that two unordered pairs meet

Two edges of a graph are adjacent in its line graph when they have an endpoint in common, and
the obvious way to say that is `∃ v, v ∈ e ∧ v ∈ f`.  Read as a decision procedure that is a
search over the whole vertex type: `card α` candidates, each tested for membership in both
pairs.  The pairs have two entries each, so four comparisons settle it, and `meet` is that test.

For the line graph of the cube — whose vertices are functions `Fin 3 → Bool`, so a single
comparison is itself a search — the difference is the difference between a kernel computation
that takes seconds and one that does not.
-/

set_option autoImplicit false

universe u

namespace Sym2

variable {α : Type u} [DecidableEq α]

/-- Whether two unordered pairs have an element in common. -/
def meet : Sym2 α → Sym2 α → Bool :=
  Sym2.lift₂ ⟨fun a b c d ↦ (a == c || a == d) || (b == c || b == d), by
    intro a b c d
    refine ⟨?_, ?_⟩ <;>
      · rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, beq_iff_eq]
        tauto⟩

@[simp] theorem meet_mk (a b c d : α) :
    meet s(a, b) s(c, d) = ((a == c || a == d) || (b == c || b == d)) := rfl

theorem meet_iff (e f : Sym2 α) : meet e f = true ↔ ∃ v, v ∈ e ∧ v ∈ f := by
  induction e with | _ a b =>
  induction f with | _ c d =>
  simp only [meet_mk, Bool.or_eq_true, beq_iff_eq, Sym2.mem_iff]
  constructor
  · rintro ((h | h) | h | h)
    exacts [⟨a, Or.inl rfl, Or.inl h⟩, ⟨a, Or.inl rfl, Or.inr h⟩,
      ⟨b, Or.inr rfl, Or.inl h⟩, ⟨b, Or.inr rfl, Or.inr h⟩]
  · rintro ⟨v, (rfl | rfl), (h | h)⟩ <;> simp [h]

theorem meet_comm (e f : Sym2 α) : meet e f = meet f e := by
  rw [Bool.eq_iff_iff, meet_iff, meet_iff]
  exact ⟨fun ⟨v, h1, h2⟩ ↦ ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ ↦ ⟨v, h2, h1⟩⟩

@[simp] theorem meet_self (e : Sym2 α) : meet e e = true := by
  induction e with | _ a b => simp

end Sym2
