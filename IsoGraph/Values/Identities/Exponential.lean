import IsoGraph.Values.Identities.Semiring

/-!
# The graph exponential

`G ^g H` has the maps `H.V → G.V` for vertices, two distinct maps being adjacent when every edge
of `H` is carried to an edge of `G`.  On graphs *with* loops this is the internal hom of the tensor
product, and the whole exponent calculus follows from that adjunction; a `CGraph` is loopless, the
diagonal is deleted, and almost none of the calculus survives.  What is left is this module: the
vertex count `(G ^g H).V = G.V ^ H.V`, the degenerate cases, and counterexamples to the laws one
would expect.

## What holds

| identity | |
| --- | --- |
| `V_exponential` | `(G ^g H).V = G.V ^ H.V` |
| `exponential_empty` | `G ^g empty n = complete (G.V ^ n)` |
| `empty_one_exponential` | `empty 1 ^g G = empty 1` |
| `empty_zero_exponential` | `empty 0 ^g G = empty (0 ^ G.V)` |
| `empty_exponential` | `empty m ^g G = empty (m ^ G.V)` when `G` has an edge |

An edgeless exponent imposes no condition at all, so `G ^g empty n` is *complete* on its `G.V ^ n`
vertices — in particular `G ^g empty 0 = empty 1` and `G ^g empty 1 = complete G.V`, so `1` is not
an exponent unit and the graph is not recovered from its first power.

## What fails

Everything else, and for the same reason each time: a map that would be adjacent to itself in the
loop-ful exponential is instead isolated, and the two sides lose different numbers of edges.  The
vertex counts always agree — `G.V ^ (H.V * K.V)` on both sides of the tower law, and so on — so the
counterexamples are all about edges.  `not_forall_exponential_exponential`,
`not_forall_exponential_disjUnion`, `not_forall_tensorProduct_exponential` and
`not_forall_exponential_empty_one` refute the four shapes over the tensor product; the smallest
witness in each case is edgeless or complete on at most four vertices.

## Notation

`^g` is the notation for the operation, on `CGraph` and on `IsoGraph`, and is always available.
The scope `IsoGraph.Exponential` re-tags it as the `Pow` instance of both, so that `G ^ H` with a
graph in the exponent means `G ^g H`.  It is deliberately separate from the scopes of
`Identities/Semiring.lean`: opening both leaves `G ^ (n : ℕ)` the monoid power of whichever product
was opened, and `G ^ (H : IsoGraph)` the exponential.
-/

set_option autoImplicit false

/-! ## Degenerate exponentials -/

namespace CGraph.Iso

/-- With an edgeless exponent every pair of distinct maps is adjacent. -/
@[toIsoGraph simp exponential_empty]
noncomputable def exponentialEmpty (G : CGraph) (n : ℕ) :
    G ^g empty n ≃cg complete (Fintype.card G.V ^ n) := by
  refine isoCompleteOfCard ?_ (by simp)
  intro f f' hff'
  simp [exponential_adj, hff']

/-- One vertex to any power is one vertex. -/
@[toIsoGraph simp empty_one_exponential]
noncomputable def emptyOneExponential (G : CGraph) : empty 1 ^g G ≃cg empty 1 := by
  refine isoEmptyOfCard ?_ (by simp)
  intro f f'
  haveI : Subsingleton (empty 1).V := inferInstanceAs (Subsingleton (Fin 1))
  have h : f = f' := funext fun _ ↦ Subsingleton.elim _ _
  simp [exponential_adj, h]

/-- No vertices to any power: `0 ^ n` vertices, and no edges. -/
@[toIsoGraph simp empty_zero_exponential]
noncomputable def emptyZeroExponential (G : CGraph) :
    empty 0 ^g G ≃cg empty (0 ^ Fintype.card G.V) := by
  refine isoEmptyOfCard ?_ (by simp)
  intro f f'
  by_cases h : Nonempty G.V
  · obtain ⟨x⟩ := h
    exact (f x).elim0
  · have hf : f = f' := funext fun x ↦ absurd ⟨x⟩ h
    simp [exponential_adj, hf]

/-- With an edgeless base and an exponent that has an edge, nothing is adjacent: the one edge of
the exponent has to go somewhere, and there is nowhere for it to go. -/
noncomputable def emptyExponential (m : ℕ) (G : CGraph) {x y : G.V} (hxy : G.Adj x y) :
    empty m ^g G ≃cg empty (m ^ Fintype.card G.V) := by
  refine isoEmptyOfCard ?_ (by simp)
  intro f f'
  simp only [exponential_adj]
  simp
  exact fun _ ↦ ⟨x, y, hxy⟩

end CGraph.Iso

namespace IsoGraph

@[simp] theorem exponential_empty_zero (G : IsoGraph) : G ^g empty 0 = empty 1 := by
  rw [exponential_empty, pow_zero, complete_one]

/-- The first power is the *complete* graph on the vertices, not the graph itself. -/
theorem exponential_empty_one (G : IsoGraph) : G ^g empty 1 = complete G.V := by
  rw [exponential_empty, pow_one]

theorem empty_zero_exponential_of_ne {G : IsoGraph} (h : G ≠ empty 0) :
    empty 0 ^g G = empty 0 := by
  rw [empty_zero_exponential, zero_pow]
  simpa using h

/-- An edgeless base and an exponent with an edge give an edgeless power. -/
theorem empty_exponential (m : ℕ) {G : IsoGraph} (h : G ≠ empty G.V) :
    empty m ^g G = empty (m ^ G.V) := by
  induction G using Quotient.inductionOn with
  | h g =>
    by_cases hedge : ∃ x y, g.Adj x y = true
    · obtain ⟨x, y, hxy⟩ := hedge
      exact Quotient.sound ⟨CGraph.Iso.emptyExponential m g hxy⟩
    · push_neg at hedge
      exact absurd (mk_eq_empty (by simpa using hedge)) h

/-! ## The exponent laws all fail

Four shapes, one witness each, all over the tensor product; the same witnesses refute the versions
over the other three products, since every side that is not the exponential itself is edgeless or
a single vertex, and the four products agree there. -/

/-- The one non-degenerate exponential small enough to compute with: `K₂ ^g K₂` has four vertices
and one edge — the two constant maps are adjacent, and the two bijections are isolated — where the
loop-ful exponent law would make it `K₄`. -/
theorem complete_two_exponential_complete_two_ne_complete_four :
    (complete 2 : IsoGraph) ^g complete 2 ≠ complete 4 := by
  intro h
  obtain ⟨f, f', hff', hadj⟩ :
      ∃ f f' : (CGraph.complete 2).V → (CGraph.complete 2).V,
        f ≠ f' ∧ (CGraph.complete 2 ^g CGraph.complete 2).Adj f f' = false := by decide
  rw [adj_of_mk_eq_complete (n := 4) h hff'] at hadj
  exact Bool.noConfusion hadj

/-- The tower law fails: `(E₂ ^g E₁) ^g K₂` is `K₂ ^g K₂`, one edge on four vertices, where
`E₂ ^g (E₁ ⊗g K₂)` is `K₄`. -/
theorem not_forall_exponential_exponential :
    ¬ ∀ a b c : IsoGraph, (a ^g b) ^g c = a ^g (b ⊗g c) := by
  intro h
  have h2 := h (empty 2) (empty 1) (complete 2)
  rw [show ((empty 2 : IsoGraph) ^g empty 1) = complete 2 by
        rw [exponential_empty_one, V_empty],
      show ((empty 1 : IsoGraph) ⊗g complete 2) = empty 2 by
        rw [empty_tensorProduct, V_complete, one_mul],
      exponential_empty, V_empty] at h2
  exact complete_two_exponential_complete_two_ne_complete_four (by norm_num at h2; exact h2)

/-- A sum in the exponent is not a product of powers: `E₂ ^g (E₀ ⊕g E₁)` is `K₂`, where
`E₂ ^g E₀ ⊗g E₂ ^g E₁` is `E₁ ⊗g K₂`, which is edgeless. -/
theorem not_forall_exponential_disjUnion :
    ¬ ∀ a b c : IsoGraph, a ^g (b ⊕g c) = a ^g b ⊗g a ^g c := by
  intro h
  have h2 := h (empty 2) (empty 0) (empty 1)
  rw [empty_zero_disjUnion, exponential_empty_one, V_empty, exponential_empty_zero,
    empty_tensorProduct, V_complete, one_mul] at h2
  exact empty_ne_complete 0 h2.symm

/-- A product in the base is not a product of powers: `(E₁ ⊗g E₂) ^g E₁` is `K₂`, where
`E₁ ^g E₁ ⊗g E₂ ^g E₁` is again edgeless. -/
theorem not_forall_tensorProduct_exponential :
    ¬ ∀ a b c : IsoGraph, (a ⊗g b) ^g c = a ^g c ⊗g b ^g c := by
  intro h
  have h2 := h (empty 1) (empty 2) (empty 1)
  rw [show ((empty 1 : IsoGraph) ⊗g empty 2) = empty 2 by
        rw [empty_tensorProduct, V_empty, one_mul],
      exponential_empty_one, V_empty, empty_one_exponential, empty_tensorProduct, V_complete,
      one_mul] at h2
  exact empty_ne_complete 0 h2.symm

/-- The first power is not the identity: `E₂ ^g E₁` is `K₂`. -/
theorem not_forall_exponential_empty_one : ¬ ∀ a : IsoGraph, a ^g empty 1 = a := by
  intro h
  have h2 := h (empty 2)
  rw [exponential_empty_one, V_empty] at h2
  exact empty_ne_complete 0 h2.symm

/-! ## The scoped power notation -/

/-- `^` for `CGraph`, with a graph in the exponent. -/
def instPowCGraph : Pow CGraph CGraph := ⟨CGraph.exponential⟩

/-- `^` for `IsoGraph`, with a class in the exponent. -/
def instPowIsoGraph : Pow IsoGraph IsoGraph := ⟨IsoGraph.exponential⟩

namespace Exponential

attribute [scoped instance] IsoGraph.instPowCGraph IsoGraph.instPowIsoGraph

@[scoped simp] theorem cgraph_pow_eq (G H : CGraph) : G ^ H = G ^g H := rfl
@[scoped simp] theorem pow_eq (G H : IsoGraph) : G ^ H = G ^g H := rfl

end Exponential

/-! ## Simp normal form

The exponential of an edgeless graph, on either side, reduces to `empty` or `complete` on a vertex
count; nothing else does. -/

example (G : IsoGraph) (n : ℕ) : G ^g empty n = complete (G.V ^ n) := by simp
example (G : IsoGraph) : empty 1 ^g G = empty 1 := by simp
example (G : IsoGraph) : empty 0 ^g G = empty (0 ^ G.V) := by simp
example (G : IsoGraph) : G ^g empty 0 = empty 1 := by simp
example (G H : IsoGraph) : (G ^g H).V = G.V ^ H.V := by simp

open scoped IsoGraph.Exponential in
example (G H : CGraph) : (G ^ H).V = (H.V → G.V) := rfl

open scoped IsoGraph.Exponential IsoGraph.Semiring in
example (G : IsoGraph) : G ^ (empty 0 : IsoGraph) = 1 ∧ G ^ (0 : ℕ) = 1 := by
  refine ⟨by simp, pow_zero G⟩

end IsoGraph
