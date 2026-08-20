import IsoGraph.Algebra.Connected

/-!
# Exponentiation

Exponentiation of isomorphism classes, its scoped notation, its simp normal form, and the exponent
laws — most of which fail.
-/

namespace CGraph.Iso

/-- With an edgeless exponent every pair of distinct maps is adjacent. -/
@[toIsoGraph simp exponential_empty]
noncomputable def exponentialEmpty (G : CGraph) (n : ℕ) :
    G ^g empty n ≃cg complete (FinEnum.card G.V ^ n) := by
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
    empty 0 ^g G ≃cg empty (0 ^ FinEnum.card G.V) := by
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
    empty m ^g G ≃cg empty (m ^ FinEnum.card G.V) := by
  refine isoEmptyOfCard ?_ (by simp)
  intro f f'
  simp only [exponential_adj]
  simp
  exact fun _ ↦ ⟨x, y, hxy⟩

end CGraph.Iso

namespace CGraph

/-! ### A complete base

`K₂ ^g G` is the one family with a complete base that can be described outright.  For `m ≥ 3` the
description fails — `K₃ ^g K₂` has more than the constant maps adjacent — and for `m = 2` a map is
adjacent to another only if the two are the two constants, so the graph is one edge and `2 ^ G.V -
2` isolated vertices. -/

/-- **`K₂ ^g G` has exactly one edge**, between the two constant maps, whenever `G` is connected.
Adjacency forces the two maps apart across every edge of `G`; in a two-element codomain that makes
`fun u ↦ decide (f u = f' u)` constant along edges, hence constant, hence `false` since `f ≠ f'`,
and then `f` itself is constant along edges. -/
theorem complete_two_exponential_adj {G : CGraph} (hG : G.IsConnected)
    (f f' : (complete 2 ^g G).V) :
    (complete 2 ^g G).Adj f f' = true
      ↔ ∃ b b' : Fin 2, b ≠ b' ∧ f = (fun _ ↦ b) ∧ f' = (fun _ ↦ b') := by
  have key : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b = c := by decide
  obtain ⟨x₀⟩ := hG.nonempty
  constructor
  · intro hadj
    rw [exponential_adj, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hadj
    obtain ⟨hne, hcol⟩ := hadj
    have hcol' : ∀ u v, G.Adj u v → f u ≠ f' v := fun u v huv ↦ by
      have h := hcol u v huv
      rwa [complete_adj, decide_eq_true_eq] at h
    -- either the two maps agree everywhere or they disagree everywhere
    have hφ : ∀ u v, G.Adj u v → decide (f u = f' u) = decide (f v = f' v) := by
      intro u v huv
      have h1 : f u ≠ f' v := hcol' u v huv
      have h2 : f v ≠ f' u := hcol' v u (by rwa [G.symm])
      refine decide_eq_decide.2 ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · exact key (f u) (f v) (f' v) (Ne.symm (he ▸ h2)) h1
      · exact key (f v) (f u) (f' u) (Ne.symm (he ▸ h1)) h2
    obtain ⟨u₁, hu₁⟩ : ∃ u, f u ≠ f' u := by
      by_contra hc
      push_neg at hc
      exact hne (funext hc)
    have hne' : ∀ u, f u ≠ f' u := by
      intro u
      have h := eq_of_forall_adj hG hφ u u₁
      simp only [decide_eq_decide] at h
      exact fun hc ↦ hu₁ (h.1 hc)
    -- and then both maps are constant
    have hfconst : ∀ u v, G.Adj u v → f u = f v := fun u v huv ↦
      (key (f' v) (f v) (f u) (Ne.symm (hne' v)) (Ne.symm (hcol' u v huv))).symm
    have hf : f = fun _ ↦ f x₀ := funext fun u ↦ eq_of_forall_adj hG hfconst u x₀
    have hf' : f' = fun _ ↦ f' x₀ := funext fun u ↦
      key (f u) (f' u) (f' x₀) (hne' u) (by rw [congrFun hf u]; exact hne' x₀)
    exact ⟨f x₀, f' x₀, hne' x₀, hf, hf'⟩
  · rintro ⟨b, b', hbb', rfl, rfl⟩
    rw [exponential_adj, Bool.and_eq_true]
    refine ⟨decide_eq_true fun hc ↦ hbb' (congrFun hc x₀), decide_eq_true fun u v _ ↦ ?_⟩
    rw [complete_adj]
    exact decide_eq_true hbb'

end CGraph

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

end IsoGraph

namespace IsoGraph.Exponential

attribute [scoped instance] IsoGraph.instPowCGraph IsoGraph.instPowIsoGraph

@[scoped simp] theorem cgraph_pow_eq (G H : CGraph) : G ^ H = G ^g H := rfl

@[scoped simp] theorem pow_eq (G H : IsoGraph) : G ^ H = G ^g H := rfl

end IsoGraph.Exponential

namespace IsoGraph

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

/-! ## The reflexive exponential

Everything the plain exponential fails to do, `^hg` does, with `⊠g` in place of `⊗g`.  The proofs
are all the same shape: build the map of vertices, and check with `isoOfAdjR` that it preserves
reflexive adjacency, which for these graphs is a statement with no `≠` in it. -/

namespace CGraph.Iso

/-- One vertex to any power is one vertex. -/
@[toIsoGraph simp empty_one_homExponential]
noncomputable def emptyOneHomExponential (G : CGraph) : empty 1 ^hg G ≃cg empty 1 := by
  haveI : Unique (empty 1).V := inferInstanceAs (Unique (Fin 1))
  refine isoEmptyOfCard ?_ ?_
  · intro f f'
    have h : f = f' := Subtype.ext (funext fun _ ↦ Subsingleton.elim _ _)
    simp [h]
  · rw [FinEnum.card_eq_fintypeCard]
    refine Fintype.card_eq_one_iff.2 ⟨⟨fun _ ↦ default, fun u v _ ↦ by simp⟩, fun f ↦ ?_⟩
    exact Subtype.ext (funext fun _ ↦ Subsingleton.elim _ _)

/-- The zeroth power is one vertex: there is exactly one map out of the empty graph. -/
@[toIsoGraph simp homExponential_empty_zero]
noncomputable def homExponentialEmptyZero (G : CGraph) : G ^hg empty 0 ≃cg empty 1 := by
  refine isoEmptyOfCard ?_ ?_
  · intro f f'
    have h : f = f' := Subtype.ext (funext fun u ↦ u.elim0)
    simp [h]
  · rw [FinEnum.card_eq_fintypeCard]
    exact Fintype.card_eq_one_iff.2
      ⟨⟨fun u ↦ u.elim0, fun u _ _ ↦ u.elim0⟩, fun f ↦ Subtype.ext (funext fun u ↦ u.elim0)⟩

/-- **The first power is the graph itself**: the vertices of `G ^hg empty 1` are the vertices of
`G`, and two of them are adjacent exactly when they were. -/
@[toIsoGraph simp homExponential_empty_one]
def homExponentialEmptyOne (G : CGraph) : G ^hg empty 1 ≃cg G := by
  haveI : Unique (empty 1).V := inferInstanceAs (Unique (Fin 1))
  refine isoOfAdjR ((Equiv.subtypeUnivEquiv (p := fun f : (empty 1).V → G.V ↦
      ∀ u v, (empty 1).adjR u v → G.adjR (f u) (f v)) fun f u v _ ↦ by
        rw [Subsingleton.elim u v]; simp).trans (Equiv.funUnique _ _)) ?_
  intro f f'
  show G.adjR (f.1 default) (f'.1 default) = _
  rw [adjR_homExponential]
  have h : (∀ u v, (empty 1).adjR u v → G.adjR (f.1 u) (f'.1 v))
      ↔ G.adjR (f.1 default) (f'.1 default) = true :=
    ⟨fun h ↦ h _ _ (by simp), fun h u v _ ↦ by
      rwa [Subsingleton.elim u default, Subsingleton.elim v default]⟩
  rw [decide_eq_decide.2 h, Bool.decide_coe]

/-- Every map into a complete graph is a homomorphism, and any two distinct ones are adjacent. -/
@[toIsoGraph simp complete_homExponential]
noncomputable def completeHomExponential (m : ℕ) (G : CGraph) :
    complete m ^hg G ≃cg complete (m ^ FinEnum.card G.V) := by
  refine isoCompleteOfCard (fun f f' hff' ↦ by simp [hff']) ?_
  have h : FinEnum.card (complete m ^hg G).V = Fintype.card (G.V → (complete m).V) :=
    FinEnum.card_eq_fintypeCard.trans
      (Fintype.card_congr (Equiv.subtypeUnivEquiv fun f u v _ ↦ adjR_complete m (f u) (f v)))
  rw [h]
  simp

/-- No vertices to any power: no maps at all, unless the exponent is empty too. -/
@[toIsoGraph simp empty_zero_homExponential]
noncomputable def emptyZeroHomExponential (G : CGraph) :
    empty 0 ^hg G ≃cg empty (0 ^ FinEnum.card G.V) := by
  refine isoEmptyOfCard (fun f f' ↦ ?_) ?_
  · by_cases h : Nonempty G.V
    · exact (f.1 h.some).elim0
    · have hf : f = f' := Subtype.ext (funext fun x ↦ absurd ⟨x⟩ h)
      simp [hf]
  · by_cases h : Nonempty G.V
    · obtain ⟨x⟩ := h
      haveI : Nonempty G.V := ⟨x⟩
      rw [zero_pow (FinEnum.card_pos_iff.2 ⟨x⟩).ne']
      exact FinEnum.card_eq_zero_iff.2 ⟨fun f ↦ (f.1 x).elim0⟩
    · have hcard : FinEnum.card G.V = 0 := FinEnum.card_eq_zero_iff.2 ⟨fun x ↦ h ⟨x⟩⟩
      rw [hcard, pow_zero, FinEnum.card_eq_fintypeCard]
      exact Fintype.card_eq_one_iff.2
        ⟨⟨fun x ↦ absurd ⟨x⟩ h, fun u _ _ ↦ absurd ⟨u⟩ h⟩,
          fun f ↦ Subtype.ext (funext fun x ↦ absurd ⟨x⟩ h)⟩

/-- **A sum in the exponent is a strong product of powers.** -/
@[toIsoGraph homExponential_disjUnion]
def homExponentialDisjUnion (A B C : CGraph) :
    A ^hg (B ⊕g C) ≃cg (A ^hg B) ⊠g (A ^hg C) := by
  refine isoOfAdjR
    { toFun := fun f ↦
        (⟨fun u ↦ f.1 (.inl u), fun u v huv ↦ f.2 _ _ (by rwa [adjR_disjUnion_inl])⟩,
          ⟨fun u ↦ f.1 (.inr u), fun u v huv ↦ f.2 _ _ (by rwa [adjR_disjUnion_inr])⟩)
      invFun := fun p ↦ ⟨Sum.elim p.1.1 p.2.1, by
        rintro (u | u) (v | v) huv
        · exact p.1.2 u v (by rwa [adjR_disjUnion_inl] at huv)
        · simp at huv
        · simp at huv
        · exact p.2.2 u v (by rwa [adjR_disjUnion_inr] at huv)⟩
      left_inv := fun f ↦ Subtype.ext (funext fun u ↦ by cases u <;> rfl)
      right_inv := fun p ↦ rfl } ?_
  intro f f'
  rw [adjR_strongProduct, adjR_homExponential, adjR_homExponential, adjR_homExponential,
    ← Bool.decide_and, decide_eq_decide]
  constructor
  · rintro ⟨h1, h2⟩ (u | u) (v | v) huv
    · exact h1 u v (by rwa [← adjR_disjUnion_inl (H := C)])
    · simp at huv
    · simp at huv
    · exact h2 u v (by rwa [← adjR_disjUnion_inr (G := B)])
  · exact fun h ↦ ⟨fun u v huv ↦ h _ _ (by rwa [adjR_disjUnion_inl]),
      fun u v huv ↦ h _ _ (by rwa [adjR_disjUnion_inr])⟩

/-- **A strong product in the base is a strong product of powers.** -/
@[toIsoGraph strongProduct_homExponential]
def strongProductHomExponential (A B C : CGraph) :
    (A ⊠g B) ^hg C ≃cg (A ^hg C) ⊠g (B ^hg C) := by
  refine isoOfAdjR
    { toFun := fun f ↦
        (⟨fun u ↦ (f.1 u).1, fun u v huv ↦ by
            have h := f.2 u v huv
            rw [adjR_strongProduct, Bool.and_eq_true] at h
            exact h.1⟩,
          ⟨fun u ↦ (f.1 u).2, fun u v huv ↦ by
            have h := f.2 u v huv
            rw [adjR_strongProduct, Bool.and_eq_true] at h
            exact h.2⟩)
      invFun := fun p ↦ ⟨fun u ↦ (p.1.1 u, p.2.1 u), fun u v huv ↦ by
        rw [adjR_strongProduct, Bool.and_eq_true]
        exact ⟨p.1.2 u v huv, p.2.2 u v huv⟩⟩
      left_inv := fun f ↦ Subtype.ext (funext fun u ↦ rfl)
      right_inv := fun p ↦ rfl } ?_
  intro f f'
  rw [adjR_strongProduct, adjR_homExponential, adjR_homExponential, adjR_homExponential,
    ← Bool.decide_and, decide_eq_decide]
  constructor
  · rintro ⟨h1, h2⟩ u v huv
    rw [adjR_strongProduct, Bool.and_eq_true]
    exact ⟨h1 u v huv, h2 u v huv⟩
  · refine fun h ↦ ⟨fun u v huv ↦ ?_, fun u v huv ↦ ?_⟩ <;>
      · have hh := h u v huv
        rw [adjR_strongProduct, Bool.and_eq_true] at hh
        simp [hh.1, hh.2]

/-- **The tower law**: the reflexive exponential is the right adjoint of the strong product. -/
@[toIsoGraph homExponential_homExponential]
def homExponentialHomExponential (A B C : CGraph) :
    (A ^hg B) ^hg C ≃cg A ^hg (B ⊠g C) := by
  refine isoOfAdjR
    { toFun := fun F ↦ ⟨fun p ↦ (F.1 p.2).1 p.1, fun p q hpq ↦ by
        rw [adjR_strongProduct, Bool.and_eq_true] at hpq
        have h := F.2 p.2 q.2 hpq.2
        rw [adjR_homExponential] at h
        exact of_decide_eq_true h p.1 q.1 hpq.1⟩
      invFun := fun g ↦ ⟨fun u ↦ ⟨fun x ↦ g.1 (x, u),
          fun x y hxy ↦ g.2 (x, u) (y, u) (by simp [hxy])⟩,
        fun u v huv ↦ by
          rw [adjR_homExponential]
          exact decide_eq_true fun x y hxy ↦ g.2 (x, u) (y, v) (by simp [hxy, huv])⟩
      left_inv := fun F ↦ Subtype.ext (funext fun u ↦ Subtype.ext (funext fun x ↦ rfl))
      right_inv := fun g ↦ Subtype.ext (funext fun p ↦ rfl) } ?_
  intro F F'
  rw [adjR_homExponential, adjR_homExponential, decide_eq_decide]
  constructor
  · intro h u v huv
    rw [adjR_homExponential]
    refine decide_eq_true fun x y hxy ↦ h (x, u) (y, v) ?_
    simp [hxy, huv]
  · rintro h ⟨x, u⟩ ⟨y, v⟩ hpq
    rw [adjR_strongProduct, Bool.and_eq_true] at hpq
    have hh := h u v hpq.2
    rw [adjR_homExponential] at hh
    exact of_decide_eq_true hh x y hpq.1

/-- An edgeless base and a connected exponent: a homomorphism into an edgeless graph is constant
on a connected graph, so the power is edgeless on `m` vertices. -/
noncomputable def emptyHomExponentialConnected (m : ℕ) {G : CGraph} (hG : G.IsConnected) :
    empty m ^hg G ≃cg empty m := by
  have x₀ : G.V := hG.nonempty.some
  have hconst : ∀ (f : (empty m ^hg G).V) x y, G.Adj x y → f.1 x = f.1 y :=
    fun f x y hxy ↦ by simpa using f.2 x y (adjR_of_adj hxy)
  refine isoEmptyOfCard (fun f f' ↦ ?_) ?_
  · by_contra hc
    rw [Bool.not_eq_false, homExponential_adj, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hc
    exact hc.1 (Subtype.ext (funext fun u ↦ by simpa using hc.2 u u (by simp)))
  · rw [FinEnum.card_eq_fintypeCard, Fintype.card_congr (α := (empty m ^hg G).V) (β := (empty m).V)
      { toFun := fun f ↦ f.1 x₀
        invFun := fun b ↦ ⟨fun _ ↦ b, fun u v _ ↦ by simp⟩
        left_inv := fun f ↦ Subtype.ext (funext fun u ↦
          eq_of_forall_adj hG (hconst f) x₀ u)
        right_inv := fun b ↦ rfl }]
    simp

end CGraph.Iso

namespace IsoGraph

/-- **An edgeless base and a connected exponent**: `empty m ^hg G = empty m`.  In general the
answer is `empty (m ^ numComponents G)`, one choice of vertex per component. -/
theorem empty_homExponential_of_isConnected (m : ℕ) {G : IsoGraph} (h : G.IsConnected) :
    empty m ^hg G = empty m := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [isConnected_mk] at h
    exact Quotient.sound ⟨CGraph.Iso.emptyHomExponentialConnected m h⟩

theorem empty_zero_homExponential_of_ne {G : IsoGraph} (h : G ≠ empty 0) :
    empty 0 ^hg G = empty 0 := by
  rw [empty_zero_homExponential, zero_pow]
  simpa using h

/-! ## The scoped power notation, again -/

/-- `^` for `CGraph`, with a graph in the exponent, the reflexive convention. -/
def instPowHomCGraph : Pow CGraph CGraph := ⟨CGraph.homExponential⟩

/-- `^` for `IsoGraph`, with a class in the exponent, the reflexive convention. -/
def instPowHomIsoGraph : Pow IsoGraph IsoGraph := ⟨IsoGraph.homExponential⟩

end IsoGraph

namespace IsoGraph.HomExponential

attribute [scoped instance] IsoGraph.instPowHomCGraph IsoGraph.instPowHomIsoGraph

@[scoped simp] theorem cgraph_pow_eq (G H : CGraph) : G ^ H = G ^hg H := rfl

@[scoped simp] theorem pow_eq (G H : IsoGraph) : G ^ H = G ^hg H := rfl

end IsoGraph.HomExponential

namespace IsoGraph

/-! ## Simp normal form

The four computable powers reduce; the three laws are `rfl`-free theorems and are not simp lemmas,
since neither side is smaller than the other. -/

example (G : IsoGraph) : G ^hg empty 1 = G := by simp

example (G : IsoGraph) : G ^hg empty 0 = empty 1 := by simp

example (G : IsoGraph) : empty 1 ^hg G = empty 1 := by simp

example (G : IsoGraph) : empty 0 ^hg G = empty (0 ^ G.V) := by simp

example (m : ℕ) (G : IsoGraph) : complete m ^hg G = complete (m ^ G.V) := by simp

example (A B C : IsoGraph) : (A ^hg B) ^hg C = A ^hg (B ⊠g C) := homExponential_homExponential A B C

example (A B C : IsoGraph) : A ^hg (B ⊕g C) = A ^hg B ⊠g A ^hg C := homExponential_disjUnion A B C

example (A B C : IsoGraph) : (A ⊠g B) ^hg C = A ^hg C ⊠g B ^hg C :=
  strongProduct_homExponential A B C

open scoped IsoGraph.HomExponential in
example (G H : IsoGraph) :
    G ^ (empty 1 : IsoGraph) = G ∧ (G ^hg H) ^ (empty 1 : IsoGraph) = G ^hg H := by
  simp

end IsoGraph
