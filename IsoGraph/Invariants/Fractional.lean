import IsoGraph.Invariants.Derived
import IsoGraph.Core.Colouring
import Mathlib.Data.Real.Archimedean

/-!
# The fractional relaxations

Four of the invariants of `IsoGraph.Invariants` are NP-hard to compute: `α`, `ω`, `χ` and `θ`.
Each of them is the value of an integer program, and relaxing the integrality constraint gives a
linear program whose value is computable in the size of the program — the *fractional*
independence number and the *fractional* chromatic number.  This file defines them and places
them between the invariants they relax.

The independence number is the largest number of vertices no two of which are adjacent.  Written
as a program: give every vertex a weight of `0` or `1`, keep the weight of every clique at most
one, and maximise the total.  Dropping "`0` or `1`" in favour of "at least `0`" gives

* `CGraph.IsFracIndep` — a nonnegative rational weighting of the vertices that puts weight at
  most one on every clique;
* `CGraph.fracIndepNum` — the supremum `α_f(G)` of the totals of such weightings.

The complement turns cliques into independent sets, so the same program on `Gᶜ` is the fractional
*clique* number, which is what `CGraph.fracChromNum` is defined to be.  Linear programming
duality identifies it with the usual covering definition of `χ_f` — the least total weight of a
nonnegative weighting of the independent sets that covers every vertex — but that duality is not
proved here, and nothing below needs it.

The four bounds this file exists for are

| bound | name |
| --- | --- |
| `α(G) ≤ α_f(G)` | `CGraph.indepNum_le_fracIndepNum` |
| `α_f(G) ≤ θ(G)` | `CGraph.fracIndepNum_le_cliqueCoverNum` |
| `ω(G) ≤ χ_f(G)` | `CGraph.cliqueNum_le_fracChromNum` |
| `χ_f(G) ≤ χ(G)` | `CGraph.fracChromNum_le_chromNum` |

with the last two the first two read on the complement.  `CGraph.fracCliqueCoverNum` is the
covering program dual to `α_f`; it is here for completeness, with weak duality
`α_f ≤ θ_f` and nothing else.

Both directions of a fractional bound come with a finite certificate, and those are what the
`compute_fractional_indepNum` tactic emits: `CGraph.fracIndepNum_le_of_cover` takes a *fractional
clique cover* — finitely many cliques with nonnegative weights covering every vertex — and
`CGraph.le_fracIndepNum` takes a single feasible weighting.  Feasibility quantifies over all
cliques, so `CGraph.isFracIndep_of_card_le` cuts the check down to the sets of at most `ω`
vertices, which is a `decide` of `∑_{k ≤ ω} (n choose k)` sums rather than of `2 ^ n`.  What the
tactic in `IsoGraph/Fractional.lean` actually calls are the integer-scaled forms of those two,
`CGraph.fracIndepNum_le_of_natCover` and `CGraph.le_fracIndepNum_of_natWeights`, which take the
weights already cleared of denominators so that no side condition mentions `ℚ` at all.

Finally, since `α` and `ω` are integers, an upper bound on `α_f` rounds down and a lower bound on
`χ_f` rounds up: `CGraph.indepNum_le_of_fracIndepNum_le` and
`CGraph.lt_chromNum_of_lt_fracChromNum` are the integrality steps that let a linear program settle
a goal `graph_sat` would otherwise have to search for.
-/

set_option autoImplicit false

open Finset

namespace CGraph

variable (G : CGraph)

/-! ## Cliques as a decidable predicate on finite sets

`SimpleGraph.IsClique` is a statement about a `Set`, and the sets that a certificate names are
`Finset`s.  `IsCliqueOn` is the same condition phrased so that it is decidable by `decide`. -/

/-- `G.IsCliqueOn K`: the vertices of the finite set `K` are pairwise adjacent. -/
def IsCliqueOn (K : Finset G.V) : Prop := ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v = true

instance (K : Finset G.V) : Decidable (G.IsCliqueOn K) :=
  inferInstanceAs (Decidable (∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v = true))

variable {G}

theorem isCliqueOn_iff {K : Finset G.V} :
    G.IsCliqueOn K ↔ G.toSimple.IsClique (↑K : Set G.V) := by
  constructor
  · intro h u hu v hv huv
    exact (toSimple_adj _ _ _).2 (h u hu v hv huv)
  · intro h u hu v hv huv
    exact (toSimple_adj _ _ _).1 (h hu hv huv)

theorem IsCliqueOn.card_le_cliqueNum {K : Finset G.V} (h : G.IsCliqueOn K) :
    K.card ≤ G.cliqueNum :=
  SimpleGraph.IsClique.card_le_cliqueNum (tc := isCliqueOn_iff.1 h)

@[simp] theorem isCliqueOn_empty : G.IsCliqueOn (∅ : Finset G.V) := by
  intro u hu; exact absurd hu (by simp)

@[simp] theorem isCliqueOn_singleton (v : G.V) : G.IsCliqueOn ({v} : Finset G.V) := by
  intro u hu w hw huw
  rw [Finset.mem_singleton] at hu hw
  exact absurd (hu.trans hw.symm) huw

/-! ## The fractional independence number -/

variable (G)

/-- A *fractional independent set*: a nonnegative weight on each vertex, with total weight at
most one on every clique.  The indicator of an independent set is one; the definition is the
relaxation of that special case in which the weights are allowed to be any rationals. -/
def IsFracIndep (x : G.V → ℚ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ K : Finset G.V, G.IsCliqueOn K → ∑ v ∈ K, x v ≤ 1

variable {G}

theorem IsFracIndep.nonneg {x : G.V → ℚ} (h : G.IsFracIndep x) (v : G.V) : 0 ≤ x v := h.1 v

theorem IsFracIndep.sum_le {x : G.V → ℚ} (h : G.IsFracIndep x) {K : Finset G.V}
    (hK : G.IsCliqueOn K) : ∑ v ∈ K, x v ≤ 1 := h.2 K hK

/-- A single vertex is a clique, so a fractional independent set weights it at most one. -/
theorem IsFracIndep.le_one {x : G.V → ℚ} (h : G.IsFracIndep x) (v : G.V) : x v ≤ 1 := by
  have := h.sum_le (isCliqueOn_singleton v)
  simpa using this

theorem isFracIndep_zero (G : CGraph) : G.IsFracIndep 0 := ⟨fun _ ↦ le_rfl, fun _ _ ↦ by simp⟩

/-- **A bound on the clique number cuts the feasibility check down to the small sets.**  A
weighting is feasible as soon as it is feasible on the cliques of at most `w` vertices, provided
no clique is larger than that; the sets of at most `w` vertices are a decidable range to search,
where "all cliques" would be `2 ^ n` sets. -/
theorem isFracIndep_of_card_le {x : G.V → ℚ} {w : ℕ} (hnn : ∀ v, 0 ≤ x v)
    (hw : G.cliqueNum ≤ w)
    (h : ∀ k ≤ w, ∀ K ∈ Finset.powersetCard k (Finset.univ : Finset G.V),
      G.IsCliqueOn K → ∑ v ∈ K, x v ≤ 1) :
    G.IsFracIndep x := by
  refine ⟨hnn, fun K hK ↦ ?_⟩
  refine h K.card (le_trans hK.card_le_cliqueNum hw) K ?_ hK
  simp [Finset.mem_powersetCard]

variable (G)

/-- The totals of the fractional independent sets: the feasible objective values of the linear
program whose optimum is `CGraph.fracIndepNum`. -/
def fracIndepVals : Set ℝ :=
  {r | ∃ x : G.V → ℚ, G.IsFracIndep x ∧ ((∑ v, x v : ℚ) : ℝ) = r}

theorem fracIndepVals_nonempty : G.fracIndepVals.Nonempty :=
  ⟨0, 0, G.isFracIndep_zero, by simp⟩

theorem fracIndepVals_bddAbove : BddAbove G.fracIndepVals := by
  refine ⟨(Fintype.card G.V : ℝ), ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have h : ∑ v, x v ≤ (Fintype.card G.V : ℚ) := by
    calc ∑ v, x v ≤ ∑ _v : G.V, (1 : ℚ) := Finset.sum_le_sum fun v _ ↦ hx.le_one v
      _ = (Fintype.card G.V : ℚ) := by simp
  exact_mod_cast h

/-- The *fractional independence number* `α_f(G)`: the value of the linear program that relaxes
the independence number, that is, the largest total weight of a fractional independent set. -/
noncomputable def fracIndepNum : ℝ := sSup G.fracIndepVals

variable {G}

/-- **A feasible weighting bounds the fractional independence number below.** -/
theorem le_fracIndepNum {x : G.V → ℚ} (hx : G.IsFracIndep x) :
    ((∑ v, x v : ℚ) : ℝ) ≤ G.fracIndepNum :=
  le_csSup G.fracIndepVals_bddAbove ⟨x, hx, rfl⟩

/-- **Every feasible weighting bounds the fractional independence number above.** -/
theorem fracIndepNum_le {c : ℝ} (h : ∀ x : G.V → ℚ, G.IsFracIndep x → ((∑ v, x v : ℚ) : ℝ) ≤ c) :
    G.fracIndepNum ≤ c :=
  csSup_le G.fracIndepVals_nonempty (by rintro r ⟨x, hx, rfl⟩; exact h x hx)

variable (G)

theorem zero_le_fracIndepNum : 0 ≤ G.fracIndepNum := by
  have := le_fracIndepNum (G.isFracIndep_zero)
  simpa using this

theorem fracIndepNum_le_card : G.fracIndepNum ≤ FinEnum.card G.V := by
  refine fracIndepNum_le fun x hx ↦ ?_
  have h : ∑ v, x v ≤ (Fintype.card G.V : ℚ) := by
    calc ∑ v, x v ≤ ∑ _v : G.V, (1 : ℚ) := Finset.sum_le_sum fun v _ ↦ hx.le_one v
      _ = (Fintype.card G.V : ℚ) := by simp
  rw [FinEnum.card_eq_fintypeCard' (α := G.V)]
  exact_mod_cast h

/-! ## The certificates

The two directions of a fractional bound are certified differently.  A lower bound is one
feasible weighting, `CGraph.le_fracIndepNum`.  An upper bound is a *fractional clique cover*: a
family of cliques with nonnegative weights, together putting weight at least one on every vertex.
Weak duality says the total weight of any such cover bounds `α_f` above, which is the direction
that bounds `α` and so the direction a tactic wants. -/

/-- **Weak duality: a fractional clique cover bounds the fractional independence number above.**
The cliques `K i` carry weights `y i ≥ 0` covering every vertex to total weight at least one;
then no fractional independent set can total more than `∑ y`.

The cliqueness hypothesis is only needed where the weight is nonzero, so a cover may be padded
with junk sets of weight zero. -/
theorem fracIndepNum_le_of_cover {ι : Type*} [Fintype ι] (K : ι → Finset G.V) (y : ι → ℚ)
    (hy : ∀ i, 0 ≤ y i) (hK : ∀ i, y i ≠ 0 → G.IsCliqueOn (K i))
    (hcov : ∀ v : G.V, 1 ≤ ∑ i, if v ∈ K i then y i else 0) :
    G.fracIndepNum ≤ ((∑ i, y i : ℚ) : ℝ) := by
  refine fracIndepNum_le fun x hx ↦ ?_
  have key : ∑ v, x v ≤ ∑ i, y i := by
    calc ∑ v, x v ≤ ∑ v, (∑ i, if v ∈ K i then y i else 0) * x v :=
          Finset.sum_le_sum fun v _ ↦ le_mul_of_one_le_left (hx.nonneg v) (hcov v)
      _ = ∑ i, ∑ v, (if v ∈ K i then y i else 0) * x v := by
          simp only [Finset.sum_mul]; exact Finset.sum_comm
      _ = ∑ i, y i * ∑ v ∈ K i, x v := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [ite_mul, Finset.sum_ite_mem, Finset.mul_sum]
      _ ≤ ∑ i, y i * 1 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rcases eq_or_ne (y i) 0 with h | h
          · simp [h]
          · exact mul_le_mul_of_nonneg_left (hx.sum_le (hK i h)) (hy i)
      _ = ∑ i, y i := by simp
  exact_mod_cast key

/-- Pulling a constant denominator out of a sum of natural numbers, the shape both scaled
certificates need. -/
private theorem sum_natCast_div {α : Type*} {R : Type*} [DivisionRing R] (s : Finset α)
    (f : α → ℕ) (d : ℕ) :
    ∑ i ∈ s, (f i : R) / (d : R) = ((∑ i ∈ s, f i : ℕ) : R) / (d : R) := by
  rw [div_eq_mul_inv, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [div_eq_mul_inv]

/-- **An upper bound from an integer-scaled fractional clique cover.**  The same certificate as
`CGraph.fracIndepNum_le_of_cover` with the denominators cleared: the cliques `K i` carry natural
weights `a i` and every vertex is covered to total weight at least `d`, so `α_f ≤ (∑ a) / d`.

Every hypothesis is then an arithmetic statement about natural numbers, which is what a machine
can hand back and `decide` can check. -/
theorem fracIndepNum_le_of_natCover {m d s : ℕ} (hd : 0 < d) (K : Fin m → Finset G.V)
    (a : Fin m → ℕ) (hs : ∑ i, a i = s) (hK : ∀ i, a i ≠ 0 → G.IsCliqueOn (K i))
    (hcov : ∀ v : G.V, d ≤ ∑ i, if v ∈ K i then a i else 0) :
    G.fracIndepNum ≤ (s : ℝ) / (d : ℝ) := by
  subst hs
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hcov' : ∀ v : G.V, 1 ≤ ∑ i, if v ∈ K i then ((a i : ℚ) / (d : ℚ)) else 0 := by
    intro v
    have hcast : ∑ i, (if v ∈ K i then (a i : ℚ) / (d : ℚ) else 0)
        = ((∑ i, if v ∈ K i then a i else 0 : ℕ) : ℚ) / (d : ℚ) := by
      rw [← sum_natCast_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      split_ifs <;> simp
    rw [hcast, le_div_iff₀ hd', one_mul]
    exact_mod_cast hcov v
  have h := fracIndepNum_le_of_cover (G := G) K (fun i ↦ (a i : ℚ) / (d : ℚ))
    (fun i ↦ div_nonneg (by positivity) hd'.le)
    (fun i hi ↦ hK i (by simpa [div_eq_zero_iff, hd'.ne'] using hi)) hcov'
  refine le_trans h (le_of_eq ?_)
  simp only [sum_natCast_div]
  push_cast
  ring

/-- **A lower bound from an integer-scaled feasible weighting.**  The vertex `v` carries weight
`b v / d`; feasibility need only be checked on the sets of at most `w` vertices, where `w` bounds
the clique number, so `α_f ≥ (∑ b) / d`. -/
theorem le_fracIndepNum_of_natWeights {d w s : ℕ} (hd : 0 < d) (b : G.V → ℕ)
    (hs : ∑ v, b v = s) (hw : G.cliqueNum ≤ w)
    (h : ∀ k ≤ w, ∀ K ∈ Finset.powersetCard k (Finset.univ : Finset G.V),
      G.IsCliqueOn K → ∑ v ∈ K, b v ≤ d) :
    (s : ℝ) / (d : ℝ) ≤ G.fracIndepNum := by
  subst hs
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hfeas : G.IsFracIndep (fun v ↦ (b v : ℚ) / (d : ℚ)) :=
    isFracIndep_of_card_le (fun v ↦ div_nonneg (by positivity) hd'.le) hw fun k hk K hK hcl ↦ by
      rw [sum_natCast_div, div_le_one hd']
      exact_mod_cast h k hk K hK hcl
  have hle := le_fracIndepNum hfeas
  simp only [sum_natCast_div] at hle
  push_cast at hle ⊢
  exact hle

/-- **A partition of the vertices into cliques bounds the fractional independence number
above.**  A colouring whose colour classes are cliques — a proper colouring of the complement —
is the integral fractional clique cover, and gives `α_f(G) ≤ k`. -/
theorem fracIndepNum_le_of_cliqueColouring {k : ℕ} (c : G.V → Fin k)
    (hc : ∀ u v : G.V, u ≠ v → c u = c v → G.Adj u v = true) : G.fracIndepNum ≤ k := by
  classical
  refine fracIndepNum_le fun x hx ↦ ?_
  have hfib : ∑ i : Fin k, ∑ v ∈ Finset.univ.filter (fun v ↦ c v = i), x v = ∑ v, x v :=
    Finset.sum_fiberwise _ _ _
  have key : ∑ v, x v ≤ (k : ℚ) := by
    rw [← hfib]
    calc ∑ i : Fin k, ∑ v ∈ Finset.univ.filter (fun v ↦ c v = i), x v
        ≤ ∑ _i : Fin k, (1 : ℚ) := by
          refine Finset.sum_le_sum fun i _ ↦ hx.sum_le fun u hu w hw huw ↦ ?_
          simp only [Finset.mem_filter] at hu hw
          exact hc u w huw (hu.2.trans hw.2.symm)
      _ = (k : ℚ) := by simp
  exact_mod_cast key

/-- **A bound on the clique number bounds the fractional independence number below**: the uniform
weighting `1 / w` is feasible as soon as no clique has more than `w` vertices, so
`α_f(G) ≥ n / ω(G)`.  Applied to the complement this is the classical `χ_f(G) ≥ n / α(G)`. -/
theorem card_div_le_fracIndepNum {w : ℕ} (hw : 0 < w) (h : G.cliqueNum ≤ w) :
    (FinEnum.card G.V : ℝ) / w ≤ G.fracIndepNum := by
  have hw' : (0 : ℚ) < (w : ℚ) := by exact_mod_cast hw
  have hfeas : G.IsFracIndep (fun _ ↦ 1 / (w : ℚ)) := by
    refine ⟨fun _ ↦ div_nonneg zero_le_one hw'.le, fun K hK ↦ ?_⟩
    have hcard : (K.card : ℚ) ≤ (w : ℚ) := by
      exact_mod_cast le_trans hK.card_le_cliqueNum h
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [mul_one_div, div_le_one hw']
    exact hcard
  have := le_fracIndepNum hfeas
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, Finset.card_univ] at this
  rw [FinEnum.card_eq_fintypeCard' (α := G.V)]
  push_cast at this ⊢
  exact this

/-! ## The relaxation of the independence number

`α ≤ α_f ≤ θ`: an independent set is a fractional independent set, and a partition into cliques
is a fractional clique cover. -/

/-- **The independence number is at most the fractional independence number.**  The indicator of
a largest independent set is feasible: a clique and an independent set share at most one
vertex. -/
theorem indepNum_le_fracIndepNum : (G.indepNum : ℝ) ≤ G.fracIndepNum := by
  classical
  obtain ⟨S, hS, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hfeas : G.IsFracIndep (fun v ↦ if v ∈ S then 1 else 0) := by
    refine ⟨fun v ↦ by positivity, fun K hK ↦ ?_⟩
    have hinter : ((K ∩ S).card : ℚ) ≤ 1 := by
      have : (K ∩ S).card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
        simp only [Finset.mem_inter] at ha hb
        by_contra hab
        exact hS (by simpa using ha.2) (by simpa using hb.2) hab
          ((toSimple_adj _ _ _).2 (hK a ha.1 b hb.1 hab))
      exact_mod_cast this
    calc ∑ v ∈ K, (if v ∈ S then (1 : ℚ) else 0) = ∑ _v ∈ K ∩ S, (1 : ℚ) :=
          Finset.sum_ite_mem K S _
      _ = ((K ∩ S).card : ℚ) := by simp
      _ ≤ 1 := hinter
  have hsum : ∑ v, (if v ∈ S then (1 : ℚ) else 0) = (G.indepNum : ℚ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    rfl
  have := le_fracIndepNum hfeas
  rwa [hsum, Rat.cast_natCast] at this

/-- **The fractional independence number is at most the clique cover number.**  A cover of the
vertices by `θ(G)` cliques is a fractional clique cover of total weight `θ(G)`. -/
theorem fracIndepNum_le_cliqueCoverNum : G.fracIndepNum ≤ G.cliqueCoverNum := by
  obtain ⟨c⟩ := colorable_chromNum (G := Gᶜ)
  refine fracIndepNum_le_of_cliqueColouring (G := G) (k := Gᶜ.chromNum) (fun v ↦ c v) ?_
  intro u v huv hcuv
  dsimp only at hcuv
  by_contra hadj
  refine c.valid ?_ hcuv
  rw [toSimple_adj, compl_adj]
  simp [huv, Bool.eq_false_iff.2 hadj]

/-! ## The relaxation of the chromatic number

The fractional chromatic number is the fractional independence number of the complement, and
`ω ≤ χ_f ≤ χ` is `α ≤ α_f ≤ θ` read there. -/

/-- The *fractional chromatic number* `χ_f(G)`: the value of the packing program on the
complement, that is, the fractional clique number.  Linear programming duality identifies it with
the least total weight of a fractional cover of the vertices by independent sets, which is the
usual definition; the duality is not proved here. -/
noncomputable def fracChromNum : ℝ := Gᶜ.fracIndepNum

theorem fracChromNum_eq_compl : G.fracChromNum = Gᶜ.fracIndepNum := rfl

theorem zero_le_fracChromNum : 0 ≤ G.fracChromNum := Gᶜ.zero_le_fracIndepNum

/-- **The clique number is at most the fractional chromatic number.** -/
theorem cliqueNum_le_fracChromNum : (G.cliqueNum : ℝ) ≤ G.fracChromNum := by
  have := Gᶜ.indepNum_le_fracIndepNum
  rwa [indepNum_compl] at this

/-- **The fractional chromatic number is at most the chromatic number.**  A proper colouring of
`G` has independent colour classes, which are cliques of `Gᶜ`. -/
theorem fracChromNum_le_chromNum : G.fracChromNum ≤ G.chromNum := by
  obtain ⟨c⟩ := colorable_chromNum (G := G)
  refine fracIndepNum_le_of_cliqueColouring (G := Gᶜ) (k := G.chromNum) (fun v ↦ c v) ?_
  intro u v huv hcuv
  dsimp only at hcuv
  rw [compl_adj]
  have hadj : G.Adj u v = false := by
    cases hb : G.Adj u v with
    | false => rfl
    | true => exact absurd hcuv (c.valid ((toSimple_adj _ _ _).2 hb))
  simp [huv, hadj]

/-- **A bound on the independence number bounds the fractional chromatic number below**:
`χ_f(G) ≥ n / α(G)`, the uniform weighting on the complement. -/
theorem card_div_le_fracChromNum {w : ℕ} (hw : 0 < w) (h : G.indepNum ≤ w) :
    (FinEnum.card G.V : ℝ) / w ≤ G.fracChromNum := by
  have := card_div_le_fracIndepNum (G := Gᶜ) hw (by rwa [cliqueNum_compl])
  rwa [card_compl] at this

/-! ## The covering program

The program dual to `α_f`: weights on the cliques rather than on the vertices, covering every
vertex instead of packing every clique.  Strong duality would make it equal to `α_f`; only weak
duality is proved. -/

/-- A *fractional clique cover*: a nonnegative weight on each set of vertices, zero off the
cliques, putting total weight at least one on every vertex. -/
def IsFracCliqueCover (y : Finset G.V → ℚ) : Prop :=
  (∀ K, 0 ≤ y K) ∧ (∀ K, y K ≠ 0 → G.IsCliqueOn K) ∧
    ∀ v : G.V, 1 ≤ ∑ K : Finset G.V, if v ∈ K then y K else 0

/-- The totals of the fractional clique covers. -/
def fracCliqueCoverVals : Set ℝ :=
  {r | ∃ y : Finset G.V → ℚ, G.IsFracCliqueCover y ∧ ((∑ K, y K : ℚ) : ℝ) = r}

/-- The cover by singletons: every vertex is a clique on its own. -/
theorem isFracCliqueCover_singletons :
    G.IsFracCliqueCover (fun K ↦ if K.card = 1 then 1 else 0) := by
  refine ⟨fun K ↦ by dsimp only; split_ifs <;> norm_num, fun K hK ↦ ?_, fun v ↦ ?_⟩
  · have h1 : K.card = 1 := by
      by_contra h
      simp only [h, if_false] at hK
      exact hK rfl
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.1 h1
    exact isCliqueOn_singleton u
  · have hnn : ∀ K ∈ (Finset.univ : Finset (Finset G.V)),
        0 ≤ (if v ∈ K then (if K.card = 1 then (1 : ℚ) else 0) else 0) := by
      intro K _
      split_ifs <;> norm_num
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ ({v} : Finset G.V)))
    simp

theorem fracCliqueCoverVals_nonempty : G.fracCliqueCoverVals.Nonempty :=
  ⟨_, _, G.isFracCliqueCover_singletons, rfl⟩

theorem fracCliqueCoverVals_bddBelow : BddBelow G.fracCliqueCoverVals := by
  refine ⟨0, ?_⟩
  rintro r ⟨y, hy, rfl⟩
  have : (0 : ℚ) ≤ ∑ K, y K := Finset.sum_nonneg fun K _ ↦ hy.1 K
  exact_mod_cast this

/-- The *fractional clique cover number* `θ_f(G)`: the least total weight of a fractional clique
cover.  It is the linear programming dual of `α_f`, so strong duality would make the two equal;
`CGraph.fracIndepNum_le_fracCliqueCoverNum` is the easy half. -/
noncomputable def fracCliqueCoverNum : ℝ := sInf G.fracCliqueCoverVals

/-- **Weak duality**: every fractional clique cover outweighs every fractional independent
set. -/
theorem fracIndepNum_le_fracCliqueCoverNum : G.fracIndepNum ≤ G.fracCliqueCoverNum := by
  refine le_csInf G.fracCliqueCoverVals_nonempty ?_
  rintro r ⟨y, hy, rfl⟩
  exact fracIndepNum_le_of_cover (G := G) (ι := Finset G.V) id y hy.1 hy.2.1 hy.2.2

theorem fracCliqueCoverNum_le_card : G.fracCliqueCoverNum ≤ FinEnum.card G.V := by
  classical
  refine csInf_le G.fracCliqueCoverVals_bddBelow ⟨_, G.isFracCliqueCover_singletons, ?_⟩
  have hfilter : (Finset.univ.filter (fun K : Finset G.V ↦ K.card = 1))
      = Finset.powersetCard 1 (Finset.univ : Finset G.V) := by
    ext K; simp [Finset.mem_powersetCard]
  have h : ∑ K : Finset G.V, (if K.card = 1 then (1 : ℚ) else 0)
      = (FinEnum.card G.V : ℚ) := by
    rw [Finset.sum_boole, hfilter, Finset.card_powersetCard, Finset.card_univ,
      Nat.choose_one_right, FinEnum.card_eq_fintypeCard' (α := G.V)]
  rw [h]
  norm_num

/-! ## Integrality

`α` and `ω` are integers, so an upper bound on `α_f` may be rounded down and a lower bound on
`χ_f` rounded up.  These are the steps that turn a linear program into a proof about the
invariant it relaxes. -/

variable {G}

/-- **Integrality, above**: if the linear program stays below `n + 1` then the independence
number is at most `n`. -/
theorem indepNum_le_of_fracIndepNum_le {n : ℕ} {c : ℝ} (h : G.fracIndepNum ≤ c)
    (hc : c < n + 1) : G.indepNum ≤ n := by
  have h1 : (G.indepNum : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    push_cast
    exact lt_of_le_of_lt (le_trans G.indepNum_le_fracIndepNum h) hc
  exact Nat.lt_succ_iff.1 (by exact_mod_cast h1)

/-- **Integrality, above**: the same for the clique number, through the complement. -/
theorem cliqueNum_le_of_fracChromNum_le {n : ℕ} {c : ℝ} (h : G.fracChromNum ≤ c)
    (hc : c < n + 1) : G.cliqueNum ≤ n := by
  have h1 : (G.cliqueNum : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    push_cast
    exact lt_of_le_of_lt (le_trans G.cliqueNum_le_fracChromNum h) hc
  exact Nat.lt_succ_iff.1 (by exact_mod_cast h1)

/-- **Integrality, below**: a lower bound on the fractional chromatic number is a lower bound on
the chromatic number. -/
theorem lt_chromNum_of_lt_fracChromNum {k : ℕ} {c : ℝ} (hk : (k : ℝ) < c)
    (h : c ≤ G.fracChromNum) : k < G.chromNum := by
  have h1 : (k : ℝ) < (G.chromNum : ℝ) :=
    lt_of_lt_of_le hk (le_trans h G.fracChromNum_le_chromNum)
  exact_mod_cast h1

/-- **Integrality, below**: a lower bound on the fractional independence number is a lower bound
on the clique cover number. -/
theorem lt_cliqueCoverNum_of_lt_fracIndepNum {k : ℕ} {c : ℝ} (hk : (k : ℝ) < c)
    (h : c ≤ G.fracIndepNum) : k < G.cliqueCoverNum := by
  have h1 : (k : ℝ) < (G.cliqueCoverNum : ℝ) :=
    lt_of_lt_of_le hk (le_trans h G.fracIndepNum_le_cliqueCoverNum)
  exact_mod_cast h1

end CGraph
