import IsoGraph.Invariants.Derived
import IsoGraph.Core.Colouring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

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
nonnegative weighting of the independent sets that covers every vertex — and that duality is not
proved here in general, only for the vertex-transitive graphs
(`CGraph.fracChromNum_eq_fracCliqueCoverNum_compl`); nothing below needs it.

The four bounds this file exists for are

| bound | name |
| --- | --- |
| `α(G) ≤ α_f(G)` | `CGraph.indepNum_le_fracIndepNum` |
| `α_f(G) ≤ θ(G)` | `CGraph.fracIndepNum_le_cliqueCoverNum` |
| `ω(G) ≤ χ_f(G)` | `CGraph.cliqueNum_le_fracChromNum` |
| `χ_f(G) ≤ χ(G)` | `CGraph.fracChromNum_le_chromNum` |

with the last two the first two read on the complement.  `CGraph.fracCliqueCoverNum` is the
covering program dual to `α_f`; it is here for completeness, with weak duality `α_f ≤ θ_f` in
general and equality when `G` is vertex-transitive.

Past those four bounds is the basic theory of how the two quantities behave under substructure
and under the graph operations.  An adjacency-reflecting injection `H.V → G.V` cannot lower `α_f`
(`CGraph.fracIndepNum_le_of_injective`), which is every containment at once; `α_f` adds over `⊕`
and maximises over `∇` (`CGraph.fracIndepNum_disjUnion`, `CGraph.fracIndepNum_join`), with `χ_f`
doing the opposite; and `α_f` is multiplicative over the strong and lexicographic products
(`CGraph.fracIndepNum_strongProduct`, `CGraph.fracIndepNum_lexProduct`), which `α` is not.  The
two extremes are `CGraph.fracIndepNum_empty` and `CGraph.fracIndepNum_complete`, and the two
quantities meet in `CGraph.card_le_fracIndepNum_mul_fracChromNum`, the fractional `n ≤ α · χ`.

Both directions of a fractional bound come with a finite certificate, and those are what the
`compute_fractional_indepNum` tactic emits: `CGraph.fracIndepNum_le_of_cover` takes a *fractional
clique cover* — finitely many cliques with nonnegative weights covering every vertex — and
`CGraph.le_fracIndepNum` takes a single feasible weighting.  What the tactic in
`IsoGraph/Fractional.lean` actually calls are the integer-scaled forms of those two,
`CGraph.fracIndepNum_le_of_natCover` and `CGraph.le_fracIndepNum_of_natWeights`, which take the
weights already cleared of denominators so that no side condition mentions `ℚ` at all — and it
calls them through a further pair of bridges that phrase the side conditions as arithmetic on
lists of indices, since a `Finset G.V` is an expensive thing to ask a kernel about.
`CGraph.isFracIndep_of_card_le` is the other way to make feasibility finite — check the sets of at
most `ω` vertices — and is here for its own sake; the tactic enumerates cliques instead.

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
`b v / d`, no clique weighs more than `d`, and so `α_f ≥ (∑ b) / d`. -/
theorem le_fracIndepNum_of_natWeights {d s : ℕ} (hd : 0 < d) (b : G.V → ℕ)
    (hs : ∑ v, b v = s) (h : ∀ K : Finset G.V, G.IsCliqueOn K → ∑ v ∈ K, b v ≤ d) :
    (s : ℝ) / (d : ℝ) ≤ G.fracIndepNum := by
  subst hs
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hfeas : G.IsFracIndep (fun v ↦ (b v : ℚ) / (d : ℚ)) :=
    ⟨fun v ↦ div_nonneg (by positivity) hd'.le, fun K hK ↦ by
      rw [sum_natCast_div, div_le_one hd']
      exact_mod_cast h K hK⟩
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

/-- The two quantities are each other's on the complement, by definition one way and by
`CGraph.compl_compl` the other. -/
@[simp] theorem fracIndepNum_compl : Gᶜ.fracIndepNum = G.fracChromNum := rfl

@[simp] theorem fracChromNum_compl : Gᶜ.fracChromNum = G.fracIndepNum := by
  rw [fracChromNum_eq_compl, compl_compl]

theorem fracChromNum_le_card : G.fracChromNum ≤ FinEnum.card G.V :=
  Gᶜ.fracIndepNum_le_card

/-- **`n ≤ α_f(G) · χ_f(G)`**, the fractional form of `n ≤ α(G) · χ(G)`: the uniform weighting
`1 / ω(G)` is feasible, and `ω ≤ χ_f`. -/
theorem card_le_fracIndepNum_mul_fracChromNum :
    (FinEnum.card G.V : ℝ) ≤ G.fracIndepNum * G.fracChromNum := by
  rcases Nat.eq_zero_or_pos (FinEnum.card G.V) with h0 | h0
  · rw [h0, Nat.cast_zero]
    exact mul_nonneg G.zero_le_fracIndepNum G.zero_le_fracChromNum
  · have hne : Nonempty G.V := by
      rw [FinEnum.card_eq_fintypeCard' (α := G.V)] at h0
      exact Fintype.card_pos_iff.1 h0
    have hw : 0 < G.cliqueNum := one_le_cliqueNum
    have h := G.card_div_le_fracIndepNum hw le_rfl
    rw [div_le_iff₀ (by exact_mod_cast hw)] at h
    exact h.trans (mul_le_mul_of_nonneg_left G.cliqueNum_le_fracChromNum G.zero_le_fracIndepNum)

/-! ## Vertex-transitive graphs

Both relaxations are exactly the obvious ratio when the automorphism group is transitive: the
uniform weighting is optimal, so no integrality gap survives averaging.  This is where the two
programs part company with `α` and `χ`, for which the clique–coclique bound
`CGraph.indepNum_mul_cliqueNum_le_card` is only an inequality. -/

/-- The image of a clique under an adjacency-preserving permutation is a clique. -/
private theorem isCliqueOn_image {G : CGraph} {σ : Equiv.Perm G.V}
    (hσ : ∀ u v, G.Adj (σ u) (σ v) = G.Adj u v) {C : Finset G.V} (hC : G.IsCliqueOn C) :
    G.IsCliqueOn (C.image σ) := by
  classical
  intro u hu v hv huv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  rw [hσ a b]
  exact hC a ha b hb fun hab ↦ huv (by rw [hab])

/-- **Averaging a weighting over the automorphism group.**  If every automorphic image of `C`
carries weight at most one then `|C| · ∑ x ≤ |V|`: each of the `|Aut G|` automorphisms
contributes at most one, while for a fixed `c ∈ C` each vertex is `σ c` for exactly
`|Aut G| / |V|` automorphisms `σ`. -/
private theorem card_mul_sum_le_card {G : CGraph} {x : G.V → ℚ} (hvt : G.IsVertexTransitive)
    (C : Finset G.V) (h : ∀ σ : Equiv.Perm G.V, (∀ u v, G.Adj (σ u) (σ v) = G.Adj u v) →
      ∑ c ∈ C, x (σ c) ≤ 1) :
    (C.card : ℚ) * ∑ v, x v ≤ FinEnum.card G.V := by
  classical
  rcases isEmpty_or_nonempty G.V with hV | hne
  · have hC : C = ∅ := Finset.eq_empty_of_isEmpty C
    simp [hC, Finset.univ_eq_empty]
  obtain ⟨Γ, m, hmpos, hcard, hadj, hfib⟩ := exists_autFinset_of_isVertexTransitive hvt hne
  set N : ℚ := ∑ σ ∈ Γ, ∑ c ∈ C, x (σ c) with hN
  have hupper : N ≤ (FinEnum.card G.V : ℚ) * m := by
    have hone : ∀ σ ∈ Γ, ∑ c ∈ C, x (σ c) ≤ (1 : ℚ) := fun σ hσ ↦ h σ (hadj σ hσ)
    calc N ≤ Γ.card • (1 : ℚ) := Finset.sum_le_card_nsmul _ _ 1 hone
      _ = (Γ.card : ℚ) := by simp
      _ = (FinEnum.card G.V : ℚ) * m := by rw [hcard]; push_cast; ring
  have hlower : N = (C.card : ℚ) * ((m : ℚ) * ∑ v, x v) := by
    have hcol : ∀ c : G.V, ∑ σ ∈ Γ, x (σ c) = (m : ℚ) * ∑ v, x v := by
      intro c
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm G.V ↦ σ c)
        (t := Finset.univ) (fun σ _ ↦ Finset.mem_univ _)]
      have hinner : ∀ v : G.V, ∑ σ ∈ Γ.filter (fun σ ↦ σ c = v), x (σ c) = (m : ℚ) * x v := by
        intro v
        rw [Finset.sum_congr rfl fun σ hσ ↦ by rw [(Finset.mem_filter.1 hσ).2],
          Finset.sum_const, hfib c v, nsmul_eq_mul]
      rw [Finset.sum_congr rfl fun v _ ↦ hinner v, ← Finset.mul_sum]
    rw [hN, Finset.sum_comm, Finset.sum_congr rfl fun c _ ↦ hcol c, Finset.sum_const,
      nsmul_eq_mul]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hmpos
  refine le_of_mul_le_mul_right ?_ hmq
  calc (C.card : ℚ) * (∑ v, x v) * m = N := by rw [hlower]; ring
    _ ≤ (FinEnum.card G.V : ℚ) * m := hupper

/-- **`α_f` of a vertex-transitive graph is at most `n / ω`.**  Average a feasible weighting over
the automorphism group: a maximum clique is carried to a clique by every automorphism, and each
vertex is hit equally often. -/
theorem fracIndepNum_le_card_div_cliqueNum (hvt : G.IsVertexTransitive) (hω : 0 < G.cliqueNum) :
    G.fracIndepNum ≤ (FinEnum.card G.V : ℝ) / G.cliqueNum := by
  classical
  refine fracIndepNum_le fun x hx ↦ ?_
  obtain ⟨C, hC, hCcard⟩ := G.toSimple.exists_isNClique_cliqueNum
  have hC' : G.IsCliqueOn C := fun u hu v hv huv ↦ (toSimple_adj _ _ _).1 (hC hu hv huv)
  have key : (C.card : ℚ) * ∑ v, x v ≤ FinEnum.card G.V := by
    refine card_mul_sum_le_card hvt C fun σ hσ ↦ ?_
    have hsum := hx.sum_le (isCliqueOn_image hσ hC')
    rwa [Finset.sum_image fun a _ b _ hab ↦ σ.injective hab] at hsum
  rw [hCcard] at key
  have hωq : (0 : ℝ) < G.cliqueNum := by exact_mod_cast hω
  rw [le_div_iff₀ hωq]
  have hR : ((G.cliqueNum : ℝ) * ((∑ v, x v : ℚ) : ℝ)) ≤ (FinEnum.card G.V : ℝ) := by
    exact_mod_cast key
  linarith

/-- **`α_f(G) = n / ω(G)` for a vertex-transitive graph.**  The uniform weighting `1 / ω` is
feasible, and by the averaging bound nothing does better. -/
theorem fracIndepNum_eq_card_div_cliqueNum (hvt : G.IsVertexTransitive) (hω : 0 < G.cliqueNum) :
    G.fracIndepNum = (FinEnum.card G.V : ℝ) / G.cliqueNum :=
  le_antisymm (fracIndepNum_le_card_div_cliqueNum G hvt hω) (card_div_le_fracIndepNum G hω le_rfl)

/-- **`χ_f(G) = n / α(G)` for a vertex-transitive graph**, the same statement on the complement,
which is vertex-transitive too. -/
theorem fracChromNum_eq_card_div_indepNum (hvt : G.IsVertexTransitive) (hα : 0 < G.indepNum) :
    G.fracChromNum = (FinEnum.card G.V : ℝ) / G.indepNum := by
  have h := fracIndepNum_eq_card_div_cliqueNum (G := Gᶜ) (isVertexTransitive_compl G hvt)
    (by rwa [cliqueNum_compl])
  rwa [cliqueNum_compl, card_compl, ← fracChromNum_eq_compl] at h

/-- **`χ_f` of a cycle is `n / ⌊n / 2⌋`.**  The cycle is vertex-transitive and its independence
number is `⌊n / 2⌋`. -/
theorem fracChromNum_cycle (n : ℕ) :
    (cycle (n + 3)).fracChromNum = (n + 3 : ℕ) / (((n + 3) / 2 : ℕ) : ℝ) := by
  rw [fracChromNum_eq_card_div_indepNum _ (isVertexTransitive_cycle _)
    (by rw [indepNum_cycle]; omega), indepNum_cycle, card_cycle]

/-- **`χ_f(C_{2k+3}) = (2k+3) / (k+1)`**: the odd cycles, whose fractional chromatic number falls
strictly between the clique number `2` and the chromatic number `3`. -/
theorem fracChromNum_cycle_odd (k : ℕ) :
    (cycle (2 * k + 3)).fracChromNum = (2 * k + 3 : ℝ) / (k + 1) := by
  have h := fracChromNum_cycle (2 * k)
  rw [show (2 * k + 3) / 2 = k + 1 from by omega] at h
  rw [h]
  push_cast
  ring

/-- **`χ_f` of an even cycle is `2`**, as is `χ`. -/
theorem fracChromNum_cycle_even (k : ℕ) : (cycle (2 * k + 4)).fracChromNum = 2 := by
  have h := fracChromNum_cycle (2 * k + 1)
  rw [show 2 * k + 1 + 3 = 2 * k + 4 from by omega,
    show (2 * k + 4) / 2 = k + 2 from by omega] at h
  rw [h]
  have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  rw [div_eq_iff hk]
  ring

/-! ## The two extremes

On the edgeless graph every vertex may take weight one, and on the complete graph the whole
vertex set is a single clique; the complement exchanges the two. -/

/-- **`α_f` of the edgeless graph is the number of vertices**, which is already `α`. -/
@[simp] theorem fracIndepNum_empty (n : ℕ) : (empty n).fracIndepNum = n := by
  refine le_antisymm ?_ ?_
  · simpa using (empty n).fracIndepNum_le_card
  · have h := (empty n).indepNum_le_fracIndepNum
    rwa [indepNum_empty] at h

/-- **`α_f` of the complete graph is one**, or zero when there are no vertices at all. -/
@[simp] theorem fracIndepNum_complete (n : ℕ) : (complete n).fracIndepNum = min n 1 := by
  match n with
  | 0 =>
    have h := (complete 0).fracIndepNum_le_card
    rw [card_complete] at h
    simpa using le_antisymm (by exact_mod_cast h) (complete 0).zero_le_fracIndepNum
  | m + 1 =>
    refine le_antisymm ?_ ?_
    · have h := fracIndepNum_le_of_cliqueColouring (G := complete (m + 1)) (fun _ ↦ (0 : Fin 1))
        (fun u v huv _ ↦ by simpa using huv)
      simpa using h
    · have h := (complete (m + 1)).indepNum_le_fracIndepNum
      rw [indepNum_complete] at h
      simpa using h

@[simp] theorem fracChromNum_complete (n : ℕ) : (complete n).fracChromNum = n := by
  rw [fracChromNum_eq_compl, compl_complete, fracIndepNum_empty]

@[simp] theorem fracChromNum_empty (n : ℕ) : (empty n).fracChromNum = min n 1 := by
  rw [fracChromNum_eq_compl, compl_empty, fracIndepNum_complete]

/-! ## Substructure

One lemma covers every containment: an injection `f : H.V → G.V` that *reflects* adjacency —
every edge of `G` between two vertices of the image is an edge of `H` — cannot lower `α_f`, since
extending a weighting of `H` by zero keeps every clique of `G` light.  Induced subgraphs are the
case where `f` reflects and preserves adjacency, adding edges to a graph is the case `f = id`, and
an isomorphism is the case where `f` is a bijection, so `α_f` and `χ_f` are graph invariants.
Reading the lemma on the complements asks instead for an injection that *preserves* adjacency, and
bounds `χ_f`. -/

/-- **A reflecting injection cannot lower `α_f`.** -/
theorem fracIndepNum_le_of_injective {H G : CGraph} (f : H.V → G.V)
    (hinj : Function.Injective f)
    (hadj : ∀ u v, G.Adj (f u) (f v) = true → H.Adj u v = true) :
    H.fracIndepNum ≤ G.fracIndepNum := by
  classical
  refine fracIndepNum_le fun x hx ↦ ?_
  set z : G.V → ℚ := Function.extend f x 0 with hzdef
  have hzf : ∀ u, z (f u) = x u := fun u ↦ hinj.extend_apply x 0 u
  have hz0 : ∀ w, ¬ (∃ u, f u = w) → z w = 0 := by
    intro w hw
    rw [hzdef, Function.extend_apply' _ _ _ hw]
    rfl
  have hsum : ∀ K : Finset H.V, ∑ w ∈ K.image f, z w = ∑ u ∈ K, x u := by
    intro K
    rw [Finset.sum_image fun a _ b _ h ↦ hinj h]
    exact Finset.sum_congr rfl fun u _ ↦ hzf u
  have hfeas : G.IsFracIndep z := by
    refine ⟨fun w ↦ ?_, fun K hK ↦ ?_⟩
    · by_cases h : ∃ u, f u = w
      · obtain ⟨u, rfl⟩ := h
        rw [hzf]
        exact hx.nonneg u
      · rw [hz0 w h]
    · set K' : Finset H.V := Finset.univ.filter (fun u ↦ f u ∈ K) with hK'def
      have hK' : H.IsCliqueOn K' := by
        intro u hu v hv huv
        rw [hK'def, Finset.mem_filter] at hu hv
        exact hadj u v (hK _ hu.2 _ hv.2 fun h ↦ huv (hinj h))
      have himg : K'.image f ⊆ K := by
        intro w hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
        exact (Finset.mem_filter.1 hu).2
      have hrestrict : ∑ w ∈ K, z w = ∑ w ∈ K'.image f, z w := by
        refine (Finset.sum_subset himg ?_).symm
        intro w hwK hw
        by_cases h : ∃ u, f u = w
        · obtain ⟨u, rfl⟩ := h
          exact absurd (Finset.mem_image.2
            ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hwK⟩, rfl⟩) hw
        · exact hz0 w h
      rw [hrestrict, hsum K']
      exact hx.sum_le hK'
  have htot : ∑ w, z w = ∑ u, x u := by
    rw [← hsum Finset.univ]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro w _ hw
    by_cases h : ∃ u, f u = w
    · obtain ⟨u, rfl⟩ := h
      exact absurd (Finset.mem_image_of_mem f (Finset.mem_univ u)) hw
    · exact hz0 w h
  have := le_fracIndepNum hfeas
  rwa [htot] at this

/-- **A preserving injection cannot lower `χ_f`.** -/
theorem fracChromNum_le_of_injective {H G : CGraph} (f : H.V → G.V)
    (hinj : Function.Injective f)
    (hadj : ∀ u v, H.Adj u v = true → G.Adj (f u) (f v) = true) :
    H.fracChromNum ≤ G.fracChromNum := by
  refine fracIndepNum_le_of_injective (H := Hᶜ) (G := Gᶜ) f hinj fun u v h ↦ ?_
  rw [compl_adj] at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h ⊢
  refine ⟨fun he ↦ h.1 (by rw [he]), ?_⟩
  by_contra hb
  rw [Bool.not_eq_false] at hb
  rw [hadj u v hb] at h
  exact Bool.noConfusion h.2

/-- **`α_f` is an isomorphism invariant.** -/
theorem Iso.fracIndepNum_eq {G H : CGraph} (i : G ≃cg H) : G.fracIndepNum = H.fracIndepNum :=
  le_antisymm
    (fracIndepNum_le_of_injective i (RelIso.injective i) fun u v h ↦ by
      rwa [Iso.adj_eq i u v] at h)
    (fracIndepNum_le_of_injective i.symm (RelIso.injective i.symm) fun u v h ↦ by
      rwa [Iso.adj_eq i.symm u v] at h)

/-- **`χ_f` is an isomorphism invariant.** -/
theorem Iso.fracChromNum_eq {G H : CGraph} (i : G ≃cg H) : G.fracChromNum = H.fracChromNum :=
  Iso.fracIndepNum_eq i.compl

/-! ## Sums and products

`α_f` adds over the disjoint union and maximises over the join; `χ_f` is `α_f` of the complement,
which exchanges those two operations, so it does the opposite.  A clique of a strong product is
exactly a product of cliques, and that makes `α_f` multiplicative there — unlike `α` itself, whose
failure to be multiplicative on `C₅ ⊠ C₅` is the beginning of the Shannon capacity, which `α_f`
therefore bounds from above.  The lexicographic product takes the same value, squeezed between a
product weighting from below and `G ⊠ H ≤ G[H]` from above; on the complement that reads
`χ_f(G[H]) = χ_f(G) · χ_f(H)`.  A clique of a Cartesian product lies in one row or one column, so
`α_f(G □ H)` is caught between `α_f(G) · α_f(H)` and `n(G) · α_f(H)`; the tensor product gets only
the lower bounds. -/

/-- Sums over the vertices of a disjoint union. -/
private theorem sum_univ_disjUnion {G H : CGraph} {M : Type*} [AddCommMonoid M]
    (f : (G ⊕g H).V → M) :
    ∑ w, f w = (∑ u, f (Sum.inl u)) + ∑ v, f (Sum.inr v) :=
  (Finset.sum_univ_inst_eq _ (instFintypeSum G.V H.V) f).trans (Fintype.sum_sum_type f)

/-- Sums over the vertices of a join. -/
private theorem sum_univ_join {G H : CGraph} {M : Type*} [AddCommMonoid M]
    (f : (G ∇g H).V → M) :
    ∑ w, f w = (∑ u, f (Sum.inl u)) + ∑ v, f (Sum.inr v) :=
  (Finset.sum_univ_inst_eq _ (instFintypeSum G.V H.V) f).trans (Fintype.sum_sum_type f)

/-- A product of weightings, summed over the vertices of a lexicographic product. -/
private theorem sum_univ_lexProduct {G H : CGraph} (x : G.V → ℚ) (y : H.V → ℚ) :
    ∑ p : (G ·g H).V, x p.1 * y p.2 = (∑ u, x u) * ∑ v, y v := by
  rw [Finset.sum_mul_sum]
  exact (Finset.sum_univ_inst_eq _ (instFintypeProd G.V H.V) _).trans
    (Fintype.sum_prod_type _)

/-- Sums over the vertices of a Cartesian product, fibre by fibre. -/
private theorem sum_univ_cartesianProduct {G H : CGraph} (z : (G □g H).V → ℚ) :
    ∑ p, z p = ∑ u, ∑ v, z (u, v) :=
  (Finset.sum_univ_inst_eq _ (instFintypeProd G.V H.V) z).trans (Fintype.sum_prod_type z)

/-- Sums over the vertices of a strong product, fibre by fibre. -/
private theorem sum_univ_strongProduct {G H : CGraph} (z : (G ⊠g H).V → ℚ) :
    ∑ p, z p = ∑ u, ∑ v, z (u, v) :=
  (Finset.sum_univ_inst_eq _ (instFintypeProd G.V H.V) z).trans (Fintype.sum_prod_type z)

/-- A weighting that ignores the second coordinate, summed over a tensor product. -/
private theorem sum_univ_tensorProduct {G H : CGraph} (x : G.V → ℚ) :
    ∑ p : (G ⊗g H).V, x p.1 = (FinEnum.card H.V : ℚ) * ∑ u, x u := by
  rw [Finset.mul_sum]
  refine ((Finset.sum_univ_inst_eq _ (instFintypeProd G.V H.V) _).trans
    (Fintype.sum_prod_type _)).trans (Finset.sum_congr rfl fun u _ ↦ ?_)
  show ∑ _v : H.V, x u = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    FinEnum.card_eq_fintypeCard' (α := H.V)]

/-- **Scaling `α_f` by a rational bound.** -/
theorem sum_le_mul_fracIndepNum_rat {G : CGraph} {x : G.V → ℚ} {p : ℚ} (hnn : ∀ v, 0 ≤ x v)
    (hp : ∀ K : Finset G.V, G.IsCliqueOn K → ∑ v ∈ K, x v ≤ p) :
    ((∑ v, x v : ℚ) : ℝ) ≤ (p : ℝ) * G.fracIndepNum := by
  have hdiv : ∀ s : Finset G.V, ∑ v ∈ s, x v / p = (∑ v ∈ s, x v) / p := by
    intro s
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have hp0 : (0 : ℚ) ≤ p := by simpa using hp ∅ isCliqueOn_empty
  rcases eq_or_lt_of_le hp0 with h | h
  · have hx : ∀ v, x v = 0 := by
      intro v
      refine le_antisymm ?_ (hnn v)
      have := hp {v} (isCliqueOn_singleton v)
      simpa [← h] using this
    simp [hx, ← h]
  · have hfeas : G.IsFracIndep (fun v ↦ x v / p) :=
      ⟨fun v ↦ div_nonneg (hnn v) h.le, fun K hK ↦ by
        rw [hdiv, div_le_one h]
        exact hp K hK⟩
    have hle := le_fracIndepNum hfeas
    rw [hdiv] at hle
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast h
    rw [Rat.cast_div, div_le_iff₀ hpR] at hle
    linarith

/-- **Scaling `α_f`.**  If every clique of `G` weighs at most `c`, the whole weighting weighs
at most `c · α_f(G)`.  The bound `c` may be any real number. -/
theorem sum_le_mul_fracIndepNum {G : CGraph} {x : G.V → ℚ} {c : ℝ} (hnn : ∀ v, 0 ≤ x v)
    (hc : ∀ K : Finset G.V, G.IsCliqueOn K → ((∑ v ∈ K, x v : ℚ) : ℝ) ≤ c) :
    ((∑ v, x v : ℚ) : ℝ) ≤ c * G.fracIndepNum := by
  have hq : ∀ p : ℚ, c ≤ (p : ℝ) →
      ((∑ v, x v : ℚ) : ℝ) ≤ (p : ℝ) * G.fracIndepNum := fun p hp ↦
    sum_le_mul_fracIndepNum_rat hnn fun K hK ↦ by
      exact_mod_cast le_trans (hc K hK) hp
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le G.zero_le_fracIndepNum with h0 | h0
  · obtain ⟨p, hp⟩ := exists_rat_gt c
    have h1 := hq p hp.le
    rw [← h0, mul_zero] at h1
    rw [← h0, mul_zero] at hcon
    linarith
  · have hlt : c < ((∑ v, x v : ℚ) : ℝ) / G.fracIndepNum := by
      rw [lt_div_iff₀ h0]
      linarith
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hlt
    rw [lt_div_iff₀ h0] at hp2
    have h1 := hq p hp1.le
    linarith

/-- Two feasible weightings at once, for a bound on `α_f + α_f`. -/
theorem fracIndepNum_add_fracIndepNum_le {G H : CGraph} {c : ℝ}
    (h : ∀ (x : G.V → ℚ) (y : H.V → ℚ), G.IsFracIndep x → H.IsFracIndep y →
      ((∑ u, x u : ℚ) : ℝ) + ((∑ v, y v : ℚ) : ℝ) ≤ c) :
    G.fracIndepNum + H.fracIndepNum ≤ c := by
  have h1 : ∀ y : H.V → ℚ, H.IsFracIndep y →
      G.fracIndepNum ≤ c - ((∑ v, y v : ℚ) : ℝ) := fun y hy ↦
    fracIndepNum_le fun x hx ↦ by linarith [h x y hx hy]
  have h2 : H.fracIndepNum ≤ c - G.fracIndepNum :=
    fracIndepNum_le fun y hy ↦ by linarith [h1 y hy]
  linarith

/-- Two feasible weightings at once, for a bound on `α_f * α_f`. -/
theorem fracIndepNum_mul_fracIndepNum_le {G H : CGraph} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (x : G.V → ℚ) (y : H.V → ℚ), G.IsFracIndep x → H.IsFracIndep y →
      ((∑ u, x u : ℚ) : ℝ) * ((∑ v, y v : ℚ) : ℝ) ≤ c) :
    G.fracIndepNum * H.fracIndepNum ≤ c := by
  rcases eq_or_lt_of_le G.zero_le_fracIndepNum with h0 | h0
  · rw [← h0, zero_mul]
    exact hc
  rw [mul_comm, ← le_div_iff₀ h0]
  refine fracIndepNum_le fun y hy ↦ ?_
  have hy0 : (0 : ℝ) ≤ ((∑ v, y v : ℚ) : ℝ) := by
    exact_mod_cast Finset.sum_nonneg fun v _ ↦ hy.nonneg v
  rcases eq_or_lt_of_le hy0 with hy0' | hy0'
  · rw [← hy0']
    exact div_nonneg hc h0.le
  rw [le_div_iff₀ h0, mul_comm, ← le_div_iff₀ hy0']
  refine fracIndepNum_le fun x hx ↦ ?_
  rw [le_div_iff₀ hy0']
  exact h x y hx hy

/-- **`α_f` adds over the disjoint union.** -/
@[simp] theorem fracIndepNum_disjUnion (G H : CGraph) :
    (G ⊕g H).fracIndepNum = G.fracIndepNum + H.fracIndepNum := by
  refine le_antisymm (fracIndepNum_le fun z hz ↦ ?_) ?_
  · have hG : G.IsFracIndep (fun u ↦ z (Sum.inl u)) := by
      refine ⟨fun u ↦ hz.nonneg _, fun K hK ↦ ?_⟩
      have hcl : (G ⊕g H).IsCliqueOn (K.map ⟨Sum.inl, Sum.inl_injective⟩) := by
        intro a ha b hb hab
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hb
        exact hK u hu v hv fun h ↦ hab (by rw [h])
      have hs := hz.sum_le hcl
      rwa [Finset.sum_map] at hs
    have hH : H.IsFracIndep (fun v ↦ z (Sum.inr v)) := by
      refine ⟨fun v ↦ hz.nonneg _, fun K hK ↦ ?_⟩
      have hcl : (G ⊕g H).IsCliqueOn (K.map ⟨Sum.inr, Sum.inr_injective⟩) := by
        intro a ha b hb hab
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hb
        exact hK u hu v hv fun h ↦ hab (by rw [h])
      have hs := hz.sum_le hcl
      rwa [Finset.sum_map] at hs
    rw [sum_univ_disjUnion z, Rat.cast_add]
    exact add_le_add (le_fracIndepNum hG) (le_fracIndepNum hH)
  · refine fracIndepNum_add_fracIndepNum_le fun x y hx hy ↦ ?_
    have hfeas : (G ⊕g H).IsFracIndep (Sum.elim x y) := by
      refine ⟨fun w ↦ ?_, fun K hK ↦ ?_⟩
      · cases w with
        | inl u => exact hx.nonneg u
        | inr v => exact hy.nonneg v
      · have hleft : G.IsCliqueOn K.toLeft := by
          intro u hu v hv huv
          rw [Finset.mem_toLeft] at hu hv
          exact hK _ hu _ hv fun h ↦ huv (Sum.inl.inj h)
        have hright : H.IsCliqueOn K.toRight := by
          intro u hu v hv huv
          rw [Finset.mem_toRight] at hu hv
          exact hK _ hu _ hv fun h ↦ huv (Sum.inr.inj h)
        have hone : K.toLeft = ∅ ∨ K.toRight = ∅ := by
          by_contra hcon
          push Not at hcon
          obtain ⟨u, hu⟩ := hcon.1
          obtain ⟨v, hv⟩ := hcon.2
          rw [Finset.mem_toLeft] at hu
          rw [Finset.mem_toRight] at hv
          have hadj := hK _ hu _ hv (by simp)
          rw [disjUnion_adj_inl_inr] at hadj
          exact Bool.noConfusion hadj
        have hsplit : ∑ w ∈ K, Sum.elim x y w
            = (∑ a ∈ K.toLeft, x a) + ∑ b ∈ K.toRight, y b :=
          Finset.sum_sum_eq_sum_toLeft_add_sum_toRight K _
        rw [hsplit]
        rcases hone with hemp | hemp
        · rw [hemp, Finset.sum_empty, zero_add]
          exact hy.sum_le hright
        · rw [hemp, Finset.sum_empty, add_zero]
          exact hx.sum_le hleft
    have hle := le_fracIndepNum hfeas
    rw [sum_univ_disjUnion (Sum.elim x y), Rat.cast_add] at hle
    exact hle

/-- **`α_f` of a join is the larger of the two.**  Weight `p` of a clique of `G` and weight `q`
of one of `H` join to a clique of `G ∇ H`, so `p + q ≤ 1`, and the two sides scale by `p` and
`q`. -/
@[simp] theorem fracIndepNum_join (G H : CGraph) :
    (G ∇g H).fracIndepNum = max G.fracIndepNum H.fracIndepNum := by
  refine le_antisymm (fracIndepNum_le fun z hz ↦ ?_) (max_le ?_ ?_)
  · obtain ⟨KG, hKG, hKGmax⟩ := Finset.exists_max_image
      (Finset.univ.filter fun K : Finset G.V ↦ G.IsCliqueOn K)
      (fun K ↦ ∑ u ∈ K, z (Sum.inl u)) ⟨∅, by simp⟩
    obtain ⟨KH, hKH, hKHmax⟩ := Finset.exists_max_image
      (Finset.univ.filter fun K : Finset H.V ↦ H.IsCliqueOn K)
      (fun K ↦ ∑ v ∈ K, z (Sum.inr v)) ⟨∅, by simp⟩
    rw [Finset.mem_filter] at hKG hKH
    set p : ℚ := ∑ u ∈ KG, z (Sum.inl u) with hpdef
    set q : ℚ := ∑ v ∈ KH, z (Sum.inr v) with hqdef
    have hpmax : ∀ K : Finset G.V, G.IsCliqueOn K → ∑ u ∈ K, z (Sum.inl u) ≤ p :=
      fun K hKc ↦ hKGmax K (Finset.mem_filter.2 ⟨Finset.mem_univ K, hKc⟩)
    have hqmax : ∀ K : Finset H.V, H.IsCliqueOn K → ∑ v ∈ K, z (Sum.inr v) ≤ q :=
      fun K hKc ↦ hKHmax K (Finset.mem_filter.2 ⟨Finset.mem_univ K, hKc⟩)
    have hpq : p + q ≤ 1 := by
      have hcl : (G ∇g H).IsCliqueOn (KG.disjSum KH) := by
        intro a ha b hb hab
        obtain ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ := Finset.mem_disjSum.1 ha <;>
          obtain ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ := Finset.mem_disjSum.1 hb
        · rw [join_adj_inl_inl]
          exact hKG.2 u hu v hv fun h ↦ hab (by rw [h])
        · exact join_adj_inl_inr G H u v
        · exact join_adj_inr_inl G H u v
        · rw [join_adj_inr_inr]
          exact hKH.2 u hu v hv fun h ↦ hab (by rw [h])
      have hsplit : ∑ w ∈ KG.disjSum KH, z w
          = (∑ u ∈ KG, z (Sum.inl u)) + ∑ v ∈ KH, z (Sum.inr v) :=
        Finset.sum_disjSum KG KH z
      calc p + q = ∑ w ∈ KG.disjSum KH, z w := hsplit.symm
        _ ≤ 1 := hz.sum_le hcl
    have hp0 : (0 : ℚ) ≤ p := by simpa using hpmax ∅ isCliqueOn_empty
    have hq0 : (0 : ℚ) ≤ q := by simpa using hqmax ∅ isCliqueOn_empty
    have hGa : ((∑ u, z (Sum.inl u) : ℚ) : ℝ) ≤ (p : ℝ) * G.fracIndepNum :=
      sum_le_mul_fracIndepNum_rat (fun u ↦ hz.nonneg _) hpmax
    have hHa : ((∑ v, z (Sum.inr v) : ℚ) : ℝ) ≤ (q : ℝ) * H.fracIndepNum :=
      sum_le_mul_fracIndepNum_rat (fun v ↦ hz.nonneg _) hqmax
    have hpqR : (p : ℝ) + (q : ℝ) ≤ 1 := by exact_mod_cast hpq
    have hp0R : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    have hGM : G.fracIndepNum ≤ max G.fracIndepNum H.fracIndepNum := le_max_left _ _
    have hHM : H.fracIndepNum ≤ max G.fracIndepNum H.fracIndepNum := le_max_right _ _
    have hM0 : (0 : ℝ) ≤ max G.fracIndepNum H.fracIndepNum :=
      le_trans G.zero_le_fracIndepNum hGM
    rw [sum_univ_join z, Rat.cast_add]
    nlinarith [mul_le_mul_of_nonneg_left hGM hp0R, mul_le_mul_of_nonneg_left hHM hq0R]
  · exact fracIndepNum_le_of_injective Sum.inl Sum.inl_injective fun u v h ↦ by
      rwa [join_adj_inl_inl] at h
  · exact fracIndepNum_le_of_injective Sum.inr Sum.inr_injective fun u v h ↦ by
      rwa [join_adj_inr_inr] at h

/-- **`χ_f` adds over the join.** -/
@[simp] theorem fracChromNum_join (G H : CGraph) :
    (G ∇g H).fracChromNum = G.fracChromNum + H.fracChromNum := by
  rw [fracChromNum_eq_compl, compl_join, fracIndepNum_disjUnion]
  rfl

/-- **`χ_f` of a disjoint union is the larger of the two.** -/
@[simp] theorem fracChromNum_disjUnion (G H : CGraph) :
    (G ⊕g H).fracChromNum = max G.fracChromNum H.fracChromNum := by
  rw [fracChromNum_eq_compl, compl_disjUnion, fracIndepNum_join]
  rfl

/-- **A product of feasible weightings is feasible in the lexicographic product.** -/
theorem fracIndepNum_mul_fracIndepNum_le_fracIndepNum_lexProduct (G H : CGraph) :
    G.fracIndepNum * H.fracIndepNum ≤ (G ·g H).fracIndepNum := by
  classical
  refine fracIndepNum_mul_fracIndepNum_le (G ·g H).zero_le_fracIndepNum fun x y hx hy ↦ ?_
  have hfeas : (G ·g H).IsFracIndep (fun p ↦ x p.1 * y p.2) := by
    refine ⟨fun p ↦ mul_nonneg (hx.nonneg _) (hy.nonneg _), fun K hK ↦ ?_⟩
    have hfst : G.IsCliqueOn (K.image Prod.fst) := by
      intro a ha b hb hab
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
      have hpq : p ≠ q := fun h ↦ hab (by rw [h])
      have hadj := hK p hp q hq hpq
      rw [lexProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with h | ⟨h, -⟩
      · exact h
      · exact absurd h hab
    have hfib : ∀ a : G.V,
        H.IsCliqueOn ((K.filter fun p ↦ p.1 = a).image Prod.snd) := by
      intro a c hc d hd hcd
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hd
      rw [Finset.mem_filter] at hp hq
      have hpq : p ≠ q := fun h ↦ hcd (by rw [h])
      have hadj := hK p hp.1 q hq.1 hpq
      rw [lexProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with h | ⟨-, h⟩
      · rw [hp.2, hq.2, adj_self] at h
        exact Bool.noConfusion h
      · exact h
    calc ∑ p ∈ K, x p.1 * y p.2
        = ∑ a ∈ K.image Prod.fst, ∑ p ∈ K.filter fun p ↦ p.1 = a, x p.1 * y p.2 :=
          (Finset.sum_fiberwise_of_maps_to (fun p hp ↦ Finset.mem_image_of_mem _ hp) _).symm
      _ ≤ ∑ a ∈ K.image Prod.fst, x a := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          have hcast : ∑ p ∈ K.filter fun p ↦ p.1 = a, x p.1 * y p.2
              = x a * ∑ p ∈ K.filter fun p ↦ p.1 = a, y p.2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p hp ↦ ?_
            rw [(Finset.mem_filter.1 hp).2]
          have himg : ∑ v ∈ (K.filter fun p ↦ p.1 = a).image Prod.snd, y v
              = ∑ p ∈ K.filter fun p ↦ p.1 = a, y p.2 := by
            refine Finset.sum_image fun p hp q hq h ↦ ?_
            simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
            exact Prod.ext (hp.2.trans hq.2.symm) h
          rw [hcast, ← himg]
          calc x a * ∑ v ∈ (K.filter fun p ↦ p.1 = a).image Prod.snd, y v
              ≤ x a * 1 :=
                mul_le_mul_of_nonneg_left (hy.sum_le (hfib a)) (hx.nonneg a)
            _ = x a := mul_one _
      _ ≤ 1 := hx.sum_le hfst
  have hle := le_fracIndepNum hfeas
  rw [sum_univ_lexProduct x y, Rat.cast_mul] at hle
  exact hle

/-- The strong product is a subgraph of the lexicographic one. -/
theorem fracIndepNum_lexProduct_le_fracIndepNum_strongProduct (G H : CGraph) :
    (G ·g H).fracIndepNum ≤ (G ⊠g H).fracIndepNum :=
  fracIndepNum_le_of_injective (H := G ·g H) (G := G ⊠g H) id Function.injective_id
    fun _ _ h ↦ (toSimple_adj _ _ _).1 (strongProduct_le_lexProduct G H
      ((toSimple_adj _ _ _).2 h))

/-- The product weighting is feasible in the strong product too. -/
theorem fracIndepNum_mul_fracIndepNum_le_fracIndepNum_strongProduct (G H : CGraph) :
    G.fracIndepNum * H.fracIndepNum ≤ (G ⊠g H).fracIndepNum :=
  le_trans (fracIndepNum_mul_fracIndepNum_le_fracIndepNum_lexProduct G H)
    (fracIndepNum_lexProduct_le_fracIndepNum_strongProduct G H)

/-- **`α_f` is multiplicative on the strong product.**  Unlike `α` itself: a weighting of
`G ⊠ H` restricted to `K × V(H)`, for a clique `K` of `G`, is feasible for `H`. -/
@[simp] theorem fracIndepNum_strongProduct (G H : CGraph) :
    (G ⊠g H).fracIndepNum = G.fracIndepNum * H.fracIndepNum := by
  refine le_antisymm (fracIndepNum_le fun z hz ↦ ?_)
    (fracIndepNum_mul_fracIndepNum_le_fracIndepNum_strongProduct G H)
  have hxnn : ∀ u : G.V, (0 : ℚ) ≤ ∑ v, z (u, v) :=
    fun u ↦ Finset.sum_nonneg fun v _ ↦ hz.nonneg _
  have hrow : ∀ K : Finset G.V, G.IsCliqueOn K →
      ((∑ u ∈ K, ∑ v, z (u, v) : ℚ) : ℝ) ≤ H.fracIndepNum := by
    intro K hKc
    have hw : H.IsFracIndep fun v ↦ ∑ u ∈ K, z (u, v) := by
      refine ⟨fun v ↦ Finset.sum_nonneg fun u _ ↦ hz.nonneg _, fun L hL ↦ ?_⟩
      have hcl : (G ⊠g H).IsCliqueOn (K ×ˢ L) := by
        intro a ha b hb hab
        obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
        obtain ⟨hb1, hb2⟩ := Finset.mem_product.1 hb
        rw [strongProduct_adj]
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
        refine ⟨hab, ?_, ?_⟩
        · rcases eq_or_ne a.1 b.1 with h | h
          · exact Or.inl h
          · exact Or.inr (hKc _ ha1 _ hb1 h)
        · rcases eq_or_ne a.2 b.2 with h | h
          · exact Or.inl h
          · exact Or.inr (hL _ ha2 _ hb2 h)
      calc ∑ v ∈ L, ∑ u ∈ K, z (u, v)
          = ∑ u ∈ K, ∑ v ∈ L, z (u, v) := Finset.sum_comm
        _ = ∑ w ∈ K ×ˢ L, z w := (Finset.sum_product K L z).symm
        _ ≤ 1 := hz.sum_le hcl
    have hle := le_fracIndepNum hw
    rwa [Finset.sum_comm] at hle
  have hmain := sum_le_mul_fracIndepNum hxnn hrow
  rw [sum_univ_strongProduct z, mul_comm]
  exact hmain

/-- **`α_f` is multiplicative on the lexicographic product.** -/
@[simp] theorem fracIndepNum_lexProduct (G H : CGraph) :
    (G ·g H).fracIndepNum = G.fracIndepNum * H.fracIndepNum :=
  le_antisymm
    ((fracIndepNum_lexProduct_le_fracIndepNum_strongProduct G H).trans
      (fracIndepNum_strongProduct G H).le)
    (fracIndepNum_mul_fracIndepNum_le_fracIndepNum_lexProduct G H)

/-- The Cartesian product has even fewer edges than the strong product. -/
theorem fracIndepNum_mul_fracIndepNum_le_fracIndepNum_cartesianProduct (G H : CGraph) :
    G.fracIndepNum * H.fracIndepNum ≤ (G □g H).fracIndepNum :=
  le_trans (fracIndepNum_mul_fracIndepNum_le_fracIndepNum_strongProduct G H)
    (fracIndepNum_le_of_injective (H := G ⊠g H) (G := G □g H) id Function.injective_id
      fun _ _ h ↦ (toSimple_adj _ _ _).1 (cartesianProduct_le_strongProduct G H
        ((toSimple_adj _ _ _).2 h)))

/-- **The rows of a Cartesian product bound it above.**  Every clique of `G □ H` lies in a single
row or a single column, so a feasible weighting restricted to one row `{u} × V(H)` is feasible for
`H`, and there are `n(G)` rows. -/
theorem fracIndepNum_cartesianProduct_le_card_mul (G H : CGraph) :
    (G □g H).fracIndepNum ≤ (FinEnum.card G.V : ℝ) * H.fracIndepNum := by
  refine fracIndepNum_le fun z hz ↦ ?_
  have hrow : ∀ u : G.V, ((∑ v, z (u, v) : ℚ) : ℝ) ≤ H.fracIndepNum := by
    intro u
    refine le_fracIndepNum ⟨fun v ↦ hz.nonneg _, fun L hL ↦ ?_⟩
    have hcl : (G □g H).IsCliqueOn (({u} : Finset G.V) ×ˢ L) := by
      intro a ha b hb hab
      obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
      obtain ⟨hb1, hb2⟩ := Finset.mem_product.1 hb
      rw [Finset.mem_singleton] at ha1 hb1
      have h1 : a.1 = b.1 := ha1.trans hb1.symm
      have h2 : a.2 ≠ b.2 := fun h ↦ hab (Prod.ext h1 h)
      rw [cartesianProduct_adj]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨h1, hL _ ha2 _ hb2 h2⟩
    calc ∑ v ∈ L, z (u, v)
        = ∑ w ∈ ({u} : Finset G.V) ×ˢ L, z w :=
          ((Finset.sum_product ({u} : Finset G.V) L z).trans (Finset.sum_singleton _ _)).symm
      _ ≤ 1 := hz.sum_le hcl
  have hcast : ((∑ p, z p : ℚ) : ℝ) = ∑ u, ((∑ v, z (u, v) : ℚ) : ℝ) := by
    rw [sum_univ_cartesianProduct z]
    push_cast
    rfl
  rw [hcast]
  refine (Finset.sum_le_sum fun u _ ↦ hrow u).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    FinEnum.card_eq_fintypeCard' (α := G.V)]

/-- The same bound read along the columns. -/
theorem fracIndepNum_cartesianProduct_le_mul_card (G H : CGraph) :
    (G □g H).fracIndepNum ≤ G.fracIndepNum * (FinEnum.card H.V : ℝ) := by
  rw [Iso.fracIndepNum_eq (Iso.cartesianProductComm G H), mul_comm]
  exact fracIndepNum_cartesianProduct_le_card_mul H G

/-- **A weighting of `G` lifted to `G ⊗ H` ignoring the second coordinate is feasible**, since a
clique of a tensor product meets every fibre once. -/
theorem fracIndepNum_mul_card_le_fracIndepNum_tensorProduct (G H : CGraph) :
    G.fracIndepNum * FinEnum.card H.V ≤ (G ⊗g H).fracIndepNum := by
  classical
  rcases Nat.eq_zero_or_pos (FinEnum.card H.V) with h0 | h0
  · rw [h0]
    simpa using (G ⊗g H).zero_le_fracIndepNum
  have hn : (0 : ℝ) < (FinEnum.card H.V : ℝ) := by exact_mod_cast h0
  rw [← le_div_iff₀ hn]
  refine fracIndepNum_le fun x hx ↦ ?_
  rw [le_div_iff₀ hn]
  have hfeas : (G ⊗g H).IsFracIndep (fun p ↦ x p.1) := by
    refine ⟨fun p ↦ hx.nonneg _, fun K hK ↦ ?_⟩
    have hinj : ∀ p ∈ K, ∀ q ∈ K, p.1 = q.1 → p = q := by
      intro p hp q hq h
      by_contra hne
      have hadj := hK p hp q hq hne
      rw [tensorProduct_adj, Bool.and_eq_true] at hadj
      rw [h, adj_self] at hadj
      exact Bool.noConfusion hadj.1
    have hfst : G.IsCliqueOn (K.image Prod.fst) := by
      intro a ha b hb hab
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
      have hpq : p ≠ q := fun h ↦ hab (by rw [h])
      have hadj := hK p hp q hq hpq
      rw [tensorProduct_adj, Bool.and_eq_true] at hadj
      exact hadj.1
    have himg : ∑ a ∈ K.image Prod.fst, x a = ∑ p ∈ K, x p.1 := Finset.sum_image hinj
    rw [← himg]
    exact hx.sum_le hfst
  have hle := le_fracIndepNum hfeas
  rw [sum_univ_tensorProduct x, Rat.cast_mul, Rat.cast_natCast] at hle
  linarith

/-- The same bound on the other side of the tensor product. -/
theorem card_mul_fracIndepNum_le_fracIndepNum_tensorProduct (G H : CGraph) :
    (FinEnum.card G.V : ℝ) * H.fracIndepNum ≤ (G ⊗g H).fracIndepNum := by
  rw [Iso.fracIndepNum_eq (Iso.tensorProductComm G H), mul_comm]
  exact fracIndepNum_mul_card_le_fracIndepNum_tensorProduct H G

/-- **`α_f` bounds the independence number of every strong power**, so it bounds the Shannon
capacity of `G` from above. -/
theorem indepNum_strongProduct_le_mul_fracIndepNum (G H : CGraph) :
    ((G ⊠g H).indepNum : ℝ) ≤ G.fracIndepNum * H.fracIndepNum :=
  le_trans (indepNum_le_fracIndepNum _) (fracIndepNum_strongProduct G H).le

/-- **`χ_f` is multiplicative on the lexicographic product**, because the complement of
`G[H]` is `Gᶜ[Hᶜ]`. -/
@[simp] theorem fracChromNum_lexProduct (G H : CGraph) :
    (G ·g H).fracChromNum = G.fracChromNum * H.fracChromNum := by
  simp only [fracChromNum_eq_compl]
  rw [Iso.fracIndepNum_eq (Iso.complLexProduct G H)]
  exact fracIndepNum_lexProduct Gᶜ Hᶜ

/-! ## The covering program

The program dual to `α_f`: weights on the cliques rather than on the vertices, covering every
vertex instead of packing every clique.  Strong duality would make it equal to `α_f`; that is
proved below for the vertex-transitive graphs, and only weak duality in general. -/

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
`CGraph.fracIndepNum_le_fracCliqueCoverNum` is the easy half, and
`CGraph.fracIndepNum_eq_fracCliqueCoverNum` the other half for a vertex-transitive graph. -/
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

/-- **A partition of the vertices into cliques is a fractional clique cover**, so `θ_f(G) ≤ k`
for a colouring in `k` colours whose classes are cliques.  The counterpart of
`CGraph.fracIndepNum_le_of_cliqueColouring` on the covering side. -/
theorem fracCliqueCoverNum_le_of_cliqueColouring {k : ℕ} (c : G.V → Fin k)
    (hc : ∀ u v : G.V, u ≠ v → c u = c v → G.Adj u v = true) : G.fracCliqueCoverNum ≤ k := by
  classical
  set F : Fin k → Finset G.V := fun i ↦ Finset.univ.filter fun v ↦ c v = i with hF
  set S : Finset (Finset G.V) := Finset.univ.image F with hS
  have hcover : G.IsFracCliqueCover (fun K ↦ if K ∈ S then 1 else 0) := by
    refine ⟨fun K ↦ by dsimp only; split_ifs <;> norm_num, fun K hK ↦ ?_, fun v ↦ ?_⟩
    · have hKS : K ∈ S := by
        by_contra h
        exact hK (by simp [h])
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hKS
      intro u hu w hw huw
      simp only [hF, Finset.mem_filter] at hu hw
      exact hc u w huw (hu.2.trans hw.2.symm)
    · have hmem : F (c v) ∈ S := Finset.mem_image_of_mem F (Finset.mem_univ _)
      have hvF : v ∈ F (c v) := by simp [hF]
      have hnn : ∀ K ∈ (Finset.univ : Finset (Finset G.V)),
          0 ≤ (if v ∈ K then (if K ∈ S then (1 : ℚ) else 0) else 0) := by
        intro K _
        split_ifs <;> norm_num
      refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ (F (c v))))
      simp [hvF, hmem]
  have htot : (∑ K, (if K ∈ S then (1 : ℚ) else 0)) = (S.card : ℚ) := by
    rw [Finset.sum_boole]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hval : ((S.card : ℚ) : ℝ) ∈ G.fracCliqueCoverVals := ⟨_, hcover, by rw [htot]⟩
  refine le_trans (csInf_le G.fracCliqueCoverVals_bddBelow hval) ?_
  have hcard : S.card ≤ k := by
    calc S.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  exact_mod_cast hcard

/-- **`θ_f ≤ θ`**: a cover of the vertices by `θ(G)` cliques weighs `θ(G)`.  With weak duality
this sharpens `CGraph.fracIndepNum_le_cliqueCoverNum`. -/
theorem fracCliqueCoverNum_le_cliqueCoverNum : G.fracCliqueCoverNum ≤ G.cliqueCoverNum := by
  obtain ⟨c⟩ := colorable_chromNum (G := Gᶜ)
  refine fracCliqueCoverNum_le_of_cliqueColouring G (k := Gᶜ.chromNum) (fun v ↦ c v) ?_
  intro u v huv hcuv
  by_contra hadj
  refine c.valid ?_ hcuv
  rw [toSimple_adj, compl_adj]
  simp [huv, Bool.eq_false_iff.2 hadj]

/-! ### The covering program on a vertex-transitive graph

Strong duality is not proved in general, but it holds on a vertex-transitive graph for a reason
that is elementary: spread a maximum clique over its orbit and the resulting cover has total
weight `n / ω`, which is the value of the packing program.  Both are then optimal. -/

/-- **A vertex-transitive graph has a fractional clique cover of weight `n / ω`.**  Give each
automorphic image `σ C` of a maximum clique the weight `1 / (ω · |Aut G| / |V|)`; every vertex
of `σ C` is covered by exactly `|Aut G| · ω / |V|` of them, and the total weight is `n / ω`. -/
theorem fracCliqueCoverNum_le_card_div_cliqueNum (G : CGraph) (hvt : G.IsVertexTransitive)
    (hω : 0 < G.cliqueNum) :
    G.fracCliqueCoverNum ≤ (FinEnum.card G.V : ℝ) / G.cliqueNum := by
  classical
  obtain ⟨C, hC, hCcard⟩ := G.toSimple.exists_isNClique_cliqueNum
  have hC' : G.IsCliqueOn C := fun u hu v hv huv ↦ (toSimple_adj _ _ _).1 (hC hu hv huv)
  have hne : Nonempty G.V := by
    rcases Finset.eq_empty_or_nonempty C with rfl | ⟨c, hc⟩
    · exfalso
      rw [Finset.card_empty, show G.toSimple.cliqueNum = G.cliqueNum from rfl] at hCcard
      omega
    · exact ⟨c⟩
  obtain ⟨Γ, m, hmpos, hcard, hadj, hfib⟩ := exists_autFinset_of_isVertexTransitive hvt hne
  have hdpos : 0 < m * G.cliqueNum := Nat.mul_pos hmpos hω
  have hdq : (0 : ℚ) < ((m * G.cliqueNum : ℕ) : ℚ) := by exact_mod_cast hdpos
  set y : Finset G.V → ℚ := fun K ↦
    (((Γ.filter fun σ : Equiv.Perm G.V ↦ C.image σ = K).card : ℚ)) /
      ((m * G.cliqueNum : ℕ) : ℚ) with hy
  -- the fibres of `σ ↦ σ C`, summed over the finsets of vertices
  have hfibre : ∀ (p : Finset G.V → Prop) (_ : DecidablePred p),
      ∑ K : Finset G.V,
          (if p K then (Γ.filter fun σ : Equiv.Perm G.V ↦ C.image σ = K).card else 0)
        = (Γ.filter fun σ : Equiv.Perm G.V ↦ p (C.image σ)).card := by
    intro p _
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm G.V ↦ C.image σ)
      (s := Γ.filter fun σ : Equiv.Perm G.V ↦ p (C.image σ)) (t := Finset.univ)
      (fun σ _ ↦ by simp)]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    by_cases hp : p K
    · rw [if_pos hp, Finset.filter_filter]
      congr 1
      exact (Finset.filter_congr fun σ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hp, h⟩⟩).symm
    · rw [if_neg hp, Finset.filter_filter, eq_comm, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      rintro σ _ ⟨h1, h2⟩
      exact hp (h2 ▸ h1)
  have hcover : G.IsFracCliqueCover y := by
    refine ⟨fun K ↦ by positivity, fun K hK ↦ ?_, fun v ↦ ?_⟩
    · have hpos : (Γ.filter fun σ : Equiv.Perm G.V ↦ C.image σ = K).Nonempty := by
        rw [← Finset.card_pos]
        by_contra h
        have h0 : (Γ.filter fun σ : Equiv.Perm G.V ↦ C.image σ = K).card = 0 := by omega
        exact hK (by rw [hy]; simp [h0])
      obtain ⟨σ, hσ⟩ := hpos
      rw [Finset.mem_filter] at hσ
      exact hσ.2 ▸ isCliqueOn_image (hadj σ hσ.1) hC'
    · -- every vertex is covered to weight exactly one
      have h1 : ∑ K : Finset G.V, (if v ∈ K then y K else 0)
          = (((Γ.filter fun σ : Equiv.Perm G.V ↦ v ∈ C.image σ).card : ℕ) : ℚ) /
            ((m * G.cliqueNum : ℕ) : ℚ) := by
        rw [← hfibre (fun K ↦ v ∈ K) _, ← sum_natCast_div]
        refine Finset.sum_congr rfl fun K _ ↦ ?_
        by_cases hv : v ∈ K <;> simp [hy, hv]
      have h2 : (Γ.filter fun σ : Equiv.Perm G.V ↦ v ∈ C.image σ).card = C.card * m := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm G.V ↦ σ.symm v)
          (s := Γ.filter fun σ : Equiv.Perm G.V ↦ v ∈ C.image σ) (t := C) ?_]
        · rw [Finset.sum_congr rfl (g := fun _ ↦ m) ?_, Finset.sum_const, smul_eq_mul]
          intro c hc
          rw [Finset.filter_filter, ← hfib c v]
          congr 1
          refine Finset.filter_congr fun σ _ ↦ ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
          · rw [← h.2]; simp
          · exact Finset.mem_image.2 ⟨c, hc, h⟩
          · rw [← h]; simp
        · intro σ hσ
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hσ
          obtain ⟨c, hc, hcv⟩ := Finset.mem_image.1 hσ.2
          have hsymm : σ.symm v = c := by rw [← hcv]; simp
          simpa [hsymm] using hc
      rw [h1, h2, hCcard, le_div_iff₀ hdq, one_mul]
      push_cast
      ring_nf
      exact le_refl _
  refine csInf_le G.fracCliqueCoverVals_bddBelow ⟨y, hcover, ?_⟩
  have htot : (∑ K, y K : ℚ) = (FinEnum.card G.V : ℚ) / G.cliqueNum := by
    rw [hy]
    rw [show (∑ K : Finset G.V,
        (((Γ.filter fun σ : Equiv.Perm G.V ↦ C.image σ = K).card : ℚ)) /
          ((m * G.cliqueNum : ℕ) : ℚ))
      = ∑ K : Finset G.V,
        (((if True then (Γ.filter fun σ : Equiv.Perm G.V ↦ C.image σ = K).card
          else 0 : ℕ) : ℚ)) / ((m * G.cliqueNum : ℕ) : ℚ) from by simp]
    rw [sum_natCast_div, hfibre (fun _ ↦ True) _]
    simp only [Finset.filter_true_of_mem fun _ _ ↦ trivial]
    rw [hcard]
    have hωq : (0 : ℚ) < (G.cliqueNum : ℚ) := by exact_mod_cast hω
    push_cast
    rw [div_eq_div_iff (by positivity) hωq.ne']
    ring
  rw [htot]
  push_cast
  rfl

/-- **`θ_f(G) = n / ω(G)` for a vertex-transitive graph.** -/
theorem fracCliqueCoverNum_eq_card_div_cliqueNum (G : CGraph) (hvt : G.IsVertexTransitive)
    (hω : 0 < G.cliqueNum) : G.fracCliqueCoverNum = (FinEnum.card G.V : ℝ) / G.cliqueNum :=
  le_antisymm (fracCliqueCoverNum_le_card_div_cliqueNum G hvt hω)
    ((fracIndepNum_eq_card_div_cliqueNum G hvt hω) ▸ G.fracIndepNum_le_fracCliqueCoverNum)

/-- **Strong duality on a vertex-transitive graph**: the packing program and the covering
program have the same value, both equal to `n / ω`.  In general only `α_f ≤ θ_f` is proved. -/
theorem fracIndepNum_eq_fracCliqueCoverNum (G : CGraph) (hvt : G.IsVertexTransitive)
    (hω : 0 < G.cliqueNum) : G.fracIndepNum = G.fracCliqueCoverNum := by
  rw [fracIndepNum_eq_card_div_cliqueNum G hvt hω,
    fracCliqueCoverNum_eq_card_div_cliqueNum G hvt hω]

/-- **`χ_f` is the covering program on the complement, for a vertex-transitive graph**: the
fractional chromatic number defined by packing the independent sets — which is what
`CGraph.fracChromNum` is — agrees with the one defined by covering the vertices with them. -/
theorem fracChromNum_eq_fracCliqueCoverNum_compl (G : CGraph) (hvt : G.IsVertexTransitive)
    (hα : 0 < G.indepNum) : G.fracChromNum = Gᶜ.fracCliqueCoverNum :=
  fracIndepNum_eq_fracCliqueCoverNum Gᶜ (isVertexTransitive_compl G hvt) (by rwa [cliqueNum_compl])

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
