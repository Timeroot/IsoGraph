import IsoGraph.Containment.Defs

/-!
# Interchangeable vertices, and the symmetry they cost a search

A search for a copy of `H` inside `G` — as an induced subgraph, as a minor — asks where each
vertex of `H` goes.  When two vertices of `H` are *interchangeable*, swapping them is an
automorphism of `H`, so every solution comes with a partner that the search will find separately
and reject separately.  A class of `k` interchangeable vertices multiplies the work by `k!`, and
for a pattern like `empty k` — no edges, every vertex interchangeable with every other — that
factor is the whole problem.

`CGraph.symPairs H hs` returns the pairs of vertices a search may keep in a fixed order: the
consecutive members of each class.  A search that requires the images of those pairs to come in
increasing order of some `rank` still finds a solution whenever there is one, because of
`CGraph.exists_sort_perm` and `CGraph.adj_perm`: any solution can be composed with the permutation
that sorts a class, and the result is still a solution.

The classes themselves are found by a heuristic — `CGraph.twinsOf` collects the vertices with the
same neighbours as a given one — and then *checked*, by `CGraph.classOk` and `CGraph.disjOk`.
Nothing downstream reasons about how the classes were found: if the check fails, `symPairs` is
empty and nothing is constrained.  That keeps the completeness proof independent of the heuristic,
which is the same discipline the rest of the search follows.
-/

set_option autoImplicit false

namespace CGraph

variable {H : CGraph}

/-- Consecutive pairs of a list. -/
def consecPairs {α : Type} : List α → List (α × α)
  | x :: y :: T => (x, y) :: consecPairs (y :: T)
  | _ => []

theorem consecPairs_of_isChain {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, List.IsChain R l → ∀ p ∈ consecPairs l, R p.1 p.2
  | [], _, p, hp => by simp [consecPairs] at hp
  | [_], _, p, hp => by simp [consecPairs] at hp
  | x :: y :: T, h, p, hp => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact consecPairs_of_isChain h.2 p hp

theorem consecPairs_ne {α : Type} :
    ∀ {l : List α}, l.Nodup → ∀ p ∈ consecPairs l, p.1 ≠ p.2
  | [], _, p, hp => by simp [consecPairs] at hp
  | [_], _, p, hp => by simp [consecPairs] at hp
  | x :: y :: T, h, p, hp => by
    rw [List.nodup_cons] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact fun hxy ↦ h.1 (List.mem_cons.mpr (Or.inl hxy))
    · exact consecPairs_ne h.2 p hp

/-- A test that lets some entries through unconditionally is the test on the rest of the list.
Worth doing when the exemption does not depend on the enclosing loops, as in `classOk`. -/
theorem all_or_eq_all_filter {α : Type} (l : List α) (q p : α → Bool) :
    (l.all fun z ↦ q z || p z) = (l.filter fun z ↦ !q z).all p := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_filter, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, and_imp]
  constructor
  · exact fun h z hz hq ↦ (h z hz).resolve_left (by simp [hq])
  · intro h z hz
    cases hq : q z
    · exact Or.inr (h z hz hq)
    · exact Or.inl rfl

variable (H)

/-- The vertices of `hs` that can take `x`'s place: those with the same neighbours as `x`, apart
from the two of them. -/
def twinsOf (hs : List H.V) (x : H.V) : List H.V :=
  hs.filter fun y ↦ hs.all fun z ↦ decide (z = x) || decide (z = y) || (H.Adj x z == H.Adj y z)

/-- Is `C` a class of interchangeable vertices: all with the same neighbours outside `C`, and all
adjacent to each other or none of them?  Any permutation of such a class is an automorphism. -/
def classOk (hs C : List H.V) : Bool :=
  decide C.Nodup &&
  (C.all fun x ↦ C.all fun y ↦ hs.all fun z ↦ C.contains z || (H.Adj x z == H.Adj y z)) &&
  (C.all fun x ↦ C.all fun y ↦ C.all fun z ↦ C.all fun w ↦
    decide (x = y) || decide (z = w) || (H.Adj x y == H.Adj z w))

/-- The adjacencies between distinct vertices of `C`. -/
def offVals (C : List H.V) : List Bool :=
  C.flatMap fun x ↦ (C.filter fun y ↦ decide (x ≠ y)).map fun y ↦ H.Adj x y

/-- What `classOk` runs.  The vertices outside the class are filtered out once rather than tested
at every pair, and the `|C| ^ 4` loop — each off-diagonal adjacency equal to each other one — is
replaced by the `|C| ^ 2` list of those adjacencies compared against its head.  Together they are
three quarters of what `symPairs` costs on a small pattern. -/
def classOkFast (hs C : List H.V) : Bool :=
  let out := hs.filter fun z ↦ !C.contains z
  let vals := offVals H C
  decide C.Nodup &&
  (C.all fun x ↦ C.all fun y ↦ out.all fun z ↦ H.Adj x z == H.Adj y z) &&
  vals.all fun b ↦ b == vals.headD false

section
variable {H}

theorem mem_offVals {C : List H.V} {b : Bool} :
    b ∈ offVals H C ↔ ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ H.Adj x y = b := by
  simp only [offVals, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨x, hx, y, ⟨hy, hne⟩, hb⟩ ↦ ⟨x, hx, y, hy, hne, hb⟩,
    fun ⟨x, hx, y, hy, hne, hb⟩ ↦ ⟨x, hx, y, ⟨hy, hne⟩, hb⟩⟩

theorem classOk_outside_eq {hs C : List H.V} :
    (C.all fun x ↦ C.all fun y ↦ hs.all fun z ↦ C.contains z || (H.Adj x z == H.Adj y z))
      = (C.all fun x ↦ C.all fun y ↦ (hs.filter fun z ↦ !C.contains z).all
          fun z ↦ H.Adj x z == H.Adj y z) := by
  simp only [all_or_eq_all_filter]

theorem classOk_inside_eq {C : List H.V} :
    (C.all fun x ↦ C.all fun y ↦ C.all fun z ↦ C.all fun w ↦
        decide (x = y) || decide (z = w) || (H.Adj x y == H.Adj z w))
      = (offVals H C).all fun b ↦ b == (offVals H C).headD false := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro h b hb
    obtain ⟨x, hx, y, hy, hne, rfl⟩ := mem_offVals.1 hb
    have hd : (offVals H C).headD false ∈ offVals H C := by
      cases hv : offVals H C with
      | nil => rw [hv] at hb; simp at hb
      | cons a t => simp
    obtain ⟨z, hz, w, hw, hnw, hdw⟩ := mem_offVals.1 hd
    rcases h x hx y hy z hz w hw with (h1 | h1) | h1
    · exact absurd h1 hne
    · exact absurd h1 hnw
    · rw [h1, hdw]
  · intro h x hx y hy z hz w hw
    by_cases hxy : x = y
    · exact Or.inl (Or.inl hxy)
    by_cases hzw : z = w
    · exact Or.inl (Or.inr hzw)
    refine Or.inr ?_
    rw [h _ (mem_offVals.2 ⟨x, hx, y, hy, hxy, rfl⟩), h _ (mem_offVals.2 ⟨z, hz, w, hw, hzw, rfl⟩)]

@[csimp] theorem classOk_eq_classOkFast : @classOk = @classOkFast := by
  funext H hs C
  rw [classOk, classOkFast, classOk_outside_eq, classOk_inside_eq]

end

/-- The classes of mutually interchangeable vertices, each in `hs` order.  A class is recorded
once, at the first of its members, and classes of one vertex are dropped: they say nothing. -/
def twinClasses (hs : List H.V) : List (List H.V) :=
  hs.filterMap fun x ↦
    if (twinsOf H hs x).head? = some x ∧ 2 ≤ (twinsOf H hs x).length then some (twinsOf H hs x)
    else none

/-- Are these classes pairwise disjoint? -/
def disjOk : List (List H.V) → Bool
  | [] => true
  | C :: rest => rest.all (fun D ↦ C.all fun x ↦ !D.contains x) && disjOk rest

/-- The pairs of vertices whose images a search will keep in order: consecutive members of a class
of interchangeable vertices.  The classes are checked here rather than reasoned about, and if the
check fails nothing is constrained. -/
def symPairs (hs : List H.V) : List (H.V × H.V) :=
  if (twinClasses H hs).all (classOk H hs) && disjOk H (twinClasses H hs) then
    (twinClasses H hs).flatMap consecPairs
  else []

variable {H}

/-- A vertex is never paired with itself: a class is a `Nodup` list, and the pairs are its
consecutive entries. -/
theorem symPairs_ne {hs : List H.V} : ∀ p ∈ symPairs H hs, p.1 ≠ p.2 := by
  intro p hp
  rw [symPairs] at hp
  split at hp
  · rename_i hok
    rw [Bool.and_eq_true] at hok
    obtain ⟨C, hC, hpC⟩ := List.mem_flatMap.mp hp
    have hcl := List.all_eq_true.mp hok.1 C hC
    rw [classOk, Bool.and_eq_true, Bool.and_eq_true] at hcl
    exact consecPairs_ne (of_decide_eq_true hcl.1.1) p hpC
  · exact absurd hp (by simp)

theorem pairwise_of_disjOk : ∀ {cs : List (List H.V)}, disjOk H cs = true →
    List.Pairwise (fun A B ↦ ∀ x ∈ A, x ∉ B) cs
  | [], _ => List.Pairwise.nil
  | C :: rest, h => by
    rw [disjOk, Bool.and_eq_true] at h
    refine List.pairwise_cons.mpr ⟨fun D hD x hx ↦ ?_, pairwise_of_disjOk h.2⟩
    have := (List.all_eq_true.mp ((List.all_eq_true.mp h.1) D hD)) x hx
    simpa using this

/-- **Permuting a class of interchangeable vertices is an automorphism.** -/
theorem adj_perm {hs C : List H.V} (hC : classOk H hs C = true) (hcov : ∀ x : H.V, x ∈ hs)
    {σ : H.V → H.V} (hσC : ∀ x ∈ C, σ x ∈ C) (hσout : ∀ x, x ∉ C → σ x = x)
    (hinj : Function.Injective σ) (x y : H.V) : H.Adj (σ x) (σ y) = H.Adj x y := by
  rw [classOk, Bool.and_eq_true, Bool.and_eq_true] at hC
  obtain ⟨⟨-, h1⟩, h2⟩ := hC
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem] at h1 h2
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · by_cases hxy : x = y
    · subst hxy
      rw [Bool.eq_false_iff.mpr (H.loopless _), Bool.eq_false_iff.mpr (H.loopless _)]
    · exact (h2 (σ x) (hσC x hx) (σ y) (hσC y hy) x hx y hy).elim
        (fun h ↦ h.elim (fun h ↦ absurd (hinj h) hxy) (fun h ↦ absurd h hxy)) id
  · rw [hσout y hy]
    rcases h1 (σ x) (hσC x hx) x hx y (hcov y) with h | h
    · exact absurd h hy
    · exact h
  · rw [hσout x hx, H.symm, H.symm x]
    rcases h1 (σ y) (hσC y hy) y hy x (hcov x) with h | h
    · exact absurd h hx
    · exact h
  · rw [hσout x hx, hσout y hy]

/-- **A class can be permuted so that the values of `m` on it come in increasing order.** -/
theorem exists_sort_perm (C : List H.V) (hnd : C.Nodup) (m : H.V → ℕ) :
    ∃ σ : H.V → H.V, (∀ x ∈ C, σ x ∈ C) ∧ (∀ x, x ∉ C → σ x = x) ∧ Function.Injective σ ∧
      List.IsChain (fun a b ↦ m (σ a) ≤ m (σ b)) C := by
  classical
  set le : H.V → H.V → Bool := fun a b ↦ decide (m a ≤ m b) with hle
  set C' := C.mergeSort le with hC'
  have hperm : C'.Perm C := List.mergeSort_perm C le
  have hlen : C'.length = C.length := hperm.length_eq
  have hnd' : C'.Nodup := hperm.nodup_iff.mpr hnd
  have hmem : ∀ x, x ∈ C' ↔ x ∈ C := fun x ↦ hperm.mem_iff
  set σ : H.V → H.V := fun x ↦ if x ∈ C then C'.getD (C.idxOf x) x else x with hσ
  have hidx : ∀ x ∈ C, C.idxOf x < C'.length := by
    intro x hx
    rw [hlen]
    exact List.idxOf_lt_length_iff.mpr hx
  have hget : ∀ x (hx : x ∈ C), σ x = C'[C.idxOf x]'(hidx x hx) := by
    intro x hx
    rw [hσ]
    simp only [hx, ite_eq_left]
    exact List.getD_eq_getElem _ _ (hidx x hx)
  have hσC : ∀ x ∈ C, σ x ∈ C := by
    intro x hx
    rw [hget x hx]
    exact (hmem _).mp (List.getElem_mem _)
  have hσout : ∀ x, x ∉ C → σ x = x := by
    intro x hx
    rw [hσ]
    simp [hx]
  have hinj : Function.Injective σ := by
    intro a b hab
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
    · rw [hget a ha, hget b hb] at hab
      exact (List.idxOf_inj ha).mp ((List.Nodup.getElem_inj_iff hnd').mp hab)
    · exact absurd (hσout b hb ▸ hab ▸ hσC a ha) hb
    · exact absurd (hσout a ha ▸ hab ▸ hσC b hb) ha
    · rwa [hσout a ha, hσout b hb] at hab
  refine ⟨σ, hσC, hσout, hinj, ?_⟩
  have hmapC : C.map σ = C' := by
    refine List.ext_getElem (by rw [List.length_map, hlen]) fun i h₁ h₂ ↦ ?_
    rw [List.length_map] at h₁
    rw [List.getElem_map, hget _ (List.getElem_mem h₁)]
    simp only [List.Nodup.idxOf_getElem hnd i h₁]
  refine (List.isChain_map (R := fun a b ↦ m a ≤ m b) σ).mp ?_
  rw [hmapC, hC']
  refine List.Pairwise.isChain (List.Pairwise.imp ?_ (List.pairwise_mergeSort ?_ ?_ C))
  · intro a b h
    simpa [hle] using h
  · intro a b c hab hbc
    simp only [hle, decide_eq_true_eq] at hab hbc ⊢
    omega
  · intro a b
    simp only [hle, Bool.or_eq_true, decide_eq_true_eq]
    omega

end CGraph
