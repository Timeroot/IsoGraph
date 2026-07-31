import IsoGraph.Equivariance

/-!
# The search tree, and what the search is looking for

`IsoGraph.Equivariance` proves that the *ingredients* of the search — refinement,
individualisation, the certificate — are equivariant, and that every leaf the search records is
an honest one.  This file is about the search *tree*:

* `lexCmpU64` is shown to be `compare` on `List UInt64`, which hands us a linear order (Std's
  `OrientedOrd`/`TransOrd`/`LawfulEqOrd` instances) for free.
* `Reach` describes the leaves of the *unpruned* tree, and `key` the quantity the search
  maximises: the pair (node-invariant path, certificate), encoded as a `List (List UInt64)` so
  that lexicographic `compare` on it is the comparison `leafUpdate` performs.
* `reach_transfer` transports leaves along a renaming, and `bestKey_transfer` concludes that the
  *specification* — "the largest key of any leaf" — is an isomorphism invariant.

What is still missing is the bridge from the algorithm to the specification: that the search's
winner really is the largest key, i.e. that none of the three pruning rules ever discards it.
-/

set_option autoImplicit false

namespace IsoGraph
namespace Canon

open Std

/-! ## The comparison used to pick the winner

`lexCmpU64` is `compare` on the underlying lists, so it is a linear order: antisymmetric
(`LawfulEqCmp`), total (`OrientedCmp`) and transitive (`TransCmp`). -/

theorem lexCmpFrom_eq_compare (a b : Array UInt64) : ∀ (fuel i : Nat),
    i + fuel = min a.size b.size →
    lexCmpFrom a b fuel i = compare (a.toList.drop i) (b.toList.drop i)
  | 0, i, h => by
    rw [lexCmpFrom]
    rcases Nat.lt_or_ge a.size b.size with hab | hab
    · have h1 : a.toList.drop i = [] := by
        rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
      have h2 : (b.toList.drop i) ≠ [] := by
        rw [Ne, List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
      cases hb : b.toList.drop i with
      | nil => exact absurd hb h2
      | cons x xs => rw [h1, List.compare_nil_cons]; exact Nat.compare_eq_lt.2 hab
    · rcases Nat.eq_or_lt_of_le hab with hab' | hab'
      · have h1 : a.toList.drop i = [] := by
          rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        have h2 : b.toList.drop i = [] := by
          rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        rw [h1, h2, List.compare_nil_nil, hab']
        simp
      · have h1 : b.toList.drop i = [] := by
          rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        have h2 : (a.toList.drop i) ≠ [] := by
          rw [Ne, List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        cases ha : a.toList.drop i with
        | nil => exact absurd ha h2
        | cons x xs =>
          rw [h1, List.compare_cons_nil]
          exact Nat.compare_eq_gt.2 hab'
  | fuel + 1, i, h => by
    rw [lexCmpFrom, if_pos (by omega)]
    have hia : i < a.size := by omega
    have hib : i < b.size := by omega
    have hda : a.toList.drop i = a[i]! :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hia), getElem!_pos a i hia]
      simp
    have hdb : b.toList.drop i = b[i]! :: b.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hib), getElem!_pos b i hib]
      simp
    rw [hda, hdb, List.compare_cons_cons]
    cases hc : compare a[i]! b[i]! with
    | eq => rw [Ordering.then, lexCmpFrom_eq_compare a b fuel (i + 1) (by omega)]
    | lt => rfl
    | gt => rfl

/-- The search's comparison is `compare` on the underlying lists. -/
theorem lexCmpU64_eq_compare (a b : Array UInt64) :
    lexCmpU64 a b = compare a.toList b.toList := by
  have h := lexCmpFrom_eq_compare a b (min a.size b.size) 0 (by omega)
  simpa using h

theorem lexCmpU64_eq_iff {a b : Array UInt64} : lexCmpU64 a b = .eq ↔ a = b := by
  rw [lexCmpU64_eq_compare]
  constructor
  · intro h
    exact Array.toList_inj.1 (LawfulEqCmp.eq_of_compare h)
  · rintro rfl
    exact compare_self

theorem lexCmpU64_refl (a : Array UInt64) : lexCmpU64 a a = .eq :=
  lexCmpU64_eq_iff.2 rfl

/-- The key a leaf is judged by: its node-invariant path first, its certificate second.  Packing
the two as a `List (List UInt64)` makes lexicographic `compare` on the pair — exactly the
comparison `leafUpdate` performs — available with all of Std's order lemmas. -/
def leafKey (invPath cert : Array UInt64) : List (List UInt64) := [invPath.toList, cert.toList]

/-- `compare` on keys is the two-stage comparison of `leafUpdate`. -/
theorem compare_leafKey (i c i' c' : Array UInt64) :
    compare (leafKey i c) (leafKey i' c')
      = match lexCmpU64 i i' with
        | .eq => lexCmpU64 c c'
        | o => o := by
  rw [leafKey, leafKey, List.compare_cons_cons, List.compare_cons_cons, List.compare_nil_nil,
    ← lexCmpU64_eq_compare, ← lexCmpU64_eq_compare]
  cases lexCmpU64 i i' <;> cases lexCmpU64 c c' <;> rfl

theorem leafKey_inj {i c i' c' : Array UInt64} (h : leafKey i c = leafKey i' c') :
    i = i' ∧ c = c' := by
  rw [leafKey, leafKey, List.cons.injEq, List.cons.injEq] at h
  exact ⟨Array.toList_inj.1 h.1, Array.toList_inj.1 h.2.1⟩

/-! ## The search tree

`Reach n f invPath p k` says that the tree rooted at the refined partition `p` — the *unpruned*
tree, in which every vertex of the target cell is individualised in turn — has a leaf with key
`k`.  This is the search's specification: `canonical` is supposed to return the largest such key
(`BestKey`), and that is manifestly an isomorphism invariant (`bestKey_transfer`). -/

/-- The child of `p` obtained by individualising `v` and re-refining, with the trace of the
refinement.  This is exactly the step `dfsChildren` takes. -/
def child (G : Graph) (p : Part) (v : Nat) : Part × UInt64 :=
  refine G (individualize p v).1
    ((Array.replicate G.n false).set! (individualize p v).2 true) hashSeed

/-- The node invariant of that child, appended to the path invariant. -/
def childInv (G : Graph) (invPath : Array UInt64) (p : Part) (v : Nat) : Array UInt64 :=
  invPath.push (mix (child G p v).2 ((child G p v).1.shapeHash G.n))

/-- The leaves of the unpruned search tree below `p`, described by their keys. -/
inductive Reach (n : Nat) (f : Nat → Nat → Bool) :
    Array UInt64 → Part → List (List UInt64) → Prop
  | leaf {invPath : Array UInt64} {p : Part} (h : p.targetCell n = none) :
      Reach n f invPath p (leafKey invPath (certOf (Graph.ofOracle n f) p.lab))
  | step {invPath : Array UInt64} {p : Part} {c v : Nat} {k : List (List UInt64)}
      (hc : p.targetCell n = some c) (hv : v < n) (hcell : p.cst[p.pos[v]!]! = c)
      (h : Reach n f (childInv (Graph.ofOracle n f) invPath p v)
        (child (Graph.ofOracle n f) p v).1 k) :
      Reach n f invPath p k

/-! ### The tree is equivariant -/

theorem child_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    {v : Nat} (hv : v < n) :
    PartEquiv n σ (child (Graph.ofOracle n f) p (σ v)).1
        (child (Graph.ofOracle n fun a b => f (σ a) (σ b)) q v).1
      ∧ (child (Graph.ofOracle n f) p (σ v)).2
        = (child (Graph.ofOracle n fun a b => f (σ a) (σ b)) q v).2 := by
  obtain ⟨he, hs⟩ := individualize_partEquiv hσ hp hq h hv
  rw [child, child, ofOracle_n, ofOracle_n, hs]
  exact refine_equiv hσ (individualize_wf' hp (hσ.maps v hv)) (individualize_wf' hq hv) he _ _

theorem childInv_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    (invPath : Array UInt64) {v : Nat} (hv : v < n) :
    childInv (Graph.ofOracle n f) invPath p (σ v)
      = childInv (Graph.ofOracle n fun a b => f (σ a) (σ b)) invPath q v := by
  obtain ⟨he, hs⟩ := child_equiv hσ hp hq h hv
  rw [childInv, childInv, hs, ofOracle_n, ofOracle_n, he.shapeHash]

/-- **Leaves transport along a renaming.**  If `p` is `q` renamed by `σ`, every leaf of the tree
below `q` in the renamed graph has a leaf below `p` in the original one with the *same key*. -/
theorem reach_transfer {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    {invPath : Array UInt64} {q : Part} {k : List (List UInt64)}
    (hr : Reach n (fun a b => f (σ a) (σ b)) invPath q k) :
    ∀ {p : Part}, Part.WF n p → Part.WF n q → PartEquiv n σ p q → Reach n f invPath p k := by
  induction hr with
  | leaf htc =>
    rename_i invPath q
    intro p hp hq h
    have htcp : p.targetCell n = none := h.targetCell.trans htc
    have hpd := discrete_of_targetCell_none hp htcp
    have hqd := discrete_of_targetCell_none hq htc
    rw [certOf_of_partEquiv hσ hp hq hpd hqd h f]
    exact Reach.leaf htcp
  | step hc hv hcell _ ih =>
    rename_i invPath q c v k _
    intro p hp hq h
    have hσv : σ v < n := hσ.maps v hv
    refine Reach.step (h.targetCell.trans hc) hσv ((h.cell v hv).trans hcell) ?_
    rw [childInv_equiv hσ hp hq h invPath hv]
    exact ih (refine_wf (individualize_wf' hp hσv) _ _) (refine_wf (individualize_wf' hq hv) _ _)
      (child_equiv hσ hp hq h hv).1

/-- The converse direction: a leaf below `p` gives one below `q`, again with the same key.  The
vertex to individualise is pulled back through `σ`. -/
theorem reach_transfer' {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    {invPath : Array UInt64} {p : Part} {k : List (List UInt64)} (hr : Reach n f invPath p k) :
    ∀ {q : Part}, Part.WF n p → Part.WF n q → PartEquiv n σ p q →
      Reach n (fun a b => f (σ a) (σ b)) invPath q k := by
  induction hr with
  | leaf htc =>
    rename_i invPath p
    intro q hp hq h
    have htcq : q.targetCell n = none := h.targetCell.symm.trans htc
    have hpd := discrete_of_targetCell_none hp htc
    have hqd := discrete_of_targetCell_none hq htcq
    rw [← certOf_of_partEquiv hσ hp hq hpd hqd h f]
    exact Reach.leaf htcq
  | step hc hu hcell _ ih =>
    rename_i invPath p c u k _
    intro q hp hq h
    obtain ⟨v, hv, rfl⟩ := hσ.surj hu
    refine Reach.step (h.targetCell.symm.trans hc) hv ((h.cell v hv).symm.trans hcell) ?_
    rw [← childInv_equiv hσ hp hq h invPath hv]
    exact ih (refine_wf (individualize_wf' hp (hσ.maps v hv)) _ _)
      (refine_wf (individualize_wf' hq hv) _ _) (child_equiv hσ hp hq h hv).1

/-! ### The specification, and its invariance -/

/-- The root of the search: the initially refined partition and its one-entry invariant path. -/
def rootPart (n : Nat) (f : Nat → Nat → Bool) : Part :=
  (initialRefine (Graph.ofOracle n f)).1

/-- The invariant path at the root. -/
def rootInv (n : Nat) (f : Nat → Nat → Bool) : Array UInt64 :=
  #[mix (initialRefine (Graph.ofOracle n f)).2 ((rootPart n f).shapeHash n)]

/-- `k` is the key of a leaf of the whole (unpruned) search tree. -/
def Leafkey (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64)) : Prop :=
  Reach n f (rootInv n f) (rootPart n f) k

/-- **The specification of `canonical`**: the largest key of any leaf. -/
def BestKey (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64)) : Prop :=
  Leafkey n f k ∧ ∀ k', Leafkey n f k' → compare k' k ≠ .gt

theorem bestKey_unique {n : Nat} {f : Nat → Nat → Bool} {k k' : List (List UInt64)}
    (h : BestKey n f k) (h' : BestKey n f k') : k = k' := by
  have h1 := h.2 k' h'.1
  have h2 := h'.2 k h.1
  cases hc : compare k k' with
  | eq => exact LawfulEqCmp.eq_of_compare hc
  | lt => exact absurd (OrientedCmp.gt_of_lt hc) h1
  | gt => exact absurd hc h2

/-- **The specification is an isomorphism invariant.**  Renaming the graph does not change the
set of leaf keys, hence not the largest one. -/
theorem leafkey_transfer {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    (k : List (List UInt64)) : Leafkey n (fun a b => f (σ a) (σ b)) k ↔ Leafkey n f k := by
  have hpe := (initialRefine_equiv (f := f) hσ).1
  have htr := (initialRefine_equiv (f := f) hσ).2
  have hroot : rootInv n (fun a b => f (σ a) (σ b)) = rootInv n f := by
    rw [rootInv, rootInv, ← htr, rootPart, rootPart, hpe.shapeHash]
  rw [Leafkey, Leafkey, hroot]
  exact ⟨fun h => reach_transfer hσ h (initialRefine_wf f) (initialRefine_wf _) hpe,
    fun h => reach_transfer' hσ h (initialRefine_wf f) (initialRefine_wf _) hpe⟩

theorem bestKey_transfer {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    (k : List (List UInt64)) : BestKey n (fun a b => f (σ a) (σ b)) k ↔ BestKey n f k := by
  rw [BestKey, BestKey, leafkey_transfer hσ]
  exact and_congr_right fun _ =>
    ⟨fun h k' hk' => h k' ((leafkey_transfer hσ k').2 hk'),
     fun h k' hk' => h k' ((leafkey_transfer hσ k').1 hk')⟩

end Canon
end IsoGraph
