import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import IsoGraph.Canon.Spec
import IsoGraph.Canon.Leaves

/-!
# The automorphism group, computed alongside the canonical labelling

The individualisation–refinement search of `IsoGraph.Canon.Algorithm` already discovers
automorphisms: every time it reaches a leaf whose certificate ties the current best one, the two
labellings differ by an automorphism, and it records that permutation in `St.autos` and uses it to
prune the rest of the search.  Those generators are thrown away by `canonPerm`, which keeps only
the labelling.  This file keeps them.

## What is here

* `autGroup n adj` — the automorphism group of a graph on `Fin n`, as a `Subgroup
  (Equiv.Perm (Fin n))`.
* `autGens n adj` — the generators the search harvested, as *elements of that subgroup*.  There
  is no run-time check involved: `Leaves.dfsNode_good` already proves that everything the search
  puts in `St.autos` is an automorphism, so the membership proof comes for free.
* `canonPermAndGens n adj` — **the pair entry point**: the canonical labelling and the generators,
  from a single run of the search.  `canonPerm` and `autGens` are its two projections
  definitionally, so nothing is recomputed by using it.
* `canonMatrixAndGens n adj` — the same, with the canonical form as an adjacency matrix.

## What is and is not proved

Everything the search hands back is genuine — `autGens` are elements of `autGroup n adj`, with
the membership proof coming from `Leaves.dfsNode_good`, not from a run-time check.  What is *not*
proved is that they are enough: the search prunes, and `St.addAuto` stops recording after
`maxGens` of them, so nothing here says the subgroup they generate is the whole automorphism
group.  (In practice it is; that is what nauty relies on.)

When completeness is what you need, `Canon/Chain.lean` computes a generating set and proves it
complete — `autGroup n adj = Subgroup.closure (permsOf n (chainArrays n adj))` — and
`Canon/Transitive.lean` uses that to *decide* vertex- and arc-transitivity, falsehood included.
It pays for it with a subtree search per candidate point, so it is the reference implementation,
not the fast path.
-/

set_option autoImplicit false

namespace IsoGraph.Canon

variable {n : Nat}

/-! ## The automorphism group of a graph on `Fin n` -/

/-- The automorphism group of the graph `adj` on `Fin n`, as a subgroup of all permutations. -/
def autGroup (n : Nat) (adj : Fin n → Fin n → Bool) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i j, adj (σ i) (σ j) = adj i j}
  mul_mem' {σ τ} hσ hτ i j := by
    show adj (σ (τ i)) (σ (τ j)) = adj i j
    rw [hσ (τ i) (τ j), hτ i j]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ i j := by
    show adj (σ.symm i) (σ.symm j) = adj i j
    rw [← hσ (σ.symm i) (σ.symm j), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem mem_autGroup {adj : Fin n → Fin n → Bool} {σ : Equiv.Perm (Fin n)} :
    σ ∈ autGroup n adj ↔ ∀ i j, adj (σ i) (σ j) = adj i j := Iff.rfl

theorem autGroup_adj {adj : Fin n → Fin n → Bool} (σ : autGroup n adj) (i j : Fin n) :
    adj ((σ : Equiv.Perm (Fin n)) i) ((σ : Equiv.Perm (Fin n)) j) = adj i j := σ.2 i j

/-! ## The generators the search harvests -/

/-- **Every automorphism the search records is genuine.**  This is `Leaves.dfsNode_good`, whose
`StGood` invariant carries exactly this, read off at the root call. -/
theorem canonical_autos_isAuto (m : Nat) (f : Nat → Nat → Bool) {g : Array Nat}
    (hg : g ∈ (canonical (Graph.ofOracle m f)).autos) : IsAutoArr m f g := by
  have hgood : StGood m f (canonSt m f) :=
    dfsNode_good m f (m + 1) #[] (rootInv m f) (rootPart m f) _ Node.root
      ⟨by simp, by simp, by simp⟩
  rw [canonical_eq] at hg
  rcases hb : (canonSt m f).best with _ | b
  · rw [hb] at hg; simp at hg
  · rw [hb] at hg; exact hgood.2.2 g hg

/-- An automorphism in array form, read as a permutation of `Fin n`, is an automorphism. -/
theorem permOfArrays_mem_autGroup {adj : Fin n → Fin n → Bool} {g : Array Nat}
    (h : IsAutoArr n (oracleOfFin n adj) g) :
    permOfArrays n g (invArray n g) ∈ autGroup n adj := by
  intro i j
  have hval : ∀ k : Fin n, (permOfArrays n g (invArray n g) k).1 = g[k.1]! := fun k =>
    permOfArrays_val h.perm.isPerm
      (fun x hx => invArray_apply h.perm.size h.perm.isPerm x hx) k
  have hi := h.perm.lt i.1 i.2
  have hj := h.perm.lt j.1 j.2
  rw [show permOfArrays n g (invArray n g) i = ⟨g[i.1]!, hi⟩ from Fin.ext (hval i),
    show permOfArrays n g (invArray n g) j = ⟨g[j.1]!, hj⟩ from Fin.ext (hval j)]
  have := h.adj i.1 i.2 j.1 j.2
  rwa [oracleOfFin_apply adj hi hj, oracleOfFin_apply adj i.2 j.2, Fin.eta, Fin.eta] at this

/-- Package an array-form automorphism as an element of `autGroup`.  Kept separate from `autGens`
so that elaboration never has to unfold the search to check the membership proof. -/
def autGenOf (n : Nat) (adj : Fin n → Fin n → Bool) (g : Array Nat)
    (hg : IsAutoArr n (oracleOfFin n adj) g) : autGroup n adj :=
  ⟨permOfArrays n g (invArray n g), permOfArrays_mem_autGroup hg⟩

/-- The automorphisms the search harvested, in raw array form. -/
def autoArrays (n : Nat) (adj : Fin n → Fin n → Bool) : Array (Array Nat) :=
  (canonical (Graph.ofOracle n (oracleOfFin n adj))).autos

/-- **The automorphism generators of `adj`**: what the canonical labelling search harvested along
the way, as elements of `autGroup n adj`.

These are generators of *a* subgroup of the automorphism group; for the usual reasons (this is
what nauty does) it is the whole group in practice, but nothing here relies on that.  For a
generating set that is *proved* to generate everything, see `fullGens` in `Canon/Chain.lean`. -/
def autGens (n : Nat) (adj : Fin n → Fin n → Bool) : Array (autGroup n adj) :=
  (autoArrays n adj).attach.map fun g =>
    autGenOf n adj g.1 (canonical_autos_isAuto n (oracleOfFin n adj) g.2)

/-! ## The pair entry point -/

/-- **One search, both halves**: the canonical labelling of `adj` *and* generators for its
automorphism group.

`canonPerm` and `autGens` are the two projections (`canonPermAndGens_fst`,
`canonPermAndGens_snd`), so a caller that wants both should ask for this pair rather than for the
two of them, which would run the search twice. -/
def canonPermAndGens (n : Nat) (adj : Fin n → Fin n → Bool) :
    Equiv.Perm (Fin n) × Array (autGroup n adj) :=
  let r := canonical (Graph.ofOracle n (oracleOfFin n adj))
  let lab := if isPermArray n r.lab then r.lab else Array.range n
  (permOfArrays n lab (invArray n lab),
    r.autos.attach.map fun g =>
      autGenOf n adj g.1 (canonical_autos_isAuto n (oracleOfFin n adj) g.2))

theorem canonPermAndGens_fst (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonPermAndGens n adj).1 = canonPerm n adj := rfl

theorem canonPermAndGens_snd (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonPermAndGens n adj).2 = autGens n adj := rfl

/-- The canonical form and the automorphism generators, from one search. -/
def canonMatrixAndGens (n : Nat) (adj : Fin n → Fin n → Bool) :
    AdjMatrix n × Array (autGroup n adj) :=
  let (σ, gens) := canonPermAndGens n adj
  (matrixOfPerm n adj σ, gens)

theorem canonMatrixAndGens_fst (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonMatrixAndGens n adj).1 = canonMatrix n adj := rfl

theorem canonMatrixAndGens_snd (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonMatrixAndGens n adj).2 = autGens n adj := rfl

/-! ## Diagnostics

Unverified, and not used by anything above: the order of the group generated by the harvested
permutations, computed by simply enumerating it.  That is exponentially worse than the
Schreier–Sims algorithm one would normally use, but it is obviously correct, and the point here is
to have a number to look at (`#eval`), not to have it fast. -/

/-- The order of the group generated by `gens` (permutations of `{0, …, n-1}` in array form), or
`none` if it exceeds `limit`.  Plain breadth-first enumeration of the group elements. -/
def groupOrder? (n : Nat) (gens : Array (Array Nat)) (limit : Nat) : Option Nat := Id.run do
  let e : Array Nat := Array.range n
  let mut seen : Std.HashSet (List Nat) := (∅ : Std.HashSet (List Nat)).insert e.toList
  let mut queue : Array (Array Nat) := #[e]
  let mut i := 0
  for _ in [0:limit] do
    if h : i < queue.size then
      let g := queue[i]
      i := i + 1
      for k in [0:gens.size] do
        let ga := gens[k]!
        let c : Array Nat := (Array.range n).map fun v => ga[g[v]!]!
        if !seen.contains c.toList then
          if seen.size ≥ limit then return none
          seen := seen.insert c.toList
          queue := queue.push c
  if i < queue.size then return none
  return some seen.size

/-- The order of the automorphism group of `adj`, as generated by the harvested generators, or
`none` if it exceeds `limit`.  Unverified; a diagnostic. -/
def autGroupOrder? (n : Nat) (adj : Fin n → Fin n → Bool) (limit : Nat := 100000) : Option Nat :=
  groupOrder? n (autoArrays n adj) limit

end IsoGraph.Canon
