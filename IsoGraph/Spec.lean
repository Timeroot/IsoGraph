import Mathlib.Logic.Equiv.Defs
import IsoGraph.Canonical

/-!
# From the canonical labelling algorithm to permutations, and its specification

`IsoGraph.Canonical` computes with raw `Array Nat`s.  This file wraps that up as an honest
`Equiv.Perm (Fin n)` and states exactly what remains to be proved about it.

## The wrapper

`permOfArrays` turns the algorithm's output and its inverse into an `Equiv.Perm (Fin n)` by
*checking at run time* (in `O(n)`) that the two arrays really are mutually inverse, falling back
to the identity if not.  That keeps `canonPerm` total and proof-free, and it is what makes
`exists_relabel_of_canonAdj_eq` below unconditional: **whatever** the algorithm returns,
`canonAdj n adj` is the graph `adj` read through *some* permutation, hence isomorphic to it.

## What is proved, and what is not

Write `relabel σ adj` for `adj` with its vertices renamed along `σ`.  Two statements matter:

* **Soundness** — `canonAdj n adjG = canonAdj n adjH → adjG ≅ adjH`.  Proved outright
  (`exists_relabel_of_canonAdj_eq`); the run-time check above is exactly what buys it.  This is
  the direction that guarantees a canonical-form comparison never conflates non-isomorphic
  graphs.

* **Invariance** — `canonAdj n (relabel σ adj) = canonAdj n adj`.  This is
  `canonAdj_relabel`, and it is the one genuinely deep obligation of the whole development: it
  is what licenses `Quotient.lift`ing anything defined through the canonical form.  It is
  currently a `sorry`; see the docstring there for how it decomposes.
-/

namespace IsoGraph.Canon

/-! ## Arrays as permutations -/

/-- Read an array of naturals as a function `Fin n → Fin n`, sending out-of-range entries to
themselves. -/
def finFn (n : Nat) (a : Array Nat) (i : Fin n) : Fin n :=
  if h : a[i.1]! < n then ⟨a[i.1]!, h⟩ else i

/-- Build a permutation of `Fin n` out of an array and its claimed inverse.

The two arrays are *checked* (in `O(n)`) to be mutually inverse, and the identity is returned if
they are not.  So this is total and needs no facts about the algorithm that produced them; the
fallback is unreachable in practice. -/
def permOfArrays (n : Nat) (a b : Array Nat) : Equiv.Perm (Fin n) :=
  if h : (∀ i, finFn n b (finFn n a i) = i) ∧ (∀ i, finFn n a (finFn n b i) = i) then
    { toFun := finFn n a, invFun := finFn n b, left_inv := h.1, right_inv := h.2 }
  else Equiv.refl _

/-- The inverse of an array-encoded permutation of `{0, …, n-1}`. -/
def invArray (n : Nat) (a : Array Nat) : Array Nat := Id.run do
  let mut b := Array.replicate n 0
  for i in [0:n] do
    if a[i]! < n then b := b.set! a[i]! i
  return b

/-- Adjacency oracle on `{0, …, n-1}` coming from an adjacency function on `Fin n`. -/
def oracleOfFin (n : Nat) (adj : Fin n → Fin n → Bool) (v w : Nat) : Bool :=
  if hv : v < n then if hw : w < n then adj ⟨v, hv⟩ ⟨w, hw⟩ else false else false

/-- The canonical labelling of a graph on `Fin n`: canonical position `i` holds the vertex
`canonPerm n adj i`. -/
def canonPerm (n : Nat) (adj : Fin n → Fin n → Bool) : Equiv.Perm (Fin n) :=
  let lab := canonicalLabellingOfOracle n (oracleOfFin n adj)
  permOfArrays n lab (invArray n lab)

/-- The canonical form of a graph on `Fin n`: the graph relabelled so that its adjacency matrix
is the canonical one.

**This is the specification, not the way to compute.**  Lean η-expands every function-typed
definition, so each query `canonAdj n adj i j` re-runs the whole search.  To compute, use
`canonOracleOf`, whose result is a structure and therefore shares the search across queries. -/
def canonAdj (n : Nat) (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  let σ := canonPerm n adj
  fun i j ↦ adj (σ i) (σ j)

/-- A graph on `{0, …, size-1}` given by an adjacency oracle.

The reason this is a structure and not a bare `Nat → Nat → Bool`: the Lean compiler η-expands
every definition whose type is a function type, so a `def f (x) : Nat → Nat → Bool := <search>;
fun a b ↦ …` re-runs `<search>` on every single query.  Returning a structure blocks the
η-expansion, and the search is run once and captured in the closure. -/
structure Oracle where
  /-- The number of vertices. -/
  size : Nat
  /-- Adjacency; `false` outside `{0, …, size-1}`. -/
  adj : Nat → Nat → Bool

theorem Oracle.ext' {o₁ o₂ : Oracle} (hs : o₁.size = o₂.size) (ha : o₁.adj = o₂.adj) : o₁ = o₂ := by
  cases o₁; cases o₂; cases hs; cases ha; rfl

/-- The graph `adj` read through the permutation `σ`, as an `Oracle`. -/
def oracleOfPerm (n : Nat) (adj : Fin n → Fin n → Bool) (σ : Equiv.Perm (Fin n)) : Oracle where
  size := n
  adj := oracleOfFin n fun i j ↦ adj (σ i) (σ j)

/-- **The canonical form of a graph on `Fin n`, computed.**  The search runs once, when this is
forced; each query of the resulting `Oracle.adj` is then `O(1)`. -/
def canonOracleOf (n : Nat) (adj : Fin n → Fin n → Bool) : Oracle :=
  oracleOfPerm n adj (canonPerm n adj)

@[simp] theorem canonOracleOf_size (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonOracleOf n adj).size = n := rfl

@[simp] theorem canonOracleOf_adj (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonOracleOf n adj).adj = oracleOfFin n (canonAdj n adj) := rfl

/-- `Fin m ≃ Fin n` from `m = n`.  Unlike `Equiv.cast` this has a definitional `val`. -/
def finEq {m n : Nat} (h : m = n) : Fin m ≃ Fin n where
  toFun i := ⟨i.1, h ▸ i.2⟩
  invFun j := ⟨j.1, h ▸ j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem finEq_val {m n : Nat} (h : m = n) (i : Fin m) : (finEq h i).1 = i.1 := rfl

@[simp] theorem finEq_symm_val {m n : Nat} (h : m = n) (j : Fin n) :
    ((finEq h).symm j).1 = j.1 := rfl

theorem oracleOfFin_apply {n : Nat} (f : Fin n → Fin n → Bool) {a b : Nat} (ha : a < n)
    (hb : b < n) : oracleOfFin n f a b = f ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [oracleOfFin, ha, hb]

theorem oracleOfFin_comm {n : Nat} {f : Fin n → Fin n → Bool} (hf : ∀ i j, f i j = f j i)
    (a b : Nat) : oracleOfFin n f a b = oracleOfFin n f b a := by
  by_cases ha : a < n
  · by_cases hb : b < n
    · rw [oracleOfFin_apply f ha hb, oracleOfFin_apply f hb ha]; exact hf _ _
    · simp [oracleOfFin, ha, hb]
  · simp [oracleOfFin, ha]

theorem oracleOfFin_irrefl {n : Nat} {f : Fin n → Fin n → Bool} (hf : ∀ i, f i i = false)
    (a : Nat) : oracleOfFin n f a a = false := by
  by_cases ha : a < n
  · rw [oracleOfFin_apply f ha ha]; exact hf _
  · simp [oracleOfFin, ha]

/-! ## Relabelling -/

variable {n : Nat}

/-- `adj` with its vertices renamed along `σ`: the vertex `i` of `relabel σ adj` plays the role of
the vertex `σ i` of `adj`. -/
def relabel (σ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j ↦ adj (σ i) (σ j)

@[simp] theorem relabel_apply (σ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) (i j) :
    relabel σ adj i j = adj (σ i) (σ j) := rfl

@[simp] theorem relabel_refl (adj : Fin n → Fin n → Bool) : relabel (Equiv.refl _) adj = adj := rfl

theorem relabel_relabel (σ τ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) :
    relabel σ (relabel τ adj) = relabel (σ.trans τ) adj := rfl

/-- `canonAdj` is, pointwise, the original adjacency read through `canonPerm`. -/
@[simp] theorem canonAdj_apply (adj : Fin n → Fin n → Bool) (i j : Fin n) :
    canonAdj n adj i j = adj (canonPerm n adj i) (canonPerm n adj j) := rfl

/-- The canonical form is a relabelling of the original graph. -/
theorem canonAdj_eq_relabel (adj : Fin n → Fin n → Bool) :
    canonAdj n adj = relabel (canonPerm n adj) adj := rfl

theorem canonAdj_comm {adj : Fin n → Fin n → Bool} (h : ∀ i j, adj i j = adj j i) (i j : Fin n) :
    canonAdj n adj i j = canonAdj n adj j i := h _ _

theorem canonAdj_irrefl {adj : Fin n → Fin n → Bool} (h : ∀ i, ¬adj i i) (i : Fin n) :
    ¬canonAdj n adj i i := h _

/-! ## Soundness: equal canonical forms come from isomorphic graphs -/

/-- **Soundness.**  If two graphs on `Fin n` have the same canonical form then they are
isomorphic — indeed, an explicit isomorphism is produced.

Nothing about the search is needed here.  `canonAdj n adj` is by construction `adj` read through
the permutation `canonPerm n adj`, and `permOfArrays` guarantees that this really is a
permutation whatever the algorithm returned; so equal canonical forms exhibit the two graphs as
relabellings of one common graph. -/
theorem exists_relabel_of_canonAdj_eq {adjG adjH : Fin n → Fin n → Bool}
    (h : canonAdj n adjG = canonAdj n adjH) :
    ∃ σ : Equiv.Perm (Fin n), relabel σ adjG = adjH := by
  refine ⟨(canonPerm n adjH).symm.trans (canonPerm n adjG), ?_⟩
  funext x y
  have hxy := congrFun (congrFun h ((canonPerm n adjH).symm x)) ((canonPerm n adjH).symm y)
  simpa [Equiv.trans_apply] using hxy

/-! ## Invariance: the remaining obligation -/

/-- **Invariance of the canonical form.**  Renaming the vertices of a graph does not change its
canonical form.

This is the one deep fact about the algorithm, and everything else — that `IsoGraph` may be
`Quotient.lift`ed through the canonical form, and hence that graph invariants computed from it
are well defined — reduces to it.

It decomposes as follows.  Fix `σ` and write `q ≈ p` for "the ordered partitions `q` and `p` have
the same cell boundaries, and the `i`-th cell of `q` is the `σ`-image of the `i`-th cell of `p`
*as a set*".  (Only as a set: refinement's counting sort is stable, so the order *within* a cell
is inherited from the parent cell and so depends on vertex names, which are not invariant.  What
is invariant is the sequence of cells.)  Then:

1. `refineStep` is `≈`-equivariant: it returns `≈`-related partitions, the same worklist, and the
   same trace hash, because every quantity it hashes (`s`, cell starts, fragment sizes, neighbour
   counts) is determined by positions and multiplicities.  Hence so are `refineLoop`, `refine`
   and `initialRefine` — note `Part.unit n ≈ Part.unit n` for every `σ`, the point being that a
   one-cell partition carries no order information.
2. `Part.shapeHash` and `Part.targetCell` read only cell boundaries, so they agree on `≈`-related
   partitions.
3. `individualize p v` and `individualize q (σ v)` produce `≈`-related partitions and the same
   splitter position.
4. On *discrete* partitions `≈` forces `q.lab = σ ∘ p.lab`, and then `certOf` agrees, since it
   reads the adjacency matrix in exactly that order.
5. Therefore the two search trees have the same shape and the same node invariants, and their
   leaves correspond — except that the children of a node are enumerated in a different order,
   since the target cell is listed in `lab` order.
6. So it remains to see that the *maximum* over the leaves does not depend on the order in which
   children are enumerated.  This is where the three prunings have to be justified: invariant
   pruning discards only subtrees whose leaves are dominated; orbit pruning discards only
   children whose subtrees are automorphic images of an already-explored one; and the backjump of
   `leafUpdate` discards only the remainder of a branch all of whose leaves are automorphic
   images of leaves already visited. -/
theorem canonAdj_relabel (σ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) :
    canonAdj n (relabel σ adj) = canonAdj n adj := by
  sorry

/-- Two adjacency functions related by a permutation have the same canonical form. -/
theorem canonAdj_eq_of_equiv {A B : Fin n → Fin n → Bool} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ a b, B (σ a) (σ b) = A a b) : canonAdj n A = canonAdj n B := by
  have h : A = relabel σ B := by funext a b; exact (hσ a b).symm
  subst h
  exact canonAdj_relabel σ B

/-- The `ℕ`-indexed form of `canonAdj_eq_of_equiv`: two adjacency functions, on index sets of the
same size, related by a bijection, have the same canonical adjacency oracle.  This is the shape
needed to lift the canonical form through a quotient. -/
theorem oracleOfFin_canonAdj_congr {m k : Nat} (h : m = k) {A : Fin m → Fin m → Bool}
    {B : Fin k → Fin k → Bool} (σ : Fin m ≃ Fin k) (hσ : ∀ a b, B (σ a) (σ b) = A a b) :
    oracleOfFin m (canonAdj m A) = oracleOfFin k (canonAdj k B) := by
  subst h
  rw [canonAdj_eq_of_equiv σ hσ]

/-- The `Oracle`-level form of `oracleOfFin_canonAdj_congr`: this is what gets lifted through the
quotient in `IsoGraph.Basic`. -/
theorem canonOracleOf_congr {m k : Nat} (h : m = k) {A : Fin m → Fin m → Bool}
    {B : Fin k → Fin k → Bool} (σ : Fin m ≃ Fin k) (hσ : ∀ a b, B (σ a) (σ b) = A a b) :
    canonOracleOf m A = canonOracleOf k B :=
  Oracle.ext' h (oracleOfFin_canonAdj_congr h σ hσ)

/-- Two graphs on `Fin n` have the same canonical form exactly when they are isomorphic. -/
theorem canonAdj_eq_iff {adjG adjH : Fin n → Fin n → Bool} :
    canonAdj n adjG = canonAdj n adjH ↔ ∃ σ : Equiv.Perm (Fin n), relabel σ adjG = adjH := by
  refine ⟨exists_relabel_of_canonAdj_eq, ?_⟩
  rintro ⟨σ, rfl⟩
  exact (canonAdj_relabel σ adjG).symm

/-- The transported form of `canonAdj_relabel`: graphs on `Fin m` and `Fin n` that are isomorphic
(so in particular `m = n`) have the same canonical form. -/
theorem canonAdj_congr {m n : Nat} (h : m = n) {adjG : Fin m → Fin m → Bool}
    {adjH : Fin n → Fin n → Bool} (σ : Fin m ≃ Fin n)
    (hσ : ∀ a b, adjH (σ a) (σ b) = adjG a b) (x y : Fin m) :
    canonAdj m adjG x y = canonAdj n adjH (h ▸ x) (h ▸ y) := by
  subst h
  have : adjG = relabel σ adjH := by funext a b; exact (hσ a b).symm
  subst this
  rw [canonAdj_relabel]

end IsoGraph.Canon
