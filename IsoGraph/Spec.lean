import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Defs
import IsoGraph.Canonical
import IsoGraph.Equivariance
import IsoGraph.Correct

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

## What is proved

Write `relabel σ adj` for `adj` with its vertices renamed along `σ`.  Two statements matter, and
both are proved.

* **Soundness** — `canonAdj n adjG = canonAdj n adjH → adjG ≅ adjH`.  Proved outright
  (`exists_relabel_of_canonAdj_eq`); the run-time check above is exactly what buys it.  This is
  the direction that guarantees a canonical-form comparison never conflates non-isomorphic
  graphs.

* **Invariance** — `canonAdj n (relabel σ adj) = canonAdj n adj`.  This is `canonAdj_relabel`,
  the deep half: it is what licenses `Quotient.lift`ing anything defined through the canonical
  form.  It is reduced below to `LabellingInvariant`, a statement about raw arrays, which is
  discharged in `IsoGraph/Correct.lean` from the soundness and optimality of the search.
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
`canonMatrix`, whose result is a structure and therefore shares the search across queries. -/
def canonAdj (n : Nat) (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  let σ := canonPerm n adj
  fun i j ↦ adj (σ i) (σ j)

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

/-! ## Adjacency matrices

The type the canonical form is actually delivered in.  Two things are going on:

* it is a **structure**, not a bare `Fin n → Fin n → Bool`, because the compiler η-expands every
  definition whose type is a function type — a `def f (x) : Fin n → Fin n → Bool := <search>;
  fun i j ↦ …` re-runs `<search>` on every single query.  One field is enough to block that, and
  a one-field structure is unboxed at runtime, so the wrapper is free;
* it is indexed by its size, so that "the canonical form of a graph on `V`" can live in
  `AdjMatrix (Fintype.card V)` — a type that does not mention the listing of `V` used to compute
  it, which is what makes the quotient lift in `IsoGraph.Basic` typecheck.
-/

/-- The adjacency matrix of a graph on `Fin n`. -/
structure AdjMatrix (n : Nat) where
  /-- The adjacency function. -/
  adj : Fin n → Fin n → Bool

namespace AdjMatrix

theorem ext' {n : Nat} {M N : AdjMatrix n} (h : M.adj = N.adj) : M = N := by
  cases M; cases N; cases h; rfl

/-- Query a matrix at plain naturals; `false` out of range. -/
def get {n : Nat} (M : AdjMatrix n) (a b : Nat) : Bool := oracleOfFin n M.adj a b

theorem get_eq {n : Nat} (M : AdjMatrix n) {a b : Nat} (ha : a < n) (hb : b < n) :
    M.get a b = M.adj ⟨a, ha⟩ ⟨b, hb⟩ := oracleOfFin_apply _ ha hb

/-- Move a matrix onto the index set `Fin m`, reading `false` outside the common range.

This is the one place where an index set of the "wrong" size is tolerated, and it is what lets
the canonical form of a graph be stated on `Fin (Fintype.card V)` while being computed from a
listing whose length is only *provably* that. -/
def reindex {n : Nat} (M : AdjMatrix n) (m : Nat) : AdjMatrix m :=
  ⟨fun i j ↦ M.get i.1 j.1⟩

@[simp] theorem reindex_adj {n m : Nat} (M : AdjMatrix n) (i j : Fin m) :
    (M.reindex m).adj i j = M.get i.1 j.1 := rfl

theorem reindex_congr {n k m : Nat} {M : AdjMatrix n} {N : AdjMatrix k}
    (h : ∀ a b, M.get a b = N.get a b) : M.reindex m = N.reindex m :=
  ext' (funext fun i ↦ funext fun j ↦ h i.1 j.1)

theorem get_comm {n : Nat} {M : AdjMatrix n} (h : ∀ i j, M.adj i j = M.adj j i) (a b : Nat) :
    M.get a b = M.get b a := oracleOfFin_comm h a b

theorem get_irrefl {n : Nat} {M : AdjMatrix n} (h : ∀ i, M.adj i i = false) (a : Nat) :
    M.get a a = false := oracleOfFin_irrefl h a

/-- Matrices of the same size, agreeing pointwise up to the identification of the index sets, are
heterogeneously equal. -/
theorem heq_of_adj {m n : Nat} (h : m = n) {M : AdjMatrix m} {N : AdjMatrix n}
    (hMN : ∀ x y, M.adj x y = N.adj (finEq h x) (finEq h y)) : HEq M N := by
  subst h
  exact heq_of_eq (ext' (funext fun x ↦ funext fun y ↦ hMN x y))

end AdjMatrix

/-- The graph `adj` read through the permutation `σ`, as a matrix. -/
def matrixOfPerm (n : Nat) (adj : Fin n → Fin n → Bool) (σ : Equiv.Perm (Fin n)) : AdjMatrix n :=
  ⟨fun i j ↦ adj (σ i) (σ j)⟩

/-- **The canonical form of a graph on `Fin n`, computed.**  The search runs once, when this is
forced — `σ` is an argument of `matrixOfPerm`, so it is evaluated before the closure is built —
and each query of the resulting `adj` is then `O(1)`. -/
def canonMatrix (n : Nat) (adj : Fin n → Fin n → Bool) : AdjMatrix n :=
  matrixOfPerm n adj (canonPerm n adj)

@[simp] theorem canonMatrix_adj (n : Nat) (adj : Fin n → Fin n → Bool) :
    (canonMatrix n adj).adj = canonAdj n adj := rfl

theorem canonMatrix_get (n : Nat) (adj : Fin n → Fin n → Bool) (a b : Nat) :
    (canonMatrix n adj).get a b = oracleOfFin n (canonAdj n adj) a b := rfl

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

/-! ## Invariance

Renaming the vertices of a graph does not change its canonical form.  This is the one deep fact
about the algorithm, and everything else — that `IsoGraph` may be `Quotient.lift`ed through the
canonical form, and hence that graph invariants computed from it are well defined — reduces to
it.

It is `canonAdj_relabel` below, and it is *derived* here from two statements about the raw array
algorithm, `LabellingIsPerm` and `LabellingInvariant`.  That reduction is the point of this
section: it discharges the whole `Fin`/`Equiv.Perm` wrapper — the `permOfArrays` run-time check,
the `invArray` inverse, the translation between `Equiv.Perm (Fin n)` and a renaming of
`{0, …, n-1}` — so that what is left to prove mentions nothing but `Array Nat` and
`canonicalLabellingOfOracle`.  See `IsoGraph/Equivariance.lean` for the groundwork on that side.

Of the two, `LabellingIsPerm` is cheap: `canonicalLabellingOfOracle` verifies it at run time in
`O(n)`.  `LabellingInvariant` is where all the work is; it follows from `canonical_cert_relabel`
of `IsoGraph/Correct.lean`. -/

/-- The labelling the search returns for the oracle `f` on `m` vertices: canonical position `i`
holds the vertex `labelling m f`. -/
abbrev labelling (m : Nat) (f : Nat → Nat → Bool) : Array Nat := canonicalLabellingOfOracle m f

/-- **The labelling is a permutation of the vertices.**  Proved: `canonicalLabellingOfOracle`
checks this in `O(n)` and returns the identity if the check fails, so it holds regardless of what
the search does.  See `labellingIsPerm`. -/
def LabellingIsPerm : Prop :=
  ∀ (m : Nat) (f : Nat → Nat → Bool),
    (labelling m f).size = m ∧ Canon.IsPerm m (fun v => (labelling m f)[v]!)

/-- **The remaining obligation: the labelling the search settles on is equivariant.**

Renaming the vertices along `s` and canonicalising gives the same adjacency matrix as
canonicalising and not renaming.  Note this is weaker than "the labelling itself transforms along
`s`", which is false: the winner is only determined up to an automorphism, and which of several
equally-good leaves the search happens to reach does depend on vertex names.  What must not
depend on them is the *matrix read off at the winner*, which is what this says. -/
def LabellingInvariant : Prop :=
  ∀ (m : Nat) (f : Nat → Nat → Bool) (s : Nat → Nat), Canon.IsPerm m s →
    ∀ i, i < m → ∀ j, j < m →
      f (s ((labelling m fun v w => f (s v) (s w))[i]!))
          (s ((labelling m fun v w => f (s v) (s w))[j]!))
        = f ((labelling m f)[i]!) ((labelling m f)[j]!)

theorem labellingIsPerm : LabellingIsPerm :=
  Canon.canonicalLabellingOfOracle_isPerm

/-- The deep half.  The search's answer satisfies the specification `BestKey`
(`canonSt_bestKey`), which is manifestly an isomorphism invariant, so the certificate it returns
does not depend on the vertex names (`canonical_cert_relabel`); `certOf_get` reads the adjacency
matrix back out of that certificate. -/
theorem labellingInvariant : LabellingInvariant := by
  intro m f s hs i hi j hj
  have h1 : certGet m (canonical (Graph.ofOracle m fun v w => f (s v) (s w))).cert i j
      = f (s (canonical (Graph.ofOracle m fun v w => f (s v) (s w))).lab[i]!)
          (s (canonical (Graph.ofOracle m fun v w => f (s v) (s w))).lab[j]!) :=
    canonical_get m (fun v w => f (s v) (s w)) hi hj
  have h2 := canonical_get m f hi hj
  simp only [labelling, canonicalLabellingOfOracle_eq]
  rw [← h1, ← h2, canonical_cert_relabel m f hs]

/-! ### `invArray` and `permOfArrays` on a genuine permutation -/

theorem invArray_size (m : Nat) (a : Array Nat) : (invArray m a).size = m := by
  unfold invArray
  simp only [Id.run, Array.set!]
  simp (config := { decide := true })
  dsimp [ForIn.forIn]
  -- Key: List.forIn' in Id with yielding steps preserves size
  -- We prove a general lemma by structural induction on the list.
  -- Even though List.forIn' is protected, we know its equations from the definition.
  -- Step function preserves size
  have step_size' : ∀ (i val : Nat) (st : Array Nat), Array.size st = m →
      Array.size (if val < m then st.setIfInBounds val i else st) = m := by
    intro i val st hr
    simp only [Array.setIfInBounds]
    split_ifs with h1 h2 <;> simp [Array.size_set, hr] at *
  have loop_size : ∀ (xs : List Nat) (st : Array Nat) (w : ∃ bs, bs ++ xs = List.range' 0 m),
      Array.size st = m →
      Array.size ((List.forIn'.loop (List.range' 0 m)
        (fun a_1 _ r => pure (ForInStep.yield (if a[a_1]! < m then r.setIfInBounds (a[a_1]!) a_1 else r)))
        xs st w : Id (Array Nat))) = m := by
    intro xs
    induction xs with
    | nil =>
      simp [List.forIn'.loop]
      intro st hr
      simp [pure]; exact hr
    | cons head tail ih =>
      simp [List.forIn'.loop]
      intro st x hx hst
      have hhead_mem : head ∈ List.range' 0 m := by
        rw [← hx]
        exact List.mem_append_right _ List.mem_cons_self
      let new_st := if a[head]! < m then st.setIfInBounds (a[head]!) head else st
      have hnew_st : Array.size new_st = m := step_size' head (a[head]!) st hst
      let w' : ∃ bs, bs ++ tail = List.range' 0 m := ⟨x ++ [head], by
        show x ++ [head] ++ tail = List.range' 0 m
        rw [List.append_assoc]; exact hx⟩
      simp [bind, pure] at *
      exact ih new_st (x ++ [head]) (by simp [List.append_assoc]; exact hx) hnew_st
  have heq : (forIn' (List.range' 0 m) (Array.replicate m 0)
      (fun a_1 x r => if a[a_1]! < m then pure (ForInStep.yield (r.setIfInBounds a[a_1]! a_1)) else pure (ForInStep.yield r)) : Id (Array Nat))
    = (List.forIn'.loop (List.range' 0 m)
      (fun a_1 _ r => pure (ForInStep.yield (if a[a_1]! < m then r.setIfInBounds (a[a_1]!) a_1 else r)))
      (List.range' 0 m) (Array.replicate m 0) ⟨[], rfl⟩ : Id (Array Nat)) := by
    dsimp [ForIn'.forIn', List.forIn']
    congr 1
    funext a_1 x r
    by_cases h : a[a_1]! < m <;> simp [h]
  rw [heq]
  exact loop_size _ _ _ (Array.size_replicate)

/-- On a permutation array, `invArray` really is the inverse. -/
theorem invArray_apply {m : Nat} {a : Array Nat} (ha : a.size = m)
    (h : Canon.IsPerm m fun v => a[v]!) (i : Nat) (hi : i < m) :
    (invArray m a)[a[i]!]! = i := by
  -- The result of invArray m a does not depend on a[i] for i >= m (out of range reads are 0)
  -- Key fact: invArray builds b such that b[a[k]!] = k for each k < m where a[k]! < m.
  -- Since a is a permutation, a[i]! < m, and no other k < m, k ≠ i has a[k]! = a[i]!.
  -- So after the loop, (invArray m a)[a[i]!]! = i.
  have ha_lt : ∀ k, k < m → a[k]! < m := fun k hk => h.maps k hk
  have forIn'_always_yield : ∀ (l : List Nat) (init : Array Nat),
      Id.run (forIn' l init (fun k _ (x : Array Nat) => pure (ForInStep.yield (if a[k]! < m then Array.setIfInBounds x (a[k]!) k else x)))) =
      List.foldl (fun x k => if a[k]! < m then Array.setIfInBounds x (a[k]!) k else x) init l := by
    intro l
    induction l with
    | nil =>
      simp [List.forIn']
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons]
      simp (config := { decide := true }) [List.forIn']
      rw [List.foldl_map]
      simp
  -- Now prove the main goal
  unfold invArray
  simp (config := { decide := true }) [Array.set!]
  have forIn_eq_foldl : ∀ (l : List Nat) (init : Array Nat),
      Id.run (forIn l init (fun i (r : Array Nat) =>
          if a[i]! < m then pure (ForInStep.yield (Array.setIfInBounds r (a[i]!) i))
          else pure (ForInStep.yield r))) =
      List.foldl (fun x k => if a[k]! < m then Array.setIfInBounds x (a[k]!) k else x) init l := by
    intro l
    induction l with
    | nil =>
      simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons, List.forIn_cons]
      split <;> simp [ih]
  rw [forIn_eq_foldl]
  -- Key invariant: after folding over a list of indices all < m, position a[i]! contains i
  -- for any i in that list (processed last among those with that a-value, but a is injective).
  -- We prove by induction on the list that after folding, for any k in the list with k < m,
  -- the result at position a[k]! equals k.
  -- Then apply with l = range' 0 m and our specific i.
  -- Helper: Array.getElem! after setIfInBounds at a different position
  have arr_get_same : ∀ (x : Array Nat) (j : Nat) (v : Nat),
      j < x.size → (x.setIfInBounds j v)[j]! = v := by
    intro x j v hj
    simp (config := { decide := true }) [Array.setIfInBounds, hj]
  -- Main invariant: for any list l of naturals all < m, for any init array,
  -- for any i ∈ l with i < m, (foldl fstep init l)[a[i]!]! = i.
  set fstep : Array Nat → Nat → Array Nat := fun x k => if a[k]! < m then Array.setIfInBounds x (a[k]!) k else x
  have arr_get_other : ∀ (x : Array Nat) (j k : Nat) (v : Nat),
      j ≠ k → k < x.size → (x.setIfInBounds j v)[k]! = x[k]! := by
    intro x j k v hjk hk
    unfold Array.setIfInBounds
    by_cases hj : j < x.size
    · dsimp [getElem!]
      simp [hj, Array.getElem_set, hjk, hk]
    · simp [hj]
  have arr_size : ∀ (x : Array Nat) (k : Nat), k < m → (fstep x k).size = x.size := by
    intro x k hk
    simp [fstep, ha_lt k hk]
  -- Main invariant: for any list l of naturals all < m, for any init array,
  -- for any i ∈ l with i < m, (foldl fstep init l)[a[i]!]! = i.
  -- Stronger loop invariant: for each position a[i]!, the fold either sets it to i (if i ∈ l)
  -- or leaves it equal to init (if i ∉ l). This holds for arbitrary lists (possibly with duplicates).
  -- Key: if i ∈ l, the LAST occurrence of i in l determines the value, and subsequent steps
  -- (processing j with j ≠ i) don't overwrite a[i]! (by injectivity of a).
  -- For i ∉ l, no step writes to a[i]!, so it stays as init.
  have inv : ∀ (l : List Nat) (init : Array Nat),
      init.size = m →
      (∀ k ∈ l, k < m) →
      ∀ i < m, (i ∈ l → (List.foldl fstep init l)[a[i]!]! = i) ∧
                (i ∉ l → (List.foldl fstep init l)[a[i]!]! = init[a[i]!]!) := by
    intro l
    induction l with
    | nil =>
      intro init hinit _ i hi
      simp
    | cons hd tl ihl =>
      intro init hinit halt i hi
      simp only [List.foldl_cons]
      have halt_hd : hd < m := halt hd (List.mem_cons_self)
      have hainj : ∀ x hx y hy, a[x]! = a[y]! → x = y := fun x hx y hy heq => h.inj x hx y hy heq
      -- For any x of size m, if x[a[hd]!]! = hd, then folding over tl preserves this.
      -- Because for each k ∈ tl: either a[k]! ≠ a[hd]! (position untouched), or a[k]! = a[hd]!
      --   which by injectivity means k = hd, so fstep writes hd to a[hd]! (same value).
      have preserve_any_list : ∀ (l : List Nat), (∀ k ∈ l, k < m) →
          ∀ (x : Array Nat), x.size = m → x[a[hd]!]! = hd →
          (List.foldl fstep x l)[a[hd]!]! = hd := by
        intro l
        induction l with
        | nil => simp
        | cons hd2 tl2 ih2 =>
          intro hlt x hx hxval
          simp only [List.foldl_cons]
          have hhd2_lt : hd2 < m := hlt hd2 (List.mem_cons_self)
          by_cases h_eq : a[hd2]! = a[hd]!
          · have hkd : hd2 = hd := hainj hd2 hhd2_lt hd halt_hd h_eq
            rw [hkd]
            simp [fstep, ha_lt hd halt_hd]
            have hfstep_size : (x.setIfInBounds a[hd]! hd).size = m := by
              simp [Array.setIfInBounds, hx, ha_lt hd halt_hd]
            have hfstep_val : (x.setIfInBounds a[hd]! hd)[a[hd]!]! = hd :=
              arr_get_same x (a[hd]!) hd (hx ▸ ha_lt hd halt_hd)
            exact ih2 (fun j hj => hlt j (List.mem_cons.mpr (Or.inr hj)))
              (x.setIfInBounds a[hd]! hd) hfstep_size hfstep_val
          · have hfstep_size : (fstep x hd2).size = m := by rw [arr_size x hd2 hhd2_lt, hx]
            have hfstep_val_at_hd : (fstep x hd2)[a[hd]!]! = x[a[hd]!]! := by
              simp [fstep, ha_lt hd2 hhd2_lt]
              exact arr_get_other x (a[hd2]!) (a[hd]!) hd2 h_eq (hx ▸ ha_lt hd halt_hd)
            exact ih2 (fun j hj => hlt j (List.mem_cons.mpr (Or.inr hj))) (fstep x hd2) hfstep_size (hfstep_val_at_hd ▸ hxval)
      have preserve_hd_val := fun (x : Array Nat) (hx : x.size = m) (hxval : x[a[hd]!]! = hd)
          (htl_lt : ∀ k ∈ tl, k < m) => preserve_any_list tl htl_lt x hx hxval
      by_cases hi_hd : i = hd
      · rw [hi_hd]
        have step_eq : fstep init hd = init.setIfInBounds (a[hd]!) hd := by
          simp [fstep, ha_lt hd halt_hd]
        rw [step_eq]
        have step_val : (init.setIfInBounds (a[hd]!) hd)[a[hd]!]! = hd :=
          arr_get_same init (a[hd]!) hd (hinit ▸ ha_lt hd halt_hd)
        have hsize_step : (init.setIfInBounds (a[hd]!) hd).size = m := by
          simp [Array.setIfInBounds, hinit, ha_lt hd halt_hd]
        exact ⟨fun _ => preserve_hd_val _ hsize_step step_val
          (fun k hk => halt k (List.mem_cons.mpr (Or.inr hk))),
              fun hinil => False.elim (hinil List.mem_cons_self)⟩
      · have hitl_or : i ∈ tl ∨ i ∉ tl := em _
        obtain hitl | hitl := hitl_or
        · have hsize_tl : ∀ k ∈ tl, k < m := fun k hk => halt k (List.mem_cons.mpr (Or.inr hk))
          have ih_result := ihl (fstep init hd) (by rw [arr_size init hd halt_hd, hinit]) hsize_tl i hi
          exact ⟨fun _ => ih_result.1 hitl, fun h => absurd (List.mem_cons.mpr (Or.inr hitl)) h⟩
        · -- i ∉ tl and i ≠ hd, so i ∉ hd :: tl
          have ih_result := ihl (fstep init hd) (by rw [arr_size init hd halt_hd, hinit])
            (fun k hk => halt k (List.mem_cons.mpr (Or.inr hk))) i hi
          have hnot_eq : a[i]! ≠ a[hd]! := by
            intro heq; exact hi_hd (hainj i hi hd halt_hd heq)
          have hstep_preserves_i : (fstep init hd)[a[i]!]! = init[a[i]!]! := by
            simp [fstep, ha_lt hd halt_hd]
            exact arr_get_other init (a[hd]!) (a[i]!) hd hnot_eq.symm (hinit ▸ ha_lt i hi)
          have hinel : i ∈ hd :: tl → False := by
            intro hinil; cases List.mem_cons.mp hinil with
            | inl h => exact hi_hd h
            | inr h => exact hitl h
          exact ⟨fun hinil => False.elim (hinel hinil),
                 fun _ => hstep_preserves_i ▸ ih_result.2 hitl⟩
  -- Main goal: use inv with l = range' 0 m
  have hmem : i ∈ List.range' 0 m := by
    simp [List.mem_range', hi]
  have hall : ∀ k ∈ List.range' 0 m, k < m := by
    intro k hk; simp [List.mem_range'] at hk; exact hk
  exact (inv (List.range' 0 m) (Array.replicate m 0) (by simp) hall i hi).1 hmem

/-- So the run-time check inside `permOfArrays` succeeds, and the permutation it returns is the
array read literally. -/
theorem permOfArrays_val {m : Nat} {a : Array Nat} (h : Canon.IsPerm m fun v => a[v]!)
    (hinv : ∀ i, i < m → (invArray m a)[a[i]!]! = i) (i : Fin m) :
    (permOfArrays m a (invArray m a) i).1 = a[i.1]! := by
  have hmaps : ∀ k : Fin m, a[k.1]! < m := fun k => h.maps _ k.2
  have hfa : ∀ k : Fin m, finFn m a k = ⟨a[k.1]!, hmaps k⟩ := fun k => dif_pos (hmaps k)
  have hb : ∀ k : Fin m, finFn m (invArray m a) ⟨a[k.1]!, hmaps k⟩ = k := by
    intro k
    have hv : (invArray m a)[a[k.1]!]! = k.1 := hinv k.1 k.2
    have hlt : (invArray m a)[(⟨a[k.1]!, hmaps k⟩ : Fin m).1]! < m := by rw [hv]; exact k.2
    exact Fin.ext (by rw [finFn, dif_pos hlt]; exact hv)
  have hleft : ∀ k, finFn m (invArray m a) (finFn m a k) = k := fun k => by rw [hfa k]; exact hb k
  have hinj : Function.Injective fun k : Fin m => (⟨a[k.1]!, hmaps k⟩ : Fin m) := by
    intro x y hxy
    exact Fin.ext (h.inj _ x.2 _ y.2 (congrArg Fin.val hxy))
  have hright : ∀ k, finFn m a (finFn m (invArray m a) k) = k := by
    intro k
    obtain ⟨l, rfl⟩ := Finite.surjective_of_injective hinj k
    rw [hb l, hfa l]
  simp only [permOfArrays, dif_pos (And.intro hleft hright)]
  exact congrArg Fin.val (hfa i)

/-! ### The renaming of `{0, …, n-1}` induced by a permutation of `Fin n` -/

/-- `σ` as a renaming of plain naturals, fixing everything outside the vertex set. -/
def natOfPerm (m : Nat) (σ : Equiv.Perm (Fin m)) (v : Nat) : Nat :=
  if h : v < m then (σ ⟨v, h⟩).1 else v

theorem natOfPerm_lt {m : Nat} (σ : Equiv.Perm (Fin m)) {v : Nat} (hv : v < m) :
    natOfPerm m σ v = (σ ⟨v, hv⟩).1 := dif_pos hv

theorem natOfPerm_isPerm (m : Nat) (σ : Equiv.Perm (Fin m)) : Canon.IsPerm m (natOfPerm m σ) where
  maps v hv := by rw [natOfPerm_lt σ hv]; exact (σ ⟨v, hv⟩).2
  inj v hv w hw hvw := by
    rw [natOfPerm_lt σ hv, natOfPerm_lt σ hw] at hvw
    exact congrArg Fin.val (σ.injective (Fin.ext hvw))

/-- Relabelling a graph on `Fin n` is renaming its oracle. -/
theorem oracleOfFin_relabel (m : Nat) (σ : Equiv.Perm (Fin m)) (adj : Fin m → Fin m → Bool) :
    oracleOfFin m (relabel σ adj) = fun v w => oracleOfFin m adj (natOfPerm m σ v)
      (natOfPerm m σ w) := by
  funext v w
  by_cases hv : v < m
  · by_cases hw : w < m
    · rw [oracleOfFin_apply _ hv hw, natOfPerm_lt σ hv, natOfPerm_lt σ hw,
        oracleOfFin_apply _ (σ ⟨v, hv⟩).2 (σ ⟨w, hw⟩).2, relabel_apply]
    · simp [oracleOfFin, natOfPerm, hv, hw]
  · simp [oracleOfFin, natOfPerm, hv]

/-! ### The reduction -/

/-- Under obligation A, `canonPerm` is the labelling array read literally. -/
theorem canonPerm_val (hA : LabellingIsPerm) (adj : Fin n → Fin n → Bool) (i : Fin n) :
    (canonPerm n adj i).1 = (labelling n (oracleOfFin n adj))[i.1]! :=
  have h := hA n (oracleOfFin n adj)
  permOfArrays_val h.2 (fun k hk => invArray_apply h.1 h.2 k hk) i

/-- The canonical form, evaluated: it is the oracle read at the labelling. -/
theorem canonAdj_eq_oracle (hA : LabellingIsPerm) (adj : Fin n → Fin n → Bool) (i j : Fin n) :
    canonAdj n adj i j
      = oracleOfFin n adj ((labelling n (oracleOfFin n adj))[i.1]!)
          ((labelling n (oracleOfFin n adj))[j.1]!) := by
  have h := hA n (oracleOfFin n adj)
  have hi : canonPerm n adj i = ⟨(labelling n (oracleOfFin n adj))[i.1]!, h.2.maps _ i.2⟩ :=
    Fin.ext (canonPerm_val hA adj i)
  have hj : canonPerm n adj j = ⟨(labelling n (oracleOfFin n adj))[j.1]!, h.2.maps _ j.2⟩ :=
    Fin.ext (canonPerm_val hA adj j)
  rw [canonAdj_apply, hi, hj, oracleOfFin_apply adj (h.2.maps _ i.2) (h.2.maps _ j.2)]

/-- **The reduction.**  Invariance of the canonical form follows from the two array-level
obligations, with nothing else about the algorithm needed. -/
theorem canonAdj_relabel_of (hA : LabellingIsPerm) (hB : LabellingInvariant)
    (σ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) :
    canonAdj n (relabel σ adj) = canonAdj n adj := by
  funext i j
  rw [canonAdj_eq_oracle hA (relabel σ adj) i j, canonAdj_eq_oracle hA adj i j,
    oracleOfFin_relabel n σ adj]
  exact hB n (oracleOfFin n adj) (natOfPerm n σ) (natOfPerm_isPerm n σ) i.1 i.2 j.1 j.2

/-- **Invariance of the canonical form.**  Renaming the vertices of a graph does not change its
canonical form.

Everything else in the development — that `IsoGraph` may be `Quotient.lift`ed through the
canonical form, and hence that graph invariants computed from it are well defined — reduces to
this.  It in turn reduces, by `canonAdj_relabel_of`, to `LabellingIsPerm` — proved, by a run-time
check — and `LabellingInvariant`, which is the deep one and decomposes as follows.  Steps 2, 3 and
4 are done, in `IsoGraph/Equivariance.lean`, as are the first two of step 1's phases; 5 and 6 are
not.

Fix `σ` and write `q ≈ p` for "the ordered partitions `q` and `p` have
the same cell boundaries, and the `i`-th cell of `q` is the `σ`-image of the `i`-th cell of `p`
*as a set*".  (Only as a set: refinement's counting sort is stable, so the order *within* a cell
is inherited from the parent cell and so depends on vertex names, which are not invariant.  What
is invariant is the sequence of cells.)  Then:

1. `refineStep` is `≈`-equivariant: it returns `≈`-related partitions, the same worklist, and the
   same trace hash, because every quantity it hashes (`s`, cell starts, fragment sizes, neighbour
   counts) is determined by positions and multiplicities.  Hence so are `refineLoop`, `refine`
   and `initialRefine` — note `Part.unit n ≈ Part.unit n` for every `σ`, the point being that a
   one-cell partition carries no order information.  *(Partly done: `Canon.cellCount_equiv` is the
   "determined by multiplicities" part and `Canon.countFrom_cellCount` says the counting phase
   computes such a multiplicity, `Canon.countFrom_equiv` combining the two; `Canon.collect_equiv`
   then says the two runs split the same cells in the same order.  The counting sort of each cell
   and the worklist rule that follow are not done.)*
2. `Part.shapeHash` and `Part.targetCell` read only cell boundaries, so they agree on `≈`-related
   partitions.  *(Done: `Canon.shapeHash_congr`, `Canon.targetCell_congr`.)*
3. `individualize p v` and `individualize q (σ v)` produce `≈`-related partitions and the same
   splitter position.  *(Done: `Canon.individualize_partEquiv`, with `Canon.individualize_wf` for
   the well-formedness the next step needs.)*
4. On *discrete* partitions `≈` forces `q.lab = σ ∘ p.lab`, and then `certOf` agrees, since it
   reads the adjacency matrix in exactly that order.  *(Done: `Canon.certOf_relabel`.)*
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
    canonAdj n (relabel σ adj) = canonAdj n adj :=
  canonAdj_relabel_of labellingIsPerm labellingInvariant σ adj

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

/-- Canonical forms of isomorphic graphs agree entrywise, at the level of plain naturals. -/
theorem canonMatrix_get_congr {m k : Nat} (h : m = k) {A : Fin m → Fin m → Bool}
    {B : Fin k → Fin k → Bool} (σ : Fin m ≃ Fin k) (hσ : ∀ a b, B (σ a) (σ b) = A a b) (a b : Nat) :
    (canonMatrix m A).get a b = (canonMatrix k B).get a b :=
  congrFun (congrFun (oracleOfFin_canonAdj_congr h σ hσ) a) b

/-- **The congruence that gets lifted through the quotient in `IsoGraph.Basic`.**  Canonical forms
of isomorphic graphs, moved onto a common index set, are equal — and `N` is arbitrary, so it can
be `Fintype.card V`, which is what makes the lift's motive independent of the listing. -/
theorem canonMatrix_reindex_congr {m k : Nat} (h : m = k) {A : Fin m → Fin m → Bool}
    {B : Fin k → Fin k → Bool} (σ : Fin m ≃ Fin k) (hσ : ∀ a b, B (σ a) (σ b) = A a b) (N : Nat) :
    (canonMatrix m A).reindex N = (canonMatrix k B).reindex N :=
  AdjMatrix.reindex_congr (canonMatrix_get_congr h σ hσ)

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
