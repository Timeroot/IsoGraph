import IsoGraph.Canonical
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

/-!
# Towards invariance: equivariance of the pieces

`IsoGraph/Spec.lean` states the one deep obligation of the development,

```lean
canonAdj n (relabel σ adj) = canonAdj n adj
```

and its docstring records the six-step decomposition it needs.  This file starts turning that
prose into Lean.  It works at the level of `IsoGraph.Canonical`, i.e. with raw `Array Nat`s and
permutations of `{0, …, n-1}` represented as `Nat → Nat`, since that is where the algorithm
lives; the translation to `Equiv.Perm (Fin n)` happens back in `Spec.lean`.

What is here so far is the *bottom* layer: how `Graph.ofOracle` responds to renaming, and the two
readers of a partition (`shapeHash`, `targetCell`) that see only cell boundaries.  These are the
facts every later step is phrased in terms of.  The steps about `refineStep` and about the search
tree are not here yet.
-/

namespace IsoGraph
namespace Canon

/-! ## Permutations of an initial segment -/

/-- `σ` permutes `{0, …, n-1}`: it maps the segment into itself and is injective there.  Since
the segment is finite this is the same as being a bijection of it, but the two clauses are what
the proofs actually use. -/
structure IsPerm (n : Nat) (σ : Nat → Nat) : Prop where
  /-- `σ` maps the segment into itself. -/
  maps : ∀ v, v < n → σ v < n
  /-- `σ` is injective on the segment. -/
  inj : ∀ v, v < n → ∀ w, w < n → σ v = σ w → v = w

theorem IsPerm.id (n : Nat) : IsPerm n _root_.id := ⟨fun _ h => h, fun _ _ _ _ h => h⟩

theorem IsPerm.comp {n : Nat} {σ τ : Nat → Nat} (hσ : IsPerm n σ) (hτ : IsPerm n τ) :
    IsPerm n (fun v => σ (τ v)) :=
  ⟨fun v hv => hσ.maps _ (hτ.maps v hv),
   fun v hv w hw h => hτ.inj v hv w hw (hσ.inj _ (hτ.maps v hv) _ (hτ.maps w hw) h)⟩

/-! ## `Graph.ofOracle`

The algorithm never reads an oracle directly: it reads the `adj` matrix and the `nbr` lists that
`Graph.ofOracle` builds from it.  So every statement about renaming vertices has to pass through
these three lemmas. -/

@[simp] theorem ofOracle_n (n : Nat) (f : Nat → Nat → Bool) : (Graph.ofOracle n f).n = n := by
  rfl

/-- The dense matrix of `Graph.ofOracle` is the oracle, on the intended range. -/
theorem ofOracle_adj (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n) (hw : w < n) :
    ((Graph.ofOracle n f).adj[v]!)[w]! = f v w := by
  sorry

/-- The neighbour lists of `Graph.ofOracle` are the rows of the oracle. -/
theorem ofOracle_mem_nbr (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n) (hw : w < n) :
    w ∈ (Graph.ofOracle n f).nbr[v]! ↔ f v w = true := by
  sorry

/-- Neighbour lists stay inside the vertex set. -/
theorem ofOracle_nbr_lt (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n)
    (hw : w ∈ (Graph.ofOracle n f).nbr[v]!) : w < n := by
  sorry

/-! ## Readers of a partition that see only the cell boundaries

Step 2 of the decomposition: `shapeHash` and `targetCell` walk the partition cell by cell using
`cen` alone, never touching `lab`.  So they agree on any two partitions with the same boundaries
— in particular on partitions related by a renaming of the vertices, whatever that renaming does
inside the cells. -/

theorem shapeHash_congr (n : Nat) (p q : Part) (h : ∀ i, i < n → p.cen[i]! = q.cen[i]!) :
    p.shapeHash n = q.shapeHash n := by
  sorry

theorem targetCell_congr (n : Nat) (p q : Part) (h : ∀ i, i < n → p.cen[i]! = q.cen[i]!) :
    p.targetCell n = q.targetCell n := by
  -- The loop body depends only on cen[cur]! at indices cur < n.
  -- We prove a general statement about the `forIn` loop with state.
  -- Key lemma: for any cur₁ cur₂, if cur₁ = cur₂ and ∀ i < n, p.cen[i]! = q.cen[i]!,
  -- then running the loop from cur₁ with p.cen gives same result as from cur₂ with q.cen.
  -- Since cur always stays < n (or ≥ n causing early exit), cur₁ = cur₂ is maintained.
  -- Unfold `[0:n]` into a recursive form. We induct on `n`.
  have loop_equiv : ∀ (cur : Nat) (m : Nat),
      ∀ (cen1 cen2 : Array Nat), (∀ i < n, cen1[i]! = cen2[i]!) →
      (Id.run do
        let mut cur' := cur
        for _ in [0:m] do
          if cur' ≥ n then break
          let e := cen1[cur']!
          if e - cur' > 1 then return some cur'
          cur' := e
        return none) =
      (Id.run do
        let mut cur' := cur
        for _ in [0:m] do
          if cur' ≥ n then break
          let e := cen2[cur']!
          if e - cur' > 1 then return some cur'
          cur' := e
        return none) := by
    intro cur m cen1 cen2 hcen
    -- All reads of cen happen at indices < n (since we only read when cur' < n)
    -- so cen1[cur']! = cen2[cur']! at every read. Hence the loops are identical.
    -- The body functions are equal pointwise because cen1[r.snd]! = cen2[r.snd]! whenever r.snd < n,
    -- and when r.snd ≥ n the body doesn't read cen.
    let mkBody (cen : Array Nat) : Nat → Option (Option Nat) × Nat → Id (ForInStep (Option (Option Nat) × Nat)) :=
      fun x r =>
        if r.snd ≥ n then pure (ForInStep.done ⟨none, r.snd⟩)
        else do
          pure PUnit.unit
          if cen[r.snd]! - r.snd > 1 then pure (ForInStep.done ⟨some (some r.snd), r.snd⟩)
          else do
            pure PUnit.unit
            pure PUnit.unit
            pure (ForInStep.yield ⟨none, cen[r.snd]!⟩)
    have hbody_eq : mkBody cen1 = mkBody cen2 := by
      funext x r
      dsimp only [mkBody]
      by_cases hsnd : r.snd ≥ n
      · simp [hsnd]
      · push_neg at hsnd
        rw [hcen r.snd hsnd]
    show Id.run _ = Id.run _
    simp only [Id.run]
    congr 2
    funext x r
    by_cases hsnd : r.snd ≥ n
    · simp [hsnd]
    · push_neg at hsnd
      simp [hcen r.snd hsnd]
  show p.targetCell n = q.targetCell n
  exact loop_equiv 0 n p.cen q.cen h

/-- The target cell, when there is one, is a cell start inside the vertex set that is not a
singleton.  (Used to know that individualising is legitimate.) -/
theorem targetCell_lt (n : Nat) (p : Part) (i : Nat) (h : p.targetCell n = some i) : i < n := by
  sorry

/-! ## Certificates

Step 4 of the decomposition, certificate half.  A certificate is the adjacency matrix read in the
order given by `lab`; so renaming the vertices along `σ` and reading in the order `lab` gives the
same bits as leaving the graph alone and reading in the order `σ ∘ lab`.  This is the point at
which "the search found corresponding leaves" turns into "the two runs return the same array". -/

/-- `certOf` reads the adjacency matrix only at the pairs named by `lab`. -/
theorem certOf_congr (G H : Graph) (lab lab' : Array Nat) (hn : G.n = H.n)
    (hlab : ∀ i, i < G.n → ∀ j, j < G.n → (G.adj[lab[i]!]!)[lab[j]!]! = (H.adj[lab'[i]!]!)[lab'[j]!]!) :
    certOf G lab = certOf H lab' := by
  sorry

/-- **Certificates are equivariant.**  Reading the renamed graph along `lab` is reading the
original along `σ ∘ lab`. -/
theorem certOf_relabel (n : Nat) (f : Nat → Nat → Bool) (σ : Nat → Nat) (hσ : IsPerm n σ)
    (lab : Array Nat) (hsz : lab.size = n) (hlab : ∀ i, i < n → lab[i]! < n) :
    certOf (Graph.ofOracle n (fun v w => f (σ v) (σ w))) lab
      = certOf (Graph.ofOracle n f) (lab.map σ) := by
  sorry

end Canon
end IsoGraph
