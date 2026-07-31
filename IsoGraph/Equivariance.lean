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
@[simp] theorem ofOracle_adj (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n)
    (hw : w < n) : ((Graph.ofOracle n f).adj[v]!)[w]! = f v w := by
  simp [Graph.ofOracle, getElem!_pos, hv, hw]

/-- A neighbour list of `Graph.ofOracle` is the row of the oracle, as a filtered range. -/
theorem ofOracle_nbr (n : Nat) (f : Nat → Nat → Bool) (v : Nat) (hv : v < n) :
    (Graph.ofOracle n f).nbr[v]! = (Array.range n).filter (f v) := by
  simp [Graph.ofOracle, getElem!_pos, hv]

/-- The neighbour lists of `Graph.ofOracle` are the rows of the oracle. -/
theorem ofOracle_mem_nbr (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n) (hw : w < n) :
    w ∈ (Graph.ofOracle n f).nbr[v]! ↔ f v w = true := by
  rw [ofOracle_nbr n f v hv, Array.mem_filter, Array.mem_range]
  simp [hw]

/-- Neighbour lists stay inside the vertex set. -/
theorem ofOracle_nbr_lt (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n)
    (hw : w ∈ (Graph.ofOracle n f).nbr[v]!) : w < n := by
  rw [ofOracle_nbr n f v hv, Array.mem_filter, Array.mem_range] at hw
  exact hw.1

/-! ## Readers of a partition that see only the cell boundaries

Step 2 of the decomposition: `shapeHash` and `targetCell` walk the partition cell by cell using
`cen` alone, never touching `lab`.  So they agree on any two partitions with the same boundaries
— in particular on partitions related by a renaming of the vertices, whatever that renaming does
inside the cells. -/

/-- The cell walk only ever reads `cen` at indices `< n`, so two `cen`s that agree there send it
along the same path.  Both congruence lemmas below are this observation at `fuel = n`, `i = 0`. -/
theorem cenHashFrom_congr {n : Nat} {c d : Array Nat} (h : ∀ i, i < n → c[i]! = d[i]!) :
    ∀ (fuel i : Nat) (x : UInt64), cenHashFrom c n fuel i x = cenHashFrom d n fuel i x
  | 0, _, _ => rfl
  | fuel + 1, i, x => by
    rw [cenHashFrom, cenHashFrom]
    by_cases hi : i ≥ n
    · simp [hi]
    · rw [h i (Nat.lt_of_not_le hi)]
      simpa [hi] using cenHashFrom_congr h fuel d[i]! (mixN x (d[i]! - i))

theorem cenTargetFrom_congr {n : Nat} {c d : Array Nat} (h : ∀ i, i < n → c[i]! = d[i]!) :
    ∀ (fuel i : Nat), cenTargetFrom c n fuel i = cenTargetFrom d n fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    rw [cenTargetFrom, cenTargetFrom]
    by_cases hi : i ≥ n
    · simp [hi]
    · rw [h i (Nat.lt_of_not_le hi)]
      simp only [if_neg hi]
      by_cases hd : d[i]! - i > 1
      · simp [hd]
      · simp [hd, cenTargetFrom_congr h fuel d[i]!]

theorem shapeHash_congr (n : Nat) (p q : Part) (h : ∀ i, i < n → p.cen[i]! = q.cen[i]!) :
    p.shapeHash n = q.shapeHash n :=
  cenHashFrom_congr h n 0 hashSeed

theorem targetCell_congr (n : Nat) (p q : Part) (h : ∀ i, i < n → p.cen[i]! = q.cen[i]!) :
    p.targetCell n = q.targetCell n :=
  cenTargetFrom_congr h n 0

/-- The walk only reports a cell start it has already checked is `< n`. -/
theorem cenTargetFrom_lt {n : Nat} {c : Array Nat} :
    ∀ (fuel i j : Nat), cenTargetFrom c n fuel i = some j → j < n
  | 0, _, _, h => by simp [cenTargetFrom] at h
  | fuel + 1, i, j, h => by
    rw [cenTargetFrom] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hi
      split at h
      · cases h; exact Nat.lt_of_not_le hi
      · exact cenTargetFrom_lt fuel c[i]! j h

/-- The target cell, when there is one, is a cell start inside the vertex set that is not a
singleton.  (Used to know that individualising is legitimate.) -/
theorem targetCell_lt (n : Nat) (p : Part) (i : Nat) (h : p.targetCell n = some i) : i < n :=
  cenTargetFrom_lt n 0 i h

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
