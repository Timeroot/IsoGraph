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

What is here is the bottom layer and the two steps that rest directly on it:

* how `Graph.ofOracle` responds to renaming, and the fact that the labelling really is a
  permutation (which `canonicalLabellingOfOracle` checks at run time);
* **step 2** — the two readers of a partition, `shapeHash` and `targetCell`, see only cell
  boundaries, so they agree on partitions related by any renaming;
* `PartEquiv`, the relation "same partition up to renaming" that the whole decomposition is
  phrased in;
* **step 4** — two runs that reach related *discrete* partitions read off the same certificate
  (`certOf_of_partEquiv`, via `certOf_relabel`).

Steps 1, 3, 5 and 6 — equivariance of `refineStep` and of `individualize`, and the argument that
the maximum over the leaves does not depend on the order children are enumerated in — are not
here yet.
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

/-- The identity labelling is a permutation — the fallback branch of
`canonicalLabellingOfOracle`. -/
theorem range_isPerm (n : Nat) :
    (Array.range n).size = n ∧ IsPerm n (fun v => (Array.range n)[v]!) := by
  refine ⟨by simp, ⟨fun v hv => ?_, fun v hv w hw h => ?_⟩⟩
  · rw [getElem!_pos _ _ (by simpa using hv)]; simpa using hv
  · rw [getElem!_pos _ _ (by simpa using hv), getElem!_pos _ _ (by simpa using hw)] at h
    simpa using h

/-- `isPermArray` is sound: what it accepts really is a permutation of `{0, …, n-1}`.  (It is
also complete, but nothing below needs that — an unsound accept would be the problem.) -/
theorem isPermArray_spec {n : Nat} {a : Array Nat} (h : isPermArray n a = true) :
    a.size = n ∧ IsPerm n (fun v => a[v]!) := by
  simp only [isPermArray, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hsz, hall⟩ := h
  refine ⟨hsz, ⟨fun v hv => (hall v hv).1, fun v hv w hw hvw => ?_⟩⟩
  have hv2 := (hall v hv).2
  rw [hvw, (hall w hw).2] at hv2
  exact hv2.symm

/-- **The labelling really is a labelling.**  Not because the search is known to produce one —
that is still open — but because `canonicalLabellingOfOracle` checks, and falls back to the
identity if the check fails. -/
theorem canonicalLabellingOfOracle_isPerm (n : Nat) (f : Nat → Nat → Bool) :
    (canonicalLabellingOfOracle n f).size = n ∧
      IsPerm n (fun v => (canonicalLabellingOfOracle n f)[v]!) := by
  -- stated for an arbitrary `a` so that `split` sees the `if`, then applied to the search output
  have h : ∀ a : Array Nat,
      (if isPermArray n a then a else Array.range n).size = n ∧
        IsPerm n (fun v => (if isPermArray n a then a else Array.range n)[v]!) := by
    intro a
    split
    · exact isPermArray_spec (by assumption)
    · exact range_isPerm n
  exact h _

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

/-- One packed row only reads columns `j < n`.  The fuel invariant `j + fuel = n` is what makes
that available: it says the loop is at position `j` with `fuel` columns left, so `fuel ≥ 1`
forces `j < n`. -/
theorem certRow_congr {n : Nat} {b b' : Nat → Bool} (h : ∀ j, j < n → b j = b' j) :
    ∀ (fuel j : Nat) (acc : UInt64) (k : Nat) (out : Array UInt64), j + fuel = n →
      certRow n b fuel j acc k out = certRow n b' fuel j acc k out
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, j, acc, k, out, hj => by
    simp only [certRow, h j (by omega)]
    split <;> exact certRow_congr h fuel (j + 1) _ _ _ (by omega)

/-- The same for the rows: row `i` is packed only for `i < n`. -/
theorem certRowsFrom_congr {n : Nat} {b b' : Nat → Nat → Bool} (w : Nat)
    (h : ∀ i, i < n → ∀ j, j < n → b i j = b' i j) :
    ∀ (fuel i : Nat) (out : Array UInt64), i + fuel = n →
      certRowsFrom n b w fuel i out = certRowsFrom n b' w fuel i out
  | 0, _, _, _ => rfl
  | fuel + 1, i, out, hi => by
    rw [certRowsFrom, certRowsFrom,
      certRow_congr (h i (by omega)) n 0 0 (i * w) out (Nat.zero_add n)]
    exact certRowsFrom_congr w h fuel (i + 1) _ (by omega)

/-- `certBits` reads the matrix only inside `{0, …, n-1}²`. -/
theorem certBits_congr (n : Nat) (b b' : Nat → Nat → Bool)
    (h : ∀ i, i < n → ∀ j, j < n → b i j = b' i j) : certBits n b = certBits n b' :=
  certRowsFrom_congr _ h n 0 _ (Nat.zero_add n)

theorem certOf_eq (G : Graph) (lab : Array Nat) :
    certOf G lab = certBits G.n fun i j => (G.adj[lab[i]!]!)[lab[j]!]! := rfl

/-- `certOf` reads the adjacency matrix only at the pairs named by `lab`. -/
theorem certOf_congr (G H : Graph) (lab lab' : Array Nat) (hn : G.n = H.n)
    (hlab : ∀ i, i < G.n → ∀ j, j < G.n →
      (G.adj[lab[i]!]!)[lab[j]!]! = (H.adj[lab'[i]!]!)[lab'[j]!]!) :
    certOf G lab = certOf H lab' := by
  rw [certOf_eq, certOf_eq, ← hn]
  exact certBits_congr _ _ _ hlab

/-- **Certificates are equivariant.**  Reading the renamed graph along `lab` is reading the
original along `σ ∘ lab`. -/
theorem certOf_relabel (n : Nat) (f : Nat → Nat → Bool) (σ : Nat → Nat) (hσ : IsPerm n σ)
    (lab : Array Nat) (hsz : lab.size = n) (hlab : ∀ i, i < n → lab[i]! < n) :
    certOf (Graph.ofOracle n (fun v w => f (σ v) (σ w))) lab
      = certOf (Graph.ofOracle n f) (lab.map σ) := by
  have hmap : ∀ i, i < n → (lab.map σ)[i]! = σ lab[i]! := by
    intro i hi
    rw [getElem!_pos _ _ (by simpa [hsz] using hi), getElem!_pos _ _ (by omega)]
    simp
  refine certOf_congr _ _ _ _ rfl fun i hi j hj => ?_
  rw [ofOracle_n] at hi hj
  rw [ofOracle_adj n _ _ _ (hlab i hi) (hlab j hj), hmap i hi, hmap j hj,
    ofOracle_adj n f _ _ (hσ.maps _ (hlab i hi)) (hσ.maps _ (hlab j hj))]

/-! ## Partitions related by a renaming

The vocabulary the rest of the decomposition is phrased in.  Fix a renaming `σ` and think of two
runs of the algorithm: one on `f`, one on the graph `fun v w => f (σ v) (σ w)` whose vertex `v`
"is" vertex `σ v` of the first.  The two runs do *not* produce partitions that agree positionwise
under `σ` — they both start from `Part.unit n`, whose `lab` is `Array.range n` in either run, and
refinement's counting sort is stable, so the order *within* a cell is inherited from the parent
and depends on vertex names.  What they do produce is partitions whose cells sit at the same
positions and correspond as *sets*, which is what `PartEquiv` says. -/

/-- `p` is a well-formed ordered partition of `{0, …, n-1}`: `lab` and `pos` are mutually inverse
bijections of the segment. -/
structure Part.WF (n : Nat) (p : Part) : Prop where
  /-- Positions hold vertices of the segment. -/
  labLt : ∀ i, i < n → p.lab[i]! < n
  /-- Vertices sit at positions in the segment. -/
  posLt : ∀ v, v < n → p.pos[v]! < n
  /-- `pos` is a left inverse of `lab`. -/
  posLab : ∀ i, i < n → p.pos[p.lab[i]!]! = i
  /-- `lab` is a left inverse of `pos`. -/
  labPos : ∀ v, v < n → p.lab[p.pos[v]!]! = v

/-- `p` is discrete: every cell is a singleton, so each position is its own cell start. -/
def Part.Discrete (n : Nat) (p : Part) : Prop := ∀ i, i < n → p.cst[i]! = i

/-- `p` and `q` are the same ordered partition up to the renaming `σ`: the cells occupy the same
ranges of positions, and vertex `v` of `q`'s graph lies in the cell where `σ v` lies in `p`.

The third clause is how "the cells correspond as sets" is said pointwise: a cell is named by its
start position, so it asserts that `σ` maps the cell of `v` in `q` onto the cell at the same
place in `p`. -/
structure PartEquiv (n : Nat) (σ : Nat → Nat) (p q : Part) : Prop where
  /-- Cells start at the same positions. -/
  cst : ∀ i, i < n → p.cst[i]! = q.cst[i]!
  /-- Cells end at the same positions. -/
  cen : ∀ i, i < n → p.cen[i]! = q.cen[i]!
  /-- `σ` carries the cell of `v` in `q` to the cell at the same position in `p`. -/
  cell : ∀ v, v < n → p.cst[p.pos[σ v]!]! = q.cst[q.pos[v]!]!

/-- Related partitions have the same cell-size hash. -/
theorem PartEquiv.shapeHash {n σ p q} (h : PartEquiv n σ p q) : p.shapeHash n = q.shapeHash n :=
  shapeHash_congr n p q h.cen

/-- Related partitions individualise at the same position. -/
theorem PartEquiv.targetCell {n σ p q} (h : PartEquiv n σ p q) :
    p.targetCell n = q.targetCell n :=
  targetCell_congr n p q h.cen

/-- The unit partition is related to itself under every renaming: one cell carries no order
information. -/
theorem partEquiv_unit (n : Nat) (σ : Nat → Nat) :
    PartEquiv n σ (Part.unit n) (Part.unit n) := by
  have hcst : ∀ i : Nat, (Part.unit n).cst[i]! = 0 := by
    intro i
    show (Array.replicate n 0)[i]! = 0
    by_cases h : i < n
    · rw [getElem!_pos (Array.replicate n 0) i (by simpa using h)]; simp
    · rw [getElem!_neg (Array.replicate n 0) i (by simpa using h)]; rfl
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => (hcst _).trans (hcst _).symm⟩

/-- **Once the partitions are discrete, `σ` relates the labellings positionwise.**  This is where
"cells correspond as sets" turns into an equation between arrays: a singleton cell has only one
member, so there is nothing left for the stable sort to have permuted. -/
theorem lab_eq_of_discrete {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (hp : Part.WF n p) (hq : Part.WF n q) (hpd : p.Discrete n) (hqd : q.Discrete n)
    (h : PartEquiv n σ p q) (i : Nat) (hi : i < n) : p.lab[i]! = σ q.lab[i]! := by
  have hv : q.lab[i]! < n := hq.labLt i hi
  have hσv : σ q.lab[i]! < n := hσ.maps _ hv
  have hc := h.cell q.lab[i]! hv
  rw [hq.posLab i hi, hqd i hi, hpd _ (hp.posLt _ hσv)] at hc
  calc p.lab[i]! = p.lab[p.pos[σ q.lab[i]!]!]! := by rw [hc]
    _ = σ q.lab[i]! := hp.labPos _ hσv

/-- **Step 4 of the decomposition.**  Two runs that reach related discrete partitions read off
the same certificate — the renamed graph along `q.lab` is the original along `p.lab`.  This is
the point at which "the search found corresponding leaves" becomes "the two runs return the same
array". -/
theorem certOf_of_partEquiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (hp : Part.WF n p) (hq : Part.WF n q) (hpd : p.Discrete n) (hqd : q.Discrete n)
    (hqsz : q.lab.size = n) (h : PartEquiv n σ p q) (f : Nat → Nat → Bool) :
    certOf (Graph.ofOracle n fun v w => f (σ v) (σ w)) q.lab
      = certOf (Graph.ofOracle n f) p.lab := by
  rw [certOf_relabel n f σ hσ q.lab hqsz fun i hi => hq.labLt i hi]
  refine certOf_congr _ _ _ _ rfl fun i hi j hj => ?_
  rw [ofOracle_n] at hi hj
  have hmap : ∀ k, k < n → (q.lab.map σ)[k]! = p.lab[k]! := by
    intro k hk
    have h1 : (q.lab.map σ)[k]! = σ q.lab[k]! := by
      rw [getElem!_pos (q.lab.map σ) k (by simpa [hqsz] using hk),
        getElem!_pos q.lab k (by omega)]
      simp
    rw [h1, ← lab_eq_of_discrete hσ hp hq hpd hqd h k hk]
  rw [hmap i hi, hmap j hj]

end Canon
end IsoGraph
