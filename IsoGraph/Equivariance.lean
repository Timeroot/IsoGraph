import IsoGraph.Canonical
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Intervals
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

What is here is the bottom layer and the steps that rest directly on it:

* how `Graph.ofOracle` responds to renaming, and the fact that the labelling really is a
  permutation (which `canonicalLabellingOfOracle` checks at run time);
* `Part.WF` and `PartEquiv`, the vocabulary — "well-formed ordered partition" and "the same
  partition up to renaming" — that the whole decomposition is phrased in;
* the first two phases of **step 1** — `cellCount_equiv`, that corresponding cells agree on every
  count, together with `countFrom_cellCount`, that `refineStep`'s counting phase computes exactly
  such a count (`countFrom_equiv` combines them), and `countFrom_mem_touched`, that the set of
  vertices the phase records is invariant too; then `collect_equiv`, that the two runs go on to
  split the very same list of cells, in the very same order;
* **step 2** — the two readers of a partition, `shapeHash` and `targetCell`, see only cell
  boundaries, so they agree on partitions related by any renaming;
* **step 3** — individualising corresponding vertices of related partitions gives related
  partitions, at the same position (`individualize_partEquiv`), and preserves well-formedness;
* **step 4** — two runs that reach related *discrete* partitions read off the same certificate
  (`certOf_of_partEquiv`, via `certOf_relabel`), with `discrete_of_targetCell_none` supplying
  the discreteness at the leaves.

What is *not* here: the rest of `refineStep` after the collection phase — the counting sort of
each cell, the fragment boundaries and Hopcroft's worklist rule (the rest of step 1) — the
correspondence of the two search trees (step 5), and the argument that the maximum over the leaves
does not depend on the order children are enumerated in (step 6).
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

/-- The number of neighbour lists is the number of vertices. -/
@[simp] theorem ofOracle_nbr_size (n : Nat) (f : Nat → Nat → Bool) :
    (Graph.ofOracle n f).nbr.size = n := by simp [Graph.ofOracle]

/-- Neighbour lists stay inside the vertex set, with no hypothesis on the vertex: out of range
`nbr[u]!` is the empty array, which has no members either. -/
theorem ofOracle_nbr_lt' (n : Nat) (f : Nat → Nat → Bool) (u x : Nat)
    (hx : x ∈ (Graph.ofOracle n f).nbr[u]!) : x < n := by
  by_cases hu : u < n
  · exact ofOracle_nbr_lt n f u x hu hx
  · rw [getElem!_neg _ _ (by simp; omega),
      show (default : Array Nat) = #[] from rfl] at hx
    simp at hx

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
bijections of the segment, and `cst`/`cen` mark off a decomposition of it into intervals.

The last two clauses are what make `cst`/`cen` describe *cells* rather than arbitrary bounds: the
interval `[cst[i], cen[i])` is the same for every `i` inside it, so `cst[i]` is a well-defined name
for the cell containing position `i`. -/
structure Part.WF (n : Nat) (p : Part) : Prop where
  /-- `lab` covers the segment. -/
  labSize : p.lab.size = n
  /-- `pos` covers the segment. -/
  posSize : p.pos.size = n
  /-- `cst` covers the segment. -/
  cstSize : p.cst.size = n
  /-- `cen` covers the segment. -/
  cenSize : p.cen.size = n
  /-- Positions hold vertices of the segment. -/
  labLt : ∀ i, i < n → p.lab[i]! < n
  /-- Vertices sit at positions in the segment. -/
  posLt : ∀ v, v < n → p.pos[v]! < n
  /-- `pos` is a left inverse of `lab`. -/
  posLab : ∀ i, i < n → p.pos[p.lab[i]!]! = i
  /-- `lab` is a left inverse of `pos`. -/
  labPos : ∀ v, v < n → p.lab[p.pos[v]!]! = v
  /-- A cell starts at or before each of its positions. -/
  cstLe : ∀ i, i < n → p.cst[i]! ≤ i
  /-- A cell ends after each of its positions. -/
  ltCen : ∀ i, i < n → i < p.cen[i]!
  /-- Cells stay inside the segment. -/
  cenLe : ∀ i, i < n → p.cen[i]! ≤ n
  /-- Every position of a cell reports the same start. -/
  cellCst : ∀ i, i < n → ∀ j, p.cst[i]! ≤ j → j < p.cen[i]! → p.cst[j]! = p.cst[i]!
  /-- Every position of a cell reports the same end. -/
  cellCen : ∀ i, i < n → ∀ j, p.cst[i]! ≤ j → j < p.cen[i]! → p.cen[j]! = p.cen[i]!

/-- **Cells are determined by their starts.**  Two positions report the same cell start exactly
when they lie in the same interval — so `cst` really is a set-theoretic partition of positions,
not just a monotone pair of arrays.  This is the workhorse behind `individualize_cell`. -/
theorem Part.WF.cst_eq_iff {n : Nat} {p : Part} (hp : Part.WF n p) {i : Nat} (hi : i < n)
    {k : Nat} (hk : k < n) : p.cst[k]! = p.cst[i]! ↔ (p.cst[i]! ≤ k ∧ k < p.cen[i]!) := by
  refine ⟨fun h => ⟨h ▸ hp.cstLe k hk, ?_⟩, fun h => hp.cellCst i hi k h.1 h.2⟩
  by_contra hke
  -- if `k` sat past the end of `i`'s cell, the position `cen[i] - 1` would be in both cells, and
  -- reading `cen` there would give both `cen[i]` and `cen[k] > k ≥ cen[i]`
  have h1 : p.cst[i]! ≤ i := hp.cstLe i hi
  have h2 : i < p.cen[i]! := hp.ltCen i hi
  have h3 : k < p.cen[k]! := hp.ltCen k hk
  have h4 := hp.cellCen k hk (p.cen[i]! - 1) (by omega) (by omega)
  have h5 := hp.cellCen i hi (p.cen[i]! - 1) (by omega) (by omega)
  omega

/-- `p` is discrete: every cell is a singleton, so each position is its own cell start. -/
def Part.Discrete (n : Nat) (p : Part) : Prop := ∀ i, i < n → p.cst[i]! = i

/-- The position after a singleton cell starts the next one. -/
theorem cst_succ {n : Nat} {p : Part} (hp : Part.WF n p) {i : Nat}
    (hcen : p.cen[i]! = i + 1) (h : i + 1 < n) : p.cst[i + 1]! = i + 1 := by
  have h1 : p.cst[i + 1]! ≤ i + 1 := hp.cstLe _ h
  by_contra hne
  have h3 : i + 1 < p.cen[i + 1]! := hp.ltCen _ h
  -- if `i + 1` were inside an earlier cell, that cell would contain `i` too, and so would end
  -- where `i`'s cell ends — at `i + 1`
  have h5 : p.cen[i]! = p.cen[i + 1]! := hp.cellCen (i + 1) h i (by omega) (by omega)
  omega

/-- The cell walk reaches `n` only by stepping through singletons. -/
theorem cenTargetFrom_none {n : Nat} {p : Part} (hp : Part.WF n p) :
    ∀ (fuel i : Nat), n ≤ i + fuel → (i < n → p.cst[i]! = i) →
      cenTargetFrom p.cen n fuel i = none → ∀ k, i ≤ k → k < n → p.cst[k]! = k
  | 0, _, _, _, _, _, _, _ => by omega
  | fuel + 1, i, hf, hst, h, k, hk1, hk2 => by
    rw [cenTargetFrom] at h
    by_cases hi : i ≥ n
    · omega
    rw [if_neg hi] at h
    have hcst := hst (by omega)
    have hlt := hp.ltCen i (by omega)
    by_cases hd : p.cen[i]! - i > 1
    · rw [if_pos hd] at h; simp at h
    rw [if_neg hd] at h
    have hcen : p.cen[i]! = i + 1 := by omega
    rw [hcen] at h
    by_cases hki : k = i
    · rw [hki]; exact hcst
    · exact cenTargetFrom_none hp fuel (i + 1) (by omega)
        (fun hn => cst_succ hp hcen hn) h k (by omega) hk2

/-- **A partition the walk finds no target in is discrete.**  This is what discharges the
`Discrete` hypotheses of step 4 at the leaves of the search: the algorithm stops individualising
exactly when `targetCell` returns `none`, and that is the same condition. -/
theorem discrete_of_targetCell_none {n : Nat} {p : Part} (hp : Part.WF n p)
    (h : p.targetCell n = none) : p.Discrete n := by
  intro k hk
  refine cenTargetFrom_none hp n 0 (by omega) (fun h0 => ?_) h k (Nat.zero_le k) hk
  have := hp.cstLe 0 h0
  omega

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

/-- The search starts from a well-formed partition: one cell, `[0, n)`, in vertex order. -/
theorem unit_wf (n : Nat) : Part.WF n (Part.unit n) := by
  have hlab : (Part.unit n).lab = Array.range n := rfl
  have hpos : (Part.unit n).pos = Array.range n := rfl
  have hcst : (Part.unit n).cst = Array.replicate n 0 := rfl
  have hcen : (Part.unit n).cen = Array.replicate n n := rfl
  have hr : ∀ i, i < n → (Array.range n)[i]! = i := by
    intro i hi; rw [getElem!_pos _ _ (by simpa using hi)]; simp
  have hrep : ∀ (x i : Nat), i < n → (Array.replicate n x)[i]! = x := by
    intro x i hi; rw [getElem!_pos _ _ (by simpa using hi)]; simp
  refine ⟨by rw [hlab]; simp, by rw [hpos]; simp, by rw [hcst]; simp, by rw [hcen]; simp,
    fun i hi => by rw [hlab, hr i hi]; exact hi,
    fun v hv => by rw [hpos, hr v hv]; exact hv,
    fun i hi => by rw [hlab, hr i hi, hpos]; exact hr i hi,
    fun v hv => by rw [hpos, hr v hv, hlab]; exact hr v hv,
    fun i hi => by rw [hcst, hrep 0 i hi]; exact Nat.zero_le i,
    fun i hi => by rw [hcen, hrep n i hi]; exact hi,
    fun i hi => by rw [hcen, hrep n i hi], fun i hi j h1 h2 => ?_, fun i hi j h1 h2 => ?_⟩
  · rw [hcen, hrep n i hi] at h2
    rw [hcst, hrep 0 j h2, hrep 0 i hi]
  · rw [hcen, hrep n i hi] at h2
    rw [hcen, hrep n j h2, hrep n i hi]

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
    (h : PartEquiv n σ p q) (f : Nat → Nat → Bool) :
    certOf (Graph.ofOracle n fun v w => f (σ v) (σ w)) q.lab
      = certOf (Graph.ofOracle n f) p.lab := by
  have hqsz := hq.labSize
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

/-! ## Step 3 of the decomposition: individualisation

`individualize p v` splits `v` off to the front of its cell.  The two runs pick *different*
vertices to displace — `p.lab[c]` need not be `σ (q.lab[c])`, since the order inside a cell is
name-dependent — so the arrays are genuinely different.  What survives is exactly what `PartEquiv`
records: the cell boundaries move the same way, and a vertex other than the individualised one
lands in the second fragment of the old cell precisely when it was in that cell to begin with. -/

/-- Reading one entry of `Array.set!`, the only fact about it these proofs need. -/
theorem getElem!_set! {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (hi : i < a.size) (k : Nat) :
    (a.set! i x)[k]! = if k = i then x else a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk, eq_comm (a := i)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk,
      if_neg (by omega)]

theorem setCstFrom_size (c ec : Nat) :
    ∀ (fuel j : Nat) (cst : Array Nat), (setCstFrom c ec fuel j cst).size = cst.size
  | 0, _, _ => rfl
  | fuel + 1, j, cst => by
    rw [setCstFrom]
    split
    · rfl
    · rw [setCstFrom_size c ec fuel (j + 1) _]; simp

theorem setCstFrom_getElem! {c ec : Nat} {cst : Array Nat} (hec : ec ≤ cst.size) :
    ∀ (fuel j : Nat), ec ≤ j + fuel → ∀ k,
      (setCstFrom c ec fuel j cst)[k]! = if j ≤ k ∧ k < ec then c + 1 else cst[k]!
  | 0, j, hf, k => by rw [setCstFrom, if_neg (by omega)]
  | fuel + 1, j, hf, k => by
    rw [setCstFrom]
    split
    · rw [if_neg (by omega)]
    · rename_i hj
      rw [setCstFrom_getElem! (by simpa using hec) fuel (j + 1) (by omega) k,
        getElem!_set! (by omega) k]
      by_cases h1 : j + 1 ≤ k ∧ k < ec
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1]
        by_cases h2 : k = j
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]

section Individualize

variable {n : Nat} {p : Part} {v i c ec u : Nat}

/-- The position returned by `individualize` is the start of the cell that was split. -/
theorem individualize_snd (p : Part) (v : Nat) : (individualize p v).2 = p.cst[p.pos[v]!]! := rfl

theorem individualize_lab_eq (p : Part) (v : Nat) : (individualize p v).1.lab
    = (p.lab.set! (p.cst[p.pos[v]!]!) v).set! (p.pos[v]!) (p.lab[p.cst[p.pos[v]!]!]!) := rfl

theorem individualize_pos_eq (p : Part) (v : Nat) : (individualize p v).1.pos
    = (p.pos.set! v (p.cst[p.pos[v]!]!)).set! (p.lab[p.cst[p.pos[v]!]!]!) (p.pos[v]!) := rfl

theorem individualize_cst_eq (p : Part) (v : Nat) : (individualize p v).1.cst
    = setCstFrom (p.cst[p.pos[v]!]!) (p.cen[p.pos[v]!]!)
        (p.cen[p.pos[v]!]! - (p.cst[p.pos[v]!]! + 1)) (p.cst[p.pos[v]!]! + 1) p.cst := rfl

theorem individualize_cen_eq (p : Part) (v : Nat) : (individualize p v).1.cen
    = p.cen.set! (p.cst[p.pos[v]!]!) (p.cst[p.pos[v]!]! + 1) := rfl

/-- The facts about `p` that every statement below is phrased in: `v` sits at position `i`, whose
cell is `[c, ec)`, and `u` is the vertex displaced from the front of that cell. -/
structure IndivData (n : Nat) (p : Part) (v i c ec u : Nat) : Prop where
  /-- `v` is a vertex of the segment. -/
  vLt : v < n
  /-- `i` is where `v` sits. -/
  posv : p.pos[v]! = i
  /-- `c` is the start of `i`'s cell. -/
  csti : p.cst[i]! = c
  /-- `ec` is its end. -/
  ceni : p.cen[i]! = ec
  /-- `u` is the vertex at the front of it. -/
  labc : p.lab[c]! = u

namespace IndivData

variable (hp : Part.WF n p) (hd : IndivData n p v i c ec u)
include hp hd

theorem iLt : i < n := hd.posv ▸ hp.posLt v hd.vLt
theorem cLe : c ≤ i := hd.csti ▸ hp.cstLe i (iLt hp hd)
theorem iLtEc : i < ec := hd.ceni ▸ hp.ltCen i (iLt hp hd)
theorem ecLe : ec ≤ n := hd.ceni ▸ hp.cenLe i (iLt hp hd)
theorem cLt : c < n := by have := cLe hp hd; have := iLt hp hd; omega

/-- The cell start is its own cell start. -/
theorem cstc : p.cst[c]! = c := by
  have h1 := cLe hp hd
  have h2 := iLtEc hp hd
  have h := hp.cellCst i (iLt hp hd) c (by rw [hd.csti]) (by rw [hd.ceni]; omega)
  rw [h, hd.csti]

theorem uLt : u < n := hd.labc ▸ hp.labLt c (cLt hp hd)

/-- The displaced vertex sits at the front of the cell. -/
theorem posu : p.pos[u]! = c := by rw [← hd.labc]; exact hp.posLab c (cLt hp hd)

/-- Membership in the split cell is visible from `cst` alone. -/
theorem mem_iff {k : Nat} (hk : k < n) : p.cst[k]! = c ↔ (c ≤ k ∧ k < ec) := by
  rw [← hd.csti, ← hd.ceni]; exact hp.cst_eq_iff (iLt hp hd) hk

theorem cst_eq {k : Nat} (h1 : c ≤ k) (h2 : k < ec) : p.cst[k]! = c := by
  have h := hp.cellCst i (iLt hp hd) k (by rw [hd.csti]; exact h1) (by rw [hd.ceni]; exact h2)
  rw [h, hd.csti]

theorem cen_eq {k : Nat} (h1 : c ≤ k) (h2 : k < ec) : p.cen[k]! = ec := by
  have h := hp.cellCen i (iLt hp hd) k (by rw [hd.csti]; exact h1) (by rw [hd.ceni]; exact h2)
  rw [h, hd.ceni]

end IndivData

/-- After individualisation the old cell `[c, ec)` has been cut into `{c}` and `[c+1, ec)`. -/
theorem individualize_cst_getElem! (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (k : Nat) :
    (individualize p v).1.cst[k]! = if c + 1 ≤ k ∧ k < ec then c + 1 else p.cst[k]! := by
  rw [individualize_cst_eq, hd.posv, hd.csti, hd.ceni]
  exact setCstFrom_getElem! (by rw [hp.cstSize]; exact hd.ecLe hp) _ _ (by omega) k

theorem individualize_cen_getElem! (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (k : Nat) :
    (individualize p v).1.cen[k]! = if k = c then c + 1 else p.cen[k]! := by
  rw [individualize_cen_eq, hd.posv, hd.csti]
  exact getElem!_set! (by rw [hp.cenSize]; exact hd.cLt hp) k

theorem individualize_pos_getElem! (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (w : Nat) :
    (individualize p v).1.pos[w]! = if w = u then i else if w = v then c else p.pos[w]! := by
  have h1 : u < (p.pos.set! v c).size := by
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hp.posSize]
    exact hd.uLt hp
  have h2 : v < p.pos.size := by rw [hp.posSize]; exact hd.vLt
  rw [individualize_pos_eq, hd.posv, hd.csti, hd.labc, getElem!_set! h1 w, getElem!_set! h2 w]

theorem individualize_lab_getElem! (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (k : Nat) :
    (individualize p v).1.lab[k]! = if k = i then u else if k = c then v else p.lab[k]! := by
  have h1 : i < (p.lab.set! c v).size := by
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hp.labSize]
    exact hd.iLt hp
  have h2 : c < p.lab.size := by rw [hp.labSize]; exact hd.cLt hp
  rw [individualize_lab_eq, hd.posv, hd.csti, hd.labc, getElem!_set! h1 k, getElem!_set! h2 k]

/-- The individualised vertex now occupies the singleton cell at `c`. -/
theorem individualize_pos_self (hp : Part.WF n p) (hd : IndivData n p v i c ec u) :
    (individualize p v).1.pos[v]! = c := by
  rw [individualize_pos_getElem! hp hd v]
  by_cases hvu : v = u
  · rw [if_pos hvu]
    have h := hd.posu hp
    rw [← hvu, hd.posv] at h
    omega
  · rw [if_neg hvu, if_pos rfl]

/-- **The cell of each vertex after individualisation.**  `v` gets the singleton cell `c`;
everything else that was in `v`'s cell moves to `c + 1`; everything else is untouched.  Note that
this says nothing about *where inside its cell* a vertex sits — which is exactly why it is stable
under a renaming that reorders cells internally. -/
theorem individualize_cell (hp : Part.WF n p) (hd : IndivData n p v i c ec u)
    (w : Nat) (hw : w < n) :
    (individualize p v).1.cst[(individualize p v).1.pos[w]!]!
      = if w = v then c else if p.cst[p.pos[w]!]! = c then c + 1 else p.cst[p.pos[w]!]! := by
  have hcLe := hd.cLe hp
  have hiEc := hd.iLtEc hp
  by_cases hwv : w = v
  · subst hwv
    rw [if_pos rfl, individualize_pos_self hp hd, individualize_cst_getElem! hp hd,
      if_neg (by omega), hd.cstc hp]
  rw [if_neg hwv, individualize_pos_getElem! hp hd w]
  by_cases hwu : w = u
  · -- `w` is the displaced vertex: it was at the front of the cell and is now at position `i`
    have hic : i ≠ c := by
      intro h
      refine hwv ?_
      rw [hwu, ← hd.labc, ← h, ← hd.posv]
      exact hp.labPos v hd.vLt
    have hA : p.cst[p.pos[w]!]! = c := by
      rw [hwu, hd.posu hp, hd.cstc hp]
    rw [if_pos hwu, hA, if_pos rfl, individualize_cst_getElem! hp hd, if_pos ⟨by omega, hiEc⟩]
  rw [if_neg hwu, if_neg hwv, individualize_cst_getElem! hp hd]
  have hjN : p.pos[w]! < n := hp.posLt w hw
  have hjc : p.pos[w]! ≠ c := by
    intro h
    exact hwu (by rw [← hd.labc, ← h, hp.labPos w hw])
  by_cases hA : p.cst[p.pos[w]!]! = c
  · have := (hd.mem_iff hp hjN).1 hA
    rw [if_pos hA, if_pos ⟨by omega, this.2⟩]
  · rw [if_neg hA, if_neg (fun hh => hA ((hd.mem_iff hp hjN).2 ⟨by omega, hh.2⟩))]

/-- **Individualisation preserves well-formedness.**  `lab`/`pos` stay inverse because the update
is a transposition, and `cst`/`cen` still describe intervals because `[c, ec)` was cut in two. -/
theorem individualize_wf (hp : Part.WF n p) (hd : IndivData n p v i c ec u) :
    Part.WF n (individualize p v).1 := by
  have hiLt := hd.iLt hp
  have hcLe := hd.cLe hp
  have hiEc := hd.iLtEc hp
  have hecN := hd.ecLe hp
  have hcN := hd.cLt hp
  have huN := hd.uLt hp
  have hvN := hd.vLt
  have hcstc := hd.cstc hp
  have hposu := hd.posu hp
  have hlabi : p.lab[i]! = v := by rw [← hd.posv]; exact hp.labPos v hvN
  have hlab := individualize_lab_getElem! hp hd
  have hpos := individualize_pos_getElem! hp hd
  have hcst := individualize_cst_getElem! hp hd
  have hcen := individualize_cen_getElem! hp hd
  -- the transposition is injective, in the four forms the proofs below need
  have hlabu : ∀ k, k < n → p.lab[k]! = u → k = c := by
    intro k hk h; have h2 := hp.posLab k hk; rw [h, hposu] at h2; omega
  have hlabv : ∀ k, k < n → p.lab[k]! = v → k = i := by
    intro k hk h; have h2 := hp.posLab k hk; rw [h, hd.posv] at h2; omega
  have hposi : ∀ w, w < n → p.pos[w]! = i → w = v := by
    intro w hw h; have h2 := hp.labPos w hw; rw [h, hlabi] at h2; omega
  have hposc : ∀ w, w < n → p.pos[w]! = c → w = u := by
    intro w hw h; have h2 := hp.labPos w hw; rw [h, hd.labc] at h2; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [individualize_lab_eq]; simp [hp.labSize]
  · rw [individualize_pos_eq]; simp [hp.posSize]
  · rw [individualize_cst_eq, setCstFrom_size]; exact hp.cstSize
  · rw [individualize_cen_eq]; simp [hp.cenSize]
  · intro k hk
    rw [hlab k]
    split_ifs
    · exact huN
    · exact hvN
    · exact hp.labLt k hk
  · intro w hw
    rw [hpos w]
    split_ifs
    · exact hiLt
    · exact hcN
    · exact hp.posLt w hw
  · -- `pos` is still a left inverse of `lab`
    intro k hk
    rw [hlab k]
    by_cases h1 : k = i
    · rw [if_pos h1, hpos u, if_pos rfl, h1]
    rw [if_neg h1]
    by_cases h2 : k = c
    · have hci : c ≠ i := fun hh => h1 (h2.trans hh)
      have hvu : v ≠ u := fun h => hci (by rw [← hposu, ← h, hd.posv])
      rw [if_pos h2, hpos v, if_neg hvu, if_pos rfl, h2]
    · rw [if_neg h2, hpos p.lab[k]!, if_neg (fun h => h2 (hlabu k hk h)),
        if_neg (fun h => h1 (hlabv k hk h)), hp.posLab k hk]
  · -- and `lab` of `pos`
    intro w hw
    rw [hpos w]
    by_cases h1 : w = u
    · rw [if_pos h1, hlab i, if_pos rfl, h1]
    rw [if_neg h1]
    by_cases h2 : w = v
    · have hci : c ≠ i := fun hh => h1 (by rw [h2, ← hlabi, ← hh, hd.labc])
      rw [if_pos h2, hlab c, if_neg hci, if_pos rfl, h2]
    · rw [if_neg h2, hlab p.pos[w]!, if_neg (fun h => h2 (hposi w hw h)),
        if_neg (fun h => h1 (hposc w hw h)), hp.labPos w hw]
  · intro k hk
    rw [hcst k]
    split_ifs with h
    · omega
    · exact hp.cstLe k hk
  · intro k hk
    rw [hcen k]
    split_ifs with h
    · omega
    · exact hp.ltCen k hk
  · intro k hk
    rw [hcen k]
    split_ifs
    · omega
    · exact hp.cenLe k hk
  · -- cells still report a common start …
    intro k hk j hj1 hj2
    have hcenk : (individualize p v).1.cen[k]! ≤ n := by
      rw [hcen k]
      split_ifs
      · omega
      · exact hp.cenLe k hk
    have hjn : j < n := by omega
    rw [hcst k] at hj1
    rw [hcen k] at hj2
    rw [hcst j, hcst k]
    by_cases h1 : c + 1 ≤ k ∧ k < ec
    · obtain ⟨h1a, h1b⟩ := h1
      rw [if_pos (⟨h1a, h1b⟩ : c + 1 ≤ k ∧ k < ec)] at hj1
      rw [if_neg (by omega : ¬ k = c), hd.cen_eq hp (by omega) h1b] at hj2
      rw [if_pos (⟨by omega, by omega⟩ : c + 1 ≤ j ∧ j < ec),
        if_pos (⟨h1a, h1b⟩ : c + 1 ≤ k ∧ k < ec)]
    rw [if_neg h1] at hj1 ⊢
    by_cases h2 : k = c
    · rw [if_pos h2] at hj2
      rw [h2, hcstc] at hj1 ⊢
      rw [if_neg (by omega : ¬(c + 1 ≤ j ∧ j < ec))]
      rw [show j = c by omega, hcstc]
    · rw [if_neg h2] at hj2
      have hkc : ¬(c ≤ k ∧ k < ec) := fun hh => h1 ⟨by omega, hh.2⟩
      have hck : p.cst[k]! ≠ c := fun hh => hkc ((hd.mem_iff hp hk).1 hh)
      have hjk : p.cst[j]! = p.cst[k]! := hp.cellCst k hk j hj1 hj2
      rw [if_neg (fun hh =>
        hck (hjk.symm.trans (hd.cst_eq hp (Nat.le_of_succ_le hh.1) hh.2))), hjk]
  · -- … and a common end
    intro k hk j hj1 hj2
    have hcenk : (individualize p v).1.cen[k]! ≤ n := by
      rw [hcen k]
      split_ifs
      · omega
      · exact hp.cenLe k hk
    have hjn : j < n := by omega
    rw [hcst k] at hj1
    rw [hcen k] at hj2
    rw [hcen j, hcen k]
    by_cases h1 : c + 1 ≤ k ∧ k < ec
    · obtain ⟨h1a, h1b⟩ := h1
      rw [if_pos (⟨h1a, h1b⟩ : c + 1 ≤ k ∧ k < ec)] at hj1
      rw [if_neg (by omega : ¬ k = c), hd.cen_eq hp (by omega) h1b] at hj2
      rw [if_neg (by omega : ¬ k = c), hd.cen_eq hp (by omega) h1b]
      rw [if_neg (by omega : ¬ j = c), hd.cen_eq hp (by omega) hj2]
    rw [if_neg h1] at hj1
    by_cases h2 : k = c
    · rw [if_pos h2] at hj2 ⊢
      rw [h2, hcstc] at hj1
      rw [if_pos (by omega : j = c)]
    · rw [if_neg h2] at hj2 ⊢
      have hkc : ¬(c ≤ k ∧ k < ec) := fun hh => h1 ⟨by omega, hh.2⟩
      have hck : p.cst[k]! ≠ c := fun hh => hkc ((hd.mem_iff hp hk).1 hh)
      have hjc : j ≠ c := by
        intro hh
        exact hck ((hp.cellCst k hk c (by omega) (by omega)).symm.trans hcstc)
      rw [if_neg hjc]
      exact hp.cellCen k hk j hj1 hj2

end Individualize

/-- **Step 3 of the decomposition.**  Individualising corresponding vertices of related partitions
gives related partitions, and at the same position — so the two runs stay in step through the
branch, and the recursive call sees the same splitter. -/
theorem individualize_partEquiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q) {v : Nat} (hv : v < n) :
    PartEquiv n σ (individualize p (σ v)).1 (individualize q v).1
      ∧ (individualize p (σ v)).2 = (individualize q v).2 := by
  have hσv : σ v < n := hσ.maps v hv
  -- the two runs split the cell at the same position `c`, and it has the same extent `ec`
  set c := q.cst[q.pos[v]!]! with hc
  have hcp : p.cst[p.pos[σ v]!]! = c := h.cell v hv
  have hdp : IndivData n p (σ v) p.pos[σ v]! c p.cen[p.pos[σ v]!]! p.lab[c]! :=
    ⟨hσv, rfl, hcp, rfl, rfl⟩
  have hdq : IndivData n q v q.pos[v]! c q.cen[q.pos[v]!]! q.lab[c]! := ⟨hv, rfl, hc.symm, rfl, rfl⟩
  have hcn : c < n := hdq.cLt hq
  have hecp : p.cen[c]! = p.cen[p.pos[σ v]!]! :=
    hp.cellCen _ (hdp.iLt hp) c (by rw [hcp]) (by have := hdp.cLe hp; have := hdp.iLtEc hp; omega)
  have hecq : q.cen[c]! = q.cen[q.pos[v]!]! :=
    hq.cellCen _ (hdq.iLt hq) c (by rw [← hc]) (by have := hdq.cLe hq; have := hdq.iLtEc hq; omega)
  have hec : p.cen[p.pos[σ v]!]! = q.cen[q.pos[v]!]! := by rw [← hecp, ← hecq, h.cen c hcn]
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_, fun w hw => ?_⟩, hcp⟩
  · rw [individualize_cst_getElem! hp hdp k, individualize_cst_getElem! hq hdq k, hec]
    split
    · rfl
    · exact h.cst k hk
  · rw [individualize_cen_getElem! hp hdp k, individualize_cen_getElem! hq hdq k]
    split
    · rfl
    · exact h.cen k hk
  · rw [individualize_cell hp hdp (σ w) (hσ.maps w hw), individualize_cell hq hdq w hw,
      h.cell w hw]
    by_cases hwv : w = v
    · rw [if_pos hwv, if_pos (by rw [hwv])]
    · rw [if_neg hwv, if_neg (fun hh => hwv (hσ.inj w hw v hv hh))]

/-! ## Towards step 1: what `refineStep` counts

`refineStep` is the one piece of the algorithm whose equivariance is *not* positionwise.  Every
other loop walks positions, and corresponding positions hold corresponding data; but the counting
phase walks a cell in `lab` order, and corresponding cells are related only as sets.  So the
quantity it computes has to be described set-theoretically before it can be shown invariant, and
that description is `cellCount`: the number of vertices of a given cell satisfying a predicate.

The arithmetic comes first (`cellCount_equiv`: the quantity is invariant), then the first of
`refineStep`'s loops (`countFrom_cellCount`: the loop computes the quantity).  What is not yet
proved is the rest of the step — that the counting sort orders the fragments by count, and that
Hopcroft's rule then picks out the same fragments. -/

/-- A permutation of a finite initial segment is onto it.  Not part of `IsPerm` because nothing
before this section needed it — injectivity was always enough. -/
theorem IsPerm.surj {n : Nat} {σ : Nat → Nat} (hσ : IsPerm n σ) {w : Nat} (hw : w < n) :
    ∃ v, v < n ∧ σ v = w := by
  have hsub : (Finset.range n).image σ ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact hσ.maps a ha
  have hcard : ((Finset.range n).image σ).card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact hσ.inj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) hab
  have heq : (Finset.range n).image σ = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hmem : w ∈ (Finset.range n).image σ := by rw [heq]; exact Finset.mem_range.2 hw
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨a, ha, hax⟩ := hmem
  exact ⟨a, ha, hax⟩

/-- How many vertices of the cell starting at position `s` satisfy `P`.  Every number
`refineStep` computes is of this form: the neighbour count of `v` is `P w := adj w v`, a bucket
size in the counting sort is `P w := cnt w == t`, and a cell size is `P w := true`. -/
def cellCount (n : Nat) (p : Part) (s : Nat) (P : Nat → Bool) : Nat :=
  ((Finset.range n).filter fun w => p.cst[p.pos[w]!]! = s ∧ P w = true).card

/-- **The arithmetic behind step 1.**  Corresponding cells have the same size, and more generally
agree on any count, because `σ` restricts to a bijection between them.  Note this is a genuine
cardinality argument — there is no order-preserving correspondence to appeal to. -/
theorem cellCount_equiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (h : PartEquiv n σ p q) (s : Nat) (P : Nat → Bool) :
    cellCount n p s P = cellCount n q s (fun w => P (σ w)) := by
  refine (Finset.card_bij (fun w _ => σ w) ?_ ?_ ?_).symm
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
    exact ⟨hσ.maps w hw.1, (h.cell w hw.1).trans hw.2.1, hw.2.2⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact hσ.inj a ha.1 b hb.1 hab
  · intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_range] at hw'
    obtain ⟨w, hw, rfl⟩ := hσ.surj hw'.1
    refine ⟨w, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hw, (h.cell w hw).symm.trans hw'.2.1, hw'.2.2⟩

/-- Corresponding cells have the same size. -/
theorem cellSize_equiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (h : PartEquiv n σ p q) (s : Nat) :
    cellCount n p s (fun _ => true) = cellCount n q s (fun _ => true) :=
  cellCount_equiv hσ h s _

/-- The neighbour counts that drive refinement are equivariant: `σ v` sees as many neighbours in
`p`'s cell at `s` as `v` does in `q`'s. -/
theorem cellNbrCount_equiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (h : PartEquiv n σ p q) (f : Nat → Nat → Bool) (s v : Nat) :
    cellCount n p s (fun w => f w (σ v))
      = cellCount n q s (fun w => (fun a b => f (σ a) (σ b)) w v) :=
  cellCount_equiv hσ h s _

/-! ### The counting loop

`countFrom` is phase (1) of `refineStep`: it walks the splitter cell `lab[s:e]` and, for every
vertex `w`, accumulates in `cnt[w]` the number of cell members adjacent to `w`.  Written as a
`for` loop this would be out of reach — see the note on `cenHashFrom` — so `Canonical.lean` gives
it as a structural recursion on fuel, and the three lemmas below read the result off.

The bridge to `cellCount` is `List.count`: the inner loop bumps `cnt[w]` once per occurrence of
`w` in a neighbour list, and `Graph.ofOracle`'s neighbour lists are filtered ranges, hence
duplicate-free, so each cell member contributes at most one. -/

/-- Companion to `getElem!_set!` for the off-diagonal case, where no bound on `i` is needed:
writing at `i` never disturbs another index, in bounds or not. -/
theorem getElem!_set!_ne {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {x : α} {k : Nat}
    (h : k ≠ i) :
    (a.set! i x)[k]! = a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk,
      if_neg (Ne.symm h)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk]

/-- The inner loop only writes, never resizes. -/
theorem bumpFrom_size (nbrs : Array Nat) : ∀ (fuel j : Nat) (cnt touched : Array Nat),
    (bumpFrom nbrs fuel j cnt touched).1.size = cnt.size
  | 0, _, _, _ => rfl
  | fuel + 1, j, cnt, touched => by
    rw [bumpFrom]
    split
    · rfl
    · rw [bumpFrom_size nbrs fuel (j + 1) _ _]
      simp

/-- The inner loop adds to `cnt[w]` the multiplicity of `w` in the part of the neighbour list it
scans.  Entries of `nbrs` outside `cnt` write nothing, but they are not `w` either, so the
statement needs no hypothesis on them. -/
theorem bumpFrom_getElem! (nbrs : Array Nat) : ∀ (fuel j : Nat) (cnt touched : Array Nat),
    nbrs.size ≤ j + fuel → ∀ w, w < cnt.size →
      (bumpFrom nbrs fuel j cnt touched).1[w]! = cnt[w]! + (nbrs.toList.drop j).count w
  | 0, j, cnt, touched, hf, w, hw => by
    rw [bumpFrom, List.drop_eq_nil_of_le (by simp; omega), List.count_nil]
    simp
  | fuel + 1, j, cnt, touched, hf, w, hw => by
    rw [bumpFrom]
    split
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.count_nil]
      simp
    · rename_i hj
      have hjs : j < nbrs.size := by omega
      have hdrop : nbrs.toList.drop j = nbrs[j]! :: nbrs.toList.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjs), getElem!_pos nbrs j hjs,
          Array.getElem_toList]
      rw [bumpFrom_getElem! nbrs fuel (j + 1) _ _ (by omega) w
        (by simpa using hw), hdrop, List.count_cons]
      by_cases hwj : w = nbrs[j]!
      · rw [getElem!_set! (by omega : nbrs[j]! < cnt.size) w, if_pos hwj, if_pos (by simp [hwj]),
          hwj]
        omega
      · rw [getElem!_set!_ne hwj, if_neg (by simpa using fun h => hwj h.symm)]
        omega

/-- Unfolding lemma for the outer loop.  The definition destructures the inner loop's result
rather than projecting it (that is what keeps `cnt` unshared, see `Canonical.lean`), and
definitional eta for structures makes the two forms interchangeable. -/
theorem countFrom_succ (G : Graph) (lab : Array Nat) (e fuel k : Nat) (cnt touched : Array Nat) :
    countFrom G lab e (fuel + 1) k cnt touched =
      if k ≥ e then (cnt, touched)
      else
        countFrom G lab e fuel (k + 1)
          (bumpFrom (G.nbr[lab[k]!]!) (G.nbr[lab[k]!]!).size 0 cnt touched).1
          (bumpFrom (G.nbr[lab[k]!]!) (G.nbr[lab[k]!]!).size 0 cnt touched).2 := by
  rw [countFrom]

/-- The counting phase only writes, never resizes. -/
theorem countFrom_size (G : Graph) (lab : Array Nat) (e : Nat) :
    ∀ (fuel k : Nat) (cnt touched : Array Nat),
      (countFrom G lab e fuel k cnt touched).1.size = cnt.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, cnt, touched => by
    rw [countFrom_succ]
    split
    · rfl
    · rw [countFrom_size G lab e fuel (k + 1) _ _, bumpFrom_size]

/-- The counting phase adds to `cnt[w]` one for every occurrence of `w` in a neighbour list of a
vertex sitting at a position in `[k, e)`. -/
theorem countFrom_getElem! (G : Graph) (lab : Array Nat) (e : Nat) :
    ∀ (fuel k : Nat) (cnt touched : Array Nat), e ≤ k + fuel → ∀ w, w < cnt.size →
      (countFrom G lab e fuel k cnt touched).1[w]!
        = cnt[w]! + ∑ i ∈ Finset.Ico k e, (G.nbr[lab[i]!]!).toList.count w
  | 0, k, cnt, touched, hf, w, hw => by
    rw [countFrom, Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    simp
  | fuel + 1, k, cnt, touched, hf, w, hw => by
    rw [countFrom_succ]
    split
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      simp
    · rename_i hk
      have hsplit : ∑ i ∈ Finset.Ico k e, (G.nbr[lab[i]!]!).toList.count w
          = (G.nbr[lab[k]!]!).toList.count w
            + ∑ i ∈ Finset.Ico (k + 1) e, (G.nbr[lab[i]!]!).toList.count w :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [countFrom_getElem! G lab e fuel (k + 1) _ _ (by omega) w
          (by rw [bumpFrom_size]; exact hw),
        bumpFrom_getElem! (G.nbr[lab[k]!]!) (G.nbr[lab[k]!]!).size 0 cnt touched (by omega) w hw,
        List.drop_zero, hsplit]
      omega

/-- Neighbour lists of `Graph.ofOracle` are duplicate-free, so a vertex occurs in one at most
once.  This is what turns the multiplicities counted above into a `0`/`1` adjacency test. -/
theorem ofOracle_nbr_count (n : Nat) (f : Nat → Nat → Bool) (u v : Nat) (hu : u < n) (hv : v < n) :
    (Graph.ofOracle n f).nbr[u]!.toList.count v = if f u v then 1 else 0 := by
  rw [ofOracle_nbr n f u hu,
    show ((Array.range n).filter (f u)).toList = (List.range n).filter (f u) by simp]
  by_cases h : f u v
  · rw [if_pos h, List.count_filter h, List.count_range, if_pos hv]
  · rw [if_neg h, List.count_eq_zero_of_not_mem]
    simp [h]

/-- **What the counting phase computes.**  Run from cleared scratch over the cell starting at
position `s`, `countFrom` leaves `cnt[w]` holding the number of vertices of that cell adjacent to
`w` — that is, exactly `cellCount n p s (· is adjacent to w)`.

This is the missing half of step 1's first loop: `cellCount_equiv` says the quantity is invariant,
and this says the loop computes the quantity. -/
theorem countFrom_cellCount {n : Nat} (f : Nat → Nat → Bool) {p : Part} (hp : Part.WF n p)
    {s : Nat} (hs : s < n) (hcst : p.cst[s]! = s) {w : Nat} (hw : w < n) :
    (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]).1[w]!
      = cellCount n p s (fun u => f u w) := by
  set e := p.cen[s]! with he
  have hsE : s < e := he ▸ hp.ltCen s hs
  have hEn : e ≤ n := he ▸ hp.cenLe s hs
  have hsz : (Array.replicate n 0 : Array Nat).size = n := by simp
  rw [countFrom_getElem! _ _ _ _ _ _ _ (by omega) w (by rw [hsz]; exact hw),
    show (Array.replicate n 0 : Array Nat)[w]! = 0 by
      rw [getElem!_pos _ _ (by simpa using hw)]; simp,
    Nat.zero_add]
  have hterm : ∀ i ∈ Finset.Ico s e,
      ((Graph.ofOracle n f).nbr[p.lab[i]!]!).toList.count w = if f p.lab[i]! w then 1 else 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact ofOracle_nbr_count n f _ w (hp.labLt i (by omega)) hw
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  -- What is left is a bijection: positions of the cell ↔ vertices of the cell.
  refine Finset.card_bij (fun i _ => p.lab[i]!) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp.labLt i (by omega), ?_, hi.2⟩
    rw [hp.posLab i (by omega)]
    have := hp.cellCst s hs i (by rw [hcst]; omega) (by omega)
    rw [this, hcst]
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    have hab' : p.lab[a]! = p.lab[b]! := hab
    have h1 := hp.posLab a (by omega)
    have h2 := hp.posLab b (by omega)
    rw [hab', h2] at h1
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    refine ⟨p.pos[u]!, ?_, hp.labPos u hu.1⟩
    have hpu : p.pos[u]! < n := hp.posLt u hu.1
    have hmem := (hp.cst_eq_iff hs hpu).1 (by rw [hu.2.1, hcst])
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rw [hcst] at hmem
    exact ⟨⟨hmem.1, hmem.2⟩, by rw [hp.labPos u hu.1]; exact hu.2.2⟩

/-- **The counting phase of `refineStep` is equivariant.**  Putting the two halves together: in
two runs whose partitions correspond under `σ`, the count the `f`-run records at `σ w` is the one
the `f ∘ σ`-run records at `w`.  Note the cells need only correspond as sets — the two runs walk
them in different orders, and the proof goes through `cellCount` precisely to avoid caring. -/
theorem countFrom_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    {s : Nat} (hs : s < n) (hcst : q.cst[s]! = s) {w : Nat} (hw : w < n) :
    (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]).1[σ w]!
      = (countFrom (Graph.ofOracle n fun a b => f (σ a) (σ b)) q.lab q.cen[s]! (q.cen[s]! - s) s
        (Array.replicate n 0) #[]).1[w]! := by
  rw [countFrom_cellCount f hp hs (by rw [h.cst s hs, hcst]) (hσ.maps w hw),
    countFrom_cellCount _ hq hs hcst hw]
  exact cellNbrCount_equiv hσ h f s w

/-- The invariant the counting phase maintains on its scratch space: `touched` lists exactly the
vertices whose count is nonzero, each once.

`refineStep` needs both halves.  Completeness is what makes the collected cells the right ones —
a cell met by the splitter has a member with a nonzero count, so it is represented.  Soundness
and no-repetition are what make the restore loop at the end of the step put the scratch back
*exactly*, in time proportional to what was dirtied rather than to `n`. -/
structure Touched (cnt touched : Array Nat) : Prop where
  /-- No vertex is recorded twice. -/
  nodup : touched.toList.Nodup
  /-- Only vertices are recorded. -/
  lt : ∀ w ∈ touched, w < cnt.size
  /-- Recorded is the same as counted. -/
  mem : ∀ w, w < cnt.size → (w ∈ touched ↔ cnt[w]! ≠ 0)

/-- Cleared scratch satisfies the invariant. -/
theorem touched_empty (cnt : Array Nat) (h : ∀ w, w < cnt.size → cnt[w]! = 0) :
    Touched cnt #[] :=
  ⟨by simp, by simp, fun w hw => by simp [h w hw]⟩

/-- An in-bounds `getElem!` is a member. -/
theorem getElem!_mem {a : Array Nat} {j : Nat} (h : j < a.size) : a[j]! ∈ a := by
  rw [getElem!_pos a j h]
  exact Array.getElem_mem h

/-- The inner loop maintains the scratch invariant: it pushes a vertex exactly when it is raising
that vertex's count off zero.  The hypothesis on `nbrs` is needed — a neighbour outside `cnt`
would leave the count at the `getElem!` default of `0` and so be pushed on every visit. -/
theorem bumpFrom_touched (nbrs : Array Nat) : ∀ (fuel j : Nat) (cnt touched : Array Nat),
    (∀ x ∈ nbrs, x < cnt.size) → Touched cnt touched →
      Touched (bumpFrom nbrs fuel j cnt touched).1 (bumpFrom nbrs fuel j cnt touched).2
  | 0, _, _, _, _, ht => ht
  | fuel + 1, j, cnt, touched, hnb, ht => by
    rw [bumpFrom]
    split
    · exact ht
    · rename_i hj
      have hjs : j < nbrs.size := by omega
      have hv : nbrs[j]! < cnt.size := hnb _ (getElem!_mem hjs)
      have hsz : (cnt.set! nbrs[j]! (cnt[nbrs[j]!]! + 1)).size = cnt.size := by simp
      refine bumpFrom_touched nbrs fuel (j + 1) _ _ (by simpa [hsz] using hnb) ⟨?_, ?_, ?_⟩
      · split
        · rename_i hc
          have hnot : nbrs[j]! ∉ touched := fun hmem =>
            ((ht.mem _ hv).1 hmem) (by simpa using hc)
          rw [Array.toList_push]
          refine List.nodup_append.2 ⟨ht.nodup, by simp, ?_⟩
          intro a ha b hb hab
          rw [List.mem_singleton] at hb
          subst hab
          subst hb
          exact hnot (by simpa using ha)
        · exact ht.nodup
      · intro w hw
        rw [hsz]
        split at hw
        · rcases Array.mem_push.1 hw with h | h
          · exact ht.lt w h
          · exact h ▸ hv
        · exact ht.lt w hw
      · intro w hw
        rw [hsz] at hw
        by_cases hwv : w = nbrs[j]!
        · subst hwv
          rw [getElem!_set! hv _, if_pos rfl]
          simp only [ne_eq, Nat.succ_ne_zero, not_false_eq_true, iff_true]
          split
          · exact Array.mem_push.2 (Or.inr rfl)
          · rename_i hc
            exact (ht.mem _ hw).2 (by simpa using hc)
        · rw [getElem!_set!_ne hwv]
          split
          · rw [Array.mem_push]
            simp only [hwv, or_false]
            exact ht.mem w hw
          · exact ht.mem w hw

/-- The outer loop maintains the scratch invariant. -/
theorem countFrom_touched (G : Graph) (lab : Array Nat) (e : Nat) :
    ∀ (fuel k : Nat) (cnt touched : Array Nat),
      (∀ (u x : Nat), x ∈ G.nbr[u]! → x < cnt.size) → Touched cnt touched →
        Touched (countFrom G lab e fuel k cnt touched).1
          (countFrom G lab e fuel k cnt touched).2
  | 0, _, _, _, _, ht => ht
  | fuel + 1, k, cnt, touched, hG, ht => by
    rw [countFrom_succ]
    split
    · exact ht
    · refine countFrom_touched G lab e fuel (k + 1) _ _ ?_
        (bumpFrom_touched _ _ _ _ _ (fun x hx => hG lab[k]! x hx) ht)
      intro u x hx
      rw [bumpFrom_size]
      exact hG u x hx

/-- The counting phase as `refineStep` actually calls it, from cleared scratch. -/
theorem countFrom_touched_spec {n : Nat} (f : Nat → Nat → Bool) (lab : Array Nat) (e s : Nat) :
    Touched (countFrom (Graph.ofOracle n f) lab e (e - s) s (Array.replicate n 0) #[]).1
      (countFrom (Graph.ofOracle n f) lab e (e - s) s (Array.replicate n 0) #[]).2 :=
  countFrom_touched _ _ _ _ _ _ _
    (fun u x hx => by simpa using ofOracle_nbr_lt' n f u x hx)
    (touched_empty _ fun w hw => by rw [getElem!_pos (Array.replicate n 0) w hw]; simp)

/-- **The vertices the counting phase records form an invariant set.**  `touched` is exactly the
set of vertices that the splitter cell reaches, and membership is stated in terms of `cellCount`,
which `cellCount_equiv` shows corresponding runs agree on.

The *order* of `touched` is not invariant — it is first-touch order, which depends on vertex
names.  That is why `refineStep` maps it to cell starts and sorts before using it. -/
theorem countFrom_mem_touched {n : Nat} (f : Nat → Nat → Bool) {p : Part} (hp : Part.WF n p)
    {s : Nat} (hs : s < n) (hcst : p.cst[s]! = s) {w : Nat} (hw : w < n) :
    w ∈ (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]).2 ↔ cellCount n p s (fun u => f u w) ≠ 0 := by
  rw [(countFrom_touched_spec f p.lab p.cen[s]! s).mem w
      (by rw [countFrom_size]; simpa using hw),
    countFrom_cellCount f hp hs hcst hw]

/-! ### Collecting the cells met by the splitter

Phase (2) of `refineStep` turns the touched vertices into the list of cells that have to be split.
Its output has to be canonical in a stronger sense than phase (1)'s: not just the same *set* of
cells in both runs, but the same *array*, since the step then processes them in order.  That is
what the sort is for, and why `sortNats` goes through `List.mergeSort` rather than `Array.qsort` —
`qsort` has no specification in this toolchain, and an unspecified order is exactly what cannot be
tolerated here.  `sortNats_ext` is the punchline of the sorting half ("duplicate-free arrays with
the same elements sort alike"), `collect_equiv` of the whole phase.
-/

/-- Sorting a `List` and sorting the `Array` of the same elements agree. -/
@[simp] theorem sortNats_toList (a : Array Nat) :
    (sortNats a).toList = a.toList.mergeSort (fun x y => x ≤ y) := by
  simp [sortNats]

theorem sortNats_perm (a : Array Nat) : (sortNats a).toList.Perm a.toList := by
  rw [sortNats_toList]
  exact List.mergeSort_perm _ _

theorem sortNats_pairwise (a : Array Nat) : (sortNats a).toList.Pairwise (· ≤ ·) := by
  rw [sortNats_toList]
  have := List.pairwise_mergeSort (le := fun x y : Nat => x ≤ y)
    (fun a b c hab hbc => by simpa using le_trans (by simpa using hab) (by simpa using hbc))
    (fun a b => by simpa using le_total a b) a.toList
  simpa using this

theorem sortNats_mem {a : Array Nat} {c : Nat} : c ∈ sortNats a ↔ c ∈ a := by
  rw [← Array.mem_toList_iff, ← Array.mem_toList_iff]
  exact (sortNats_perm a).mem_iff

/-- **Sorting normalises.**  Two duplicate-free arrays with the same elements sort to the same
array; this is what makes the list of cells met by a splitter canonical. -/
theorem sortNats_ext {a b : Array Nat} (ha : a.toList.Nodup) (hb : b.toList.Nodup)
    (h : ∀ c, c ∈ a ↔ c ∈ b) : sortNats a = sortNats b := by
  have hperm : (sortNats a).toList.Perm (sortNats b).toList :=
    ((sortNats_perm a).trans
      (List.perm_of_nodup_nodup_toFinset_eq ha hb (by
        ext c
        simpa using h c))).trans (sortNats_perm b).symm
  refine Array.ext' (List.Perm.eq_of_pairwise ?_ (sortNats_pairwise a) (sortNats_pairwise b) hperm)
  intro x y _ _ hxy hyx
  exact le_antisymm hxy hyx


/-- The scratch invariant of the collection phase: `cells` lists exactly the cell starts marked
in `hit`, each once.  The analogue of `Touched` for phase (2). -/
structure Collected (hit : Array Bool) (cells : Array Nat) : Prop where
  /-- No cell is collected twice — this is what `hit` is for. -/
  nodup : cells.toList.Nodup
  /-- Collected cells are in range. -/
  lt : ∀ c ∈ cells, c < hit.size
  /-- `hit` marks exactly the collected cells. -/
  mem : ∀ c, c < hit.size → (c ∈ cells ↔ hit[c]! = true)

theorem collected_empty (hit : Array Bool) (h : ∀ c, c < hit.size → hit[c]! = false) :
    Collected hit #[] :=
  ⟨by simp, by simp, fun c hc => by simp [h c hc]⟩

/-- Marking and pushing an unmarked cell preserves the invariant. -/
theorem Collected.push {hit : Array Bool} {cells : Array Nat} (h : Collected hit cells) {c : Nat}
    (hc : c < hit.size) (hf : hit[c]! = false) : Collected (hit.set! c true) (cells.push c) := by
  have hsz : (hit.set! c true).size = hit.size := by simp
  have hnot : c ∉ cells := fun hmem => by rw [(h.mem c hc).1 hmem] at hf; exact Bool.noConfusion hf
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.toList_push]
    refine List.nodup_append.2 ⟨h.nodup, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hab
    subst hb
    exact hnot (by simpa using ha)
  · intro w hw
    rw [hsz]
    rcases Array.mem_push.1 hw with hw | hw
    · exact h.lt w hw
    · exact hw ▸ hc
  · intro w hw
    rw [hsz] at hw
    by_cases hwc : w = c
    · subst hwc
      rw [getElem!_set! hc _, if_pos rfl, Array.mem_push]
      simp
    · rw [getElem!_set!_ne hwc, Array.mem_push]
      simp only [hwc, or_false]
      exact h.mem w hw

theorem collectFrom_collected (pos cst touched : Array Nat) :
    ∀ (fuel j : Nat) (hit : Array Bool) (cells : Array Nat),
      (∀ v ∈ touched, cst[pos[v]!]! < hit.size) → Collected hit cells →
        Collected (collectFrom pos cst touched fuel j hit cells).1
          (collectFrom pos cst touched fuel j hit cells).2
  | 0, _, _, _, _, hc => hc
  | fuel + 1, j, hit, cells, hb, hc => by
    rw [collectFrom]
    split
    · exact hc
    · rename_i hj
      have hjs : j < touched.size := by omega
      have hlt : cst[pos[touched[j]!]!]! < hit.size := hb _ (getElem!_mem hjs)
      dsimp only
      split
      · exact collectFrom_collected pos cst touched fuel (j + 1) hit cells hb hc
      · rename_i hf
        refine collectFrom_collected pos cst touched fuel (j + 1) _ _ (by simpa using hb)
          (hc.push hlt (by simpa using hf))

/-- **What the collection phase collects**: exactly the cell starts of the vertices it is given,
each once (the `Nodup` half is `collectFrom_collected`). -/
theorem collectFrom_mem (pos cst touched : Array Nat) :
    ∀ (fuel j : Nat) (hit : Array Bool) (cells : Array Nat), touched.size ≤ j + fuel →
      (∀ v ∈ touched, cst[pos[v]!]! < hit.size) → Collected hit cells → ∀ c,
        (c ∈ (collectFrom pos cst touched fuel j hit cells).2 ↔
          c ∈ cells ∨ ∃ v ∈ touched.toList.drop j, cst[pos[v]!]! = c)
  | 0, j, hit, cells, hf, _, _, c => by
    rw [collectFrom, List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | fuel + 1, j, hit, cells, hf, hb, hc, c => by
    rw [collectFrom]
    split
    · rw [List.drop_eq_nil_of_le (by simp; omega)]
      simp
    · rename_i hj
      have hjs : j < touched.size := by omega
      have hlt : cst[pos[touched[j]!]!]! < hit.size := hb _ (getElem!_mem hjs)
      have hdrop : touched.toList.drop j = touched[j]! :: touched.toList.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjs), getElem!_pos touched j hjs,
          Array.getElem_toList]
      dsimp only
      split
      · rename_i hhit
        rw [collectFrom_mem pos cst touched fuel (j + 1) hit cells (by omega) hb hc c, hdrop]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by simpa using Or.inr h)
        · rintro (h | h)
          · exact Or.inl h
          · rcases (by simpa using h) with h | h
            · exact Or.inl (h ▸ (hc.mem _ hlt).2 hhit)
            · exact Or.inr h
      · rename_i hhit
        rw [collectFrom_mem pos cst touched fuel (j + 1) _ _ (by omega) (by simpa using hb)
          (hc.push hlt (by simpa using hhit)) c, hdrop, Array.mem_push]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (by simp [h])
          · exact Or.inr (by simpa using Or.inr h)
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · rcases (by simpa using h) with h | h
            · exact Or.inl (Or.inr h.symm)
            · exact Or.inr h

/-- The collection phase as `refineStep` runs it: from an all-clear `hit`, it collects exactly the
cells that the touched vertices lie in. -/
theorem collect_mem {n : Nat} {p : Part} (hp : Part.WF n p) {touched : Array Nat}
    (htn : ∀ v ∈ touched, v < n) {hit : Array Bool} (hsz : hit.size = n)
    (hf0 : ∀ c, c < n → hit[c]! = false) (c : Nat) :
    c ∈ (collectFrom p.pos p.cst touched touched.size 0 hit #[]).2 ↔
      ∃ v ∈ touched, p.cst[p.pos[v]!]! = c := by
  have hbd : ∀ v ∈ touched, p.cst[p.pos[v]!]! < hit.size := by
    intro v hv
    have h1 : p.pos[v]! < n := hp.posLt v (htn v hv)
    have h2 : p.cst[p.pos[v]!]! ≤ p.pos[v]! := hp.cstLe _ h1
    omega
  rw [collectFrom_mem p.pos p.cst touched touched.size 0 hit #[] (by omega) hbd
    (collected_empty hit fun c hc => hf0 c (by omega)) c]
  simp

theorem collect_nodup {n : Nat} {p : Part} (hp : Part.WF n p) {touched : Array Nat}
    (htn : ∀ v ∈ touched, v < n) {hit : Array Bool} (hsz : hit.size = n)
    (hf0 : ∀ c, c < n → hit[c]! = false) :
    (collectFrom p.pos p.cst touched touched.size 0 hit #[]).2.toList.Nodup := by
  refine (collectFrom_collected p.pos p.cst touched touched.size 0 hit #[] ?_
    (collected_empty hit fun c hc => hf0 c (by omega))).nodup
  intro v hv
  have h1 : p.pos[v]! < n := hp.posLt v (htn v hv)
  have h2 : p.cst[p.pos[v]!]! ≤ p.pos[v]! := hp.cstLe _ h1
  omega

/-- Every vertex the counting phase touches is a vertex. -/
theorem countFrom_touched_lt {n : Nat} (f : Nat → Nat → Bool) (lab : Array Nat) (e s : Nat)
    {v : Nat} (hv : v ∈ (countFrom (Graph.ofOracle n f) lab e (e - s) s
      (Array.replicate n 0) #[]).2) : v < n := by
  have := (countFrom_touched_spec f lab e s).lt v hv
  rwa [countFrom_size, Array.size_replicate] at this

/-- **Phase (2) of `refineStep` is equivariant.**  The two runs meet the same cells, in the same
order: the cells are the same *positions* because `PartEquiv` matches cell boundaries, and the
sort makes the order depend on nothing but the set. -/
theorem collect_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    {s : Nat} (hs : s < n) (hcst : q.cst[s]! = s)
    {hit : Array Bool} (hsz : hit.size = n) (hf0 : ∀ c, c < n → hit[c]! = false)
    {tp tq : Array Nat}
    (htp : tp = (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[]).2)
    (htq : tq = (countFrom (Graph.ofOracle n fun a b => f (σ a) (σ b)) q.lab q.cen[s]!
      (q.cen[s]! - s) s (Array.replicate n 0) #[]).2) :
    sortNats (collectFrom p.pos p.cst tp tp.size 0 hit #[]).2
      = sortNats (collectFrom q.pos q.cst tq tq.size 0 hit #[]).2 := by
  have hcstp : p.cst[s]! = s := by rw [h.cst s hs, hcst]
  have htpn : ∀ v ∈ tp, v < n := fun v hv => countFrom_touched_lt f p.lab _ s (htp ▸ hv)
  have htqn : ∀ v ∈ tq, v < n := fun v hv => countFrom_touched_lt _ q.lab _ s (htq ▸ hv)
  -- Membership of the two touched sets corresponds along `σ`.
  have hmemp : ∀ v, v < n → (v ∈ tp ↔ cellCount n p s (fun u => f u v) ≠ 0) := by
    intro v hv
    rw [htp]
    exact countFrom_mem_touched f hp hs hcstp hv
  have hmemq : ∀ w, w < n → (w ∈ tq ↔ cellCount n q s (fun u => f (σ u) (σ w)) ≠ 0) := by
    intro w hw
    rw [htq]
    exact countFrom_mem_touched _ hq hs hcst hw
  refine sortNats_ext (collect_nodup hp htpn hsz hf0) (collect_nodup hq htqn hsz hf0) ?_
  intro c
  rw [collect_mem hp htpn hsz hf0, collect_mem hq htqn hsz hf0]
  constructor
  · rintro ⟨v, hv, hc⟩
    obtain ⟨w, hw, rfl⟩ := hσ.surj (htpn v hv)
    refine ⟨w, (hmemq w hw).2 ?_, ?_⟩
    · rw [← cellNbrCount_equiv hσ h f s w]
      exact (hmemp _ (hσ.maps w hw)).1 hv
    · rw [← h.cell w hw, hc]
  · rintro ⟨w, hw, hc⟩
    have hwn : w < n := htqn w hw
    refine ⟨σ w, (hmemp _ (hσ.maps w hwn)).2 ?_, ?_⟩
    · rw [cellNbrCount_equiv hσ h f s w]
      exact (hmemq w hwn).1 hw
    · rw [h.cell w hwn, hc]

/-! ### The counting sort

The heart of `refineStep`: each cell that the splitter met is sorted by neighbour count.  The
sort is a counting sort in five passes — count the buckets (`bucketFrom`), turn the counts into
offsets (`offsetFrom`), scatter the vertices into a block (`scatterFrom`), write the block back
(`writeFrom`), install the new fragment boundaries (`boundsFrom`) — and each pass gets its own
`getElem!` characterisation here.  The one substantial argument is `scatterFrom_block`: the
scatter writes each vertex to a distinct slot, which needs the buckets' offset ranges to be
disjoint (`Sep`) and is what makes the whole thing a permutation of the cell.
-/

/-- How many of the positions `[k, ec)` hold a vertex of neighbour count `t`. -/
def bucketSize (lab cnt : Array Nat) (k ec t : Nat) : Nat :=
  ∑ i ∈ Finset.Ico k ec, if cnt[lab[i]!]! = t then 1 else 0

theorem bucketSize_zero (lab cnt : Array Nat) {k ec t : Nat} (h : ec ≤ k) :
    bucketSize lab cnt k ec t = 0 := by
  rw [bucketSize, Finset.Ico_eq_empty (by omega), Finset.sum_empty]

theorem bucketSize_succ (lab cnt : Array Nat) {k ec t : Nat} (h : k < ec) :
    bucketSize lab cnt k ec t
      = (if cnt[lab[k]!]! = t then 1 else 0) + bucketSize lab cnt (k + 1) ec t :=
  Finset.sum_eq_sum_Ico_succ_bot h _

theorem bucketFrom_size (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (bc ks : Array Nat), (bucketFrom lab cnt ec fuel k bc ks).1.size = bc.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, bc, ks => by
    rw [bucketFrom]
    split
    · rfl
    · rw [bucketFrom_size lab cnt ec fuel (k + 1) _ _]
      simp

theorem bucketFrom_getElem! (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (bc ks : Array Nat), ec ≤ k + fuel → ∀ t, t < bc.size →
      (bucketFrom lab cnt ec fuel k bc ks).1[t]! = bc[t]! + bucketSize lab cnt k ec t
  | 0, k, bc, ks, hf, t, ht => by
    rw [bucketFrom, bucketSize_zero lab cnt (by omega)]
    simp
  | fuel + 1, k, bc, ks, hf, t, ht => by
    rw [bucketFrom]
    split
    · rw [bucketSize_zero lab cnt (by omega)]
      simp
    · rename_i hk
      have hlt : k < ec := by omega
      rw [bucketSize_succ lab cnt hlt]
      dsimp only
      rw [bucketFrom_getElem! lab cnt ec fuel (k + 1) _ _ (by omega) t (by simpa using ht)]
      by_cases hteq : t = cnt[lab[k]!]!
      · rw [getElem!_set! (by omega : cnt[lab[k]!]! < bc.size) t, if_pos hteq,
          if_pos (by simp [hteq]), hteq]
        omega
      · rw [getElem!_set!_ne hteq, if_neg (by simpa using fun h => hteq h.symm)]
        omega

/-- The bucket table and the list of occurring counts satisfy the same invariant as the count
array and its touched list: `ks` lists exactly the counts with a nonzero bucket, each once. -/
theorem bucketFrom_touched (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (bc ks : Array Nat), (∀ (v : Nat), cnt[v]! < bc.size) → Touched bc ks →
      Touched (bucketFrom lab cnt ec fuel k bc ks).1 (bucketFrom lab cnt ec fuel k bc ks).2
  | 0, _, _, _, _, ht => ht
  | fuel + 1, k, bc, ks, hcb, ht => by
    rw [bucketFrom]
    split
    · exact ht
    · have hv : cnt[lab[k]!]! < bc.size := hcb _
      have hsz : (bc.set! cnt[lab[k]!]! (bc[cnt[lab[k]!]!]! + 1)).size = bc.size := by simp
      dsimp only
      refine bucketFrom_touched lab cnt ec fuel (k + 1) _ _ (by simpa [hsz] using hcb) ⟨?_, ?_, ?_⟩
      · split
        · rename_i hc
          have hnot : cnt[lab[k]!]! ∉ ks := fun hmem => ((ht.mem _ hv).1 hmem) (by simpa using hc)
          rw [Array.toList_push]
          refine List.nodup_append.2 ⟨ht.nodup, by simp, ?_⟩
          intro a ha b hb hab
          rw [List.mem_singleton] at hb
          subst hab
          subst hb
          exact hnot (by simpa using ha)
        · exact ht.nodup
      · intro w hw
        rw [hsz]
        split at hw
        · rcases Array.mem_push.1 hw with h | h
          · exact ht.lt w h
          · exact h ▸ hv
        · exact ht.lt w hw
      · intro w hw
        rw [hsz] at hw
        by_cases hwv : w = cnt[lab[k]!]!
        · subst hwv
          rw [getElem!_set! hv _, if_pos rfl]
          simp only [ne_eq, Nat.succ_ne_zero, not_false_eq_true, iff_true]
          split
          · exact Array.mem_push.2 (Or.inr rfl)
          · rename_i hc
            exact (ht.mem _ hw).2 (by simpa using hc)
        · rw [getElem!_set!_ne hwv]
          split
          · rw [Array.mem_push]
            simp only [hwv, or_false]
            exact ht.mem w hw
          · exact ht.mem w hw

/-- **What the bucketing phase collects**: exactly the counts that occur in the cell. -/
theorem bucket_mem {lab cnt bc : Array Nat} {c ec : Nat} (hcb : ∀ (v : Nat), cnt[v]! < bc.size)
    (hbc0 : ∀ t, t < bc.size → bc[t]! = 0) (t : Nat) :
    t ∈ (bucketFrom lab cnt ec (ec - c) c bc #[]).2 ↔
      t < bc.size ∧ bucketSize lab cnt c ec t ≠ 0 := by
  have hT : Touched (bucketFrom lab cnt ec (ec - c) c bc #[]).1
      (bucketFrom lab cnt ec (ec - c) c bc #[]).2 :=
    bucketFrom_touched lab cnt ec (ec - c) c bc #[] hcb
      (touched_empty bc fun w hw => hbc0 w hw)
  constructor
  · intro hmem
    have hlt : t < bc.size := by
      have := hT.lt t hmem
      rwa [bucketFrom_size] at this
    refine ⟨hlt, ?_⟩
    have := (hT.mem t (by rw [bucketFrom_size]; exact hlt)).1 hmem
    rwa [bucketFrom_getElem! lab cnt ec (ec - c) c bc #[] (by omega) t hlt, hbc0 t hlt,
      Nat.zero_add] at this
  · rintro ⟨hlt, hne⟩
    refine (hT.mem t (by rw [bucketFrom_size]; exact hlt)).2 ?_
    rw [bucketFrom_getElem! lab cnt ec (ec - c) c bc #[] (by omega) t hlt, hbc0 t hlt, Nat.zero_add]
    exact hne

/-- The bucket sizes are cell counts, so the vocabulary of step 1 applies to them: the same
position-to-vertex bijection as in `countFrom_cellCount`. -/
theorem bucketSize_cellCount {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) (cnt : Array Nat) (t : Nat) :
    bucketSize p.lab cnt c p.cen[c]! t = cellCount n p c (fun u => cnt[u]! == t) := by
  have hcE : c < p.cen[c]! := hp.ltCen c hc
  have hEn : p.cen[c]! ≤ n := hp.cenLe c hc
  rw [bucketSize, ← Finset.sum_filter, ← Finset.card_eq_sum_ones, cellCount]
  refine Finset.card_bij (fun i _ => p.lab[i]!) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp.labLt i (by omega), ?_, by simpa using hi.2⟩
    rw [hp.posLab i (by omega)]
    have := hp.cellCst c hc i (by rw [hcst]; omega) (by omega)
    rw [this, hcst]
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    have hab' : p.lab[a]! = p.lab[b]! := hab
    have h1 := hp.posLab a (by omega)
    have h2 := hp.posLab b (by omega)
    rw [hab', h2] at h1
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    refine ⟨p.pos[u]!, ?_, hp.labPos u hu.1⟩
    have hpu : p.pos[u]! < n := hp.posLt u hu.1
    have hmem := (hp.cst_eq_iff hc hpu).1 (by rw [hu.2.1, hcst])
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rw [hcst] at hmem
    exact ⟨⟨hmem.1, hmem.2⟩, by rw [hp.labPos u hu.1]; simpa using hu.2.2⟩

/-- Distinct positions of a duplicate-free array hold distinct values. -/
theorem nodup_getElem!_ne {a : Array Nat} (h : a.toList.Nodup) {i j : Nat} (hi : i < a.size)
    (hj : j < a.size) (hij : i ≠ j) : a[i]! ≠ a[j]! := by
  rw [getElem!_pos a i hi, getElem!_pos a j hj]
  intro he
  exact hij ((List.Nodup.getElem_inj_iff h).mp (by simpa using he))

theorem offsetFrom_size1 (ks : Array Nat) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat),
      (offsetFrom ks fuel j sizes bc acc).1.size = sizes.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, sizes, bc, acc => by
    rw [offsetFrom]
    split
    · rfl
    · rw [offsetFrom_size1 ks fuel (j + 1) _ _ _]
      simp

theorem offsetFrom_size2 (ks : Array Nat) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat),
      (offsetFrom ks fuel j sizes bc acc).2.size = bc.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, sizes, bc, acc => by
    rw [offsetFrom]
    split
    · rfl
    · rw [offsetFrom_size2 ks fuel (j + 1) _ _ _]
      simp

/-- The pass writes only at the indices named in `ks[j:]`. -/
theorem offsetFrom_ne (ks : Array Nat) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc x : Nat),
      (∀ i, j ≤ i → i < ks.size → x ≠ ks[i]!) → (offsetFrom ks fuel j sizes bc acc).2[x]! = bc[x]!
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, j, sizes, bc, acc, x, hx => by
    rw [offsetFrom]
    split
    · rfl
    · rename_i hj
      rw [offsetFrom_ne ks fuel (j + 1) _ _ _ x (fun i h1 h2 => hx i (by omega) h2),
        getElem!_set!_ne (hx j (by omega) (by omega))]

/-- **The fragment sizes**: `sizes[j]` is the size of the bucket of the `j`-th count. -/
theorem offsetFrom_sizes (ks : Array Nat) (hnd : ks.toList.Nodup) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat), ks.size ≤ j + fuel →
      sizes.size = ks.size → ∀ i, i < ks.size →
        (offsetFrom ks fuel j sizes bc acc).1[i]! = if i < j then sizes[i]! else bc[ks[i]!]!
  | 0, j, sizes, bc, acc, hf, hsz, i, hi => by
    rw [offsetFrom, if_pos (by omega)]
  | fuel + 1, j, sizes, bc, acc, hf, hsz, i, hi => by
    rw [offsetFrom]
    split
    · rw [if_pos (by omega)]
    · rename_i hj
      rw [offsetFrom_sizes ks hnd fuel (j + 1) _ _ _ (by omega) (by simpa using hsz) i hi]
      rcases Nat.lt_trichotomy i j with h | h | h
      · rw [if_pos (by omega), if_pos h, getElem!_set!_ne (by omega : i ≠ j)]
      · subst h
        rw [if_pos (by omega), if_neg (by omega), getElem!_set! (by omega : i < sizes.size) i,
          if_pos rfl]
      · rw [if_neg (by omega), if_neg (by omega),
          getElem!_set!_ne (nodup_getElem!_ne hnd hi (by omega) (by omega))]

/-- **The fragment offsets**: after the pass, the bucket of the `i`-th count starts at the sum of
the sizes of the buckets before it. -/
theorem offsetFrom_bc (ks : Array Nat) (hnd : ks.toList.Nodup) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat), ks.size ≤ j + fuel →
      (∀ i, i < ks.size → ks[i]! < bc.size) → ∀ i, j ≤ i → i < ks.size →
        (offsetFrom ks fuel j sizes bc acc).2[ks[i]!]!
          = acc + ∑ i' ∈ Finset.Ico j i, bc[ks[i']!]!
  | 0, j, sizes, bc, acc, hf, hks, i, hji, hi => by omega
  | fuel + 1, j, sizes, bc, acc, hf, hks, i, hji, hi => by
    rw [offsetFrom]
    split
    · omega
    · rename_i hj
      rcases Nat.eq_or_lt_of_le hji with h | h
      · subst h
        rw [Finset.Ico_self, Finset.sum_empty, Nat.add_zero,
          offsetFrom_ne ks fuel (j + 1) _ _ _ _
            (fun i' h1 h2 => nodup_getElem!_ne hnd hi h2 (by omega)),
          getElem!_set! (hks j hi) _, if_pos rfl]
        omega
      · have hsplit : ∑ i' ∈ Finset.Ico j i, bc[ks[i']!]!
            = bc[ks[j]!]! + ∑ i' ∈ Finset.Ico (j + 1) i, bc[ks[i']!]! :=
          Finset.sum_eq_sum_Ico_succ_bot h _
        have hterm : ∀ i' ∈ Finset.Ico (j + 1) i,
            (bc.set! ks[j]! acc)[ks[i']!]! = bc[ks[i']!]! := by
          intro i' hi'
          rw [Finset.mem_Ico] at hi'
          exact getElem!_set!_ne (nodup_getElem!_ne hnd (by omega) (by omega) (by omega))
        rw [offsetFrom_bc ks hnd fuel (j + 1) _ _ _ (by omega) (by simpa using hks) i (by omega) hi,
          Finset.sum_congr rfl hterm, hsplit]
        omega

theorem bucketSize_split (lab cnt : Array Nat) {k i ec t : Nat} (h1 : k ≤ i) (h2 : i ≤ ec) :
    bucketSize lab cnt k ec t = bucketSize lab cnt k i t + bucketSize lab cnt i ec t := by
  rw [bucketSize, bucketSize, bucketSize, Finset.sum_Ico_consecutive _ h1 h2]

theorem bucketSize_mono (lab cnt : Array Nat) {k i ec t : Nat} (h1 : k ≤ i) (h2 : i ≤ ec) :
    bucketSize lab cnt i ec t ≤ bucketSize lab cnt k ec t := by
  rw [bucketSize_split lab cnt h1 h2]
  omega

theorem bucketSize_pos (lab cnt : Array Nat) {k ec t : Nat} (h : k < ec)
    (ht : cnt[lab[k]!]! = t) : 0 < bucketSize lab cnt k ec t := by
  rw [bucketSize_succ lab cnt h, if_pos ht]
  omega

theorem scatterFrom_size1 (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat),
      (scatterFrom lab cnt ec fuel k block bc).1.size = block.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, block, bc => by
    rw [scatterFrom]
    split
    · rfl
    · rw [scatterFrom_size1 lab cnt ec fuel (k + 1) _ _]
      simp

theorem scatterFrom_size2 (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat),
      (scatterFrom lab cnt ec fuel k block bc).2.size = bc.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, block, bc => by
    rw [scatterFrom]
    split
    · rfl
    · rw [scatterFrom_size2 lab cnt ec fuel (k + 1) _ _]
      simp

/-- The offset the scatter writes the vertex at position `i` to, as seen from position `k`: the
bucket's current offset plus the number of items of the same count already scattered. -/
def scatterAt (lab cnt bc : Array Nat) (k i : Nat) : Nat :=
  bc[cnt[lab[i]!]!]! + bucketSize lab cnt k i (cnt[lab[i]!]!)

/-- Taking one step leaves every later item's target offset where it was: the bucket that just
grew also advanced by one. -/
theorem scatterAt_step (lab cnt bc : Array Nat) {k i : Nat} (hk : k < i)
    (hb : cnt[lab[k]!]! < bc.size) :
    scatterAt lab cnt (bc.set! cnt[lab[k]!]! (bc[cnt[lab[k]!]!]! + 1)) (k + 1) i
      = scatterAt lab cnt bc k i := by
  rw [scatterAt, scatterAt, bucketSize_succ lab cnt hk]
  by_cases h : cnt[lab[i]!]! = cnt[lab[k]!]!
  · rw [h, getElem!_set! hb _, if_pos rfl, if_pos rfl]
    omega
  · rw [getElem!_set!_ne h, if_neg (by simpa using fun h' => h h'.symm)]
    omega

/-- The scatter writes only at the offsets its remaining items name. -/
theorem scatterFrom_ne (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat) (o : Nat), (∀ (v : Nat), cnt[v]! < bc.size) →
      (∀ i, k ≤ i → i < ec → scatterAt lab cnt bc k i ≠ o) →
        (scatterFrom lab cnt ec fuel k block bc).1[o]! = block[o]!
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, k, block, bc, o, hcb, ho => by
    rw [scatterFrom]
    split
    · rfl
    · rename_i hk
      have hne : bc[cnt[lab[k]!]!]! ≠ o := by
        have := ho k (by omega) (by omega)
        rwa [scatterAt, bucketSize_zero lab cnt (by omega), Nat.add_zero] at this
      rw [scatterFrom_ne lab cnt ec fuel (k + 1) _ _ o (by simpa using hcb) ?_,
        getElem!_set!_ne (by simpa using fun h => hne h.symm)]
      intro i h1 h2
      rw [scatterAt_step lab cnt bc (by omega) (hcb _)]
      exact ho i (by omega) h2

/-- The buckets do not overlap: distinct counts have disjoint offset ranges, each as wide as the
number of items still to be scattered into it. -/
def Sep (lab cnt : Array Nat) (k ec : Nat) (bc : Array Nat) : Prop :=
  ∀ t t' : Nat, t ≠ t' → ∀ a b : Nat, a < bucketSize lab cnt k ec t →
    b < bucketSize lab cnt k ec t' → bc[t]! + a ≠ bc[t']! + b

theorem Sep.step {lab cnt bc : Array Nat} {k ec : Nat} (h : Sep lab cnt k ec bc) (hk : k < ec)
    (hb : cnt[lab[k]!]! < bc.size) :
    Sep lab cnt (k + 1) ec (bc.set! cnt[lab[k]!]! (bc[cnt[lab[k]!]!]! + 1)) := by
  intro t t' htt a b ha hb'
  have hmono : ∀ u : Nat, bucketSize lab cnt (k + 1) ec u ≤ bucketSize lab cnt k ec u :=
    fun u => bucketSize_mono lab cnt (by omega) (by omega)
  have hstep : ∀ u : Nat, bucketSize lab cnt k ec u
      = (if cnt[lab[k]!]! = u then 1 else 0) + bucketSize lab cnt (k + 1) ec u :=
    fun u => bucketSize_succ lab cnt hk
  by_cases ht0 : t = cnt[lab[k]!]!
  · have ht0' : t' ≠ cnt[lab[k]!]! := fun h' => htt (ht0.trans h'.symm)
    rw [getElem!_set! hb t, if_pos ht0, getElem!_set!_ne ht0', ← ht0]
    have h1 : a + 1 < bucketSize lab cnt k ec t := by
      have := hstep t
      rw [if_pos ht0.symm] at this
      omega
    have := h t t' htt (a + 1) b h1 (by have := hmono t'; omega)
    omega
  · by_cases ht0' : t' = cnt[lab[k]!]!
    · rw [getElem!_set!_ne ht0, getElem!_set! hb t', if_pos ht0', ← ht0']
      have h1 : b + 1 < bucketSize lab cnt k ec t' := by
        have := hstep t'
        rw [if_pos ht0'.symm] at this
        omega
      have := h t t' htt a (b + 1) (by have := hmono t; omega) h1
      omega
    · rw [getElem!_set!_ne ht0, getElem!_set!_ne ht0']
      exact h t t' htt a b (by have := hmono t; omega) (by have := hmono t'; omega)

/-- **Where the scatter puts each vertex.**  The vertex at position `i` of the cell lands at its
bucket's offset plus the number of same-count vertices before it — a stable counting sort. -/
theorem scatterFrom_block (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat), ec ≤ k + fuel → (∀ (v : Nat), cnt[v]! < bc.size) →
      Sep lab cnt k ec bc → (∀ i, k ≤ i → i < ec → scatterAt lab cnt bc k i < block.size) →
        ∀ i, k ≤ i → i < ec →
          (scatterFrom lab cnt ec fuel k block bc).1[scatterAt lab cnt bc k i]! = lab[i]!
  | 0, k, block, bc, hf, _, _, _, i, h1, h2 => by omega
  | fuel + 1, k, block, bc, hf, hcb, hsep, hrange, i, h1, h2 => by
    rw [scatterFrom]
    split
    · omega
    · rename_i hk
      have hbk : cnt[lab[k]!]! < bc.size := hcb _
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · -- the vertex written now: no later write lands on the offset it just took
        subst h
        have hbsz : bc[cnt[lab[k]!]!]! < block.size := by
          have := hrange k (le_refl k) (by omega)
          rwa [scatterAt, bucketSize_zero lab cnt (le_refl k), Nat.add_zero] at this
        rw [scatterAt, bucketSize_zero lab cnt (le_refl k), Nat.add_zero,
          scatterFrom_ne lab cnt ec fuel (k + 1) _ _ _ (by simpa using hcb) ?_,
          getElem!_set! hbsz _, if_pos (Nat.add_zero _)]
        intro i' h1' h2'
        rw [scatterAt_step lab cnt bc (by omega) hbk, scatterAt]
        by_cases ht : cnt[lab[i']!]! = cnt[lab[k]!]!
        · rw [ht]
          have : 0 < bucketSize lab cnt k i' cnt[lab[k]!]! :=
            bucketSize_pos lab cnt (by omega) rfl
          omega
        · have hb1 : bucketSize lab cnt k i' cnt[lab[i']!]!
              < bucketSize lab cnt k ec cnt[lab[i']!]! := by
            rw [bucketSize_split lab cnt (show k ≤ i' by omega) (show i' ≤ ec by omega)]
            have := bucketSize_pos lab cnt (k := i') (ec := ec) (t := cnt[lab[i']!]!)
              (by omega) rfl
            omega
          have hb2 : 0 < bucketSize lab cnt k ec cnt[lab[k]!]! :=
            bucketSize_pos lab cnt (by omega) rfl
          exact hsep _ _ ht _ 0 hb1 hb2
      · rw [← scatterAt_step lab cnt bc h hbk]
        refine scatterFrom_block lab cnt ec fuel (k + 1) _ _ (by omega) (by simpa using hcb)
          (hsep.step (by omega) hbk) ?_ i (by omega) h2
        intro i' h1' h2'
        rw [scatterAt_step lab cnt bc (by omega) hbk]
        simpa using hrange i' (by omega) h2'

/-! ### Writing the sorted block back -/

theorem writeFrom_size1 (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), (writeFrom block c fuel k lab pos).1.size = lab.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, lab, pos => by
    rw [writeFrom]
    split
    · rfl
    · rw [writeFrom_size1 block c fuel (k + 1) _ _]
      simp

theorem writeFrom_size2 (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), (writeFrom block c fuel k lab pos).2.size = pos.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, lab, pos => by
    rw [writeFrom]
    split
    · rfl
    · rw [writeFrom_size2 block c fuel (k + 1) _ _]
      simp

/-- Positions outside the cell keep their label. -/
theorem writeFrom_lab_ne (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat) (x : Nat), (x < c + k ∨ c + block.size ≤ x) →
      (writeFrom block c fuel k lab pos).1[x]! = lab[x]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, k, lab, pos, x, hx => by
    rw [writeFrom]
    split
    · rfl
    · rw [writeFrom_lab_ne block c fuel (k + 1) _ _ x (by omega),
        getElem!_set!_ne (by omega : x ≠ c + k)]

/-- The block is laid down at positions `c, c+1, …`. -/
theorem writeFrom_lab (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), block.size ≤ k + fuel → c + block.size ≤ lab.size →
      ∀ m, k ≤ m → m < block.size → (writeFrom block c fuel k lab pos).1[c + m]! = block[m]!
  | 0, k, lab, pos, hf, _, m, h1, h2 => by omega
  | fuel + 1, k, lab, pos, hf, hlab, m, h1, h2 => by
    rw [writeFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        rw [writeFrom_lab_ne block c fuel (k + 1) _ _ _ (by omega),
          getElem!_set! (by omega) _, if_pos rfl]
      · exact writeFrom_lab block c fuel (k + 1) _ _ (by omega) (by simpa using hlab) m
          (by omega) h2

/-- Vertices the block does not mention keep their position. -/
theorem writeFrom_pos_ne (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat) (v : Nat),
      (∀ m, k ≤ m → m < block.size → block[m]! ≠ v) →
        (writeFrom block c fuel k lab pos).2[v]! = pos[v]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, k, lab, pos, v, hv => by
    rw [writeFrom]
    split
    · rfl
    · rename_i hk
      rw [writeFrom_pos_ne block c fuel (k + 1) _ _ v (fun m h1 h2 => hv m (by omega) h2),
        getElem!_set!_ne (Ne.symm (hv k (by omega) (by omega)))]

/-- **Where each vertex of the block ends up.**  The block has no repeats, so the write that
places a vertex is the only one that touches its position. -/
theorem writeFrom_pos (block : Array Nat) (c : Nat) (hnd : block.toList.Nodup) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), block.size ≤ k + fuel →
      (∀ m, m < block.size → block[m]! < pos.size) →
        ∀ m, k ≤ m → m < block.size → (writeFrom block c fuel k lab pos).2[block[m]!]! = c + m
  | 0, k, lab, pos, hf, _, m, h1, h2 => by omega
  | fuel + 1, k, lab, pos, hf, hp, m, h1, h2 => by
    rw [writeFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        rw [writeFrom_pos_ne block c fuel (k + 1) _ _ _
            (fun m' h1' h2' => nodup_getElem!_ne hnd h2' h2 (by omega)),
          getElem!_set! (hp k h2) _, if_pos rfl]
      · exact writeFrom_pos block c hnd fuel (k + 1) _ _ (by omega) (by simpa using hp) m
          (by omega) h2

/-! ### The fragment boundaries -/

theorem fillBoundsFrom_size1 (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat),
    (fillBoundsFrom st en fuel i cst cen).1.size = cst.size
  | 0, _, _, _ => rfl
  | fuel + 1, i, cst, cen => by
    rw [fillBoundsFrom]
    split
    · rfl
    · rw [fillBoundsFrom_size1 st en fuel (i + 1) _ _]
      simp

theorem fillBoundsFrom_size2 (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat),
    (fillBoundsFrom st en fuel i cst cen).2.size = cen.size
  | 0, _, _, _ => rfl
  | fuel + 1, i, cst, cen => by
    rw [fillBoundsFrom]
    split
    · rfl
    · rw [fillBoundsFrom_size2 st en fuel (i + 1) _ _]
      simp

theorem fillBoundsFrom_ne (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat) (x : Nat),
    (x < i ∨ en ≤ x) → (fillBoundsFrom st en fuel i cst cen).1[x]! = cst[x]!
      ∧ (fillBoundsFrom st en fuel i cst cen).2[x]! = cen[x]!
  | 0, _, _, _, _, _ => ⟨rfl, rfl⟩
  | fuel + 1, i, cst, cen, x, hx => by
    rw [fillBoundsFrom]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hi
      obtain ⟨h1, h2⟩ := fillBoundsFrom_ne st en fuel (i + 1) (cst.set! i st) (cen.set! i en) x
        (by omega)
      exact ⟨by rw [h1, getElem!_set!_ne (by omega : x ≠ i)],
        by rw [h2, getElem!_set!_ne (by omega : x ≠ i)]⟩

theorem fillBoundsFrom_getElem! (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat),
    en ≤ i + fuel → en ≤ cst.size → en ≤ cen.size → ∀ x, i ≤ x → x < en →
      (fillBoundsFrom st en fuel i cst cen).1[x]! = st
        ∧ (fillBoundsFrom st en fuel i cst cen).2[x]! = en
  | 0, i, cst, cen, hf, _, _, x, h1, h2 => by omega
  | fuel + 1, i, cst, cen, hf, hc1, hc2, x, h1, h2 => by
    rw [fillBoundsFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        obtain ⟨e1, e2⟩ := fillBoundsFrom_ne st en fuel (i + 1) (cst.set! i st) (cen.set! i en) i
          (by omega)
        exact ⟨by rw [e1, getElem!_set! (by omega) _, if_pos rfl],
          by rw [e2, getElem!_set! (by omega) _, if_pos rfl]⟩
      · exact fillBoundsFrom_getElem! st en fuel (i + 1) _ _ (by omega) (by simpa using hc1)
          (by simpa using hc2) x (by omega) h2

/-- The total size of the fragments `[a, b)`. -/
def sizesSum (sizes : Array Nat) (a b : Nat) : Nat := ∑ j ∈ Finset.Ico a b, sizes[j]!

theorem sizesSum_self (sizes : Array Nat) (a : Nat) : sizesSum sizes a a = 0 := by
  simp [sizesSum]

theorem sizesSum_succ (sizes : Array Nat) {a b : Nat} (h : a < b) :
    sizesSum sizes a b = sizes[a]! + sizesSum sizes (a + 1) b := by
  rw [sizesSum, sizesSum, Finset.sum_eq_sum_Ico_succ_bot h]

theorem sizesSum_le (sizes : Array Nat) {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    sizesSum sizes a b ≤ sizesSum sizes a c := by
  rw [sizesSum, sizesSum, ← Finset.sum_Ico_consecutive _ h1 h2]
  omega

theorem sizesSum_split (sizes : Array Nat) {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    sizesSum sizes a c = sizesSum sizes a b + sizesSum sizes b c := by
  rw [sizesSum, sizesSum, sizesSum, Finset.sum_Ico_consecutive _ h1 h2]

/-- Positions outside the split cell keep their boundaries. -/
theorem boundsFrom_ne (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64) (x : Nat),
      (x < st ∨ st + sizesSum sizes j ks.size ≤ x) →
        (boundsFrom ks sizes fuel j cst cen starts st tr).1[x]! = cst[x]!
          ∧ (boundsFrom ks sizes fuel j cst cen starts st tr).2.1[x]! = cen[x]!
  | 0, _, _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | fuel + 1, j, cst, cen, starts, st, tr, x, hx => by
    rw [boundsFrom]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hj
      have hsz : sizes[j]! ≤ sizesSum sizes j ks.size := by
        rw [sizesSum_succ sizes (show j < ks.size by omega)]
        omega
      have hsub : sizesSum sizes (j + 1) ks.size + sizes[j]! = sizesSum sizes j ks.size := by
        rw [sizesSum_succ sizes (show j < ks.size by omega)]
        omega
      obtain ⟨h1, h2⟩ := boundsFrom_ne ks sizes fuel (j + 1)
        (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).1
        (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).2
        (starts.push st) (st + sizes[j]!) (mixN (mixN tr sizes[j]!) ks[j]!) x (by omega)
      obtain ⟨e1, e2⟩ := fillBoundsFrom_ne st (st + sizes[j]!) sizes[j]! st cst cen x (by omega)
      exact ⟨by rw [h1, e1], by rw [h2, e2]⟩

/-- **The boundaries the split installs.**  Every position of fragment `j'` reports that
fragment's range. -/
theorem boundsFrom_getElem! (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64), ks.size ≤ j + fuel →
      st + sizesSum sizes j ks.size ≤ cst.size → st + sizesSum sizes j ks.size ≤ cen.size →
        ∀ j', j ≤ j' → j' < ks.size → ∀ x, st + sizesSum sizes j j' ≤ x →
          x < st + sizesSum sizes j (j' + 1) →
            (boundsFrom ks sizes fuel j cst cen starts st tr).1[x]!
                = st + sizesSum sizes j j'
              ∧ (boundsFrom ks sizes fuel j cst cen starts st tr).2.1[x]!
                = st + sizesSum sizes j (j' + 1)
  | 0, j, cst, cen, starts, st, tr, hf, _, _, j', h1, h2, x, _, _ => by omega
  | fuel + 1, j, cst, cen, starts, st, tr, hf, hc1, hc2, j', h1, h2, x, hx1, hx2 => by
    rw [boundsFrom]
    split
    · omega
    · rename_i hj
      have hsub : ∀ m, j + 1 ≤ m → sizesSum sizes j m = sizes[j]! + sizesSum sizes (j + 1) m :=
        fun m hm => sizesSum_succ sizes (by omega)
      have hcell : st + sizes[j]! + sizesSum sizes (j + 1) ks.size
          = st + sizesSum sizes j ks.size := by rw [hsub ks.size (by omega)]; omega
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · -- the fragment being written now
        subst h
        rw [sizesSum_self, Nat.add_zero] at hx1 ⊢
        rw [hsub (j + 1) (by omega), sizesSum_self, Nat.add_zero] at hx2 ⊢
        obtain ⟨e1, e2⟩ := boundsFrom_ne ks sizes fuel (j + 1)
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).1
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).2
          (starts.push st) (st + sizes[j]!) (mixN (mixN tr sizes[j]!) ks[j]!) x (by omega)
        obtain ⟨f1, f2⟩ := fillBoundsFrom_getElem! st (st + sizes[j]!) sizes[j]! st cst cen
          (by omega) (by omega) (by omega) x (by omega) (by omega)
        exact ⟨by rw [e1, f1]; omega, by rw [e2, f2]; omega⟩
      · have := boundsFrom_getElem! ks sizes fuel (j + 1)
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).1
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).2
          (starts.push st) (st + sizes[j]!) (mixN (mixN tr sizes[j]!) ks[j]!) (by omega)
          (by rw [fillBoundsFrom_size1]; omega) (by rw [fillBoundsFrom_size2]; omega)
          j' (by omega) h2 x (by rw [hsub j' (by omega)] at hx1; omega)
          (by rw [hsub (j' + 1) (by omega)] at hx2; omega)
        rw [hsub j' (by omega), hsub (j' + 1) (by omega)]
        constructor
        · rw [this.1]; omega
        · rw [this.2]; omega

/-! ### Odds and ends: array extensionality, the leftover bucket counters, clearing scratch -/

theorem array_ext! {α : Type _} [Inhabited α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  refine Array.ext hs fun i hi hi' => ?_
  have := h i hi
  rwa [getElem!_pos a i hi, getElem!_pos b i hi'] at this

theorem mem_iff_getElem! {a : Array Nat} {v : Nat} : v ∈ a ↔ ∃ i, i < a.size ∧ a[i]! = v := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
    exact ⟨i, hi, by rw [getElem!_pos a i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    rw [getElem!_pos a i hi]
    exact Array.getElem_mem hi

/-- Counters the scatter never advances keep their value. -/
theorem scatterFrom_bc_ne (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat) (t : Nat),
      (∀ i, k ≤ i → i < ec → cnt[lab[i]!]! ≠ t) →
        (scatterFrom lab cnt ec fuel k block bc).2[t]! = bc[t]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, k, block, bc, t, ht => by
    rw [scatterFrom]
    split
    · rfl
    · rename_i hk
      rw [scatterFrom_bc_ne lab cnt ec fuel (k + 1) _ _ t (fun i h1 h2 => ht i (by omega) h2),
        getElem!_set!_ne (Ne.symm (ht k (by omega) (by omega)))]

/-- The fragment starts and the trace do not depend on the boundary arrays being written. -/
theorem boundsFrom_congr (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen cst' cen' starts : Array Nat) (st : Nat) (tr : UInt64),
      (boundsFrom ks sizes fuel j cst cen starts st tr).2.2
        = (boundsFrom ks sizes fuel j cst' cen' starts st tr).2.2
  | 0, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, j, cst, cen, cst', cen', starts, st, tr => by
    rw [boundsFrom, boundsFrom]
    split
    · rfl
    · exact boundsFrom_congr ks sizes fuel (j + 1) _ _ _ _ _ _ _

theorem clearCntFrom_size (touched : Array Nat) : ∀ (fuel j : Nat) (cnt : Array Nat),
    (clearCntFrom touched fuel j cnt).size = cnt.size
  | 0, _, _ => rfl
  | fuel + 1, j, cnt => by
    rw [clearCntFrom]
    split
    · rfl
    · rw [clearCntFrom_size touched fuel (j + 1) _]
      simp

theorem clearCntFrom_ne (touched : Array Nat) : ∀ (fuel j : Nat) (cnt : Array Nat) (v : Nat),
    (∀ j', j ≤ j' → j' < touched.size → touched[j']! ≠ v) →
      (clearCntFrom touched fuel j cnt)[v]! = cnt[v]!
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, cnt, v, hv => by
    rw [clearCntFrom]
    split
    · rfl
    · rename_i hj
      rw [clearCntFrom_ne touched fuel (j + 1) _ v (fun j' h1 h2 => hv j' (by omega) h2),
        getElem!_set!_ne (Ne.symm (hv j (by omega) (by omega)))]

theorem clearCntFrom_mem (touched : Array Nat) : ∀ (fuel j : Nat) (cnt : Array Nat),
    touched.size ≤ j + fuel → ∀ j', j ≤ j' → j' < touched.size → touched[j']! < cnt.size →
      (clearCntFrom touched fuel j cnt)[touched[j']!]! = 0
  | 0, j, cnt, hf, j', h1, h2, _ => by omega
  | fuel + 1, j, cnt, hf, j', h1, h2, hlt => by
    rw [clearCntFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        by_cases hmem : ∀ j'', j + 1 ≤ j'' → j'' < touched.size → touched[j'']! ≠ touched[j]!
        · rw [clearCntFrom_ne touched fuel (j + 1) _ _ hmem, getElem!_set! hlt _, if_pos rfl]
        · push_neg at hmem
          obtain ⟨j'', hj1, hj2, hj3⟩ := hmem
          rw [← hj3]
          exact clearCntFrom_mem touched fuel (j + 1) _ (by omega) j'' hj1 hj2
            (by rw [hj3]; simpa using hlt)
      · exact clearCntFrom_mem touched fuel (j + 1) _ (by omega) j' (by omega) h2
          (by simpa using hlt)

/-- **Clearing the counts.**  Every vertex the counting loop touched is reset, so the scratch is
back to all zeros. -/
theorem clearCntFrom_zero {cnt touched : Array Nat} (h : Touched cnt touched) (v : Nat)
    (hv : v < cnt.size) : (clearCntFrom touched touched.size 0 cnt)[v]! = 0 := by
  by_cases hmem : v ∈ touched
  · obtain ⟨j, hj1, hj2⟩ := mem_iff_getElem!.1 hmem
    have := clearCntFrom_mem touched touched.size 0 cnt (by omega) j (by omega) hj1
      (by rw [hj2]; exact hv)
    rwa [hj2] at this
  · rw [clearCntFrom_ne touched touched.size 0 cnt v
      (fun j' _ h2 => fun he => hmem (he ▸ getElem!_mem h2))]
    by_contra hne
    exact hmem ((h.mem v hv).2 hne)

theorem clearHitFrom_ne (cells : Array Nat) : ∀ (fuel j : Nat) (hit : Array Bool) (v : Nat),
    (∀ j', j ≤ j' → j' < cells.size → cells[j']! ≠ v) →
      (clearHitFrom cells fuel j hit)[v]! = hit[v]!
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, hit, v, hv => by
    rw [clearHitFrom]
    split
    · rfl
    · rename_i hj
      rw [clearHitFrom_ne cells fuel (j + 1) _ v (fun j' h1 h2 => hv j' (by omega) h2),
        getElem!_set!_ne (Ne.symm (hv j (by omega) (by omega)))]

theorem clearHitFrom_mem (cells : Array Nat) : ∀ (fuel j : Nat) (hit : Array Bool),
    cells.size ≤ j + fuel → ∀ j', j ≤ j' → j' < cells.size → cells[j']! < hit.size →
      (clearHitFrom cells fuel j hit)[cells[j']!]! = false
  | 0, j, hit, hf, j', h1, h2, _ => by omega
  | fuel + 1, j, hit, hf, j', h1, h2, hlt => by
    rw [clearHitFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        by_cases hmem : ∀ j'', j + 1 ≤ j'' → j'' < cells.size → cells[j'']! ≠ cells[j]!
        · rw [clearHitFrom_ne cells fuel (j + 1) _ _ hmem, getElem!_set! hlt _, if_pos rfl]
        · push_neg at hmem
          obtain ⟨j'', hj1, hj2, hj3⟩ := hmem
          rw [← hj3]
          exact clearHitFrom_mem cells fuel (j + 1) _ (by omega) j'' hj1 hj2
            (by rw [hj3]; simpa using hlt)
      · exact clearHitFrom_mem cells fuel (j + 1) _ (by omega) j' (by omega) h2
          (by simpa using hlt)

/-- **Clearing the cell marks.**  Every collected cell is unmarked, so the scratch is back to all
`false`. -/
theorem clearHitFrom_zero {hit : Array Bool} {cells : Array Nat} (h : Collected hit cells)
    (v : Nat) (hv : v < hit.size) : (clearHitFrom cells cells.size 0 hit)[v]! = false := by
  by_cases hmem : v ∈ cells
  · obtain ⟨j, hj1, hj2⟩ := mem_iff_getElem!.1 hmem
    have := clearHitFrom_mem cells cells.size 0 hit (by omega) j (by omega) hj1
      (by rw [hj2]; exact hv)
    rwa [hj2] at this
  · rw [clearHitFrom_ne cells cells.size 0 hit v
      (fun j' _ h2 => fun he => hmem (he ▸ getElem!_mem h2))]
    by_contra hne
    exact hmem ((h.mem v hv).2 (by simpa using hne))

theorem clearBcFrom_size (ks : Array Nat) : ∀ (fuel j : Nat) (bc : Array Nat),
    (clearBcFrom ks fuel j bc).size = bc.size
  | 0, _, _ => rfl
  | fuel + 1, j, bc => by
    rw [clearBcFrom]
    split
    · rfl
    · rw [clearBcFrom_size ks fuel (j + 1) _]
      simp

theorem clearBcFrom_ne (ks : Array Nat) : ∀ (fuel j : Nat) (bc : Array Nat) (v : Nat),
    (∀ j', j ≤ j' → j' < ks.size → ks[j']! ≠ v) → (clearBcFrom ks fuel j bc)[v]! = bc[v]!
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, bc, v, hv => by
    rw [clearBcFrom]
    split
    · rfl
    · rename_i hj
      rw [clearBcFrom_ne ks fuel (j + 1) _ v (fun j' h1 h2 => hv j' (by omega) h2),
        getElem!_set!_ne (Ne.symm (hv j (by omega) (by omega)))]

theorem clearBcFrom_mem (ks : Array Nat) : ∀ (fuel j : Nat) (bc : Array Nat),
    ks.size ≤ j + fuel → ∀ j', j ≤ j' → j' < ks.size → ks[j']! < bc.size →
      (clearBcFrom ks fuel j bc)[ks[j']!]! = 0
  | 0, j, bc, hf, j', h1, h2, _ => by omega
  | fuel + 1, j, bc, hf, j', h1, h2, hlt => by
    rw [clearBcFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        by_cases hmem : ∀ j'', j + 1 ≤ j'' → j'' < ks.size → ks[j'']! ≠ ks[j]!
        · rw [clearBcFrom_ne ks fuel (j + 1) _ _ hmem, getElem!_set! hlt _, if_pos rfl]
        · push_neg at hmem
          obtain ⟨j'', hj1, hj2, hj3⟩ := hmem
          rw [← hj3]
          exact clearBcFrom_mem ks fuel (j + 1) _ (by omega) j'' hj1 hj2
            (by rw [hj3]; simpa using hlt)
      · exact clearBcFrom_mem ks fuel (j + 1) _ (by omega) j' (by omega) h2 (by simpa using hlt)

theorem bucketSize_card (lab cnt : Array Nat) (c ec t : Nat) :
    bucketSize lab cnt c ec t = ((Finset.Ico c ec).filter (fun i => cnt[lab[i]!]! = t)).card := by
  rw [bucketSize, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The fragments of a split cell exhaust it: the bucket sizes sum to the size of the cell. -/
theorem sum_bucketSize (lab cnt ks : Array Nat) {c ec : Nat} (hnd : ks.toList.Nodup)
    (hmem : ∀ i, c ≤ i → i < ec → ∃ j, j < ks.size ∧ ks[j]! = cnt[lab[i]!]!) :
    ∑ j ∈ Finset.range ks.size, bucketSize lab cnt c ec ks[j]! = ec - c := by
  have hinj : ∀ j ∈ Finset.range ks.size, ∀ j' ∈ Finset.range ks.size,
      ks[j]! = ks[j']! → j = j' := by
    intro j hj j' hj' h
    simp only [Finset.mem_range] at hj hj'
    by_contra hne
    exact nodup_getElem!_ne hnd hj hj' hne h
  have himg : ∀ i ∈ Finset.Ico c ec,
      cnt[lab[i]!]! ∈ (Finset.range ks.size).image (fun j => ks[j]!) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    obtain ⟨j, hj, hjv⟩ := hmem i hi.1 hi.2
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, hjv⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun i => cnt[lab[i]!]!) (s := Finset.Ico c ec)
    (t := (Finset.range ks.size).image (fun j => ks[j]!))
    (by intro i hi; simpa using himg i (by simpa using hi))
  rw [Finset.sum_image (by intro j hj j' hj' h; exact hinj j (by simpa using hj) j' (by simpa using hj') h)] at hcard
  simp only [bucketSize_card]
  rw [← hcard, Nat.card_Ico]

theorem pairwise_getElem!_lt {a : Array Nat} (hp : a.toList.Pairwise (· ≤ ·))
    (hnd : a.toList.Nodup) {i j : Nat} (hj : j < a.size) (hij : i < j) : a[i]! < a[j]! := by
  have hi : i < a.size := by omega
  have hle : a[i]! ≤ a[j]! := by
    have := List.pairwise_iff_getElem.1 hp i j (by simpa using hi) (by simpa using hj) hij
    rwa [getElem!_pos a i hi, getElem!_pos a j hj, ← Array.getElem_toList, ← Array.getElem_toList]
  exact lt_of_le_of_ne hle (nodup_getElem!_ne hnd hi hj (by omega))

theorem pairwise_getElem!_le {a : Array Nat} (hp : a.toList.Pairwise (· ≤ ·)) {i j : Nat}
    (hj : j < a.size) (hij : i ≤ j) : a[i]! ≤ a[j]! := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_refl _
  · have hi : i < a.size := by omega
    have := List.pairwise_iff_getElem.1 hp i j (by simpa using hi) (by simpa using hj) h
    rwa [getElem!_pos a i hi, getElem!_pos a j hj, ← Array.getElem_toList, ← Array.getElem_toList]

/-- Where the fragment of neighbour count `t` starts: after every vertex of the cell with a
smaller count.  The point of this description is that it never mentions the bucket list, so two
runs of `refineStep` on isomorphic inputs manifestly agree on it. -/
def fragStart (n : Nat) (p : Part) (cnt : Array Nat) (c t : Nat) : Nat :=
  c + ∑ t' ∈ Finset.range t, cellCount n p c (fun u => cnt[u]! == t')

/-- The prefix sums the algorithm computes are the fragment starts.  The bucket list is sorted
and holds exactly the counts that occur, so summing along it is summing over all smaller counts. -/
theorem fragStart_eq {n : Nat} {p : Part} {c : Nat} {cnt ks sizes : Array Nat}
    (hnd : ks.toList.Nodup) (hsorted : ks.toList.Pairwise (· ≤ ·))
    (hmem : ∀ t, t ∈ ks ↔ cellCount n p c (fun u => cnt[u]! == t) ≠ 0)
    (hsizes : ∀ j, j < ks.size → sizes[j]! = cellCount n p c (fun u => cnt[u]! == ks[j]!))
    (j : Nat) (hj : j < ks.size) :
    c + sizesSum sizes 0 j = fragStart n p cnt c ks[j]! := by
  have hs : sizesSum sizes 0 j
      = ∑ j' ∈ Finset.Ico 0 j, cellCount n p c (fun u => cnt[u]! == ks[j']!) := by
    rw [sizesSum]
    exact Finset.sum_congr rfl fun j' hj' => hsizes j' (by
      simp only [Finset.mem_Ico] at hj'; omega)
  have key : ∑ j' ∈ Finset.Ico 0 j, cellCount n p c (fun u => cnt[u]! == ks[j']!)
      = ∑ t' ∈ Finset.range ks[j]!, cellCount n p c (fun u => cnt[u]! == t') := by
    rw [← Finset.sum_filter_ne_zero (Finset.range ks[j]!)]
    refine Finset.sum_bij (fun j' _ => ks[j']!) ?_ ?_ ?_ ?_
    · intro j' hj'
      simp only [Finset.mem_Ico] at hj'
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨pairwise_getElem!_lt hsorted hnd hj (by omega),
        (hmem ks[j']!).1 (getElem!_mem (by omega))⟩
    · intro a ha b hb hab
      simp only [Finset.mem_Ico] at ha hb
      by_contra hne
      exact nodup_getElem!_ne hnd (show a < ks.size by omega) (show b < ks.size by omega) hne hab
    · intro t' ht'
      simp only [Finset.mem_filter, Finset.mem_range] at ht'
      obtain ⟨j'', hj''1, hj''2⟩ := mem_iff_getElem!.1 ((hmem t').2 ht'.2)
      refine ⟨j'', ?_, hj''2⟩
      simp only [Finset.mem_Ico]
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hle
      have : ks[j]! ≤ ks[j'']! := pairwise_getElem!_le hsorted hj''1 (by omega)
      omega
    · intro a _
      rfl
  rw [fragStart, hs, key]

/-- The partition carried by the cell loop's state. -/
def SplitState.part (st : SplitState) : Part :=
  { lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen }

/-- **What splitting one cell does.**  Outside the cell `[c, cen[c])` nothing moves; inside, each
vertex lands in the fragment of its neighbour count, and the fragments sit in increasing order of
count.  Everything is phrased through `fragStart`/`cellCount`, which mention only the cell as a
set — that is what makes the description equivariant. -/
structure SplitOk (n : Nat) (p : Part) (cnt : Array Nat) (c : Nat) (p' : Part) : Prop where
  /-- The result is still a partition. -/
  wf : Part.WF n p'
  /-- Positions outside the cell keep their vertex. -/
  lab_ne : ∀ i, i < n → (i < c ∨ p.cen[c]! ≤ i) → p'.lab[i]! = p.lab[i]!
  /-- Positions outside the cell keep their cell start. -/
  cst_ne : ∀ i, i < n → (i < c ∨ p.cen[c]! ≤ i) → p'.cst[i]! = p.cst[i]!
  /-- Positions outside the cell keep their cell end. -/
  cen_ne : ∀ i, i < n → (i < c ∨ p.cen[c]! ≤ i) → p'.cen[i]! = p.cen[i]!
  /-- Vertices outside the cell keep their position. -/
  pos_ne : ∀ v, v < n → (p.pos[v]! < c ∨ p.cen[c]! ≤ p.pos[v]!) → p'.pos[v]! = p.pos[v]!
  /-- Vertices of the cell stay in it. -/
  pos_mem : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! →
    c ≤ p'.pos[v]! ∧ p'.pos[v]! < p.cen[c]!
  /-- A vertex of the cell lands in the fragment of its count. -/
  cell : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! →
    p'.cst[p'.pos[v]!]! = fragStart n p cnt c cnt[v]!
  /-- That fragment is as long as the number of cell vertices of that count. -/
  cen_cell : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! →
    p'.cen[p'.pos[v]!]! = fragStart n p cnt c cnt[v]!
      + cellCount n p c (fun u => cnt[u]! == cnt[v]!)

theorem cellCount_congr {n : Nat} {p : Part} {c : Nat} {P Q : Nat → Bool}
    (h : ∀ w, w < n → p.cst[p.pos[w]!]! = c → P w = Q w) :
    cellCount n p c P = cellCount n p c Q := by
  rw [cellCount, cellCount]
  congr 1
  refine Finset.filter_congr fun w hw => ?_
  simp only [Finset.mem_range] at hw
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← h w hw h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h w hw h1]; exact h2⟩

/-- A cell has as many vertices as it has positions. -/
theorem cellCount_true {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) : cellCount n p c (fun _ => true) = p.cen[c]! - c := by
  rw [cellCount, ← Nat.card_Ico c p.cen[c]!]
  refine Finset.card_bij (fun w _ => p.pos[w]!) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    have hpw : p.pos[w]! < n := hp.posLt w hw.1
    have := (hp.cst_eq_iff hc hpw).1 (by rw [hw.2.1, hcst])
    rw [hcst] at this
    simpa using this
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have h1 := hp.labPos a ha.1
    have h2 := hp.labPos b hb.1
    rw [show p.pos[a]! = p.pos[b]! from hab, h2] at h1
    omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    have hin : i < n := lt_of_lt_of_le hi.2 (hp.cenLe c hc)
    refine ⟨p.lab[i]!, ?_, hp.posLab i hin⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp.labLt i hin, ?_, trivial⟩
    rw [hp.posLab i hin, hp.cellCst c hc i (by rw [hcst]; omega) hi.2, hcst]

/-- **A cell whose vertices all have the same count does not split.**  Both easy branches of
`splitCell` are this: the cell is a singleton, or the counting pass found a single bucket. -/
theorem splitOk_of_uniform {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) (cnt : Array Nat)
    (huni : ∀ v w, v < n → w < n → p.cst[p.pos[v]!]! = c → p.cst[p.pos[w]!]! = c →
      cnt[v]! = cnt[w]!) :
    SplitOk n p cnt c p := by
  have hmem : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! → p.cst[p.pos[v]!]! = c := by
    intro v hv h1 h2
    rw [hp.cellCst c hc _ (by rw [hcst]; omega) h2, hcst]
  have hfrag : ∀ v, v < n → p.cst[p.pos[v]!]! = c → fragStart n p cnt c cnt[v]! = c := by
    intro v hv hvc
    rw [fragStart, Nat.add_eq_left]
    refine Finset.sum_eq_zero fun t' ht' => ?_
    simp only [Finset.mem_range] at ht'
    rw [cellCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw
    simp only [Finset.mem_range] at hw
    rintro ⟨hwc, hwt⟩
    have : cnt[w]! = t' := by simpa using hwt
    rw [← huni v w hv hw hvc hwc] at this
    omega
  refine ⟨hp, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ h1 h2 => ⟨h1, h2⟩, fun v hv h1 h2 => ?_, fun v hv h1 h2 => ?_⟩
  · rw [hmem v hv h1 h2, hfrag v hv (hmem v hv h1 h2)]
  · have hc' : c < p.cen[c]! := hp.ltCen c hc
    rw [hp.cellCen c hc _ (by rw [hcst]; omega) h2, hfrag v hv (hmem v hv h1 h2),
      cellCount_congr (P := fun u => cnt[u]! == cnt[v]!) (Q := fun _ => true)
        (fun w hw hwc => by rw [huni v w hv hw (hmem v hv h1 h2) hwc]; simp),
      cellCount_true hp hc hcst]
    omega

theorem boundsFrom_size1 (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64),
      (boundsFrom ks sizes fuel j cst cen starts st tr).1.size = cst.size
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, j, cst, cen, starts, st, tr => by
    rw [boundsFrom]
    split
    · rfl
    · rw [boundsFrom_size1 ks sizes fuel (j + 1) _ _ _ _ _, fillBoundsFrom_size1]

theorem boundsFrom_size2 (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64),
      (boundsFrom ks sizes fuel j cst cen starts st tr).2.1.size = cen.size
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, j, cst, cen, starts, st, tr => by
    rw [boundsFrom]
    split
    · rfl
    · rw [boundsFrom_size2 ks sizes fuel (j + 1) _ _ _ _ _, fillBoundsFrom_size2]

theorem sizesSum_one (sizes : Array Nat) (j : Nat) : sizesSum sizes j (j + 1) = sizes[j]! := by
  rw [sizesSum_succ sizes (Nat.lt_succ_self j), sizesSum_self]
  omega

/-- A nonempty bucket has a member. -/
theorem exists_of_bucketSize {lab cnt : Array Nat} {c ec t : Nat}
    (h : bucketSize lab cnt c ec t ≠ 0) : ∃ i, c ≤ i ∧ i < ec ∧ cnt[lab[i]!]! = t := by
  by_contra hno
  push_neg at hno
  refine h ?_
  rw [bucketSize]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  rw [if_neg (hno i hi.1 hi.2)]

/-! ### The counting sort is a permutation of the cell

Everything the scatter needs is packaged in `Offsets`: the counts occurring in the cell, in some
order and without duplicates (`ks`), their bucket sizes (`sizes`) and the offset each bucket was
given (`bc1`, the prefix sums).  From that alone the scatter is a bijection from the cell onto
`[0, ec - c)`. -/

/-- What the count-and-offset passes leave behind. -/
structure Offsets (lab cnt ks sizes bc1 : Array Nat) (c ec : Nat) : Prop where
  /-- The counts are listed once each. -/
  nodup : ks.toList.Nodup
  /-- `sizes[j]` is the size of bucket `ks[j]`. -/
  sizes_eq : ∀ j, j < ks.size → sizes[j]! = bucketSize lab cnt c ec ks[j]!
  /-- Bucket `ks[j]` was given the offset just past all earlier buckets. -/
  bc_eq : ∀ j, j < ks.size → bc1[ks[j]!]! = sizesSum sizes 0 j
  /-- Every count occurring in the cell is listed. -/
  mem : ∀ i, c ≤ i → i < ec → ∃ j, j < ks.size ∧ ks[j]! = cnt[lab[i]!]!

namespace Offsets

variable {lab cnt ks sizes bc1 : Array Nat} {c ec : Nat}

/-- The buckets exhaust the cell. -/
theorem total (h : Offsets lab cnt ks sizes bc1 c ec) : sizesSum sizes 0 ks.size = ec - c := by
  rw [sizesSum, ← Finset.range_eq_Ico, ← sum_bucketSize lab cnt ks h.nodup h.mem]
  exact Finset.sum_congr rfl fun j hj => h.sizes_eq j (Finset.mem_range.1 hj)

theorem index (h : Offsets lab cnt ks sizes bc1 c ec) {t : Nat}
    (ht : bucketSize lab cnt c ec t ≠ 0) : ∃ j, j < ks.size ∧ ks[j]! = t := by
  obtain ⟨i, h1, h2, h3⟩ := exists_of_bucketSize ht
  obtain ⟨j, hj, hjv⟩ := h.mem i h1 h2
  exact ⟨j, hj, by rw [hjv, h3]⟩

/-- Distinct buckets get disjoint ranges of slots. -/
theorem sep (h : Offsets lab cnt ks sizes bc1 c ec) : Sep lab cnt c ec bc1 := by
  intro t t' htt a b ha hb
  obtain ⟨j, hj, hjt⟩ := h.index (t := t) (by omega)
  obtain ⟨j', hj', hjt'⟩ := h.index (t := t') (by omega)
  have hne : j ≠ j' := by
    rintro rfl
    exact htt (by rw [← hjt, hjt'])
  have hja : a < sizes[j]! := by rw [h.sizes_eq j hj, hjt]; omega
  have hjb : b < sizes[j']! := by rw [h.sizes_eq j' hj', hjt']; omega
  rw [← hjt, ← hjt', h.bc_eq j hj, h.bc_eq j' hj']
  rcases Nat.lt_or_ge j j' with hlt | hge
  · have h1 : sizesSum sizes 0 (j + 1) ≤ sizesSum sizes 0 j' :=
      sizesSum_le sizes (by omega) (by omega)
    rw [sizesSum_split sizes (Nat.zero_le j) (Nat.le_succ j), sizesSum_one] at h1
    omega
  · have hne' : j' < j := by omega
    have h1 : sizesSum sizes 0 (j' + 1) ≤ sizesSum sizes 0 j :=
      sizesSum_le sizes (by omega) (by omega)
    rw [sizesSum_split sizes (Nat.zero_le j') (Nat.le_succ j'), sizesSum_one] at h1
    omega

/-- The slot a cell position is scattered to lies in its bucket's range. -/
theorem scatterAt_mem (h : Offsets lab cnt ks sizes bc1 c ec) {i : Nat} (h1 : c ≤ i) (h2 : i < ec)
    {j : Nat} (hj : j < ks.size) (hjt : ks[j]! = cnt[lab[i]!]!) :
    sizesSum sizes 0 j ≤ scatterAt lab cnt bc1 c i
      ∧ scatterAt lab cnt bc1 c i < sizesSum sizes 0 (j + 1) := by
  have hsplit : bucketSize lab cnt c ec cnt[lab[i]!]!
      = bucketSize lab cnt c i cnt[lab[i]!]! + bucketSize lab cnt i ec cnt[lab[i]!]! :=
    bucketSize_split lab cnt (by omega) (by omega)
  have hpos : 0 < bucketSize lab cnt i ec cnt[lab[i]!]! := bucketSize_pos lab cnt h2 rfl
  have hsz : sizes[j]! = bucketSize lab cnt c ec cnt[lab[i]!]! := by rw [h.sizes_eq j hj, hjt]
  have hbc : bc1[cnt[lab[i]!]!]! = sizesSum sizes 0 j := by rw [← hjt, h.bc_eq j hj]
  rw [scatterAt, hbc, sizesSum_split sizes (Nat.zero_le j) (Nat.le_succ j), sizesSum_one]
  omega

theorem scatterAt_lt (h : Offsets lab cnt ks sizes bc1 c ec) {i : Nat} (h1 : c ≤ i) (h2 : i < ec) :
    scatterAt lab cnt bc1 c i < ec - c := by
  obtain ⟨j, hj, hjt⟩ := h.mem i h1 h2
  have := (h.scatterAt_mem h1 h2 hj hjt).2
  have hle : sizesSum sizes 0 (j + 1) ≤ sizesSum sizes 0 ks.size :=
    sizesSum_le sizes (by omega) (by omega)
  rw [h.total] at hle
  omega

/-- Distinct cell positions are scattered to distinct slots. -/
theorem scatterAt_ne (h : Offsets lab cnt ks sizes bc1 c ec) {i i' : Nat} (h1 : c ≤ i)
    (hii : i < i') (h2 : i' < ec) :
    scatterAt lab cnt bc1 c i ≠ scatterAt lab cnt bc1 c i' := by
  by_cases ht : cnt[lab[i]!]! = cnt[lab[i']!]!
  · -- same bucket: `i` was scattered before `i'`, so it sits at a smaller offset
    have hstep : bucketSize lab cnt c (i + 1) cnt[lab[i]!]!
        = bucketSize lab cnt c i cnt[lab[i]!]! + 1 := by
      rw [bucketSize_split lab cnt (show c ≤ i by omega) (Nat.le_succ i),
        bucketSize_succ lab cnt (Nat.lt_succ_self i), if_pos rfl,
        bucketSize_zero lab cnt (le_refl _)]
    have hmono : bucketSize lab cnt c (i + 1) cnt[lab[i]!]!
        ≤ bucketSize lab cnt c i' cnt[lab[i]!]! := by
      rw [bucketSize_split lab cnt (show c ≤ i + 1 by omega) (show i + 1 ≤ i' by omega)]
      omega
    rw [scatterAt, scatterAt, ← ht]
    omega
  · have hi : bucketSize lab cnt c i cnt[lab[i]!]! < bucketSize lab cnt c ec cnt[lab[i]!]! := by
      have := bucketSize_pos lab cnt (show i < ec by omega) (rfl (a := cnt[lab[i]!]!))
      rw [bucketSize_split lab cnt (show c ≤ i by omega) (show i ≤ ec by omega)]
      omega
    have hi' : bucketSize lab cnt c i' cnt[lab[i']!]! < bucketSize lab cnt c ec cnt[lab[i']!]! := by
      have := bucketSize_pos lab cnt h2 (rfl (a := cnt[lab[i']!]!))
      rw [bucketSize_split lab cnt (show c ≤ i' by omega) (show i' ≤ ec by omega)]
      omega
    exact h.sep _ _ ht _ _ hi hi'

theorem scatterAt_inj (h : Offsets lab cnt ks sizes bc1 c ec) {i i' : Nat} (h1 : c ≤ i)
    (h2 : i < ec) (h1' : c ≤ i') (h2' : i' < ec)
    (he : scatterAt lab cnt bc1 c i = scatterAt lab cnt bc1 c i') : i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd he (h.scatterAt_ne h1 hlt h2')
  · exact heq
  · exact absurd he.symm (h.scatterAt_ne h1' hgt h2)

/-- **The scatter is onto**: every slot of the block is written. -/
theorem scatterAt_surj (h : Offsets lab cnt ks sizes bc1 c ec) {m : Nat} (hm : m < ec - c) :
    ∃ i, c ≤ i ∧ i < ec ∧ scatterAt lab cnt bc1 c i = m := by
  have himg : (Finset.Ico c ec).image (fun i => scatterAt lab cnt bc1 c i)
      = Finset.range (ec - c) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · simp only [Finset.mem_image, Finset.mem_Ico] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact Finset.mem_range.2 (h.scatterAt_lt hi.1 hi.2)
    · rw [Finset.card_range, Finset.card_image_of_injOn, Nat.card_Ico]
      intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      exact h.scatterAt_inj ha.1 ha.2 hb.1 hb.2 hab
  have : m ∈ (Finset.Ico c ec).image (fun i => scatterAt lab cnt bc1 c i) := by
    rw [himg]
    exact Finset.mem_range.2 hm
  simp only [Finset.mem_image, Finset.mem_Ico] at this
  obtain ⟨i, hi, hie⟩ := this
  exact ⟨i, hi.1, hi.2, hie⟩

end Offsets

/-! ### Reading off one step of `splitCell`

`splitCell` has three branches, and the proofs below all start by naming the state each one
produces.  These equations exist so that the rest of the file never has to unfold `splitCell`
again: unfolding it in place would leave the trace hash of the branch in the goal, and deciding
whether two such hashes agree is something the kernel should never be asked to do. -/

theorem part_mk (lab pos cst cen : Array Nat) (inW : Array Bool) (tr : UInt64) (bc : Array Nat) :
    (SplitState.mk lab pos cst cen inW tr bc).part
      = { lab := lab, pos := pos, cst := cst, cen := cen } := rfl

theorem part_update (st : SplitState) (inW : Array Bool) (tr : UInt64) (bc : Array Nat) :
    ({ lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen, inW, tr, bc } :
      SplitState).part = st.part := rfl

/-- A singleton cell: only the trace hash moves. -/
theorem splitCell_eq_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) :
    splitCell cnt c st = { st with tr := mixN (mixN st.tr c) cnt[st.lab[c]!]! } := by
  rw [splitCell]
  dsimp only
  exact if_pos h

/-- A cell with a single bucket: again only the trace hash moves (and the bucket counter is
put back). -/
theorem splitCell_eq_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    splitCell cnt c st = { st with tr := mixN (mixN st.tr c) ks0[0]!, bc := bc0.set! ks0[0]! 0 } := by
  rw [splitCell]
  dsimp only
  rw [if_neg h1, hb]
  dsimp only
  exact if_pos h2

/-- The general branch, with each pass of the counting sort named. -/
theorem splitCell_eq_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat}
    (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat}
    (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64}
    (hbd : boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
      (mixN st.tr c) = (cst, cen, starts, tr)) :
    splitCell cnt c st =
      { lab := lab, pos := pos, cst := cst, cen := cen,
        inW := if st.inW[c]! then markAllFrom starts starts.size 0 st.inW
          else markExceptFrom starts (maxIdxFrom sizes sizes.size 0 0) starts.size 0 st.inW,
        tr := tr, bc := clearBcFrom (sortNats ks0) (sortNats ks0).size 0 bc2 } := by
  rw [splitCell]
  dsimp only
  rw [if_neg h1, hb]
  dsimp only
  rw [if_neg h2, ho]
  dsimp only
  rw [hsc]
  dsimp only
  rw [hw]
  dsimp only
  rw [hbd]

/-- The partition after a singleton cell "splits": unchanged. -/
theorem splitCell_part_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) : (splitCell cnt c st).part = st.part := by
  rw [splitCell_eq_singleton h]
  exact part_update st st.inW _ st.bc

/-- The partition after a one-bucket cell "splits": unchanged. -/
theorem splitCell_part_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    (splitCell cnt c st).part = st.part := by
  rw [splitCell_eq_one hb h1 h2]
  exact part_update st st.inW _ _

/-- The partition after a genuine split. -/
theorem splitCell_part_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat}
    (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat}
    (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64}
    (hbd : boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
      (mixN st.tr c) = (cst, cen, starts, tr)) :
    (splitCell cnt c st).part = { lab := lab, pos := pos, cst := cst, cen := cen } := by
  rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]
  exact part_mk _ _ _ _ _ _ _

/-- An array whose entries at distinct indices differ has no duplicates. -/
theorem nodup_of_getElem!_ne {a : Array Nat}
    (h : ∀ i j, i < a.size → j < a.size → i < j → a[i]! ≠ a[j]!) : a.toList.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < a.size := by simpa using hi
  have hj' : j < a.size := by simpa using hj
  have := h i j hi' hj' hij
  rwa [getElem!_pos a i hi', getElem!_pos a j hj'] at this

/-- Every offset below the total is inside exactly one fragment. -/
theorem sizesSum_exists (sizes : Array Nat) : ∀ (K x : Nat), x < sizesSum sizes 0 K →
    ∃ j, j < K ∧ sizesSum sizes 0 j ≤ x ∧ x < sizesSum sizes 0 (j + 1)
  | 0, x, hx => by rw [sizesSum_self] at hx; omega
  | K + 1, x, hx => by
    by_cases h : x < sizesSum sizes 0 K
    · obtain ⟨j, hj, h1, h2⟩ := sizesSum_exists sizes K x h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨K, by omega, by omega, hx⟩

/-- **The general branch of `splitCell`**: the counting sort really does sort the cell into
fragments by count, and installs the fragment boundaries. -/
theorem splitOk_general {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hp : Part.WF n st.part) (hc : c < n) (hcst : st.cst[c]! = c)
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size)
    {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true) :
    SplitOk n st.part cnt c (splitCell cnt c st).part := by
  obtain ⟨lab, pos, cst, cen, inW, tr, bc⟩ := st
  dsimp only [SplitState.part] at hp hcst hbc hcb hb h1
  -- the partition data, with the projections spelled out
  have hlabn : lab.size = n := hp.labSize
  have hposn : pos.size = n := hp.posSize
  have hcstn : cst.size = n := hp.cstSize
  have hcenn : cen.size = n := hp.cenSize
  have hlabLt : ∀ i, i < n → lab[i]! < n := hp.labLt
  have hposLt : ∀ v, v < n → pos[v]! < n := hp.posLt
  have hposLab : ∀ i, i < n → pos[lab[i]!]! = i := hp.posLab
  have hlabPos : ∀ v, v < n → lab[pos[v]!]! = v := hp.labPos
  have hcstLe : ∀ i, i < n → cst[i]! ≤ i := hp.cstLe
  have hltCen : ∀ i, i < n → i < cen[i]! := hp.ltCen
  have hcenLe : ∀ i, i < n → cen[i]! ≤ n := hp.cenLe
  have hcellCst : ∀ i, i < n → ∀ j, cst[i]! ≤ j → j < cen[i]! → cst[j]! = cst[i]! := hp.cellCst
  have hcellCen : ∀ i, i < n → ∀ j, cst[i]! ≤ j → j < cen[i]! → cen[j]! = cen[i]! := hp.cellCen
  have hcE : c < cen[c]! := hltCen c hc
  have hEn : cen[c]! ≤ n := hcenLe c hc
  -- the counting pass
  have e1 : (bucketFrom lab cnt cen[c]! (cen[c]! - c) c bc #[]).1 = bc0 := by rw [hb]
  have e2 : (bucketFrom lab cnt cen[c]! (cen[c]! - c) c bc #[]).2 = ks0 := by rw [hb]
  have hbc0size : bc0.size = bc.size := by rw [← e1, bucketFrom_size]
  have hbc0 : ∀ t, t < bc.size → bc0[t]! = bucketSize lab cnt c cen[c]! t := by
    intro t ht
    rw [← e1, bucketFrom_getElem! lab cnt cen[c]! (cen[c]! - c) c bc #[] (by omega) t ht, hbc t ht]
    omega
  have hks0mem : ∀ t, t ∈ ks0 ↔ t < bc.size ∧ bucketSize lab cnt c cen[c]! t ≠ 0 := by
    intro t
    rw [← e2]
    exact bucket_mem hcb hbc t
  have hks0nd : ks0.toList.Nodup := by
    have h := bucketFrom_touched lab cnt cen[c]! (cen[c]! - c) c bc #[] hcb
      (touched_empty bc fun w hw => hbc w hw)
    rw [e2] at h
    exact h.nodup
  -- sorting the counts
  have hndks : (sortNats ks0).toList.Nodup := (sortNats_perm ks0).nodup_iff.2 hks0nd
  have hksmem : ∀ t, t ∈ sortNats ks0 ↔ t < bc.size ∧ bucketSize lab cnt c cen[c]! t ≠ 0 :=
    fun t => sortNats_mem.trans (hks0mem t)
  have hkslt : ∀ j, j < (sortNats ks0).size → (sortNats ks0)[j]! < bc.size :=
    fun j hj => ((hksmem _).1 (getElem!_mem hj)).1
  -- the remaining passes
  obtain ⟨sizes, bc1, ho⟩ : ∃ sizes bc1, offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1) := ⟨_, _, rfl⟩
  obtain ⟨block, bc2, hsc⟩ : ∃ block bc2, scatterFrom lab cnt cen[c]! (cen[c]! - c) c
      (Array.replicate (cen[c]! - c) 0) bc1 = (block, bc2) := ⟨_, _, rfl⟩
  obtain ⟨lab', pos', hw⟩ : ∃ lab' pos', writeFrom block c block.size 0 lab pos = (lab', pos') :=
    ⟨_, _, rfl⟩
  obtain ⟨cst', cen', starts, tr', hbd⟩ : ∃ cst' cen' starts tr',
      boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 cst cen #[] c (mixN tr c)
        = (cst', cen', starts, tr') := ⟨_, _, _, _, rfl⟩
  -- what the offset pass computed
  have hsizes_eq : ∀ j, j < (sortNats ks0).size →
      sizes[j]! = bucketSize lab cnt c cen[c]! (sortNats ks0)[j]! := by
    intro j hj
    have h := offsetFrom_sizes (sortNats ks0) hndks (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 (by omega) (by simp) j hj
    rw [ho] at h
    rw [h, if_neg (by omega), hbc0 _ (hkslt j hj)]
  have hbc_eq : ∀ j, j < (sortNats ks0).size → bc1[(sortNats ks0)[j]!]! = sizesSum sizes 0 j := by
    intro j hj
    have h := offsetFrom_bc (sortNats ks0) hndks (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 (by omega)
      (fun i hi => by rw [hbc0size]; exact hkslt i hi) j (by omega) hj
    rw [ho] at h
    rw [h, sizesSum, Nat.zero_add]
    exact Finset.sum_congr rfl fun i hi => by
      simp only [Finset.mem_Ico] at hi
      rw [hsizes_eq i (by omega), hbc0 _ (hkslt i (by omega))]
  have hmemj : ∀ i, c ≤ i → i < cen[c]! →
      ∃ j, j < (sortNats ks0).size ∧ (sortNats ks0)[j]! = cnt[lab[i]!]! := by
    intro i ha hb'
    have hpos0 : 0 < bucketSize lab cnt i cen[c]! cnt[lab[i]!]! := bucketSize_pos lab cnt hb' rfl
    have hmono : bucketSize lab cnt i cen[c]! cnt[lab[i]!]!
        ≤ bucketSize lab cnt c cen[c]! cnt[lab[i]!]! :=
      bucketSize_mono lab cnt (by omega) (by omega)
    exact mem_iff_getElem!.1 ((hksmem _).2 ⟨hcb _, by omega⟩)
  have hoff : Offsets lab cnt (sortNats ks0) sizes bc1 c cen[c]! :=
    ⟨hndks, hsizes_eq, hbc_eq, hmemj⟩
  have hK : sizesSum sizes 0 (sortNats ks0).size = cen[c]! - c := hoff.total
  have hbc1size : bc1.size = bc.size := by
    have h := offsetFrom_size2 (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0
    rw [ho] at h
    rw [h, hbc0size]
  have hcb1 : ∀ v : Nat, cnt[v]! < bc1.size := fun v => by rw [hbc1size]; exact hcb v
  -- what the scatter produced
  have hblocksize : block.size = cen[c]! - c := by
    have h := scatterFrom_size1 lab cnt cen[c]! (cen[c]! - c) c (Array.replicate (cen[c]! - c) 0) bc1
    rw [hsc] at h
    rw [h]; simp
  have hblockval : ∀ i, c ≤ i → i < cen[c]! → block[scatterAt lab cnt bc1 c i]! = lab[i]! := by
    intro i ha hb'
    have h := scatterFrom_block lab cnt cen[c]! (cen[c]! - c) c
      (Array.replicate (cen[c]! - c) 0) bc1 (by omega) hcb1 hoff.sep
      (fun i' h1' h2' => by simpa using hoff.scatterAt_lt h1' h2') i ha hb'
    rw [hsc] at h
    exact h
  have hblocknd : block.toList.Nodup := by
    refine nodup_of_getElem!_ne fun m m' hm hm' hmm => ?_
    rw [hblocksize] at hm hm'
    obtain ⟨i, hi1, hi2, hi3⟩ := hoff.scatterAt_surj hm
    obtain ⟨i', hi1', hi2', hi3'⟩ := hoff.scatterAt_surj hm'
    rw [← hi3, ← hi3', hblockval i hi1 hi2, hblockval i' hi1' hi2']
    intro he
    have hii : i = i' := by
      have h := congrArg (fun x => pos[x]!) he
      simp only at h
      rw [hposLab i (by omega), hposLab i' (by omega)] at h
      exact h
    rw [hii, hi3'] at hi3
    omega
  have hblocklt : ∀ m, m < block.size → block[m]! < pos.size := by
    intro m hm
    rw [hblocksize] at hm
    obtain ⟨i, hi1, hi2, hi3⟩ := hoff.scatterAt_surj hm
    rw [← hi3, hblockval i hi1 hi2, hposn]
    exact hlabLt i (by omega)
  -- what the write-back produced
  have hlab'_ne : ∀ x, (x < c ∨ cen[c]! ≤ x) → lab'[x]! = lab[x]! := by
    intro x hx
    have h := writeFrom_lab_ne block c block.size 0 lab pos x (by rw [hblocksize]; omega)
    rw [hw] at h; exact h
  have hlab'_in : ∀ m, m < cen[c]! - c → lab'[c + m]! = block[m]! := by
    intro m hm
    have h := writeFrom_lab block c block.size 0 lab pos (by omega)
      (by rw [hlabn, hblocksize]; omega) m (by omega) (by rw [hblocksize]; omega)
    rw [hw] at h; exact h
  have hnotblock : ∀ v, v < n → (pos[v]! < c ∨ cen[c]! ≤ pos[v]!) →
      ∀ m, m < block.size → block[m]! ≠ v := by
    intro v hv hvp m hm hmv
    rw [hblocksize] at hm
    obtain ⟨i, hi1, hi2, hi3⟩ := hoff.scatterAt_surj hm
    rw [← hi3, hblockval i hi1 hi2] at hmv
    have h := hposLab i (by omega)
    rw [hmv] at h
    omega
  have hpos'_ne : ∀ v, v < n → (pos[v]! < c ∨ cen[c]! ≤ pos[v]!) → pos'[v]! = pos[v]! := by
    intro v hv hvp
    have h := writeFrom_pos_ne block c block.size 0 lab pos v
      (fun m _ hm => hnotblock v hv hvp m hm)
    rw [hw] at h; exact h
  have hpos'_block : ∀ m, m < block.size → pos'[block[m]!]! = c + m := by
    intro m hm
    have h := writeFrom_pos block c hblocknd block.size 0 lab pos (by omega) hblocklt m
      (by omega) hm
    rw [hw] at h; exact h
  have hpos'_in : ∀ v, v < n → c ≤ pos[v]! → pos[v]! < cen[c]! →
      pos'[v]! = c + scatterAt lab cnt bc1 c pos[v]! := by
    intro v hv ha hb'
    have hm : scatterAt lab cnt bc1 c pos[v]! < block.size := by
      rw [hblocksize]; exact hoff.scatterAt_lt ha hb'
    have hbv : block[scatterAt lab cnt bc1 c pos[v]!]! = v := by
      rw [hblockval _ ha hb', hlabPos v hv]
    have h := hpos'_block _ hm
    rwa [hbv] at h
  have hlab'_cell : ∀ i, c ≤ i → i < cen[c]! →
      ∃ i', c ≤ i' ∧ i' < cen[c]! ∧ lab'[i]! = lab[i']! := by
    intro i ha hb'
    obtain ⟨i', hi1, hi2, hi3⟩ := hoff.scatterAt_surj (show i - c < cen[c]! - c by omega)
    refine ⟨i', hi1, hi2, ?_⟩
    have hcm : c + (i - c) = i := by omega
    rw [← hcm, hlab'_in (i - c) (by omega), ← hi3, hblockval i' hi1 hi2]
  -- what the boundary pass produced
  have hbounds_ne : ∀ x, (x < c ∨ cen[c]! ≤ x) → cst'[x]! = cst[x]! ∧ cen'[x]! = cen[x]! := by
    intro x hx
    have h := boundsFrom_ne (sortNats ks0) sizes (sortNats ks0).size 0 cst cen #[] c (mixN tr c) x
      (by rw [hK]; omega)
    rw [hbd] at h; exact h
  have hbounds : ∀ j, j < (sortNats ks0).size → ∀ x, c + sizesSum sizes 0 j ≤ x →
      x < c + sizesSum sizes 0 (j + 1) →
        cst'[x]! = c + sizesSum sizes 0 j ∧ cen'[x]! = c + sizesSum sizes 0 (j + 1) := by
    intro j hj x ha hb'
    have h := boundsFrom_getElem! (sortNats ks0) sizes (sortNats ks0).size 0 cst cen #[] c
      (mixN tr c) (by omega) (by rw [hcstn, hK]; omega) (by rw [hcenn, hK]; omega) j (by omega) hj
      x ha hb'
    rw [hbd] at h; exact h
  have hin : ∀ x, c ≤ x → x < cen[c]! → ∃ j, j < (sortNats ks0).size ∧
      c + sizesSum sizes 0 j ≤ x ∧ x < c + sizesSum sizes 0 (j + 1) := by
    intro x ha hb'
    obtain ⟨j, hj, hj1, hj2⟩ := sizesSum_exists sizes (sortNats ks0).size (x - c) (by rw [hK]; omega)
    exact ⟨j, hj, by omega, by omega⟩
  -- the fragment a cell vertex lands in
  have hfrag : ∀ i, c ≤ i → i < cen[c]! → ∃ j, j < (sortNats ks0).size ∧
      (sortNats ks0)[j]! = cnt[lab[i]!]! ∧
      c + sizesSum sizes 0 j ≤ c + scatterAt lab cnt bc1 c i ∧
      c + scatterAt lab cnt bc1 c i < c + sizesSum sizes 0 (j + 1) := by
    intro i ha hb'
    obtain ⟨j, hj, hjt⟩ := hmemj i ha hb'
    obtain ⟨u1, u2⟩ := hoff.scatterAt_mem ha hb' hj hjt
    exact ⟨j, hj, hjt, by omega, by omega⟩
  -- the fragment starts, in the invariant vocabulary
  have hcellCount : ∀ t, bucketSize lab cnt c cen[c]! t
      = cellCount n { lab := lab, pos := pos, cst := cst, cen := cen } c (fun u => cnt[u]! == t) :=
    fun t => bucketSize_cellCount hp hc hcst cnt t
  have hfragStart : ∀ j, j < (sortNats ks0).size → c + sizesSum sizes 0 j
      = fragStart n { lab := lab, pos := pos, cst := cst, cen := cen } cnt c (sortNats ks0)[j]! := by
    refine fragStart_eq hndks (sortNats_pairwise ks0) ?_ ?_
    · intro t
      rw [← hcellCount t, hksmem t]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨i, _, _, h3⟩ := exists_of_bucketSize h
      rw [← h3]
      exact hcb _
    · intro j hj
      rw [hsizes_eq j hj, hcellCount]
  -- the sizes of the new arrays
  have hlab'n : lab'.size = n := by
    have h := writeFrom_size1 block c block.size 0 lab pos
    rw [hw] at h; rw [h, hlabn]
  have hpos'n : pos'.size = n := by
    have h := writeFrom_size2 block c block.size 0 lab pos
    rw [hw] at h; rw [h, hposn]
  have hcst'n : cst'.size = n := by
    have h := boundsFrom_size1 (sortNats ks0) sizes (sortNats ks0).size 0 cst cen #[] c (mixN tr c)
    rw [hbd] at h; rw [h, hcstn]
  have hcen'n : cen'.size = n := by
    have h := boundsFrom_size2 (sortNats ks0) sizes (sortNats ks0).size 0 cst cen #[] c (mixN tr c)
    rw [hbd] at h; rw [h, hcenn]
  -- the new arrays are still a permutation
  have hlab'Lt : ∀ i, i < n → lab'[i]! < n := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · obtain ⟨i', hi1, hi2, hi3⟩ := hlab'_cell i hcell.1 hcell.2
      rw [hi3]
      exact hlabLt i' (by omega)
    · rw [hlab'_ne i (by omega)]
      exact hlabLt i hi
  have hpos'Lt : ∀ v, v < n → pos'[v]! < n := by
    intro v hv
    by_cases hcell : c ≤ pos[v]! ∧ pos[v]! < cen[c]!
    · rw [hpos'_in v hv hcell.1 hcell.2]
      have := hoff.scatterAt_lt hcell.1 hcell.2
      omega
    · rw [hpos'_ne v hv (by omega)]
      exact hposLt v hv
  have hpos'Lab : ∀ i, i < n → pos'[lab'[i]!]! = i := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · have hm : i - c < block.size := by rw [hblocksize]; omega
      have hcm : c + (i - c) = i := by omega
      have h := hpos'_block (i - c) hm
      rw [← hlab'_in (i - c) (by rw [← hblocksize]; exact hm), hcm] at h
      exact h
    · rw [hlab'_ne i (by omega)]
      have hvp : pos[lab[i]!]! < c ∨ cen[c]! ≤ pos[lab[i]!]! := by
        rw [hposLab i hi]; omega
      rw [hpos'_ne _ (hlabLt i hi) hvp, hposLab i hi]
  have hlab'Pos : ∀ v, v < n → lab'[pos'[v]!]! = v := by
    intro v hv
    by_cases hcell : c ≤ pos[v]! ∧ pos[v]! < cen[c]!
    · rw [hpos'_in v hv hcell.1 hcell.2, hlab'_in _ (hoff.scatterAt_lt hcell.1 hcell.2),
        hblockval _ hcell.1 hcell.2, hlabPos v hv]
    · rw [hpos'_ne v hv (by omega), hlab'_ne _ (by omega), hlabPos v hv]
  -- the new boundaries are still boundaries
  have hcst'Le : ∀ i, i < n → cst'[i]! ≤ i := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').1]
      omega
    · rw [(hbounds_ne i (by omega)).1]
      exact hcstLe i hi
  have hltCen' : ∀ i, i < n → i < cen'[i]! := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').2]
      omega
    · rw [(hbounds_ne i (by omega)).2]
      exact hltCen i hi
  have hcen'Le : ∀ i, i < n → cen'[i]! ≤ n := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').2]
      have hle : sizesSum sizes 0 (j + 1) ≤ sizesSum sizes 0 (sortNats ks0).size :=
        sizesSum_le sizes (by omega) (by omega)
      omega
    · rw [(hbounds_ne i (by omega)).2]
      exact hcenLe i hi
  -- an old cell that is not the split cell is untouched
  have hout : ∀ i, i < n → (i < c ∨ cen[c]! ≤ i) → ∀ y, cst[i]! ≤ y → y < cen[i]! →
      (y < c ∨ cen[c]! ≤ y) := by
    intro i hi hio y hy1 hy2
    by_contra hcon
    push_neg at hcon
    have hcy : cst[y]! = c := by
      rw [hcellCst c hc y (by omega) (by omega), hcst]
    have hcy2 : cen[y]! = cen[c]! := hcellCen c hc y (by omega) (by omega)
    have h1' : cst[y]! = cst[i]! := hcellCst i hi y hy1 hy2
    have h2' : cen[y]! = cen[i]! := hcellCen i hi y hy1 hy2
    have := hcstLe i hi
    have := hltCen i hi
    omega
  have hcellCst' : ∀ i, i < n → ∀ x, cst'[i]! ≤ x → x < cen'[i]! → cst'[x]! = cst'[i]! := by
    intro i hi x hx1 hx2
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').1] at hx1
      rw [(hbounds j hj i ha hb').2] at hx2
      rw [(hbounds j hj x hx1 hx2).1, (hbounds j hj i ha hb').1]
    · rw [(hbounds_ne i (by omega)).1] at hx1
      rw [(hbounds_ne i (by omega)).2] at hx2
      rw [(hbounds_ne x (hout i hi (by omega) x hx1 hx2)).1, (hbounds_ne i (by omega)).1]
      exact hcellCst i hi x hx1 hx2
  have hcellCen' : ∀ i, i < n → ∀ x, cst'[i]! ≤ x → x < cen'[i]! → cen'[x]! = cen'[i]! := by
    intro i hi x hx1 hx2
    by_cases hcell : c ≤ i ∧ i < cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').1] at hx1
      rw [(hbounds j hj i ha hb').2] at hx2
      rw [(hbounds j hj x hx1 hx2).2, (hbounds j hj i ha hb').2]
    · rw [(hbounds_ne i (by omega)).1] at hx1
      rw [(hbounds_ne i (by omega)).2] at hx2
      rw [(hbounds_ne x (hout i hi (by omega) x hx1 hx2)).2, (hbounds_ne i (by omega)).2]
      exact hcellCen i hi x hx1 hx2
  have hwf : Part.WF n { lab := lab', pos := pos', cst := cst', cen := cen' } :=
    ⟨hlab'n, hpos'n, hcst'n, hcen'n, hlab'Lt, hpos'Lt, hpos'Lab, hlab'Pos, hcst'Le, hltCen',
      hcen'Le, hcellCst', hcellCen'⟩
  -- the cell fields
  have hposMem : ∀ v, v < n → c ≤ pos[v]! → pos[v]! < cen[c]! →
      c ≤ pos'[v]! ∧ pos'[v]! < cen[c]! := by
    intro v hv ha hb'
    rw [hpos'_in v hv ha hb']
    have := hoff.scatterAt_lt ha hb'
    omega
  have hcellFrag : ∀ v, v < n → c ≤ pos[v]! → pos[v]! < cen[c]! →
      cst'[pos'[v]!]! = fragStart n { lab := lab, pos := pos, cst := cst, cen := cen } cnt c
        cnt[v]! := by
    intro v hv ha hb'
    obtain ⟨j, hj, hjt, hs1, hs2⟩ := hfrag pos[v]! ha hb'
    rw [hpos'_in v hv ha hb', (hbounds j hj _ hs1 hs2).1, hfragStart j hj, hjt, hlabPos v hv]
  have hcenFrag : ∀ v, v < n → c ≤ pos[v]! → pos[v]! < cen[c]! →
      cen'[pos'[v]!]! = fragStart n { lab := lab, pos := pos, cst := cst, cen := cen } cnt c
          cnt[v]!
        + cellCount n { lab := lab, pos := pos, cst := cst, cen := cen } c
          (fun u => cnt[u]! == cnt[v]!) := by
    intro v hv ha hb'
    obtain ⟨j, hj, hjt, hs1, hs2⟩ := hfrag pos[v]! ha hb'
    have hfs : c + sizesSum sizes 0 j
        = fragStart n { lab := lab, pos := pos, cst := cst, cen := cen } cnt c cnt[v]! := by
      rw [hfragStart j hj, hjt, hlabPos v hv]
    have hsz : sizes[j]! = cellCount n { lab := lab, pos := pos, cst := cst, cen := cen } c
        (fun u => cnt[u]! == cnt[v]!) := by
      rw [hsizes_eq j hj, hcellCount, hjt, hlabPos v hv]
    rw [hpos'_in v hv ha hb', (hbounds j hj _ hs1 hs2).2,
      sizesSum_split sizes (Nat.zero_le j) (Nat.le_succ j), sizesSum_one]
    omega
  rw [splitCell_part_general hb h1 h2 ho hsc hw hbd]
  exact ⟨hwf, fun i _ h => hlab'_ne i h, fun i _ h => (hbounds_ne i h).1,
    fun i _ h => (hbounds_ne i h).2, fun v hv h => hpos'_ne v hv h, hposMem, hcellFrag, hcenFrag⟩

theorem splitCell_spec {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hp : Part.WF n st.part) (hc : c < n) (hcst : st.cst[c]! = c)
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size) :
    SplitOk n st.part cnt c (splitCell cnt c st).part := by
  have hce : st.part.cen[c]! = st.cen[c]! := rfl
  have hcstp : st.part.cst[c]! = c := hcst
  obtain ⟨bc0, ks0, hb⟩ : ∃ bc0 ks0,
      bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0) := ⟨_, _, rfl⟩
  by_cases h1 : (st.cen[c]! - c == 1) = true
  · -- a singleton cell: no two vertices to compare
    rw [splitCell_part_singleton h1]
    have hsing : st.cen[c]! - c = 1 := by simpa using h1
    refine splitOk_of_uniform hp hc hcstp cnt ?_
    intro v w hv hw hvc hwc
    have h2 := (hp.cst_eq_iff hc (hp.posLt v hv)).1 (by rw [hvc, hcstp])
    have h3 := (hp.cst_eq_iff hc (hp.posLt w hw)).1 (by rw [hwc, hcstp])
    rw [hcstp] at h2 h3
    rw [← hp.labPos v hv, ← hp.labPos w hw, show st.part.pos[v]! = st.part.pos[w]! by omega]
  · by_cases h2 : (ks0.size == 1) = true
    · -- one bucket: every vertex of the cell has the same neighbour count
      rw [splitCell_part_one hb h1 h2]
      have hks1 : ks0.size = 1 := by simpa using h2
      refine splitOk_of_uniform hp hc hcstp cnt ?_
      have key : ∀ v, v < n → st.part.cst[st.part.pos[v]!]! = c → cnt[v]! = ks0[0]! := by
        intro v hv hvc
        have h3 := (hp.cst_eq_iff hc (hp.posLt v hv)).1 (by rw [hvc, hcstp])
        rw [hcstp] at h3
        have hpos : 0 < bucketSize st.lab cnt st.part.pos[v]! st.cen[c]! cnt[v]! :=
          bucketSize_pos st.lab cnt (by omega)
            (show cnt[st.part.lab[st.part.pos[v]!]!]! = cnt[v]! by rw [hp.labPos v hv])
        have hbs : bucketSize st.lab cnt st.part.pos[v]! st.cen[c]! cnt[v]!
            ≤ bucketSize st.lab cnt c st.cen[c]! cnt[v]! :=
          bucketSize_mono st.lab cnt (by omega) (by omega)
        have hmem : cnt[v]! ∈ ks0 := by
          rw [← show (bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[]).2 = ks0 by
            rw [hb]]
          exact (bucket_mem (lab := st.lab) (c := c) (ec := st.cen[c]!) hcb hbc cnt[v]!).2
            ⟨hcb v, by omega⟩
        obtain ⟨i, hi, hiv⟩ := mem_iff_getElem!.1 hmem
        rw [hks1] at hi
        rw [← hiv, show i = 0 by omega]
      intro v w hv hw hvc hwc
      rw [key v hv hvc, key w hw hwc]
    · exact splitOk_general hp hc hcst hbc hcb hb h1 h2

end Canon
end IsoGraph
