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
* the first loop of **step 1** — `cellCount_equiv`, that corresponding cells agree on every count,
  together with `countFrom_cellCount`, that `refineStep`'s counting phase computes exactly such a
  count (`countFrom_equiv` combines them), and `countFrom_mem_touched`, that the set of vertices
  the phase records is invariant too;
* **step 2** — the two readers of a partition, `shapeHash` and `targetCell`, see only cell
  boundaries, so they agree on partitions related by any renaming;
* **step 3** — individualising corresponding vertices of related partitions gives related
  partitions, at the same position (`individualize_partEquiv`), and preserves well-formedness;
* **step 4** — two runs that reach related *discrete* partitions read off the same certificate
  (`certOf_of_partEquiv`, via `certOf_relabel`), with `discrete_of_targetCell_none` supplying
  the discreteness at the leaves.

What is *not* here: the rest of `refineStep` after the counting phase — the counting sort, the
fragment boundaries and Hopcroft's worklist rule (the rest of step 1) — the correspondence of the
two search trees (step 5), and the argument that the maximum over the leaves does not depend on
the order children are enumerated in (step 6).
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
theorem getElem!_set! {a : Array Nat} {i x : Nat} (hi : i < a.size) (k : Nat) :
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
theorem getElem!_set!_ne {a : Array Nat} {i x k : Nat} (h : k ≠ i) :
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

end Canon
end IsoGraph
