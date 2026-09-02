/-!
# Canonical labelling of finite graphs (a compact "mini-nauty")

This file is deliberately *programming* Lean rather than *proving* Lean: it implements an
individualisation–refinement (IR) canonical labelling algorithm in the style of McKay's `nauty`,
with no `Prop`-level content beyond the `@[csimp]` equations that let an optimised implementation
stand in for a readable one.  Correctness proofs live elsewhere; the only thing this file promises
syntactically is termination.

## The algorithm

Fix a graph `G` on the vertex set `{0, …, n-1}`.

* An **ordered partition** of the vertices is stored `nauty`-style: an array `lab` listing the
  vertices in partition order, its inverse `pos`, and for every *position* `i` the start `cst[i]`
  and end `cen[i]` of the cell containing position `i`.  Cells are contiguous blocks of `lab`.

* **Refinement** (`refine`) computes the coarsest equitable ordered partition refining a given
  one, by the usual Hopcroft-style worklist: pop a cell `S` (the *splitter*), and split every
  other cell `C` according to `|N(v) ∩ S|`, ordering the fragments by increasing count.  This is
  1-dimensional Weisfeiler–Leman; on a random graph it already produces a discrete partition.

* A discrete ordered partition *is* a labelling, so it yields a **certificate**: the adjacency
  matrix read off in that order, stored one `Nat` bitmask per row.  Certificates are totally
  ordered lexicographically.

* When refinement does not discretise, we **individualise**: pick the first non-singleton cell
  (an isomorphism-invariant choice), split off one of its vertices, re-refine, and recurse.  This
  produces a search tree whose leaves are labellings.

* The canonical labelling is the leaf that is largest for the order
  `(invariant path, certificate)`, lexicographically.  The **invariant path** records, for each
  node on the root-to-leaf path, a hash of the *trace* of the refinement that produced it (which
  cells split, into what sizes, at which counts) together with the shape of the resulting
  partition.  Everything hashed is a function of positions and multiplicities only — never of
  vertex names — so the invariant path is an isomorphism invariant.

Two prunings make this fast:

* **Invariant pruning.**  At a node of depth `d`, compare its length-`d` invariant path with that
  of the best leaf so far.  Smaller ⇒ every leaf below is smaller ⇒ prune.  Larger ⇒ every leaf
  below beats the incumbent ⇒ discard the incumbent.

* **Automorphism pruning.**  Two leaves with equal certificates differ by an automorphism `γ`,
  which we record.  At a node with individualisation path `p`, any recorded `γ` fixing `p`
  pointwise maps the subtree below `p ++ [v]` isomorphically onto the one below `p ++ [γ v]`, so
  only one vertex per orbit needs to be explored.

Note that hash collisions can only *weaken* pruning: an invariant path is used solely as the first
component of a total order on leaves, and any isomorphism-invariant function works there.
-/

namespace IsoGraph
namespace Canon

/-! ## Graphs -/

/-- A finite graph on the vertex set `{0, …, n-1}`, stored both as a dense adjacency matrix (for
`O(1)` adjacency queries) and as neighbour lists (for the refinement inner loop).

The algorithm below never inspects `adj`/`nbr` beyond index `n`, and assumes they agree and are
symmetric; `Graph.ofOracle` builds a well-formed value. -/
structure Graph where
  /-- Number of vertices. -/
  n : Nat
  /-- `adj[v]![w]!` is `true` iff `v` and `w` are adjacent. -/
  adj : Array (Array Bool)
  /-- `nbr[v]!` lists the neighbours of `v` in increasing order. -/
  nbr : Array (Array Nat)
  deriving Inhabited

/-- Build a `Graph` from an adjacency oracle on `{0, …, n-1}`.

Written with `Array.ofFn`/`Array.filter` rather than as an imperative fill: the arrays are the
same, but every entry is then definitionally the oracle, which is what makes the lemmas in
`IsoGraph/Canon/Equivariance.lean` about this function short.  `vs` is shared across the rows so the
`nbr` pass allocates only the neighbour lists themselves, and the rows are read off `adj` rather
than off the oracle a second time: `f` is typically a `Decidable` instance behind a `FinEnum`
transport, and asking it `n²` times instead of `2n²` is a third of what building a graph costs. -/
def Graph.ofOracle (n : Nat) (f : Nat → Nat → Bool) : Graph :=
  let vs := Array.range n
  let adj := Array.ofFn (n := n) fun v => Array.ofFn (n := n) fun w => f v.1 w.1
  { n := n
    adj := adj
    nbr := adj.map fun r => vs.filter fun w => r[w]! }

/-- One row of `Graph.ofOracleFast`: ask `f v w` for `w`, `w + 1`, … and push each answer onto the
dense row, and `w` itself onto the neighbour list when the answer is `true`.  `fuel` is the number
of columns left, and is only ever `n`. -/
def buildRow (f : Nat → Nat → Bool) (v : Nat) :
    Nat → Nat → Array Bool → Array Nat → Array Bool × Array Nat
  | 0, _, row, nb => (row, nb)
  | fuel + 1, w, row, nb =>
    let b := f v w
    buildRow f v fuel (w + 1) (row.push b) (if b then nb.push w else nb)

/-- The rows of `Graph.ofOracleFast` from `v` on, each of them built by `buildRow`.  `fuel` is the
number of rows left, and is only ever `n`. -/
def buildRows (n : Nat) (f : Nat → Nat → Bool) :
    Nat → Nat → Array (Array Bool) → Array (Array Nat) → Array (Array Bool) × Array (Array Nat)
  | 0, _, adj, nbr => (adj, nbr)
  | fuel + 1, v, adj, nbr =>
    match buildRow f v n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n) with
    | (row, nb) => buildRows n f fuel (v + 1) (adj.push row) (nbr.push nb)

/-- What `Graph.ofOracle` actually runs: the same two arrays, filled by one pass over the `n²`
oracle calls rather than by an `Array.ofFn` nest and then an `Array.filter` per row.  A row's
neighbour list is known while the row is being built, so the second traversal — and with it a
bounds-checked `r[w]!` per entry, and the `Fin` that `Array.ofFn` hands its argument — buys
nothing.  It is about a quarter off building a graph (17 µs against 22 µs at `n = 20`), which the
enumerator pays once per candidate and every canonicalisation in the library pays once. -/
def Graph.ofOracleFast (n : Nat) (f : Nat → Nat → Bool) : Graph :=
  match buildRows n f n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n) with
  | (adj, nbr) => { n := n, adj := adj, nbr := nbr }

/-- `Array.toList_ofFn` for a function that only sees the index, in the form the proofs below
want.  This file cannot use `List.ofFn`: it imports nothing. -/
private theorem toList_ofFn_range {α : Type} (n : Nat) (g : Nat → α) :
    (Array.ofFn (n := n) fun w : Fin n => g w.1).toList = (List.range n).map g := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp

/-- Both halves of one row: the dense part is the oracle's answers on `[w, w + fuel)`, the sparse
part is the sublist of those that were `true`. -/
theorem toList_buildRow (f : Nat → Nat → Bool) (v : Nat) :
    ∀ (fuel w : Nat) (row : Array Bool) (nb : Array Nat),
      (buildRow f v fuel w row nb).1.toList = row.toList ++ (List.range' w fuel).map (f v) ∧
        (buildRow f v fuel w row nb).2.toList = nb.toList ++ (List.range' w fuel).filter (f v) := by
  intro fuel
  induction fuel with
  | zero => intro w row nb; simp [buildRow]
  | succ k ih =>
    intro w row nb
    obtain ⟨h1, h2⟩ := ih (w + 1) (row.push (f v w)) (if f v w then nb.push w else nb)
    refine ⟨?_, ?_⟩
    · rw [buildRow, h1]
      simp [List.range'_succ]
    · rw [buildRow, h2]
      cases hb : f v w <;> simp [List.range'_succ, hb]

theorem buildRow_fst_eq (f : Nat → Nat → Bool) (n v : Nat) :
    (buildRow f v n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).1
      = Array.ofFn (n := n) fun w : Fin n => f v w.1 := by
  refine Array.ext' ?_
  rw [(toList_buildRow f v n 0 _ _).1, toList_ofFn_range]
  simp [List.range_eq_range']

theorem buildRow_snd_eq (f : Nat → Nat → Bool) (n v : Nat) :
    (buildRow f v n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).2
      = (Array.range n).filter fun w ↦
          (Array.ofFn (n := n) fun w : Fin n => f v w.1)[w]! := by
  refine Array.ext' ?_
  rw [(toList_buildRow f v n 0 _ _).2, Array.toList_filter, Array.toList_range]
  simp only [← List.range_eq_range']
  refine (List.filter_congr fun w hw ↦ ?_).symm
  have hw : w < n := List.mem_range.1 hw
  rw [getElem!_pos _ _ (by simpa using hw)]
  simp

/-- The fill visits the rows in order, so both accumulators end up holding what `buildRow` returns
for each `v` in `[v, v + fuel)`. -/
theorem toList_buildRows (n : Nat) (f : Nat → Nat → Bool) :
    ∀ (fuel v : Nat) (adj : Array (Array Bool)) (nbr : Array (Array Nat)),
      (buildRows n f fuel v adj nbr).1.toList = adj.toList ++ (List.range' v fuel).map
          (fun v ↦ (buildRow f v n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).1) ∧
        (buildRows n f fuel v adj nbr).2.toList = nbr.toList ++ (List.range' v fuel).map
          (fun v ↦ (buildRow f v n 0 (Array.emptyWithCapacity n)
            (Array.emptyWithCapacity n)).2) := by
  intro fuel
  induction fuel with
  | zero => intro v adj nbr; simp [buildRows]
  | succ k ih =>
    intro v adj nbr
    obtain ⟨h1, h2⟩ := ih (v + 1)
      (adj.push (buildRow f v n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).1)
      (nbr.push (buildRow f v n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).2)
    refine ⟨?_, ?_⟩
    · rw [buildRows, h1]
      simp [List.range'_succ]
    · rw [buildRows, h2]
      simp [List.range'_succ]

@[csimp] theorem ofOracle_eq_ofOracleFast : @Graph.ofOracle = @Graph.ofOracleFast := by
  funext n f
  have h1 := (toList_buildRows n f n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).1
  have h2 := (toList_buildRows n f n 0 (Array.emptyWithCapacity n) (Array.emptyWithCapacity n)).2
  -- `Graph.ext` needs the `ext` machinery, which this file has no import for.
  have hmk : ∀ (A A' : Array (Array Bool)) (N N' : Array (Array Nat)), A = A' → N = N' →
      (⟨n, A, N⟩ : Graph) = ⟨n, A', N'⟩ := by rintro A A' N N' rfl rfl; rfl
  have hof := toList_ofFn_range n fun v ↦ Array.ofFn (n := n) fun w : Fin n => f v w.1
  refine hmk _ _ _ _ (Array.ext' ?_) (Array.ext' ?_)
  · rw [h1, hof]
    simp only [List.range_eq_range']
    exact List.map_congr_left fun v _ ↦ (buildRow_fst_eq f n v).symm
  · rw [h2, Array.toList_map, hof]
    simp only [List.range_eq_range', List.map_map, Function.comp_def]
    exact List.map_congr_left fun v _ ↦ (buildRow_snd_eq f n v).symm

/-- **Only the oracle's values below `n` matter.**  Everything the algorithm ever sees is read off
the two arrays, and those are filled from `f v w` for `v, w < n` alone, so a caller is free to
replace its oracle by any cheaper function agreeing with it there. -/
theorem Graph.ofOracle_congr {n : Nat} {f g : Nat → Nat → Bool}
    (h : ∀ v w, v < n → w < n → f v w = g v w) : Graph.ofOracle n f = Graph.ofOracle n g := by
  have hadj : (Array.ofFn (n := n) fun v : Fin n => Array.ofFn (n := n) fun w : Fin n => f v.1 w.1)
      = Array.ofFn (n := n) fun v : Fin n => Array.ofFn (n := n) fun w : Fin n => g v.1 w.1 :=
    congrArg _ (funext fun v ↦ congrArg _ (funext fun w ↦ h v.1 w.1 v.2 w.2))
  simp only [Graph.ofOracle, hadj]

/-- Number of edges (counting each unordered pair once); handy for sanity checks. -/
def Graph.edgeCount (G : Graph) : Nat := Id.run do
  let mut m := 0
  for v in [0:G.n] do
    m := m + G.nbr[v]!.size
  return m / 2

/-! ## Hashing

A 64-bit FNV-style mixer.  Only used to compress isomorphism-invariant integer sequences into a
comparable summary; collisions cost pruning power, never correctness. -/

/-- The FNV-1a offset basis, used as the seed of every invariant hash. -/
def hashSeed : UInt64 := 1469598103934665603

/-- Fold one number into a running hash. -/
@[inline] def mix (h : UInt64) (x : UInt64) : UInt64 :=
  (h ^^^ x) * 1099511628211

/-- Fold one `Nat` into a running hash. -/
@[inline] def mixN (h : UInt64) (x : Nat) : UInt64 :=
  mix h (UInt64.ofNat x)

/-! ## Ordered partitions -/

/-- An ordered partition of `{0, …, n-1}` into contiguous cells of `lab`.

* `lab[i]!` — the vertex at position `i`;
* `pos[v]!` — the position of vertex `v` (inverse of `lab`);
* `cst[i]!` — first position of the cell containing position `i`;
* `cen[i]!` — one past the last position of that cell.

A cell is therefore identified by its start position, and cell starts are exactly the `i` with
`cst[i]! = i`. -/
structure Part where
  /-- Position `↦` vertex. -/
  lab : Array Nat
  /-- Vertex `↦` position. -/
  pos : Array Nat
  /-- Position `↦` start of its cell. -/
  cst : Array Nat
  /-- Position `↦` end (exclusive) of its cell. -/
  cen : Array Nat
  deriving Inhabited

/-- The one-cell (unit) partition of `{0, …, n-1}`. -/
def Part.unit (n : Nat) : Part :=
  { lab := Array.range n
    pos := Array.range n
    cst := Array.replicate n 0
    cen := Array.replicate n n }

/-! Both readers of a partition below walk it cell by cell: from a cell start `i`, `cen[i]!` is
the start of the next cell, so the walk `i ↦ cen[i]!` visits every cell once and reaches `n`.
They are written as structural recursions on an explicit fuel rather than as `for` loops with a
`break`, because that is the form induction works on — see `IsoGraph/Canon/Equivariance.lean`, where
everything about them is proved.  `n` is always enough fuel: there are at most `n` cells. -/

/-- Fold the cell sizes from cell start `i` into the hash `h`. -/
def cenHashFrom (cen : Array Nat) (n : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | fuel + 1, i, h =>
    if i ≥ n then h else cenHashFrom cen n fuel cen[i]! (mixN h (cen[i]! - i))

/-- Start of the first non-singleton cell at or after cell start `i`, if any. -/
def cenTargetFrom (cen : Array Nat) (n : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    if i ≥ n then none
    else if cen[i]! - i > 1 then some i
    else cenTargetFrom cen n fuel cen[i]!

/-- Hash of the sequence of cell sizes.  Isomorphism-invariant. -/
def Part.shapeHash (p : Part) (n : Nat) : UInt64 := cenHashFrom p.cen n n 0 hashSeed

/-- Start position of the first non-singleton cell, if any.  This is the target cell for
individualisation; picking the *first* one is an isomorphism-invariant rule. -/
def Part.targetCell (p : Part) (n : Nat) : Option Nat := cenTargetFrom p.cen n n 0

/-! ## Refinement -/

/-- Scratch space reused across refinement steps.

Allocating these three arrays afresh in every step would make a step cost `Ω(n)` even when the
splitter is tiny, which on sparse graphs dominates everything else.  Instead they are threaded
through the worklist loop and each step *restores* them, so the invariant

* `cnt` is all `0`,
* `hit` is all `false`,
* `bc` is all `0`

holds on entry to and on exit from every step, and clearing costs only what was dirtied. -/
structure Scratch where
  /-- Vertex `↦` number of neighbours in the current splitter cell. -/
  cnt : Array Nat
  /-- Cell start `↦` has this cell already been collected? -/
  hit : Array Bool
  /-- Neighbour count `↦` bucket size, then bucket offset, during the counting sort. -/
  bc : Array Nat
  deriving Inhabited

/-- Cleared scratch space for a graph on `n` vertices.  Counts never exceed `n`, so `bc` needs
`n + 1` entries. -/
def Scratch.empty (n : Nat) : Scratch :=
  { cnt := Array.replicate n 0, hit := Array.replicate n false, bc := Array.replicate (n + 1) 0 }

/-- Bump `cnt[v]` for every `v` in `nbrs[j:]`, pushing each newly-touched vertex onto `touched`.

Like `cenHashFrom` above this is a structural recursion on an explicit fuel (only ever
`nbrs.size - j`) rather than a `for` loop, so that the equivariance proof can read off the
resulting count at each index; the `j < nbrs.size` that a `for` loop hides is exactly what the
proof needs. -/
def bumpFrom (nbrs : Array Nat) : Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, cnt, touched => (cnt, touched)
  | fuel + 1, j, cnt, touched =>
    if j ≥ nbrs.size then (cnt, touched)
    else
      let v := nbrs[j]!
      let c := cnt[v]!
      bumpFrom nbrs fuel (j + 1) (cnt.set! v (c + 1)) (if c == 0 then touched.push v else touched)

/-- Accumulate into `cnt` the number of neighbours each vertex has among `lab[k:e]`, recording in
`touched` the vertices whose count became nonzero.  This is phase (1) of `refineStep`, and is the
hot loop of the whole algorithm: it costs the splitter cell's degree sum. -/
def countFrom (G : Graph) (lab : Array Nat) (e : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, cnt, touched => (cnt, touched)
  | fuel + 1, k, cnt, touched =>
    if k ≥ e then (cnt, touched)
    else
      let nbrs := G.nbr[lab[k]!]!
      match bumpFrom nbrs nbrs.size 0 cnt touched with
      | (cnt, touched) => countFrom G lab e fuel (k + 1) cnt touched

/-- `countFrom` and `bumpFrom` fused into a single loop: `kf` counts the vertices of the splitter
cell still to visit and `nbrs[j:]` the neighbours of the current one, so that walking off the end
of one neighbour list runs straight on into the next vertex.

This is the same work in the same order — what it saves is the pair of arrays that the inner loop
returns to the outer one, allocated once per vertex of the splitter cell rather than once per
step, in the hottest loop of the algorithm.  Termination is lexicographic: a bump shortens the
neighbour list, a step to the next vertex lowers `kf`. -/
def countAllFrom (G : Graph) (lab : Array Nat) (e kf k : Nat) (nbrs : Array Nat) (j : Nat)
    (cnt touched : Array Nat) : Array Nat × Array Nat :=
  if hj : j < nbrs.size then
    let v := nbrs[j]!
    let c := cnt[v]!
    countAllFrom G lab e kf k nbrs (j + 1) (cnt.set! v (c + 1))
      (if c == 0 then touched.push v else touched)
  else
    match kf with
    | 0 => (cnt, touched)
    | kf + 1 =>
      if k ≥ e then (cnt, touched)
      else countAllFrom G lab e kf (k + 1) G.nbr[lab[k]!]! 0 cnt touched
termination_by (kf, nbrs.size - j)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

@[inherit_doc countAllFrom]
def countFromFast (G : Graph) (lab : Array Nat) (e : Nat) (fuel k : Nat)
    (cnt touched : Array Nat) : Array Nat × Array Nat :=
  countAllFrom G lab e fuel k #[] 0 cnt touched

/-- Out of fuel at a vertex boundary. -/
theorem countAllFrom_done (G : Graph) (lab : Array Nat) (e k : Nat) (nbrs : Array Nat) (j : Nat)
    (cnt touched : Array Nat) (h : ¬ j < nbrs.size) :
    countAllFrom G lab e 0 k nbrs j cnt touched = (cnt, touched) := by
  rw [countAllFrom.eq_def G lab e 0 k nbrs j cnt touched, dite_eq_right h]

/-- At a vertex boundary the loop moves on to `lab[k]`. -/
theorem countAllFrom_next (G : Graph) (lab : Array Nat) (e kf k : Nat) (nbrs : Array Nat) (j : Nat)
    (cnt touched : Array Nat) (h : ¬ j < nbrs.size) :
    countAllFrom G lab e (kf + 1) k nbrs j cnt touched =
      if k ≥ e then (cnt, touched)
      else countAllFrom G lab e kf (k + 1) G.nbr[lab[k]!]! 0 cnt touched := by
  rw [countAllFrom.eq_def G lab e (kf + 1) k nbrs j cnt touched, dite_eq_right h]

/-- Nor does anything else at a vertex boundary: the scan position is dead there. -/
theorem countAllFrom_boundary (G : Graph) (lab : Array Nat) (e kf k : Nat) (nbrs nbrs' : Array Nat)
    (j j' : Nat) (cnt touched : Array Nat) (h : ¬ j < nbrs.size) (h' : ¬ j' < nbrs'.size) :
    countAllFrom G lab e kf k nbrs j cnt touched
      = countAllFrom G lab e kf k nbrs' j' cnt touched := by
  rw [countAllFrom.eq_def G lab e kf k nbrs j cnt touched,
    countAllFrom.eq_def G lab e kf k nbrs' j' cnt touched, dite_eq_right h, dite_eq_right h']

/-- The inner scan runs to the end of `nbrs` and lands on the boundary, having done exactly what
`bumpFrom` does. -/
theorem countAllFrom_bump (G : Graph) (lab : Array Nat) (e kf k : Nat) (nbrs : Array Nat) :
    ∀ (fuel j : Nat) (cnt touched : Array Nat), j + fuel = nbrs.size →
      countAllFrom G lab e kf k nbrs j cnt touched
        = match bumpFrom nbrs fuel j cnt touched with
          | (cnt, touched) => countAllFrom G lab e kf k nbrs nbrs.size cnt touched := by
  intro fuel
  induction fuel with
  | zero =>
    intro j cnt touched hj
    simp only [bumpFrom]
    rw [show j = nbrs.size by omega]
  | succ f ih =>
    intro j cnt touched hj
    have hlt : j < nbrs.size := by omega
    rw [countAllFrom.eq_def G lab e kf k nbrs j cnt touched, dite_eq_left hlt, bumpFrom,
      ite_eq_right (by omega)]
    exact ih (j + 1) _ _ (by omega)

@[csimp] theorem countFrom_eq_countFromFast : @countFrom = @countFromFast := by
  funext G lab e fuel k cnt touched
  induction fuel generalizing k cnt touched with
  | zero => rw [countFrom, countFromFast, countAllFrom_done _ _ _ _ _ _ _ _ (by simp)]
  | succ f ih =>
    rw [countFromFast, countAllFrom_next _ _ _ _ _ _ _ _ _ (by simp)]
    simp only [countFrom]
    by_cases hk : k ≥ e
    · rw [ite_eq_left hk, ite_eq_left hk]
    · rw [ite_eq_right hk, ite_eq_right hk,
        countAllFrom_bump G lab e f (k + 1) _ G.nbr[lab[k]!]!.size 0 cnt touched (by omega)]
      cases bumpFrom G.nbr[lab[k]!]! G.nbr[lab[k]!]!.size 0 cnt touched with
      | mk c t =>
        show countFrom G lab e f (k + 1) c t
          = countAllFrom G lab e f (k + 1) G.nbr[lab[k]!]! G.nbr[lab[k]!]!.size c t
        rw [countAllFrom_boundary G lab e f (k + 1) _ #[] _ 0 c t (by omega) (by simp)]
        exact ih (k + 1) c t

/-- Insert `x` into a list already sorted increasingly. -/
def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

/-- Insertion sort. -/
def sortNatList : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNatList xs)

/-- Sort an array of naturals increasingly.

`Array.qsort` would do the same job, but it has no verified specification in this toolchain, and
the sorted order of the cells and of the counts *is* part of what makes the trace canonical.  So
this goes through a list sort, which does — `sortNats_toList` in
`IsoGraph/Canon/Equivariance.lean` identifies it with `List.mergeSort`.

Which sort, though, depends on how many there are to sort.  Both call sites sort the cells that
one splitter meets, and on a sparse graph that is one or two of them, where the merge's splitting
is pure overhead — a tenth of `canonical` on the order-six benchmark once went on sorting
three-element arrays.  On a dense graph a splitter meets a constant fraction of the cells, and
there insertion sort *is* the algorithm's cost: at `n = 1000` the quadratic term buried in this
one line was five sixths of the whole canonicalisation.  So: insertion sort up to eight entries,
`List.mergeSort` above. -/
def sortNats (a : Array Nat) : Array Nat :=
  if a.size ≤ 8 then (sortNatList a.toList).toArray
  else (a.toList.mergeSort fun x y ↦ x ≤ y).toArray

/-- Insertion sort of three naturals, as a comparison tree. -/
theorem sortNatList_three (x y z : Nat) :
    sortNatList [x, y, z] =
      (if x ≤ y then (if y ≤ z then [x, y, z] else if x ≤ z then [x, z, y] else [z, x, y])
        else (if x ≤ z then [y, x, z] else if y ≤ z then [y, z, x] else [z, y, x])) := by
  by_cases h1 : x ≤ y <;> by_cases h2 : y ≤ z <;> by_cases h3 : x ≤ z <;>
    simp only [sortNatList, insertNat, h1, h2, h3, ite_true, ite_false] <;>
    first | rfl | (exfalso; omega)

/-! Above eight entries the sort is a comparison sort no longer by necessity but by habit: what
both call sites sort are *keys bounded by the number of vertices* — cell starts at one of them,
neighbour counts at the other — and a long array of such keys is dense in its own range.  Counting
sort is then linear, and the rest of this section is its correctness proof, which is what buys the
right to run it in place of the merge.  The pay-off is large because sorting is where a dense
refinement spends its time: at `n = 128` the array of cell starts takes 24 µs to merge and 4 µs to
count, and initial refinement of a random graph speeds up by 1.8× at `n = 64`, rising to 2.7× at
`n = 512`. -/

/-- Push `k` copies of `v` onto `out`. -/
def pushCopies (v : Nat) : Nat → Array Nat → Array Nat
  | 0, out => out
  | k + 1, out => pushCopies v k (out.push v)

/-- Emit `cnt[i]` copies of `i` for every `i` in `[j, cnt.size)`, in increasing order: the reading
phase of the counting sort, as a structural recursion on fuel.  `fuel` is only ever `cnt.size`. -/
def emitFrom (cnt : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, out => out
  | fuel + 1, i, out =>
    if cnt.size ≤ i then out else emitFrom cnt fuel (i + 1) (pushCopies i cnt[i]! out)

/-- Count how often each key occurs in `a`, whose entries must all be at most `m`. -/
def tally (m : Nat) (a : Array Nat) : Array Nat :=
  a.foldl (fun c x ↦ c.set! x (c[x]! + 1)) (Array.replicate (m + 1) 0)

/-- Counting sort of `a`, whose entries must all be at most `m`.  Linear in `m + a.size`. -/
def countSort (m : Nat) (a : Array Nat) : Array Nat :=
  emitFrom (tally m a) (m + 1) 0 #[]

/-- The largest entry of `a`, or `0` if it is empty. -/
def maxOf (a : Array Nat) : Nat := a.foldl (fun x y ↦ max x y) 0

/-- Reading one entry of `Array.set!`.  This duplicates `getElem!_set!` in
`IsoGraph/ForMathlib/Array.lean`, which this file cannot use: it imports nothing. -/
private theorem getElem!_set!_nat {a : Array Nat} {i x : Nat} (hi : i < a.size) (k : Nat) :
    (a.set! i x)[k]! = if k = i then x else a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk, eq_comm (a := i)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk,
      ite_eq_right (by omega)]

theorem toList_pushCopies (v k : Nat) (out : Array Nat) :
    (pushCopies v k out).toList = out.toList ++ List.replicate k v := by
  induction k generalizing out with
  | zero => simp [pushCopies]
  | succ k ih => simp [pushCopies, ih, List.replicate_succ]

theorem count_pushCopies (v k w : Nat) (out : Array Nat) :
    (pushCopies v k out).toList.count w = out.toList.count w + (if v = w then k else 0) := by
  rw [toList_pushCopies, List.count_append, List.count_replicate]
  simp

/-- What is emitted is sorted: each round appends a block of `i`s to something all of whose
entries are at most `i`. -/
theorem pairwise_emitFrom (cnt : Array Nat) (fuel : Nat) :
    ∀ (i : Nat) (out : Array Nat), out.toList.Pairwise (· ≤ ·) →
      (∀ x ∈ out.toList, x ≤ i) → (emitFrom cnt fuel i out).toList.Pairwise (· ≤ ·) := by
  induction fuel with
  | zero => intro i out hp _; exact hp
  | succ fuel ih =>
    intro i out hp hle
    rw [emitFrom]
    split
    · exact hp
    · refine ih (i + 1) _ ?_ ?_
      · rw [toList_pushCopies, List.pairwise_append]
        refine ⟨hp, List.pairwise_replicate.2 (Or.inr (Nat.le_refl i)), ?_⟩
        intro x hx y hy
        obtain ⟨-, rfl⟩ := List.mem_replicate.1 hy
        exact hle x hx
      · intro x hx
        rw [toList_pushCopies, List.mem_append] at hx
        rcases hx with h | h
        · exact Nat.le_succ_of_le (hle x h)
        · obtain ⟨-, rfl⟩ := List.mem_replicate.1 h; omega

/-- Every key in range is emitted as often as `cnt` says. -/
theorem count_emitFrom (cnt : Array Nat) (fuel : Nat) :
    ∀ (i : Nat), cnt.size ≤ i + fuel → ∀ (out : Array Nat) (w : Nat),
      (emitFrom cnt fuel i out).toList.count w
        = out.toList.count w + (if i ≤ w ∧ w < cnt.size then cnt[w]! else 0) := by
  induction fuel with
  | zero =>
    intro i hi out w
    rw [emitFrom, ite_eq_right (by omega)]
    omega
  | succ fuel ih =>
    intro i hi out w
    rw [emitFrom]
    split
    · rename_i h
      rw [ite_eq_right (by omega)]
      omega
    · rename_i h
      rw [ih (i + 1) (by omega), count_pushCopies]
      by_cases hiw : i = w
      · subst hiw
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left ⟨Nat.le_refl i, by omega⟩]
        omega
      · rw [ite_eq_right hiw]
        by_cases hlt : i ≤ w ∧ w < cnt.size
        · rw [ite_eq_left hlt, ite_eq_left ⟨by omega, hlt.2⟩]
          omega
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

theorem size_tally (m : Nat) (a : Array Nat) : (tally m a).size = m + 1 := by
  have h : ∀ (l : List Nat) (c : Array Nat),
      (l.foldl (fun (c : Array Nat) (x : Nat) ↦ c.set! x (c[x]! + 1)) c).size = c.size := by
    intro l
    induction l with
    | nil => intro c; rfl
    | cons x xs ih => intro c; rw [List.foldl_cons, ih, Array.size_set!]
  rw [tally, ← Array.foldl_toList, h]
  simp

theorem getElem!_tally (m : Nat) (a : Array Nat) (hm : ∀ x ∈ a.toList, x ≤ m) (w : Nat)
    (hw : w ≤ m) : (tally m a)[w]! = a.toList.count w := by
  have key : ∀ (l : List Nat), (∀ x ∈ l, x ≤ m) → ∀ (c : Array Nat), c.size = m + 1 →
      (l.foldl (fun (c : Array Nat) (x : Nat) ↦ c.set! x (c[x]! + 1)) c)[w]!
        = c[w]! + l.count w := by
    intro l
    induction l with
    | nil => intro _ c _; simp
    | cons x xs ih =>
      intro hx c hc
      rw [List.foldl_cons,
        ih (fun y hy ↦ hx y (List.mem_cons_of_mem x hy)) _ (by rw [Array.size_set!, hc]),
        getElem!_set!_nat (by rw [hc]; exact Nat.lt_succ_of_le (hx x List.mem_cons_self)),
        List.count_cons]
      by_cases hxw : x = w
      · subst hxw
        rw [ite_eq_left rfl, ite_eq_left (by simp)]
        omega
      · rw [ite_eq_right (fun h ↦ hxw h.symm), ite_eq_right (by simpa using hxw)]
        omega
  rw [tally, ← Array.foldl_toList, key a.toList hm _ (by simp),
    getElem!_pos _ _ (by simp; omega)]
  simp

theorem count_countSort (m : Nat) (a : Array Nat) (hm : ∀ x ∈ a.toList, x ≤ m) (w : Nat) :
    (countSort m a).toList.count w = a.toList.count w := by
  rw [countSort, count_emitFrom _ _ 0 (by rw [size_tally]; omega)]
  simp only [List.count_nil, Nat.zero_add, Nat.zero_le, true_and, size_tally]
  by_cases hw : w < m + 1
  · rw [ite_eq_left hw, getElem!_tally m a hm w (by omega)]
  · rw [ite_eq_right hw, List.count_eq_zero.2 (fun h ↦ absurd (hm w h) (by omega))]

theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat), acc ≤ l.foldl (fun x y ↦ max x y) acc
  | [], acc => Nat.le_refl acc
  | x :: xs, acc => Nat.le_trans (Nat.le_max_left acc x) (le_foldl_max xs (max acc x))

theorem le_maxOf (a : Array Nat) : ∀ x ∈ a.toList, x ≤ maxOf a := by
  have key : ∀ (l : List Nat) (acc x : Nat), x ∈ l → x ≤ l.foldl (fun x y ↦ max x y) acc := by
    intro l
    induction l with
    | nil => intro _ _ h; exact absurd h (by simp)
    | cons y ys ih =>
      intro acc x h
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right acc x) (le_foldl_max ys (max acc x))
      · exact ih (max acc y) x h
  intro x hx
  rw [maxOf, ← Array.foldl_toList]
  exact key a.toList 0 x hx

/-- The counting sort agrees with the merge, which is what lets `sortNatsFast` run it. -/
theorem countSort_eq_mergeSort (m : Nat) (a : Array Nat) (hm : ∀ x ∈ a.toList, x ≤ m) :
    countSort m a = (a.toList.mergeSort fun x y ↦ x ≤ y).toArray := by
  refine Array.ext' ?_
  rw [List.toList_toArray]
  refine List.Perm.eq_of_pairwise (le := fun x y ↦ x ≤ y) (fun x y _ _ h1 h2 ↦ by omega) ?_ ?_ ?_
  · exact pairwise_emitFrom _ _ 0 #[] (by simp) (by simp)
  · exact (List.pairwise_mergeSort (fun x y z ↦ by simp; omega) (fun x y ↦ by simp; omega)
      a.toList).imp (by simp)
  · exact (List.perm_iff_count.2 (count_countSort m a hm)).trans
      (List.mergeSort_perm a.toList _).symm

/-- The `sortNats` path for arrays too long for insertion sort: counting sort when the keys are
dense enough in their range to pay for the tally array, merge sort otherwise.  Sixteen keys' worth
of empty buckets per key is well inside the point where counting wins; the test only exists
because nothing about the *type* `Array Nat` says the keys are small, and one wild entry would
otherwise allocate an array the size of it. -/
def sortNatsLarge (a : Array Nat) : Array Nat :=
  let m := maxOf a
  if m ≤ 16 * a.size then countSort m a
  else (a.toList.mergeSort fun x y ↦ x ≤ y).toArray

theorem sortNatsLarge_eq (a : Array Nat) :
    sortNatsLarge a = (a.toList.mergeSort fun x y ↦ x ≤ y).toArray := by
  show (if maxOf a ≤ 16 * a.size then countSort (maxOf a) a
      else (a.toList.mergeSort fun x y ↦ x ≤ y).toArray) = _
  split
  · exact countSort_eq_mergeSort _ a (le_maxOf a)
  · rfl

/-! Below eight entries insertion sort is the right algorithm, but `sortNatList` is the wrong way to
run it: every insertion rebuilds the spine of the list it inserts into, so sorting eight keys
allocates thirty-six cons cells and then an array to hold the answer.  The same comparisons in the
same order, performed on an array that nothing else holds a reference to, allocate one array.  What
follows is that version and its agreement with `sortNatList`; it is worth about 5% of an initial
refinement of a sparse graph. -/

/-- Insert `x` into the sorted prefix `a[0:j]` of an array whose slot `j` is free, sliding the
entries greater than `x` up one place.  `fuel` is only ever `j + 1`. -/
def bubbleDown (x : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, a => a
  | fuel + 1, j, a =>
    if j = 0 then a.set! 0 x
    else if a[j-1]! < x then a.set! j x
    else bubbleDown x fuel (j - 1) (a.set! j a[j-1]!)

/-- Insert `x` into the sorted array `out`, before anything equal to it. -/
def insertArr (x : Nat) (out : Array Nat) : Array Nat :=
  bubbleDown x (out.size + 1) out.size (out.push x)

/-- Insert `a[i-1]`, `a[i-2]`, …, `a[0]` into `out`, in that order — the order in which
`sortNatList` inserts them.  `fuel` is only ever `i`. -/
def insSortFrom (a : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, out => out
  | fuel + 1, i, out =>
    if i = 0 then out else insSortFrom a fuel (i - 1) (insertArr a[i-1]! out)

/-- Insertion sort of an array, done in the array. -/
def insSortArr (a : Array Nat) : Array Nat :=
  insSortFrom a a.size a.size (Array.emptyWithCapacity a.size)

private theorem or_lcomm {a b c : Prop} : (a ∨ b ∨ c) ↔ (b ∨ a ∨ c) :=
  ⟨fun h ↦ h.elim (fun ha ↦ Or.inr (Or.inl ha))
      (fun h ↦ h.elim Or.inl fun hc ↦ Or.inr (Or.inr hc)),
   fun h ↦ h.elim (fun hb ↦ Or.inr (Or.inl hb))
      (fun h ↦ h.elim Or.inl fun hc ↦ Or.inr (Or.inr hc))⟩

theorem mem_insertNat {x z : Nat} : ∀ {l : List Nat}, z ∈ insertNat x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insertNat]
  | y :: ys => by
    by_cases h : x ≤ y
    · simp [insertNat, h]
    · simp only [insertNat, h, ite_false, List.mem_cons, mem_insertNat (l := ys)]
      exact or_lcomm

theorem pairwise_insertNat (x : Nat) : ∀ {l : List Nat}, l.Pairwise (· ≤ ·) →
    (insertNat x l).Pairwise (· ≤ ·)
  | [], _ => by simp [insertNat]
  | y :: ys, h => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.1 h
    by_cases hxy : x ≤ y
    · rw [insertNat, ite_eq_left hxy]
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy (hy z hz)
    · rw [insertNat, ite_eq_right hxy]
      refine List.pairwise_cons.2 ⟨?_, pairwise_insertNat x hys⟩
      intro z hz
      rcases mem_insertNat.1 hz with rfl | hz
      · omega
      · exact hy z hz

theorem pairwise_sortNatList : ∀ l : List Nat, (sortNatList l).Pairwise (· ≤ ·)
  | [] => by simp [sortNatList]
  | x :: xs => pairwise_insertNat x (pairwise_sortNatList xs)

/-- Where `insertNat` puts `x`: after everything strictly smaller than it, before everything
else. -/
theorem insertNat_split (x : Nat) : ∀ (pre suf : List Nat), (∀ z ∈ pre, ¬ x ≤ z) →
    (∀ z ∈ suf, x ≤ z) → insertNat x (pre ++ suf) = pre ++ x :: suf
  | [], suf, _, hs => by
    cases suf with
    | nil => rfl
    | cons y ys =>
      show insertNat x (y :: ys) = x :: y :: ys
      rw [insertNat, ite_eq_left (hs y (by simp))]
  | p :: ps, suf, hp, hs => by
    show insertNat x (p :: (ps ++ suf)) = p :: (ps ++ x :: suf)
    rw [insertNat, ite_eq_right (hp p (by simp)),
      insertNat_split x ps suf (fun z hz ↦ hp z (List.mem_cons_of_mem p hz)) hs]

private theorem set_append_len (p : List Nat) (y v : Nat) (s : List Nat) :
    (p ++ y :: s).set p.length v = p ++ v :: s := by
  induction p with
  | nil => rfl
  | cons a t ih => simp [ih]

private theorem set_len_reverse (rpre : List Nat) (y v : Nat) (s : List Nat) :
    (rpre.reverse ++ y :: s).set rpre.length v = rpre.reverse ++ v :: s := by
  have h := set_append_len rpre.reverse y v s
  rwa [List.length_reverse] at h

private theorem getElem!_append_len (p : List Nat) (y : Nat) (s : List Nat) :
    (p ++ y :: s)[p.length]! = y := by
  induction p with
  | nil => rfl
  | cons a t ih => simp

private theorem toList_set!_nat (a : Array Nat) (i v : Nat) :
    (a.set! i v).toList = a.toList.set i v := by
  simp [Array.set!_eq_setIfInBounds]

private theorem getElem!_toList_nat (a : Array Nat) (i : Nat) : a[i]! = a.toList[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, getElem!_pos a.toList i (by simpa using h)]
    simp
  · rw [getElem!_neg a i h, getElem!_neg a.toList i (by simpa using h)]

/-- The invariant of the slide: the scan sits at index `j`, the sorted prefix below it read
backwards is `rpre`, the slot at `j` holds junk, and everything above it is at least `x`. -/
theorem toList_bubbleDown (x : Nat) (rpre : List Nat) :
    ∀ (fuel j : Nat) (suf : List Nat) (y : Nat) (a : Array Nat),
      j = rpre.length → j < fuel → rpre.Pairwise (fun p q ↦ q ≤ p) → (∀ z ∈ suf, x ≤ z) →
      a.toList = rpre.reverse ++ y :: suf →
      (bubbleDown x fuel j a).toList = insertNat x (rpre.reverse ++ suf) := by
  induction rpre with
  | nil =>
    intro fuel j suf y a hj hf _ hs ha
    subst hj
    cases fuel with
    | zero => exact absurd hf (by omega)
    | succ fuel =>
      rw [bubbleDown, ite_eq_left (show ([] : List Nat).length = 0 from rfl), toList_set!_nat, ha]
      simpa using (insertNat_split x [] suf (by simp) hs).symm
  | cons v rs ih =>
    intro fuel j suf y a hj hf hp hs ha
    subst hj
    have hmax : ∀ z ∈ v :: rs, z ≤ v := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact Nat.le_refl z
      · exact (List.pairwise_cons.1 hp).1 z hz
    have hrev : (v :: rs).reverse = rs.reverse ++ [v] := by simp
    have hva : a[(v :: rs).length - 1]! = v := by
      rw [getElem!_toList_nat, ha, hrev, List.append_assoc]
      simp
    cases fuel with
    | zero => exact absurd hf (by omega)
    | succ fuel =>
      rw [bubbleDown, ite_eq_right (by simp), hva]
      by_cases hvx : v < x
      · rw [ite_eq_left hvx, toList_set!_nat, ha, set_len_reverse]
        refine (insertNat_split x ((v :: rs).reverse) suf ?_ hs).symm
        intro z hz
        have := hmax z (List.mem_reverse.1 hz)
        omega
      · rw [ite_eq_right hvx]
        have hnext : (a.set! (v :: rs).length v).toList = rs.reverse ++ v :: (v :: suf) := by
          rw [toList_set!_nat, ha, set_len_reverse, hrev, List.append_assoc]
          rfl
        have hkey := ih fuel rs.length (v :: suf) v (a.set! (v :: rs).length v) rfl
          (by simp at hf ⊢; omega) (List.pairwise_cons.1 hp).2
          (by
            intro z hz
            rcases List.mem_cons.1 hz with rfl | hz
            · omega
            · exact hs z hz)
          hnext
        rw [show (v :: rs).length - 1 = rs.length by simp, hkey, hrev, List.append_assoc]
        rfl

theorem toList_insertArr (x : Nat) (out : Array Nat) (h : out.toList.Pairwise (· ≤ ·)) :
    (insertArr x out).toList = insertNat x out.toList := by
  have hrev : out.toList.reverse.Pairwise (fun p q ↦ q ≤ p) := List.pairwise_reverse.2 h
  have hkey := toList_bubbleDown x out.toList.reverse (out.size + 1) out.size [] x (out.push x)
    (by simp) (by omega) hrev (by simp) (by simp)
  rw [insertArr]
  simpa using hkey

theorem toList_insSortFrom (a : Array Nat) : ∀ (fuel i : Nat) (out : Array Nat), i ≤ fuel →
    i ≤ a.size → out.toList = sortNatList (a.toList.drop i) →
    (insSortFrom a fuel i out).toList = sortNatList a.toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro i out hi _ hout
    have hi0 : i = 0 := Nat.le_zero.1 hi
    subst hi0
    simpa [insSortFrom] using hout
  | succ k ih =>
    intro i out hi hsz hout
    rw [insSortFrom]
    match i with
    | 0 => simpa using hout
    | i + 1 =>
      rw [ite_eq_right (by omega), Nat.add_sub_cancel]
      refine ih i _ (by omega) (by omega) ?_
      have hlt : i < a.toList.length := by
        have : i < a.size := by omega
        simpa using this
      have hdrop : a.toList.drop i = a.toList[i] :: a.toList.drop (i + 1) :=
        List.drop_eq_getElem_cons hlt
      rw [toList_insertArr _ _ (hout ▸ pairwise_sortNatList _), hout, hdrop, sortNatList,
        getElem!_toList_nat, getElem!_pos a.toList i hlt]

/-- The array insertion sort agrees with the list one, which is what lets `sortNatsFast` run it. -/
theorem insSortArr_eq (a : Array Nat) : insSortArr a = (sortNatList a.toList).toArray := by
  have hd : a.toList.drop a.size = [] := List.drop_eq_nil_of_le (by simp)
  refine Array.ext' ?_
  rw [List.toList_toArray]
  exact toList_insSortFrom a a.size a.size _ (Nat.le_refl _) (Nat.le_refl _)
    (by simp [hd, sortNatList])

/-- What `sortNats` actually runs.  Most splitters meet one, two or three cells whatever the size
of the graph, and those three lengths are worth peeling off, because the list round trip costs
more than the comparisons do: sorting three elements this way allocates one array, and through
`sortNatList` it allocates a dozen.  Refinement of a sparse graph spends about a tenth of its time
in this function, and both of its call sites are in the pop loop.  Long arrays go to
`sortNatsLarge`, which counts rather than compares. -/
def sortNatsFast (a : Array Nat) : Array Nat :=
  if a.size ≤ 1 then a
  else if a.size == 2 then (if a[0]! ≤ a[1]! then a else #[a[1]!, a[0]!])
  else if a.size == 3 then
    let x := a[0]!
    let y := a[1]!
    let z := a[2]!
    if x ≤ y then (if y ≤ z then a else if x ≤ z then #[x, z, y] else #[z, x, y])
    else (if x ≤ z then #[y, x, z] else if y ≤ z then #[y, z, x] else #[z, y, x])
  else if a.size ≤ 8 then insSortArr a
  else sortNatsLarge a

@[csimp] theorem sortNats_eq_sortNatsFast : @sortNats = @sortNatsFast := by
  funext a
  obtain ⟨l⟩ := a
  match l with
  | [] => rfl
  | [x] => rfl
  | [x, y] =>
    simp only [sortNats, sortNatsFast, Array.size, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceLeDiff, ite_false, beq_self_eq_true, ite_true, sortNatList,
      insertNat]
    split <;> simp_all <;> omega
  | [x, y, z] =>
    have e0 : (⟨[x, y, z]⟩ : Array Nat)[0]! = x := rfl
    have e1 : (⟨[x, y, z]⟩ : Array Nat)[1]! = y := rfl
    have e2 : (⟨[x, y, z]⟩ : Array Nat)[2]! = z := rfl
    simp only [sortNats, sortNatsFast, Array.size, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceLeDiff, ite_false, Nat.reduceBEq, ite_true, Bool.false_eq_true,
      e0, e1, e2]
    rw [sortNatList_three]
    split <;> split <;> first | rfl | (split <;> rfl)
  | x :: y :: z :: w :: t =>
    simp only [sortNatsFast, Array.size, List.length_cons]
    rw [ite_eq_right (by omega), ite_eq_right (by simp), ite_eq_right (by simp), sortNatsLarge_eq,
      insSortArr_eq]
    rfl

/-- Collect the distinct cell starts of the vertices in `touched[j:]`, using `hit` to deduplicate.
Phase (2) of `refineStep`, as a structural recursion on fuel; `fuel` is only ever
`touched.size - j`. -/
def collectFrom (pos cst touched : Array Nat) :
    Nat → Nat → Array Bool → Array Nat → Array Bool × Array Nat
  | 0, _, hit, cells => (hit, cells)
  | fuel + 1, j, hit, cells =>
    if j ≥ touched.size then (hit, cells)
    else
      let c := cst[pos[touched[j]!]!]!
      if hit[c]! then collectFrom pos cst touched fuel (j + 1) hit cells
      else collectFrom pos cst touched fuel (j + 1) (hit.set! c true) (cells.push c)

/-- Bucket the cell `lab[k:ec]` by neighbour count: `bc[t]` counts the members whose count is `t`,
and `ks` lists the counts that occur, in first-occurrence order.  Phase (3a) of `refineStep`, and
another fuel recursion in place of a `for` loop; `fuel` is only ever `ec - k`. -/
def bucketFrom (lab cnt : Array Nat) (ec : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, bc, ks => (bc, ks)
  | fuel + 1, k, bc, ks =>
    if k ≥ ec then (bc, ks)
    else
      let t := cnt[lab[k]!]!
      let b := bc[t]!
      bucketFrom lab cnt ec fuel (k + 1) (bc.set! t (b + 1)) (if b == 0 then ks.push t else ks)

/-- Turn the bucket sizes into the fragment sizes `sizes[j]` and the bucket *offsets* `bc[ks[j]]`
(relative to the start of the cell).  `acc` is the running offset.  Phase (3b). -/
def offsetFrom (ks : Array Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Array Nat × Array Nat
  | 0, _, sizes, bc, _ => (sizes, bc)
  | fuel + 1, j, sizes, bc, acc =>
    if j ≥ ks.size then (sizes, bc)
    else
      let t := ks[j]!
      let b := bc[t]!
      offsetFrom ks fuel (j + 1) (sizes.set! j b) (bc.set! t acc) (acc + b)

/-- Scatter the cell's vertices into `block` in count order, each bucket keeping the order it had
in the cell.  Phase (3c). -/
def scatterFrom (lab cnt : Array Nat) (ec : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, block, bc => (block, bc)
  | fuel + 1, k, block, bc =>
    if k ≥ ec then (block, bc)
    else
      let v := lab[k]!
      let t := cnt[v]!
      let o := bc[t]!
      scatterFrom lab cnt ec fuel (k + 1) (block.set! o v) (bc.set! t (o + 1))

/-- Zero the buckets the cell used, leaving `bc` clear for the next cell.  Phase (3d). -/
def clearBcFrom (ks : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, bc => bc
  | fuel + 1, j, bc =>
    if j ≥ ks.size then bc else clearBcFrom ks fuel (j + 1) (bc.set! ks[j]! 0)

/-- Copy the sorted block back into `lab[c:]`, keeping `pos` its inverse.  Phase (3e). -/
def writeFrom (block : Array Nat) (c : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, lab, pos => (lab, pos)
  | fuel + 1, k, lab, pos =>
    if k ≥ block.size then (lab, pos)
    else
      let v := block[k]!
      writeFrom block c fuel (k + 1) (lab.set! (c + k) v) (pos.set! v (c + k))

/-- Write the boundaries of the fragment `[st, en)` into `cst`/`cen`.  Phase (4a). -/
def fillBoundsFrom (st en : Nat) : Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, cst, cen => (cst, cen)
  | fuel + 1, i, cst, cen =>
    if i ≥ en then (cst, cen)
    else fillBoundsFrom st en fuel (i + 1) (cst.set! i st) (cen.set! i en)

/-- Install the boundaries of every fragment of a split cell, collecting the fragment starts and
hashing each fragment's size and count into the trace.  Phase (4). -/
def boundsFrom (ks sizes : Array Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat → Nat → UInt64 →
      Array Nat × Array Nat × Array Nat × UInt64
  | 0, _, cst, cen, starts, _, tr => (cst, cen, starts, tr)
  | fuel + 1, j, cst, cen, starts, st, tr =>
    if j ≥ ks.size then (cst, cen, starts, tr)
    else
      let sz := sizes[j]!
      let en := st + sz
      match fillBoundsFrom st en sz st cst cen with
      | (cst, cen) =>
        boundsFrom ks sizes fuel (j + 1) cst cen (starts.push st) en (mixN (mixN tr sz) ks[j]!)

/-- Queue every fragment of a split cell.  Phase (5), the case where the parent was queued. -/
def markAllFrom (starts : Array Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, inW => inW
  | fuel + 1, j, inW =>
    if j ≥ starts.size then inW else markAllFrom starts fuel (j + 1) (inW.set! starts[j]! true)

/-- Index of a largest fragment, scanning left to right. -/
def maxIdxFrom (sizes : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, bi => bi
  | fuel + 1, k, bi =>
    if k ≥ sizes.size then bi
    else maxIdxFrom sizes fuel (k + 1) (if sizes[k]! > sizes[bi]! then k else bi)

/-- Queue every fragment but `starts[bi]`.  Phase (5), Hopcroft's case: skipping one largest
fragment is what keeps refinement near-linear. -/
def markExceptFrom (starts : Array Nat) (bi : Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, inW => inW
  | fuel + 1, k, inW =>
    if k ≥ starts.size then inW
    else markExceptFrom starts bi fuel (k + 1) (if k != bi then inW.set! starts[k]! true else inW)

/-- Zero the counts of the touched vertices.  Phase (6). -/
def clearCntFrom (touched : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, cnt => cnt
  | fuel + 1, j, cnt =>
    if j ≥ touched.size then cnt else clearCntFrom touched fuel (j + 1) (cnt.set! touched[j]! 0)

/-- Unmark the cells that were collected.  Phase (6). -/
def clearHitFrom (cells : Array Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, hit => hit
  | fuel + 1, j, hit =>
    if j ≥ cells.size then hit else clearHitFrom cells fuel (j + 1) (hit.set! cells[j]! false)

/-- The state `refineStep`'s cell loop carries: the partition being rewritten, the worklist, the
trace, and the bucket scratch.  (`cnt` is read-only during the loop, so it stays outside.) -/
structure SplitState where
  /-- Position to vertex. -/
  lab : Array Nat
  /-- Vertex to position. -/
  pos : Array Nat
  /-- Position to the start of its cell. -/
  cst : Array Nat
  /-- Position to the end of its cell. -/
  cen : Array Nat
  /-- Which cells are queued as splitters. -/
  inW : Array Bool
  /-- The trace hash so far. -/
  tr : UInt64
  /-- The bucket scratch, all-zero between cells. -/
  bc : Array Nat

/-- Split the cell starting at position `c` by neighbour count, phases (3) to (5).  Written as a
chain of `match`es rather than a `do` block for the same reason as the loops above. -/
def splitCell (cnt : Array Nat) (c : Nat) (st : SplitState) : SplitState :=
  -- Read the cell's extent *before* splitting it; splits stay inside `[c, ec)`, so the cells
  -- collected by phase (2) keep their starts.
  let ec := st.cen[c]!
  if ec - c == 1 then
    -- A singleton cell cannot split, but its count is still invariant information.
    { st with tr := mixN (mixN st.tr c) cnt[st.lab[c]!]! }
  else
    -- (3) counting sort of the cell by neighbour count.  Only the counts that actually occur in
    -- the cell are visited, so the cost is `O(|cell|)` rather than `O(|splitter|)`; `bc` doubles
    -- as the bucket-size table and then as the offset table, and is left all-zero again.
    match bucketFrom st.lab cnt ec (ec - c) c st.bc #[] with
    | (bc, ks) =>
      if ks.size == 1 then
        -- No split; record the common count and reset the scratch counter.
        { st with tr := mixN (mixN st.tr c) ks[0]!, bc := bc.set! ks[0]! 0 }
      else
        let ks := sortNats ks
        match offsetFrom ks ks.size 0 (Array.replicate ks.size 0) bc 0 with
        | (sizes, bc) =>
          match scatterFrom st.lab cnt ec (ec - c) c (Array.replicate (ec - c) 0) bc with
          | (block, bc) =>
            match writeFrom block c block.size 0 st.lab st.pos with
            | (lab, pos) =>
              -- (4) install the fragment boundaries and collect them.
              match boundsFrom ks sizes ks.size 0 st.cst st.cen #[] c (mixN st.tr c) with
              | (cst, cen, starts, tr) =>
                -- (5) worklist maintenance (Hopcroft).
                let inW :=
                  if st.inW[c]! then markAllFrom starts starts.size 0 st.inW
                  else markExceptFrom starts (maxIdxFrom sizes sizes.size 0 0) starts.size 0 st.inW
                { lab, pos, cst, cen, inW, tr, bc := clearBcFrom ks ks.size 0 bc }

/-- Phases (3) to (5) as they run on a cell of no special shape: the body of `splitCell`'s `else`
branch, with the state taken apart.  `splitCellFast` falls through to this whenever its shortcut
does not apply. -/
def splitCellGen (cnt : Array Nat) (c ec : Nat) (slab spos scst scen : Array Nat)
    (sinW : Array Bool) (str : UInt64) (sbc : Array Nat) : SplitState :=
  match bucketFrom slab cnt ec (ec - c) c sbc #[] with
  | (bc, ks) =>
    if ks.size == 1 then
      ⟨slab, spos, scst, scen, sinW, mixN (mixN str c) ks[0]!, bc.set! ks[0]! 0⟩
    else
      let ks := sortNats ks
      match offsetFrom ks ks.size 0 (Array.replicate ks.size 0) bc 0 with
      | (sizes, bc) =>
        match scatterFrom slab cnt ec (ec - c) c (Array.replicate (ec - c) 0) bc with
        | (block, bc) =>
          match writeFrom block c block.size 0 slab spos with
          | (lab, pos) =>
            match boundsFrom ks sizes ks.size 0 scst scen #[] c (mixN str c) with
            | (cst, cen, starts, tr) =>
              let inW :=
                if sinW[c]! then markAllFrom starts starts.size 0 sinW
                else markExceptFrom starts (maxIdxFrom sizes sizes.size 0 0) starts.size 0 sinW
              { lab, pos, cst, cen, inW, tr, bc := clearBcFrom ks ks.size 0 bc }

/-- Is bucket `t` in range and empty?  The two-element shortcut below computes the general path's
answer in closed form, but only when both counts have a clear bucket to begin with.  That is an
invariant of `refineStep`'s cell loop — the loop restores `bc` after every cell — but `SplitState`
does not carry it, so the shortcut has to test for it. -/
def bcOpen (sbc : Array Nat) (t : Nat) : Bool := t < sbc.size && sbc[t]! == 0

/-- What `splitCell` actually runs.  Two changes, both invisible to the caller.

*The state is taken apart first.*  `writeFrom`, `boundsFrom` and the two `mark*From` write into
`lab`, `pos`, `cst`, `cen` and `inW`, and Lean's arrays are copy-on-write: an update is in place
only when the array it is handed is the only reference to it.  Reading a field off `st` at the
point of the call leaves `st` itself holding a second reference, so every one of those five loops
would copy an array as long as the partition before touching it.  Destructuring at the top retires
`st` before any of them runs, which is worth about 1.2× on a sparse refinement — and nothing on a
dense one, where the copies are dwarfed by the counting.

*Cells of two elements are done in closed form.*  They are the commonest cell to reach the general
path, and everything it does to one is decided by whether the two counts agree: it allocates two
scratch arrays, sorts a two-element array, and makes eleven writes into the bucket array that
cancel out.  The shortcut compares the counts and writes the answer, at the cost of the `bcOpen`
guard, which the general path needs no help with.  Worth about 2% of the enumerator. -/
def splitCellFast (cnt : Array Nat) (c : Nat) (st : SplitState) : SplitState :=
  match st with
  | ⟨slab, spos, scst, scen, sinW, str, sbc⟩ =>
    let ec := scen[c]!
    if ec - c == 1 then
      ⟨slab, spos, scst, scen, sinW, mixN (mixN str c) cnt[slab[c]!]!, sbc⟩
    else if ec - c == 2 then
      let v₀ := slab[c]!
      let v₁ := slab[c + 1]!
      let t₀ := cnt[v₀]!
      let t₁ := cnt[v₁]!
      if bcOpen sbc t₀ && bcOpen sbc t₁ then
        if t₀ == t₁ then ⟨slab, spos, scst, scen, sinW, mixN (mixN str c) t₀, sbc⟩
        else
          let sw := t₁ < t₀
          let a := if sw then v₁ else v₀
          let b := if sw then v₀ else v₁
          let ta := if sw then t₁ else t₀
          let tb := if sw then t₀ else t₁
          ⟨(slab.set! c a).set! (c + 1) b, (spos.set! a c).set! b (c + 1),
            (scst.set! c c).set! (c + 1) (c + 1), (scen.set! c (c + 1)).set! (c + 1) (c + 2),
            (if sinW[c]! then (sinW.set! c true).set! (c + 1) true else sinW.set! (c + 1) true),
            mixN (mixN (mixN (mixN (mixN str c) 1) ta) 1) tb, sbc⟩
      else splitCellGen cnt c ec slab spos scst scen sinW str sbc
    else splitCellGen cnt c ec slab spos scst scen sinW str sbc

/-! ### `splitCellFast` is `splitCell`

Everything from here to `splitCell_eq_splitCellFast` exists to justify the two-element shortcut
above.  The plan: name the value of each phase of `splitCellGen` on a cell of two elements
(`bucketFrom_two_eq` … `clearBcFrom_two`), chain them (`splitCellGen_two_eq`, `splitCellGen_two_lt`,
`splitCellGen_two_gt`), and case on the guard. -/

/-- Writing back what is already there is a no-op, in bounds or out. -/
private theorem set!_of_getElem! {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {v : α}
    (h : a[i]! = v) : a.set! i v = a := by
  by_cases hi : i < a.size
  · subst h
    rw [getElem!_pos a i hi]
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hi]
  · exact Array.setIfInBounds_eq_of_size_le (by omega)

/-- `set!_of_getElem!` in the form `simp` leaves the goal in. -/
private theorem setIf_of_getElem! {α : Type _} [Inhabited α] {a : Array α} {i : Nat} {v : α}
    (h : a[i]! = v) : a.setIfInBounds i v = a := set!_of_getElem! h

/-- Writing at `i` never disturbs another index, in bounds or not. -/
private theorem getElem!_set!_nat_ne {a : Array Nat} {i x k : Nat} (h : k ≠ i) :
    (a.set! i x)[k]! = a[k]! := by
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.set! i x) k (by simpa using hk), getElem!_pos a k hk]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hk,
      ite_eq_right (Ne.symm h)]
  · rw [getElem!_neg (a.set! i x) k (by simpa using hk), getElem!_neg a k hk]

/-- Reading back what was just written. -/
private theorem getElem!_set!_nat_self {a : Array Nat} {i x : Nat} (hi : i < a.size) :
    (a.set! i x)[i]! = x := by
  rw [getElem!_set!_nat hi, ite_eq_left rfl]

/-- `getElem!_set!_nat` in the form `simp` leaves the goal in. -/
private theorem getElem!_setIfInBounds_nat {a : Array Nat} {i x : Nat} (hi : i < a.size) (k : Nat) :
    (a.setIfInBounds i x)[k]! = if k = i then x else a[k]! := getElem!_set!_nat hi k

/-- Any chain of writes at two distinct indices collapses to one write at each. -/
private theorem setIf_collapse {a : Array Nat} {i j x y u : Nat} (h : i ≠ j) :
    ((a.setIfInBounds i x).setIfInBounds j y).setIfInBounds i u
      = (a.setIfInBounds i u).setIfInBounds j y := by
  rw [Array.setIfInBounds_comm _ _ h.symm, Array.setIfInBounds_setIfInBounds]

private theorem size_two {α : Type _} (x y : α) : (#[x, y] : Array α).size = 2 := rfl

private theorem replicate_two {α : Type _} (x : α) : Array.replicate 2 x = #[x, x] := rfl

/-- Insertion sort of two naturals, as one comparison. -/
theorem sortNats_two (x y : Nat) : sortNats #[x, y] = if x ≤ y then #[x, y] else #[y, x] := by
  show (if (#[x, y] : Array Nat).size ≤ 8 then (sortNatList (#[x, y] : Array Nat).toList).toArray
      else _) = _
  rw [ite_eq_left (by simp)]
  show (sortNatList [x, y]).toArray = _
  simp only [sortNatList, insertNat]
  split <;> simp

section Phases
variable {slab spos scst scen cnt sbc : Array Nat} {sinW : Array Bool} {str : UInt64}
  {c v₀ v₁ t₀ t₁ : Nat}

/-- Phase (3a) on a two-element cell whose two counts agree. -/
theorem bucketFrom_two_eq (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁)
    (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₀) (h0 : t₀ < sbc.size) (z0 : sbc[t₀]! = 0) :
    bucketFrom slab cnt (c + 2) 2 c sbc #[] = ((sbc.set! t₀ 1).set! t₀ 2, #[t₀]) := by
  rw [bucketFrom, ite_eq_right (by omega : ¬ c ≥ c + 2)]
  simp only [hv0, ht0, z0]
  rw [bucketFrom, ite_eq_right (by omega : ¬ c + 1 ≥ c + 2)]
  simp only [hv1, ht1, bucketFrom]
  simp [getElem!_setIfInBounds_nat h0]

/-- Phase (3a) on a two-element cell whose two counts differ. -/
theorem bucketFrom_two_ne (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁)
    (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₁) (h0 : t₀ < sbc.size) (z0 : sbc[t₀]! = 0)
    (z1 : sbc[t₁]! = 0) (hne : t₁ ≠ t₀) :
    bucketFrom slab cnt (c + 2) 2 c sbc #[] = ((sbc.set! t₀ 1).set! t₁ 1, #[t₀, t₁]) := by
  rw [bucketFrom, ite_eq_right (by omega : ¬ c ≥ c + 2)]
  simp only [hv0, ht0, z0]
  rw [bucketFrom, ite_eq_right (by omega : ¬ c + 1 ≥ c + 2)]
  simp only [hv1, ht1, bucketFrom]
  simp [getElem!_setIfInBounds_nat h0, hne, z1]

/-- Phase (3b) on two singleton buckets. -/
theorem offsetFrom_two (ta tb : Nat) (bc : Array Nat) (hab : tb ≠ ta) (hta : ta < bc.size)
    (ha : bc[ta]! = 1) (hb : bc[tb]! = 1) :
    offsetFrom #[ta, tb] 2 0 (Array.replicate 2 0) bc 0
      = (#[1, 1], (bc.set! ta 0).set! tb 1) := by
  rw [replicate_two, offsetFrom, ite_eq_right (by simp)]
  simp only [show (#[ta, tb] : Array Nat)[0]! = ta from rfl, ha]
  rw [offsetFrom, ite_eq_right (by simp)]
  simp only [show (#[ta, tb] : Array Nat)[1]! = tb from rfl, getElem!_set!_nat hta,
    ite_eq_right hab, hb,
    offsetFrom]
  rfl

/-- Phase (3c) on a two-element cell. -/
theorem scatterFrom_two {bc : Array Nat} {o₀ o₁ : Nat}
    (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁) (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₁)
    (h₀ : bc[t₀]! = o₀) (h₁ : (bc.set! t₀ (o₀ + 1))[t₁]! = o₁) :
    scatterFrom slab cnt (c + 2) 2 c (Array.replicate 2 0) bc
      = (((Array.replicate 2 0).set! o₀ v₀).set! o₁ v₁,
          (bc.set! t₀ (o₀ + 1)).set! t₁ (o₁ + 1)) := by
  rw [scatterFrom, ite_eq_right (by omega : ¬ c ≥ c + 2)]
  simp only [hv0, ht0, h₀]
  rw [scatterFrom, ite_eq_right (by omega : ¬ c + 1 ≥ c + 2)]
  simp only [hv1, ht1, h₁]
  rw [scatterFrom]

/-- Phase (3e) on a two-element block. -/
theorem writeFrom_two (x y : Nat) (lab pos : Array Nat) (k : Nat) :
    writeFrom #[x, y] k 2 0 lab pos
      = ((lab.set! k x).set! (k + 1) y, (pos.set! x k).set! y (k + 1)) := by
  rfl

/-- Phase (4a) on a singleton fragment. -/
theorem fillBoundsFrom_one (st : Nat) (cst cen : Array Nat) :
    fillBoundsFrom st (st + 1) 1 st cst cen = (cst.set! st st, cen.set! st (st + 1)) := by
  rw [fillBoundsFrom, ite_eq_right (by omega), fillBoundsFrom]

/-- Phase (4) on two singleton fragments. -/
theorem boundsFrom_two (ta tb : Nat) (tr : UInt64) :
    boundsFrom #[ta, tb] #[1, 1] 2 0 scst scen #[] c tr
      = ((scst.set! c c).set! (c + 1) (c + 1), (scen.set! c (c + 1)).set! (c + 1) (c + 2),
          #[c, c + 1], mixN (mixN (mixN (mixN tr 1) ta) 1) tb) := by
  rw [boundsFrom, ite_eq_right (by simp)]
  simp only [show (#[1, 1] : Array Nat)[0]! = 1 from rfl,
    show (#[ta, tb] : Array Nat)[0]! = ta from rfl, fillBoundsFrom_one]
  rw [boundsFrom, ite_eq_right (by simp)]
  simp only [show (#[1, 1] : Array Nat)[1]! = 1 from rfl,
    show (#[ta, tb] : Array Nat)[1]! = tb from rfl, fillBoundsFrom_one]
  rw [boundsFrom]
  simp

/-- Two fragments of equal size: the first is a largest one. -/
theorem maxIdxFrom_two : maxIdxFrom #[1, 1] 2 0 0 = 0 := by
  rfl

/-- Phase (5) on two singleton fragments, parent queued. -/
theorem markAllFrom_two :
    markAllFrom #[c, c + 1] 2 0 sinW = (sinW.set! c true).set! (c + 1) true := by
  rfl

/-- Phase (5) on two singleton fragments, parent not queued: the second one is enough. -/
theorem markExceptFrom_two :
    markExceptFrom #[c, c + 1] 0 2 0 sinW = sinW.set! (c + 1) true := by
  rfl

/-- Phase (3d) on two buckets. -/
theorem clearBcFrom_two (ta tb : Nat) (bc : Array Nat) :
    clearBcFrom #[ta, tb] 2 0 bc = (bc.set! ta 0).set! tb 0 := by
  rfl

end Phases

section Gen
variable {slab spos scst scen cnt sbc : Array Nat} {sinW : Array Bool} {str : UInt64}
  {c v₀ v₁ t₀ t₁ : Nat}

/-- A two-element cell whose two vertices have the same count does not split: the general path
leaves everything but the trace alone, and puts the bucket array back as it found it. -/
theorem splitCellGen_two_eq (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁)
    (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₀) (h0 : t₀ < sbc.size) (z0 : sbc[t₀]! = 0) :
    splitCellGen cnt c (c + 2) slab spos scst scen sinW str sbc =
      ⟨slab, spos, scst, scen, sinW, mixN (mixN str c) t₀, sbc⟩ := by
  rw [splitCellGen, show c + 2 - c = 2 from by omega,
    bucketFrom_two_eq hv0 hv1 ht0 ht1 h0 z0]
  simp [setIf_of_getElem! z0]

/-- A two-element cell whose two vertices have different counts splits into two singletons.  The
hypotheses name the intermediate quantities the general path computes: the sorted key array
`#[ta, tb]`, the two scatter offsets, the resulting block `#[a, b]`, and the fact that the bucket
array comes back clear. -/
theorem splitCellGen_two_aux
    (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁) (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₁)
    (h0 : t₀ < sbc.size) (z0 : sbc[t₀]! = 0) (z1 : sbc[t₁]! = 0) (hne : t₁ ≠ t₀)
    {ta tb a b o₀ o₁ : Nat}
    (hsort : sortNats #[t₀, t₁] = #[ta, tb]) (hab : tb ≠ ta)
    (hta : ta < ((sbc.set! t₀ 1).set! t₁ 1).size)
    (ha : ((sbc.set! t₀ 1).set! t₁ 1)[ta]! = 1)
    (hb : ((sbc.set! t₀ 1).set! t₁ 1)[tb]! = 1)
    (ho₀ : ((((sbc.set! t₀ 1).set! t₁ 1).set! ta 0).set! tb 1)[t₀]! = o₀)
    (ho₁ : (((((sbc.set! t₀ 1).set! t₁ 1).set! ta 0).set! tb 1).set! t₀ (o₀ + 1))[t₁]! = o₁)
    (hblock : ((Array.replicate 2 0).set! o₀ v₀).set! o₁ v₁ = #[a, b])
    (hclear : (((((((sbc.set! t₀ 1).set! t₁ 1).set! ta 0).set! tb 1).set! t₀ (o₀ + 1)).set! t₁
        (o₁ + 1)).set! ta 0).set! tb 0 = sbc) :
    splitCellGen cnt c (c + 2) slab spos scst scen sinW str sbc =
      ⟨(slab.set! c a).set! (c + 1) b, (spos.set! a c).set! b (c + 1),
        (scst.set! c c).set! (c + 1) (c + 1), (scen.set! c (c + 1)).set! (c + 1) (c + 2),
        (if sinW[c]! then (sinW.set! c true).set! (c + 1) true else sinW.set! (c + 1) true),
        mixN (mixN (mixN (mixN (mixN str c) 1) ta) 1) tb, sbc⟩ := by
  rw [splitCellGen, show c + 2 - c = 2 from by omega,
    bucketFrom_two_ne hv0 hv1 ht0 ht1 h0 z0 z1 hne]
  simp only [show ((2 : Nat) == 1) = false from rfl, Bool.false_eq_true,
    ite_false, hsort, size_two, offsetFrom_two ta tb _ hab hta ha hb,
    scatterFrom_two hv0 hv1 ht0 ht1 ho₀ ho₁, hblock, writeFrom_two, boundsFrom_two, maxIdxFrom_two,
    markAllFrom_two, markExceptFrom_two, clearBcFrom_two, hclear]

/-- The general path on a two-element cell, first vertex of smaller count. -/
theorem splitCellGen_two_lt (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁)
    (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₁) (h0 : t₀ < sbc.size) (h1 : t₁ < sbc.size)
    (z0 : sbc[t₀]! = 0) (z1 : sbc[t₁]! = 0) (hlt : t₀ < t₁) :
    splitCellGen cnt c (c + 2) slab spos scst scen sinW str sbc =
      ⟨(slab.set! c v₀).set! (c + 1) v₁, (spos.set! v₀ c).set! v₁ (c + 1),
        (scst.set! c c).set! (c + 1) (c + 1), (scen.set! c (c + 1)).set! (c + 1) (c + 2),
        (if sinW[c]! then (sinW.set! c true).set! (c + 1) true else sinW.set! (c + 1) true),
        mixN (mixN (mixN (mixN (mixN str c) 1) t₀) 1) t₁, sbc⟩ := by
  have hne : t₁ ≠ t₀ := by omega
  have hne' : t₀ ≠ t₁ := by omega
  have s2 : t₁ < (sbc.set! t₀ 1).size := by simpa using h1
  have s0 : t₀ < ((sbc.set! t₀ 1).set! t₁ 1).size := by simpa using h0
  have s3 : t₁ < (((sbc.set! t₀ 1).set! t₁ 1).set! t₀ 0).size := by simpa using h1
  refine splitCellGen_two_aux (ta := t₀) (tb := t₁) (a := v₀) (b := v₁) (o₀ := 0) (o₁ := 1)
    hv0 hv1 ht0 ht1 h0 z0 z1 hne (by rw [sortNats_two, ite_eq_left (Nat.le_of_lt hlt)]) hne s0
    (by rw [getElem!_set!_nat_ne hne', getElem!_set!_nat_self h0])
    (by rw [getElem!_set!_nat_self s2])
    (by rw [getElem!_set!_nat_ne hne', getElem!_set!_nat_self s0])
    (by rw [getElem!_set!_nat_ne hne, getElem!_set!_nat_self s3]) rfl ?_
  simp [setIf_collapse hne', setIf_collapse hne, setIf_of_getElem! z0, setIf_of_getElem! z1]

/-- The general path on a two-element cell, second vertex of smaller count. -/
theorem splitCellGen_two_gt (hv0 : slab[c]! = v₀) (hv1 : slab[c + 1]! = v₁)
    (ht0 : cnt[v₀]! = t₀) (ht1 : cnt[v₁]! = t₁) (h0 : t₀ < sbc.size) (h1 : t₁ < sbc.size)
    (z0 : sbc[t₀]! = 0) (z1 : sbc[t₁]! = 0) (hlt : t₁ < t₀) :
    splitCellGen cnt c (c + 2) slab spos scst scen sinW str sbc =
      ⟨(slab.set! c v₁).set! (c + 1) v₀, (spos.set! v₁ c).set! v₀ (c + 1),
        (scst.set! c c).set! (c + 1) (c + 1), (scen.set! c (c + 1)).set! (c + 1) (c + 2),
        (if sinW[c]! then (sinW.set! c true).set! (c + 1) true else sinW.set! (c + 1) true),
        mixN (mixN (mixN (mixN (mixN str c) 1) t₁) 1) t₀, sbc⟩ := by
  have hne : t₁ ≠ t₀ := by omega
  have hne' : t₀ ≠ t₁ := by omega
  have s2 : t₁ < (sbc.set! t₀ 1).size := by simpa using h1
  have s4 : t₁ < ((sbc.set! t₀ 1).set! t₁ 1).size := by simpa using h1
  have s5 : t₀ < (((sbc.set! t₀ 1).set! t₁ 1).set! t₁ 0).size := by simpa using h0
  refine splitCellGen_two_aux (ta := t₁) (tb := t₀) (a := v₁) (b := v₀) (o₀ := 1) (o₁ := 0)
    hv0 hv1 ht0 ht1 h0 z0 z1 hne (by rw [sortNats_two, ite_eq_right (by omega)]) hne' s4
    (by rw [getElem!_set!_nat_self s2])
    (by rw [getElem!_set!_nat_ne hne', getElem!_set!_nat_self h0])
    (by rw [getElem!_set!_nat_self s5])
    (by rw [getElem!_set!_nat_ne hne, getElem!_set!_nat_ne hne, getElem!_set!_nat_self s4]) rfl ?_
  simp [setIf_collapse hne', setIf_of_getElem! z0, setIf_of_getElem! z1]

end Gen

theorem bcOpen_iff {sbc : Array Nat} {t : Nat} :
    bcOpen sbc t = true ↔ t < sbc.size ∧ sbc[t]! = 0 := by
  simp [bcOpen]

/-- `splitCell` with the state taken apart and the general path named. -/
theorem splitCell_eq_ite (cnt : Array Nat) (c : Nat) (slab spos scst scen sbc : Array Nat)
    (sinW : Array Bool) (str : UInt64) :
    splitCell cnt c ⟨slab, spos, scst, scen, sinW, str, sbc⟩
      = if scen[c]! - c == 1 then
          ⟨slab, spos, scst, scen, sinW, mixN (mixN str c) cnt[slab[c]!]!, sbc⟩
        else splitCellGen cnt c scen[c]! slab spos scst scen sinW str sbc := rfl

@[csimp] theorem splitCell_eq_splitCellFast : @splitCell = @splitCellFast := by
  funext cnt c st
  obtain ⟨slab, spos, scst, scen, sinW, str, sbc⟩ := st
  rw [splitCell_eq_ite]
  simp only [splitCellFast]
  by_cases h1 : (scen[c]! - c == 1) = true
  · simp only [ite_eq_left h1]
  simp only [ite_eq_right h1]
  by_cases h2 : (scen[c]! - c == 2) = true
  · simp only [ite_eq_left h2]
    by_cases hg : (bcOpen sbc cnt[slab[c]!]! && bcOpen sbc cnt[slab[c + 1]!]!) = true
    · simp only [ite_eq_left hg]
      rw [Bool.and_eq_true] at hg
      obtain ⟨g0, g1⟩ := hg
      obtain ⟨b0, z0⟩ := bcOpen_iff.1 g0
      obtain ⟨b1, z1⟩ := bcOpen_iff.1 g1
      have hec : scen[c]! = c + 2 := by
        have : scen[c]! - c = 2 := by simpa using h2
        omega
      rw [hec]
      by_cases he : (cnt[slab[c]!]! == cnt[slab[c + 1]!]!) = true
      · rw [ite_eq_left he]
        exact splitCellGen_two_eq rfl rfl rfl (Eq.symm (by simpa using he)) b0 z0
      · rw [ite_eq_right he]
        have hne : cnt[slab[c + 1]!]! ≠ cnt[slab[c]!]! := fun h ↦ he (by simp [h])
        by_cases hsw : cnt[slab[c + 1]!]! < cnt[slab[c]!]!
        · simp only [ite_eq_left hsw]
          exact splitCellGen_two_gt rfl rfl rfl rfl b0 b1 z0 z1 hsw
        · simp only [ite_eq_right hsw]
          exact splitCellGen_two_lt rfl rfl rfl rfl b0 b1 z0 z1 (by omega)
    · simp only [ite_eq_right hg]
  · simp only [ite_eq_right h2]

/-- Split every cell in `cells[j:]`, left to right. -/
def splitCellsFrom (cnt cells : Array Nat) : Nat → Nat → SplitState → SplitState
  | 0, _, st => st
  | fuel + 1, j, st =>
    if j ≥ cells.size then st
    else splitCellsFrom cnt cells fuel (j + 1) (splitCell cnt cells[j]! st)

/-- Perform one refinement step: use the cell starting at position `s` as a splitter, splitting
every cell that meets its neighbourhood.

Returns the new partition, the updated worklist (`inW`, indexed by cell start position), the
updated trace hash, and the scratch space, restored to its cleared state.  Cells created by a
split are pushed onto the worklist following Hopcroft's rule: all fragments if the parent was
queued, otherwise all but a largest fragment.

The trailing `Nat` is a *scan hint* for `refineLoop`: a position below which this step has
certainly left the worklist untouched, so that the next pop need not rescan from `0`.  Only cells
that were split get queued, every such cell starts at or after the leftmost one processed, and `s`
itself is cleared before the step runs, so `min (s + 1) cells[0]!` will do.  Nothing is proved
about the hint and nothing needs to be: `refineLoop` pops in whatever order the hint dictates, and
`Equivariance.refineStep_equiv` shows the hint is the same on relabelled input, which is all that
equivariance of the result requires. -/
def refineStepLo (G : Graph) (p : Part) (inW : Array Bool) (s : Nat) (tr : UInt64) (sc : Scratch) :
    (Part × Array Bool × UInt64 × Scratch) × Nat :=
  let e := p.cen[s]!
  let tr := mixN tr s
  -- (1) count neighbours inside the splitter cell `lab[s:e]`.
  match countFrom G p.lab e (e - s) s sc.cnt #[] with
  | (cnt, touched) =>
    -- Nothing in the splitter cell has a neighbour, so there is nothing to split.  From cleared
    -- scratch `cnt` is `sc.cnt` unchanged (`countFrom_eq_of_touched_isEmpty`), and it is the array
    -- `countFrom` returned, rather than `sc.cnt`, that is handed back: naming `sc.cnt` here would
    -- leave a second reference to it alive across the counting loop, and the first bump of *every*
    -- step would copy an array as long as the partition instead of writing in place.
    if touched.isEmpty then ((p, inW, tr, { sc with cnt := cnt }), s + 1)
    else
      -- (2) collect the cells met by the splitter and process them left to right, so that the
      -- order in which they are processed depends only on positions.  Only *met* cells are
      -- visited, which is what keeps a refinement step proportional to the splitter's degree sum
      -- rather than to the number of cells.
      match collectFrom p.pos p.cst touched touched.size 0 sc.hit #[] with
      | (hit, collected) =>
        let cells := sortNats collected
        match splitCellsFrom cnt cells cells.size 0
            { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW, tr, bc := sc.bc } with
        | st =>
          -- (6) restore the scratch space, touching only the entries that were dirtied.  `bc` is
          -- already back to all-zero: every bucket counter is reset as soon as its cell is done.
          (({ lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen }, st.inW, st.tr,
            { cnt := clearCntFrom touched touched.size 0 cnt,
              hit := clearHitFrom cells cells.size 0 hit,
              bc := st.bc }),
            if cells.isEmpty then s + 1 else min (s + 1) cells[0]!)

/-- One refinement step, forgetting `refineStepLo`'s scan hint.  Everything proved about a step is
proved about this. -/
def refineStep (G : Graph) (p : Part) (inW : Array Bool) (s : Nat) (tr : UInt64) (sc : Scratch) :
    Part × Array Bool × UInt64 × Scratch :=
  (refineStepLo G p inW s tr sc).1

/-- Scan `a` upwards from `j` for a `true` entry.  `fuel` is only ever `a.size - j`. -/
def firstSetAux (a : Array Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j =>
    if j ≥ a.size then none else if a[j]! then some j else firstSetAux a fuel (j + 1)

/-- Index of the first `true` entry of `a` at or after `lo`.

A fuel recursion rather than the `for j in [lo:a.size]` it reads as, for once not because of a
proof — nothing below looks inside this function — but because the loop allocates its range and a
`ForInStep` per iteration, and it runs on every worklist pop: writing the scan out is worth about
3% of a refinement. -/
def firstSetFrom (a : Array Bool) (lo : Nat) : Option Nat := firstSetAux a (a.size - lo) lo

/-- The refinement worklist loop.  `fuel` bounds the number of splitter pops.

`lo` is where the scan for the next splitter starts: positions below it are known to be clear, so
the loop is spared rescanning the prefix it has already drained.  On a sparse graph the worklist
holds a few hundred cell starts at a time and the scan, not the counting, is the bulk of the work;
resuming from the hint is worth about 1.3× there and nothing on dense input.

The guard `s < G.n && p.cst[s]! == s` is never false in a real run — only cell starts are ever
queued, and a cell start stays one when its cell is split — but checking it costs one array read
per pop and saves `Equivariance.refineLoop_equiv` from having to carry the worklist invariant.
Popping a position that is not a cell start simply drops it. -/
def refineLoop (G : Graph) : Nat → Part → Array Bool → Nat → UInt64 → Scratch → Part × UInt64
  | 0, p, _, _, tr, _ => (p, tr)
  | fuel + 1, p, inW, lo, tr, sc =>
    match firstSetFrom inW lo with
    | none => (p, tr)
    | some s =>
      if s < G.n && p.cst[s]! == s then
        match refineStepLo G p (inW.set! s false) s tr sc with
        | ((p, inW, tr, sc), lo) => refineLoop G fuel p inW lo tr sc
      else refineLoop G fuel p (inW.set! s false) (s + 1) tr sc

/-- Everything the worklist loop threads, in one record: the partition, the worklist, the trace
hash, the scratch space and the scan hint.

`refineLoop` carries the same ten arrays as a `Part`, a `Scratch` and a nest of pairs, which the
step has to take apart on the way in and build back up on the way out — eight cells allocated per
pop to hold ten pointers that the next pop immediately reads back.  Flattening them into one
record costs one allocation per pop instead, and lets the step be written the way `splitCellFast`
is: destructured, so that the arrays it updates are held uniquely and updated in place. -/
structure RState where
  lab : Array Nat
  pos : Array Nat
  cst : Array Nat
  cen : Array Nat
  inW : Array Bool
  tr : UInt64
  cnt : Array Nat
  hit : Array Bool
  bc : Array Nat
  lo : Nat

/-- What `refineStepLo` actually runs: the same step over `RState`.

The two accumulators start with room for eight entries rather than none, which saves three
doublings on the typical step and is free of proof: `Array.emptyWithCapacity` is definitionally
`#[]`.  Eight and not `G.n`: a step on a large sparse graph touches a handful of vertices, and
asking for an array as long as the partition each time costs more than the doublings do. -/
def refineStepFlat (G : Graph) (s : Nat) : RState → RState
  | ⟨plab, ppos, pcst, pcen, pinW, ptr, scnt, shit, sbc, _⟩ =>
    let e := pcen[s]!
    let tr := mixN ptr s
    match countFrom G plab e (e - s) s scnt (Array.emptyWithCapacity 8) with
    | (cnt, touched) =>
      if touched.isEmpty then ⟨plab, ppos, pcst, pcen, pinW, tr, cnt, shit, sbc, s + 1⟩
      else
        match collectFrom ppos pcst touched touched.size 0 shit (Array.emptyWithCapacity 8) with
        | (hit, collected) =>
          let cells := sortNats collected
          match splitCellsFrom cnt cells cells.size 0
              { lab := plab, pos := ppos, cst := pcst, cen := pcen, inW := pinW, tr,
                bc := sbc } with
          | st =>
            ⟨st.lab, st.pos, st.cst, st.cen, st.inW, st.tr,
              clearCntFrom touched touched.size 0 cnt,
              clearHitFrom cells cells.size 0 hit, st.bc,
              if cells.isEmpty then s + 1 else min (s + 1) cells[0]!⟩

@[inherit_doc refineStepFlat]
def refineLoopAux (G : Graph) : Nat → RState → RState
  | 0, r => r
  | fuel + 1, r =>
    match firstSetFrom r.inW r.lo with
    | none => r
    | some s =>
      if s < G.n && r.cst[s]! == s then
        refineLoopAux G fuel (refineStepFlat G s { r with inW := r.inW.set! s false })
      else
        refineLoopAux G fuel { r with inW := r.inW.set! s false, lo := s + 1 }

@[inherit_doc refineStepFlat]
def refineLoopFast (G : Graph) (fuel : Nat) (p : Part) (inW : Array Bool) (lo : Nat) (tr : UInt64)
    (sc : Scratch) : Part × UInt64 :=
  match refineLoopAux G fuel ⟨p.lab, p.pos, p.cst, p.cen, inW, tr, sc.cnt, sc.hit, sc.bc, lo⟩ with
  | r => ({ lab := r.lab, pos := r.pos, cst := r.cst, cen := r.cen }, r.tr)

/-- The flat step is the same step: both sides run the same `match`es on the same arguments and
package the same results. -/
theorem refineStepFlat_eq (G : Graph) (p : Part) (inW : Array Bool) (s : Nat) (tr : UInt64)
    (sc : Scratch) (lo : Nat) :
    refineStepFlat G s ⟨p.lab, p.pos, p.cst, p.cen, inW, tr, sc.cnt, sc.hit, sc.bc, lo⟩
      = match refineStepLo G p inW s tr sc with
        | ((p', inW', tr', sc'), lo') =>
          ⟨p'.lab, p'.pos, p'.cst, p'.cen, inW', tr', sc'.cnt, sc'.hit, sc'.bc, lo'⟩ := by
  obtain ⟨plab, ppos, pcst, pcen⟩ := p
  obtain ⟨scnt, shit, sbc⟩ := sc
  dsimp only [refineStepFlat, refineStepLo]
  -- the accumulators are `Array.emptyWithCapacity 8` on one side and `#[]` on the other, and
  -- `split` needs the two `if`s to have syntactically equal discriminants
  simp only [show (Array.emptyWithCapacity 8 : Array Nat) = #[] from rfl]
  split <;> rfl

@[csimp] theorem refineLoop_eq_refineLoopFast : @refineLoop = @refineLoopFast := by
  funext G fuel p inW lo tr sc
  induction fuel generalizing p inW lo tr sc with
  | zero => rfl
  | succ f ih =>
    rw [refineLoop, refineLoopFast, refineLoopAux]
    cases h : firstSetFrom inW lo with
    | none => rfl
    | some s =>
      dsimp only
      by_cases hg : (s < G.n && p.cst[s]! == s) = true
      · rw [ite_eq_left hg, ite_eq_left hg, refineStepFlat_eq]
        cases refineStepLo G p (inW.set! s false) s tr sc with
        | mk a lo' =>
          cases a with
          | mk p' b =>
            cases b with
            | mk inW' c =>
              cases c with
              | mk tr' sc' => exact ih p' inW' lo' tr' sc'
      · rw [ite_eq_right hg, ite_eq_right hg]
        exact ih p (inW.set! s false) (s + 1) tr sc

/-- Refine `p` to the coarsest equitable partition refining it, using the cells whose start
positions are flagged in `inW` as initial splitters.  Returns the refined partition together with
the trace hash of the refinement.

The fuel `n² + n + 1` is a genuine bound: a cell start enters the worklist once initially and once
per fragment of each split, there are at most `n - 1` splits, and each split creates at most `n`
fragments. -/
def refine (G : Graph) (p : Part) (inW : Array Bool) (tr : UInt64) : Part × UInt64 :=
  refineLoop G (G.n * G.n + G.n + 1) p inW 0 tr (Scratch.empty G.n)

/-- Refine from the unit partition: equivalently, the coarsest equitable partition of `G`. -/
def initialRefine (G : Graph) : Part × UInt64 :=
  let p := Part.unit G.n
  let inW := if G.n == 0 then #[] else (Array.replicate G.n false).set! 0 true
  refine G p inW hashSeed

/-- Write `c + 1` into `cst[j]` for every `j ∈ [j₀, ec)`, where `j₀` is the second argument.  A
structural recursion rather than a `for` loop so that `Equivariance.setCstFrom_getElem!` can read
off each entry; `fuel` is only ever `ec - j₀`, so the work is the same. -/
def setCstFrom (c ec : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, cst => cst
  | fuel + 1, j, cst =>
    if j ≥ ec then cst else setCstFrom c ec fuel (j + 1) (cst.set! j (c + 1))

/-- Split the vertex `v` off from its cell, placing it first.  Returns the new partition and the
position of the new singleton cell `{v}` (which is the only splitter needed to re-refine, since
the input partition is assumed equitable). -/
def individualize (p : Part) (v : Nat) : Part × Nat :=
  let i := p.pos[v]!
  let c := p.cst[i]!
  let ec := p.cen[i]!
  let u := p.lab[c]!
  let lab := (p.lab.set! c v).set! i u
  let pos := (p.pos.set! v c).set! u i
  let cst := setCstFrom c ec (ec - (c + 1)) (c + 1) p.cst
  let cen := p.cen.set! c (c + 1)
  ({ lab, pos, cst, cen }, c)

/-! ## Certificates -/

/-- Number of 64-bit words used for one row of a certificate. -/
def rowWords (n : Nat) : Nat := (n + 63) / 64

/-- An `n × n` bit matrix packed into 64-bit words: row `i` occupies words
`[i * rowWords n, (i+1) * rowWords n)`, and column `j` of a row is bit `63 - j % 64` of word
`j / 64`.  Unused trailing bits are zero.

The matrix is given as a curried function, which reads as if a caller could do its per-row work
— for `certOf` below, one array index — in the outer lambda and have this loop apply it once per
row.  It cannot: the compiler eta-expands `fun i => let row := …; fun j => …` into a function of
two arguments, so `bit i` is a partial application and the outer lambda's body runs once per
*bit*.  `certOfFast` below is what `certOf` actually runs, and it is a factor of five.

Like the partition walks above, the two loops are structural recursions on fuel rather than
`for` loops, so that induction applies to them: `fuel` counts the entries still to do and `j`
(resp. `i`) the position reached, and `j + fuel = n` is the invariant that gives `j < n` inside
the body — which is exactly what a proof about the loop needs and what a `for` loop hides. -/
def certRow (n : Nat) (b : Nat → Bool) :
    Nat → Nat → UInt64 → Nat → Array UInt64 → Array UInt64
  | 0, _, acc, k, out =>
    if n % 64 != 0 then out.set! k (acc <<< UInt64.ofNat (64 - n % 64)) else out
  | fuel + 1, j, acc, k, out =>
    let acc := acc <<< 1 ||| (if b j then 1 else 0)
    if (j + 1) % 64 == 0 then certRow n b fuel (j + 1) 0 (k + 1) (out.set! k acc)
    else certRow n b fuel (j + 1) acc k out

/-- Pack rows `i, i+1, …` of the matrix, `fuel` of them, into `out`. -/
def certRowsFrom (n : Nat) (bit : Nat → Nat → Bool) (w : Nat) :
    Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, out => out
  | fuel + 1, i, out => certRowsFrom n bit w fuel (i + 1) (certRow n (bit i) n 0 0 (i * w) out)

@[inherit_doc certRow]
def certBits (n : Nat) (bit : Nat → Nat → Bool) : Array UInt64 :=
  certRowsFrom n bit (rowWords n) n 0 (Array.replicate (n * rowWords n) 0)

/-- The adjacency matrix of `G` read off in the order `lab`, packed by `certBits`.

Packing bits most-significant-first means that comparing the word arrays lexicographically, as
unsigned integers, compares the bit strings lexicographically.  Two labellings give the same
certificate exactly when they differ by an automorphism. -/
def certOf (G : Graph) (lab : Array Nat) : Array UInt64 :=
  certBits G.n fun i => let row := G.adj[lab[i]!]!; fun j => row[lab[j]!]!

/-- `certRow` with the row of the adjacency matrix in hand rather than behind a closure. -/
def certRowAt (row : Array Bool) (lab : Array Nat) (n : Nat) :
    Nat → Nat → UInt64 → Nat → Array UInt64 → Array UInt64
  | 0, _, acc, k, out =>
    if n % 64 != 0 then out.set! k (acc <<< UInt64.ofNat (64 - n % 64)) else out
  | fuel + 1, j, acc, k, out =>
    let acc := acc <<< 1 ||| (if row[lab[j]!]! then 1 else 0)
    if (j + 1) % 64 == 0 then certRowAt row lab n fuel (j + 1) 0 (k + 1) (out.set! k acc)
    else certRowAt row lab n fuel (j + 1) acc k out

theorem certRow_eq_certRowAt (row : Array Bool) (lab : Array Nat) (n : Nat) :
    ∀ (fuel j : Nat) (acc : UInt64) (k : Nat) (out : Array UInt64),
      certRow n (fun j => row[lab[j]!]!) fuel j acc k out = certRowAt row lab n fuel j acc k out
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, acc, k, out => by
    rw [certRow, certRowAt]
    split <;> exact certRow_eq_certRowAt row lab n fuel _ _ _ _

@[inherit_doc certRowsFrom]
def certRowsFromAt (adj : Array (Array Bool)) (lab : Array Nat) (n w : Nat) :
    Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, out => out
  | fuel + 1, i, out =>
    certRowsFromAt adj lab n w fuel (i + 1) (certRowAt adj[lab[i]!]! lab n n 0 0 (i * w) out)

theorem certRowsFrom_eq_certRowsFromAt (G : Graph) (lab : Array Nat) (w : Nat) :
    ∀ (fuel i : Nat) (out : Array UInt64),
      certRowsFrom G.n (fun i => let row := G.adj[lab[i]!]!; fun j => row[lab[j]!]!) w fuel i out
        = certRowsFromAt G.adj lab G.n w fuel i out
  | 0, _, _ => rfl
  | fuel + 1, i, out => by
    rw [certRowsFrom, certRowsFromAt, certRow_eq_certRowAt]
    exact certRowsFrom_eq_certRowsFromAt G lab w fuel (i + 1) _

/-- Pack `fuel` bits of a row, starting at column `j`, into the low end of `acc`.

A word at a time rather than a bit at a time: `certRowAt` carries the output array and the word
index through every bit, and asks `(j + 1) % 64 == 0` at every bit whether to write.  This loop
carries neither, and its caller writes once per word.  That is worth a factor of two on the
certificate, on dense and sparse input alike. -/
def certWord (row : Array Bool) (lab : Array Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, acc => acc
  | fuel + 1, j, acc =>
    certWord row lab fuel (j + 1) (acc <<< 1 ||| (if row[lab[j]!]! then 1 else 0))

/-- Pack one row, word by word.  `fuel` counts the words still to write and `j` is the column the
next one starts at; the last word is short exactly when `n` is not a multiple of 64, and is
shifted up so that column `j` stays at bit `63 - j % 64`. -/
def certRowByWords (row : Array Bool) (lab : Array Nat) (n : Nat) :
    Nat → Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, _, out => out
  | fuel + 1, j, k, out =>
    if j + 64 ≤ n then
      certRowByWords row lab n fuel (j + 64) (k + 1) (out.set! k (certWord row lab 64 j 0))
    else if j ≥ n then out
    else out.set! k (certWord row lab (n - j) j 0 <<< UInt64.ofNat (64 - (n - j)))

@[inherit_doc certRowsFrom]
def certRowsByWords (adj : Array (Array Bool)) (lab : Array Nat) (n w : Nat) :
    Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, out => out
  | fuel + 1, i, out =>
    certRowsByWords adj lab n w fuel (i + 1)
      (certRowByWords adj[lab[i]!]! lab n (w + 1) 0 (i * w) out)

/-- A whole word: `f` more bits reach the next word boundary, where the bit loop writes. -/
theorem certRowAt_word (row : Array Bool) (lab : Array Nat) (n : Nat) :
    ∀ (f fuel j : Nat) (acc : UInt64) (k : Nat) (out : Array UInt64),
      j % 64 + f = 64 → f ≤ fuel →
        certRowAt row lab n fuel j acc k out
          = certRowAt row lab n (fuel - f) (j + f) 0 (k + 1)
              (out.set! k (certWord row lab f j acc)) := by
  intro f
  induction f with
  | zero => intro _ j _ _ _ h _; omega
  | succ f ih =>
    intro fuel j acc k out hj hf
    obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    rw [show fuel + 1 - (f + 1) = fuel - f from by omega,
      show j + (f + 1) = j + 1 + f from by omega, certRowAt, certWord]
    rcases Nat.eq_zero_or_pos f with rfl | hfpos
    · rw [ite_eq_left (show ((j + 1) % 64 == 0) = true by simp only [beq_iff_eq]; omega), certWord]
      simp only [Nat.sub_zero, Nat.add_zero]
    · rw [ite_eq_right (show ¬ (((j + 1) % 64 == 0) = true) by simp only [beq_iff_eq]; omega)]
      exact ih fuel (j + 1) _ k out (by omega) (by omega)

/-- The last, partial word: fewer than 64 bits remain and no boundary is crossed. -/
theorem certRowAt_tail (row : Array Bool) (lab : Array Nat) (n : Nat) :
    ∀ (f j : Nat) (acc : UInt64) (k : Nat) (out : Array UInt64), j % 64 + f ≤ 63 →
      certRowAt row lab n f j acc k out
        = if n % 64 != 0 then
            out.set! k (certWord row lab f j acc <<< UInt64.ofNat (64 - n % 64))
          else out := by
  intro f
  induction f with
  | zero => intro j acc k out _; rw [certRowAt, certWord]
  | succ f ih =>
    intro j acc k out hj
    rw [certRowAt,
      ite_eq_right (show ¬ (((j + 1) % 64 == 0) = true) by simp only [beq_iff_eq]; omega),
      ih (j + 1) _ k out (by omega), certWord]

/-- The two row loops agree, started from any word boundary. -/
theorem certRowAt_eq_certRowByWords (row : Array Bool) (lab : Array Nat) (n : Nat) :
    ∀ (fuel j k : Nat) (out : Array UInt64), j % 64 = 0 → j ≤ n → n - j ≤ 64 * fuel →
      certRowAt row lab n (n - j) j 0 k out = certRowByWords row lab n fuel j k out := by
  intro fuel
  induction fuel with
  | zero =>
    intro j k out hj hjn hf
    rw [certRowByWords, show n - j = 0 from by omega, certRowAt, show n % 64 = 0 from by omega]
    simp
  | succ fuel ih =>
    intro j k out hj hjn hf
    rw [certRowByWords]
    by_cases hlt : j + 64 ≤ n
    · rw [ite_eq_left hlt, certRowAt_word row lab n 64 (n - j) j 0 k out (by omega) (by omega),
        show n - j - 64 = n - (j + 64) from by omega]
      exact ih (j + 64) (k + 1) _ (by omega) (by omega) (by omega)
    · rw [ite_eq_right hlt, certRowAt_tail row lab n (n - j) j 0 k out (by omega)]
      by_cases hge : j ≥ n
      · rw [ite_eq_left hge, show n % 64 = 0 from by omega]
        simp
      · rw [ite_eq_right hge, show n % 64 = n - j from by omega,
          ite_eq_left (show ((n - j) != 0) = true by simp only [bne_iff_ne, ne_eq]; omega)]

theorem certRowsFromAt_eq_certRowsByWords (adj : Array (Array Bool)) (lab : Array Nat) (n w : Nat)
    (hw : n ≤ 64 * (w + 1)) : ∀ (fuel i : Nat) (out : Array UInt64),
      certRowsFromAt adj lab n w fuel i out = certRowsByWords adj lab n w fuel i out := by
  intro fuel
  induction fuel with
  | zero => intro i out; rfl
  | succ fuel ih =>
    intro i out
    rw [certRowsFromAt, certRowsByWords,
      show certRowAt adj[lab[i]!]! lab n n 0 0 (i * w) out
        = certRowAt adj[lab[i]!]! lab n (n - 0) 0 0 (i * w) out from by rw [Nat.sub_zero],
      certRowAt_eq_certRowByWords adj[lab[i]!]! lab n (w + 1) 0 (i * w) out (by omega) (by omega)
        (by omega)]
    exact ih (i + 1) _

/-- What `certOf` runs.  The row of the adjacency matrix is passed to the bit loop as an array
instead of being captured in a closure, which is the only way to make the lookup happen once per
row: see the note on `certRow`; and the bits are packed a word at a time, for the reason given at
`certWord`.  A certificate is `n²` bits, and it is taken at every leaf of the search, so this is
the second-largest cost in the whole algorithm after the refinement itself. -/
def certOfFast (G : Graph) (lab : Array Nat) : Array UInt64 :=
  certRowsByWords G.adj lab G.n (rowWords G.n) G.n 0 (Array.replicate (G.n * rowWords G.n) 0)

@[csimp] theorem certOf_eq_certOfFast : @certOf = @certOfFast := by
  funext G lab
  rw [certOfFast, ← certRowsFromAt_eq_certRowsByWords G.adj lab G.n (rowWords G.n)
    (by rw [rowWords]; omega)]
  exact certRowsFrom_eq_certRowsFromAt G lab (rowWords G.n) G.n 0 _

/-- Lexicographic comparison of `a` and `b` from index `i` on, with `fuel` bounding the number of
positions still to look at.  Written as a structural recursion rather than a `for` loop so that
the order lemmas in `IsoGraph.Canon.Search` can be proved by induction on `fuel`. -/
def lexCmpFrom (a b : Array UInt64) : Nat → Nat → Ordering
  | 0, _ => compare a.size b.size
  | fuel + 1, i =>
    if i < min a.size b.size then
      match compare a[i]! b[i]! with
      | .eq => lexCmpFrom a b fuel (i + 1)
      | c => c
    else compare a.size b.size

/-- Lexicographic comparison of `UInt64` arrays (shorter is smaller on a common prefix). -/
def lexCmpU64 (a b : Array UInt64) : Ordering := lexCmpFrom a b (min a.size b.size) 0

/-- Lexicographic comparison of `a` against the *prefix* of `b` of `a`'s length, from index `i`
on: `a` shorter than `b` and agreeing with it reads as `.eq` rather than as `.lt`.  This is
`lexCmpU64 a (b.extract 0 a.size)` without the copy — see `lexCmpU64_extract_eq`. -/
def lexCmpPreFrom (a b : Array UInt64) : Nat → Nat → Ordering
  | 0, _ => if a.size ≤ b.size then .eq else .gt
  | fuel + 1, i =>
    if i < min a.size b.size then
      match compare a[i]! b[i]! with
      | .eq => lexCmpPreFrom a b fuel (i + 1)
      | c => c
    else if a.size ≤ b.size then .eq else .gt

@[inherit_doc lexCmpPreFrom]
def lexCmpPre (a b : Array UInt64) : Ordering := lexCmpPreFrom a b (min a.size b.size) 0

private theorem size_extract_zero (b : Array UInt64) (k : Nat) :
    (b.extract 0 k).size = min k b.size := by
  simp

private theorem getElem!_extract_zero {b : Array UInt64} {k i : Nat} (h : i < min k b.size) :
    (b.extract 0 k)[i]! = b[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos b i (by omega)]
  simp

private theorem min_min_self (x y : Nat) : min x (min x y) = min x y := by omega

private theorem compare_size_min (a b : Array UInt64) :
    compare a.size (min a.size b.size) = if a.size ≤ b.size then .eq else .gt := by
  by_cases h : a.size ≤ b.size
  · rw [ite_eq_left h, Nat.min_eq_left h]
    exact Nat.compare_eq_eq.2 rfl
  · rw [ite_eq_right h, Nat.min_eq_right (by omega)]
    exact Nat.compare_eq_gt.2 (by omega)

theorem lexCmpFrom_extract (a b : Array UInt64) :
    ∀ (fuel i : Nat), lexCmpFrom a (b.extract 0 a.size) fuel i = lexCmpPreFrom a b fuel i
  | 0, _ => by rw [lexCmpFrom, lexCmpPreFrom, size_extract_zero, compare_size_min]
  | fuel + 1, i => by
    rw [lexCmpFrom, lexCmpPreFrom, size_extract_zero, min_min_self]
    by_cases h : i < min a.size b.size
    · rw [ite_eq_left h, ite_eq_left h, getElem!_extract_zero h]
      cases compare a[i]! b[i]! <;> simp [lexCmpFrom_extract a b fuel (i + 1)]
    · rw [ite_eq_right h, ite_eq_right h, compare_size_min]

/-- Comparing against a truncation is comparing against a prefix: `lexCmpPre` computes the same
answer without building the truncation. -/
theorem lexCmpU64_extract_eq (a b : Array UInt64) :
    lexCmpU64 a (b.extract 0 a.size) = lexCmpPre a b := by
  rw [lexCmpU64, lexCmpPre, size_extract_zero, min_min_self, lexCmpFrom_extract]

/-! ## Automorphisms -/

/-- Given two labellings `σ τ : position → vertex` with equal certificates, the permutation
`γ = τ ∘ σ⁻¹`, which is an automorphism of the graph.

Written as a `foldl` over `List.range n` rather than as a `for` loop so that
`IsoGraph.Canon.Autos.autoOf_get` can read off each entry; the work is the same. -/
def autoOf (n : Nat) (σ τ : Array Nat) : Array Nat :=
  (List.range n).foldl (init := Array.replicate n 0) fun g i => g.set! σ[i]! τ[i]!

/-- Whether a permutation moves some point. -/
def moves (g : Array Nat) : Bool := Id.run do
  for i in [0:g.size] do
    if g[i]! != i then return true
  return false

/-- One step of orbit closure: mark the images of `v` under all generators.  A `foldl` rather
than a `for` loop so that `IsoGraph.Canon.Orbits` can induct on the generator list. -/
def closureStep (gens : Array (Array Nat)) (mark : Array Bool) (stack : Array Nat)
    (v : Nat) : Array Bool × Array Nat :=
  gens.foldl (init := (mark, stack)) fun ms g =>
    let w := g[v]!
    if !ms.1[w]! then (ms.1.set! w true, ms.2.push w) else ms

/-- Close `mark` under the generators, using `stack` as the frontier.  `fuel` bounds the number of
pops, which is at most the number of marked points. -/
def closureLoop (gens : Array (Array Nat)) : Nat → Array Bool → Array Nat → Array Bool
  | 0, mark, _ => mark
  | fuel + 1, mark, stack =>
    if stack.isEmpty then mark
    else
      let v := stack[stack.size - 1]!
      let (mark, stack) := closureStep gens mark stack.pop v
      closureLoop gens fuel mark stack

/-- The union of the `gens`-orbits of the vertices in `seed`, as a membership array of size `n`. -/
def orbitClosure (n : Nat) (gens : Array (Array Nat)) (seed : Array Nat) : Array Bool :=
  closureLoop gens (n + 1) (seed.foldl (init := Array.replicate n false)
    fun mark v => mark.set! v true) seed
/-! ## The search -/

/-- Scan for the first disagreement at or after `i`, stopping at `m`.  A structural recursion on
fuel rather than a `for` loop with a `break`, for the same reason as the partition walks above:
`IsoGraph.Canon.Jump` needs to induct on it. -/
def commonPrefixFrom (a b : Array Nat) (m : Nat) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if i ≥ m then m
    else if a[i]! == b[i]! then commonPrefixFrom a b m fuel (i + 1)
    else i

/-- Length of the longest common prefix of two paths. -/
def commonPrefix (a b : Array Nat) : Nat :=
  let m := min a.size b.size
  commonPrefixFrom a b m m 0

/-- A leaf of the search tree: a discrete ordered partition together with the data used to compare
it against other leaves. -/
structure Leaf where
  /-- The vertices individualised to reach this leaf. -/
  path : Array Nat
  /-- Node invariants along the root-to-leaf path. -/
  invPath : Array UInt64
  /-- The certificate of `lab`. -/
  cert : Array UInt64
  /-- The labelling itself: position `↦` vertex. -/
  lab : Array Nat
  deriving Inhabited

/-- Mutable state threaded through the depth-first search. -/
structure St where
  /-- The best leaf seen so far, for the order `(invPath, cert)`. -/
  best : Option Leaf
  /-- The very first leaf reached, kept only to detect automorphisms. -/
  first : Option Leaf
  /-- Automorphisms discovered so far, as image arrays `γ[v]!`. -/
  autos : Array (Array Nat)
  /-- Number of search-tree nodes visited. -/
  nodes : Nat
  /-- When `some k`: abandon the search below depth `k`.  See `leafUpdate`. -/
  abortTo : Option Nat
  deriving Inhabited

/-- Cap on the number of stored automorphism generators.  Dropping generators only weakens orbit
pruning, so this is a pure performance guard. -/
def maxGens : Nat := 256

/-- Record a newly found automorphism, ignoring the identity and duplicates. -/
def St.addAuto (st : St) (g : Array Nat) : St :=
  if !moves g then st
  else if st.autos.size ≥ maxGens then st
  else if st.autos.any (fun h => h == g) then st
  else { st with autos := st.autos.push g }

/-- Invariant pruning at a node.  Returns `none` if the whole subtree is dominated by the current
best leaf, and otherwise the state to continue with (with the incumbent discarded if the subtree
is guaranteed to beat it). -/
def pruneNode (invPath : Array UInt64) (st : St) : Option St :=
  match st.best with
  | none => some st
  | some b =>
    match lexCmpU64 invPath (b.invPath.extract 0 invPath.size) with
    | .lt => none
    | .gt => some { st with best := none }
    | .eq => some st

/-- What `pruneNode` runs: it compares against a prefix of the incumbent's invariant path in
place, instead of copying that prefix out first, which saves an array allocation at every node
of the search. -/
def pruneNodeFast (invPath : Array UInt64) (st : St) : Option St :=
  match st.best with
  | none => some st
  | some b =>
    match lexCmpPre invPath b.invPath with
    | .lt => none
    | .gt => some { st with best := none }
    | .eq => some st

@[csimp] theorem pruneNode_eq_pruneNodeFast : @pruneNode = @pruneNodeFast := by
  funext invPath st
  simp only [pruneNode, pruneNodeFast, lexCmpU64_extract_eq]

/-- Process a leaf: update the incumbent, harvest any automorphism, and decide how far to
backjump.

If the new leaf `ν` has the same certificate as a previously completed leaf `ζ`, then
`γ = ζ ∘ ν⁻¹` is an automorphism.  Writing `k` for the depth of the greatest common ancestor of
the two leaves, `γ` fixes the first `k` individualised vertices and maps `ν`'s branch at depth `k`
onto `ζ`'s.  Since depth-first search had already *finished* `ζ`'s branch before entering `ν`'s,
every leaf still unexplored below `ν`'s branch is a `γ`-image of one already seen, and carries the
same certificate.  So the whole remainder of that branch can be abandoned: we request a backjump
to depth `k`. -/
def leafUpdate (G : Graph) (path : Array Nat) (invPath : Array UInt64) (lab : Array Nat)
    (st : St) : St := Id.run do
  let cert := certOf G lab
  let leaf : Leaf := { path, invPath, cert, lab }
  let mut st := st
  let mut jump : Option Nat := none
  match st.first with
  | none => st := { st with first := some leaf }
  | some f =>
    if lexCmpU64 cert f.cert == .eq then
      st := st.addAuto (autoOf G.n lab f.lab)
      jump := some (commonPrefix path f.path)
  match st.best with
  | none => st := { st with best := some leaf }
  | some b =>
    match lexCmpU64 invPath b.invPath with
    | .gt => st := { st with best := some leaf }
    | .lt => pure ()
    | .eq =>
      match lexCmpU64 cert b.cert with
      | .gt => st := { st with best := some leaf }
      | .lt => pure ()
      | .eq =>
        st := st.addAuto (autoOf G.n lab b.lab)
        let k := commonPrefix path b.path
        jump := some (match jump with | none => k | some j => min j k)
  return { st with abortTo := jump }

/-- The automorphisms found so far that fix every vertex of `path`.  Only these may be used to
prune the children of the node reached by `path`. -/
def usableAutos (autos : Array (Array Nat)) (path : Array Nat) : Array (Array Nat) :=
  if autos.isEmpty then autos else autos.filter fun g => path.all fun x => g[x]! == x

/-- Cached orbit information for the children of one search-tree node: the orbit of the already
processed children, under those automorphisms that fix the node's individualisation path.

`gens` is a thunk because most nodes never look at it.  A node needs it only once a child has come
back *without* a backjump request, and the branch that a matching leaf abandons is exactly a run of
nodes that each explore one child and then unwind — so on a graph with a large automorphism group
the filter would run at almost every node and be read at almost none.  Deferring it is a third of
the whole canonicalisation of `K₁₆₀`. -/
structure Orbits where
  /-- Size of `St.autos` when this was computed; used to detect staleness. -/
  nGens : Nat
  /-- The automorphisms fixing the node's path pointwise. -/
  gens : Thunk (Array (Array Nat))
  /-- Membership array for the orbit of the processed children. -/
  mark : Array Bool
  deriving Inhabited

mutual

/-- Visit one node of the search tree.  `p` is the (already refined) ordered partition, `path`
the vertices individualised to reach it, and `invPath` the node invariants along that path. -/
def dfsNode (G : Graph) (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part)
    (st : St) : St :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    if st.abortTo.isSome then st else
    match pruneNode invPath st with
    | none => st
    | some st =>
      let st := { st with nodes := st.nodes + 1 }
      match p.targetCell G.n with
      | none => leafUpdate G path invPath p.lab st
      | some c =>
        let verts := (p.lab.extract c (p.cen[c]!)).toList
        let orb : Orbits :=
          { nGens := st.autos.size, gens := Thunk.mk fun _ ↦ usableAutos st.autos path,
            mark := Array.replicate G.n false }
        dfsChildren G fuel path invPath p verts #[] orb st
  termination_by (fuel, 0)

/-- Visit the remaining children `verts` of a node, skipping those in the orbit of an already
visited child, and honouring any backjump request coming back from below. -/
def dfsChildren (G : Graph) (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part)
    (verts : List Nat) (processed : Array Nat) (orb : Orbits) (st : St) : St :=
  match verts with
  | [] => st
  | v :: vs =>
    if st.abortTo.isSome then st else
    -- Refresh the orbit cache if new automorphisms have turned up since it was built.
    let orb : Orbits :=
      if orb.nGens == st.autos.size then orb
      else
        let gens := usableAutos st.autos path
        { nGens := st.autos.size, gens := Thunk.mk fun _ ↦ gens,
          mark := orbitClosure G.n gens processed }
    if orb.mark[v]! then
      dfsChildren G fuel path invPath p vs processed orb st
    else
      let (p', s) := individualize p v
      let inW := (Array.replicate G.n false).set! s true
      let (p'', tr) := refine G p' inW hashSeed
      let childInv := invPath.push (mix tr (p''.shapeHash G.n))
      let st := dfsNode G fuel (path.push v) childInv p'' st
      -- A backjump to depth `path.size` stops here; a shallower one keeps unwinding.
      let st : St :=
        match st.abortTo with
        | some k => if k ≥ path.size then { st with abortTo := none } else st
        | none => st
      if st.abortTo.isSome then st
      else
        let orb : Orbits :=
          { orb with mark := closureLoop orb.gens.get (G.n + 1) (orb.mark.set! v true) #[v] }
        dfsChildren G fuel path invPath p vs (processed.push v) orb st
  termination_by (fuel, verts.length + 1)

end

/-! ## Entry points -/

/-- The result of canonicalisation. -/
structure Result where
  /-- The canonical labelling: `lab[i]!` is the vertex placed at canonical position `i`. -/
  lab : Array Nat
  /-- The canonical form: `certOf G lab`, one row bitmask per canonical position. -/
  cert : Array UInt64
  /-- Generators of (a subgroup of) the automorphism group found along the way. -/
  autos : Array (Array Nat)
  /-- Number of search-tree nodes visited, for diagnostics. -/
  nodes : Nat
  deriving Inhabited

/-- Compute a canonical labelling of `G`.

`Result.lab` is a permutation of `{0, …, n-1}` such that `Result.cert` depends only on the
isomorphism class of `G`. -/
def canonical (G : Graph) : Result :=
  let (p, tr) := initialRefine G
  let inv0 : Array UInt64 := #[mix tr (p.shapeHash G.n)]
  let st := dfsNode G (G.n + 1) #[] inv0 p
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }
  match st.best with
  | none =>
    { lab := Array.range G.n, cert := certOf G (Array.range G.n), autos := #[], nodes := st.nodes }
  | some b => { lab := b.lab, cert := b.cert, autos := st.autos, nodes := st.nodes }

/-- The canonical form of `G`: an isomorphism invariant that is complete (equal iff isomorphic,
for graphs on the same number of vertices). -/
def canonicalForm (G : Graph) : Array UInt64 :=
  (canonical G).cert

/-- Positional inverse of `a`: if `a` is a permutation of `{0, …, n-1}` then this is the array
with `invLab n a` at position `a[i]!` equal to `i`.  Used only to *check* that, so nothing is
claimed about it when `a` is not a permutation. -/
def invLab (n : Nat) (a : Array Nat) : Array Nat :=
  (List.range n).foldl (init := Array.replicate n 0) fun b i =>
    if a[i]! < n then b.set! a[i]! i else b

/-- Is `a` a permutation of `{0, …, n-1}`?  `O(n)`: build the positional inverse and check that
it really inverts, which gives injectivity for free (if `a[v]! = a[w]!` then
`v = b[a[v]!]! = b[a[w]!]! = w`). -/
def isPermArray (n : Nat) (a : Array Nat) : Bool :=
  a.size == n &&
    (let b := invLab n a
     (List.range n).all fun i => a[i]! < n && b[a[i]!]! == i)

/-- Canonical labelling from an adjacency oracle.

The search's output is checked to be a permutation of `{0, …, n-1}` before being returned, and
the identity is substituted if it is not.  The check costs `O(n)` against an `Ω(n²)` search, and
makes the returned array a permutation whatever the search does (`Spec.labellingIsPerm`). -/
def canonicalLabellingOfOracle (n : Nat) (f : Nat → Nat → Bool) : Array Nat :=
  let a := (canonical (Graph.ofOracle n f)).lab
  if isPermArray n a then a else Array.range n

end Canon
end IsoGraph
