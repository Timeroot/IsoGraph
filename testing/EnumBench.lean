import IsoGraph.Enum.Conn

/-!
Benchmark driver for the graph enumerators.

    lake exe enumbench          -- `enumCodesFast` and `enumConnCodes` up to n = 8
    lake exe enumbench --all    -- also the two weaker prunings, and the brute-force sweep
    lake exe enumbench 9        -- up to n = 9 (274668 graphs, ~1 minute)

The all-graphs counts must reproduce OEIS A000088, the connected ones OEIS A001349.
-/

open CGraph.Enum

/-- Number of graphs on `n` unlabelled vertices (OEIS A000088). -/
def a000088 : Array Nat := #[1, 1, 2, 4, 11, 34, 156, 1044, 12346, 274668]

/-- Number of *connected* graphs on `n` unlabelled vertices (OEIS A001349), except that the empty
graph is not counted as connected here. -/
def a001349 : Array Nat := #[0, 1, 1, 2, 6, 21, 112, 853, 11117, 261080]

/-- CPU nanoseconds this thread has been *running* for, from `/proc/thread-self/schedstat`.  The
wall clock is useless on a shared machine: the first field of `schedstat` excludes the time the
thread spent on the runqueue, which is the second.  It has to be `thread-self`: `main` does not
run on the thread group leader, so `/proc/self/schedstat` never moves. -/
def cpuNs : IO Nat := do
  let s ← IO.FS.readFile "/proc/thread-self/schedstat"
  return ((s.splitOn " ").headD "0").trimAscii.toNat?.getD 0

def timeIt (label : String) (expect : Nat) (act : Unit → Nat) : IO Bool := do
  let t0 ← IO.monoMsNow
  let v := act ()
  -- force before reading the clock: `let v := …` on its own would leave a thunk
  let v ← (if v == 0 then pure 0 else pure v)
  let t1 ← IO.monoMsNow
  let ok := v == expect
  IO.println s!"  {label}  {v} classes  ({t1 - t0} ms){if ok then "" else s!"  *** expected {expect}"}"
  (← IO.getStdout).flush
  return ok

def run (name : String) (upTo : Nat) (expect : Array Nat) (f : Nat → Nat) : IO Bool := do
  IO.println name
  let mut ok := true
  for n in List.range (upTo + 1) do
    ok := (← timeIt s!"n={n}" expect[n]! fun _ => f n) && ok
  return ok

/-! ### Where the top level goes

`--split n` times the last step of `enumCodesFast (n+1)` in pieces, each line adding one stage to
the one above it, so that a difference of two lines is the cost of a stage:

* `parents` is `enumCodesFast n`, which every line below pays for;
* `autos`, `sym`, `masks`, `key` are the candidate reduction taken apart: the automorphisms of each
  parent (one canonicalisation search per parent), the scan of all `2^n` masks for the least in its
  orbit, and the least-degree and least-key tests that survive it;
* `sweep` … `canon` add the per-*candidate* work, one piece of the canonicalisation at a time;
* `full` adds the sort and the deduplication.

Three lines are not stages but the discarded halves of an A/B: `sweepFin` builds the same graph
through the `Fin`-indexed `CGraph.Adj` that `canonOfCode` used to go through, `sweepTrv` replaces
the oracle by a constant-time one, and `code` is the certificate readback as `codeOfAdj ∘ certGet`
rather than as `codeOfCert`.  At `n = 7` the level splits as

    parents 36  autos +28  sym +25  masks +2  key +15  sweep +39  refine +95  nodes +123  code +5

in milliseconds — the canonicalisation is just over two thirds of it, and the initial refinement
alone is more than a third of *that*.  The reduction pays about 15 ms for the key test and saves
several times that on every stage below it.  `sweepFin - sweep` is the 12 ms the `Fin` round trip
used to cost and `code - codeFast` the 22 ms the old readback used to. -/
def splitParents (n : ℕ) : ℕ := (enumCodesFast n).length

def overParents (n : ℕ) (f : ℕ → ℕ) : ℕ := (enumCodesFast n).foldl (fun a c ↦ a + f c) 0

/-- Scaffolding: the automorphism stage with only the search, no permutation plumbing. -/
def splitAutoSrch (n : ℕ) : ℕ :=
  overParents n fun c ↦
    (IsoGraph.Canon.canonical (IsoGraph.Canon.Graph.ofOracle n (codeOracle c))).autos.size

/-- Scaffolding: + `permOfArrays`/`invArray`, forced by reading every value of every perm. -/
def splitAutoConv (n : ℕ) : ℕ :=
  overParents n fun c ↦
    ((IsoGraph.Canon.canonical (IsoGraph.Canon.Graph.ofOracle n (codeOracle c))).autos.toList.map
      fun a ↦ IsoGraph.Canon.permOfArrays n a (IsoGraph.Canon.invArray n a)).foldl
        (fun t σ ↦ (List.finRange n).foldl (fun u k ↦ u + (σ k).1) t) 0

def splitAutos (n : ℕ) : ℕ := overParents n fun c ↦ (autoPerms n (graphOfCode n c).Adj).length

/-- Candidate replacement for `gatherMask` in the orbit test: `s ≤ gatherMask s p`, decided from
the top bit down.  Bit `k` of `gatherMask s p` is bit `p[k]` of `s`, so the highest `k` at which
the two differ settles the comparison — usually the second or third one tried. -/
def leGatherFrom (s : ℕ) (p : Array ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    let a := s.testBit k
    let b := s.testBit p[k]!
    if a == b then leGatherFrom s p k else b

/-- Candidate `symMasksFast`, with the orbit test above.  Must agree with `sym`. -/
def splitSymEarly (n : ℕ) : ℕ :=
  overParents n fun c ↦
    let ps := (autoPerms n (graphOfCode n c).Adj).map fun σ ↦ Array.ofFn (n := n) fun k ↦ (σ k).1
    ((List.range (2 ^ n)).filter fun s ↦ ps.all fun p ↦ leGatherFrom s p n).length

/-- Scaffolding: the mask scan with the orbit test removed, so that what is left is `List.range`
and the filter.  The floor for the two lines above it. -/
def splitSymTriv (n : ℕ) : ℕ :=
  overParents n fun c ↦
    let m := 2 ^ n
    (autoPerms n (graphOfCode n c).Adj).length + ((List.range m).filter fun s ↦ s != m).length

def splitSym (n : ℕ) : ℕ := overParents n fun c ↦ (symMasks n c).length

def splitMasks (n : ℕ) : ℕ := overParents n fun c ↦ (redMasks n c).length

/-! ### How much finer can the deletion rule be?

`redMasks` offers the masks whose new vertex is of least degree in the extension, and the level
would then canonicalise 18329 candidates to find 12346 classes: 1.48 candidates per class, one for
each orbit of least-degree vertices.  *Any* isomorphism-invariant key on the vertices would do —
every graph has a vertex of least key, which is all `redMasks_complete` needs — and a finer key
admits fewer.  `key` is the library's `keyMasks`, whose key is the degree tie-broken by the sum of
the neighbours' degrees; `keyMul` is the discarded alternative, the whole *multiset* of the
neighbours' degrees as a base-16 numeral, counted here ignoring what computing it would cost.
`full` at 12346 is the floor.

    masks 18329   key 13304   keyMul 13080   full 12346

Five sixths of the way to the floor for a test that reads two sums off the parent's degrees; the
multiset buys another 224 candidates for a numeral `2^n` bits wide. -/
def splitKey (n : ℕ) : ℕ := overParents n fun c ↦ (keyMasks n c).length

/-- The whole multiset of the neighbours' degrees, base 16, tie-broken under the degree. -/
def keyMul {m : ℕ} (adj : Fin m → Fin m → Bool) (i : Fin m) : ℕ :=
  deg adj i * 16 ^ m + ((List.finRange m).filter (adj i)).foldl (fun a j ↦ a + 16 ^ deg adj j) 0

/-- Candidates left when the new vertex must minimise `key` over the extension. -/
def overKey (n : ℕ) (key : (Fin (n + 1) → Fin (n + 1) → Bool) → Fin (n + 1) → ℕ) : ℕ :=
  overParents n fun c ↦
    ((redMasks n c).filter fun s ↦
      let A := (graphOfCode (n + 1) (extendCode n c s)).Adj
      let k := key A (Fin.last n)
      (List.finRange (n + 1)).all fun i ↦ decide (k ≤ key A i)).length

def splitKeyMul (n : ℕ) : ℕ := overKey n keyMul

/-- Fold `f` over every candidate code of the last level, on top of the two stages above. -/
def overCands (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  (enumCodesFast n).foldl (fun a c ↦ (keyMasks n c).foldl (fun a s ↦ a + f (extendCode n c s)) a) 0

def splitSweep (n : ℕ) : ℕ :=
  overCands n fun C ↦ (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C)).nbr.size

def splitSweepFin (n : ℕ) : ℕ :=
  overCands n fun C ↦ (IsoGraph.Canon.Graph.ofOracle (n + 1)
    (IsoGraph.Canon.oracleOfFin (n + 1) (graphOfCode (n + 1) C).Adj)).nbr.size

/-- The oracle-free floor of `sweep`: the same two arrays built from a constant-time oracle.  Only
a fifth of the sweep is the oracle, so there is nothing to win by making `codeOracle` cheaper —
rewriting its `pairIdx` with shifts, or hoisting the column offset out of the row loop, both came
out at the `sweep` time to within a millisecond. -/
def splitSweepTriv (n : ℕ) : ℕ :=
  overCands n fun _ ↦ (IsoGraph.Canon.Graph.ofOracle (n + 1) (fun i j ↦ i != j)).nbr.size

def splitRefine (n : ℕ) : ℕ :=
  overCands n fun C ↦ (IsoGraph.Canon.initialRefine
    (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).1.lab[0]!

/-! ### A/B harness for the refinement

The refinement is two thirds of the enumerator and every edit to it costs a full rebuild of the
library, because `precompileModules` makes every executable link the shared object.  Copying the
worklist loop here instead costs a fifteen-second rebuild of this file: the leaf helpers stay the
library's, and `csimp` applies to a copy in a downstream module exactly as it does to the original,
so `refineP` really is what `initialRefine` runs.  `refineNull` is its floor — the four arrays of
the unit partition and the three of the scratch space, allocated and thrown away.

The copy takes the cell splitter as a parameter (`splitRefineOf`), which is where the candidates
went.  Two are settled and gone: giving the two `push` accumulators of `splitCell` a capacity to
start with is worth nothing (`Array.emptyWithCapacity` only hints to the runtime, and the arrays
reach one or two entries anyway), and the two-element shortcut is in the library. -/
open IsoGraph.Canon in
/-- Setup only: `Part.unit` and `Scratch.empty`, with nothing refined. -/
def splitRefineNull (n : ℕ) : ℕ :=
  overCands n fun C ↦
    let G := Graph.ofOracle (n + 1) (codeOracle C)
    let p := Part.unit G.n
    let sc := Scratch.empty G.n
    p.lab[0]! + p.pos[0]! + p.cst[0]! + p.cen[0]! + sc.cnt[0]! + sc.bc[0]!
      + (if sc.hit[0]! then 1 else 0)

section RefineAB
open IsoGraph.Canon

/-- Copy of `splitCellsFrom` over a cell splitter to be chosen. -/
@[specialize] def splitCellsFromG (sc : Array Nat → Nat → SplitState → SplitState)
    (cnt cells : Array Nat) : Nat → Nat → SplitState → SplitState
  | 0, _, st => st
  | fuel + 1, j, st =>
    if j ≥ cells.size then st
    else splitCellsFromG sc cnt cells fuel (j + 1) (sc cnt cells[j]! st)

/-- Copy of `refineStepFlat`. -/
@[specialize] def refineStepG (sc : Array Nat → Nat → SplitState → SplitState) (G : Graph)
    (s : Nat) : RState → RState
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
          match splitCellsFromG sc cnt cells cells.size 0
              { lab := plab, pos := ppos, cst := pcst, cen := pcen, inW := pinW, tr,
                bc := sbc } with
          | st =>
            ⟨st.lab, st.pos, st.cst, st.cen, st.inW, st.tr,
              clearCntFrom touched touched.size 0 cnt,
              clearHitFrom cells cells.size 0 hit, st.bc,
              if cells.isEmpty then s + 1 else min (s + 1) cells[0]!⟩

/-- Copy of `refineLoopAux`. -/
@[specialize] def refineLoopG (sc : Array Nat → Nat → SplitState → SplitState) (G : Graph) :
    Nat → RState → RState
  | 0, r => r
  | fuel + 1, r =>
    match firstSetFrom r.inW r.lo with
    | none => r
    | some s =>
      if s < G.n && r.cst[s]! == s then
        refineLoopG sc G fuel (refineStepG sc G s { r with inW := r.inW.set! s false })
      else refineLoopG sc G fuel { r with inW := r.inW.set! s false, lo := s + 1 }

/-- Copy of `initialRefine`. -/
@[specialize] def initialRefineG (sc : Array Nat → Nat → SplitState → SplitState) (G : Graph) :
    Part × UInt64 :=
  let p := Part.unit G.n
  let inW := if G.n == 0 then #[] else (Array.replicate G.n false).set! 0 true
  let scr := Scratch.empty G.n
  match refineLoopG sc G (G.n * G.n + G.n + 1)
    ⟨p.lab, p.pos, p.cst, p.cen, inW, hashSeed, scr.cnt, scr.hit, scr.bc, 0⟩ with
  | r => ({ lab := r.lab, pos := r.pos, cst := r.cst, cen := r.cen }, r.tr)

end RefineAB

/-- Refine every candidate of the last level, splitting cells with `sc`. -/
@[specialize] def splitRefineOf
    (sc : Array Nat → Nat → IsoGraph.Canon.SplitState → IsoGraph.Canon.SplitState) (n : ℕ) : ℕ :=
  overCands n fun C ↦ (initialRefineG sc
    (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).1.lab[0]!

/-- The in-file baseline: must agree with `refine`, in value and in time. -/
def splitRefineP (n : ℕ) : ℕ := splitRefineOf IsoGraph.Canon.splitCell n

/-! ### What a refinement is made of

`--stats n` counts, over every candidate of the last level of `enumCodesFast (n+1)`, the units of
work an initial refinement does: worklist pops, splitter-cell vertices, neighbour bumps (the
counting loop), cells collected, and the vertices of the cells actually handed to `splitCell`. -/
open IsoGraph.Canon in
/-- The step of `refineStepFlat`, with counters alongside. -/
def refineStepS (G : Graph) (s : Nat) : RState × (Nat × Nat × Nat × Nat × Nat) →
    RState × (Nat × Nat × Nat × Nat × Nat)
  | (⟨plab, ppos, pcst, pcen, pinW, ptr, scnt, shit, sbc, _⟩, ⟨pops, sv, bumps, cl, sz⟩) =>
    let e := pcen[s]!
    let sv := sv + (e - s)
    let bumps := bumps + (List.range (e - s)).foldl (fun a k ↦ a + G.nbr[plab[s + k]!]!.size) 0
    let tr := mixN ptr s
    match countFrom G plab e (e - s) s scnt (Array.emptyWithCapacity 8) with
    | (cnt, touched) =>
      if touched.isEmpty then
        (⟨plab, ppos, pcst, pcen, pinW, tr, cnt, shit, sbc, s + 1⟩, ⟨pops + 1, sv, bumps, cl, sz⟩)
      else
        match collectFrom ppos pcst touched touched.size 0 shit (Array.emptyWithCapacity 8) with
        | (hit, collected) =>
          let cells := sortNats collected
          let sz := sz + cells.foldl (fun a c ↦ a + (pcen[c]! - c)) 0
          match splitCellsFrom cnt cells cells.size 0
              { lab := plab, pos := ppos, cst := pcst, cen := pcen, inW := pinW, tr,
                bc := sbc } with
          | st =>
            (⟨st.lab, st.pos, st.cst, st.cen, st.inW, st.tr,
              clearCntFrom touched touched.size 0 cnt,
              clearHitFrom cells cells.size 0 hit, st.bc,
              if cells.isEmpty then s + 1 else min (s + 1) cells[0]!⟩,
              ⟨pops + 1, sv, bumps, cl + cells.size, sz⟩)

open IsoGraph.Canon in
/-- The loop of `refineLoopAux`, with counters alongside. -/
def refineLoopS (G : Graph) : Nat → RState × (Nat × Nat × Nat × Nat × Nat) →
    RState × (Nat × Nat × Nat × Nat × Nat)
  | 0, r => r
  | fuel + 1, (r, cs) =>
    match firstSetFrom r.inW r.lo with
    | none => (r, cs)
    | some s =>
      if s < G.n && r.cst[s]! == s then
        refineLoopS G fuel (refineStepS G s ({ r with inW := r.inW.set! s false }, cs))
      else refineLoopS G fuel ({ r with inW := r.inW.set! s false, lo := s + 1 }, cs)

open IsoGraph.Canon in
/-- Counters for one initial refinement. -/
def initialRefineS (G : Graph) (cs : Nat × Nat × Nat × Nat × Nat) :
    Nat × Nat × Nat × Nat × Nat :=
  let p := Part.unit G.n
  let inW := if G.n == 0 then #[] else (Array.replicate G.n false).set! 0 true
  let sc := Scratch.empty G.n
  (refineLoopS G (G.n * G.n + G.n + 1)
    (⟨p.lab, p.pos, p.cst, p.cen, inW, hashSeed, sc.cnt, sc.hit, sc.bc, 0⟩, cs)).2

def refineStats (n : ℕ) : IO Unit := do
  let mut cs := (0, 0, 0, 0, 0)
  let mut cands := 0
  for c in enumCodesFast n do
    for s in keyMasks n c do
      cands := cands + 1
      cs := initialRefineS
        (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle (extendCode n c s))) cs
  let (pops, sv, bumps, cl, sz) := cs
  IO.println s!"initialRefine over {cands} candidates on {n+1} vertices, per candidate:"
  IO.println s!"  pops           {(pops * 100 / cands : Nat)}e-2"
  IO.println s!"  splitter verts {(sv * 100 / cands : Nat)}e-2"
  IO.println s!"  bumps          {(bumps * 100 / cands : Nat)}e-2"
  IO.println s!"  cells split    {(cl * 100 / cands : Nat)}e-2"
  IO.println s!"  their vertices {(sz * 100 / cands : Nat)}e-2"

/-- Not a time but a count: search-tree nodes over all the candidates of the last level. -/
def splitNodes (n : ℕ) : ℕ :=
  overCands n fun C ↦ (IsoGraph.Canon.canonical
    (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).nodes

/-! ### A/B harness for the search

The same trick as for the refinement, for the depth-first search on top of it: `canonicalP` is a
copy of `canonical` down to `pruneNode` and the two `dfs` functions, so a change to any of them can
be timed against the library's original in one file.

One candidate here is settled and gone: `pruneNode` used to compare `invPath` against a freshly
`extract`ed prefix of the incumbent's, and comparing against the prefix in place was worth 2-3 ms
of `nodes`' 366 at `n = 8`.  It is `lexCmpPre` in the library now. -/
section SearchAB
open IsoGraph.Canon

/-- Verbatim copy of `pruneNode`. -/
def pruneNodeP (invPath : Array UInt64) (st : St) : Option St :=
  match st.best with
  | none => some st
  | some b =>
    match lexCmpPre invPath b.invPath with
    | .lt => none
    | .gt => some { st with best := none }
    | .eq => some st

/-- Shared orbit cache for a node with no automorphisms to prune by: no generators, and a `mark`
that the `nGens != 0` guards below keep anyone from reading. -/
def noOrbits : Orbits := { nGens := 0, gens := Thunk.mk fun _ ↦ #[], mark := #[] }

/-- Verbatim copy of `leafUpdate`. -/
def leafUpdateP (G : Graph) (path : Array Nat) (invPath : Array UInt64) (lab : Array Nat)
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

/-! The branching rule is a parameter of the copy below: any isomorphism-invariant choice of a
non-singleton cell is correct, and which one is chosen decides the shape of the search tree.
`Part.targetCell` is the library's — the *first* non-singleton cell — and `targetCellQ` is the
candidate: a *smallest* one, leftmost among those, which is what `nauty` branches on. -/
/-- Scan the cells of a partition for a smallest non-singleton one, keeping the best start `bi`
and its size `bsz` (`0` while none has been seen). -/
def cenSmallFrom (cen : Array Nat) (n : Nat) : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, bi, bsz => if bsz == 0 then none else some bi
  | fuel + 1, i, bi, bsz =>
    if i ≥ n then (if bsz == 0 then none else some bi)
    else
      let sz := cen[i]! - i
      if sz > 1 && (bsz == 0 || sz < bsz) then cenSmallFrom cen n fuel cen[i]! i sz
      else cenSmallFrom cen n fuel cen[i]! bi bsz

@[inherit_doc cenSmallFrom]
def targetCellQ (p : Part) (n : Nat) : Option Nat := cenSmallFrom p.cen n n 0 0 0

mutual

/-- Copy of `dfsNode`, over a branching rule `tc` and an invariant pruning `pn`. -/
@[specialize] def dfsNodeG (tc : Part → Nat → Option Nat)
    (pn : Array UInt64 → St → Option St) (G : Graph) (fuel : Nat)
    (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St) : St :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    if st.abortTo.isSome then st else
    match pn invPath st with
    | none => st
    | some st =>
      let st := { st with nodes := st.nodes + 1 }
      match tc p G.n with
      | none => leafUpdateP G path invPath p.lab st
      | some c =>
        let orb : Orbits :=
          if st.autos.isEmpty then noOrbits
          else
            { nGens := st.autos.size, gens := Thunk.mk fun _ ↦ usableAutos st.autos path,
              mark := Array.replicate G.n false }
        dfsChildrenG tc pn G fuel path invPath p c p.cen[c]! #[] orb st
  termination_by (fuel, 0)

/-- Copy of `dfsChildren`, walking the target cell by position instead of over a list of it, and
skipping the orbit bookkeeping entirely while no automorphism is known. -/
@[specialize] def dfsChildrenG (tc : Part → Nat → Option Nat)
    (pn : Array UInt64 → St → Option St) (G : Graph) (fuel : Nat)
    (path : Array Nat) (invPath : Array UInt64) (p : Part) (k ec : Nat) (processed : Array Nat)
    (orb : Orbits) (st : St) : St :=
  if k ≥ ec then st
  else
    let v := p.lab[k]!
    if st.abortTo.isSome then st else
    let orb : Orbits :=
      if orb.nGens == st.autos.size then orb
      else
        let gens := usableAutos st.autos path
        { nGens := st.autos.size, gens := Thunk.mk fun _ ↦ gens,
          mark := orbitClosure G.n gens processed }
    if orb.nGens != 0 && orb.mark[v]! then
      dfsChildrenG tc pn G fuel path invPath p (k + 1) ec processed orb st
    else
      let (p', s) := individualize p v
      let inW := (Array.replicate G.n false).set! s true
      let (p'', tr) := refine G p' inW hashSeed
      let childInv := invPath.push (mix tr (p''.shapeHash G.n))
      let st := dfsNodeG tc pn G fuel (path.push v) childInv p'' st
      let st : St :=
        match st.abortTo with
        | some k => if k ≥ path.size then { st with abortTo := none } else st
        | none => st
      if st.abortTo.isSome then st
      else
        let orb : Orbits :=
          if orb.nGens == 0 then orb
          else { orb with mark := closureLoop orb.gens.get (G.n + 1) (orb.mark.set! v true) #[v] }
        dfsChildrenG tc pn G fuel path invPath p (k + 1) ec (processed.push v) orb st
  termination_by (fuel, ec - k + 1)

end

/-- Copy of `canonical`, over a branching rule and an invariant pruning. -/
@[specialize] def canonicalG (tc : Part → Nat → Option Nat)
    (pn : Array UInt64 → St → Option St) (G : Graph) : Result :=
  let (p, tr) := initialRefine G
  let inv0 : Array UInt64 := #[mix tr (p.shapeHash G.n)]
  let st := dfsNodeG tc pn G (G.n + 1) #[] inv0 p
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }
  match st.best with
  | none =>
    { lab := Array.range G.n, cert := certOf G (Array.range G.n), autos := #[], nodes := st.nodes }
  | some b => { lab := b.lab, cert := b.cert, autos := st.autos, nodes := st.nodes }

/-- The library's branching rule. -/
def canonicalP (G : Graph) : Result := canonicalG (fun p n ↦ p.targetCell n) pruneNodeP G

/-- The candidate branching rule. -/
def canonicalQ (G : Graph) : Result := canonicalG targetCellQ pruneNodeP G

end SearchAB

/-- Must agree with `nodes`, in value and in time. -/
def splitNodesP (n : ℕ) : ℕ :=
  overCands n fun C ↦ (canonicalP (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).nodes

/-- Search-tree nodes under the candidate branching rule.  The count is *meant* to differ; what
must not differ is `fullQ` below. -/
def splitNodesQ (n : ℕ) : ℕ :=
  overCands n fun C ↦ (canonicalQ (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).nodes

/-- The level, canonicalised by the copy with the library's branching rule: must be `full`. -/
def splitFullP (n : ℕ) : ℕ :=
  (dedupNat ((enumCodesFast n).flatMap fun c ↦ (keyMasks n c).map fun s ↦
    codeOfCert (n + 1)
      (canonicalP (IsoGraph.Canon.Graph.ofOracle (n + 1)
        (codeOracle (extendCode n c s)))).cert)).length

/-- The level, canonicalised by the copy with the candidate branching rule: must also be `full`,
though every individual canonical form may differ. -/
def splitFullQ (n : ℕ) : ℕ :=
  (dedupNat ((enumCodesFast n).flatMap fun c ↦ (keyMasks n c).map fun s ↦
    codeOfCert (n + 1)
      (canonicalQ (IsoGraph.Canon.Graph.ofOracle (n + 1)
        (codeOracle (extendCode n c s)))).cert)).length

/-- The certificate of every candidate, forced. -/
def someCert (n C : ℕ) : Array UInt64 :=
  (IsoGraph.Canon.canonical (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).cert

def splitCode (n : ℕ) : ℕ :=
  overCands n fun C ↦ codeOfAdj (n + 1) (IsoGraph.Canon.certGet (n + 1) (someCert n C)) % 1000003

def splitCodeFast (n : ℕ) : ℕ :=
  overCands n fun C ↦ codeOfCert (n + 1) (someCert n C) % 1000003

def splitCanonFin (n : ℕ) : ℕ :=
  overCands n fun C ↦ canonCode (n + 1) (graphOfCode (n + 1) C).Adj % 2

def splitCanon (n : ℕ) : ℕ := overCands n fun C ↦ canonOfCode (n + 1) C % 2

def splitFull (n : ℕ) : ℕ := (enumCodesFast (n + 1)).length

/-! ### How much of the search a cheap invariant would save

`--inv n` asks what the level would cost if the candidates were first separated by the trace hash
of their *initial* refinement.  That hash is an isomorphism invariant, so two candidates with
different hashes are already known to be non-isomorphic: only a group that shares a hash has to be
canonicalised, and a candidate alone in its group can be reported as it stands.  The report is the
number of candidates, of distinct hashes, of candidates alone in their group, and the DFS nodes the
groups that are left would still cost. -/

/-- Every candidate of the last level, with the trace hash of its initial refinement. -/
def candInvs (n : ℕ) : List (ℕ × ℕ) :=
  (enumCodesFast n).flatMap fun c ↦ (keyMasks n c).map fun s ↦
    let C := extendCode n c s
    (C, (IsoGraph.Canon.initialRefine
      (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).2.toNat)

/-- Fold a sorted list of keys into (groups, singletons, largest group). -/
def runStats : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ × ℕ × ℕ
  | _, run, gs, ss, mx, [] => (gs, ss + (if run == 1 then 1 else 0), max mx run)
  | prev, run, gs, ss, mx, y :: ys =>
    if y == prev then runStats prev (run + 1) gs ss mx ys
    else runStats y 1 (gs + 1) (ss + (if run == 1 then 1 else 0)) (max mx run) ys

def invReport (n : ℕ) : IO Unit := do
  let cands := candInvs n
  let hs := (cands.map (·.2)).mergeSort (· ≤ ·)
  let (gs, ss, mx) := match hs with
    | [] => (0, 0, 0)
    | h :: t => runStats h 1 1 0 0 t
  -- the nodes a canonicalisation of the whole level costs, and of the ambiguous groups only
  let nodesOf : ℕ → ℕ := fun C ↦ (IsoGraph.Canon.canonical
    (IsoGraph.Canon.Graph.ofOracle (n + 1) (codeOracle C))).nodes
  let dup : Std.HashMap ℕ ℕ := hs.foldl (fun m h ↦ m.insert h (m.getD h 0 + 1)) {}
  let allNodes := cands.foldl (fun a p ↦ a + nodesOf p.1) 0
  let ambNodes := cands.foldl (fun a p ↦ a + (if dup.getD p.2 0 > 1 then nodesOf p.1 else 0)) 0
  IO.println s!"initial-refinement invariant over the level of enumCodesFast {n+1}:"
  IO.println s!"  candidates    {cands.length}"
  IO.println s!"  distinct      {gs}"
  IO.println s!"  alone         {ss}"
  IO.println s!"  largest group {mx}"
  IO.println s!"  search nodes  {allNodes} all, {ambNodes} in the groups that are left"
  (← IO.getStdout).flush

/-! ### Where the connected level goes

`enumConnCodes 8` costs more than `enumCodesFast 8` does, for fewer graphs, so it gets the same
treatment: `--conn n` times the last step of `enumConnCodes (n+1)` in pieces.  The stage that is
not shared with the all-graphs enumerator is `masks`, which asks of every mask whether the new
vertex has least key among the non-cut vertices.  `degMsk` is the same scan with the coarser
least-degree rule, `tab` is the table of the parts of `G - u` that the stage builds once per parent
and then only reads, and `noBFS` is the floor, the same scan with the non-cut test deleted
altogether; the last two counts are wrong on purpose.  At `n = 7` the level splits as

    parents 33  autos +23  sym +18  masks +78  full +245

in milliseconds.  Of the 78, 33 build the tables and the rest is the key comparison and the reads.
The stage cost +48 with the least-degree rule, but then `full` cost +340: the key admits 12069
masks where the degree admits 17007.  It cost +166 when the non-cut test was a search per mask and
vertex guarded by a clique check, and +347 with neither.

Three other ways to cut the stage were measured and dropped; the timings are against the guarded
search that the table replaced:

* sorting the vertex table by ascending degree, so that `List.all` gives up sooner: 434 ms;
* skipping the search for a vertex of degree one, which the clique test already subsumed: 351 ms;
* skipping it as well for a vertex with a pendant neighbour, which *is* a cut vertex: 288 ms,
  worse than the clique test on its own. -/
def connParents (n : ℕ) : ℕ := (enumConnCodes n).length

def overConnParents (n : ℕ) (f : ℕ → ℕ) : ℕ := (enumConnCodes n).foldl (fun a c ↦ a + f c) 0

def connAutos (n : ℕ) : ℕ := overConnParents n fun c ↦ (autoPerms n (graphOfCode n c).Adj).length

def connSym (n : ℕ) : ℕ := overConnParents n fun c ↦ (symMasks n c).length

def connMasksN (n : ℕ) : ℕ := overConnParents n fun c ↦ (connMasks n c).length

/-- The degree test on its own, for the price of the finer key test that replaced it: the same
scan with the second digit of the key dropped.  The count is wrong on purpose. -/
def connDegMasksN (n : ℕ) : ℕ :=
  overConnParents n fun c ↦
    let tab := compTab n (rowsOfCode n c)
    let ds := (List.finRange n).map fun i ↦ (deg (graphOfCode n c).Adj i, i.1)
    ((symMasks n c).filter fun s ↦
      decide (s ≠ 0) &&
        (let m := maskCard n s
         ds.all fun d ↦ decide (m ≤ d.1 + (if s.testBit d.2 then 1 else 0))
           || !nonCutHitsFast n tab s d.2)).length

/-- The table of parts on its own, to price building it. -/
def connTabOnly (n : ℕ) : ℕ :=
  overConnParents n fun c ↦
    ((compTab n (rowsOfCode n c)).foldl (fun a r ↦ a + r.foldl (fun b m ↦ b + m) 0) 0) % 2

/-- The floor of the `masks` stage: the same scan with the connectivity search removed, so what is
left is the degree comparison.  The count is wrong on purpose. -/
def connNoBFS (n : ℕ) : ℕ :=
  overConnParents n fun c ↦
    let ds := (List.finRange n).map fun i ↦ (deg (graphOfCode n c).Adj i, i.1)
    ((symMasks n c).filter fun s ↦
      decide (s ≠ 0) &&
        (let m := maskCard n s
         ds.all fun d ↦ decide (m ≤ d.1 + (if s.testBit d.2 then 1 else 0)))).length

def connFull (n : ℕ) : ℕ := (enumConnCodes (n + 1)).length

def connSplit (n : ℕ) : IO Unit := do
  IO.println s!"enumConnCodes {n+1}, by stage:"
  for (lab, f) in [("parents", connParents), ("autos  ", connAutos), ("sym    ", connSym),
      ("masks  ", connMasksN), ("degMsk ", connDegMasksN), ("tab    ", connTabOnly),
      ("noBFS  ", connNoBFS), ("full   ", connFull)] do
    let t0 ← cpuNs
    let v := f n
    let v ← (if v == 0 then pure 0 else pure v)
    let t1 ← cpuNs
    IO.println s!"  {lab}  {v}  ({(t1 - t0 + 500000) / 1000000} ms)"
    (← IO.getStdout).flush

def split (n : ℕ) : IO Unit := do
  IO.println s!"enumCodesFast {n+1}, by stage:"
  for (lab, f) in [("parents ", splitParents), ("autoSrch", splitAutoSrch),
      ("autoConv", splitAutoConv), ("autos   ", splitAutos),
      ("symTriv ", splitSymTriv), ("symEarly", splitSymEarly), ("sym     ", splitSym),
      ("masks   ", splitMasks), ("key     ", splitKey), ("keyMul  ", splitKeyMul),
      ("sweep   ", splitSweep), ("sweepFin", splitSweepFin),
      ("sweepTrv", splitSweepTriv), ("refNull ", splitRefineNull),
      ("refineP ", splitRefineP), ("refine  ", splitRefine),
      ("nodesP  ", splitNodesP), ("nodesQ  ", splitNodesQ), ("nodes   ", splitNodes),
      ("code    ", splitCode), ("codeFast", splitCodeFast), ("canonFin", splitCanonFin),
      ("canon   ", splitCanon), ("fullP   ", splitFullP), ("fullQ   ", splitFullQ),
      ("full    ", splitFull)] do
    let t0 ← cpuNs
    let v := f n
    let v ← (if v == 0 then pure 0 else pure v)
    let t1 ← cpuNs
    IO.println s!"  {lab}  {v}  ({(t1 - t0 + 500000) / 1000000} ms)"
    (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let upTo := (args.filterMap String.toNat?).head?.getD 8
  let all := args.contains "--all"
  if args.contains "--split" then
    split upTo
    return 0
  if args.contains "--conn" then
    connSplit upTo
    return 0
  if args.contains "--stats" then
    refineStats upTo
    return 0
  if args.contains "--inv" then
    invReport upTo
    return 0
  -- `--only=fast|conn n`: run a single generator at a single `n`, for timing the process
  -- with an external CPU-time clock on a shared machine
  if let some a := args.find? (·.startsWith "--only=") then
    let f : Nat → Nat := match (a.drop 7).toString with
      | "conn" => fun n => (enumConnCodes n).length
      | _ => fun n => (enumCodesFast n).length
    IO.println s!"{f upTo}"
    return 0
  let mut ok ← run "enumCodesFast (extension + orbit reduction + least key):" upTo a000088
    fun n => (enumCodesFast n).length
  ok := (← run "enumConnCodes (connected only: + nonempty + least key among non-cut):"
    upTo a001349 fun n => (enumConnCodes n).length) && ok
  if all then
    ok := (← run "enumCodesSym (extension + orbit reduction):" 8 a000088
      fun n => (enumCodesSym n).length) && ok
    ok := (← run "enumCodesExt (extension only):" 8 a000088
      fun n => (enumCodesExt n).length) && ok
    ok := (← run "sweepCodes (brute-force sweep of all 2^(n choose 2) codes):" 7 a000088
      fun n => (sweepCodes n).length) && ok
  IO.println (if ok then "ALL COUNTS MATCH" else "*** SOME COUNTS WRONG ***")
  return (if ok then 0 else 1)
