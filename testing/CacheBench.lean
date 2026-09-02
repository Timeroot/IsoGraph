import IsoGraph.Containment.Algorithms.Cached
import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.Immersion
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Containment.Algorithms.TopMinor
import IsoGraph.Enum.All
import IsoGraph.Cache
import IsoGraph.SmallGraphs.Defs.Named
import IsoGraph.Invariants.Symmetry

/-! Head-to-head timing driver for the two ways of tabulating an adjacency matrix, and for the
`FinEnum` instances they are built on.

```
cachebench canon-tutte 3        -- three rounds, alternating the variants
cachebench kneser 3 10 5        -- three rounds on the Kneser graph K(10,5)
cachebench fe-subtype 3 10 5    -- the enumeration of its vertex type, fast against Mathlib's
```

Every case runs the same computation once per variant and prints all of them:

* `plain` — the graph as it is defined;
* `keep` — `CGraph.cache`, which tabulates but keeps the vertex type, so every query maps its two
  arguments through `FinEnum.equiv`;
* `fin` — `CGraph.cacheFin`, which relabels onto `Fin (FinEnum.card G.V)`, so a query is a bare
  array read but the answer has to be transported back along `CGraph.isoCacheFin`.

The variants alternate inside one process, so a machine that speeds up or slows down during the
run does so for all of them.  Take the minimum over the rounds of each variant.

Two traps this file has to stay clear of.  The first is that a closed term is evaluated once, at
module initialisation, and never timed: the hosts built from an edge list therefore go through
`hostOfEdges`, whose list is bent through a number read from `argv`, and the `cycle`/`complete`/
`kneser` cases take their size from `argv` directly, so neither a graph nor its cache is a
constant the compiler can lift out.  The second is that the cache is built *inside* the timed
thunk, so the millisecond count of a cached line is the whole cost — filling the `n × n` array and
then running the search on it — and is directly comparable with the `plain` line above it. -/

open CGraph Backtrack NamedGraphs

/-- `ofEdges n es`, with the edge list routed through `k` so that the result is not a closed term.
`k % 1` is `0`, but the compiler does not know that. -/
def hostOfEdges (k n : ℕ) (es : List (ℕ × ℕ)) : CGraph := ofEdges n (es.drop (k % 1))

/-! ## What gets timed -/

/-- Force the canonical form: the number of ordered adjacent pairs of the canonical matrix. -/
def canonSum (G : CGraph) : String :=
  let c := G.canon
  let idx := List.finRange (FinEnum.card G.V)
  toString ((idx.map fun a ↦ (idx.filter fun b ↦ c.adj a b).length).sum)

/-! ### Tabulating inside the canonical form

`CGraph.canonOfArray` tabulates the adjacency before it runs the search — `canonOfArrayTab`, a
`@[csimp]` implementation of it — so the search reads an array rather than calling `G.Adj`.  The
`raw` line below is the same computation written the way it ran before, straight off
`G.adjOfArray`; the `entry` line is `CGraph.canon`; the `full` line between them is the tabulated
search off a full `adjArray` rather than the half sweep it uses, so the three together separate
"tabulate at all" from "tabulate half".  The fill is inside the timed thunk, so all three are
directly comparable, and the gap between `raw` and `entry` is also the check that the `@[csimp]`
really fired. -/

/-- The number of ordered adjacent pairs of an adjacency matrix. -/
def matSum (n : ℕ) (c : IsoGraph.Canon.AdjMatrix n) : String :=
  let idx := List.finRange n
  toString ((idx.map fun a ↦ (idx.filter fun b ↦ c.adj a b).length).sum)

/-- The canonical form of `G` off the raw adjacency function: no `canonOfArray` in sight, so the
`@[csimp]` does not reach it. -/
def canonRaw (G : CGraph) : IsoGraph.Canon.AdjMatrix (FinEnum.card G.V) :=
  let a := (FinEnum.toList G.V).toArray
  (IsoGraph.Canon.canonMatrix a.size (G.adjOfArray a)).reindex (FinEnum.card G.V)

def canonRawSum (G : CGraph) : String := matSum _ (canonRaw G)

/-- Canonicalise the first `hi` labelled graphs on `n` vertices, and count those whose canonical
form has its first two vertices adjacent.  One query forces the whole search, so this times the
search and nothing else — on graphs small enough that the `n²` fill might not pay for itself. -/
def massRaw (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦ (canonRaw (Enum.graphOfCode n c)).get 0 1)

def massEntry (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦ (Enum.graphOfCode n c).canon.get 0 1)

/-- `massRaw` in pieces: what a canonicalisation of a six-vertex graph spends before the search
starts.  `oracle` is `Canon.Graph.ofOracle` — the `n²` sweep and the neighbour lists — and nothing
else; `refine` is that plus the initial refinement, which on a graph this small is most of what the
search does; the `raw` line of the case is the whole of it. -/
def massOracle (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦
    (IsoGraph.Canon.Graph.ofOracle n (Enum.codeOracle c)).nbr.size != n)

@[inherit_doc massOracle]
def massSetup (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦
    let G := IsoGraph.Canon.Graph.ofOracle n (Enum.codeOracle c)
    let p := IsoGraph.Canon.Part.unit G.n
    let sc := IsoGraph.Canon.Scratch.empty G.n
    p.lab[0]! + sc.cnt[0]! + sc.bc[0]! != 0)

@[inherit_doc massOracle]
def massRefine (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦
    (IsoGraph.Canon.initialRefine
      (IsoGraph.Canon.Graph.ofOracle n (Enum.codeOracle c))).1.lab[0]! != 0)

/-- The same sweep as `massOracle`, but reached the way `Enum.extendLevel` reaches it: through the
`Fin`-indexed `Adj` field of a `CGraph` and the `oracleOfFin` that unwraps it again.  The gap
between the two `oracle` lines is what that round trip costs per canonicalisation. -/
def massOracleFin (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦
    (IsoGraph.Canon.Graph.ofOracle n
      (IsoGraph.Canon.oracleOfFin n (Enum.graphOfCode n c).Adj)).nbr.size != n)

/-- The enumerator's own inner call, `Enum.canonOfCode`, against the composite it replaced:
`canonCode` of the `CGraph` read off a code, which reaches the search through `oracleOfFin`.  The
gap is the same round trip as between the two `oracle` lines, now measured through the whole
canonicalisation. -/
def massCodeFin (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦
    Enum.canonCode n (Enum.graphOfCode n c).Adj != 0)

@[inherit_doc massCodeFin]
def massCode (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦ Enum.canonOfCode n c != 0)

/-- `CGraph.canonOfArrayTab` written with the *full* fill, so the `full` lines below A/B the half
sweep against the sweep it replaced with everything after the fill held fixed. -/
def canonFull (G : CGraph) : IsoGraph.Canon.AdjMatrix (FinEnum.card G.V) :=
  let a := (FinEnum.toList G.V).toArray
  (IsoGraph.Canon.canonMatrix a.size
    (IsoGraph.Canon.matLookup a.size
      (IsoGraph.Canon.adjArray a.size (G.adjOfArray a)))).reindex (FinEnum.card G.V)

def canonFullSum (G : CGraph) : String := matSum _ (canonFull G)

def massFull (n hi : ℕ) : String :=
  toString ((List.range hi).countP fun c ↦ (canonFull (Enum.graphOfCode n c)).get 0 1)

/-- Force the automorphism group: the number of generators the stabiliser chain produces.  The
relabelling onto `Fin` is the one the enumeration supplies, so this runs on any vertex type. -/
def autCount (G : CGraph) : String :=
  let e := FinEnum.equiv (α := G.V)
  toString (IsoGraph.Canon.chainArrays (FinEnum.card G.V)
    (fun i j ↦ G.Adj (e.symm i) (e.symm j))).size

/-- The number of ordered adjacent pairs, read straight off the adjacency function: `n²` queries
and nothing else, so this is the purest measure of what a query costs. -/
def pairCount (G : CGraph) : String :=
  let vs := FinEnum.toList G.V
  toString ((vs.map fun a ↦ (vs.filter fun b ↦ G.Adj a b).length).sum)

/-- Force a filled matrix: the number of `true` entries.  The `fill` case below is the fill and
this count and nothing else, so it separates the sweep of the adjacency function from every search
that reads what it leaves. -/
def fillSum (a : Array (Array Bool)) : String :=
  toString (a.foldl (fun s r ↦ s + r.foldl (fun t b ↦ if b then t + 1 else t) 0) 0)

/-! ## Reading a coordinate of a function-typed vertex

A hypercube's vertices are the functions `Fin n → Bool`, and `FinEnum.instArrow` hands them out as
closures that decode one digit of the vertex's index.  Every adjacency query applies two of them
`n` times, so the `decode` case below times that one application, eight ways.  Everything here is
`Fin n → Bool` so that the arithmetic is the cheapest it can be and the overhead around it shows. -/

/-- What `FinEnum.instArrow`'s inverse used to be: `finFunctionFinEquiv` under `arrowCongr`, four
`Equiv`s deep, reading its digit by `Nat.pow`.  The `real` line is the same job through the current
instance, so the two together are the before-and-after of that change. -/
def decodeEquiv (n : ℕ) (i : Fin (FinEnum.card Bool ^ FinEnum.card (Fin n))) : Fin n → Bool :=
  ((Equiv.arrowCongr FinEnum.equiv FinEnum.equiv).trans finFunctionFinEquiv).symm i

/-- The digit by the power, which is the obvious way to write it. -/
def decodePow (n i : ℕ) : Fin n → Bool := fun j ↦ (i / 2 ^ (j : ℕ)) % 2 == 1

/-- The digit by descending, which is what `FinEnum.instArrow` does now. -/
def decodeDiv (n i : ℕ) : Fin n → Bool := fun j ↦
  (Nat.rec (motive := fun _ ↦ ℕ) i (fun _ v ↦ v / 2) (j : ℕ)) % 2 == 1

/-- The floor: the machine instruction, with no digit to reach. -/
def decodeShift (n i : ℕ) : Fin n → Bool := fun j ↦ (i >>> (j : ℕ)) % 2 == 1

/-- The shift with the `Equiv` back around it, which is what `FinEnum.instArrow` does now: the
digit is a `Fin (card β)` and the vertex's value is `equiv.symm` of it. -/
def decodeSymm (n i : ℕ) : Fin n → Bool := fun j ↦
  (FinEnum.equiv (α := Bool)).symm ⟨(i >>> (j : ℕ)) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The same, reading the `Equiv`'s inverse out of its field instead of building the reversed
`Equiv` to apply it.  `Equiv.symm` is a plain function that allocates. -/
def decodeInv (n i : ℕ) : Fin n → Bool := fun j ↦
  (FinEnum.equiv (α := Bool)).invFun ⟨(i >>> (j : ℕ)) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- A `Fin m → Bool` read out of a table.  Two arguments, so a partial application to the table
is a closure holding it — which is the point, and is not what happens: see `decodeTab`. -/
def tabFn {m : ℕ} (t : Array Bool) (j : Fin m) : Bool := t.getD (j : ℕ) false

/-- The same function with its `n` values computed once — or so it reads.  A `def` whose result
type is a function type is eta-expanded to full arity, so the table is rebuilt on every
application and this is the slowest line of the case by an order of magnitude.  Tabulating a
decode is not something a plain `def` can express. -/
def decodeTab (n i : ℕ) : Fin n → Bool :=
  tabFn (Array.ofFn fun j : Fin n ↦ (i / 2 ^ (j : ℕ)) % 2 == 1)

/-- How many elements `s` and `t` share, by building their intersection: what `kneser` and
`johnson` ask on every adjacency query. -/
def interFilter {n : ℕ} (s t : Finset (Fin n)) : ℕ := (s ∩ t).card

/-- The same number without the intersection, by counting the elements of `s` that lie in `t`. -/
def interCountP {n : ℕ} (s t : Finset (Fin n)) : ℕ := Multiset.countP (· ∈ t) s.val

/-- The same again, testing membership by counting rather than through `Decidable`. -/
def interCount {n : ℕ} (s t : Finset (Fin n)) : ℕ :=
  Multiset.countP (fun x ↦ t.val.count x ≠ 0) s.val

/-- Not the number but the question the Kneser graph asks: whether the two sets share an element
at all.  A bounded existential over a `Finset` gives up at the first one it finds. -/
def interMeets {n : ℕ} (s t : Finset (Fin n)) : Bool :=
  decide (∃ x ∈ s, t.val.count x ≠ 0)

/-- The Hamming distance of two bit-strings, by recursion on the index rather than over a
`List.finRange` built afresh on every query — `CGraph.hammingBelow`, but with an accumulator. -/
def hamming (n : ℕ) (x y : Fin n → Bool) : ℕ → ℕ → ℕ
  | 0, c => c
  | m + 1, c =>
    hamming n x y m (if h : m < n then (if x ⟨m, h⟩ != y ⟨m, h⟩ then c + 1 else c) else c)

/-- The same, abandoned once two differing coordinates have been seen.  A cube's adjacency only
ever asks whether the distance is one, and two bit-strings drawn at random answer that in four
coordinates rather than `n`. -/
def hammingCap (n : ℕ) (x y : Fin n → Bool) : ℕ → ℕ → ℕ
  | 0, c => c
  | m + 1, c =>
    if 2 ≤ c then c
    else hammingCap n x y m
      (if h : m < n then (if x ⟨m, h⟩ != y ⟨m, h⟩ then c + 1 else c) else c)

/-- Whether the two bit-strings differ everywhere below `m`, which is the folded cube's second
disjunct.  `&&` short-circuits, so this abandons at the first coordinate they share. -/
def hammingAll (n : ℕ) (x y : Fin n → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => (if h : m < n then x ⟨m, h⟩ != y ⟨m, h⟩ else false) && hammingAll n x y m

/-! ## The library entry points, before and after

`autCount`, `pairCount` and `fillSum` time the tabulation by hand.  These time the entry points
the library actually offers, each against the same computation written the way it was before:
`CGraph.autGens` and friends now tabulate the `Fin n` model themselves, and `CGraph.subgraphOf?`
and friends run the search on `cacheFin` copies of both graphs. -/

/-- The generators of the automorphism group, off the raw adjacency function — what `autGens` did
before it tabulated. -/
def autGensRaw (G : CGraph) : String :=
  toString (IsoGraph.Canon.autGens (FinEnum.card G.V)
    (G.finAdj (FinEnum.equiv (α := G.V)))).size

/-- The same, through the entry point, which tabulates. -/
def autGensTab (G : CGraph) : String :=
  toString (G.autGens (FinEnum.equiv (α := G.V))).size

def apiSub (H G : CGraph) : String :=
  match H.subgraphOf? G with | some _ => "found" | none => "none "

def apiInd (H G : CGraph) : String :=
  match H.inducedSubgraphOf? G with | some _ => "found" | none => "none "

def apiMinor (H G : CGraph) : String :=
  match H.minorOf? G with | some _ => "found" | none => "none "

def apiIndMinor (H G : CGraph) : String :=
  match H.inducedMinorOf? G with | some _ => "found" | none => "none "

def apiTop (H G : CGraph) : String :=
  match H.topMinorOf? G with | some _ => "found" | none => "none "

def apiImm (H G : CGraph) : String :=
  match H.immersionOf? G with | some _ => "found" | none => "none "

def apiCon (H G : CGraph) : String :=
  match H.contractionOf? G with | some _ => "found" | none => "none "

def apiHom (H G : CGraph) : String :=
  match H.homOf? G with | some _ => "found" | none => "none "

def apiQuot (H G : CGraph) : String :=
  match H.quotientOf? G with | some _ => "found" | none => "none "

def report (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findMinor H G rH rG with
  | some _ => "found"
  | none => "none "

def reportInd (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findInducedSubgraph H G rH rG with
  | some _ => "found"
  | none => "none "

def reportSub (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findSubgraph H G rH rG with
  | some _ => "found"
  | none => "none "

def reportIndMinor (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findInducedMinor H G rH rG with
  | some _ => "found"
  | none => "none "

def reportTop (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findTopMinor H G rH rG with
  | some _ => "found"
  | none => "none "

def reportImm (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findImmersion H G rH rG with
  | some _ => "found"
  | none => "none "

def reportCon (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findContraction H G rH rG with
  | some _ => "found"
  | none => "none "

def reportHom (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findHom H G rH rG (autData G rG []) with
  | some _ => "found"
  | none => "none "

def reportQuot (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findQuotient H G rH rG (autData H rH []) with
  | some _ => "found"
  | none => "none "

/-- The automorphisms `CGraph.homOf?` and `CGraph.quotientOf?` would break, for the `sym` half of
the A/B below; `[]` for the `nosym` half. -/
def benchAuts (G : CGraph) (cap : ℕ) : List (G.cacheFin ≃cg G.cacheFin) :=
  if cap == 0 then []
  else autClosure G.cacheFin (Roster.fin _) (G.cacheFin.autGens G.cacheFinEquiv).toList cap

/-- `CGraph.homOf?` with the host's symmetry breaking turned off or on, transport aside. -/
def reportHomSym (H G : CGraph) (cap : ℕ) : String :=
  let rG : Roster G.cacheFin.V := Roster.fin _
  match findHom H.cacheFin G.cacheFin (Roster.fin _) rG (autData _ rG (benchAuts G cap)) with
  | some _ => "found"
  | none => "none "

/-- `CGraph.quotientOf?` with the host's symmetry breaking turned off or on. -/
def reportQuotSym (H G : CGraph) (cap : ℕ) : String :=
  let rH : Roster H.cacheFin.V := Roster.fin _
  match findQuotient H.cacheFin G.cacheFin rH (Roster.fin _) (autData _ rH (benchAuts H cap)) with
  | some _ => "found"
  | none => "none "

partial def dfsCount {α β : Type} (cand : α → List (α × β) → List β) :
    List α → List (α × β) → ℕ
  | [], _ => 1
  | a :: todo, pre => 1 + ((cand a pre).map fun b => dfsCount cand todo ((a, b) :: pre)).sum

/-- Every node of the search tree `findQuotient H G` walks, given `auts` to prune by. -/
def nodesQuot (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) (auts : List (H ≃cg H)) :
    String :=
  let ad := autData H rH auts
  toString (dfsCount (homCandSym G H rH ad) (searchOrder G rG.toList) [])
    ++ s!" (|Aut| = {auts.length})"

/-! ## The enumerations themselves

`FinEnum.equiv` is what a `CGraph.cache` query pays twice, so it is worth timing on its own.  The
instance is passed explicitly, so the same code can be run against the fast instances of
`IsoGraph/ForMathlib/FinEnum.lean` and against Mathlib's. -/

/-- Round-trip every element of `α` through its index: the sum of `(equiv x).1` over the whole
type, plus a rebuild of each element from its index.  The instance argument is evaluated once, so
what this measures is the *query* cost, not the cost of building the enumeration. -/
def enumSum (α : Type) (e : FinEnum α) : String :=
  let l := @FinEnum.toList α e
  toString ((l.map fun x ↦ (@FinEnum.equiv α e x).1).sum)

section MathlibEnums

-- The four definitions below have a class as their type but are deliberately not instances: they
-- are the reference dictionaries the timings run against, handed to `enumSum` by hand.  Nothing
-- ever finds them by instance search, so the reducibility the linter asks for is immaterial.
set_option warn.classDefReducibility false

/-- The enumeration of `Fin n` that Mathlib supplies: a `List.finRange n` searched by `idxOf`. -/
def finEnumFinMathlib (n : ℕ) : FinEnum (Fin n) := @FinEnum.fin n

/-- Mathlib's enumeration of `Fin m × Fin n`, all the way down. -/
def finEnumProdMathlib (m n : ℕ) : FinEnum (Fin m × Fin n) :=
  @FinEnum.prod _ _ (@FinEnum.fin m) (@FinEnum.fin n)

/-- Mathlib's enumeration of `Fin m ⊕ Fin n`, all the way down. -/
def finEnumSumMathlib (m n : ℕ) : FinEnum (Fin m ⊕ Fin n) :=
  @FinEnum.sum _ _ (@FinEnum.fin m) (@FinEnum.fin n)

/-- Mathlib's enumeration of the vertex type of `kneser n k`: the `2ⁿ` subsets of `Fin n`, listed
and deduplicated, then filtered down to the ones of the right size. -/
def kneserEnumMathlib (n k : ℕ) : FinEnum {s : Finset (Fin n) // s.card = k} :=
  @FinEnum.Subtype.finEnum (Finset (Fin n)) (@FinEnum.Finset.finEnum (Fin n) (@FinEnum.fin n))
    (fun s ↦ s.card = k) (fun _ ↦ inferInstance)

end MathlibEnums

/-- `G` with its enumeration replaced.  The vertex type and the adjacency are untouched, so this
is the same graph; what changes is the index every algorithm reaches for.  This is how the fast
instances are put head to head with Mathlib's without rebuilding the library. -/
def withEnum (G : CGraph) (e : FinEnum G.V) : CGraph :=
  { V := G.V, enum := e, Adj := G.Adj, symm := G.symm, loopless := G.loopless }

/-! ## The driver -/

def bench (name : String) (act : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.print s!"{name}: {act ()}"
  let t1 ← IO.monoMsNow
  IO.println s!"  ({t1 - t0} ms)"
  (← IO.getStdout).flush

/-- Run every variant of a case, `r` times, in the order given. -/
def duel (r : ℕ) (name : String) (variants : List (String × (Unit → String))) : IO Unit := do
  for _ in [0:r] do
    for (lab, act) in variants do
      bench s!"{name} {lab}" act

/-- The three cache variants of one job on one graph. -/
def trio (r : ℕ) (name : String) (G : CGraph) (job : CGraph → String) : IO Unit :=
  duel r name
    [("plain ", fun _ => job G), ("keep  ", fun _ => job G.cache),
     ("fin   ", fun _ => job G.cacheFin)]

def main (args : List String) : IO Unit := do
  let case := (args[0]?).getD "help"
  let size (i d : ℕ) : ℕ := ((args[i]?).bind String.toNat?).getD d
  -- the number of rounds doubles as the seed that keeps the hosts off the constant path
  let r := size 1 3
  match case with
  /- ### the canonical form -/
  | "canon-tutte" => trio r "canon tutte" (hostOfEdges r 46 tutteEdges) canonSum
  | "canon-mcgee" => trio r "canon mcgee" (hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)) canonSum
  | "canon-balaban" =>
    trio r "canon balaban10" (hostOfEdges r 70 (lcfEdges balabanCode 1)) canonSum
  | "canon-cycle" =>
    let n := size 2 46
    trio r s!"canon C{n}" (cycle n) canonSum
  | "canon-complete" =>
    let n := size 2 40
    trio r s!"canon K{n}" (complete n) canonSum
  /- ### tabulating inside the canonical form -/
  | "canon-tab" =>
    let which := (args[2]?).getD "balaban"
    let G := match which with
      | "tutte" => hostOfEdges r 46 tutteEdges
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "cycle" => cycle (size 3 46)
      | "complete" => complete (size 3 40)
      | "kneser" => kneser (size 3 7) (size 4 3)
      | _ => hostOfEdges r 70 (lcfEdges balabanCode 1)
    duel r s!"canon {which}"
      [("raw   ", fun _ => canonRawSum G), ("full  ", fun _ => canonFullSum G),
       ("entry ", fun _ => canonSum G)]
  | "canon-mass" =>
    let n := size 2 6
    let hi := size 3 20000
    duel r s!"canon {hi} graphs on {n}"
      [("oracle", fun _ => massOracle n hi), ("oracFin", fun _ => massOracleFin n hi),
       ("setup ", fun _ => massSetup n hi), ("refine", fun _ => massRefine n hi),
       ("codeFin", fun _ => massCodeFin n hi), ("code  ", fun _ => massCode n hi),
       ("raw   ", fun _ => massRaw n hi), ("full  ", fun _ => massFull n hi),
       ("entry ", fun _ => massEntry n hi)]
  /- ### the automorphism group -/
  | "aut-tutte" => trio r "aut tutte" (hostOfEdges r 46 tutteEdges) autCount
  | "aut-balaban" => trio r "aut balaban10" (hostOfEdges r 70 (lcfEdges balabanCode 1)) autCount
  | "aut-cycle" =>
    let n := size 2 46
    trio r s!"aut C{n}" (cycle n) autCount
  /- ### containment, host side -/
  | "ind-empty-tutte" =>
    let m := size 2 12
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"E{m} ⊑ tutte"
      [("plain ", fun _ => reportInd (empty m) G (Roster.fin m) (Roster.fin 46)),
       ("keep  ", fun _ => reportInd (empty m) G.cache (Roster.fin m) (Roster.fin 46)),
       ("fin   ", fun _ => reportInd (empty m) G.cacheFin (Roster.fin m) (Roster.fin 46))]
  | "sub-cycle-tutte" =>
    let m := size 2 8
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} ⊆ tutte"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.fin 46)),
       ("keep  ", fun _ => reportSub (cycle m) G.cache (Roster.fin m) (Roster.fin 46)),
       ("fin   ", fun _ => reportSub (cycle m) G.cacheFin (Roster.fin m) (Roster.fin 46))]
  | "km-tutte" =>
    let m := size 2 5
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"K{m} ≼ tutte"
      [("plain ", fun _ => report (complete m) G (Roster.fin m) (Roster.fin 46)),
       ("keep  ", fun _ => report (complete m) G.cache (Roster.fin m) (Roster.fin 46)),
       ("fin   ", fun _ => report (complete m) G.cacheFin (Roster.fin m) (Roster.fin 46))]
  | "con-cycle-tutte" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} ⋏ tutte"
      [("plain ", fun _ => reportCon (cycle m) G (Roster.fin m) (Roster.fin 46)),
       ("keep  ", fun _ => reportCon (cycle m) G.cache (Roster.fin m) (Roster.fin 46)),
       ("fin   ", fun _ => reportCon (cycle m) G.cacheFin (Roster.fin m) (Roster.fin 46))]
  | "sub-cycle-mcgee" =>
    let m := size 2 8
    let G := hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
    duel r s!"C{m} ⊆ mcgee"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.fin 24)),
       ("keep  ", fun _ => reportSub (cycle m) G.cache (Roster.fin m) (Roster.fin 24)),
       ("fin   ", fun _ => reportSub (cycle m) G.cacheFin (Roster.fin m) (Roster.fin 24))]
  /- ### containment, both sides -/
  | "sub-petersen-tutte" =>
    let G := hostOfEdges r 46 tutteEdges
    let H := hostOfEdges r 10 (gpEdges 5 2)
    duel r "petersen ⊆ tutte"
      [("plain ", fun _ => reportSub H G (Roster.fin 10) (Roster.fin 46)),
       ("keep  ", fun _ => reportSub H.cache G.cache (Roster.fin 10) (Roster.fin 46)),
       ("fin   ", fun _ => reportSub H.cacheFin G.cacheFin (Roster.fin 10) (Roster.fin 46))]
  | "con-self-mcgee" =>
    let G := hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
    duel r "mcgee ⋏ mcgee"
      [("plain ", fun _ => reportCon G G (Roster.fin 24) (Roster.fin 24)),
       ("keep  ", fun _ => reportCon G.cache G.cache (Roster.fin 24) (Roster.fin 24)),
       ("fin   ", fun _ => reportCon G.cacheFin G.cacheFin (Roster.fin 24) (Roster.fin 24))]
  /- ### controls: a host whose adjacency is already a formula -/
  | "sub-cycle-complete" =>
    let m := size 2 6
    let n := size 3 9
    let G := complete n
    duel r s!"C{m} ⊆ K{n}"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.fin n)),
       ("keep  ", fun _ => reportSub (cycle m) G.cache (Roster.fin m) (Roster.fin n)),
       ("fin   ", fun _ => reportSub (cycle m) G.cacheFin (Roster.fin m) (Roster.fin n))]
  | "ind-empty-cycle" =>
    let m := size 2 10
    let n := size 3 40
    let G := cycle n
    duel r s!"E{m} ⊑ C{n}"
      [("plain ", fun _ => reportInd (empty m) G (Roster.fin m) (Roster.fin n)),
       ("keep  ", fun _ => reportInd (empty m) G.cache (Roster.fin m) (Roster.fin n)),
       ("fin   ", fun _ => reportInd (empty m) G.cacheFin (Roster.fin m) (Roster.fin n))]
  /- ### a vertex type that is not `Fin n` -/
  | "kneser" =>
    let n := size 2 10
    let k := size 3 5
    trio r s!"K({n},{k}) pairs" (kneser n k) pairCount
  | "kneser-canon" =>
    let n := size 2 10
    let k := size 3 5
    trio r s!"K({n},{k}) canon" (kneser n k) canonSum
  | "kneser-aut" =>
    let n := size 2 10
    let k := size 3 5
    trio r s!"K({n},{k}) aut" (kneser n k) autCount
  | "kneser-sub" =>
    let n := size 2 10
    let k := size 3 5
    let m := size 4 5
    let G := kneser n k
    duel r s!"C{m} ⊆ K({n},{k})"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.enum _)),
       ("keep  ", fun _ => reportSub (cycle m) G.cache (Roster.fin m) (Roster.enum _)),
       ("fin   ", fun _ => reportSub (cycle m) G.cacheFin (Roster.fin m) (Roster.enum _))]
  /- ### the same graph under the two enumerations -/
  | "kneser-enum" =>
    let n := size 2 10
    let k := size 3 5
    let G := kneser n k
    duel r s!"K({n},{k}) pairs"
      [("fast  ", fun _ => pairCount G),
       ("mathlib", fun _ => pairCount (withEnum G (kneserEnumMathlib n k))),
       ("fast/keep", fun _ => pairCount G.cache),
       ("mathlib/keep", fun _ => pairCount (withEnum G (kneserEnumMathlib n k)).cache),
       ("fast/fin", fun _ => pairCount G.cacheFin),
       ("mathlib/fin", fun _ => pairCount (withEnum G (kneserEnumMathlib n k)).cacheFin)]
  | "kneser-enum-canon" =>
    let n := size 2 10
    let k := size 3 5
    let G := kneser n k
    duel r s!"K({n},{k}) canon"
      [("fast  ", fun _ => canonSum G),
       ("mathlib", fun _ => canonSum (withEnum G (kneserEnumMathlib n k)))]
  /- ### the enumerations -/
  | "fe-fin" =>
    let n := size 2 2000
    duel r s!"enum Fin {n}"
      [("fast  ", fun _ => enumSum (Fin n) inferInstance),
       ("mathlib", fun _ => enumSum (Fin n) (finEnumFinMathlib n))]
  | "fe-prod" =>
    let n := size 2 60
    duel r s!"enum Fin {n} × Fin {n}"
      [("fast  ", fun _ => enumSum (Fin n × Fin n) inferInstance),
       ("mathlib", fun _ => enumSum (Fin n × Fin n) (finEnumProdMathlib n n))]
  | "fe-sum" =>
    let n := size 2 1000
    duel r s!"enum Fin {n} ⊕ Fin {n}"
      [("fast  ", fun _ => enumSum (Fin n ⊕ Fin n) inferInstance),
       ("mathlib", fun _ => enumSum (Fin n ⊕ Fin n) (finEnumSumMathlib n n))]
  | "fe-subtype" =>
    let n := size 2 10
    let k := size 3 5
    duel r s!"enum K({n},{k}) vertices"
      [("fast  ", fun _ => enumSum {s : Finset (Fin n) // s.card = k} inferInstance),
       ("mathlib", fun _ => enumSum {s : Finset (Fin n) // s.card = k} (kneserEnumMathlib n k))]
  | "fe-index" =>
    let n := size 2 10
    let k := size 3 5
    let V := {s : Finset (Fin n) // s.card = k}
    let vs := vertexArray V
    let each : (V → ℕ) → String := fun f ↦ Id.run do
      let mut acc := 0
      for _ in [0:vs.size] do
        for x in vs do
          acc := acc + f x
      return toString acc
    duel r s!"C({n},{k}) index"
      [("verts ", fun _ => toString vs.size),
       ("mask  ", fun _ => each fun s ↦ FinEnum.subsetMask s.1),
       ("shared", fun _ => let e : FinEnum V := inferInstance; each fun s ↦ (e.equiv s).1),
       ("equiv ", fun _ => each fun s ↦ (FinEnum.equiv s).1)]
  /- ### the library entry points, before and after -/
  | "api-aut" =>
    let which := (args[2]?).getD "tutte"
    let G := match which with
      | "balaban" => hostOfEdges r 70 (lcfEdges balabanCode 1)
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "kneser" => kneser (size 3 7) (size 4 3)
      | _ => hostOfEdges r 46 tutteEdges
    duel r s!"autGens {which}"
      [("raw   ", fun _ => autGensRaw G), ("entry ", fun _ => autGensTab G)]
  | "api-order" =>
    let which := (args[2]?).getD "tutte"
    let G := match which with
      | "balaban" => hostOfEdges r 70 (lcfEdges balabanCode 1)
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "kneser" => kneser (size 3 7) (size 4 3)
      | "cycle" => cycle (size 3 46)
      | _ => hostOfEdges r 46 tutteEdges
    duel r s!"autGroupOrder? {which}"
      [("raw   ", fun _ => toString (IsoGraph.Canon.autGroupOrder? (FinEnum.card G.V)
          (G.finAdj (FinEnum.equiv (α := G.V))) 100000)),
       ("entry ", fun _ => toString (G.autOrder? 100000))]
  | "api-vt" =>
    let which := (args[2]?).getD "tutte"
    let G := match which with
      | "balaban" => hostOfEdges r 70 (lcfEdges balabanCode 1)
      | "kneser" => kneser (size 3 7) (size 4 3)
      | _ => hostOfEdges r 46 tutteEdges
    duel r s!"vertexTransitiveB {which}"
      [("raw   ", fun _ => toString (IsoGraph.Canon.vertexTransitiveB (FinEnum.card G.V)
          (G.finAdj (FinEnum.equiv (α := G.V))))),
       ("canon ", fun _ => toString (G.canonicalize.vertexTransitiveBOfEquiv G.canonicalizeEquiv)),
       ("entry ", fun _ => toString G.vertexTransitiveB)]
  | "api-at" =>
    let which := (args[2]?).getD "heawood"
    let G := match which with
      | "balaban" => hostOfEdges r 70 (lcfEdges balabanCode 1)
      | "petersen" => gp 5 2
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "cycle" => cycle (size 3 46)
      | "kneser" => kneser (size 3 7) (size 4 3)
      | _ => hostOfEdges r 14 (lcfEdges [5, -5] 7)
    duel r s!"arcTransitiveB {which}"
      [("raw   ", fun _ => toString (IsoGraph.Canon.arcTransitiveB (FinEnum.card G.V)
          (G.finAdj (FinEnum.equiv (α := G.V))))),
       ("entry ", fun _ => toString G.arcTransitiveB)]
  | "api-sub" =>
    let m := size 2 8
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} ⊆ tutte"
      [("raw   ", fun _ => reportSub (cycle m) G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiSub (cycle m) G)]
  | "api-sub-kneser" =>
    let n := size 2 10
    let k := size 3 5
    let m := size 4 6
    let G := kneser n k
    duel r s!"C{m} ⊆ K({n},{k})"
      [("raw   ", fun _ => reportSub (cycle m) G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiSub (cycle m) G)]
  | "api-minor" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"K{m} ≼ tutte"
      [("raw   ", fun _ => report (complete m) G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiMinor (complete m) G)]
  | "api-indminor" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    let shape := (args[3]?).getD "cycle"
    let H := match shape with
      | "complete" => complete m
      | "petersen" => hostOfEdges r 10 (gpEdges 5 2)
      | _ => cycle m
    duel r s!"{shape} {m} induced minor of tutte"
      [("raw   ", fun _ => reportIndMinor H G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiIndMinor H G)]
  | "api-topminor" =>
    let which := (args[2]?).getD "petersen"
    let G := match which with
      | "heawood" => hostOfEdges r 14 (lcfEdges [5, -5] 7)
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "tutte" => hostOfEdges r 46 tutteEdges
      | _ => hostOfEdges r 10 (gpEdges 5 2)
    let shape := (args[3]?).getD "complete"
    let m := size 4 4
    let H := match shape with
      | "cycle" => cycle m
      | "petersen" => hostOfEdges r 10 (gpEdges 5 2)
      | _ => complete m
    duel r s!"{shape} {m} ≤ₜ {which}"
      [("raw   ", fun _ => reportTop H G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiTop H G)]
  | "api-immersion" =>
    let which := (args[2]?).getD "petersen"
    let G := match which with
      | "heawood" => hostOfEdges r 14 (lcfEdges [5, -5] 7)
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "tutte" => hostOfEdges r 46 tutteEdges
      | _ => hostOfEdges r 10 (gpEdges 5 2)
    let shape := (args[3]?).getD "complete"
    let m := size 4 4
    let H := match shape with
      | "cycle" => cycle m
      | "petersen" => hostOfEdges r 10 (gpEdges 5 2)
      | _ => complete m
    duel r s!"{shape} {m} immersed in {which}"
      [("raw   ", fun _ => reportImm H G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiImm H G)]
  | "api-con" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} ⋏ tutte"
      [("raw   ", fun _ => reportCon (cycle m) G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiCon (cycle m) G)]
  | "api-con-self" =>
    let G := hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
    duel r "mcgee ⋏ mcgee"
      [("raw   ", fun _ => reportCon G G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiCon G G)]
  | "api-hom" =>
    let which := (args[2]?).getD "petersen"
    let k := size 3 3
    let H := match which with
      | "tutte" => hostOfEdges r 46 tutteEdges
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "grotzsch" => grotzsch
      | _ => hostOfEdges r 10 (gpEdges 5 2)
    duel r s!"{which} → K{k}"
      [("raw   ", fun _ => reportHom H (complete k) (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiHom H (complete k))]
  | "api-quot" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} quotient of tutte"
      [("raw   ", fun _ => reportQuot (cycle m) G (Roster.enum _) (Roster.enum _)),
       ("entry ", fun _ => apiQuot (cycle m) G)]
  | "fill" =>
    let which := (args[2]?).getD "kneser"
    let G := match which with
      | "tutte" => hostOfEdges r 46 tutteEdges
      | "complete" => complete (size 3 60)
      | "cycle" => cycle (size 3 200)
      | "petersen" => hostOfEdges r 10 (gpEdges 5 2)
      | "hypercube" => hypercube (size 3 8)
      | "folded" => foldedCube (size 3 8)
      | "johnson" => johnson (size 3 10) (size 4 5)
      | "line" => lineGraph (hostOfEdges r 46 tutteEdges)
      | "paley" => paley (size 3 251)
      | "circulant" => circulant (size 3 252) [1, 2, 5]
      | "multipartite" => completeMultipartite (List.replicate (size 3 63) 4)
      | "strong" => cycle (size 3 16) ⊠g cycle (size 3 16)
      | "lex" => complete (size 3 16) ·g complete (size 3 16)
      | "mycielski" => mycielskian (hostOfEdges r 125 (cycleEdges 125))
      | _ => kneser (size 3 10) (size 4 5)
    duel r s!"fill {which}"
      [("full  ", fun _ => fillSum (adjArrayOn G.V G.Adj)),
       ("tri   ", fun _ => fillSum (adjArrayOnSymm G.V G.Adj))]
  | "decode" =>
    let n := size 2 8
    let card := 2 ^ n
    let ham : Array (Fin n → Bool) → String := fun vs ↦
      fillSum (Array.map (fun x ↦ vs.map fun y ↦ hamming n x y n 0 == 1) vs)
    duel r s!"Q{n} decode"
      [("real  ", fun _ => ham (vertexArray (Fin n → Bool))),
       ("equiv ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodeEquiv n i)),
       ("pow   ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodePow n i)),
       ("div   ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodeDiv n i)),
       ("shift ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodeShift n i)),
       ("symm  ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodeSymm n i)),
       ("inv   ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodeInv n i)),
       ("tab   ", fun _ => ham (Array.ofFn fun i : Fin card ↦ decodeTab n i))]
  | "cube-adj" =>
    let n := size 2 8
    let V := Fin n → Bool
    let one : V → V → Bool := fun x y ↦ if h : 0 < n then x ⟨0, h⟩ != y ⟨0, h⟩ else false
    let rng : V → V → Bool := fun _ _ ↦ (List.finRange n).length == 1
    let list : V → V → Bool := fun x y ↦ ((List.finRange n).countP fun i ↦ x i != y i) == 1
    let acc : V → V → Bool := fun x y ↦ hamming n x y n 0 == 1
    let cap : V → V → Bool := fun x y ↦ hammingCap n x y n 0 == 1
    let fold : V → V → Bool := fun x y ↦
      (n != 0) && (let d := hamming n x y n 0; (d == 1) || (d == n))
    let foldc : V → V → Bool := fun x y ↦
      (n != 0) && ((hammingCap n x y n 0 == 1) || hammingAll n x y n)
    duel r s!"Q{n} adjacency"
      [("verts ", fun _ => toString (vertexArray V).size),
       ("const ", fun _ => fillSum (adjArrayOnSymm V (fun _ _ ↦ true))),
       ("one   ", fun _ => fillSum (adjArrayOnSymm V one)),
       ("range ", fun _ => fillSum (adjArrayOnSymm V rng)),
       ("list  ", fun _ => fillSum (adjArrayOnSymm V list)),
       ("acc   ", fun _ => fillSum (adjArrayOnSymm V acc)),
       ("cap   ", fun _ => fillSum (adjArrayOnSymm V cap)),
       ("real  ", fun _ => fillSum (adjArrayOnSymm V (hypercube n).Adj)),
       ("fold  ", fun _ => fillSum (adjArrayOnSymm V fold)),
       ("foldc ", fun _ => fillSum (adjArrayOnSymm V foldc)),
       ("foldr ", fun _ => fillSum (adjArrayOnSymm V (foldedCube n).Adj))]
  | "set-adj" =>
    let n := size 2 10
    let k := size 3 5
    let V := {s : Finset (Fin n) // s.card = k}
    let filt : V → V → Bool := fun s t ↦ interFilter s.1 t.1 == 0
    let cntp : V → V → Bool := fun s t ↦ interCountP s.1 t.1 == 0
    let cnt : V → V → Bool := fun s t ↦ interCount s.1 t.1 == 0
    let mts : V → V → Bool := fun s t ↦ !interMeets s.1 t.1
    duel r s!"K({n},{k}) adjacency"
      [("verts ", fun _ => toString (vertexArray V).size),
       ("const ", fun _ => fillSum (adjArrayOnSymm V (fun _ _ ↦ true))),
       ("filter", fun _ => fillSum (adjArrayOnSymm V filt)),
       ("countP", fun _ => fillSum (adjArrayOnSymm V cntp)),
       ("count ", fun _ => fillSum (adjArrayOnSymm V cnt)),
       ("meets ", fun _ => fillSum (adjArrayOnSymm V mts)),
       ("real  ", fun _ => fillSum (adjArrayOnSymm V (kneser n k).Adj))]
  | "sym-quot" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} quotient of tutte"
      [("nosym ", fun _ => reportQuotSym (cycle m) G 0),
       ("sym   ", fun _ => reportQuotSym (cycle m) G (size 3 64))]
  | "sym-hom" =>
    let which := (args[2]?).getD "tutte"
    let k := size 3 3
    let H := match which with
      | "mcgee" => hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
      | "grotzsch" => grotzsch
      | "petersen" => hostOfEdges r 10 (gpEdges 5 2)
      | _ => hostOfEdges r 46 tutteEdges
    duel r s!"{which} → K{k}"
      [("nosym ", fun _ => reportHomSym H (complete k) 0),
       ("sym   ", fun _ => reportHomSym H (complete k) (size 4 64))]
  | "nodes-quot" =>
    let m := size 2 4
    let G := (hostOfEdges r 46 tutteEdges).cacheFin
    let H := (cycle m).cacheFin
    let rH : Roster H.V := Roster.fin (FinEnum.card H.V)
    let auts := if (args[3]?).getD "" == "sym" then
        autClosure H rH ((cycle m).cacheFin.autGens (cycle m).cacheFinEquiv).toList 64 else []
    bench s!"nodes C{m} quotient of tutte" fun _ =>
      nodesQuot H G rH (Roster.fin (FinEnum.card G.V)) auts
  | "nodes-quot-mcgee" =>
    let m := size 2 4
    let G := (hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)).cacheFin
    let H := (cycle m).cacheFin
    let rH : Roster H.V := Roster.fin (FinEnum.card H.V)
    let auts := if (args[3]?).getD "" == "sym" then
        autClosure H rH ((cycle m).cacheFin.autGens (cycle m).cacheFinEquiv).toList 64 else []
    bench s!"nodes C{m} quotient of mcgee" fun _ =>
      nodesQuot H G rH (Roster.fin (FinEnum.card G.V)) auts
  /- ### the cache on its own -/
  | "degsum" => trio r "degree sum of tutte" (hostOfEdges r 46 tutteEdges) pairCount
  | _ =>
    IO.println "usage: cachebench <case> [rounds] [sizes...]"
    IO.println "canon:   canon-tutte, canon-mcgee, canon-balaban, canon-cycle, canon-complete,"
    IO.println "         canon-tab <graph>, canon-mass <n> <count>"
    IO.println "aut:     aut-tutte, aut-balaban, aut-cycle"
    IO.println "search:  ind-empty-tutte, sub-cycle-tutte, km-tutte, con-cycle-tutte,"
    IO.println "         sub-cycle-mcgee, sub-petersen-tutte, con-self-mcgee"
    IO.println "control: sub-cycle-complete, ind-empty-cycle"
    IO.println "kneser:  kneser, kneser-canon, kneser-aut, kneser-sub,"
    IO.println "         kneser-enum, kneser-enum-canon"
    IO.println "finenum: fe-fin, fe-prod, fe-sum, fe-subtype, fe-index"
    IO.println "entry:   api-aut, api-order, api-vt, api-at, api-sub, api-sub-kneser, api-minor,"
    IO.println "         api-con, api-con-self, api-hom, api-quot, api-indminor, api-topminor,"
    IO.println "         api-immersion"
    IO.println "symmetry: sym-quot, sym-hom <graph> <k> <cap>, nodes-quot [sym],"
    IO.println "         nodes-quot-mcgee [sym]"
    IO.println "cache:   degsum, fill <graph>"
    IO.println "vertex:  decode, cube-adj, set-adj"
