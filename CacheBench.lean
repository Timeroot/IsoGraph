import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Graphs.Cache
import IsoGraph.Graphs.NamedGraphs
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

def reportCon (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findContraction H G rH rG with
  | some _ => "found"
  | none => "none "

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
  /- ### the cache on its own -/
  | "degsum" => trio r "degree sum of tutte" (hostOfEdges r 46 tutteEdges) pairCount
  | _ =>
    IO.println "usage: cachebench <case> [rounds] [sizes...]"
    IO.println "canon:   canon-tutte, canon-mcgee, canon-balaban, canon-cycle, canon-complete"
    IO.println "aut:     aut-tutte, aut-balaban, aut-cycle"
    IO.println "search:  ind-empty-tutte, sub-cycle-tutte, km-tutte, con-cycle-tutte,"
    IO.println "         sub-cycle-mcgee, sub-petersen-tutte, con-self-mcgee"
    IO.println "control: sub-cycle-complete, ind-empty-cycle"
    IO.println "kneser:  kneser, kneser-canon, kneser-aut, kneser-sub,"
    IO.println "         kneser-enum, kneser-enum-canon"
    IO.println "finenum: fe-fin, fe-prod, fe-sum, fe-subtype"
    IO.println "cache:   degsum"
