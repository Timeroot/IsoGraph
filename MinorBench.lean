import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Graphs.NamedGraphs

/-! Timing driver for the minor search: one case per invocation, named by the first argument,
with the sizes taken from the arguments after it —

```
minorbench kn-grid 5 4      -- is K5 a minor of the 4×4 grid?
```

Every size is read from `argv`, so the compiler can neither fold it away nor evaluate the case at
module-initialisation time — a `hide k n := n + 0 * k` wrapper does *not* survive the compiler,
and the whole run then happens before `main` starts, with every case reporting 0 ms.  The answer
is printed before the second clock reading so the work is not sunk past that one either.  Module
initialisation costs about 7 s on its own; the millisecond count excludes it. -/

open CGraph Backtrack NamedGraphs

def report (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findMinor H G rH rG with
  | some _ => "found"
  | none => "none "

def reportInd (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findInducedSubgraph H G rH rG with
  | some _ => "found"
  | none => "none "

/-- Every node of the induced-subgraph search tree, with no early exit: what the pruning is
actually worth, independently of how fast a node is. -/
partial def dfsCount {α β : Type} (cand : α → List (α × β) → List β) :
    List α → List (α × β) → ℕ
  | [], _ => 1
  | a :: todo, pre => 1 + ((cand a pre).map fun b => dfsCount cand todo ((a, b) :: pre)).sum

def nodes (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) (sym : Bool) : String :=
  let hs := searchOrder H rH.toList
  let prs := if sym then symPairs H hs else []
  toString (dfsCount (candList H G (hostRank G rG) prs (rowList G rG.toList) (adjTable G rG.toList))
    hs [])

def bench (name : String) (act : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.print s!"{name}: {act ()}"
  let t1 ← IO.monoMsNow
  IO.println s!"  ({t1 - t0} ms)"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let case := (args[0]?).getD "help"
  -- every size a case uses comes from here, so none of them is a compile-time constant
  let size (i d : ℕ) : ℕ := ((args[i]?).bind String.toNat?).getD d
  match case with
  | "cm-star" =>
    let m := size 1 3
    let n := size 2 12
    bench s!"C{m} ≼ star {n}" fun _ =>
      report (cycle m) (star n) (Roster.fin m) ((Roster.fin 1).sum (Roster.fin n))
  | "cm-cycle" =>
    let m := size 1 3
    let n := size 2 100
    bench s!"C{m} ≼ C{n}" fun _ => report (cycle m) (cycle n) (Roster.fin m) (Roster.fin n)
  | "km-kn" =>
    let m := size 1 5
    let n := size 2 6
    bench s!"K{m} ≼ K{n}" fun _ =>
      report (complete m) (complete n) (Roster.fin m) (Roster.fin n)
  | "km-heawood" =>
    let m := size 1 5
    bench s!"K{m} ≼ heawood" fun _ => report (complete m) heawood (Roster.fin m) (Roster.fin 14)
  | "kmm-heawood" =>
    let m := size 1 3
    bench s!"K{m},{m} ≼ heawood" fun _ =>
      report (bipartite m m) heawood ((Roster.fin m).sum (Roster.fin m)) (Roster.fin 14)
  | "km-mcgee" =>
    let m := size 1 5
    bench s!"K{m} ≼ mcgee" fun _ => report (complete m) mcgee (Roster.fin m) (Roster.fin 24)
  | "km-grid" =>
    let m := size 1 5
    let n := size 2 4
    bench s!"K{m} ≼ grid {n}x{n}" fun _ =>
      report (complete m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "kmm-grid" =>
    let m := size 1 3
    let n := size 2 4
    bench s!"K{m},{m} ≼ grid {n}x{n}" fun _ =>
      report (bipartite m m) (path n □g path n) ((Roster.fin m).sum (Roster.fin m))
        ((Roster.fin n).prod (Roster.fin n))
  | "km-cube" =>
    let m := size 1 5
    let n := size 2 4
    bench s!"K{m} ≼ Q{n}" fun _ =>
      report (complete m) (hypercube n) (Roster.fin m) (Roster.finArrow n Roster.bool)
  | "ind-empty-heawood" =>
    let m := size 1 7
    bench s!"E{m} ⊑ heawood" fun _ =>
      reportInd (empty m) heawood (Roster.fin m) (Roster.fin 14)
  | "ind-empty-mcgee" =>
    let m := size 1 8
    bench s!"E{m} ⊑ mcgee" fun _ => reportInd (empty m) mcgee (Roster.fin m) (Roster.fin 24)
  | "ind-empty-grid" =>
    let m := size 1 8
    let n := size 2 5
    bench s!"E{m} ⊑ grid {n}x{n}" fun _ =>
      reportInd (empty m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "ind-cycle-mcgee" =>
    let m := size 1 8
    bench s!"C{m} ⊑ mcgee" fun _ => reportInd (cycle m) mcgee (Roster.fin m) (Roster.fin 24)
  | "ind-path-grid" =>
    let m := size 1 8
    let n := size 2 5
    bench s!"P{m} ⊑ grid {n}x{n}" fun _ =>
      reportInd (path m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "ind-kmm-mcgee" =>
    let m := size 1 3
    bench s!"K{m},{m} ⊑ mcgee" fun _ =>
      reportInd (bipartite m m) mcgee ((Roster.fin m).sum (Roster.fin m)) (Roster.fin 24)
  | "nodes-empty-mcgee" =>
    let m := size 1 8
    let s := size 2 1
    bench s!"nodes E{m} ⊑ mcgee (sym {s})" fun _ =>
      nodes (empty m) mcgee (Roster.fin m) (Roster.fin 24) (s != 0)
  | "nodes-empty-heawood" =>
    let m := size 1 8
    let s := size 2 1
    bench s!"nodes E{m} ⊑ heawood (sym {s})" fun _ =>
      nodes (empty m) heawood (Roster.fin m) (Roster.fin 14) (s != 0)
  | "sym-empty" =>
    let m := size 1 8
    let H := empty m
    let hs := searchOrder H (Roster.fin m).toList
    IO.println s!"E{m}: classes {(twinClasses H hs).map List.length}, pairs {(symPairs H hs).length}"
  | _ =>
    IO.println "usage: minorbench <case> [sizes...]"
    IO.println "minor cases:   cm-star, cm-cycle, km-kn, km-heawood, kmm-heawood, km-mcgee,"
    IO.println "               km-grid, kmm-grid, km-cube"
    IO.println "induced cases: ind-empty-heawood, ind-empty-mcgee, ind-empty-grid,"
    IO.println "               ind-cycle-mcgee, ind-path-grid, ind-kmm-mcgee"
