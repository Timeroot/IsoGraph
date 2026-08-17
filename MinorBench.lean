import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Subgraph
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

def reportSub (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findSubgraph H G rH rG with
  | some _ => "found"
  | none => "none "

def reportCon (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  match findContraction H G rH rG with
  | some _ => "found"
  | none => "none "

/-- Every node of the induced-subgraph search tree, with no early exit: what the pruning is
actually worth, independently of how fast a node is. -/
partial def dfsCount {α β : Type} (cand : α → List (α × β) → List β) :
    List α → List (α × β) → ℕ
  | [], _ => 1
  | a :: todo, pre => 1 + ((cand a pre).map fun b => dfsCount cand todo ((a, b) :: pre)).sum

def nodes (H G : CGraph) (ind : Bool) (rH : Roster H.V) (rG : Roster G.V) (sym : Bool) : String :=
  let hs := searchOrder H rH.toList
  let prs := if sym then symPairs H hs else []
  toString (dfsCount (candList H G ind (hostRank G rG) rG.toList.length prs (rowList G rG.toList)
    (adjTable G rG.toList)) hs [])

/-- Every node of the minor search tree.  For a case that comes back `none` this is exactly the
tree the real search walks, so `ms / nodes` separates "too many nodes" from "each node is slow". -/
def nodesMinor (H G : CGraph) (rH : Roster H.V) (rG : Roster G.V) : String :=
  let hs := hsOrder H rH
  let gs := hostPool H G rH rG
  let init := MinorSearch.initState H G hs gs
  let cand := fun (_ : Unit) (pre : List (Unit × MinorSearch.State H G)) =>
    MinorSearch.candList H G (fun v => rG.toList.idxOf v) (symPairs H hs)
      (MinorSearch.headSt H G init pre)
  toString (dfsCount cand (List.replicate (gs.length + hs.length) ()) [])

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
  | "sub-cycle-mcgee" =>
    let m := size 1 8
    bench s!"C{m} ⊆ mcgee" fun _ => reportSub (cycle m) mcgee (Roster.fin m) (Roster.fin 24)
  | "sub-km-mcgee" =>
    let m := size 1 4
    bench s!"K{m} ⊆ mcgee" fun _ => reportSub (complete m) mcgee (Roster.fin m) (Roster.fin 24)
  | "sub-kmm-heawood" =>
    let m := size 1 3
    bench s!"K{m},{m} ⊆ heawood" fun _ =>
      reportSub (bipartite m m) heawood ((Roster.fin m).sum (Roster.fin m)) (Roster.fin 14)
  | "sub-cycle-grid" =>
    let m := size 1 8
    let n := size 2 5
    bench s!"C{m} ⊆ grid {n}x{n}" fun _ =>
      reportSub (cycle m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "sub-grid-grid" =>
    let a := size 1 3
    let n := size 2 5
    bench s!"grid {a}x{a} ⊆ grid {n}x{n}" fun _ =>
      reportSub (path a □g path a) (path n □g path n) ((Roster.fin a).prod (Roster.fin a))
        ((Roster.fin n).prod (Roster.fin n))
  | "sub-petersen-mcgee" =>
    bench "petersen ⊆ mcgee" fun _ => reportSub (gp 5 2) mcgee (Roster.fin 10) (Roster.fin 24)
  | "nodes-sub-cycle-mcgee" =>
    let m := size 1 8
    let s := size 2 1
    bench s!"nodes C{m} ⊆ mcgee (sym {s})" fun _ =>
      nodes (cycle m) mcgee false (Roster.fin m) (Roster.fin 24) (s != 0)
  | "nodes-empty-mcgee" =>
    let m := size 1 8
    let s := size 2 1
    bench s!"nodes E{m} ⊑ mcgee (sym {s})" fun _ =>
      nodes (empty m) mcgee true (Roster.fin m) (Roster.fin 24) (s != 0)
  | "nodes-empty-heawood" =>
    let m := size 1 8
    let s := size 2 1
    bench s!"nodes E{m} ⊑ heawood (sym {s})" fun _ =>
      nodes (empty m) heawood true (Roster.fin m) (Roster.fin 14) (s != 0)
  | "nodes-empty-grid" =>
    let m := size 1 8
    let n := size 2 5
    let s := size 3 1
    bench s!"nodes E{m} ⊑ grid {n}x{n} (sym {s})" fun _ =>
      nodes (empty m) (path n □g path n) true (Roster.fin m)
        ((Roster.fin n).prod (Roster.fin n)) (s != 0)
  | "nodes-km-grid" =>
    let m := size 1 5
    let n := size 2 4
    bench s!"nodes K{m} ≼ grid {n}x{n}" fun _ =>
      nodesMinor (complete m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "nodes-kmm-grid" =>
    let m := size 1 3
    let n := size 2 4
    bench s!"nodes K{m},{m} ≼ grid {n}x{n}" fun _ =>
      nodesMinor (bipartite m m) (path n □g path n) ((Roster.fin m).sum (Roster.fin m))
        ((Roster.fin n).prod (Roster.fin n))
  | "setup-grid" =>
    let n := size 1 5
    let G := path n □g path n
    let rG : Roster G.V := (Roster.fin n).prod (Roster.fin n)
    bench s!"setup grid {n}x{n}" fun _ =>
      toString ((rowList G rG.toList).length + (adjTable G rG.toList).length + G.E)
  | "micro-degree" =>
    let m := size 1 14
    let k := size 2 55447
    let H := empty m
    let vs : List H.V := (List.replicate (k / m + 1) (Roster.fin m).toList).flatten
    bench s!"{vs.length} × degree in E{m}" fun _ =>
      toString (vs.foldl (fun acc v => acc + H.toSimple.degree v) 0)
  | "micro-cand" =>
    let n := size 1 5
    let d := size 2 7
    let k := size 3 55447
    let m := size 4 14
    let H := empty m
    let G := path n □g path n
    let rG : Roster G.V := (Roster.fin n).prod (Roster.fin n)
    let gs := rG.toList
    let hs := searchOrder H (Roster.fin m).toList
    -- the even-indexed cells of an odd-side grid are an independent set
    let ev := gs.zipIdx.filterMap fun p => if p.2 % 2 == 0 then some p.1 else none
    let pre : List (H.V × G.V) := (hs.take d).zip ev
    let rs := rowList G gs
    let nb := adjTable G gs
    let prs := symPairs H hs
    match hs.drop d with
    | [] => IO.println "micro-cand: d past the end of the pattern"
    | a :: _ =>
      let work := List.replicate k (a, pre)
      bench s!"{k} × candList |pre|={pre.length}" fun _ =>
        toString (work.foldl (fun acc p =>
          acc + (candList H G true (hostRank G rG) gs.length prs rs nb p.1 p.2).length) 0)
  | "con-km-grid" =>
    let m := size 1 4
    let n := size 2 4
    bench s!"K{m} ⋏ grid {n}x{n}" fun _ =>
      reportCon (complete m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "con-path-grid" =>
    let m := size 1 4
    let n := size 2 4
    bench s!"P{m} ⋏ grid {n}x{n}" fun _ =>
      reportCon (path m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "con-cycle-grid" =>
    let m := size 1 4
    let n := size 2 4
    bench s!"C{m} ⋏ grid {n}x{n}" fun _ =>
      reportCon (cycle m) (path n □g path n) (Roster.fin m) ((Roster.fin n).prod (Roster.fin n))
  | "con-km-mcgee" =>
    let m := size 1 5
    bench s!"K{m} ⋏ mcgee" fun _ => reportCon (complete m) mcgee (Roster.fin m) (Roster.fin 24)
  | "con-cycle-mcgee" =>
    let m := size 1 6
    bench s!"C{m} ⋏ mcgee" fun _ => reportCon (cycle m) mcgee (Roster.fin m) (Roster.fin 24)
  | "con-cycle-heawood" =>
    let m := size 1 6
    bench s!"C{m} ⋏ heawood" fun _ => reportCon (cycle m) heawood (Roster.fin m) (Roster.fin 14)
  | "con-km-cube" =>
    let m := size 1 4
    let n := size 2 4
    bench s!"K{m} ⋏ Q{n}" fun _ =>
      reportCon (complete m) (hypercube n) (Roster.fin m) (Roster.finArrow n Roster.bool)
  | "con-self-mcgee" =>
    bench "mcgee ⋏ mcgee" fun _ => reportCon mcgee mcgee (Roster.fin 24) (Roster.fin 24)
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
    IO.println "contraction:   con-km-grid, con-path-grid, con-cycle-grid, con-km-mcgee,"
    IO.println "               con-cycle-mcgee, con-cycle-heawood, con-km-cube, con-self-mcgee"
    IO.println "subgraph:      sub-cycle-mcgee, sub-km-mcgee, sub-kmm-heawood, sub-cycle-grid,"
    IO.println "               sub-grid-grid, sub-petersen-mcgee"
    IO.println "node counts:   nodes-empty-mcgee, nodes-empty-heawood, nodes-empty-grid,"
    IO.println "               nodes-km-grid, nodes-kmm-grid, nodes-sub-cycle-mcgee"
