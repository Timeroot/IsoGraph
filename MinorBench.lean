import IsoGraph.Containment.Algorithms.Minor
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
  | _ =>
    IO.println "usage: minorbench <case> [sizes...]"
    IO.println "cases: cm-star, cm-cycle, km-kn, km-heawood, kmm-heawood, km-mcgee,"
    IO.println "       km-grid, kmm-grid, km-cube"
