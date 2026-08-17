import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Graphs.Cache
import IsoGraph.Graphs.NamedGraphs
import IsoGraph.Invariants.Symmetry

/-! Head-to-head timing driver for `CGraph.cache`: every case runs the same computation twice,
once on the graph as it is defined and once on the graph with its adjacency matrix precomputed,
and prints both.

```
cachebench canon-tutte 3        -- three rounds, alternating plain and cached
```

The variants alternate inside one process, so a machine that speeds up or slows down during the
run does so for both of them.  Take the minimum over the rounds of each variant.

Two traps this file has to stay clear of.  The first is that a closed term is evaluated once, at
module initialisation, and never timed: the hosts built from an edge list therefore go through
`hostOfEdges`, whose list is bent through a number read from `argv`, and the `cycle`/`complete`
controls take their size from `argv` directly, so neither a graph nor its cache is a constant the
compiler can lift out.  The second is that the cache is built *inside* the timed thunk, so the
millisecond count of a `cached` line is the whole cost — filling the `n × n` array and then
running the search on it — and is directly comparable with the `plain` line above it. -/

open CGraph Backtrack NamedGraphs

/-- `ofEdges n es`, with the edge list routed through `k` so that the result is not a closed term.
`k % 1` is `0`, but the compiler does not know that. -/
def hostOfEdges (k n : ℕ) (es : List (ℕ × ℕ)) : CGraph := ofEdges n (es.drop (k % 1))

/-! ## What gets timed -/

/-- Force the canonical form: the number of ordered adjacent pairs of the canonical matrix. -/
def canonSum (G : CGraph) : String :=
  let c := G.canon
  let idx := List.finRange (Fintype.card G.V)
  toString ((idx.map fun a ↦ (idx.filter fun b ↦ c.adj a b).length).sum)

/-- Force the automorphism group: the number of generators the stabiliser chain produces. -/
def autCount (n : ℕ) (G : CGraph) (h : G.V = Fin n := by rfl) : String :=
  toString (IsoGraph.Canon.chainArrays n
    (fun i j ↦ G.Adj (cast h.symm i) (cast h.symm j))).size

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

def main (args : List String) : IO Unit := do
  let case := (args[0]?).getD "help"
  let size (i d : ℕ) : ℕ := ((args[i]?).bind String.toNat?).getD d
  -- the number of rounds doubles as the seed that keeps the hosts off the constant path
  let r := size 1 3
  match case with
  /- ### the canonical form -/
  | "canon-tutte" =>
    let G := hostOfEdges r 46 tutteEdges
    duel r "canon tutte" [("plain ", fun _ => canonSum G), ("cached", fun _ => canonSum (G.cache 46))]
  | "canon-mcgee" =>
    let G := hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
    duel r "canon mcgee" [("plain ", fun _ => canonSum G), ("cached", fun _ => canonSum (G.cache 24))]
  | "canon-balaban" =>
    let G := hostOfEdges r 70 (lcfEdges balabanCode 1)
    duel r "canon balaban10" [("plain ", fun _ => canonSum G),
      ("cached", fun _ => canonSum (G.cache 70))]
  | "canon-cycle" =>
    let n := size 2 46
    let G := cycle n
    duel r s!"canon C{n}" [("plain ", fun _ => canonSum G), ("cached", fun _ => canonSum (G.cache n))]
  | "canon-complete" =>
    let n := size 2 40
    let G := complete n
    duel r s!"canon K{n}" [("plain ", fun _ => canonSum G), ("cached", fun _ => canonSum (G.cache n))]
  /- ### the automorphism group -/
  | "aut-tutte" =>
    let G := hostOfEdges r 46 tutteEdges
    duel r "aut tutte" [("plain ", fun _ => autCount 46 G), ("cached", fun _ => autCount 46 (G.cache 46))]
  | "aut-balaban" =>
    let G := hostOfEdges r 70 (lcfEdges balabanCode 1)
    duel r "aut balaban10" [("plain ", fun _ => autCount 70 G),
      ("cached", fun _ => autCount 70 (G.cache 70))]
  | "aut-cycle" =>
    let n := size 2 46
    let G := cycle n
    duel r s!"aut C{n}" [("plain ", fun _ => autCount n G), ("cached", fun _ => autCount n (G.cache n))]
  /- ### containment, host side -/
  | "ind-empty-tutte" =>
    let m := size 2 12
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"E{m} ⊑ tutte"
      [("plain ", fun _ => reportInd (empty m) G (Roster.fin m) (Roster.fin 46)),
       ("cached", fun _ => reportInd (empty m) (G.cache 46) (Roster.fin m) (Roster.fin 46))]
  | "sub-cycle-tutte" =>
    let m := size 2 8
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} ⊆ tutte"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.fin 46)),
       ("cached", fun _ => reportSub (cycle m) (G.cache 46) (Roster.fin m) (Roster.fin 46))]
  | "km-tutte" =>
    let m := size 2 5
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"K{m} ≼ tutte"
      [("plain ", fun _ => report (complete m) G (Roster.fin m) (Roster.fin 46)),
       ("cached", fun _ => report (complete m) (G.cache 46) (Roster.fin m) (Roster.fin 46))]
  | "con-cycle-tutte" =>
    let m := size 2 4
    let G := hostOfEdges r 46 tutteEdges
    duel r s!"C{m} ⋏ tutte"
      [("plain ", fun _ => reportCon (cycle m) G (Roster.fin m) (Roster.fin 46)),
       ("cached", fun _ => reportCon (cycle m) (G.cache 46) (Roster.fin m) (Roster.fin 46))]
  | "sub-cycle-mcgee" =>
    let m := size 2 8
    let G := hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
    duel r s!"C{m} ⊆ mcgee"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.fin 24)),
       ("cached", fun _ => reportSub (cycle m) (G.cache 24) (Roster.fin m) (Roster.fin 24))]
  /- ### containment, both sides -/
  | "sub-petersen-tutte" =>
    let G := hostOfEdges r 46 tutteEdges
    let H := hostOfEdges r 10 (gpEdges 5 2)
    duel r "petersen ⊆ tutte"
      [("plain ", fun _ => reportSub H G (Roster.fin 10) (Roster.fin 46)),
       ("host  ", fun _ => reportSub H (G.cache 46) (Roster.fin 10) (Roster.fin 46)),
       ("pat   ", fun _ => reportSub (H.cache 10) G (Roster.fin 10) (Roster.fin 46)),
       ("both  ", fun _ => reportSub (H.cache 10) (G.cache 46) (Roster.fin 10) (Roster.fin 46))]
  | "con-self-mcgee" =>
    let G := hostOfEdges r 24 (lcfEdges [12, 7, -7] 8)
    duel r "mcgee ⋏ mcgee"
      [("plain ", fun _ => reportCon G G (Roster.fin 24) (Roster.fin 24)),
       ("both  ", fun _ => reportCon (G.cache 24) (G.cache 24) (Roster.fin 24) (Roster.fin 24))]
  /- ### controls: a host whose adjacency is already a formula -/
  | "sub-cycle-complete" =>
    let m := size 2 6
    let n := size 3 9
    let G := complete n
    duel r s!"C{m} ⊆ K{n}"
      [("plain ", fun _ => reportSub (cycle m) G (Roster.fin m) (Roster.fin n)),
       ("cached", fun _ => reportSub (cycle m) (G.cache n) (Roster.fin m) (Roster.fin n))]
  | "ind-empty-cycle" =>
    let m := size 2 10
    let n := size 3 40
    let G := cycle n
    duel r s!"E{m} ⊑ C{n}"
      [("plain ", fun _ => reportInd (empty m) G (Roster.fin m) (Roster.fin n)),
       ("cached", fun _ => reportInd (empty m) (G.cache n) (Roster.fin m) (Roster.fin n))]
  /- ### the cache on its own -/
  | "degsum" =>
    let G := hostOfEdges r 46 tutteEdges
    let sum (K : CGraph) (h : K.V = Fin 46) : String :=
      toString (((List.finRange 46).map fun i ↦
        ((List.finRange 46).filter fun j ↦ K.Adj (cast h.symm i) (cast h.symm j)).length).sum)
    duel r "degree sum of tutte"
      [("plain ", fun _ => sum G rfl), ("cached", fun _ => sum (G.cache 46) rfl)]
  | _ =>
    IO.println "usage: cachebench <case> [rounds] [sizes...]"
    IO.println "canon:   canon-tutte, canon-mcgee, canon-balaban, canon-cycle, canon-complete"
    IO.println "aut:     aut-tutte, aut-balaban, aut-cycle"
    IO.println "search:  ind-empty-tutte, sub-cycle-tutte, km-tutte, con-cycle-tutte,"
    IO.println "         sub-cycle-mcgee, sub-petersen-tutte, con-self-mcgee"
    IO.println "control: sub-cycle-complete, ind-empty-cycle"
    IO.println "cache:   degsum"
