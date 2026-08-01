import IsoGraph.Enumerate

/-!
Benchmark driver for the graph enumerators.

    lake exe enumbench          -- `enumerateFast` up to n = 8
    lake exe enumbench --naive  -- also the brute-force sweep, up to n = 7

Both must reproduce OEIS A000088, the number of graphs on `n` unlabelled vertices.
-/

open CGraph.Enum

/-- Number of graphs on `n` unlabelled vertices (OEIS A000088). -/
def a000088 : Array Nat := #[1, 1, 2, 4, 11, 34, 156, 1044, 12346, 274668]

def timeIt (label : String) (expect : Nat) (act : Unit → Nat) : IO Bool := do
  let t0 ← IO.monoMsNow
  let v := act ()
  -- force before reading the clock: `let v := …` on its own would leave a thunk
  let v ← (if v == 0 then pure 0 else pure v)
  let t1 ← IO.monoMsNow
  let ok := v == expect
  IO.println s!"  {label}  {v} classes  ({t1 - t0} ms){if ok then "" else s!"  *** expected {expect}"}"
  return ok

def main (args : List String) : IO UInt32 := do
  let naive := args.contains "--naive"
  let mut ok := true
  IO.println "enumerateFast (extend one vertex at a time):"
  for n in [0,1,2,3,4,5,6,7,8] do
    ok := (← timeIt s!"n={n}" a000088[n]! fun _ => (enumCodesFast n).length) && ok
  if naive then
    IO.println "enumCodes (brute-force sweep of all 2^(n choose 2) codes):"
    for n in [0,1,2,3,4,5,6,7] do
      ok := (← timeIt s!"n={n} (2^{Nat.choose n 2} codes)" a000088[n]!
        fun _ => (enumCodes n).length) && ok
  IO.println (if ok then "ALL COUNTS MATCH A000088" else "*** SOME COUNTS WRONG ***")
  return (if ok then 0 else 1)
