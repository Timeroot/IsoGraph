import IsoGraph.Enumerate

/-!
Benchmark driver for the graph enumerators.

    lake exe enumbench          -- `enumCodesFast` up to n = 8
    lake exe enumbench --all    -- also the two weaker prunings, and the brute-force sweep
    lake exe enumbench 9        -- `enumCodesFast` up to n = 9 (minutes, and ~1 GB)

All of them must reproduce OEIS A000088, the number of graphs on `n` unlabelled vertices.
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
  (← IO.getStdout).flush
  return ok

def run (name : String) (upTo : Nat) (f : Nat → Nat) : IO Bool := do
  IO.println name
  let mut ok := true
  for n in List.range (upTo + 1) do
    ok := (← timeIt s!"n={n}" a000088[n]! fun _ => f n) && ok
  return ok

def main (args : List String) : IO UInt32 := do
  let upTo := (args.filterMap String.toNat?).head?.getD 8
  let all := args.contains "--all"
  let mut ok ← run "enumCodesFast (extension + orbit reduction + least degree):" upTo
    fun n => (enumCodesFast n).length
  if all then
    ok := (← run "enumCodesSym (extension + orbit reduction):" 8
      fun n => (enumCodesSym n).length) && ok
    ok := (← run "enumCodesExt (extension only):" 8 fun n => (enumCodesExt n).length) && ok
    ok := (← run "enumCodes (brute-force sweep of all 2^(n choose 2) codes):" 7
      fun n => (enumCodes n).length) && ok
  IO.println (if ok then "ALL COUNTS MATCH A000088" else "*** SOME COUNTS WRONG ***")
  return (if ok then 0 else 1)
