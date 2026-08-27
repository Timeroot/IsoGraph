import IsoGraph.Enum.Conn

/-!
Benchmark driver for the graph enumerators.

    lake exe enumbench          -- `enumCodesFast` and `enumConnCodes` up to n = 8
    lake exe enumbench --all    -- also the two weaker prunings, and the brute-force sweep
    lake exe enumbench 9        -- up to n = 9 (274668 graphs, ~4 minutes)

The all-graphs counts must reproduce OEIS A000088, the connected ones OEIS A001349.
-/

open CGraph.Enum

/-- Number of graphs on `n` unlabelled vertices (OEIS A000088). -/
def a000088 : Array Nat := #[1, 1, 2, 4, 11, 34, 156, 1044, 12346, 274668]

/-- Number of *connected* graphs on `n` unlabelled vertices (OEIS A001349), except that the empty
graph is not counted as connected here. -/
def a001349 : Array Nat := #[0, 1, 1, 2, 6, 21, 112, 853, 11117, 261080]

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

def main (args : List String) : IO UInt32 := do
  let upTo := (args.filterMap String.toNat?).head?.getD 8
  let all := args.contains "--all"
  -- `--only=fast|conn n`: run a single generator at a single `n`, for timing the process
  -- with an external CPU-time clock on a shared machine
  if let some a := args.find? (·.startsWith "--only=") then
    let f : Nat → Nat := match (a.drop 7).toString with
      | "conn" => fun n => (enumConnCodes n).length
      | _ => fun n => (enumCodesFast n).length
    IO.println s!"{f upTo}"
    return 0
  let mut ok ← run "enumCodesFast (extension + orbit reduction + least degree):" upTo a000088
    fun n => (enumCodesFast n).length
  ok := (← run "enumConnCodes (connected only: + nonempty + least degree among non-cut):"
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
