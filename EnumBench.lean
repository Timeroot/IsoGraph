import IsoGraph.Enumerate

open CGraph.Enum

def timeIt (label : String) (act : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := act ()
  let v ← (if v == 0 then pure 0 else pure v)
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {v}  ({t1 - t0} ms)"

def main : IO Unit := do
  for n in [0,1,2,3,4,5,6,7] do
    timeIt s!"n={n} (2^{Nat.choose n 2} codes)" fun _ => (enumCodes n).length
