import IsoGraph.Canon.Algorithm
import Std.Data.HashSet

/-!
Test / benchmark driver for `IsoGraph.Canon.canonical`.

    lake exe isobench           -- standard suite
    lake exe isobench --deep    -- also enumerate all 2^21 graphs on 7 vertices

The strongest test here is `countClasses`: it canonicalises *every* labelled graph on `n`
vertices and counts the distinct canonical forms.  That number equals the number of isomorphism
classes (OEIS A000088) exactly when the canonical form is both isomorphism-invariant (`≤`) and
complete (`≥`), so a match certifies both directions at once.
-/

open IsoGraph.Canon

/-! ## A tiny deterministic PRNG (xorshift64*) -/

structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.of (seed : Nat) : Rng := ⟨UInt64.ofNat seed ^^^ 88172645463325252⟩

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x * 2685821657736338717, ⟨x⟩)

/-- Uniform in `[0, m)` (slight modulo bias, irrelevant here). -/
def Rng.upto (r : Rng) (m : Nat) : Nat × Rng :=
  let (x, r) := r.next
  ((x >>> 11).toNat % (max m 1), r)

/-- A uniformly random permutation of `{0, …, n-1}` (Fisher–Yates). -/
def randPerm (n : Nat) (r : Rng) : Array Nat × Rng := Id.run do
  let mut a := Array.range n
  let mut r := r
  let mut i := n
  while i > 1 do
    i := i - 1
    let (j, r') := r.upto (i + 1)
    r := r'
    let ai := a[i]!
    a := a.set! i a[j]!
    a := a.set! j ai
  return (a, r)

/-! ## Graph constructions -/

/-- Build a loopless graph from a symmetric predicate. -/
def mkGraph (n : Nat) (f : Nat → Nat → Bool) : Graph :=
  Graph.ofOracle n fun v w => v != w && f v w

/-- Relabel `G` by `π`: the new vertex `π[v]` plays the role of the old vertex `v`. -/
def permuteGraph (G : Graph) (π : Array Nat) : Graph := Id.run do
  let mut inv := Array.replicate G.n 0
  for v in [0:G.n] do
    inv := inv.set! π[v]! v
  return mkGraph G.n fun a b => G.adj[inv[a]!]![inv[b]!]!

def randomGraph (n : Nat) (pPercent : Nat) (seed : Nat) : Graph := Id.run do
  let mut r := Rng.of seed
  let mut m : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for v in [0:n] do
    for w in [v+1:n] do
      let (x, r') := r.upto 100
      r := r'
      if x < pPercent then
        m := m.set! v (m[v]!.set! w true)
        m := m.set! w (m[w]!.set! v true)
  return mkGraph n fun a b => m[a]![b]!

/-- A uniformly-ish random `d`-regular graph via repeated pairing (retries on failure). -/
def randomRegular (n d seed : Nat) : Graph := Id.run do
  let mut r := Rng.of seed
  let mut attempt := 0
  while attempt < 500 do
    attempt := attempt + 1
    let mut stubs : Array Nat := #[]
    for v in [0:n] do
      for _ in [0:d] do
        stubs := stubs.push v
    let (π, r') := randPerm stubs.size r
    r := r'
    let mut perm : Array Nat := Array.replicate stubs.size 0
    for i in [0:stubs.size] do
      perm := perm.set! π[i]! stubs[i]!
    let mut m : Array (Array Bool) := Array.replicate n (Array.replicate n false)
    let mut ok := true
    let mut i := 0
    while i + 1 < perm.size do
      let a := perm[i]!
      let b := perm[i+1]!
      if a == b || m[a]![b]! then ok := false
      else
        m := m.set! a (m[a]!.set! b true)
        m := m.set! b (m[b]!.set! a true)
      i := i + 2
    if ok then
      return mkGraph n fun x y => m[x]![y]!
  return mkGraph n fun _ _ => false

/-- A uniformly random labelled tree, via a random Prüfer sequence. -/
def randomTree (n seed : Nat) : Graph := Id.run do
  if n ≤ 1 then return mkGraph n fun _ _ => false
  let mut r := Rng.of seed
  let mut code : Array Nat := #[]
  for _ in [0:n-2] do
    let (x, r') := r.upto n
    r := r'
    code := code.push x
  let mut deg : Array Nat := Array.replicate n 1
  for c in code do
    deg := deg.modify c (· + 1)
  let mut m : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  let mut leafPtr := 0
  let mut leaf := 0
  -- smallest leaf
  for i in [0:n] do
    if deg[i]! == 1 then leafPtr := i; leaf := i; break
  for c in code do
    m := m.set! leaf (m[leaf]!.set! c true)
    m := m.set! c (m[c]!.set! leaf true)
    deg := deg.modify c (· - 1)
    if deg[c]! == 1 && c < leafPtr then
      leaf := c
    else
      deg := deg.modify leaf (· - 1)
      let mut j := leafPtr + 1
      while j < n && deg[j]! != 1 do
        j := j + 1
      leafPtr := j
      leaf := j
  -- join the last two remaining
  let mut rest : Array Nat := #[]
  for i in [0:n] do
    if deg[i]! == 1 then rest := rest.push i
  if rest.size ≥ 2 then
    let a := rest[0]!
    let b := rest[rest.size - 1]!
    m := m.set! a (m[a]!.set! b true)
    m := m.set! b (m[b]!.set! a true)
  return mkGraph n fun a b => m[a]![b]!

def completeGraph (n : Nat) : Graph := mkGraph n fun _ _ => true
def emptyGraph (n : Nat) : Graph := mkGraph n fun _ _ => false
def cycleGraph (n : Nat) : Graph :=
  mkGraph n fun a b => (a + 1) % n == b || (b + 1) % n == a
def pathGraph (n : Nat) : Graph :=
  mkGraph n fun a b => a + 1 == b || b + 1 == a

/-- Disjoint union of `k` copies of `Kₘ`. -/
def disjointCliques (k m : Nat) : Graph :=
  mkGraph (k * m) fun a b => a / m == b / m

/-- Disjoint union of `k` copies of `G`. -/
def disjointCopies (k : Nat) (G : Graph) : Graph :=
  mkGraph (k * G.n) fun a b => a / G.n == b / G.n && G.adj[a % G.n]![b % G.n]!

/-- The `d`-dimensional hypercube. -/
def hypercube (d : Nat) : Graph :=
  mkGraph (2 ^ d) fun a b =>
    let x := a ^^^ b
    x != 0 && x &&& (x - 1) == 0

/-- The Kneser graph `K(n, k)`, on `k`-subsets of `{0,…,n-1}` encoded as bitmasks. -/
def kneser (n k : Nat) : Graph := Id.run do
  let mut sets : Array Nat := #[]
  for m in [0:2 ^ n] do
    let mut pc := 0
    for i in [0:n] do
      if m >>> i &&& 1 == 1 then pc := pc + 1
    if pc == k then sets := sets.push m
  return mkGraph sets.size fun a b => sets[a]! &&& sets[b]! == 0

/-- The Johnson graph `J(n, k)`: `k`-subsets meeting in `k-1` points. -/
def johnson (n k : Nat) : Graph := Id.run do
  let mut sets : Array Nat := #[]
  for m in [0:2 ^ n] do
    let mut pc := 0
    for i in [0:n] do
      if m >>> i &&& 1 == 1 then pc := pc + 1
    if pc == k then sets := sets.push m
  return mkGraph sets.size fun a b => Id.run do
    let x := sets[a]! &&& sets[b]!
    let mut pc := 0
    for i in [0:n] do
      if x >>> i &&& 1 == 1 then pc := pc + 1
    return pc + 1 == k

def completeBipartite (m n : Nat) : Graph :=
  mkGraph (m + n) fun a b => (a < m) != (b < m)

/-- Rook's graph `m × n`: cells of a grid, adjacent iff in the same row or column. -/
def rook (m n : Nat) : Graph :=
  mkGraph (m * n) fun a b => a / n == b / n || a % n == b % n

/-- The Paley graph on `q` vertices (`q` a prime ≡ 1 mod 4): `a ~ b` iff `a - b` is a square. -/
def paley (q : Nat) : Graph := Id.run do
  let mut sq : Array Bool := Array.replicate q false
  for i in [0:q] do
    sq := sq.set! (i * i % q) true
  return mkGraph q fun a b => sq[(a + q - b) % q]!

/-- The Shrikhande graph: cospectral with, but not isomorphic to, the `4 × 4` rook's graph. -/
def shrikhande : Graph :=
  mkGraph 16 fun a b =>
    let dx := (a / 4 + 4 - b / 4) % 4
    let dy := (a % 4 + 4 - b % 4) % 4
    (dx == 0 && (dy == 1 || dy == 3)) || (dy == 0 && (dx == 1 || dx == 3)) ||
      (dx == 1 && dy == 1) || (dx == 3 && dy == 3)

/-! ## Checking -/

def certToString (c : Array UInt64) : String :=
  c.foldl (fun s x => s ++ toString x ++ ",") ""

/-- Pack a canonical form on `n ≤ 8` vertices into a single `UInt64`.

For `n ≤ 64` a certificate has one word per row and the row's bits occupy the *top* `n` bits of
that word, so each row contributes `n` bits once shifted down. -/
def packCert (n : Nat) (c : Array UInt64) : UInt64 :=
  c.foldl (fun acc w => acc * UInt64.ofNat (2 ^ n) + (w >>> UInt64.ofNat (64 - n))) 0

/-- Is `lab` a permutation of `{0,…,n-1}`? -/
def isPerm (n : Nat) (lab : Array Nat) : Bool := Id.run do
  if lab.size != n then return false
  let mut seen := Array.replicate n false
  for v in lab do
    if v ≥ n || seen[v]! then return false
    seen := seen.set! v true
  return true

/-- Does `certOf G lab` really equal the reported certificate? -/
def certConsistent (G : Graph) (res : Result) : Bool :=
  lexCmpU64 (certOf G res.lab) res.cert == .eq

/-- Check that every returned generator really is an automorphism. -/
def autosValid (G : Graph) (res : Result) : Bool := Id.run do
  for g in res.autos do
    if !isPerm G.n g then return false
    for v in [0:G.n] do
      for w in [0:G.n] do
        if G.adj[v]![w]! != G.adj[g[v]!]![g[w]!]! then return false
  return true

/-- Best-of-`reps` timing of `f`, in microseconds, together with the sum of the results.

Timing pure code in Lean needs two barriers, or the compiler silently moves the work outside the
measured window: `IO.lazyPure` keeps the evaluation inside the `IO` sequence (a plain `let` is
sunk past the second clock read), and taking the argument from `xs` at the loop index keeps the
closure from being lifted out of the loop (a closed closure body is hoisted to its creation
site). -/
def timeBest {α : Type} [Inhabited α] (reps : Nat) (xs : Array α) (f : α → Nat) :
    IO (Nat × Nat) := do
  let mut best := 1 <<< 62
  let mut sink := 0
  for k in [0:max reps 1] do
    let t0 ← IO.monoNanosNow
    let v ← IO.lazyPure fun _ => f xs[k % xs.size]!
    sink := sink + v
    let t1 ← IO.monoNanosNow
    best := min best ((t1 - t0) / 1000)
  return (best, sink)

/-- Render microseconds as milliseconds with three decimals. -/
def showMs (us : Nat) : String :=
  let fr := toString (us % 1000)
  s!"{us / 1000}.{"".pushn '0' (3 - min 3 fr.length) ++ fr}ms"

structure Report where
  name : String
  n : Nat
  edges : Nat
  nodes : Nat
  gens : Nat
  us : Nat
  ok : Bool
  msg : String

/-- Canonicalise `G` and `trials` random relabellings of it; all certificates must agree. -/
def checkGraph (name : String) (G : Graph) (trials : Nat) (seed : Nat) : IO Report := do
  let (us, _) ← timeBest 1 #[G] fun G => (canonical G).nodes
  let res := canonical G
  let mut ok := true
  let mut msg := ""
  if !isPerm G.n res.lab then
    ok := false; msg := "labelling is not a permutation"
  if ok && !certConsistent G res then
    ok := false; msg := "reported certificate disagrees with certOf"
  if ok && !autosValid G res then
    ok := false; msg := "a returned generator is not an automorphism"
  let mut r := Rng.of seed
  let mut maxNodes := res.nodes
  for _ in [0:trials] do
    if !ok then break
    let (π, r') := randPerm G.n r
    r := r'
    let H := permuteGraph G π
    let resH := canonical H
    maxNodes := max maxNodes resH.nodes
    if !isPerm H.n resH.lab then
      ok := false; msg := "relabelled: labelling is not a permutation"
    else if !certConsistent H resH then
      ok := false; msg := "relabelled: certificate disagrees with certOf"
    else if lexCmpU64 res.cert resH.cert != .eq then
      ok := false; msg := "canonical form is NOT isomorphism-invariant"
  return { name, n := G.n, edges := G.edgeCount, nodes := maxNodes, gens := res.autos.size,
           us, ok, msg }

def pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - min w s.length)

def Report.render (r : Report) : String :=
  s!"{pad r.name 22} n={pad (toString r.n) 5} m={pad (toString r.edges) 6} " ++
  s!"nodes={pad (toString r.nodes) 7} gens={pad (toString r.gens) 4} " ++
  s!"{pad (showMs r.us) 12} " ++
  (if r.ok then "OK" else "FAIL: " ++ r.msg)

/-! ## Exhaustive test: count isomorphism classes -/

/-- The unordered pairs of `{0,…,n-1}`. -/
def pairsOf (n : Nat) : Array (Nat × Nat) := Id.run do
  let mut ps := #[]
  for a in [0:n] do
    for b in [a+1:n] do
      ps := ps.push (a, b)
  return ps

/-- The graph on `n` vertices whose edge set is given by the bits of `mask`. -/
def graphOfMask (n : Nat) (ps : Array (Nat × Nat)) (mask : Nat) : Graph := Id.run do
  let mut m : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for i in [0:ps.size] do
    if mask >>> i &&& 1 == 1 then
      let (a, b) := ps[i]!
      m := m.set! a (m[a]!.set! b true)
      m := m.set! b (m[b]!.set! a true)
  return mkGraph n fun a b => m[a]![b]!

/-- Number of distinct canonical forms over all `2^C(n,2)` labelled graphs on `n` vertices. -/
def countClasses (n : Nat) : Nat := Id.run do
  let ps := pairsOf n
  let mut seen : Std.HashSet UInt64 := ∅
  for mask in [0:2 ^ ps.size] do
    let G := graphOfMask n ps mask
    seen := seen.insert (packCert n (canonicalForm G))
  return seen.size

/-- Number of isomorphism classes of simple graphs on `n` vertices (OEIS A000088). -/
def a000088 : Array Nat := #[1, 1, 2, 4, 11, 34, 156, 1044, 12346]

/-! ## Profiling -/

/-- `refineLoop` again, but counting splitter pops. -/
def refineCount (G : Graph) : Nat → Part → Array Bool → Nat → UInt64 → Scratch → Nat → Part × Nat
  | 0, p, _, _, _, _, k => (p, k)
  | fuel + 1, p, inW, lo, tr, sc, k =>
    match firstSetFrom inW lo with
    | none => (p, k)
    | some s =>
      match refineStepLo G p (inW.set! s false) s tr sc with
      | ((p, inW, tr, sc), lo) => refineCount G fuel p inW lo tr sc (k + 1)

/-- `IO.println` + flush, so progress is visible when stdout is redirected. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Break the cost of one canonicalisation down into its phases. -/
def profGraph (name : String) (G : Graph) : IO Unit := do
  let n := G.n
  let inW0 := if n == 0 then #[] else (Array.replicate n false).set! 0 true
  let fuel := n * n + n + 1
  let (usInit, popsInit) ← timeBest 1 #[G] fun G =>
    (refineCount G fuel (Part.unit n) inW0 0 hashSeed (Scratch.empty n) 0).2
  let (p0, _) := initialRefine G
  let (usChild, popsChild) ← timeBest 1 #[G] fun G =>
    match p0.targetCell n with
    | none => 0
    | some c =>
      let (p', s) := individualize p0 (p0.lab[c]!)
      (refineCount G fuel p' ((Array.replicate n false).set! s true) 0 hashSeed
        (Scratch.empty n) 0).2
  let (usCert, _) ← timeBest 1 #[G] fun G => (certOf G (Array.range G.n)).size
  let (usAll, nodes) ← timeBest 1 #[G] fun G => (canonical G).nodes
  say s!"  {pad name 18} n={pad (toString n) 5} init {pad (showMs usInit) 11} ({pad (toString popsInit) 6} pops) \
    child {pad (showMs usChild) 11} ({pad (toString popsChild) 6} pops) \
    cert {pad (showMs usCert) 11} total {pad (showMs usAll) 11} ({nodes} nodes)"

def main (args : List String) : IO Unit := do
  let deep := args.contains "--deep"
  let mut allOk := true

  if args.contains "--prof" then
    say "=== phase profile ==="
    let profs : List (String × (Unit → Graph)) :=
      [ ("G(200, 1/2)",   fun _ => randomGraph 200 50 5),
        ("G(500, 1/2)",   fun _ => randomGraph 500 50 6),
        ("3-reg 100",     fun _ => randomRegular 100 3 108),
        ("3-reg 200",     fun _ => randomRegular 200 3 13),
        ("3-reg 500",     fun _ => randomRegular 500 3 109),
        ("C_500",         fun _ => cycleGraph 500),
        ("C_1000",        fun _ => cycleGraph 1000),
        ("tree 500",      fun _ => randomTree 500 107),
        ("K_100",         fun _ => completeGraph 100) ]
    for (name, mkG) in profs do
      profGraph name (mkG ())
    return

  say "=== isomorphism invariance, self-consistency, automorphism validity ==="
  say "    (each graph is canonicalised, then re-canonicalised after random relabellings)"
  let cases : List (String × (Unit → Graph) × Nat) :=
    [ ("empty 0",           fun _ => emptyGraph 0, 3),
      ("empty 1",           fun _ => emptyGraph 1, 3),
      ("K_2",               fun _ => completeGraph 2, 5),
      ("path 7",            fun _ => pathGraph 7, 10),
      ("random tree 60",    fun _ => randomTree 60 21, 5),
      ("random tree 200",   fun _ => randomTree 200 22, 3),
      ("G(30, 1/2)",        fun _ => randomGraph 30 50 1, 10),
      ("G(50, 1/2)",        fun _ => randomGraph 50 50 2, 10),
      ("G(50, 1/10)",       fun _ => randomGraph 50 10 3, 10),
      ("G(100, 1/2)",       fun _ => randomGraph 100 50 4, 5),
      ("G(200, 1/2)",       fun _ => randomGraph 200 50 5, 3),
      ("G(500, 1/2)",       fun _ => randomGraph 500 50 6, 2),
      ("random 3-reg 50",   fun _ => randomRegular 50 3 11, 5),
      ("random 4-reg 60",   fun _ => randomRegular 60 4 12, 5),
      ("random 3-reg 200",  fun _ => randomRegular 200 3 13, 2),
      ("K_20",              fun _ => completeGraph 20, 3),
      ("K_50",              fun _ => completeGraph 50, 2),
      ("empty 50",          fun _ => emptyGraph 50, 2),
      ("C_50",              fun _ => cycleGraph 50, 3),
      ("C_500",             fun _ => cycleGraph 500, 2),
      ("Q_5 hypercube",     fun _ => hypercube 5, 3),
      ("Q_7 hypercube",     fun _ => hypercube 7, 2),
      ("K_{10,10}",         fun _ => completeBipartite 10 10, 3),
      ("Petersen K(5,2)",   fun _ => kneser 5 2, 5),
      ("Kneser K(8,3)",     fun _ => kneser 8 3, 2),
      ("Johnson J(8,4)",    fun _ => johnson 8 4, 2),
      ("rook 5x5",          fun _ => rook 5 5, 3),
      ("rook 8x8",          fun _ => rook 8 8, 2),
      ("Shrikhande",        fun _ => shrikhande, 5),
      ("Paley 61",          fun _ => paley 61, 3),
      ("10 x K_5",          fun _ => disjointCliques 10 5, 2),
      ("25 x K_2",          fun _ => disjointCliques 25 2, 2),
      ("4 x G(15,1/2)",     fun _ => disjointCopies 4 (randomGraph 15 50 31), 3),
      ("8 x Petersen",      fun _ => disjointCopies 8 (kneser 5 2), 2) ]
  for (name, mkG, trials) in cases do
    let G := mkG ()
    let rep ← checkGraph name G trials 12345
    say rep.render
    if !rep.ok then allOk := false

  say ""
  say "=== exhaustive: #distinct canonical forms over ALL labelled graphs on n vertices ==="
  say "    (equals the number of isomorphism classes iff the form is invariant AND complete)"
  let top := if deep then 7 else 6
  for n in [0:top+1] do
    let (us, got) ← timeBest 1 #[n] fun n => countClasses n
    let want := a000088[n]!
    let ok := got == want
    say (s!"  n={n}: {pad (toString got) 7} classes (expected {pad (toString want) 7}) " ++
      s!"[{pad (showMs us) 12}] {if ok then "OK" else "MISMATCH"}")
    if !ok then allOk := false
  if !deep then say "  (pass --deep to also run n=7, all 2^21 graphs)"

  say ""
  say "=== non-isomorphic cospectral pair must get different certificates ==="
  let c1 := canonicalForm (rook 4 4)
  let c2 := canonicalForm shrikhande
  let differ := lexCmpU64 c1 c2 != .eq
  say s!"  rook(4,4) vs Shrikhande: certificates differ = {differ}  (expected true)"
  if !differ then allOk := false

  say ""
  say "=== timing (best of 3 runs, canonicalisation only) ==="
  let timings : List (String × (Unit → Graph)) :=
    [ ("G(50, 1/2)",     fun _ => randomGraph 50 50 101),
      ("G(100, 1/2)",    fun _ => randomGraph 100 50 102),
      ("G(200, 1/2)",    fun _ => randomGraph 200 50 103),
      ("G(500, 1/2)",    fun _ => randomGraph 500 50 104),
      ("G(1000, 1/2)",   fun _ => randomGraph 1000 50 105),
      ("G(1000, 1/100)", fun _ => randomGraph 1000 1 106),
      ("random tree 500", fun _ => randomTree 500 107),
      ("3-reg 100",      fun _ => randomRegular 100 3 108),
      ("3-reg 500",      fun _ => randomRegular 500 3 109),
      ("C_1000",         fun _ => cycleGraph 1000),
      ("K_100",          fun _ => completeGraph 100),
      ("K_150",          fun _ => completeGraph 150),
      ("Q_8",            fun _ => hypercube 8),
      ("rook 10x10",     fun _ => rook 10 10),
      ("Paley 101",      fun _ => paley 101),
      ("50 x K_2",       fun _ => disjointCliques 50 2),
      ("20 x Petersen",  fun _ => disjointCopies 20 (kneser 5 2)) ]
  for (name, mkG) in timings do
    let G := mkG ()
    let (us, sink) ← timeBest 3 #[G] fun G => (canonical G).nodes
    say (s!"  {pad name 18} n={pad (toString G.n) 6} m={pad (toString G.edgeCount) 8} " ++
      s!"{pad (showMs us) 12} {sink / 3} nodes")

  say ""
  if allOk then say "ALL CHECKS PASSED" else say "*** SOME CHECKS FAILED ***"
