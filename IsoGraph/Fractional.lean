import IsoGraph.Sat
import IsoGraph.Invariants.Fractional

/-!
# Computing the fractional relaxations

`IsoGraph/Invariants/Fractional.lean` defines `α_f` and `χ_f` and proves the bounds; this file
computes them.  The value of the linear program is found outside the kernel, by a rational
simplex, and comes back as a pair of certificates that Lean checks:

* the optimal *dual* solution is a fractional clique cover, and `CGraph.fracIndepNum_le_of_natCover`
  turns it into `α_f(G) ≤ q`;
* the optimal *primal* solution is a fractional independent set, and
  `CGraph.le_fracIndepNum_of_natWeights` turns it into `q ≤ α_f(G)`.

Both are integer-scaled, so every side condition is a `decide` about natural numbers, and
`linarith` puts the two halves together into the equation.  The primal half also needs to know
that no clique is larger than `w`, since that is what cuts its feasibility check down to a finite
search; that one bound is left to `graph_sat`.

    compute_fractional_indepNum (cycle 5)         -- h_fα : (cycle 5).fracIndepNum = 5 / 2
    compute_fractional_chromNum native petersen   -- h_fχ : petersen.fracChromNum = 5 / 2

`compute_fractional_chromNum` is the same computation run on the complement, since that is what
`CGraph.fracChromNum` is.  When the primal half is out of reach — the feasibility check grows as
`∑_{k ≤ ω} (n choose k)`, and `w` may be large — the tactic settles for the upper bound and adds
`h_fα : α_f(G) ≤ q` instead.  As in `graph_sat`, `native` proves the side conditions with
`native_decide`; on a complement, or on `Finset` vertices, that is the difference between seconds
and not finishing.

The linear program is over the *maximal* cliques, enumerated by Bron–Kerbosch: a constraint on a
clique that sits inside another is implied by it, so the smaller ones can be dropped.  The
simplex runs Bland's rule on the tableau of the packing program, whose slack basis is feasible to
start with, so no first phase is needed.  Everything here is metacode: a wrong answer cannot make
Lean accept a wrong theorem, it can only fail to produce one.

The last section puts the same bound in front of `graph_sat`, where integrality turns
`α_f(G) ≤ 5/2` into `α(G) ≤ 2` with no search at all — on the graphs where certifying it is
cheaper than the search it replaces, which is a smaller set than one would hope.
-/

set_option autoImplicit false

/-- Whether `graph_sat` tries the fractional relaxation before the SAT search.  Turning it off
restores the behaviour of `IsoGraph/Sat.lean` on its own. -/
register_option graph_sat.frac : Bool := {
  defValue := true
  descr := "in graph_sat, try the fractional relaxation and integrality before the SAT search"
}

namespace CGraph
namespace FracLP

/-! ## Maximal cliques -/

/-- The adjacency matrix of a graph given by its edge list of indices. -/
def adjMatrix (n : ℕ) (es : List (ℕ × ℕ)) : Array (Array Bool) := Id.run do
  let mut a : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for (i, j) in es do
    if i < n && j < n then
      a := a.modify i (·.set! j true)
      a := a.modify j (·.set! i true)
  return a

private def nbr (adj : Array (Array Bool)) (u v : ℕ) : Bool :=
  (adj.getD u #[]).getD v false

/-- Bron–Kerbosch with pivoting: every maximal clique of `adj`, as a sorted array of indices. -/
private partial def bkAux (adj : Array (Array Bool)) (R : List ℕ) (P X : List ℕ)
    (limit : ℕ) (acc : Array (Array ℕ)) : Array (Array ℕ) :=
  if acc.size > limit then acc
  else if P.isEmpty && X.isEmpty then acc.push (R.toArray.qsort (· < ·))
  else Id.run do
    let pivot : Option ℕ := (P ++ X).foldl (fun best u ↦
      let d := (P.filter (fun v ↦ nbr adj u v)).length
      match best with
      | none => some (u, d)
      | some (bu, bd) => if d > bd then some (u, d) else some (bu, bd)) none
      |>.map Prod.fst
    let ext := match pivot with
      | none => P
      | some u => P.filter (fun v ↦ !nbr adj u v)
    let mut P := P
    let mut X := X
    let mut acc := acc
    for v in ext do
      if acc.size > limit then break
      acc := bkAux adj (v :: R) (P.filter (nbr adj v)) (X.filter (nbr adj v)) limit acc
      P := P.erase v
      X := v :: X
    return acc

/-- The maximal cliques of a graph on `n` vertices, abandoned once there are more than `limit` of
them: the caller has a cap anyway, and a dense complement can have exponentially many. -/
def maximalCliques (n : ℕ) (adj : Array (Array Bool)) (limit : ℕ) : Array (Array ℕ) :=
  bkAux adj [] (List.range n) [] limit #[]

/-! ## An exact rational simplex

The packing program `max ∑ x` subject to `x ≥ 0` and `∑_{v ∈ K} x v ≤ 1` for every maximal
clique `K`.  Its right-hand side is positive, so the slack basis is feasible and one phase
suffices; Bland's rule keeps it from cycling. -/

/-- An optimal pair for the packing program: the vertex weights, the clique weights and their
common value. -/
structure Solution where
  /-- The optimal primal solution: a weight for each vertex. -/
  x : Array Rat
  /-- The optimal dual solution: a weight for each maximal clique. -/
  y : Array Rat
  /-- The common optimal value. -/
  val : Rat

private def pivotAt (T : Array (Array Rat)) (rows i e : ℕ) : Array (Array Rat) := Id.run do
  let piv := (T.getD i #[]).getD e 0
  let mut T := T.modify i (·.map (· / piv))
  let rowI := T.getD i #[]
  for k in [0:rows] do
    if k != i then
      let f := (T.getD k #[]).getD e 0
      if f != 0 then
        T := T.modify k (fun row ↦ row.mapIdx (fun j v ↦ v - f * rowI.getD j 0))
  return T

private partial def pivotLoop (n m cols : ℕ) (T : Array (Array Rat)) (basis : Array ℕ)
    (fuel : ℕ) : Option (Array (Array Rat) × Array ℕ) :=
  if fuel = 0 then none else
  let obj := T.getD m #[]
  let entering := (List.range (n + m)).find? (fun j ↦ obj.getD j 0 < 0)
  match entering with
  | none => some (T, basis)
  | some e =>
    let best : Option (ℕ × Rat) := (List.range m).foldl (fun best i ↦
      let a := (T.getD i #[]).getD e 0
      if a ≤ 0 then best
      else
        let r := (T.getD i #[]).getD (cols - 1) 0 / a
        match best with
        | none => some (i, r)
        | some (bi, br) =>
          if r < br || (r == br && basis.getD i 0 < basis.getD bi 0) then some (i, r)
          else best) none
    match best with
    | none => none
    | some (i, _) => pivotLoop n m cols (pivotAt T (m + 1) i e) (basis.set! i e) (fuel - 1)

/-- Solve the packing program on `n` vertices with one constraint per clique. -/
def solve (n : ℕ) (cliques : Array (Array ℕ)) : Option Solution := Id.run do
  let m := cliques.size
  let cols := n + m + 1
  let mut T : Array (Array Rat) := #[]
  for i in [0:m] do
    let mut row : Array Rat := Array.replicate cols 0
    for j in cliques.getD i #[] do
      row := row.set! j 1
    row := row.set! (n + i) 1
    row := row.set! (cols - 1) 1
    T := T.push row
  let mut obj : Array Rat := Array.replicate cols 0
  for j in [0:n] do
    obj := obj.set! j (-1)
  T := T.push obj
  let basis : Array ℕ := (Array.range m).map (n + ·)
  match pivotLoop n m cols T basis (200 + 40 * (n + m)) with
  | none => return none
  | some (fin, fbasis) =>
    let mut x : Array Rat := Array.replicate n 0
    for i in [0:m] do
      let bi := fbasis.getD i 0
      if bi < n then
        x := x.set! bi ((fin.getD i #[]).getD (cols - 1) 0)
    let mut y : Array Rat := Array.replicate m 0
    for i in [0:m] do
      y := y.set! i ((fin.getD m #[]).getD (n + i) 0)
    return some ⟨x, y, (fin.getD m #[]).getD (cols - 1) 0⟩

/-- Check an answer of `FracLP.solve` before building a proof out of it: both solutions
nonnegative and feasible, with equal objective values. -/
def Solution.valid (s : Solution) (n : ℕ) (cliques : Array (Array ℕ)) : Bool := Id.run do
  if s.x.size != n || s.y.size != cliques.size then return false
  if s.x.any (· < 0) || s.y.any (· < 0) then return false
  for i in [0:cliques.size] do
    let K := cliques.getD i #[]
    if K.foldl (fun acc j ↦ acc + s.x.getD j 0) 0 > 1 then return false
  for j in [0:n] do
    let mut tot : Rat := 0
    for i in [0:cliques.size] do
      if (cliques.getD i #[]).contains j then tot := tot + s.y.getD i 0
    if tot < 1 then return false
  if s.x.foldl (· + ·) 0 != s.val || s.y.foldl (· + ·) 0 != s.val then return false
  return true

/-- Clear the denominators of a list of nonnegative rationals: the common denominator and the
scaled numerators. -/
def clearDenom (q : Array Rat) : ℕ × Array ℕ :=
  let d := q.foldl (fun acc r ↦ Nat.lcm acc r.den) 1
  (d, q.map (fun r ↦ (r.num * (d : Int) / (r.den : Int)).toNat))

/-! ## The tactics -/

section Tactic
open Lean Elab Tactic Meta

/-- `set_option trace.graph_sat.frac true` reports the size of each program, how long it took to
read the graph and to solve it, and which way the fast path below went. -/
initialize registerTraceClass `graph_sat.frac

/-- Compile and run a closed `ℕ`-valued expression. -/
private unsafe def evalNatImpl (e : Expr) : MetaM ℕ := Meta.evalExpr ℕ (.const ``Nat []) e

/-- Evaluate a closed `ℕ`-valued expression.  As in `IsoGraph/Sat.lean`, only ever called through
its `implemented_by`; a wrong answer cannot make the certificate check out. -/
@[implemented_by evalNatImpl]
private def evalNat (_e : Expr) : MetaM ℕ := pure 0

/-- Compile and run a closed expression of type `List (ℕ × ℕ)`. -/
private unsafe def evalPairsImpl (e : Expr) : MetaM (List (ℕ × ℕ)) :=
  Meta.evalExpr (List (ℕ × ℕ))
    (mkApp (.const ``List [0])
      (mkApp2 (.const ``Prod [0, 0]) (.const ``Nat []) (.const ``Nat []))) e

/-- Evaluate a closed expression of type `List (ℕ × ℕ)`. -/
@[implemented_by evalPairsImpl]
private def evalPairs (_e : Expr) : MetaM (List (ℕ × ℕ)) := pure []

/-- The order and the edge list of a graph written as a term. -/
private def graphData (g : Term) : TermElabM (ℕ × List (ℕ × ℕ)) := do
  let n ← evalNat (← Term.elabTerm (← `(FinEnum.card ($g : CGraph).V)) none)
  let es ← evalPairs (← Term.elabTerm (← `(CGraph.Sat.edgeIdxList ($g : CGraph))) none)
  return (n, es)

/-- The `Finset` of vertices with the listed indices, read through `FinEnum.equiv`, which is the
only way to name a vertex of a graph whose vertex type is not literally `Fin n`. -/
private def cliqueTerm (g : Term) (n : ℕ) (K : Array ℕ) : TermElabM Term := do
  let elems ← K.mapM fun j ↦ `($(quote j))
  `(((([$elems,*] : List (Fin $(quote n))).map
      (FinEnum.equiv (α := ($g : CGraph).V)).symm).toFinset))

/-- A vector of natural number literals. -/
private def natVec (a : Array ℕ) : MetaM Term := do
  let elems ← a.mapM fun v ↦ `($(quote v))
  `(![$elems,*])

/-- A nonnegative rational as a real literal. -/
private def ratTerm (q : Rat) : MetaM Term :=
  if q.den == 1 then `(($(quote q.num.toNat) : ℝ))
  else `((($(quote q.num.toNat) : ℝ)) / (($(quote q.den) : ℝ)))

/-- How many sets the feasibility check of the primal certificate would have to look at. -/
private def searchSize (n w : ℕ) : ℕ := (List.range (w + 1)).foldl (fun acc k ↦ acc + n.choose k) 0

/-- Everything the elaborator learned about a graph: its order, its maximal cliques, and the
optimal pair of the packing program over them. -/
private structure Data where
  /-- The number of vertices. -/
  n : ℕ
  /-- The maximal cliques, as sorted arrays of vertex indices. -/
  cliques : Array (Array ℕ)
  /-- A verified optimal pair for the packing program. -/
  sol : Solution

/-- Run the linear program for `α_f(g)`, giving up rather than failing: `none` if the graph has no
vertices, if it has more than `maxCliques` maximal cliques, if the tableau those would make is too
big, or if the simplex does not come back with a pair that checks out. -/
private def lpData (g : Term) (maxCliques : ℕ) : TermElabM (Option Data) := do
  let t0 ← IO.monoMsNow
  let (n, es) ← graphData g
  let t1 ← IO.monoMsNow
  if n == 0 || n > 200 then return none
  let cliques := maximalCliques n (adjMatrix n es) maxCliques
  if cliques.size > maxCliques || n * cliques.size > 60000 then return none
  let some sol := solve n cliques | return none
  let t2 ← IO.monoMsNow
  trace[graph_sat.frac] "{n} vertices, {cliques.size} cliques: {t1 - t0} ms reading, \
    {t2 - t1} ms solving"
  return if sol.valid n cliques then some ⟨n, cliques, sol⟩ else none

/-- The tactic that ties the emitted literals to the graph: `decide`, or `native_decide` when the
vertex type is one the kernel is slow on.  A complement or a `Finset` subtype is usually the
point at which it becomes worth it. -/
private def sideTac (native : Bool) : MetaM (TSyntax `tactic) :=
  if native then `(tactic| native_decide) else `(tactic| decide)

/-- The dual half of the certificate: a term proving `α_f(g) ≤ q`, built from the cliques the
optimal cover actually uses, with their weights cleared of denominators. -/
private def upperTerm (g : Term) (D : Data) (native : Bool) : TermElabM Term := do
  let used := (Array.range D.cliques.size).filter (fun i ↦ D.sol.y.getD i 0 != 0)
  let (d, ay) := clearDenom (used.map (D.sol.y.getD · 0))
  let coverCliques : Array Term ← (used.map (D.cliques.getD · #[])).mapM (cliqueTerm g D.n)
  let coverTerm ← `(![$coverCliques,*])
  let weightTerm ← natVec ay
  let s := ay.foldl (· + ·) 0
  let tac ← sideTac native
  `(CGraph.fracIndepNum_le_of_natCover (G := $g) (d := $(quote d)) (s := $(quote s))
    (by norm_num) $coverTerm $weightTerm (by $tac:tactic) (by $tac:tactic) (by $tac:tactic))

/-- The primal half of the certificate: a term proving `q ≤ α_f(g)` from the optimal vertex
weights.  Their feasibility is checked over the sets of at most `ω(g)` vertices, so this is only
worth trying when there are not too many of those; the bound `ω(g) ≤ w` itself is left to
`graph_sat`. -/
private def lowerTerm (g : Term) (D : Data) (native : Bool) : TermElabM (Option Term) := do
  let w := D.cliques.foldl (fun acc K ↦ Nat.max acc K.size) 0
  if searchSize D.n w > 20000 then return none
  let (bd, bx) := clearDenom D.sol.x
  let bTerm ← natVec bx
  let sb := bx.foldl (· + ·) 0
  let tac ← sideTac native
  let sat ← if native then `(tactic| graph_sat native) else `(tactic| graph_sat)
  some <$> `(CGraph.le_fracIndepNum_of_natWeights (G := $g) (d := $(quote bd))
    (w := $(quote w)) (s := $(quote sb)) (by norm_num)
    (fun v ↦ $bTerm (FinEnum.equiv v)) (by $tac:tactic) (by $sat:tactic) (by $tac:tactic))

/-- The two halves of the certificate for `g`: a term proving `α_f(g) ≤ q`, optionally a term
proving `q ≤ α_f(g)`, and `q` itself. -/
private def certificates (g : Term) (native : Bool) : TermElabM (Term × Option Term × Rat) := do
  let some D ← lpData g 800 |
    throwError "compute_fractional_indepNum: could not solve the linear program for {g}"
  return (← upperTerm g D native, ← lowerTerm g D native, D.sol.val)

/-- **Compute the fractional independence number.**  `compute_fractional_indepNum G` runs the
linear program for `α_f(G)` and adds the value to the context as `h_fα`, with the two halves of
the proof supplied by the optimal primal and dual solutions.  If the primal half is too large to
check, the hypothesis is the upper bound `α_f(G) ≤ q` instead of the equation.
`compute_fractional_indepNum native G` proves the side conditions with `native_decide`. -/
syntax (name := computeFracIndepNum) "compute_fractional_indepNum" (ppSpace &"native")?
  ppSpace term : tactic

/-- **Compute the fractional chromatic number.**  `compute_fractional_chromNum G` is
`compute_fractional_indepNum` on the complement, since `χ_f(G)` is `α_f(Gᶜ)`; the value lands in
the context as `h_fχ`.  The complement is often where `native` becomes necessary: its adjacency is
a conjunction with a disequality, and the kernel is slow on those. -/
syntax (name := computeFracChromNum) "compute_fractional_chromNum" (ppSpace &"native")?
  ppSpace term : tactic

/-- The shared body of the two tactics: `stmt` is the left-hand side of the hypothesis to add,
`g` the graph the program runs on, and `pre` the rewrite that turns the one into the other. -/
private def addValue (g : Term) (stmt : Term) (hname : Ident) (pre : Option (TSyntax `tactic))
    (native : Bool) : TacticM Unit := withMainContext do
  let (upper, lower, val) ← certificates g native
  let q ← ratTerm val
  let preTac : TSyntax `tactic ← match pre with
    | some t => pure t
    | none => `(tactic| skip)
  match lower with
  | some lower =>
    evalTactic <| ← `(tactic|
      have $hname : $stmt = $q := by
        set_option maxRecDepth 100000 in
        (have hub := $upper
         have hlb := $lower
         $preTac:tactic
         norm_num at hub hlb ⊢
         linarith))
  | none =>
    evalTactic <| ← `(tactic|
      have $hname : $stmt ≤ $q := by
        set_option maxRecDepth 100000 in
        (have hub := $upper
         $preTac:tactic
         norm_num at hub ⊢
         linarith))

elab_rules : tactic
  | `(tactic| compute_fractional_indepNum $[native%$nat]? $g:term) => do
    addValue g (← `(($g : CGraph).fracIndepNum)) (mkIdent (.mkSimple "h_fα")) none nat.isSome

elab_rules : tactic
  | `(tactic| compute_fractional_chromNum $[native%$nat]? $g:term) => do
    addValue (← `(($g : CGraph)ᶜ)) (← `(($g : CGraph).fracChromNum))
      (mkIdent (.mkSimple "h_fχ")) (some (← `(tactic| rw [CGraph.fracChromNum_eq_compl])))
      nat.isSome

/-! ### The fast path for `graph_sat`

An upper bound on `α_f` is an upper bound on `α`, and being an integer it can be rounded down: if
the linear program says `α_f(G) ≤ 5/2` then `α(G) ≤ 2` with no search at all.  The same goes for
`ω` through `χ_f`, and hence for `ν` through the line graph.  This is a second elaborator for the
`graph_sat` syntax, tried before the SAT one; when the relaxation is too weak, too big to solve,
or too big to be worth certifying, it stands aside and the SAT search runs as before.

It fires on `graph_sat native` and on graphs of at most forty vertices — see
`worthACertificate`, which is where the measurements are.  `set_option graph_sat.frac false`
turns it off entirely. -/

/-- Whether the fast path should go on and build a certificate for a program this size.

The bound is empirical and it is *small*.  What the fast path spends is not the linear program —
that is milliseconds on anything here — but the certificate: elaborating one `Finset` literal per
clique of the cover and then checking the two sums over them.  On the 54-vertex Gray graph that
step had not finished after five minutes, where `graph_sat` alone refutes the same bound in
fifteen seconds; on the cages up to thirty-two vertices it is fast enough to save a fifth of the
file.  Being wrong here is only ever slow, never unsound, but slow is the thing worth avoiding, so
the fast path stays inside the range where it has been measured.

`native` is required for the same reason: the check is three `native_decide`s, and the kernel
takes longer over them than CaDiCaL takes to refute the bound outright — and it takes the
declaration's heartbeats with it, leaving none for the fallback. -/
private def worthACertificate (native : Bool) (D : Data) : Bool :=
  native && D.n ≤ 40 && D.cliques.size ≤ 64

/-- Close a goal `G.indepNum ≤ n`, or `G.cliqueNum ≤ n` when `dual` is set, by rounding down the
fractional bound.  Fails if the program is out of reach or its value is at least `n + 1`. -/
private def roundDown (g : Term) (n : ℕ) (dual native : Bool) : TacticM Unit := do
  let lp ← if dual then `(($g)ᶜ) else pure g
  let some D ← lpData lp 300 | throwUnsupportedSyntax
  unless worthACertificate native D do
    trace[graph_sat.frac] "the certificate would cost more than the search; leaving it to SAT"
    throwUnsupportedSyntax
  if D.sol.val ≥ (n : Rat) + 1 then
    trace[graph_sat.frac] "the relaxation gives only {D.sol.val}; leaving it to the SAT search"
    throwUnsupportedSyntax
  trace[graph_sat.frac] "closing the goal with the fractional bound {D.sol.val}"
  let upper ← upperTerm lp D native
  let q ← ratTerm D.sol.val
  if dual then
    evalTactic <| ← `(tactic|
      set_option maxRecDepth 100000 in
      (refine CGraph.cliqueNum_le_of_fracChromNum_le (G := $g) (c := $q) ?_ (by norm_num)
       rw [CGraph.fracChromNum_eq_compl]
       have hub := $upper
       norm_num at hub ⊢
       linarith))
  else
    evalTactic <| ← `(tactic|
      set_option maxRecDepth 100000 in
      (refine CGraph.indepNum_le_of_fracIndepNum_le (G := $g) (c := $q) ?_ (by norm_num)
       have hub := $upper
       norm_num at hub ⊢
       linarith))

/-- Close a goal `k < G.chromNum` by rounding *up* the fractional chromatic number, which is the
independence program on the complement.  This one needs the primal half of the certificate, so it
only fires on graphs whose feasibility check is small; it is worth trying because `χ_f` sees
things `ω` does not — `χ_f(C₅) = 5/2` proves `χ(C₅) > 2`, and `χ_f(K(n,k)) = n/k` proves the
Kneser bounds — and because when it fires there is no search at all. -/
private def roundUp (g : Term) (k : ℕ) (native : Bool) : TacticM Unit := do
  let lp ← `(($g)ᶜ)
  let some D ← lpData lp 300 | throwUnsupportedSyntax
  unless worthACertificate native D do
    trace[graph_sat.frac] "the certificate would cost more than the search; leaving it to SAT"
    throwUnsupportedSyntax
  if D.sol.val ≤ (k : Rat) then
    trace[graph_sat.frac] "the relaxation gives only {D.sol.val}; leaving it to the SAT search"
    throwUnsupportedSyntax
  let some lower ← lowerTerm lp D native | throwUnsupportedSyntax
  trace[graph_sat.frac] "closing the goal with the fractional bound {D.sol.val}"
  let q ← ratTerm D.sol.val
  evalTactic <| ← `(tactic|
    set_option maxRecDepth 100000 in
    (refine CGraph.lt_chromNum_of_lt_fracChromNum (G := $g) (c := $q) (by norm_num) ?_
     rw [CGraph.fracChromNum_eq_compl]
     have hlb := $lower
     norm_num at hlb ⊢
     linarith))

elab_rules : tactic
  | `(tactic| graph_sat $[native%$nat]?) => withMainContext do
    unless (← getOptions).getBool `graph_sat.frac true do throwUnsupportedSyntax
    let native := nat.isSome
    let some shape ← CGraph.Sat.shapeOf (← whnfR (← (← getMainGoal).getType)) |
      throwUnsupportedSyntax
    let st ← saveState
    try
      match shape with
      | .indep G n => roundDown (← Term.exprToSyntax G) n false native
      | .clique G n => roundDown (← Term.exprToSyntax G) n true native
      | .chrom G k => roundUp (← Term.exprToSyntax G) k native
    catch _ =>
      st.restore
      throwUnsupportedSyntax

end Tactic

end FracLP

/-! ## Examples

The regression tests: both entry points on a graph whose value is not an integer, the upper bound
alone on one where the two invariants come apart, and the fast path on each of the three goal
shapes it handles. -/

section Examples

set_option maxHeartbeats 1000000

example : (cycle 5).fracIndepNum = 5 / 2 := by
  compute_fractional_indepNum (cycle 5)
  exact h_fα

example : (cycle 5).fracChromNum = 5 / 2 := by
  compute_fractional_chromNum (cycle 5)
  exact h_fχ

-- The Petersen graph is triangle free and has a perfect matching, so `α_f` is `n / 2` — a whole
-- unit above `α = 4`, which is why the fast path below leaves that one to the SAT search.  Its
-- vertices are two-element `Finset`s, so this is one for `native`.
example : petersen.fracIndepNum = 5 := by
  compute_fractional_indepNum native petersen
  exact h_fα

-- `χ_f(K(n, k)) = n / k`, the theorem that gives the chromatic number of a Kneser graph; the
-- Petersen graph is `K(5, 2)`.
example : petersen.fracChromNum = 5 / 2 := by
  compute_fractional_chromNum native petersen
  exact h_fχ

-- `α(C₅) ≤ 2`, `ω(C₅) ≤ 2` and `χ(C₅) > 2`, none of them with a SAT call.  The fast path only
-- fires on `graph_sat native`; see `worthACertificate` for why.
example : (cycle 5).indepNum ≤ 2 := by graph_sat native
example : (cycle 5).cliqueNum ≤ 2 := by graph_sat native
example : 2 < (cycle 5).chromNum := by graph_sat native

end Examples

end CGraph
