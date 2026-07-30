import IsoGraph.Basic

/-!
# The canonical form actually computes

`CGraph.canonicalize` and `CGraph.canon` are ordinary definitions — no `Classical.choice`
anywhere — so they can be run.  This file runs them, on graphs whose vertex type is *not*
definitionally an interval of `ℕ` as far as the algorithm is concerned: the listing of vertices
comes out of the `Fintype` instance, through `Multiset`, through `Quot.lift`.

Everything below is checked at elaboration time.
-/

namespace IsoGraph.Compute

/-- A `CGraph` on `Fin n` from an arbitrary `Bool` matrix: symmetrised, with the diagonal
deleted. -/
def ofFn (n : ℕ) (f : ℕ → ℕ → Bool) : CGraph where
  V := Fin n
  Adj i j := decide (i ≠ j) && (f i.1 j.1 || f j.1 i.1)
  symm i j := by
    by_cases h : i = j
    · subst h; simp
    · cases f i.1 j.1 <;> cases f j.1 i.1 <;> simp [h, Ne.symm h]
  loopless i := by simp

/-- The canonical adjacency matrix, as a list of rows.

The `let c := G.canon` is what makes this one search rather than `n²` of them: the result type is
a `List`, not a function type, so the compiler keeps the sharing. -/
def canonMatrix (G : CGraph) : List (List Bool) :=
  let c := G.canon
  (List.range c.size).map fun a ↦ (List.range c.size).map fun b ↦ c.adj a b

/-- Number of ordered adjacent pairs in the canonical representative.  Unlike `canonMatrix` this
goes through `CGraph.canonicalize` itself, so it exercises the bundled graph. -/
def canonDegreeSum (G : CGraph) : ℕ :=
  let g := G.canonicalize
  (Finset.univ.filter fun p : g.V × g.V ↦ g.Adj p.1 p.2 = true).card

/-! ### The graphs -/

/-- The `n`-cycle. -/
private def cycAdj (n a b : ℕ) : Bool := (a + 1) % n == b

private def c5 : CGraph := ofFn 5 (cycAdj 5)
/-- The same 5-cycle with its vertices renamed by `i ↦ 2i mod 5`. -/
private def c5' : CGraph := ofFn 5 fun a b ↦ cycAdj 5 (2 * a % 5) (2 * b % 5)
/-- The path on 5 vertices: same number of vertices, not isomorphic. -/
private def p5 : CGraph := ofFn 5 fun a b ↦ a + 1 == b

private def c6 : CGraph := ofFn 6 (cycAdj 6)
/-- Two disjoint triangles: 2-regular on 6 vertices, like `c6`, but not isomorphic to it. -/
private def twoTriangles : CGraph := ofFn 6 fun a b ↦ a / 3 == b / 3

/-- Petersen: outer 5-cycle, spokes, inner pentagram. -/
private def petAdj (a b : ℕ) : Bool :=
  (decide (a < 5) && decide (b < 5) && (a + 1) % 5 == b) ||
  (decide (a < 5) && a + 5 == b) ||
  (decide (5 ≤ a) && decide (5 ≤ b) && (a - 5 + 2) % 5 + 5 == b)

private def petersen : CGraph := ofFn 10 petAdj
/-- Petersen with its vertices renamed by `i ↦ 3i + 7 mod 10`. -/
private def petersen' : CGraph :=
  ofFn 10 fun a b ↦ petAdj ((3 * a + 7) % 10) ((3 * b + 7) % 10)

/-- A graph whose vertex type is *not* `Fin n`: the 4-cycle, as the pairs of booleans differing in
exactly one coordinate.  Its listing of vertices comes from the `Fintype (Bool × Bool)` instance,
so the algorithm never sees a `Fin`. -/
private def square : CGraph where
  V := Bool × Bool
  Adj p q := (p.1 != q.1) != (p.2 != q.2)
  symm p q := by revert p q; decide
  loopless p := by revert p; decide

private def c4 : CGraph := ofFn 4 (cycAdj 4)

/-! ### The checks

Run through `#eval!`, so they go through the *compiler*: if any of these definitions were secretly
noncomputable, this file would not elaborate.

`#eval!` rather than `#eval` because `CGraph.canon` is a `Quot.lift`, and the proof it is
lifted along is `CGraph.canonOfList_perm`, which currently rests on the `sorry` in
`IsoGraph.Spec`.  Compiled code never looks at that proof — but `#eval` refuses to run anything
whose *term* mentions `sorry`, so it has to be told to.  Once the obligation is discharged this
becomes a plain `#eval`. -/

/-- Every check, as one `Bool`. -/
def allChecks : Bool :=
  -- isomorphic graphs get the same canonical form …
  (canonMatrix c5 == canonMatrix c5') &&
  (canonMatrix petersen == canonMatrix petersen') &&
  (canonMatrix square == canonMatrix c4) &&
  -- … and non-isomorphic ones do not, even with equal degree sequences
  (canonMatrix c5 != canonMatrix p5) &&
  (canonMatrix c6 != canonMatrix twoTriangles) &&
  -- canonicalising the canonical representative changes nothing
  (canonMatrix c5.canonicalize == canonMatrix c5) &&
  (canonMatrix petersen.canonicalize == canonMatrix petersen) &&
  -- `canonicalize` is a genuine graph with the right number of edges
  (canonDegreeSum c5 == 10) &&
  (canonDegreeSum petersen == 30) &&
  (canonDegreeSum twoTriangles == 12) &&
  (canonDegreeSum square == 8) &&
  (Fintype.card square.canonicalize.V == 4)

/-- info: true -/
#guard_msgs in
#eval! allChecks

end IsoGraph.Compute
