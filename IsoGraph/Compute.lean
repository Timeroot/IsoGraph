import IsoGraph.Basic
import IsoGraph.Symmetry

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
  let idx := List.finRange (Fintype.card G.V)
  idx.map fun a ↦ idx.map fun b ↦ c.adj a b

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

Run through `#eval`, so they go through the *compiler*: if any of these definitions were secretly
noncomputable, this file would not elaborate. -/

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
#eval allChecks

/-! ### Automorphism groups

The same graphs again, through `IsoGraph.Canon.Group`: the canonical labelling search also hands
back generators of the automorphism group, and those are enough to prove vertex- and
arc-transitivity. -/

/-- The triangular prism: two triangles joined by a perfect matching.  Vertex-transitive, but not
arc-transitive — no automorphism takes a triangle edge to a matching edge. -/
private def prism : CGraph := ofFn 6 fun a b ↦
  (decide (a < 3) && decide (b < 3) && (a + 1) % 3 == b) ||
  (decide (3 ≤ a) && decide (3 ≤ b) && (a - 3 + 1) % 3 + 3 == b) ||
  (a + 3 == b)

/-- The vertex type of `ofFn n f` is `Fin n` on the nose. -/
private def ofFnEquiv (n : ℕ) (f : ℕ → ℕ → Bool) : (ofFn n f).V ≃ Fin n := Equiv.refl _

/-- Every symmetry check, as one `Bool`. -/
def symmetryChecks : Bool :=
  -- transitivity, on graphs indexed by `Fin n`
  (c5.vertexTransitiveCertOfEquiv (ofFnEquiv 5 _)).isYes &&
  (c5.arcTransitiveCertOfEquiv (ofFnEquiv 5 _)).isYes &&
  (petersen.vertexTransitiveCertOfEquiv (ofFnEquiv 10 _)).isYes &&
  (petersen.arcTransitiveCertOfEquiv (ofFnEquiv 10 _)).isYes &&
  (twoTriangles.arcTransitiveCertOfEquiv (ofFnEquiv 6 _)).isYes &&
  (prism.vertexTransitiveCertOfEquiv (ofFnEquiv 6 _)).isYes &&
  !(prism.arcTransitiveCertOfEquiv (ofFnEquiv 6 _)).isYes &&
  !(p5.vertexTransitiveCertOfEquiv (ofFnEquiv 5 _)).isYes &&
  -- and on a graph whose vertex type is not an interval, through `canonicalize`
  square.vertexTransitiveCert.isYes &&
  square.arcTransitiveCert.isYes &&
  -- the order of the group generated by the harvested generators
  (c5.autGroupOrder? (ofFnEquiv 5 _) == some 10) &&
  (p5.autGroupOrder? (ofFnEquiv 5 _) == some 2) &&
  (petersen.autGroupOrder? (ofFnEquiv 10 _) == some 120) &&
  (prism.autGroupOrder? (ofFnEquiv 6 _) == some 12) &&
  (twoTriangles.autGroupOrder? (ofFnEquiv 6 _) == some 72) &&
  -- one search, both halves
  ((petersen.canonMatrixAndAutos (ofFnEquiv 10 _)).1.adj ==
    (IsoGraph.Canon.canonMatrix 10 (petersen.finAdj (ofFnEquiv 10 _))).adj) &&
  ((petersen.canonMatrixAndAutos (ofFnEquiv 10 _)).2.size ==
    (petersen.autGens (ofFnEquiv 10 _)).size)

/-- info: true -/
#guard_msgs in
#eval symmetryChecks

/-! And the certificates really do discharge the propositions: `Cert.out` turns a certificate
whose `isYes` is `true` into a proof of the proposition it certifies, and `native_decide` performs
that evaluation in compiled code. -/

example : petersen.IsVertexTransitive :=
  (petersen.vertexTransitiveCertOfEquiv (ofFnEquiv 10 _)).out (by native_decide)

example : petersen.IsArcTransitive :=
  (petersen.arcTransitiveCertOfEquiv (ofFnEquiv 10 _)).out (by native_decide)

example : square.IsVertexTransitive := square.vertexTransitiveCert.out (by native_decide)

end IsoGraph.Compute
