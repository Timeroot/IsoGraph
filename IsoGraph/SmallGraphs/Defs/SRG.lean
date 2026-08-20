import IsoGraph.Core.Colouring
import IsoGraph.Enum
import Mathlib.Tactic.NormNum.Prime

/-!
# Strongly regular graphs

The sporadic strongly regular graphs: the Chang graphs, the Higman–Sims and Hoffman–Singleton
graphs, and the graphs read off the Steiner system `S(3, 6, 22)`.
-/

namespace SRG

section
open CGraph CGraph.Enum

/-! ## The graphs

The families — `paley`, `johnson`/`triangular`, `kneser`, `rook`, `cocktailParty`, `foldedCube` —
live in `IsoGraph/Core/Defs.lean`.  What is left to define here are the sporadic ones. -/

/-- The Petersen graph, `K(5,2)`: the unique strongly regular graph with parameters
`(10, 3, 0, 1)`. -/
abbrev petersen : CGraph := kneser 5 2

/-- The Clebsch graph, as the folded 5-cube: the unique `(16, 5, 0, 2)` graph. -/
abbrev clebsch : CGraph := foldedCube 4

/-- The Shrikhande graph: the Cayley graph of `ℤ/4 × ℤ/4` with connection set
`{±(1,0), ±(0,1), ±(1,1)}`.

It has the same parameters `(16, 6, 2, 2)` as the `4 × 4` rook's graph but is not isomorphic to
it — the neighbourhood of a vertex is a 6-cycle here and two triangles there.  See
`shrikhande_not_iso_rook`. -/
def shrikhande : CGraph :=
  cayleyAdd (ZMod 4 × ZMod 4) fun d ↦
    [((1 : ZMod 4), (0 : ZMod 4)), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)].contains d

/-- The 27 lines on a smooth cubic surface, adjacent when they meet: `a₁ … a₆`, `b₁ … b₆` and
`c_{ij}` for `i < j`, with `aᵢ · b_j = 1` for `i ≠ j`, `aᵢ · c_{jk} = b_i · c_{jk} = 1` when
`i ∈ {j, k}`, and `c_{ij} · c_{kl} = 1` when `{i,j}` and `{k,l}` are disjoint.

This is the `(27, 10, 1, 5)` graph; its complement is the Schläfli graph. -/
def linesOnCubic : CGraph :=
  ofRel (Fin 6 ⊕ Fin 6 ⊕ {s : Finset (Fin 6) // s.card = 2}) fun x y ↦
    match x, y with
    | .inl i, .inr (.inl j) => decide (i ≠ j)
    | .inl i, .inr (.inr s) => decide (i ∈ s.1)
    | .inr (.inl i), .inr (.inr s) => decide (i ∈ s.1)
    | .inr (.inr s), .inr (.inr t) => decide (s.1 ∩ t.1 = ∅)
    | _, _ => false

/-- The Schläfli graph: 27 lines on a cubic surface, adjacent when they are *skew*.  The unique
strongly regular graph with parameters `(27, 16, 10, 8)`. -/
def schlafli : CGraph := linesOnCubicᶜ

/-- Adjacency of the Hoffman–Singleton graph in Robertson's model, on vertices numbered `0 … 49`:
`5h + j` for vertex `j` of pentagon `Pₕ`, and `25 + 5i + k` for vertex `k` of pentagram `Qᵢ`.

* inside a pentagon, `j ~ j + 1`;
* inside a pentagram, `k ~ k + 2`;
* `Pₕ j ~ Qᵢ k` exactly when `k = h·i + j (mod 5)`.

Only one direction of each pair is listed: `ofRel` symmetrises. -/
private def hsAdj (x y : ℕ) : Bool :=
  if x < 25 then
    if y < 25 then (x / 5 == y / 5) && ((x % 5 + 1) % 5 == y % 5)
    else (y - 25) % 5 == (x / 5 * ((y - 25) / 5) + x % 5) % 5
  else
    if y < 25 then false
    else ((x - 25) / 5 == (y - 25) / 5) && (((x - 25) % 5 + 2) % 5 == (y - 25) % 5)

/-- The Hoffman–Singleton graph: 50 vertices, 7-regular, girth 5, diameter 2 — the unique Moore
graph of degree 7, and the unique strongly regular graph with parameters `(50, 7, 0, 1)`. -/
def hoffmanSingleton : CGraph := ofRel (Fin 50) fun x y ↦ hsAdj x.1 y.1

/-! ### The Chang graphs

Seidel switching `T(8)` with respect to the edge set of a 2-regular (or 1-regular) spanning
subgraph of `K₈` keeps the parameters `(28, 12, 6, 4)`.  Up to isomorphism there are three ways to
do it that change the graph: switch on a perfect matching `4K₂`, on an 8-cycle `C₈`, or on a
disjoint triangle and pentagon `C₃ ∪ C₅`.  The results are the three Chang graphs, and with `T(8)`
they exhaust the graphs with these parameters. -/

/-- The first Chang graph: switch `T(8)` on the perfect matching `{01, 23, 45, 67}`. -/
def chang₁ : CGraph :=
  seidelSwitch (triangular 8) fun s ↦
    ([{0, 1}, {2, 3}, {4, 5}, {6, 7}] : List (Finset (Fin 8))).contains s.1

/-- The second Chang graph: switch `T(8)` on the 8-cycle `0 1 2 3 4 5 6 7`. -/
def chang₂ : CGraph :=
  seidelSwitch (triangular 8) fun s ↦
    ([{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 0}] :
      List (Finset (Fin 8))).contains s.1

/-- The third Chang graph: switch `T(8)` on the triangle `0 1 2` together with the pentagon
`3 4 5 6 7`. -/
def chang₃ : CGraph :=
  seidelSwitch (triangular 8) fun s ↦
    ([{0, 1}, {1, 2}, {2, 0}, {3, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 3}] :
      List (Finset (Fin 8))).contains s.1

/-! ### The Steiner system `S(3, 6, 22)`

A *Steiner system* `S(3, 6, 22)` is a family of six-element subsets — *blocks*, or *hexads* — of a
22-element point set such that every three points lie in exactly one block.  There are 77 blocks,
and the system is unique up to isomorphism; `witt_steiner` below checks the defining property of
the copy written down here.

The construction is Witt's.  Take the projective plane `PG(2, 4)`: 21 points, 21 lines of five
points each.  A *hyperoval* is a six-point set meeting every line in either zero or two points;
there are 168 of them, and they fall into three classes of 56, two hyperovals lying in the same
class exactly when they meet in an even number of points.  Adjoin a 22nd point `21` to the plane.
The blocks are then

* the 21 lines, each extended by the new point, and
* the 56 hyperovals of one class.

The lists are the result of that computation, with the points of `PG(2, 4)` numbered `0 … 20` in
the lexicographic order of their normalised homogeneous coordinates over `GF(4)`.
-/

/-- The 56 hyperovals of one class in `PG(2, 4)`: the blocks of `S(3, 6, 22)` missing the point
`21`. -/
def wittHexads : List (List ℕ) :=
  [ [0, 1, 5, 10, 16, 19], [0, 1, 6, 9, 15, 20], [0, 1, 7, 12, 14, 17],
    [0, 1, 8, 11, 13, 18], [0, 2, 5, 9, 14, 18], [0, 2, 6, 10, 13, 17],
    [0, 2, 7, 11, 16, 20], [0, 2, 8, 12, 15, 19], [0, 3, 5, 12, 13, 20],
    [0, 3, 6, 11, 14, 19], [0, 3, 7, 10, 15, 18], [0, 3, 8, 9, 16, 17],
    [0, 4, 5, 11, 15, 17], [0, 4, 6, 12, 16, 18], [0, 4, 7, 9, 13, 19],
    [0, 4, 8, 10, 14, 20], [1, 2, 5, 6, 11, 12], [1, 2, 7, 8, 9, 10],
    [1, 2, 13, 14, 19, 20], [1, 2, 15, 16, 17, 18], [1, 3, 5, 8, 14, 15],
    [1, 3, 6, 7, 13, 16], [1, 3, 9, 12, 18, 19], [1, 3, 10, 11, 17, 20],
    [1, 4, 5, 7, 18, 20], [1, 4, 6, 8, 17, 19], [1, 4, 9, 11, 14, 16],
    [1, 4, 10, 12, 13, 15], [2, 3, 5, 7, 17, 19], [2, 3, 6, 8, 18, 20],
    [2, 3, 9, 11, 13, 15], [2, 3, 10, 12, 14, 16], [2, 4, 5, 8, 13, 16],
    [2, 4, 6, 7, 14, 15], [2, 4, 9, 12, 17, 20], [2, 4, 10, 11, 18, 19],
    [3, 4, 5, 6, 9, 10], [3, 4, 7, 8, 11, 12], [3, 4, 13, 14, 17, 18],
    [3, 4, 15, 16, 19, 20], [5, 6, 13, 15, 18, 19], [5, 6, 14, 16, 17, 20],
    [5, 7, 9, 12, 15, 16], [5, 7, 10, 11, 13, 14], [5, 8, 9, 11, 19, 20],
    [5, 8, 10, 12, 17, 18], [6, 7, 9, 11, 17, 18], [6, 7, 10, 12, 19, 20],
    [6, 8, 9, 12, 13, 14], [6, 8, 10, 11, 15, 16], [7, 8, 13, 15, 17, 20],
    [7, 8, 14, 16, 18, 19], [9, 10, 13, 16, 18, 20], [9, 10, 14, 15, 17, 19],
    [11, 12, 13, 16, 17, 19], [11, 12, 14, 15, 18, 20] ]

/-- The 21 lines of `PG(2, 4)`, each extended by the point `21`: the blocks of `S(3, 6, 22)`
through that point. -/
def wittLines : List (List ℕ) :=
  [ [0, 1, 2, 3, 4, 21], [0, 5, 6, 7, 8, 21], [0, 9, 10, 11, 12, 21],
    [0, 13, 14, 15, 16, 21], [0, 17, 18, 19, 20, 21], [1, 5, 9, 13, 17, 21],
    [1, 6, 10, 14, 18, 21], [1, 7, 11, 15, 19, 21], [1, 8, 12, 16, 20, 21],
    [2, 5, 10, 15, 20, 21], [2, 6, 9, 16, 19, 21], [2, 7, 12, 13, 18, 21],
    [2, 8, 11, 14, 17, 21], [3, 5, 11, 16, 18, 21], [3, 6, 12, 15, 17, 21],
    [3, 7, 9, 14, 20, 21], [3, 8, 10, 13, 19, 21], [4, 5, 12, 14, 19, 21],
    [4, 6, 11, 13, 20, 21], [4, 7, 10, 16, 17, 21], [4, 8, 9, 15, 18, 21] ]

/-- The 77 blocks of the Steiner system `S(3, 6, 22)`, hexads first: blocks `0 … 55` avoid the
point `21` and blocks `56 … 76` contain it. -/
def wittBlocks : List (List ℕ) := wittHexads ++ wittLines

/-- The blocks as 22-bit masks, so that "point `p` lies in block `i`" and "blocks `i` and `j` are
disjoint" are one machine word each. -/
def wittMasks : Array ℕ :=
  (wittBlocks.map fun B ↦ B.foldr (fun p m ↦ m ||| 2 ^ p) 0).toArray

/-- Point `p` lies in block `i`. -/
def inBlock (i p : ℕ) : Bool := (wittMasks.getD i 0).testBit p

/-- Blocks `i` and `j` are disjoint.  A block is never disjoint from itself, so this relation is
already irreflexive. -/
def disjBlocks (i j : ℕ) : Bool := wittMasks.getD i 0 &&& wittMasks.getD j 0 == 0

theorem wittBlocks_length : wittBlocks.length = 77 := by native_decide

theorem wittBlocks_six : ∀ B ∈ wittBlocks, B.length = 6 ∧ B.Nodup ∧ ∀ p ∈ B, p < 22 := by
  native_decide

/-- **The defining property of the Steiner system**: any three distinct points of `Fin 22` lie in
exactly one of the 77 blocks. -/
theorem witt_steiner (a b c : Fin 22) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((List.range 77).filter fun i ↦ inBlock i a && inBlock i b && inBlock i c).length = 1 := by
  revert hab hac hbc; revert a b c; native_decide

/-! ### The three graphs -/

/-- The Gewirtz graph, also called the Sims–Gewirtz graph: the 56 blocks of `S(3, 6, 22)` missing
a fixed point, adjacent when disjoint.  The unique `(56, 10, 0, 2)` graph. -/
def gewirtz : CGraph := ofRel (Fin 56) fun x y ↦ disjBlocks x.1 y.1

/-- The `M₂₂` graph: all 77 blocks of `S(3, 6, 22)`, adjacent when disjoint.  The unique
`(77, 16, 0, 4)` graph; its automorphism group is the Mathieu group `M₂₂` extended by an outer
automorphism. -/
def m22 : CGraph := ofRel (Fin 77) fun x y ↦ disjBlocks x.1 y.1

/-- Adjacency of the Higman–Sims graph on `0 … 99`: the 22 points `0 … 21` of `S(3, 6, 22)`, its
77 blocks `22 … 98`, and one extra vertex `99`.

* `99` is adjacent to every point;
* a point is adjacent to the blocks containing it;
* two blocks are adjacent when they are disjoint.

Only the direction `x < y` is listed: `ofRel` symmetrises. -/
private def higmanSimsAdj (x y : ℕ) : Bool :=
  if x < 22 then
    if y < 22 then false else if y < 99 then inBlock (y - 22) x else true
  else if x < 99 then
    if 22 ≤ y ∧ y < 99 then disjBlocks (x - 22) (y - 22) else false
  else false

/-- The Higman–Sims graph: 100 vertices, the unique `(100, 22, 0, 6)` graph.  Its automorphism
group contains the sporadic simple Higman–Sims group with index two. -/
def higmanSims : CGraph := ofRel (Fin 100) fun x y ↦ higmanSimsAdj x.1 y.1

end

end SRG

/-! ## The sporadic graphs, on the quotient

The families all have `IsoGraph`-level names already, in `IsoGraph/Core/Quotient.lean`; these are
the ones that only exist here.  Each comes with the `rfl` bridge that lets `@[toIsoGraph]` state the
parameters of the graph below in terms of the isomorphism class rather than the representative. -/

namespace IsoGraph

/-- The Shrikhande graph, as an isomorphism class. -/
def shrikhande : IsoGraph := ⟦SRG.shrikhande⟧

/-- The graph of the 27 lines on a cubic surface, as an isomorphism class. -/
def linesOnCubic : IsoGraph := ⟦SRG.linesOnCubic⟧

/-- The Schläfli graph, as an isomorphism class. -/
def schlafli : IsoGraph := ⟦SRG.schlafli⟧

/-- The Hoffman–Singleton graph, as an isomorphism class. -/
def hoffmanSingleton : IsoGraph := ⟦SRG.hoffmanSingleton⟧

/-- The first Chang graph, as an isomorphism class. -/
def chang₁ : IsoGraph := ⟦SRG.chang₁⟧

/-- The second Chang graph, as an isomorphism class. -/
def chang₂ : IsoGraph := ⟦SRG.chang₂⟧

/-- The third Chang graph, as an isomorphism class. -/
def chang₃ : IsoGraph := ⟦SRG.chang₃⟧

/-- The Gewirtz graph, as an isomorphism class. -/
def gewirtz : IsoGraph := ⟦SRG.gewirtz⟧

/-- The `M₂₂` graph, as an isomorphism class. -/
def m22 : IsoGraph := ⟦SRG.m22⟧

/-- The Higman–Sims graph, as an isomorphism class. -/
def higmanSims : IsoGraph := ⟦SRG.higmanSims⟧

@[isoTransfer] theorem shrikhande_def : shrikhande = ⟦SRG.shrikhande⟧ := rfl

@[isoTransfer] theorem linesOnCubic_def : linesOnCubic = ⟦SRG.linesOnCubic⟧ := rfl

@[isoTransfer] theorem schlafli_def : schlafli = ⟦SRG.schlafli⟧ := rfl

@[isoTransfer] theorem hoffmanSingleton_def : hoffmanSingleton = ⟦SRG.hoffmanSingleton⟧ := rfl

@[isoTransfer] theorem chang₁_def : chang₁ = ⟦SRG.chang₁⟧ := rfl

@[isoTransfer] theorem chang₂_def : chang₂ = ⟦SRG.chang₂⟧ := rfl

@[isoTransfer] theorem chang₃_def : chang₃ = ⟦SRG.chang₃⟧ := rfl

@[isoTransfer] theorem gewirtz_def : gewirtz = ⟦SRG.gewirtz⟧ := rfl

@[isoTransfer] theorem m22_def : m22 = ⟦SRG.m22⟧ := rfl

@[isoTransfer] theorem higmanSims_def : higmanSims = ⟦SRG.higmanSims⟧ := rfl

end IsoGraph
