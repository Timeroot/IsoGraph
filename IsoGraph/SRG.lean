import IsoGraph.Constructions
import IsoGraph.Enum
import Mathlib.Tactic.NormNum.Prime

/-!
# A table of strongly regular graphs

A graph is *strongly regular with parameters `(n, k, ℓ, μ)`* when it has `n` vertices, is regular
of degree `k`, every adjacent pair has `ℓ` common neighbours, and every non-adjacent pair has `μ`.
The predicate is `CGraph.IsSRGWith` in `IsoGraph/Invariants.lean`, a thin wrapper around Mathlib's
`SimpleGraph.IsSRGWith`.

Seventeen of the twenty-eight parameter checks below are theorems rather than computations: the
rook, Kneser, triangular, Paley, complete bipartite and cocktail party entries come from the
infinite families `isSRGWith_rook`, `isSRGWith_kneser_two`, `isSRGWith_triangular`,
`isSRGWith_paley`, `isSRGWith_bipartite` and `isSRGWith_cocktailParty` of
`IsoGraph/Constructions.lean`, and `compl clebsch`, `schlafli`, `compl hoffmanSingleton` and
`compl higmanSims` from `isSRGWith_compl`.  Of the rest, `cycle 5`, `clebsch` and `shrikhande` are
checked by kernel `decide`; the eight largest sporadic graphs — `linesOnCubic`, the three Chang
graphs, `hoffmanSingleton`, `gewirtz`, `m22` and `higmanSims` — need `native_decide`.  The
predicate is decidable in `O(n³)` adjacency queries and the kernel does manage the smaller ones:
a `decide` on `linesOnCubic` takes about twenty-five seconds, on a Chang graph about thirty, and
on `hoffmanSingleton` several minutes.
That is a build-time price with no extra confidence attached, since the definitions are already
small and explicit, so they are left on `native_decide`.

Strongly regular graphs are the standard hard case for isomorphism testing — every vertex looks
exactly like every other one to any degree- or triangle-counting invariant — so they are also the
interesting inputs for the canonical labelling of `IsoGraph/Canon/`.  Two pairs here make that
concrete:

* `rook 4 4` and `shrikhande` both have parameters `(16, 6, 2, 2)`, and are not isomorphic;
* `triangular 8` and the three Chang graphs all have parameters `(28, 12, 6, 4)`, and are pairwise
  non-isomorphic.  Those four are *all* the graphs with those parameters, so the table below
  contains a complete classification.

Both facts are proved by computing canonical keys, i.e. by `CGraph.Enum.key_eq_iff`.

## The table

| graph                    | `n` | `k` | `ℓ` | `μ` |
| ------------------------ | --- | --- | --- | --- |
| `cycle 5`                |   5 |   2 |   0 |   1 |
| `bipartite 3 3`          |   6 |   3 |   0 |   3 |
| `cocktailParty 4`        |   8 |   6 |   4 |   6 |
| `rook 3 3`               |   9 |   4 |   1 |   2 |
| `petersen`               |  10 |   3 |   0 |   1 |
| `triangular 5`           |  10 |   6 |   3 |   4 |
| `paley 13`               |  13 |   6 |   2 |   3 |
| `kneser 6 2`             |  15 |   6 |   1 |   3 |
| `triangular 6`           |  15 |   8 |   4 |   4 |
| `clebsch`                |  16 |   5 |   0 |   2 |
| `rook 4 4`               |  16 |   6 |   2 |   2 |
| `shrikhande`             |  16 |   6 |   2 |   2 |
| `compl clebsch`          |  16 |  10 |   6 |   6 |
| `paley 17`               |  17 |   8 |   3 |   4 |
| `linesOnCubic`           |  27 |  10 |   1 |   5 |
| `schlafli`               |  27 |  16 |  10 |   8 |
| `triangular 8`           |  28 |  12 |   6 |   4 |
| `chang₁`, `chang₂`, `chang₃` | 28 | 12 | 6 | 4 |
| `paley 29`               |  29 |  14 |   6 |   7 |
| `hoffmanSingleton`       |  50 |   7 |   0 |   1 |
| `compl hoffmanSingleton` |  50 |  42 |  35 |  36 |
| `gewirtz`                |  56 |  10 |   0 |   2 |
| `m22`                    |  77 |  16 |   0 |   4 |
| `higmanSims`             | 100 |  22 |   0 |   6 |
| `compl higmanSims`       | 100 |  77 |  60 |  56 |
| `paley 101`              | 101 |  50 |  24 |  25 |

`SRG.table` collects them as data: each row carries the graph, the parameters and the proof.

## Evaluation cost

Everything here answers an adjacency query in constant or near-constant time:

* `paley q` reads a precomputed table of quadratic residues (`qrTable`);
* `hoffmanSingleton` is four divisions and a multiplication mod 5;
* `johnson`, `kneser` and `linesOnCubic` intersect two small `Finset`s;
* `shrikhande` is a Cayley graph on `ZMod 4 × ZMod 4`, i.e. a six-element list lookup;
* `gewirtz`, `m22` and `higmanSims` read the blocks of `S(3, 6, 22)` out of an array of 22-bit
  masks, so a query is one array access and one bitwise `and` or bit test.

## Not here yet

The three largest entries — `gewirtz`, `m22` and `higmanSims` — are the graphs of the Steiner
system `S(3, 6, 22)`, whose 77 blocks are written out in `wittBlocks` and checked by
`witt_steiner`.  Beyond them the next natural targets are the Hall–Janko graph
`(100, 36, 14, 12)` and the McLaughlin graph `(275, 112, 30, 56)`, and the general Latin-square
and Steiner block-graph families.
-/

namespace SRG

open CGraph CGraph.Enum

/-! ## The graphs

The families — `paley`, `johnson`/`triangular`, `kneser`, `rook`, `cocktailParty`, `foldedCube` —
live in `IsoGraph/Constructions.lean`.  What is left to define here are the sporadic ones. -/

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

instance : DecidableEq shrikhande.V := inferInstanceAs (DecidableEq (ZMod 4 × ZMod 4))

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

instance : DecidableEq linesOnCubic.V :=
  inferInstanceAs (DecidableEq (Fin 6 ⊕ Fin 6 ⊕ {s : Finset (Fin 6) // s.card = 2}))

/-- The Schläfli graph: 27 lines on a cubic surface, adjacent when they are *skew*.  The unique
strongly regular graph with parameters `(27, 16, 10, 8)`. -/
def schlafli : CGraph := compl linesOnCubic

instance : DecidableEq schlafli.V := inferInstanceAs (DecidableEq linesOnCubic.V)

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

instance : DecidableEq hoffmanSingleton.V := inferInstanceAs (DecidableEq (Fin 50))

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

instance : DecidableEq chang₁.V := inferInstanceAs (DecidableEq (triangular 8).V)
instance : DecidableEq chang₂.V := inferInstanceAs (DecidableEq (triangular 8).V)
instance : DecidableEq chang₃.V := inferInstanceAs (DecidableEq (triangular 8).V)

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

instance : DecidableEq gewirtz.V := inferInstanceAs (DecidableEq (Fin 56))

/-- The `M₂₂` graph: all 77 blocks of `S(3, 6, 22)`, adjacent when disjoint.  The unique
`(77, 16, 0, 4)` graph; its automorphism group is the Mathieu group `M₂₂` extended by an outer
automorphism. -/
def m22 : CGraph := ofRel (Fin 77) fun x y ↦ disjBlocks x.1 y.1

instance : DecidableEq m22.V := inferInstanceAs (DecidableEq (Fin 77))

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

instance : DecidableEq higmanSims.V := inferInstanceAs (DecidableEq (Fin 100))

/-! ## The parameters

Whatever can be, is proved: the rook, Kneser, triangular, Paley, complete bipartite and cocktail
party entries come from the infinite families of `IsoGraph/Constructions.lean`, and three more
from `isSRGWith_compl`.  What is left is `cycle 5`, `clebsch` and `shrikhande` by kernel `decide`,
and five large sporadic graphs by `native_decide`. -/

set_option maxRecDepth 4000 in
theorem cycle_five_srg : (cycle 5).IsSRGWith 5 2 0 1 := by decide

theorem bipartite_srg : (bipartite 3 3).IsSRGWith 6 3 0 3 := isSRGWith_bipartite 3

theorem cocktailParty_srg : (cocktailParty 4).IsSRGWith 8 6 4 6 := isSRGWith_cocktailParty 4

theorem rook_three_srg : (rook 3 3).IsSRGWith 9 4 1 2 := isSRGWith_rook 3

theorem petersen_srg : petersen.IsSRGWith 10 3 0 1 := isSRGWith_kneser_two 5

theorem triangular_five_srg : (triangular 5).IsSRGWith 10 6 3 4 :=
  isSRGWith_triangular 5 (by norm_num)

theorem paley_thirteen_srg : (paley 13).IsSRGWith 13 6 2 3 :=
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  isSRGWith_paley 13 (by norm_num)

theorem kneser_six_srg : (kneser 6 2).IsSRGWith 15 6 1 3 := isSRGWith_kneser_two 6

theorem triangular_six_srg : (triangular 6).IsSRGWith 15 8 4 4 :=
  isSRGWith_triangular 6 (by norm_num)

set_option maxRecDepth 100000 in
theorem clebsch_srg : clebsch.IsSRGWith 16 5 0 2 := by decide

theorem rook_four_srg : (rook 4 4).IsSRGWith 16 6 2 2 := isSRGWith_rook 4

set_option maxRecDepth 100000 in
theorem shrikhande_srg : shrikhande.IsSRGWith 16 6 2 2 := by decide

theorem compl_clebsch_srg : (compl clebsch).IsSRGWith 16 10 6 6 := isSRGWith_compl _ clebsch_srg

theorem paley_seventeen_srg : (paley 17).IsSRGWith 17 8 3 4 :=
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  isSRGWith_paley 17 (by norm_num)

theorem linesOnCubic_srg : linesOnCubic.IsSRGWith 27 10 1 5 := by native_decide

theorem schlafli_srg : schlafli.IsSRGWith 27 16 10 8 := isSRGWith_compl _ linesOnCubic_srg

theorem triangular_eight_srg : (triangular 8).IsSRGWith 28 12 6 4 :=
  isSRGWith_triangular 8 (by norm_num)

theorem chang₁_srg : chang₁.IsSRGWith 28 12 6 4 := by native_decide

theorem chang₂_srg : chang₂.IsSRGWith 28 12 6 4 := by native_decide

theorem chang₃_srg : chang₃.IsSRGWith 28 12 6 4 := by native_decide

theorem paley_twentynine_srg : (paley 29).IsSRGWith 29 14 6 7 :=
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  isSRGWith_paley 29 (by norm_num)

theorem hoffmanSingleton_srg : hoffmanSingleton.IsSRGWith 50 7 0 1 := by native_decide

theorem compl_hoffmanSingleton_srg : (compl hoffmanSingleton).IsSRGWith 50 42 35 36 :=
  isSRGWith_compl _ hoffmanSingleton_srg

theorem gewirtz_srg : gewirtz.IsSRGWith 56 10 0 2 := by native_decide

theorem m22_srg : m22.IsSRGWith 77 16 0 4 := by native_decide

theorem higmanSims_srg : higmanSims.IsSRGWith 100 22 0 6 := by native_decide

theorem compl_higmanSims_srg : (compl higmanSims).IsSRGWith 100 77 60 56 :=
  isSRGWith_compl _ higmanSims_srg

theorem paley_hundredone_srg : (paley 101).IsSRGWith 101 50 24 25 :=
  haveI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  isSRGWith_paley 101 (by norm_num)

/-- Strong regularity descends to `IsoGraph`, being an isomorphism invariant. -/
theorem petersen_srg_iso : IsoGraph.IsSRGWith (Quotient.mk _ petersen) 10 3 0 1 := petersen_srg

/-! ## Identifications and separations

Same parameters need not mean isomorphic, and different descriptions often do.  Where the two
graphs are already the same construction in disguise the isomorphism is written down; otherwise
the question is decided by the canonical key. -/

/-- `Paley(5)` is the 5-cycle.  Both are circulants on `Fin 5` — the nonzero squares mod `5` are
`{1, 4}`, which is `{±1}` — so the identity is already an isomorphism and the twenty-five
adjacency comparisons fit inside kernel `decide`. -/
theorem paley_five_eq_cycle : Nonempty (paley 5 ≃cg cycle 5) :=
  ⟨⟨Equiv.refl (Fin 5), fun {a b} ↦ by revert a b; decide⟩⟩

/-- `T(5)` is the complement of the Petersen graph — a special case of `johnsonTwoIso`, which
identifies `johnson n 2` with `compl (kneser n 2)` for every `n`. -/
theorem triangular_five_eq_compl_petersen : Nonempty (triangular 5 ≃cg compl petersen) :=
  ⟨johnsonTwoIso 5⟩

/-- `T(4)` is the octahedron `K_{2,2,2}`. -/
theorem triangular_four_eq_octahedron : Nonempty (triangular 4 ≃cg cocktailParty 3) := by
  rw [← key_eq_iff]; native_decide

/-- The Shrikhande graph is *not* the `4 × 4` rook's graph, though the two share the parameters
`(16, 6, 2, 2)`.  Together they are all the strongly regular graphs with those parameters. -/
theorem shrikhande_not_iso_rook : ¬Nonempty (shrikhande ≃cg rook 4 4) := by
  rw [← key_eq_iff]; native_decide

/-- `T(8)` and the three Chang graphs are pairwise non-isomorphic — a complete list of the
strongly regular graphs with parameters `(28, 12, 6, 4)`. -/
theorem changs_pairwise_not_iso :
    ([triangular 8, chang₁, chang₂, chang₃] : List CGraph).Pairwise
      fun G H ↦ ¬Nonempty (G ≃cg H) := by
  have h : (([triangular 8, chang₁, chang₂, chang₃] : List CGraph).map key).Pairwise (· ≠ ·) := by
    native_decide
  rw [List.pairwise_map] at h
  exact h.imp fun hne he ↦ hne (key_eq_iff.2 he)

/-! ## The table as data -/

/-- One row of the table: a graph, its parameters, and the proof that they are its parameters. -/
structure Entry where
  /-- What the graph is usually called. -/
  name : String
  /-- The graph. -/
  graph : CGraph
  /-- Number of vertices. -/
  n : ℕ
  /-- Degree of every vertex. -/
  k : ℕ
  /-- Common neighbours of an adjacent pair. -/
  ℓ : ℕ
  /-- Common neighbours of a distinct non-adjacent pair. -/
  μ : ℕ
  /-- The parameters are right. -/
  isSRG : graph.IsSRGWith n k ℓ μ

/-- Every strongly regular graph in this development, with its parameters. -/
def table : List Entry :=
  [ ⟨"C₅ = Paley(5)", cycle 5, 5, 2, 0, 1, cycle_five_srg⟩,
    ⟨"K₃,₃", bipartite 3 3, 6, 3, 0, 3, bipartite_srg⟩,
    ⟨"K₄ₓ₂ (cocktail party)", cocktailParty 4, 8, 6, 4, 6, cocktailParty_srg⟩,
    ⟨"3×3 rook = Paley(9)", rook 3 3, 9, 4, 1, 2, rook_three_srg⟩,
    ⟨"Petersen", petersen, 10, 3, 0, 1, petersen_srg⟩,
    ⟨"T(5)", triangular 5, 10, 6, 3, 4, triangular_five_srg⟩,
    ⟨"Paley(13)", paley 13, 13, 6, 2, 3, paley_thirteen_srg⟩,
    ⟨"Kneser K(6,2)", kneser 6 2, 15, 6, 1, 3, kneser_six_srg⟩,
    ⟨"T(6)", triangular 6, 15, 8, 4, 4, triangular_six_srg⟩,
    ⟨"Clebsch", clebsch, 16, 5, 0, 2, clebsch_srg⟩,
    ⟨"4×4 rook", rook 4 4, 16, 6, 2, 2, rook_four_srg⟩,
    ⟨"Shrikhande", shrikhande, 16, 6, 2, 2, shrikhande_srg⟩,
    ⟨"complement of Clebsch", compl clebsch, 16, 10, 6, 6, compl_clebsch_srg⟩,
    ⟨"Paley(17)", paley 17, 17, 8, 3, 4, paley_seventeen_srg⟩,
    ⟨"27 lines on a cubic", linesOnCubic, 27, 10, 1, 5, linesOnCubic_srg⟩,
    ⟨"Schläfli", schlafli, 27, 16, 10, 8, schlafli_srg⟩,
    ⟨"T(8)", triangular 8, 28, 12, 6, 4, triangular_eight_srg⟩,
    ⟨"Chang 1 (4K₂)", chang₁, 28, 12, 6, 4, chang₁_srg⟩,
    ⟨"Chang 2 (C₈)", chang₂, 28, 12, 6, 4, chang₂_srg⟩,
    ⟨"Chang 3 (C₃ ∪ C₅)", chang₃, 28, 12, 6, 4, chang₃_srg⟩,
    ⟨"Paley(29)", paley 29, 29, 14, 6, 7, paley_twentynine_srg⟩,
    ⟨"Hoffman–Singleton", hoffmanSingleton, 50, 7, 0, 1, hoffmanSingleton_srg⟩,
    ⟨"complement of Hoffman–Singleton", compl hoffmanSingleton, 50, 42, 35, 36,
      compl_hoffmanSingleton_srg⟩,
    ⟨"Gewirtz", gewirtz, 56, 10, 0, 2, gewirtz_srg⟩,
    ⟨"M₂₂", m22, 77, 16, 0, 4, m22_srg⟩,
    ⟨"Higman–Sims", higmanSims, 100, 22, 0, 6, higmanSims_srg⟩,
    ⟨"complement of Higman–Sims", compl higmanSims, 100, 77, 60, 56, compl_higmanSims_srg⟩,
    ⟨"Paley(101)", paley 101, 101, 50, 24, 25, paley_hundredone_srg⟩ ]

#guard table.length = 28

#guard table.map (fun e ↦ e.n) =
  [5, 6, 8, 9, 10, 10, 13, 15, 15, 16, 16, 16, 16, 17, 27, 27, 28, 28, 28, 28, 29, 50, 50, 56, 77,
    100, 100, 101]

/-- The parameters of any row satisfy the standard feasibility identity
`k (k - ℓ - 1) = (n - k - 1) μ` — counting, in two ways, the edges between the neighbours and the
non-neighbours of a vertex. -/
theorem param_eq (e : Entry) (hn : 0 < e.n) : e.k * (e.k - e.ℓ - 1) = (e.n - e.k - 1) * e.μ :=
  SimpleGraph.IsSRGWith.param_eq _ e.isSRG hn

end SRG
