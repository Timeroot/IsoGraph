import IsoGraph.Constructions
import IsoGraph.Enum

/-!
# A table of strongly regular graphs

A graph is *strongly regular with parameters `(n, k, ℓ, μ)`* when it has `n` vertices, is regular
of degree `k`, every adjacent pair has `ℓ` common neighbours, and every non-adjacent pair has `μ`.
The predicate is `CGraph.IsSRGWith` in `IsoGraph/Invariants.lean`, a thin wrapper around Mathlib's
`SimpleGraph.IsSRGWith`.

Nine of the rows below are theorems rather than computations: the rook, Kneser and triangular
entries come from the infinite families `isSRGWith_rook`, `isSRGWith_kneser_two` and
`isSRGWith_triangular` of `IsoGraph/Constructions.lean`, and `compl clebsch`, `schlafli` and
`compl hoffmanSingleton` from `isSRGWith_compl`.  Of the rest, everything up to seventeen
vertices is checked by kernel `decide`; only the eight largest still need `native_decide`, the
predicate being decidable in `O(n³)` adjacency queries.

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
| `paley 101`              | 101 |  50 |  24 |  25 |

`SRG.table` collects them as data: each row carries the graph, the parameters and the proof.

## Evaluation cost

Everything here answers an adjacency query in constant or near-constant time:

* `paley q` reads a precomputed table of quadratic residues;
* `hoffmanSingleton` is four divisions and a multiplication mod 5;
* `johnson`, `kneser` and `linesOnCubic` intersect two small `Finset`s;
* `shrikhande` is a Cayley graph on `ZMod 4 × ZMod 4`, i.e. a six-element list lookup.

## Not here yet

The Higman–Sims graph `(100, 22, 0, 6)`, the Gewirtz graph `(56, 10, 0, 2)` and the `M₂₂` graph
`(77, 16, 0, 4)` all want the Steiner system `S(3, 6, 22)`, which nothing in this development
builds yet.
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

/-! ## The parameters

Whatever can be, is proved: the rook, Kneser and triangular entries come from the infinite
families of `IsoGraph/Constructions.lean`, and three of the complements from `isSRGWith_compl`.
What is left — the sporadic graphs and the Paley graphs — is `O(n³)` adjacency queries, run by the
compiler rather than the kernel. -/

set_option maxRecDepth 4000 in
theorem cycle_five_srg : (cycle 5).IsSRGWith 5 2 0 1 := by decide

set_option maxRecDepth 8000 in
theorem bipartite_srg : (bipartite 3 3).IsSRGWith 6 3 0 3 := by decide

set_option maxRecDepth 20000 in
theorem cocktailParty_srg : (cocktailParty 4).IsSRGWith 8 6 4 6 := by decide

theorem rook_three_srg : (rook 3 3).IsSRGWith 9 4 1 2 := isSRGWith_rook 3

theorem petersen_srg : petersen.IsSRGWith 10 3 0 1 := isSRGWith_kneser_two 5

theorem triangular_five_srg : (triangular 5).IsSRGWith 10 6 3 4 :=
  isSRGWith_triangular 5 (by norm_num)

theorem paley_thirteen_srg : (paley 13).IsSRGWith 13 6 2 3 := by native_decide

theorem kneser_six_srg : (kneser 6 2).IsSRGWith 15 6 1 3 := isSRGWith_kneser_two 6

theorem triangular_six_srg : (triangular 6).IsSRGWith 15 8 4 4 :=
  isSRGWith_triangular 6 (by norm_num)

set_option maxRecDepth 100000 in
theorem clebsch_srg : clebsch.IsSRGWith 16 5 0 2 := by decide

theorem rook_four_srg : (rook 4 4).IsSRGWith 16 6 2 2 := isSRGWith_rook 4

set_option maxRecDepth 100000 in
theorem shrikhande_srg : shrikhande.IsSRGWith 16 6 2 2 := by decide

theorem compl_clebsch_srg : (compl clebsch).IsSRGWith 16 10 6 6 := isSRGWith_compl _ clebsch_srg

theorem paley_seventeen_srg : (paley 17).IsSRGWith 17 8 3 4 := by native_decide

theorem linesOnCubic_srg : linesOnCubic.IsSRGWith 27 10 1 5 := by native_decide

theorem schlafli_srg : schlafli.IsSRGWith 27 16 10 8 := isSRGWith_compl _ linesOnCubic_srg

theorem triangular_eight_srg : (triangular 8).IsSRGWith 28 12 6 4 :=
  isSRGWith_triangular 8 (by norm_num)

theorem chang₁_srg : chang₁.IsSRGWith 28 12 6 4 := by native_decide

theorem chang₂_srg : chang₂.IsSRGWith 28 12 6 4 := by native_decide

theorem chang₃_srg : chang₃.IsSRGWith 28 12 6 4 := by native_decide

theorem paley_twentynine_srg : (paley 29).IsSRGWith 29 14 6 7 := by native_decide

theorem hoffmanSingleton_srg : hoffmanSingleton.IsSRGWith 50 7 0 1 := by native_decide

theorem compl_hoffmanSingleton_srg : (compl hoffmanSingleton).IsSRGWith 50 42 35 36 :=
  isSRGWith_compl _ hoffmanSingleton_srg

theorem paley_hundredone_srg : (paley 101).IsSRGWith 101 50 24 25 := by native_decide

/-- Strong regularity descends to `IsoGraph`, being an isomorphism invariant. -/
theorem petersen_srg_iso : IsoGraph.IsSRGWith (Quotient.mk _ petersen) 10 3 0 1 := petersen_srg

/-! ## Identifications and separations

Same parameters need not mean isomorphic, and different descriptions often do.  Both directions
are decided by the canonical key. -/

/-- `Paley(5)` is the 5-cycle. -/
theorem paley_five_eq_cycle : Nonempty (paley 5 ≃cg cycle 5) := by
  rw [← key_eq_iff]; native_decide

/-- `T(5)` is the complement of the Petersen graph. -/
theorem triangular_five_eq_compl_petersen : Nonempty (triangular 5 ≃cg compl petersen) := by
  rw [← key_eq_iff]; native_decide

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
    ⟨"Paley(101)", paley 101, 101, 50, 24, 25, paley_hundredone_srg⟩ ]

#guard table.length = 24

#guard table.map (fun e ↦ e.n) =
  [5, 6, 8, 9, 10, 10, 13, 15, 15, 16, 16, 16, 16, 17, 27, 27, 28, 28, 28, 28, 29, 50, 50, 101]

/-- The parameters of any row satisfy the standard feasibility identity
`k (k - ℓ - 1) = (n - k - 1) μ` — counting, in two ways, the edges between the neighbours and the
non-neighbours of a vertex. -/
theorem param_eq (e : Entry) (hn : 0 < e.n) : e.k * (e.k - e.ℓ - 1) = (e.n - e.k - 1) * e.μ :=
  SimpleGraph.IsSRGWith.param_eq _ e.isSRG hn

end SRG
