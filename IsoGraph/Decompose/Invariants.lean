import IsoGraph.Decompose.Tactic
import IsoGraph.SmallGraphs
import IsoGraph.SmallGraphs.SolidValues

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Computing an invariant from a decomposition

`decompose_graph` turns a graph into a formula in named graphs, disjoint unions, joins,
complements and products.  This file uses it for the invariants that are hard to compute directly:
`compute_invariant G` decomposes `G` and then evaluates the invariant in the goal by the
compositional rules, so that an independence number nobody could `decide` becomes a maximum of
two numerals.

    example : IsoGraph.indepNum ⟦(CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ⟧ = 10 := by
      compute_invariant ((CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ)

The four co-NP invariants — `indepNum`, `cliqueNum`, `chromNum`, `cliqueCoverNum` — are the point
of the exercise, since each of them is an exponential search on the adjacency table and none of
them is `decide`-able past a dozen vertices.  All four are compositional in the same way: the
disjoint union, the join and the complement have unconditional rules, the cartesian product has
Sabidussi's theorem for `chromNum` and `cliqueNum`, and the lexicographic and tensor products have
rules for the clique and independence numbers.  The tactic is invariant-agnostic — it also
computes `V`, `E`, `numComponents`, `matchNum`, the girth and the domination number `domNum`, and
by Gallai's identity `coverNum_eq` the vertex cover number rides along with the independence
number.  Two invariants come in through the line graph: the independence number of `L(G)` is the
matching number of `G` and its chromatic number is the chromatic index, so a graph whose line
graph the atlas can name gets those for free.  The chromatic index and the matching number also compose over a
disjoint union directly, by `edgeChromNum_disjUnion` and `matchNum_disjUnion`, and the atoms
below give them values on the same families the four hard invariants get.  So does the girth,
by `girth_disjUnion` — a cycle of `G ⊕ H` lives on one side, so the shortest one is the shorter
of the two sides' shortest, with the `0`-for-acyclic convention handled by an `if`.

## The two levels

The values live on both levels of the library and the tactic has to visit both.  A family — the
cycles, the complete graphs, the Kneser graphs — carries its invariants as `IsoGraph` theorems,
while a graph named by an adjacency table — the solids, the cages, the small graphs — carries them
as `CGraph` theorems, since that is where the SAT witnesses of `SmallGraphs/SolidValues.lean` are
proved.  So the tactic first pushes the class inward with the `isoTransfer` bridges *reversed*,
turning `⟦A ∇g B⟧` into `⟦A⟧ ∇g ⟦B⟧` and `⟦CGraph.cycle 7⟧` into `IsoGraph.cycle 7`, and then
simplifies: the compositional rules fire on the `IsoGraph` formula, the families' values fire on
the lifted atoms, and an atom with no `IsoGraph` name — `⟦NamedGraphs.dodecahedron⟧` — is carried
back down by `indepNum_mk` and met by its `CGraph` theorem there.

Two atoms are lifted on purpose and two are not.  `mycielskian` is, because the Mycielskian raises
the chromatic number by one and the atlas hands back `NamedGraphs.grotzsch`, which is that
construction on the pentagon.  `completeMultipartite` is, because that is what a Turán graph
unfolds to.  `gp` and `circulant` are not: the atlas prefers a name to a family, so `gp 10 2` only
ever appears when the graph really is the dodecahedron, and lifting it would step over the values
proved for that name.

## What it knows

Every atom the decomposition can produce whose invariants are in the library.  Four lemmas below
put awkwardly-shaped rules into a form `simp` can use: the parity-dependent chromatic number of a
cycle and chromatic index of a cycle and of a complete graph fire on a numeral rather than on
`2 * m + 3`, and the domination number of a join becomes one value with an `if` instead of two
case lemmas.

What it does not know it leaves alone, as `H.indepNum` for that `H`.  The gaps worth naming are
the graphs the atlas cannot describe at all, which come back as `ofEdges`; the independence number
of a cartesian product, which is not determined by the factors; and the chromatic number of a
Kneser graph `K(n, k)` with `n ≥ 2k + 2` and `k ≥ 3`, where the full Lovász–Kneser theorem would
be needed — the library proves the cases `k = 2` and `n ≤ 2k + 1`, which `chromNum_kneser_of_le`
and `chromNum_kneser_two` put in numeral-friendly shape, and the single instance `K(8, 3)`, whose
lower bound is a SAT refutation.  The domination number composes over
disjoint unions and joins and has a value for most of the atoms, but not for the ladders and prisms
beyond the seven or eight rungs of `SmallGraphs/Brackets.lean`, nor for a Paley graph past
`q = 17`, and over a cartesian product it is Vizing's conjecture, so there is only the inequality
`domNum_cartesianProduct_le` and nothing to evaluate.

Called with no argument, `compute_invariant` decomposes every closed graph in the goal, which is
the form to use when the goal names several.
-/

set_option autoImplicit false

namespace IsoGraph

/-- **The chromatic number of a cycle**, in a shape that fires on a numeral.  `chromNum_cycle_odd`
and `chromNum_cycle_even` are stated of `2 * m + 3` and `2 * m + 2`, and `simp` cannot match either
against `cycle 7`; an offset from a numeral it can. -/
theorem chromNum_cycle_ite (n : ℕ) :
    (cycle (n + 3)).chromNum = if n % 2 = 0 then 3 else 2 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m + 3 = 2 * m + 3 by ring, chromNum_cycle_odd,
      if_pos (by omega : (m + m) % 2 = 0)]
  · subst hm
    rw [show 2 * m + 1 + 3 = 2 * (m + 1) + 2 by ring, chromNum_cycle_even,
      if_neg (by omega : ¬ (2 * m + 1) % 2 = 0)]

/-- **The chromatic index of a complete graph**, in a shape that fires on a numeral: `n - 1`
colours for an even order, `n` for an odd one. -/
theorem edgeChromNum_complete_ite (n : ℕ) :
    (complete (n + 2)).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 :=
  edgeChromNum_complete n

/-- **The chromatic index of a cycle**, in a shape that fires on a numeral.  A cycle is
`2`-regular, so Vizing leaves only two and three, and it is three exactly for the odd cycles;
`edgeChromNum_cycle_even` and `edgeChromNum_cycle_odd` are stated of `2 * m + 4` and `2 * m + 3`,
which `simp` cannot match against `cycle 7`. -/
theorem edgeChromNum_cycle_ite (n : ℕ) :
    (cycle (n + 3)).edgeChromNum = if n % 2 = 0 then 3 else 2 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m + 3 = 2 * m + 3 by ring, edgeChromNum_cycle_odd,
      if_pos (by omega : (m + m) % 2 = 0)]
  · subst hm
    rw [show 2 * m + 1 + 3 = 2 * m + 4 by ring, edgeChromNum_cycle_even,
      if_neg (by omega : ¬ (2 * m + 1) % 2 = 0)]

/-- **The domination number of a join**, as a value rather than as a pair of case lemmas.  One
vertex dominates `G ∇ H` exactly when one side has a universal vertex, and a vertex from each side
always dominates, so there is nothing else it can be. -/
theorem domNum_join_ite {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).domNum = if G.domNum = 1 ∨ H.domNum = 1 then 1 else 2 := by
  split
  · next h => exact (domNum_join_eq_one_iff G H).2 h
  · next h =>
    push Not at h
    exact domNum_join_eq_two hG hH h.1 h.2

end IsoGraph

namespace CGraph.Decompose

/-- **Compute an invariant of a graph from its decomposition.**

    compute_invariant ((CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ)

decomposes the graph with `decompose_graph` and evaluates the invariant of the resulting formula:
the independence, clique, chromatic and clique cover numbers, and also the order, the size and the
number of components.  The decomposition is checked by the kernel and the rules are theorems, so
the answer is a proof and not a computation on the adjacency table — which is the point, since
these are the invariants no adjacency table of interesting size will give up to `decide`. -/
syntax (name := computeInvariant) "compute_invariant" (ppSpace term)? : tactic

macro_rules
  | `(tactic| compute_invariant $[$t?]?) =>
    `(tactic|
      (decompose_graph $[$t?]?
       try simp only [← IsoGraph.disjUnion_mk, ← IsoGraph.join_mk, ← IsoGraph.compl_mk,
         ← IsoGraph.cartesianProduct_mk, ← IsoGraph.tensorProduct_mk,
         ← IsoGraph.strongProduct_mk, ← IsoGraph.lexProduct_mk, ← IsoGraph.mycielskian_mk,
         ← IsoGraph.empty_def, ← IsoGraph.complete_def, ← IsoGraph.path_def,
         ← IsoGraph.cycle_def, ← IsoGraph.star_def, ← IsoGraph.wheel_def,
         ← IsoGraph.hypercube_def, ← IsoGraph.paley_def, ← IsoGraph.bipartite_def,
         ← IsoGraph.kneser_def, ← IsoGraph.johnson_def, ← IsoGraph.completeMultipartite_def]
       try simp [IsoGraph.chromNum_cartesianProduct, IsoGraph.cliqueNum_cartesianProduct,
         IsoGraph.chromNum_cycle_ite, IsoGraph.edgeChromNum_complete_ite,
         IsoGraph.edgeChromNum_cycle_ite, IsoGraph.edgeChromNum_ladder,
         IsoGraph.edgeChromNum_prism, IsoGraph.edgeChromNum_crown,
         IsoGraph.edgeChromNum_cocktailParty, IsoGraph.edgeChromNum_doubleStar,
         IsoGraph.edgeChromNum_grotzsch, IsoGraph.edgeChromNum_hypercube,
         IsoGraph.matchNum_wheel, IsoGraph.matchNum_book, IsoGraph.matchNum_rook,
         IsoGraph.girth_disjUnion,
         IsoGraph.indepNum_triangular, IsoGraph.chromNum_triangular,
         IsoGraph.cliqueCoverNum_triangular, IsoGraph.indepNum_crown,
         ← IsoGraph.compl_cocktailParty, IsoGraph.indepNum_kneser,
         IsoGraph.chromNum_kneser_of_le, IsoGraph.chromNum_kneser_of_lt,
         IsoGraph.chromNum_kneser_two, IsoGraph.chromNum_kneser_eight_three,
         IsoGraph.domNum_disjUnion, IsoGraph.domNum_join_ite,
         IsoGraph.domNum_empty,
         IsoGraph.domNum_complete, IsoGraph.domNum_star,
         IsoGraph.domNum_wheel, IsoGraph.domNum_fan, IsoGraph.domNum_book,
         IsoGraph.domNum_cocktailParty, IsoGraph.domNum_rook, IsoGraph.domNum_bipartite,
         IsoGraph.domNum_triangular, IsoGraph.domNum_turan, IsoGraph.domNum_doubleStar,
         IsoGraph.domNum_johnson_one, IsoGraph.domNum_kneser_of_lt,
         IsoGraph.domNum_hypercube_three,
         IsoGraph.domNum_hypercube_four, IsoGraph.domNum_kneser_two, IsoGraph.domNum_petersen,
         IsoGraph.domNum_grotzsch, IsoGraph.domNum_mycielskian]
       all_goals try norm_num [Nat.choose]))

end CGraph.Decompose

/-! ## Examples -/

/-- The complement of four disjoint `K₁₀`s is the complete four-partite graph on forty vertices,
whose independence number is ten.  Nothing decides an independence number on forty vertices; the
decomposition turns it into `max` of four tens. -/
example : IsoGraph.indepNum (Quotient.mk CGraph.isoSetoid
    ((CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ))
      = 10 := by
  compute_invariant
    ((CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ)

/-- **A minimum vertex cover of the same forty vertices has thirty of them.**  Gallai's identity
turns the cover number into the order minus the independence number, and the decomposition
supplies both. -/
example : IsoGraph.coverNum (Quotient.mk CGraph.isoSetoid
    ((CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ))
      = 30 := by
  compute_invariant
    ((CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10 ⊕g CGraph.complete 10)ᶜ)

/-- A Turán graph is perfect, and here is one instance of it: the chromatic number and the clique
number of `T(12, 4)` agree.  Both sides of the goal mention the graph, and `decompose_graph`
rewrites both, so one call settles the equation. -/
example : IsoGraph.chromNum (Quotient.mk CGraph.isoSetoid (CGraph.turan 12 4))
    = IsoGraph.cliqueNum (Quotient.mk CGraph.isoSetoid (CGraph.turan 12 4)) := by
  compute_invariant (CGraph.turan 12 4)

/-- **The Grötzsch graph needs four colours.**  The atlas recognises the adjacency table as the
Mycielskian of the pentagon, and then the chromatic number is the pentagon's plus one. -/
example : IsoGraph.chromNum (Quotient.mk CGraph.isoSetoid (CGraph.mycielskian (CGraph.cycle 5)))
    = 4 := by
  compute_invariant (CGraph.mycielskian (CGraph.cycle 5))

/-- **The chromatic index of `K₅` is five**, computed as the chromatic number of its line graph:
the atlas recognises `L(K₅)` as the triangular graph `T(5)`, whose chromatic number is by
definition the chromatic index of `K₅`, and Vizing's theorem for complete graphs finishes it. -/
example : IsoGraph.chromNum (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph (CGraph.complete 5)))
    = 5 := by
  compute_invariant (CGraph.lineGraph (CGraph.complete 5))

/-- **The matching number of `K₅` is two**, by the other reading of the same line graph: an
independent set of `L(G)` is a matching of `G`, and the independence number of the triangular
graph `T(n)` is `⌊n/2⌋`. -/
example : IsoGraph.indepNum (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph (CGraph.complete 5)))
    = 2 := by
  compute_invariant (CGraph.lineGraph (CGraph.complete 5))

/-- The complement of the Petersen graph is the triangular graph `T(5)`, whose ten vertices are
the edges of `K₅`; a clique cover of it is a proper edge colouring of `K₅`, so it takes three
cliques for the ten vertices — a partition into three perfect matchings does not exist, and the
number is the chromatic number of the Kneser graph the other way round. -/
example : IsoGraph.cliqueCoverNum (Quotient.mk CGraph.isoSetoid CGraph.petersenᶜ) = 3 := by
  compute_invariant CGraph.petersenᶜ

/-- **Blowing up a cycle multiplies its independence number.**  The lexicographic product of `C₇`
with an empty graph on two vertices is the seven-cycle with each vertex doubled, and its
independence number is `2 · α(C₇) = 6`. -/
example : IsoGraph.indepNum (Quotient.mk CGraph.isoSetoid (CGraph.cycle 7 ·g CGraph.empty 2))
    = 6 := by
  compute_invariant (CGraph.cycle 7 ·g CGraph.empty 2)

/-- **Sabidussi's theorem at work**: the chromatic number of a cartesian product is the larger of
the two, so the torus `C₄ □ C₅` needs three colours because the odd cycle does.  The tactic has to
discharge the nonemptiness side conditions of the rule, which it does from the orders of the
factors. -/
example : IsoGraph.chromNum (Quotient.mk CGraph.isoSetoid (CGraph.cycle 4 □g CGraph.cycle 5))
    = 3 := by
  compute_invariant (CGraph.cycle 4 □g CGraph.cycle 5)

/-- A clique in `P₄ · K₂` is a clique of `P₄` with both copies of each of its vertices, so the
clique number doubles. -/
example : IsoGraph.cliqueNum (Quotient.mk CGraph.isoSetoid (CGraph.path 4 ·g CGraph.complete 2))
    = 4 := by
  compute_invariant (CGraph.path 4 ·g CGraph.complete 2)

/-- **The bipartite double cover of a bipartite graph falls apart.**  The tensor product of the
cube with `K₂` is two cubes, which the decomposition finds and the count of components confirms. -/
example : IsoGraph.numComponents
    (Quotient.mk CGraph.isoSetoid (CGraph.hypercube 3 ⊗g CGraph.complete 2)) = 2 := by
  compute_invariant (CGraph.hypercube 3 ⊗g CGraph.complete 2)

/-- Counting works the same way: the Grötzsch graph has twenty edges, by the rule for the
Mycielskian rather than by counting them. -/
example : IsoGraph.E (Quotient.mk CGraph.isoSetoid (CGraph.mycielskian (CGraph.cycle 5)))
    = 20 := by
  compute_invariant (CGraph.mycielskian (CGraph.cycle 5))

/-- A named atom inside a formula: the dodecahedron's independence number is eight — a SAT
refutation and a witness, proved once in `SmallGraphs/SolidValues.lean` — and adding a disjoint
triangle adds one. -/
example : IsoGraph.indepNum
    (Quotient.mk CGraph.isoSetoid (CGraph.gp 10 2 ⊕g CGraph.complete 3)) = 9 := by
  compute_invariant (CGraph.gp 10 2 ⊕g CGraph.complete 3)

/-- **A domination number on twenty-four vertices.**  Dominating a disjoint union means dominating
each piece, `γ(L₅) = 3` is a bracket closed in `SmallGraphs/Brackets.lean` and `γ(K₄) = 1`, so the
answer is four — against a search over `2 ^ 24` sets. -/
example : IsoGraph.domNum (Quotient.mk CGraph.isoSetoid (CGraph.ladder 5 ⊕g CGraph.complete 4))
    = 4 := by
  compute_invariant (CGraph.ladder 5 ⊕g CGraph.complete 4)

/-- **The Lovász–Kneser theorem for pairs, applied.**  `χ(K(6, 2)) = 4` is the first value of
`chromNum_kneser_two` that the fractional bound cannot reach, and the tactic reads it off the
atlas' recognition of the adjacency table. -/
example : IsoGraph.chromNum (Quotient.mk CGraph.isoSetoid (CGraph.kneser 6 2)) = 4 := by
  compute_invariant (CGraph.kneser 6 2)

/-- **The chromatic index of `K₆` is five**, the same theorem read three identifications away: the
line graph of `K₆` is the triangular graph `T(6)`, whose clique cover number is the chromatic
number of its complement `K(6, 2)`. -/
example : IsoGraph.cliqueCoverNum
    (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph (CGraph.complete 6))) = 4 := by
  compute_invariant (CGraph.lineGraph (CGraph.complete 6))

/-- **Two graphs in one goal.**  Called with no argument, the tactic decomposes every closed graph
the goal mentions: here the six-rung prism and the seven-rung ladder, each with its own bracket. -/
example : IsoGraph.domNum (Quotient.mk CGraph.isoSetoid (CGraph.prism 6))
    + IsoGraph.domNum (Quotient.mk CGraph.isoSetoid (CGraph.ladder 7)) = 8 := by
  compute_invariant

/-- The tactic is not tied to the four hard invariants: a matching number composes over a disjoint
union like everything else, and `ν(C₇) = 3` and `ν(K₆) = 3` are table entries. -/
example : IsoGraph.matchNum (Quotient.mk CGraph.isoSetoid (CGraph.cycle 7 ⊕g CGraph.complete 6))
    = 6 := by
  compute_invariant (CGraph.cycle 7 ⊕g CGraph.complete 6)

/-- **A join takes one vertex or two.**  Neither pentagon has a universal vertex, so the join of
two of them needs one vertex from each side; `domNum_join_ite` says exactly that, and the tactic
discharges the two nonemptiness conditions from the orders. -/
example : IsoGraph.domNum (Quotient.mk CGraph.isoSetoid (CGraph.cycle 5 ∇g CGraph.cycle 5))
    = 2 := by
  compute_invariant (CGraph.cycle 5 ∇g CGraph.cycle 5)

/-- **A chromatic index over a disjoint union.**  `χ'` is the maximum of the two sides, and each
side is a parity case: the seven-cycle is odd, so `χ'(C₇) = 3`, and `K₆` has even order, so
`χ'(K₆) = 5`.  Both are stated of `2 * m + 3` in their home files and neither matches a numeral;
`edgeChromNum_cycle_ite` and `edgeChromNum_complete_ite` are what let `simp` see them. -/
example : IsoGraph.edgeChromNum
    (Quotient.mk CGraph.isoSetoid (CGraph.cycle 7 ⊕g CGraph.complete 6)) = 5 := by
  compute_invariant (CGraph.cycle 7 ⊕g CGraph.complete 6)

/-- **The chromatic index of a prism is three**, whatever the number of rungs — a cubic graph of
class one.  The decomposition hands back `path 6 □g complete 2`, which is the prism by
definition, and `edgeChromNum_prism` fires on it. -/
example : IsoGraph.edgeChromNum (Quotient.mk CGraph.isoSetoid (CGraph.prism 6)) = 3 := by
  compute_invariant (CGraph.prism 6)

/-- **A matching number the tables do not hold.**  `wheel 9` is a hub over `C₉`, ten vertices, and
it has a perfect matching: `matchNum_wheel` gives five.  The disjoint rule adds the four edges of
a maximum matching of `K₉`. -/
example : IsoGraph.matchNum
    (Quotient.mk CGraph.isoSetoid (CGraph.wheel 9 ⊕g CGraph.complete 9)) = 9 := by
  compute_invariant (CGraph.wheel 9 ⊕g CGraph.complete 9)

/-- **The girth of a disjoint union**, which is `girth_disjUnion`: the shorter of the two, with an
acyclic side skipped rather than minimised over.  Here `K₃` has girth three and the Petersen graph
— which is what `kneser 5 2` is — has girth five. -/
example : IsoGraph.girth
    (Quotient.mk CGraph.isoSetoid (CGraph.complete 3 ⊕g CGraph.kneser 5 2)) = 3 := by
  compute_invariant (CGraph.complete 3 ⊕g CGraph.kneser 5 2)

/-- **A forest has no girth at all.**  Two trees make an acyclic graph, and the convention is `0`;
both `if`s fire and there is no `min` to take. -/
example : IsoGraph.girth (Quotient.mk CGraph.isoSetoid (CGraph.path 6 ⊕g CGraph.star 5)) = 0 := by
  compute_invariant (CGraph.path 6 ⊕g CGraph.star 5)
