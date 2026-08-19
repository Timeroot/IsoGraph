import IsoGraph.Enum.Decide
import IsoGraph.Containment

/-!
# Theorems proved by exhaustion

What `small_graphs` is for.  Every statement below is about *all* graphs of some small order, and
every proof is the same: enumerate the isomorphism classes and check.  None of them is a special
case of anything else in this development, and most have no short proof by hand — which is the
point.  A brute-force check is a proof, and at these orders it is a cheap one.

| theorem | order | says |
| --- | --- | --- |
| `isVertexTransitive_iff_five_dvd_E` | 5 | vertex-transitivity is visible in the edge count |
| `not_nodup_degSequence` | 6 | two vertices have the same degree |
| `isConnected_or_compl_isConnected` | 6 | a graph and its complement are not both disconnected |
| `isSelfComplementary_iff_of_le_five` | ≤ 5 | the five self-complementary graphs |
| `isRegularWith_three_iff` | 6 | the two cubic graphs |
| `eq_bipartite_of_triangle_free` | 6 | Andrásfai: triangle-free with `δ ≥ 3` forces `K₃,₃` |
| `ramsey_three_three` | 6 | `R(3,3) ≤ 6`, with `C₅` for the lower bound |
| `E_le_six_of_triangle_free` | 5 | Mantel: `⌊25/4⌋ = 6` |
| `cycle_subgraph_of_isVertexTransitive` | 6 | Lovász's conjecture, checked |
| `complete_four_minor_of_minDeg` | 6 | minimum degree three forces a `K₄` minor |

The last five go through the containment searches of `IsoGraph/Containment/`, decided on the
quotient at the end of `Containment/Algorithms/Cached.lean`.  Those are exponential in the
pattern, and the pattern here is a triangle, a `C₆` or a `K₄`, so what costs is the enumeration.

Which is the whole story of what this module costs: about ten minutes of CPU, and roughly
forty-five seconds of that is one `enumerateIso 6`, rebuilt once for each of the six theorems that
needs it.  Nothing is memoised across a `native_decide`.  Combining those six into a single
conjunction would pay for the enumeration once, at the price of saying six things in one theorem;
building the library with `precompileModules` would cut the whole file by two orders of magnitude,
at the price of what that does to every other build.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ## Invariants against invariants -/

/-- **On five vertices, vertex-transitivity is an edge count.**  A connected graph on five
vertices with no vertex of degree one is vertex-transitive exactly when five divides its number
of edges — the two witnesses being `C₅` with five edges and `K₅` with ten.

There is a proof by hand: a vertex-transitive graph is regular, so `5 ∣ 2|E|` and hence `5 ∣ |E|`;
conversely `5 ∣ |E|` with `2 ≤ δ` leaves `|E| ∈ {5, 10}`, and a connected graph on five vertices
with five edges and no degree-one vertex is `C₅`.  It is not a proof anyone would enjoy checking,
and the enumeration settles it in one line. -/
theorem isVertexTransitive_iff_five_dvd_E :
    ∀ G : IsoGraph, G.V = 5 → G.IsConnected → 2 ≤ G.minDeg →
      (G.IsVertexTransitive ↔ 5 ∣ G.E) := by
  small_graphs

/-- **Every graph on six vertices has two vertices of the same degree.**  The pigeonhole argument
is the standard one — the degrees lie in `{0, …, 5}` and `0` and `5` cannot both occur — and this
is the instance of it at `n = 6`. -/
theorem not_nodup_degSequence : ∀ G : IsoGraph, G.V = 6 → ¬ G.degSequence.Nodup := by
  small_graphs

/-- **A graph and its complement are not both disconnected**, at `n = 6`. -/
theorem isConnected_or_compl_isConnected :
    ∀ G : IsoGraph, G.V = 6 → (G.IsConnected ∨ Gᶜ.IsConnected) := by
  small_graphs

/-! ## Classifications

Three statements of the form "these are all of them", each an equality of isomorphism classes and
so decided by the canonical labelling. -/

/-- **The self-complementary graphs on at most five vertices** are `K₀`, `K₁`, `P₄`, `C₅` and the
bull.  A self-complementary graph has `n ≡ 0, 1 (mod 4)`, which is why `n = 2, 3` are missing;
that `n = 4` and `n = 5` contribute one and two is not something the congruence tells you. -/
theorem isSelfComplementary_iff_of_le_five :
    ∀ G : IsoGraph, G.V ≤ 5 →
      (G.IsSelfComplementary ↔
        G = empty 0 ∨ G = complete 1 ∨ G = path 4 ∨ G = cycle 5 ∨ G = cyclePendant 3 [1, 1]) := by
  small_graphs

/-- **The cubic graphs on six vertices** are `K₃,₃` and the triangular prism. -/
theorem isRegularWith_three_iff :
    ∀ G : IsoGraph, G.V = 6 → (G.IsRegularWith 3 ↔ G = bipartite 3 3 ∨ G = prism 3) := by
  small_graphs

/-- **Andrásfai at `n = 6`**: a triangle-free graph on six vertices with minimum degree three is
`K₃,₃`.  Minimum degree three gives at least nine edges, Mantel caps a triangle-free graph on six
vertices at nine, and `K₃,₃` is the unique extremal graph — three facts, none of them free, and
the enumeration needs none of them. -/
theorem eq_bipartite_of_triangle_free :
    ∀ G : IsoGraph, G.V = 6 → 3 ≤ G.minDeg → ¬ (complete 3 ≤ₛ G) → G = bipartite 3 3 := by
  small_graphs

/-! ## Containment

Each of these asks for a subgraph or a minor of every graph on the list, so each is a few hundred
containment searches. -/

/-- **`R(3, 3) ≤ 6`**: in any two-colouring of the edges of `K₆` — that is, in any graph on six
vertices and its complement — one side contains a triangle. -/
theorem ramsey_three_three :
    ∀ G : IsoGraph, G.V = 6 → (complete 3 ≤ₛ G ∨ complete 3 ≤ₛ Gᶜ) := by
  small_graphs

/-- **`R(3, 3) > 5`**: `C₅` is its own complement and has no triangle, so five vertices are not
enough. -/
theorem ramsey_three_three_lower :
    ∃ G : IsoGraph, G.V = 5 ∧ ¬ (complete 3 ≤ₛ G) ∧ ¬ (complete 3 ≤ₛ Gᶜ) :=
  ⟨cycle 5, rfl, by native_decide, by native_decide⟩

/-- **Mantel at `n = 5`**: a triangle-free graph on five vertices has at most `⌊25/4⌋ = 6` edges.
`K₂,₃` attains it. -/
theorem E_le_six_of_triangle_free :
    ∀ G : IsoGraph, G.V = 5 → ¬ (complete 3 ≤ₛ G) → G.E ≤ 6 := by
  small_graphs

/-- **Lovász's conjecture at `n = 6`**: every connected vertex-transitive graph on six vertices
has a Hamiltonian cycle, spelled here as "`C₆` is a subgraph".  The conjecture — that a connected
vertex-transitive graph is Hamiltonian apart from `K₂`, the Petersen and Coxeter graphs, and the
two graphs got from those two by replacing every vertex with a triangle — is open.  `K₂` is why
the order has to be named and the hypotheses alone will not do. -/
theorem cycle_subgraph_of_isVertexTransitive :
    ∀ G : IsoGraph, G.V = 6 → G.IsConnected → G.IsVertexTransitive → cycle 6 ≤ₛ G := by
  small_graphs

/-- **Minimum degree three forces a `K₄` minor**, at `n = 6`.  This is a theorem for all `n`, by
induction on the number of vertices; the base of that induction is small enough to be this. -/
theorem complete_four_minor_of_minDeg :
    ∀ G : IsoGraph, G.V = 6 → 3 ≤ G.minDeg → complete 4 ≤ₘ G := by
  small_graphs

end IsoGraph
