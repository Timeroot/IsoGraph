import IsoGraph.Decompose.Tactic
import IsoGraph.Spectrum

/-!
# Computing a Laplacian spectrum

`decompose_graph` turns a graph into a formula in named graphs, disjoint unions, joins,
complements and products.  This file uses it: `compute_lapSpectrum G` decomposes `G` and then
rewrites the spectrum of the formula with the identities of `IsoGraph/Spectrum.lean`, leaving the
eigenvalues of `G` in the goal as an explicit multiset of real numbers.

    example : IsoGraph.lapSpectrum ⟦(CGraph.path 3 ⊕g CGraph.complete 2)ᶜ⟧
        = 0 ::ₘ 5 ::ₘ 2 ::ₘ 3 ::ₘ {4} := by
      compute_lapSpectrum ((CGraph.path 3 ⊕g CGraph.complete 2)ᶜ)

The Laplacian is the right spectrum for this: `lapSpectrum_disjUnion`, `lapSpectrum_join` and
`lapSpectrum_compl` compute it for the three operations the decomposition uses, and the last two
without any hypothesis on the arguments.  The adjacency spectrum has no such rule — the spectrum
of a join is determined by the factors' only when they are regular — so the same pipeline stops at
the first join.

## What it knows

Every atom the decomposition can produce whose Laplacian spectrum is in the library: `empty`,
`complete`, `star`, `bipartite`, `path`, `cycle`, `hypercube`, `cocktailParty`, `rook`,
`triangular`, `prism`, `ladder`, `wheel` (through `wheel_eq_join`) and the Petersen graph.  Cycles
and paths contribute cosines rather than integers, which is the point of doing this over `ℝ`
rather than computing a characteristic polynomial: the answer is a multiset of real numbers given
by closed expressions, not a decidable object.

Two shapes of cartesian product are known as well, the grid `Pₘ □ Pₙ` and the torus `Cₘ □ Cₙ`.
The general product is not: `lapSpectrum_cartesianProduct` expresses the spectrum of `G □g H` as a
sum over pairs of eigenvalues, which is a formula in the *eigenvalues* of the factors rather than
in their spectra, and so does not compose with the rest of the list.  An atom the list does not
know — a named graph with no spectrum lemma, or the `ofEdges` fallback for a graph the atlas cannot
describe — is left alone, as `H.lapSpectrum` for that `H`.  Adding one is adding one lemma below.
-/

set_option autoImplicit false

namespace CGraph.Decompose

/-- **Compute the Laplacian spectrum of a graph.**

    compute_lapSpectrum (CGraph.path 3 ⊕g CGraph.complete 2)ᶜ

decomposes the graph with `decompose_graph` and evaluates the Laplacian spectrum of the resulting
formula, leaving an explicit multiset of reals in the goal.  The decomposition is checked by the
kernel, so nothing here is trusted to the elaborator; what is left afterwards is arithmetic. -/
syntax (name := computeLapSpectrum) "compute_lapSpectrum" ppSpace term : tactic

macro_rules
  | `(tactic| compute_lapSpectrum $t:term) =>
    `(tactic|
      (decompose_graph $t
       simp [CGraph.wheel_eq_join, CGraph.lapSpectrum_disjUnion, CGraph.lapSpectrum_join,
         CGraph.lapSpectrum_compl, CGraph.lapSpectrum_empty, CGraph.lapSpectrum_complete,
         CGraph.lapSpectrum_star, CGraph.lapSpectrum_bipartite, CGraph.lapSpectrum_path,
         CGraph.lapSpectrum_cycle, CGraph.lapSpectrum_hypercube, CGraph.lapSpectrum_cocktailParty,
         CGraph.lapSpectrum_rook, CGraph.lapSpectrum_triangular, CGraph.lapSpectrum_petersen,
         CGraph.lapSpectrum_grid, CGraph.lapSpectrum_cartesianProduct_cycle,
         CGraph.lapSpectrum_prism, CGraph.lapSpectrum_ladder]
       all_goals try norm_num [Nat.choose]))

end CGraph.Decompose

/-! ## Examples -/

/-- A cograph: the decomposition is into joins and unions of complete and empty graphs, and every
eigenvalue is an integer. -/
example : IsoGraph.lapSpectrum
    (Quotient.mk CGraph.isoSetoid ((CGraph.path 3 ⊕g CGraph.complete 2)ᶜ))
      = 0 ::ₘ 5 ::ₘ 2 ::ₘ 3 ::ₘ {4} := by
  compute_lapSpectrum ((CGraph.path 3 ⊕g CGraph.complete 2)ᶜ)

/-- The complement of `K₄ ⊕ K₄` is `K_{4,4}`, whose Laplacian spectrum is `0`, `8` and `4` six
times — none of which the goal mentions until the decomposition finds the bipartite graph. -/
example : IsoGraph.lapSpectrum
    (Quotient.mk CGraph.isoSetoid ((CGraph.complete 4 ⊕g CGraph.complete 4)ᶜ))
      = 0 ::ₘ 8 ::ₘ 4 ::ₘ 4 ::ₘ 4 ::ₘ 4 ::ₘ 4 ::ₘ {4} := by
  compute_lapSpectrum ((CGraph.complete 4 ⊕g CGraph.complete 4)ᶜ)

/-- The complement of the Petersen graph is the triangular graph `T(5)`: `0`, `5` four times and
`8` five times. -/
example : IsoGraph.lapSpectrum (Quotient.mk CGraph.isoSetoid CGraph.petersenᶜ)
    = 0 ::ₘ 5 ::ₘ 5 ::ₘ 5 ::ₘ 5 ::ₘ Multiset.replicate 5 8 := by
  compute_lapSpectrum CGraph.petersenᶜ

/-- The line graph of `C₆` is `C₆`, so its Laplacian eigenvalues are the six numbers
`2 - 2 cos (2 π m / 6)` — real numbers named by closed expressions, which is as computed as a
Laplacian spectrum gets. -/
example : IsoGraph.lapSpectrum (Quotient.mk CGraph.isoSetoid (CGraph.lineGraph (CGraph.cycle 6)))
    = Finset.univ.val.map (fun m : Fin 6 ↦ 2 - 2 * Real.cos (2 * Real.pi * m.1 / 6)) := by
  compute_lapSpectrum (CGraph.lineGraph (CGraph.cycle 6))

/-- A torus: the product search recovers the two cycles from the adjacency table, and the torus
rule adds their eigenvalues in pairs. -/
example : IsoGraph.lapSpectrum (Quotient.mk CGraph.isoSetoid (CGraph.cycle 5 □g CGraph.cycle 6))
    = Finset.univ.val.map (fun p : Fin 5 × Fin 6 ↦
        (2 - 2 * Real.cos (2 * Real.pi * p.1.1 / 5))
          + (2 - 2 * Real.cos (2 * Real.pi * p.2.1 / 6))) := by
  compute_lapSpectrum (CGraph.cycle 5 □g CGraph.cycle 6)

/-- The pentagonal prism is an atlas graph, so it is named rather than factored, and its own
spectrum lemma applies: the cycle's eigenvalues, and the same shifted up by `2`. -/
example : IsoGraph.lapSpectrum (Quotient.mk CGraph.isoSetoid (CGraph.prism 5))
    = Finset.univ.val.map (fun m : Fin 5 ↦ 2 - 2 * Real.cos (2 * Real.pi * m.1 / 5))
      + Finset.univ.val.map (fun m : Fin 5 ↦ 4 - 2 * Real.cos (2 * Real.pi * m.1 / 5)) := by
  compute_lapSpectrum (CGraph.prism 5)
