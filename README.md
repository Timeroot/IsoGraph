# IsoGraph

Finite graph theory in Lean 4, up to isomorphism.

When you say "the Petersen graph" you do not mean a particular labelling of ten vertices; you mean
the isomorphism class. Lean makes you pick a labelling anyway, and from then on every statement
drags a relabelling obligation behind it. IsoGraph takes the quotient instead. `CGraph` is a finite
simple graph with a concrete vertex type, `IsoGraph` is `CGraph` modulo isomorphism, and two
isomorphic graphs are *equal* — so `rw` and `simp` work on graphs the way they work on numbers. A
quotient is only worth having if you can compute in it, so underneath sits a canonical labelling
algorithm, a small nauty: individualisation–refinement with orbit pruning and backjumping, proved
correct, which canonicalises a random 50-vertex graph in a fifth of a millisecond. That is the whole
trick :)

The goal is a library you can actually get answers out of. Invariants are defined once on `CGraph`,
as thin wrappers around the Mathlib notion — that is the level concrete proofs happen at — and the
`@[toIsoGraph]` attribute states and proves the quotient-level counterpart for you. The decision
procedures are meant to be run: enumeration over all graphs of an order, nine containment searches,
a SAT backend for the co-NP invariants, an exact rational simplex for the fractional ones, and an
atlas that recognises a graph and evaluates invariants along its decomposition. What is *not* here:
infinite, directed, weighted or multi-graphs. Everything is finite, simple and undirected, and that
is not a placeholder — canonical labelling and exhaustive enumeration are what the design is for,
and neither survives dropping finiteness. It is also not trying to be Mathlib. It builds on
`SimpleGraph`, and `ForMathlib/` holds the lemmas that belong upstream, but the quotient, the
labelling algorithm and the `native_decide`-backed tables are the point and none of them are to
Mathlib's taste.

```lean
import IsoGraph

-- Isomorphic graphs are *equal*, so `rw` and `simp` work on graphs.
example : IsoGraph.lineGraph (IsoGraph.bipartite 3 3) = IsoGraph.rook 3 3 := by simp
example : IsoGraph.petersen = IsoGraph.kneser 5 2 := rfl

-- Two constructions with nothing to do with each other are out of reach of `rfl` and `simp`, so
-- you run the decision procedure instead: `native_decide` canonically labels each side and
-- compares.  Here the bipartite double cover of the Petersen graph is the Desargues graph — a
-- 10-cycle, the {10/3} star polygon inside it, and spokes between.  (The `set_option` is a wart:
-- a `CGraph` carries its vertex type as a field, so instance search only sees `(G ⊗g H).V` for
-- what it is by unfolding the product.  Most of the library sets it once at the top of the file.)
set_option backward.isDefEq.respectTransparency false in
example : IsoGraph.petersen ⊗g IsoGraph.complete 2 = ⟦NamedGraphs.desargues⟧ := by native_decide

-- What *is* this graph?  `#decompose_graph` searches an atlas of named graphs and the
-- operations between them.  These three print, respectively,
--     NamedGraphs.grotzsch        CGraph.triangular 5        CGraph.paley 13
-- the last because the Paley graph on 13 vertices is self-complementary.
#decompose_graph CGraph.mycielskian (CGraph.cycle 5)
#decompose_graph CGraph.lineGraph (CGraph.complete 5)
#decompose_graph (CGraph.paley 13)ᶜ

-- ...and it will hand you the isomorphism itself, as a certificate the kernel checks.
example : Nonempty (CGraph.gp 10 2 ≃cg NamedGraphs.dodecahedron) := by
  generate_graph_iso (CGraph.gp 10 2) with e
  exact ⟨e⟩

-- The same decomposition evaluates invariants compositionally, so you get answers no
-- search would reach.  (`⟦G⟧` is the isomorphism class of `G`.)
example : IsoGraph.chromNum ⟦CGraph.mycielskian (CGraph.cycle 5)⟧ = 4 := by
  compute_invariant (CGraph.mycielskian (CGraph.cycle 5))

example : IsoGraph.lapSpectrum ⟦CGraph.petersenᶜ⟧
    = 0 ::ₘ 5 ::ₘ 5 ::ₘ 5 ::ₘ 5 ::ₘ Multiset.replicate 5 8 := by
  compute_lapSpectrum CGraph.petersenᶜ

-- The co-NP bounds go to a SAT solver through `bv_decide`...
example : (CGraph.kneser 5 2).indepNum ≤ 4 := by graph_sat
example : 3 < IsoGraph.petersen.edgeChromNum := by graph_sat native

-- ...and the fractional relaxations to an exact rational simplex, run in the elaborator.
example : CGraph.petersen.fracChromNum = 5 / 2 := by
  compute_fractional_chromNum native CGraph.petersen
  exact h_fχ

-- `small_graphs` proves a statement about *every* isomorphism class of a given order by
-- enumerating them.  Here is R(3,3) <= 6, in one tactic: all 156 graphs of order six, in 12ms.
open IsoGraph in
theorem ramsey : ∀ G : IsoGraph, G.V = 6 → (complete 3 ≤ₛ G ∨ complete 3 ≤ₛ Gᶜ) := by
  small_graphs

-- The gallery of named graphs comes with its spectra and the bounds they give.
example : SRG.higmanSims.spectrum
    = 22 ::ₘ (Multiset.replicate 77 2 + Multiset.replicate 22 (-8)) := CGraph.spectrum_higmanSims
example : IsoGraph.higmanSims.indepNum ≤ 26 := IsoGraph.indepNum_higmanSims_le
```

## Layout

Two engines, each in its own directory: `IsoGraph/Canon/` is the canonical labelling algorithm and
its correctness proof, twenty-one modules and the bulk of the development, and `IsoGraph/Enum/` is
the enumerator built on top of it. Then the graph theory proper, one directory per kind of thing
being said — `Invariants/` *defines* the invariants, `Core/` builds the graphs everything else is
made of and settles the invariants on them, `SmallGraphs/` does the same for a gallery of about two
hundred named graphs and families, `Algebra/` treats isomorphism classes as a semiring and gets as
far as Sabidussi–Vizing unique cartesian factorisation, and `Containment/` orders them by what sits
inside what. `ForMathlib/` sits underneath everything and mentions nothing from this development.
The root files are the ones that cut across: `Basic.lean` (`CGraph`, isomorphisms, the quotient),
`Spectrum.lean`, `Edgeless.lean`, `Sat.lean`, `Fractional.lean`, `Exhaustion.lean`, and
`Decompose/` for the atlas.

Both `Core/` and `SmallGraphs/` are split by topic in the same order — definitions, then identities,
then order and size, connectivity, symmetry, colouring — which means a fact about a construction and
the same fact about a named graph live at the same depth in two parallel trees. Keeping the `CGraph`
and `IsoGraph` levels in sync by hand would be miserable, so `@[toIsoGraph]` does it: tag a
definition or a theorem about `CGraph` and the attribute picks one of four modes from its shape —
construction, operation, invariant, or plain fact — and emits the quotient-level statement with its
proof. `#isograph_dict` prints the dictionary it has accumulated. To see where the holes are,
`testing/Coverage.lean` regenerates `testing/invariant_coverage.txt`, an invariant × construction
table marking every cell for which a rewriting theorem exists; it currently reads 2337 of 2352.

The long version — the algorithm, the benchmarks, a survey of what is proved about what, and the
proof status — is in [`NOTES.md`](NOTES.md). For scale: 150 files, about 134 000 lines, 10 400
theorems.

## What is in it

**Building a graph.** `ofRel V r` from a decidable symmetric irreflexive relation; `ofEdges n es`
from an edge list, with `cliqueEdges`, `cycleEdges`, `pathEdges`, `pendantEdges`, `legEdges`,
`spiderEdges`, `thetaEdges`, `gpEdges` and `lcfEdges` to write the list; and the four atoms
`empty n`, `complete n`, `path n`, `cycle n`.

**Combining graphs.** Disjoint union `G ⊕g H` and its indexed form `sigmaUnion`; join `G ∇g H`;
complement `Gᶜ`; `seidelSwitch`. The four products — cartesian `G □g H`, tensor `G ⊗g H`, strong
`G ⊠g H`, lexicographic `G ·g H` — and the two exponentials, `exponential` and `homExponential`.
`lineGraph` and `mycielskian`. Gluing: `vertexSum`, `edgeSum`, `oneCliqueSum`, `twoCliqueSum`.

**Families.** `bipartite`, `book`, `cayleyAdd`, `circulant`, `cocktailParty`,
`completeMultipartite`, `crown`, `cyclePendant`, `doubleStar`, `fan`, `foldedCube`, `friendship`,
`gp` (generalised Petersen), `hypercube`, `johnson`, `kneser`, `ladder`, `lcf`, `lollipop`, `paley`,
`prism`, `rook`, `spider`, `star`, `tadpole`, `thetaGraph`, `triangular`, `turan`, `wheel` — and on
top of them the gallery: the 143 connected graphs on six vertices or fewer, the strongly regular
table up to Higman–Sims, the cubic cages, and the Platonic, Archimedean and Catalan solids.

**Order, size, degrees.** `V`, `E`, `nbrs`, `degSequence`, `degMultiset`, `maxDeg`, `minDeg`.

**Shape.** `IsConnected`, `numComponents`, `diameter`, `radius`, `girth`, `IsAcyclic`, `IsTree`,
`IsBipartite`, `IsHamiltonian`.

**Connectivity.** `vertexConn` (κ) and `edgeConn` (λ), with `IsCut`, `IsSeparator` and `cutSize`,
and Whitney's `κ ≤ λ ≤ δ`.

**Cliques and colourings.** `cliqueNum` (ω), `indepNum` (α), `chromNum` (χ), `coverNum` (τ),
`domNum` (γ) with `IsDominatingSet`, `matchNum` (ν), `edgeChromNum` (χ′), `cliqueCoverNum`, and the
counting versions `cliqueCount` and `indepCount`.

**Fractional relaxations.** `fracIndepNum` (α_f), `fracChromNum` (χ_f), `fracCliqueCoverNum`, with
`α ≤ α_f`, `ω ≤ χ_f ≤ χ`, multiplicativity of α_f over `⊠g`, additivity of χ_f over `∇g`, and Zhu's
fractional Hedetniemi equality `χ_f(G ⊗ H) = min (χ_f G) (χ_f H)`.

**Symmetry.** `autCount` and the generators `autGens`, `IsVertexTransitive`, `IsArcTransitive`,
`IsRegularWith`, `IsSRGWith`, `IsSelfComplementary`. The transitivity tests are *decided*, from a
stabiliser chain proved to generate the whole automorphism group.

**Spectra.** `adjMat`, `incMat`, `charpoly`, `spectrum`, `eigenvalues`, `lambdaMax`, `lambdaMin`,
`energy`, `minSpecPoly`, `Cospectral`, `IsDS`; on the Laplacian side `lapMat`, `lapCharpoly`,
`lapSpectrum`, `lapLambdaMax`, `algConn` (the Fiedler value), `LapCospectral`; and `IsSmith` /
`IsSubcritical` for the ADE classification of graphs with spectral radius at most two. The Hoffman
ratio bound is here, which is where the strongly regular table's α and χ bounds come from.

**Containment**, nine relations, each with a decision procedure and each an order: `H ≤ₛ G`
subgraph, `≤ᵢₛ` induced subgraph, `≤ₘ` minor, `≤ᵢₘ` induced minor, `≤ₜₘ` topological minor, `≤ₑ`
immersion minor, `≤ₚ` contraction, `≤ₕ` homomorphism, `≤/` quotient.

**Automation.** `small_graphs`, `graph_sat [native]`, `compute_fractional_indepNum` and
`compute_fractional_chromNum`, `compute_invariant`, `compute_lapSpectrum`, `decompose_graph` and
`generate_graph_iso … with e`, the commands `#decompose_graph` and `#isograph_dict`, and the
`@[toIsoGraph]` attribute with its escape hatch `isograph_bridge`.

## Building

The library sets `precompileModules = true`, because everything here is meant to be run and the
interpreter is about two orders of magnitude slower. The first build therefore compiles Mathlib's C
to a shared library, and that shared library wants `libLake_shared.so` on the loader path, which
Lake does not put there for its own subprocesses. So:

```sh
lake env lake build     # or: export LD_LIBRARY_PATH="$(lean --print-prefix)/lib/lean"
```

Toolchain `leanprover/lean4:v4.34.0-rc2`, Mathlib pinned to match.

The validation and timing drivers live in `testing/`, and are separate targets: `lake exe isobench`
checks the canonical labelling against 34 families of graphs and against OEIS A000088, and
`enumbench`, `minorbench` and `cachebench` time the enumerator and the containment searches.

## How to cite

```bibtex
@software{meiburg_isograph,
  author = {Alex Meiburg},
  title  = {{IsoGraph}: finite graph theory up to isomorphism in {Lean}~4},
  year   = {2026},
  url    = {https://github.com/Timeroot/IsoGraph}
}
```

Bug reports, missing invariants and "why is this cell of the coverage table empty" are all welcome
:D
