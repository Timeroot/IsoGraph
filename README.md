# IsoGraph

Graphs up to isomorphism in Lean 4, with a fast canonical labelling underneath.

The idea (see `isograph_draft.txt`) is that `IsoGraph := Quotient CGraph.isoSetoid` should be
usable for real combinatorial work: invariants are lifted through the quotient, and there is a
canonical representative that is actually computable at useful sizes.

## Layout

| file | what it is | Mathlib? |
| --- | --- | --- |
| `IsoGraph/Canonical.lean` | the canonical labelling algorithm — a mini-nauty | no |
| `IsoGraph/Spec.lean` | wraps it as an `Equiv.Perm (Fin n)`; states what must be proved | yes |
| `IsoGraph/Basic.lean` | `CGraph`, isomorphisms, the quotient `IsoGraph`, lifted invariants | yes |
| `Bench.lean` | validation and timing harness (`lake exe isobench`) | no |

`Canonical.lean` deliberately imports nothing: it is plain functional Lean over `Array`, so it
compiles in seconds and its equation lemmas are available for the eventual correctness proof.
Nothing in it is `partial` — every loop is structural on an explicit fuel argument.

## The algorithm

McKay-style individualisation–refinement.

* **Equitable refinement** (1-dimensional Weisfeiler–Leman) by a Hopcroft-style worklist: pop a
  splitter cell, counting-sort every cell it meets by the number of neighbours it has inside the
  splitter, and requeue fragments (all of them if the parent was queued, otherwise all but a
  largest). Only cells actually *met* by the splitter are visited, so a pop costs `O(deg)` rather
  than `O(n)`.
* **Scratch reuse**: the count / seen / bucket arrays are allocated once per refinement and
  threaded through every step, each step restoring them to the cleared state on the way out. This
  is what keeps sparse graphs from paying `O(n)` per splitter pop.
* **Search** over the individualisation tree, depth-first, keeping the leaf that is largest for
  `(node-invariant path, certificate)`. Three prunings: node invariants, automorphism orbits of
  the target cell, and the nauty backjump when a leaf turns out to be an automorphic image of the
  best one.
* **Node invariants** are FNV-style hashes of positions, fragment sizes and counts only — never of
  vertex names — so they are isomorphism-invariant by construction; a collision only weakens
  pruning.
* **Certificates** are the adjacency matrix in discrete-partition order, packed MSB-first into
  `Array UInt64`, so comparing two of them is a word-at-a-time lexicographic scan.

## Numbers

`lake exe isobench` on a (contended) 4-core cloud VM, best of 3, canonicalisation only:

```
G(50, 1/2)      0.79 ms      G(1000, 1/2)     458 ms      K_100        477 ms
G(100, 1/2)     3.0 ms       G(1000, 1/100)    80 ms      K_150       2415 ms
G(200, 1/2)    12.8 ms       C_1000           303 ms      Q_8         54 ms
G(500, 1/2)   114 ms         random tree 500  872 ms      Paley 101   26 ms
3-reg 100      73 ms         3-reg 500       2738 ms      rook 10x10  37 ms
```

The bar in the original request was "a random graph on 50 vertices, much better than trying all
50! permutations"; 50! ≈ 3·10^64, and this takes under a millisecond.

Highly symmetric graphs (`K_n`, unions of small cliques) are the weak spot: the automorphisms the
search harvests there are transposition-like, so it needs `Θ(n²)` nodes. Real nauty has the same
shape of problem and beats it with better generator management.

## Validation

`lake exe isobench` checks, and all of it passes:

* every graph in a library of 34 families (random, regular, trees, hypercubes, Kneser, Johnson,
  rook, Paley, Shrikhande, disjoint unions, …) gets the same certificate after random
  relabellings; the certificate agrees with recomputing it from the returned labelling; and every
  automorphism generator returned really is an automorphism;
* the number of distinct certificates over **all** labelled graphs on `n` vertices equals OEIS
  A000088 for `n = 0..7` (`--deep` does `n = 7`, all 2^21 graphs, giving exactly 1044). This pins
  down invariance and completeness simultaneously at those sizes;
* the cospectral non-isomorphic pair rook(4,4) / Shrikhande gets different certificates.

## Proof status

One `sorry`, in `IsoGraph/Spec.lean`:

```lean
theorem canonAdj_relabel (σ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) :
    canonAdj n (relabel σ adj) = canonAdj n adj
```

— renaming vertices does not change the canonical form. Its docstring records the six-step
decomposition it needs.

Everything else is proved. In particular the **soundness** direction,

```lean
canonAdj n adjG = canonAdj n adjH → ∃ σ, relabel σ adjG = adjH
```

is unconditional, and holds *whatever* the search returns: `permOfArrays` checks at run time
(in `O(n)`) that the algorithm's output and its inverse really are mutually inverse and falls back
to the identity if not, so `canonAdj n adj` is by construction `adj` read through some
permutation. So a canonical-form comparison can never conflate non-isomorphic graphs; only the
converse — that it never separates isomorphic ones — rests on the open obligation.

`Basic.lean` reduces the rest of the development to that single obligation: `canonicalize`,
`IsoGraph.toCGraph`, and the lifted invariants `V`, `indepNum`, `cliqueNum`, `E`, `degSequence`
are all derived from it, with no further `sorry`.
