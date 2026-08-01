# IsoGraph

Graphs up to isomorphism in Lean 4, with a fast canonical labelling underneath.

The idea (see `isograph_draft.txt`) is that `IsoGraph := Quotient CGraph.isoSetoid` should be
usable for real combinatorial work: invariants are lifted through the quotient, and there is a
canonical representative that is actually computable at useful sizes.

## Layout

| file | what it is | Mathlib? |
| --- | --- | --- |
| `IsoGraph/Canonical.lean` | the canonical labelling algorithm — a mini-nauty | no |
| `IsoGraph/Equivariance.lean` | how the pieces of the algorithm respond to renaming vertices | yes |
| `IsoGraph/Search.lean` | the search tree, and the specification `BestKey` it must meet | yes |
| `IsoGraph/Autos.lean` | the harvested permutations are automorphisms, and how they act on the tree | yes |
| `IsoGraph/Node.lean` | `Node` — the ghost invariant tying `path`, `invPath` and `p` together | yes |
| `IsoGraph/Orbits.lean` | the orbit-closure bitmap propagates a predicate along the generators | yes |
| `IsoGraph/Progress.lean` | refinement splits cells, so the fuel suffices and a leaf comes back | yes |
| `IsoGraph/Monotone.lean` | the incumbent never gets worse | yes |
| `IsoGraph/Paths.lean` | the leaves a node records lie below it | yes |
| `IsoGraph/Pinned.lean` | individualised vertices never move again | yes |
| `IsoGraph/Jump.lean` | backjumping is sound: the abandoned subtree has the keys already recorded | yes |
| `IsoGraph/Leaves.lean` | `StGood` — every leaf and generator a state holds is genuine | yes |
| `IsoGraph/Dominate.lean` | domination bookkeeping: `stopDepth`, moving a subtree along an automorphism | yes |
| `IsoGraph/Branch.lean` | the backjump invariants `Jmp` / `JmpC` of the optimality induction | yes |
| `IsoGraph/Optimal.lean` | `dfsNode_dom` — no pruning rule ever discards the best leaf | yes |
| `IsoGraph/Correct.lean` | soundness and optimality meet: the search satisfies `BestKey` | yes |
| `IsoGraph/Spec.lean` | wraps it as an `Equiv.Perm (Fin n)`; proves `canonAdj_relabel` | yes |
| `IsoGraph/Basic.lean` | `CGraph`, isomorphisms, the quotient `IsoGraph`, `canon`/`canonicalize` | yes |
| `IsoGraph/Invariants.lean` | invariants at both levels: `indepNum`, `E`, `IsConnected`, `diameter`, … | yes |
| `IsoGraph/Constructions.lean` | ways of building a `CGraph`, and their invariants | yes |
| `IsoGraph/Compute.lean` | evidence that `canonicalize` really runs, checked at elaboration time | yes |
| `IsoGraph/Enumerate.lean` | one graph per isomorphism class on `n` vertices, and why nothing is missed | yes |
| `IsoGraph/EnumerateConn.lean` | the same for *connected* graphs | yes |
| `Bench.lean` | validation and timing harness (`lake exe isobench`) | no |
| `EnumBench.lean` | enumeration counts and timings (`lake exe enumbench`) | no |
| `atp/` | tooling that handed `Constructions.lean`'s `sorry`s to the Harmonic prover | — |

Toolchain is `leanprover/lean4:v4.28.0` with Mathlib pinned at `v4.28.0` — the rev the prover
service's base image ships, so the project can be submitted to it without a Mathlib rebuild.

`Canonical.lean` deliberately imports nothing: it is plain functional Lean over `Array`, so it
compiles in seconds and its equation lemmas are available for the eventual correctness proof.
Nothing in it is `partial` — every loop is structural on an explicit fuel argument.

A related discipline, learned the hard way (see "Writing it so it can be proved" below): anything
a proof has to look inside is written as a structural recursion rather than as `Id.run do` with a
`for` loop.

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
G(50, 1/2)      0.47 ms      G(1000, 1/2)     213 ms      K_100        227 ms
G(100, 1/2)     1.9 ms       G(1000, 1/100)    38 ms      K_150        870 ms
G(200, 1/2)     7.5 ms       C_1000           128 ms      Q_8           25 ms
G(500, 1/2)    49 ms         random tree 500  363 ms      Paley 101    7.9 ms
3-reg 100      28 ms         3-reg 500       1152 ms      rook 10x10   9.6 ms
```

The bar in the original request was "a random graph on 50 vertices, much better than trying all
50! permutations"; 50! ≈ 3·10^64, and this takes under a millisecond.

Those are compiled. Driven through the quotient (`CGraph.canon`, in Lean's *interpreter*, at
elaboration time) the same code is ~60× slower but scales the same way: G(50) 52 ms, G(100) 242 ms,
G(200) 832 ms, and `G.canonicalize` costs one extra search rather than one per query.

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

## Computability

A `CGraph` has an abstract vertex type with a `Fintype` instance and no order on it, so getting the
graph into the algorithm means choosing a listing of the vertices — and choosing it *computably*.
`Fintype.elems` is a `Multiset`, which is a quotient of `List`, so the listing is there for the
taking:

```lean
-- writing n for Fintype.card G.V
def canonOfList     (G : CGraph) (l : List G.V)     : Canon.AdjMatrix n     -- run the search along l
theorem canonOfList_perm (h : l₁ ~ l₂) : G.canonOfList l₁ = G.canonOfList l₂ -- the listing doesn't matter
def canonOfMultiset (G : CGraph) (s : Multiset G.V) : Canon.AdjMatrix n := Quot.liftOn s _ canonOfList_perm
def canon           (G : CGraph)                    : Canon.AdjMatrix n := G.canonOfMultiset univ.val
```

The index set is `Fin (Fintype.card G.V)` and *not* `Fin l.length`: the type of the result must not
mention the listing, or the lift would not typecheck. An arbitrary `l : List G.V` need not have
length `Fintype.card G.V` — the lift is over all lists, not just enumerations — so the search runs
on `Fin l.length` and is then moved across by `AdjMatrix.reindex`, which reads `false` outside the
common range. For a listing that really does enumerate `G.V` that padding is vacuous, and it is
the only place where a wrong-sized index set is tolerated.

`canonOfList_perm` is where invariance of the algorithm under renaming is used, and it is the only
place. No `Classical.choice` occurs anywhere on this path: `canonicalize` is a plain `def` and
`Compute.lean` runs it, including on a graph whose vertex type is `Bool × Bool`. (Choice reappears
only in `isoCanonicalize`, which picks one of the isomorphisms onto the canonical representative —
a proof-side object.)

Isomorphism invariance has to be stated entrywise,

```lean
theorem canon_adj_eq_of_iso (i : G ≃cg H) (x y : Fin (Fintype.card G.V)) :
    G.canon.adj x y = H.canon.adj (finEq (Iso.card_eq G H i) x) (finEq (Iso.card_eq G H i) y)
```

since the two matrices live over index sets whose sizes are equal only propositionally;
`canon_heq_of_iso` packages it as a `HEq`, and `canonicalize_eq_of_iso` — the form the quotient
actually needs — as an honest equation between `CGraph`s.

One trap worth recording: **the Lean compiler η-expands every definition whose type is a function
type**, which destroys sharing. A `def f (G : CGraph) : Fin n → Fin n → Bool := let c := search G; fun i j ↦ …`
re-runs `search` on *every query*, turning one canonicalisation into `n²` of them. Wrapping the
function in a structure blocks the η-expansion — that is all `Canon.AdjMatrix` is, and a one-field
structure is unboxed at runtime, so it costs nothing. For the same reason the adjacency the
algorithm reads takes its vertex array as a parameter rather than building it inside a
function-typed body, and `canonMatrix` takes the permutation as an argument.

## Invariants and constructions

`Invariants.lean` gives each invariant twice: once on `CGraph`, as a thin wrapper around the
Mathlib notion for `G.toSimple` (that is the form concrete statements get proved in), and once on
`IsoGraph`, as a `Quotient.lift` whose side condition is precisely isomorphism-invariance. Present
so far: `indepNum`, `cliqueNum`, `E`, `degSequence`, `IsConnected`, `IsAcyclic`, `IsTree`,
`diameter`. Mathlib had no invariance lemma for distance, so `SimpleGraph.Iso.edist_eq`,
`ediam_eq` and `diam_eq` are proved there.

`Constructions.lean` builds the zoo out of three primitives — `ofRel` (symmetrise a `Bool`
relation, delete the diagonal), `empty`, `disjUnion` — plus `compl`:

```
complete n    = compl (empty n)                       star n  = bipartite 1 n
join G H      = compl (disjUnion (compl G) (compl H)) wheel n = join (complete 1) (cycle n)
bipartite m n = compl (disjUnion (complete m) (complete n))
```

with `path`, `cycle`, `thetaGraph`, `completeMultipartite`, the four products on `G.V × H.V`,
`hypercube`, `kneser`, `lineGraph` and `mycielskian` on top. `ofRel` is the only place the graph
axioms are discharged, so everything downstream of it is proof-obligation-free.

A `CGraph` carries a `Fintype` but no `DecidableEq`, and the second does not follow from the
first. Constructions that must ask "same vertex?" take `[DecidableEq G.V]` as an instance argument
and export the instance for their own vertex type; instance resolution only unfolds at reducible
transparency, so each *named* construction needs its own. Putting `DecidableEq` into the `CGraph`
structure would remove the boilerplate but stop the type being a bare `Fintype`-bundled graph
(and break `simpleEquiv`) — the instance arguments looked like the smaller price.

## Enumeration

The first real application. `Enumerate.lean` produces, for each `n`, a list holding **exactly one**
graph from every isomorphism class on `n` vertices; `EnumerateConn.lean` does the same for the
connected ones.

```lean
def enumerate      (n : ℕ) : List CGraph     -- brute force, the specification
def enumerateFast  (n : ℕ) : List CGraph     -- the one to use
def enumerateConn  (n : ℕ) : List CGraph     -- connected only
def enumerateIso, enumerateConnIso (n : ℕ) : List IsoGraph   -- the same, in the quotient
```

Each comes with completeness (`exists_mem_enumerate…`: every graph of that size is isomorphic to
one in the list), soundness (`enumerate…_pairwise_not_iso`), and, in the quotient, `Nodup` plus
membership of every class of that size — so the list *is* the set of classes.

A graph on `Fin n` is `n.choose 2` bits, the strict upper triangle, packed into one `Nat` — the
*code*. What makes the whole thing cheap is that `canonAdj` is invariant under relabelling and so
**idempotent**: the canonical codes are exactly the fixed points of `canonCode`, so deduplication
is a `List.filter`, with no sort, no hash set and constant memory. `enumerate` is literally

```lean
(List.range (2 ^ n.choose 2)).filter fun c ↦ canonCode n (graphOfCode n c).Adj == c
```

which is correct by inspection and hopeless past `n = 7` (2^21 canonicalisations for 1044 answers).

The fast enumerator extends one vertex at a time: take each graph on `n` vertices, add a last
vertex with neighbourhood `s`, canonicalise, deduplicate. The pruning is in which `s` to offer.

* `symMasks` keeps one mask per orbit of the automorphism group of the graph being extended (the
  group is already lying around — the canonical labelling harvests it).
* `redMasks` additionally insists the new vertex have *least degree*, which is legitimate because
  one may always choose to have deleted a least-degree vertex.
* `connMasks` (connected case) insists on a nonempty mask and least degree **among the non-cut
  vertices** — deleting a cut vertex would disconnect what remains, and `exists_nonCut` says a
  non-cut vertex always exists.

| candidates canonicalised, cumulative to `n = 8` | `allMasks` | `symMasks` | `redMasks` | `connMasks` |
| :-- | --: | --: | --: | --: |
| | 133632 | 79454 | 18329 | 17007 |
| for this many graphs | 12346 | 12346 | 12346 | 11117 (connected) |

The connectivity and non-cut tests are bitmask BFS over `rowsOfCode` — `Array ℕ`, one word per
row — and are proved to agree with `Conn` / `NonCut` on `Relation.ReflTransGen`
(`connTest_iff`, `nonCutTest_iff`). The non-cut test also has to commute with the orbit reduction
(`nonCutTest_permMask`), or the two prunings could not be combined. The payoff statement is

```lean
theorem enumConnCodes_eq (n : ℕ) : enumConnCodes n = (enumCodes n).filter (connTest n)
```

— not merely the same *set*: both sides are strictly increasing lists of codes, so the connected
enumerator computes the connected part of the full enumeration without ever looking at a
disconnected graph.

`lake exe enumbench`, compiled, on the same contended VM (counts checked against OEIS A000088 and
A001349):

```
n            5      6       7        8         9
all       5 ms   20 ms   184 ms   2.4 s     219 s      (1, 1, 2, 4, 11, 34, 156, 1044, 12346, 274668)
connected 3 ms   19 ms   170 ms   2.5 s                (0, 1, 1, 2, 6, 21, 112, 853, 11117)
```

Two refinements were built, measured and thrown away; both are worth recording because in both
cases the *pruning worked* and was still a loss.

* **All graphs from the connected ones.** Every graph is a disjoint union of connected graphs, so
  the all-graphs list can be assembled from `enumerateConn` by joining and canonicalising. It runs
  (it reproduces A000088 to `n = 8`) and it is slower: min-of-3 CPU at `n = 8` was 2.39 s for
  `enumCodesFast` against 2.80 s for the join-based version. The connected enumerator is not
  actually cheaper *per graph produced* — 1.53 canonicalisations per output against 1.48 — and the
  joins add ~1300 canonicalisations on top. Deleted.
* **Neighbourhood-invariant tie-break.** Among vertices tying on least degree, require the new one
  to also minimise the sorted multiset of its neighbours' degrees. Provably complete, compatible
  with the orbit reduction, and it cuts candidates by 29% (18329 → 13094; 17007 → 11859 connected,
  against an unreachable ideal of 11117). But a canonicalisation at `n = 8` costs ≈ 57 µs, so the
  0.30 s of saved work was outweighed by the 0.52 s of testing; tabulating the degrees through a
  `@[csimp]` fast path narrowed that to a 6% net loss but did not close it. Reverted, in both
  files.

The lesson both times: at these sizes canonicalisation is cheap enough that a pruning test has to
be *very* cheap to pay for itself, and "fewer candidates" is not the same as "faster".

## Writing it so it can be proved

The algorithm was written first and proved about second, and the single biggest obstacle turned
out to be a style question rather than a mathematical one. A loop written as

```lean
def f (n : Nat) : α := Id.run do
  let mut acc := init
  for i in [0:n] do
    if i ≥ n then break
    acc := step acc i
  return acc
```

produces goals that are very hard to work with. To prove two such loops equal you must show
their body functions are equal *pointwise at every index*, including indices the loop never
visits — the `i < n` that makes the statement true is exactly what `for` hides. `congr` on the
resulting `Id.bind (forIn …)` term either diverges or overflows the stack. Sixteen samples from
an automatic prover produced zero proofs on goals of that shape.

The same functions written as structural recursions on an explicit fuel are easy:

```lean
def f (n : Nat) : Nat → Nat → α
  | 0, _ => acc
  | fuel + 1, i => f n fuel (i + 1) (step acc i)
```

because `i + fuel = n` can be carried through the induction, and that invariant *supplies* the
`i < n` the body needs. Every lemma that had resisted went through by hand in a handful of lines
after the corresponding definition was rewritten this way: `Part.shapeHash` and
`Part.targetCell` became `cenHashFrom` / `cenTargetFrom`, and `certOf` became `certBits`, which
is `certRow` and `certRowsFrom`. `Graph.ofOracle` got the same treatment in the simplest form —
`Array.ofFn` and `Array.filter`, so that each entry is definitionally the oracle.

None of this changed what the code computes or what it costs; `lake exe isobench` reports the
same timings and passes the same checks. The bit-packing loop is the only one on the hot path,
and it is unchanged in shape — still a tail recursion over `n²` bits with a destructive `set!`.

The one place a check was *added* is `canonicalLabellingOfOracle`, which now verifies in `O(n)`
that the search returned a permutation of the vertices and substitutes the identity if not. That
turns "the search returns a permutation" from an assumption into a theorem, at a cost that is
invisible against an `Ω(n²)` search.

## Proof status

**Complete.** There is no `sorry` in the development, and `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound` for every user-facing statement — including
`labellingInvariant`, `canonAdj_relabel` and `exists_relabel_of_canonAdj_eq`.

The user-facing statement is

```lean
theorem canonAdj_relabel (σ : Equiv.Perm (Fin n)) (adj : Fin n → Fin n → Bool) :
    canonAdj n (relabel σ adj) = canonAdj n adj
```

— renaming the vertices does not change the canonical form. It is what licenses `Quotient.lift`
through the canonical form, so `canon`, `canonicalize`, `IsoGraph.toCGraph` and every lifted
invariant in `Basic.lean` / `Invariants.lean` are unconditional.

Its converse, **soundness**,

```lean
canonAdj n adjG = canonAdj n adjH → ∃ σ, relabel σ adjG = adjH
```

is easier and holds *whatever* the search returns: `permOfArrays` checks at run time (in `O(n)`)
that the algorithm's output and its inverse really are mutually inverse and falls back to the
identity if not, so `canonAdj n adj` is by construction `adj` read through some permutation.

### How it decomposes

`canonAdj_relabel` is derived from two statements about the raw array algorithm,
`LabellingIsPerm` and `LabellingInvariant`, by `canonAdj_relabel_of`. That reduction discharges
the entire `Fin` / `Equiv.Perm` wrapper — the `permOfArrays` run-time check, the `invArray`
inverse, the translation between `Equiv.Perm (Fin n)` and a renaming of `{0, …, n-1}` — so what
is left mentions nothing but `Array Nat`. `LabellingIsPerm` is the run-time check described
above. `LabellingInvariant` is where the work is:

```lean
def LabellingInvariant : Prop :=
  ∀ (m : Nat) (f : Nat → Nat → Bool) (s : Nat → Nat), Canon.IsPerm m s →
    ∀ i, i < m → ∀ j, j < m →
      f (s ((labelling m fun v w => f (s v) (s w))[i]!))
          (s ((labelling m fun v w => f (s v) (s w))[j]!))
        = f ((labelling m f)[i]!) ((labelling m f)[j]!)
```

Note this is weaker than "the labelling transforms along `s`", which is false: the winning leaf
is determined only up to an automorphism, and *which* of several equally good leaves the search
reaches does depend on vertex names. What may not depend on them is the matrix read off at the
winner.

The proof is in three parts.

**1. A specification the algorithm is not mentioned in.** `Reach n f invPath p k` (in
`Search.lean`) describes the leaves of the *unpruned* tree, and `leafKey` the quantity the search
maximises: the pair (node-invariant path, certificate), packed as a `List (List UInt64)` so that
lexicographic `compare` on it is exactly the comparison `leafUpdate` performs. Then

```lean
def BestKey (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64)) : Prop :=
  Leafkey n f k ∧ ∀ k', Leafkey n f k' → compare k' k ≠ .gt
```

`bestKey_unique` says it pins `k` down, and `bestKey_transfer` says it is an isomorphism
invariant. Neither mentions pruning, fuel or state — the specification is manifestly the right
one, and everything after this is about the algorithm meeting it.

`bestKey_transfer` rests on `reach_transfer`, which transports a leaf along a renaming, which
rests in turn on the whole of `Equivariance.lean`: `refineStep_equiv`, `refine_equiv`,
`individualize_partEquiv`, `childInv_equiv`, `child_equiv`, `certOf_relabel`. The vocabulary
there is `PartEquiv`, "the same ordered partition up to a renaming", deliberately weaker than a
positionwise equation — the two runs displace *different* vertices from the front of a split
cell, since the counting sort is stable and inherits vertex-name order from the parent, so all
that survives is which *cell* each vertex lands in. `lab_eq_of_discrete` sharpens it back to an
array equation exactly at discrete partitions, which is where the certificate is read.

**2. Soundness: the search returns a leaf, and a real one.** `dfsNode_reach` (`Search.lean`)
gives `canonSt_leafkey`: whatever the search ends up holding is a leaf of the unpruned tree.
`Progress.lean` rules out the empty-handed case — refinement never merges cells, individualising
splits one, so `numCells` strictly increases down the tree, the depth is at most `n`, and the
fuel `n + 1` suffices (`dfsNode_best`).

**3. Optimality: none of the three prunings ever discards the winner.** This is the bulk of the
development and the reason for the file count. `dfsNode_dom` (`Optimal.lean`) is one induction
over `dfsNode.induct` carrying an invariant for each pruning rule:

* *invariant pruning* — a node whose invariant path already loses is skipped. `pruneNode_none`
  (`Search.lean`) says every leaf below such a node is strictly beaten, via
  `compare_append_gt`: the invariant path is a prefix of every leaf key below it.
* *orbit pruning* — a child in the orbit of an already-processed child is skipped. `Autos.lean`
  proves the harvested permutations really are automorphisms (`autoOf_isAuto`) and that one
  fixing the node carries the subtree below `γ w` onto the subtree below `w` with the same keys
  (`reach_child_auto`, `subR_inv`); `Orbits.lean` propagates that along the closure
  (`orbitClosure_P`); `Node.auto_partEquiv` supplies the hypothesis, and `usableAutos` filters
  for exactly it.
* *backjumping* — on a certificate tie, every branch between the two leaves is abandoned.
  `Pinned.lean` shows an individualised vertex never moves again, so two leaves agreeing to
  depth `j` park their depth-`j` choices at the same *position*; `Jump.lean` reads the
  correspondence off the harvested automorphism (`auto_path`) and concludes `jump_sound` — the
  abandoned subtree and the recorded one have the same set of leaf keys. `Branch.lean` turns
  that into the running invariants `Jmp` / `JmpC` and the lemma `leaf_abort_dom`.

The structural obstacle in `dfsNode_dom` is that `pruneNode` may *clear* the incumbent, so
"dominated by the incumbent" is not preserved into a recursive call and cannot be the invariant.
Everything is therefore stated relative to an extra predicate `D`, "already accounted for by
whoever called us", with `DomD D st k := Dom st k ∨ D k`. `D` is quantified *inside* the
induction motive, so each recursive call may be made at the shifted predicate `DomD D st`, and
the `BestMono st0 st` component of `Guar` — the returning call kept the incumbent it was given —
is exactly what collapses the shift on the way back out (`DomD.shift`).

`Correct.lean` instantiates `dfsNode_dom` at the root and joins it to soundness:

```lean
theorem canonSt_bestKey (n : Nat) (f : Nat → Nat → Bool) (b : Leaf)
    (hb : (canonSt n f).best = some b) : BestKey n f (leafKey b.invPath b.cert)
```

With `bestKey_transfer` and `bestKey_unique` this gives `canonical_cert_relabel` — the winner's
certificate does not depend on the vertex names — and `certOf_get` reads the adjacency matrix
back out of the packed certificate, which is `LabellingInvariant`.

### Notes

`Constructions.lean`'s second half — 41 statements pinning down the invariants of every
construction, from `indepNum_empty` up to `E_mycielskian` and the four products — was closed by
the Harmonic `sorry`-closing prover rather than by hand; `atp/` holds the tooling that submitted
them and spliced the results back. Those proofs are machine-written: long, explicit, and
un-golfed. They are checked, not pretty.

The same prover was tried on the search obligations and returned nothing usable — sixteen
samples, zero proofs — which is what prompted the rewrite described under "Writing it so it can
be proved" and, ultimately, the by-hand development above.

`certOf_relabel` is worth a footnote: an earlier version of it, missing the `lab.size = n`
hypothesis, was *refuted* by the prover, which returned a counterexample (`n = 2`,
`f v w := v = 0 ∧ w = 0`, `σ` the transposition, `lab = #[]`) rather than a proof. Out of range
`lab[i]!` is `0` on the left but `(lab.map σ)[i]!` is also `0` on the right, so the two sides read
`f (σ 0) (σ 0)` and `f 0 0`. The counterexample is kept in `atp/rejected/`.

One thing worth recording from the fuel rewrite: it is free. The worry was reference counts — a
`for` loop over a `let mut` array updates it linearly, whereas a recursion that returns a pair of
arrays might leave them shared and turn every subsequent `set!` into a copy. The generated IR
says otherwise (the parameters stay owned, `Array.set!` stays in place, and the recursive calls
are tail calls), and a benchmark confirms it: minimum-of-six total CPU time is 14.6 s either way,
as it is for the `List.mergeSort` detour that replaced the unspecified `Array.qsort`. Measure on
a quiet machine, though — this one is shared, and single wall-clock runs of the benchmark vary by
a factor of four under load, which is enough to invent a regression that is not there.
