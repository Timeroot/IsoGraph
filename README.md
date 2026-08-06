# IsoGraph

Graphs up to isomorphism in Lean 4, with a fast canonical labelling underneath.

The idea (see `isograph_draft.txt`) is that `IsoGraph := Quotient CGraph.isoSetoid` should be
usable for real combinatorial work: invariants are lifted through the quotient, and there is a
canonical representative that is actually computable at useful sizes.

## Layout

Two engines, each in its own directory — `IsoGraph/Canon/` is the canonical labelling algorithm
and its correctness proof, `IsoGraph/Enum/` is the enumerator built on top of it — and the graph
theory proper at the root of `IsoGraph/`. `IsoGraph/Canon.lean` and `IsoGraph/Enum.lean` are
index modules that import their directory.

| file | what it is | Mathlib? |
| --- | --- | --- |
| `IsoGraph/Canon/Algorithm.lean` | the canonical labelling algorithm — a mini-nauty | no |
| `IsoGraph/Canon/Equivariance.lean` | how the pieces of the algorithm respond to renaming vertices | yes |
| `IsoGraph/Canon/Search.lean` | the search tree, and the specification `BestKey` it must meet | yes |
| `IsoGraph/Canon/Autos.lean` | the harvested permutations are automorphisms, and how they act on the tree | yes |
| `IsoGraph/Canon/Node.lean` | `Node` — the ghost invariant tying `path`, `invPath` and `p` together | yes |
| `IsoGraph/Canon/Orbits.lean` | the orbit-closure bitmap propagates a predicate along the generators | yes |
| `IsoGraph/Canon/Progress.lean` | refinement splits cells, so the fuel suffices and a leaf comes back | yes |
| `IsoGraph/Canon/Monotone.lean` | the incumbent never gets worse | yes |
| `IsoGraph/Canon/Paths.lean` | the leaves a node records lie below it | yes |
| `IsoGraph/Canon/Pinned.lean` | individualised vertices never move again | yes |
| `IsoGraph/Canon/Jump.lean` | backjumping is sound: the abandoned subtree has the keys already recorded | yes |
| `IsoGraph/Canon/Leaves.lean` | `StGood` — every leaf and generator a state holds is genuine | yes |
| `IsoGraph/Canon/Dominate.lean` | domination bookkeeping: `stopDepth`, moving a subtree along an automorphism | yes |
| `IsoGraph/Canon/Branch.lean` | the backjump invariants `Jmp` / `JmpC` of the optimality induction | yes |
| `IsoGraph/Canon/Optimal.lean` | `dfsNode_dom` — no pruning rule ever discards the best leaf | yes |
| `IsoGraph/Canon/Correct.lean` | soundness and optimality meet: the search satisfies `BestKey` | yes |
| `IsoGraph/Canon/Spec.lean` | wraps it as an `Equiv.Perm (Fin n)`; proves `canonAdj_relabel` | yes |
| `IsoGraph/Canon/Group.lean` | the automorphism group: generators harvested by the same search | yes |
| `IsoGraph/Basic.lean` | `CGraph`, isomorphisms, the quotient `IsoGraph`, `canon`/`canonicalize` | yes |
| `IsoGraph/Invariants.lean` | invariants at both levels: `indepNum`, `E`, `IsConnected`, `diameter`, … | yes |
| `IsoGraph/Constructions.lean` | ways of building a `CGraph`, and their invariants | yes |
| `IsoGraph/Identities.lean` | the same constructions on `IsoGraph`, and the equations between them | yes |
| `IsoGraph/Symmetry.lean` | automorphisms of a `CGraph`; vertex- and arc-transitivity, tested | yes |
| `IsoGraph/CliqueSum.lean` | gluing two graphs at a vertex or along an edge | yes |
| `IsoGraph/Compute.lean` | evidence that `canonicalize` really runs, checked at elaboration time | yes |
| `IsoGraph/Enum/All.lean` | one graph per isomorphism class on `n` vertices, and why nothing is missed | yes |
| `IsoGraph/Enum/Conn.lean` | the same for *connected* graphs | yes |
| `IsoGraph/NamedSmallGraphs.lean` | a name for each of the 143 connected graphs on `n ≤ 6` | yes |
| `IsoGraph/SRG.lean` | a table of strongly regular graphs, parameters checked | yes |
| `Bench.lean` | validation and timing harness (`lake exe isobench`) | no |
| `EnumBench.lean` | enumeration counts and timings (`lake exe enumbench`) | no |
| `atp/` | tooling that handed `Constructions.lean`'s `sorry`s to the Harmonic prover | — |

Toolchain is `leanprover/lean4:v4.28.0` with Mathlib pinned at `v4.28.0` — the rev the prover
service's base image ships, so the project can be submitted to it without a Mathlib rebuild.

`Algorithm.lean` deliberately imports nothing: it is plain functional Lean over `Array`, so it
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
`diameter`, `IsSRGWith`, `IsRegularWith`, `IsVertexTransitive`, `IsArcTransitive`, `IsBipartite`.
Mathlib had no invariance lemma
for distance, for strong regularity or for regularity, so `SimpleGraph.Iso.edist_eq`, `ediam_eq`,
`diam_eq`, `card_commonNeighbors_eq`, `isSRGWith_of_iso` and `isRegularOfDegree_of_iso` are proved
there. `IsBipartite` is phrased as a
`Bool`-valued colouring with no monochromatic edge rather than as a pair of vertex sets — that is
the form the double-cover splitting theorem consumes — and `isBipartite_iff_colorable` identifies
it with Mathlib's `Colorable 2`.

`Constructions.lean` builds the zoo out of three primitives — `ofRel` (symmetrise a `Bool`
relation, delete the diagonal), `empty`, `disjUnion` — plus `compl`:

```
complete n    = compl (empty n)                       star n  = bipartite 1 n
join G H      = compl (disjUnion (compl G) (compl H)) wheel n = join (complete 1) (cycle n)
bipartite m n = compl (disjUnion (complete m) (complete n))
```

with `path`, `cycle`, `thetaGraph`, `completeMultipartite`, the four products on `G.V × H.V`,
`hypercube`, `kneser`, `johnson`, `foldedCube`, `lineGraph`, `mycielskian`, the Cayley graphs
`cayleyAdd`/`circulant`/`paley`, `seidelSwitch`, and the clique sums of `CliqueSum.lean` on top.
`ofRel` is the only place the graph axioms are discharged, so everything downstream of it is
proof-obligation-free.

A `CGraph` carries a `Fintype` but no `DecidableEq`, and the second does not follow from the
first. Constructions that must ask "same vertex?" take `[DecidableEq G.V]` as an instance argument
and export the instance for their own vertex type; instance resolution only unfolds at reducible
transparency, so each *named* construction needs its own. Putting `DecidableEq` into the `CGraph`
structure would remove the boilerplate but stop the type being a bare `Fintype`-bundled graph
(and break `simpleEquiv`) — the instance arguments looked like the smaller price.

## Identities

This is what the quotient was for. On `CGraph`, `compl (compl G) = G` is *false*: the two sides
have vertex types `G.V` and `G.V`, but they are two different `CGraph` values that happen to be
isomorphic. On `IsoGraph` it is an equality, and a `@[simp]` lemma. `Identities.lean` re-exports
the whole zoo through the quotient and then proves the equations that only become available there.

Lifted names: `empty`, `complete`, `path`, `cycle`, `bipartite`, `completeMultipartite`, `star`,
`wheel`, `kneser`, `johnson`, `hypercube`, `foldedCube`, `circulant`, `paley`, `thetaGraph`,
`tadpole`, `lollipop`, `spider`, `doubleStar`, `cyclePendant`, the operations `compl`,
`disjUnion`, `join`, `lineGraph`, `mycielskian` and the four products, and the abbreviations
`book`, `fan`, `ladder`, `prism`, `triangular`, `rook`, `cocktailParty`, `petersen`.

The lifting has one wrinkle. `compl` and the four products need `[DecidableEq G.V]`, which a
`CGraph` does not carry, so they cannot be `Quotient.lift`ed as they stand. They are lifted as
`fun g ↦ ⟦CGraph.compl g.canonicalize⟧` instead: the canonical representative's vertex type is
`Fin (Fintype.card g.V)`, which does have the instance, and the congruence lemmas of the
`CGraph.Iso` namespace (`Iso.compl`, `Iso.cartesianProduct`, …) discharge the well-definedness
side condition. Each then gets a `_mk` lemma — `(show IsoGraph from ⟦G⟧)ᶜ = ⟦CGraph.compl G⟧` for
any `G` with a `DecidableEq`, not just a canonical one. `disjUnion` needs no instance, so
`disjUnion_mk` is `rfl`. `join` is not lifted at all: it is *defined* on the quotient as
`(Gᶜ ⊕g Hᶜ)ᶜ`, which makes `compl_join` and `join_comm` free.

Each operation on `IsoGraph` has a notation:

```
Gᶜ    complement      G ⊕g H   disjoint union   G □g H  Cartesian product   G ⊠g H  strong product
                      G ∇g H   join             G ⊗g H  tensor product      G ·g H  lexicographic
```

Complementation is the `Compl` instance (`\^c`), so it is spelled the way Mathlib spells
complementation everywhere else; the rest are `infixl`, the four products at 70 and the two sums
at 60, so `G ⊕g H □g K` is `G ⊕g (H □g K)`. The `g` suffix and the `⊕g` symbol follow Mathlib's
`SimpleGraph.sum`, which stays in scope — the two overload and resolve by type — and `□`
follows Mathlib's `SimpleGraph.boxProd`. Of the other box characters that suggested themselves
(`☐`, `⧠`, `◻`) none has a Lean input abbreviation, whereas `□` is `\square`.

Two things to know about `ᶜ`. There is no instance for `CGraph`: its complement takes a
`DecidableEq G.V`, so it is not a bare `α → α`, and `CGraph.compl` keeps its long name. And
`⟦g⟧ᶜ` does not elaborate — instance search sees the type as `Quotient CGraph.isoSetoid` and will
not unfold `IsoGraph` to reach the instance. A type ascription does not help, since it leaves the
inferred type unchanged; write `(show IsoGraph from ⟦g⟧)ᶜ`.

Every `IsoGraph`-level statement in the library is written in this notation; the prefix spellings
survive only where the notation is not available — inside the `CGraph` namespace, where these
names mean the un-quotiented operations, and in the six defining `def`s themselves, since the
`infixl` declarations have to come after them. `join` is one of those: it is defined as
`(disjUnion Gᶜ Hᶜ)ᶜ` because `∇g` cannot be introduced until `join` exists.

The equations themselves come in families:

```
Gᶜᶜ = G                      (cycle 5)ᶜ = cycle 5          (path 4)ᶜ = path 4
complete 1 = empty 1         cycle 3 = complete 3          wheel 3 = complete 4
G ⊕g empty 0 = G             G ∇g empty 0 = G              complete m ∇g complete n = complete (m + n)
kneser n 1 = complete n      kneser n n = empty 1          johnson n 1 = complete n
hypercube (n + 1) = hypercube n □g complete 2
hypercube 3 = prism 4        foldedCube 3 = bipartite 4 4  paley 5 = cycle 5
rook m 0 = empty 0           rook 2 2 = cycle 4            bipartite 2 2 = cycle 4
(cycle 4)ᶜ = complete 2 ⊕g complete 2
complete m ⊠g complete n = complete (m * n)
G ⊗g empty n = empty (G.V * n)
(rook m n)ᶜ = complete m ⊗g complete n
completeMultipartite (d :: ds) = empty d ∇g completeMultipartite ds
completeMultipartite [a, b] = bipartite a b               cocktailParty 2 = cycle 4
completeMultipartite (List.replicate n 1) = complete n    triangular 4 = cocktailParty 3
circulant n [] = empty n     circulant n [1] = cycle n
G □g (H ⊕g K) = (G □g H) ⊕g (G □g K)
(G ⊕g H) ·g K = (G ·g K) ⊕g (H ·g K)
empty 2 □g G = G ⊕g G                                     empty 2 ⊠g G = G ⊕g G
(star n)ᶜ = empty 1 ⊕g complete n                         (book n)ᶜ = empty 2 ⊕g complete n
(wheel n)ᶜ = empty 1 ⊕g (cycle n)ᶜ                        (fan n)ᶜ = empty 1 ⊕g (path n)ᶜ
hypercube (m + n) = hypercube m □g hypercube n
hypercube 4 = cycle 4 □g cycle 4                          johnson (n + 1) n = complete (n + 1)
johnson n k = johnson n (n - k)                           (k ≤ n)
(G ·g H)ᶜ = Gᶜ ·g Hᶜ
empty n ·g G = empty n □g G
completeMultipartite (List.replicate m d) = complete m ·g empty d
(cocktailParty n)ᶜ = empty n □g complete 2
empty n ⊠g G = empty n □g G
empty m □g empty n = empty (m * n)                        bipartite n n = complete 2 ·g empty n
johnson (n + 2) n = triangular (n + 2)
rook 2 3 = prism 3                                        (cycle 6)ᶜ = prism 3
(G ∇g H) ·g K = (G ·g K) ∇g (H ·g K)
completeMultipartite ds ·g empty d = completeMultipartite (ds.map (· * d))
bipartite (a * d) (b * d) = bipartite a b ·g empty d
complete 2 ⊗g path n = path n ⊕g path n
complete 2 ⊗g cycle (2 * m) = cycle (2 * m) ⊕g cycle (2 * m)
complete 2 ⊗g cycle (2 * m + 3) = cycle (2 * (2 * m + 3))
complete 2 ⊗g bipartite m n = bipartite m n ⊕g bipartite m n
complete 2 ⊗g ladder n = ladder n ⊕g ladder n
complete 2 ⊗g hypercube n = hypercube n ⊕g hypercube n
IsBipartite G → complete 2 ⊗g G = G ⊕g G
circulant n (0 :: S) = circulant n S                      circulant n (k :: k :: S) = circulant n (k :: S)
circulant n (k :: S) = circulant n ((n - k) :: S)         circulant n [1, n - 1] = cycle n
circulant (2 * m) [m] = empty m □g complete 2
(cocktailParty (m + 1))ᶜ = circulant (2 * (m + 1)) [m + 1]
paley 13 = circulant 13 [1, 3, 4]                         paley 17 = circulant 17 [1, 2, 4, 8]
(paley 13)ᶜ = paley 13                                    (paley 17)ᶜ = paley 17
paley 9 = completeMultipartite [3, 3, 3] = complete 3 ·g empty 3
petersenᶜ = triangular 5                                  petersen = (lineGraph (complete 5))ᶜ
tadpole m 0 = cycle m                                     tadpole 0 k = path k
lollipop m 0 = complete m                                 lollipop 0 k = path k
lollipop 1 k = path (1 + k)                               spider [k] = path (1 + k)
spider (List.replicate j 0) = empty 1                     cyclePendant m (List.replicate j 0) = cycle m
spider [a, b] = path (1 + a + b)                          thetaGraph [k] = path (k + 2)
spider (List.replicate n 1) = star n                      star 2 = path 3
doubleStar m 0 = star (m + 1)                             doubleStar 0 n = star (n + 1)
thetaGraph [] = empty 2                                   thetaGraph (List.replicate (j + 1) 0) = complete 2
thetaGraph [a, b] = cycle (2 + a + b)                     thetaGraph [a, b] = thetaGraph [b, a]
doubleStar m n = doubleStar n m                           cyclePendant m [1] = tadpole m 1
spider (0 :: ks) = spider ks                              thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks)
lollipop 2 k = tadpole 2 k                                lollipop 3 k = tadpole 3 k
tadpole 2 k = path (2 + k)                                lollipop 2 k = path (2 + k)
tadpole 1 k = path (1 + k)                                cyclePendant 1 [k] = star k
spider (pre ++ 0 :: post) = spider (pre ++ post)          cyclePendant m (ks ++ [0]) = cyclePendant m ks
spider ks = spider ls, whenever ks.Perm ls                spider (pre ++ a :: b :: post) = spider (pre ++ b :: a :: post)
thetaGraph xs = thetaGraph ys, whenever xs.Perm ys        thetaGraph [a, b] = thetaGraph [b, a]
thetaGraph (List.replicate n 1) = bipartite 2 n           spider ks = star ks.length, whenever ∀ k ∈ ks, k = 1
```

plus commutativity and associativity for `disjUnion`, `join`, and the Cartesian, tensor, strong
and lexicographic products, and the units and annihilators of each (`empty 1` for the products,
`empty 0` for the Cartesian/strong/lex products, which collapse when either factor is empty).
`empty 1` rather than `complete 1` is the simp-normal form, since `complete_one` points that way.

Three moves prove almost all of it:

1. `mk_eq_empty` / `mk_eq_complete`: a graph whose adjacency is uniformly `false` (resp. `true`
   off the diagonal) is `empty (Fintype.card G.V)` (resp. `complete …`), the relabelling coming
   from `Fintype.equivFin`. The hypothesis is usually `by decide`. This handles every "this
   degenerate case is edgeless/complete" lemma without ever naming a bijection.
2. `CGraph.isoOfAdj e (by decide)` for the sporadic small graphs — supply the vertex bijection as
   a `![…]` / `![…]` pair and let the kernel check both directions. `bipartite 2 2 = cycle 4`,
   `foldedCube 3 = bipartite 4 4` and `paley 5 = cycle 5` go this way.
3. Rewriting at the `IsoGraph` level, once enough of the above is in place: `wheel 2 = complete 3`
   is `wheel_eq_join`, `cycle_two`, `join_complete`.

`completeMultipartite` needed a fourth. Its vertex type is the dependent
`Σ i : Fin ds.length, Fin (ds.get i)`, which no amount of `decide` will touch, so the file builds
`sigmaFinSuccEquiv : (Σ i : Fin (n + 1), α i) ≃ α 0 ⊕ Σ i : Fin n, α i.succ` (Mathlib has no such
equivalence) and turns it into `CGraph.Iso.sigmaUnionSucc`. That gives the cons rule
`completeMultipartite (d :: ds) = join (empty d) (completeMultipartite ds)`, after which the whole
family is reachable by `join`-level rewriting: the append rule, `[a, b] = bipartite a b`,
`star n = completeMultipartite [1, n]`, `book n = join (complete 2) (empty n)`,
`(completeMultipartite ds).V = ds.sum`, `cocktailParty 2 = cycle 4`.

The `ofEdges` families needed a fifth. `tadpole`, `lollipop`, `spider` and `cyclePendant` are
`ofEdges n es` over `Fin n`, so their degenerate cases are equalities of `CGraph`s on the nose —
nothing is relabelled, the edge list simply *becomes* the edge list of a cycle, a clique or a
path. What that needs is a closed form for each list generator:
`pathEdges (List.range (m + 1)) = (List.range m).map (fun i ↦ (i, i + 1))`, proved by peeling the
front off with `List.range_succ_eq_map` and pushing the shift through with `pathEdges_map_succ`;
`cycleEdges (k + 1) = (List.range k).map (fun i ↦ (i, i + 1)) ++ [(k, 0)]`, the same plus a
wrap-around edge split off by `pathEdges_concat`; and membership lemmas for `cliqueEdges` and
`legEdges`. `eq_ofRel` then turns each identity into arithmetic on the indices, which `omega`
closes — with `succ_mod_eq_iff` supplying the wrap-around, since `omega` cannot see through a `%`
whose modulus is a variable. One pleasant accident: `legEdges 0 0 k`, the leg hung off vertex `0`
whose fresh vertices also start at `0`, begins with the loop `(0, 0)`, and `ofRel` deletes the
diagonal, so `tadpole 0 k` and `lollipop 0 k` are literally `path k`.

The rest of that family is *not* free that way. `spider [a, b] = path (1 + a + b)`,
`thetaGraph [k] = path (k + 2)`, `spider (List.replicate n 1) = star n` and
`doubleStar m 0 = doubleStar 0 n = star (n + 1)` draw the same graph with a different numbering,
so each carries an explicit permutation of `Fin n`. Three of them do all the work: `foldAt a N`
folds the interval `[0, a]` back on itself, which straightens the two legs of a spider into one
run; `rotTail N` rotates `[1, N-1]` one step down, which moves the second pole of a one-path theta
graph to the far end; and `swapZeroOne N` exchanges the two centres of a double star. The star
identities also cross from the `ofEdges` families to the `Sum`-typed `bipartite`, so they compose
with `finSumFinEquiv` too.  `thetaGraph (List.replicate n 1) = bipartite 2 n` is the same crossing
one dimension up: a theta graph whose paths each carry a single internal vertex is `K_{2,n}`, with
the two poles on one side and the `n` midpoints on the other, so `finSumFinEquiv` splits
`Fin (2 + n)` and `mem_thetaEdges_replicate_one` — proved by the usual induction through
`thetaEdges_cons` and `mem_thetaEdges_single` — reduces each of the four `Sum` cases to `omega`.
`thetaGraph_of_all_one` and `spider_of_all_one` then drop the `List.replicate` by way of
`List.eq_replicate_iff`, so a list of ones in any form is recognised.

Two things make those proofs bearable. The first is phrasing adjacency in terms of the underlying
naturals once and for all — `path_adj_val` and `ofEdges_adj_val` restate `Adj u v = true` as a
condition on `u.1` and `v.1` — since `(spider legs).V` is only definitionally `Fin n`, and nothing
about `Fin` fires under `simp` through that. The second is keeping the arithmetic in a lemma of
its own. Stated in one go, `spider [a, b] = path (1 + a + b)` hands `omega` an eight-disjunct
disjunction of three-conjunct clauses, whose negation is some `3^8` cases: 250-450 s, measured
(and eliminating the truncated subtraction makes it *slower*, not faster). Split out as
`foldAt_pair_iff`, with the disjunct picked by hand going forwards and `rintro`-split coming back,
the same content elaborates in seconds. Two smaller `omega` quirks show up in the same proofs: it
gives up when a hypothesis is literally `False`, and when the goal mentions `True` — both of which
`split_ifs` produces — hence the `(‹False›).elim` and `simp only [true_and]` fallbacks.

The two-path theta graph is the one that needs the whole apparatus. `thetaGraph [a, b]` draws a
cycle, but its numbering visits the two poles first and then each path in turn, so the
relabelling `thetaCycleFwd a b` sends `0 ↦ 0`, `1 ↦ a + 1`, the first path's interior down by one
and the second path's interior *backwards*, since that path is traversed towards the pole `0`
rather than away from it. Rather than compare the two adjacency relations head-on, the proof
factors through a *directed* step lemma: `(F p + 1) % (2 + a + b) = F q` holds exactly when
`(p, q)` is an edge of the first path or `(q, p)` is an edge of the second (`thetaCycle_step`),
which becomes a finite case split once `succ_mod_eq_iff` has removed the `%`. Symmetrising that
back into an undirected `Adj` statement is pure `Or`-shuffling, plus `succ_mod_ne` — a step around
a cycle of length at least two never stands still — to recover `F p ≠ F q` for free. Splitting the
edge list one path at a time (`thetaEdges_cons`) and describing a single path once
(`mem_thetaEdges_single`) means both paths are the same four disjuncts at different offsets. Even
so, the forward direction needs its disjunct chosen per branch, and the two halves of
`succ_mod_eq_iff` choose *different* edges — from the pole `1`, wrapping around means `b = 0`
while not wrapping means the far end of the second path — so the disjunction in the hypothesis has
to be `rcases`d before the `first | refine …` cascade, not after.

`doubleStar m n = doubleStar n m` is the same recipe one size down: `doubleStarSwapFwd` exchanges
the two centres and slides the two leaf blocks past each other. Both of these permutations are
built the cheap way — a plain `ℕ → ℕ` function with a bound lemma and a round-trip lemma, each
`unfold …; split_ifs <;> omega`, and `Fin.ext` to assemble the `Equiv` — which avoids the long
`show` blocks that `foldAt` and `rotTail` needed. `cyclePendant m [1] = tadpole m 1`, by contrast,
is on the nose: a single pendant vertex *is* a leg of length one.

A few identities are on the nose for a softer reason: the two edge lists are different lists that
meet the same *unordered* pairs. `ofEdges` symmetrises, so `ofEdges_congr` — same symmetrised
membership, same graph — closes all of them, and `ofEdges_append_congr` specialises it to the
shape the decorated families actually have, a cycle or clique part followed by the legs. That is
all `lollipop 2 k = tadpole 2 k` and `lollipop 3 k = tadpole 3 k` need, since `K₂ = C₂` and
`K₃ = C₃` as edge lists up to orientation: `simp only [mem_cliqueEdges, mem_cycleEdges]; omega`.
Numerals are the catch — `mem_cycleEdges_succ` is stated for `cycleEdges (k + 1)` and does not fire
on `cycleEdges 2`, so `mem_cycleEdges` restates membership for an arbitrary length. `simp` normal
form then continues past the tadpole: `tadpole 2 k = path (2 + k)`, one more `swapZeroOne`, so that
the tail leaves from the far end of the single edge. In the same vein a spider drops its empty legs
(`spider (0 :: ks) = spider ks`) and a theta graph drops a duplicated direct pole-to-pole edge
(`thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks)`) — for the latter the two edge lists differ by
one repeated `(0, 1)`, which `tauto` handles once `thetaEdges` is unfolded one step.

`ofEdges` discards the diagonal too, which is why `ofEdges_congr` only asks for agreement on pairs
of *distinct* vertices.  That extra freedom is what makes `cycleEdges 1 = [(0, 0)]` — the
one-vertex "cycle", which is a bare loop — droppable: `ofEdges_cycleEdges_one_append` deletes it,
and with it `tadpole 1 k = path (1 + k)` and `cyclePendant 1 [k] = spider (List.replicate k 1)`,
i.e. the star `K_{1,k}`, are two rewrites each.  Splitting the leg list of a spider along an append
(`spiderEdges_append`, the second block starting where the first left off) generalises the
empty-leg rule to `spider (pre ++ 0 :: post) = spider (pre ++ post)`; the corresponding rule for
pendant vertices holds only at the *end* of the list (`cyclePendant m (ks ++ [0])`), since a `0` in
the middle would still shift the later blocks onto later cycle vertices.

A spider depends only on the *multiset* of its leg lengths (`spider_perm`), which is the one
identity here whose two sides need not agree on any vertex.  Exchanging two adjacent legs is the
relabelling `swapBlocksFwd` that swaps the blocks `[s, s + a)` and `[s + a, s + a + b)` and fixes
everything else; `nonempty_iso_ofEdges_swap_legs` states it for an *abstract* edge list
`P ++ (legEdges 0 s a ++ (legEdges 0 (s + a) b ++ Q))`, asking only that `P` live below the two
blocks and `Q` on the centre `0` and above them, so the spider case is one application with `P`
the earlier legs and `Q` the later ones (`mem_spiderEdges_bound` supplies the two side conditions).
Going from an adjacent swap to an arbitrary permutation is the usual `List.Perm` induction with one
twist: the `cons` case is not provable as stated, so the statement carries a *prefix* parameter and
`spider (pre ++ x :: l)` is read as `spider ((pre ++ [x]) ++ l)`, which is the induction hypothesis
at a longer prefix.

The same relabelling permutes the *paths* of a theta graph, so the block exchange is stated once,
for an abstract middle segment: `nonempty_iso_ofEdges_swapBlocks` asks only that the exchange fix
every vertex `P` and `Q` touch and carry the middle segment onto its counterpart.  Both the leg
version and the theta version are then a handful of lines, the theta one via a pair of directed
lemmas (each path lands on the copy of itself that starts one block over) rather than one
sixteen-disjunct `omega` call.  `thetaGraph [a, b] = thetaGraph [b, a]` used to go through the
identification of a two-path theta graph with a cycle; it is now the two-element case of
`thetaGraph_perm`.

The structural laws are the exception, since they are statements about all graphs at once. Each
is a `CGraph.Iso.*Assoc` built on `Equiv.prodAssoc`, whose adjacency obligation is reduced to a
Boolean tautology: rewrite with the `*_adj` equations and `decide_prod_eq`
(`decide (p = q) = (decide (p.1 = q.1) && decide (p.2 = q.2))`) until every equality test is
between vertices of a single factor, `generalize` the six atoms, and `decide`.

Distributivity over `disjUnion` is structural in the same way, but the equivalence is
`Equiv.prodSumDistrib` (`Equiv.sumProdDistrib` for the lexicographic product, which distributes in
its first factor only — `K₂[K₁ + K₁]` is `K₄`, not `K₂ + K₂`). Here the four `rintro` cases are the
four ways of pairing `inl`/`inr`, and each needs an explicit `show` before `simp`: the equivalence
is applied to a pair whose second component is only definitionally a `Sum`. The same reducibility
gap is why `Sum.inl.injEq` does not fire on `(disjUnion G H).V`, so the file states it again as
`CGraph.disjUnion_inl_eq_inl` with the `Eq` pinned to that type. All seven quotient-level lemmas
are `@[simp]`, pushing `disjUnion` outwards. Specialising them at `empty 2 = empty (1 + 1)` and
using the `empty 1` units gives `cartesianProduct (empty 2) G = disjUnion G G` for the Cartesian,
strong and lexicographic products (not the tensor product, which is edgeless there).

The complement identities for the hub-and-rim graphs are all one rewrite once `compl_join` and
`compl_complete` are available, since `star`, `wheel`, `fan` and `book` are each a join: the hub
side becomes edgeless and the two sides stop talking to each other.

Two more families come out of `empty n □ G`, which is `n` disjoint copies of `G`. The
lexicographic and strong products agree with the Cartesian one there (`empty_lexProduct`,
`empty_strongProduct` — only the tensor product breaks ranks, being edgeless), and the
lexicographic product is the one of the four whose complement is again a product — `compl (G[H]) = (compl G)[compl H]`.
Putting those together, `K_m[G]` is `m` copies of `G` with every pair of copies joined, i.e.
`compl (empty m □ compl G)`, and the complete multipartite graphs with equal parts are exactly the
blow-ups `K_m[empty d]`; `cocktailParty n = K_n[empty 2]` and its complement is a perfect matching.
The complement proof needs the pair equality restated at `(lexProduct G H).V` as
`CGraph.lexProduct_pair_eq`, the same reducibility dodge as `disjUnion_inl_eq_inl`.

Blowing up is a `join`-level operation too: the lexicographic product distributes over `join` in
its first factor (complementation exchanges that with the `disjUnion` rule already proved), so
blowing up a complete multipartite graph by `empty d` just multiplies every part by `d`.

The tensor product with `K₂` is the bipartite double cover, and whether it splits is exactly the
question of bipartiteness. `CGraph.Iso.tensorTwoOfColouring` is the splitting criterion in its
final form: given any proper 2-colouring `c : G.V → Bool`, twisting the `K₂` coordinate by the
colour of the other (`CGraph.Iso.colourTwist`) turns `K₂ × G` into `empty 2 □ G`, which is two
copies of `G`. So the work is all in exhibiting colourings, and `IsBipartite` collects them:
the empty graphs, complete bipartite graphs, stars, paths and even cycles directly; disjoint
unions and Cartesian products of bipartite graphs by combining colourings (`xor` for the product),
tensor products as soon as one factor is bipartite; and hypercubes, ladders and even prisms as
products.  The decorated families join the list too — spiders and double stars because they are
trees, tadpoles and cycles-with-pendants when the cycle is even — and there the colour of a vertex
is *not* a function of its number: it depends on which leg or which pendant block the vertex sits
in.  `spiderDepth` and `pendantOwner` recover that by the same recursion the edge lists are built
by, so the colouring is `decide (spiderDepth 1 ks v % 2 = 1)` and the proof obligation is one
statement per edge shape.  Theta graphs are bipartite exactly when all their paths have the same
parity of length, and `thetaDepth b` is `spiderDepth` with the far pole `1` pinned to the colour
`b` — the far end of a path with `k` internal vertices is at distance `k` from the near pole, so
`(k + b) % 2 = 1` is precisely what makes the two poles disagree.  One statement covers both
parities, with `b = 1` for the paths of odd length (`isBipartite_thetaGraph_even`, the poles in
different classes) and `b = 0` for those of even length (`isBipartite_thetaGraph_odd`, the poles
together).  The two-path converse is free: `thetaGraph [a, b]` is a cycle of length `2 + a + b`,
so paths of different parity give an odd cycle and `not_isBipartite_thetaGraph_pair`.
On the other side, complete graphs on three or more vertices are not bipartite
(pigeonhole on a triangle) and neither are odd cycles: walking around the cycle the colour
alternates with the parity of the index, which the edge closing the cycle contradicts.

Both of those arguments generalise, and the general forms retire the rest of the decorated
families.  `CGraph.not_isBipartite_of_triangle` is the pigeonhole on its own — any three mutually
adjacent vertices, no numbering involved — which is what `not_isBipartite_complete` now calls, and
what settles the wheel, whose hub is adjacent to both ends of every rim edge.  Reaching into a
`join` for that needed adjacency to compute, so `join_adj_inl_inl`, `join_adj_inr_inr`,
`join_adj_inl_inr` and `join_adj_inr_inl` are `@[simp]` in `Constructions.lean`; the two same-side
ones want the `Sum` disequality supplied by hand, since `simp` will not discharge
`decide ¬Sum.inl a = Sum.inl c` from `a ≠ c` on its own.  The alternating-colour argument becomes
`CGraph.not_isBipartite_ofEdges_of_odd_cycle`: an edge list containing an odd cycle through
`0, 1, …, m-1` is never bipartite.  Its hypothesis asks only that each `cycleEdges m` entry appear
in *either* orientation, which is what lets the lollipop use it — the triangle `0, 1, 2` lives in
its head, but `cliqueEdges` stores `(0, 2)` where the cycle wants `(2, 0)`.  Odd tadpoles and odd
cycles-with-pendants then follow by `List.mem_append_left`, with the decorations simply ignored.

Underneath both of those sits `CGraph.not_isBipartite_of_odd_walk`, which asks for no structure at
all: a function `f : ℕ → G.V` whose consecutive values are adjacent for `m` steps and which
returns to where it started, with `m` odd.  The induction on the walk is the only place the
alternation argument is written down; the edge-list version is now three lines that instantiate it
at `k ↦ k % m`, and the closing edge is nothing more than `m % m = 0`.  The point of factoring it
out is that not every odd cycle in the library is presented as an edge list.

The folded cube is the case in point.  `foldedCube n` is `Q_n` with the antipodal pairs joined, so
its edges flip either one coordinate or all `n`, and it is bipartite exactly when `n` is odd.  One
direction is a colouring: `CGraph.card_ne_parity` says the number of coordinates where `x` and `y`
differ has the same parity as the total number of `true`s in the two of them — positions where
both are `true` get counted twice — so for odd `n` both edge shapes flip the parity of the weight.
That identity is proved by turning all four `Finset.card_filter`s into sums and comparing them
pointwise, where `cases x i <;> cases y i` is the whole content.  The other direction is a walk:
`CGraph.prefixVec n k`, the string whose first `k` coordinates are `true`, steps from `0…0` to
`1…1` one coordinate at a time in `n` steps, and the antipodal edge closes it in one more.  For
even `n` that is an odd closed walk, so `not_isBipartite_foldedCube_of_even`.  The walk has to be
a total function `ℕ → V`, so it is `if k ≤ n then prefixVec n k else prefixVec n 0`, which makes
`f (n+1) = f 0` hold by `if_neg`/`if_pos` rather than by arithmetic.

Circulants split the same way, and there the two halves are cleanly complementary.
`isBipartite_circulant`: if `n` is even and every element of the connection set is odd, the parity
of the index is a proper colouring — reducing mod an even number does not change parity, so
`sub_mod_cases` plus `omega` is the whole argument, in either of the two orientations the
adjacency admits.  `not_isBipartite_circulant_of_odd`: if `n` is odd and the connection set has
any `d` with `0 < d < n`, then `k ↦ k·d mod n` is a closed walk of length `n`, which is odd.  The
only real content there is that consecutive steps really do differ by `d`: with `a = k·d mod n`
the next vertex is `(a + d) mod n`, which is `a + d` or `a + d - n`, and both cases give
`d` back.  Note the asymmetry — the even case needs a condition on every element of the set, the
odd case only needs one usable element, since a single one already forces the odd cycle.

The disjoint union and the Cartesian product were only ever stated in one direction — both parts
bipartite gives a bipartite whole.  Both converses hold, and they are easier than the forward
directions: a colouring of `G ⊔ H` restricted along `Sum.inl` is a colouring of `G`, and a
colouring of `G □ H` restricted to the slice `· ↦ (·, b)` for any fixed `b : H.V` is a colouring
of `G`, since `(x, b)` and `(y, b)` are adjacent exactly when `x` and `y` are.  So
`isBipartite_disjUnion_iff` is an unconditional `simp` iff, and
`isBipartite_cartesianProduct_iff` is an iff once both factors are nonempty (an empty factor
kills every edge and makes the product bipartite regardless of the other one).  Those give a
couple of families for free: the rook's graph `K_m □ K_n` is not bipartite as soon as `m ≥ 3`
(`not_isBipartite_rook`), and the prism over an odd cycle is not bipartite
(`not_isBipartite_prism_odd`), in both cases by pushing the failure down to a single factor.

The graphs on `k`-subsets go the same way once you can produce three vertices in the right
position.  For that there is a block construction, `Finset.attachFin` applied to `Finset.Ico a
(a + k)`, whose cardinality and membership are both immediate; three blocks at `0`, `k` and `2k`
are pairwise disjoint, so `not_isBipartite_kneser` holds whenever `k ≥ 1` and `3k ≤ n`.  For the
Johnson graph the triangle is a fixed `(k-1)`-set together with three different extra points, so
`not_isBipartite_johnson` needs only `n ≥ k + 2`; specialising to `k = 2` says triangular graphs
on four or more points are not bipartite.  The Petersen graph escapes both — `kneser 5 2` has
`3k > n` and is genuinely triangle-free — so it gets the odd-walk treatment instead, with its
outer five-cycle `{0,1}, {2,3}, {4,0}, {1,2}, {3,4}` written as a function of `k % 5` and the
five adjacencies discharged by `decide`.

The join behaves like the disjoint union on one side and unlike it on the other.  Restricting a
colouring along `Sum.inl` still works, so `IsBipartite.of_join_left`/`_right` hold and a
non-bipartite side poisons the whole join.  But the join also *creates* edges, and three nonempty
sides always give a triangle — `not_isBipartite_join_join` needs nothing at all about the three
graphs beyond a vertex in each.  Since `completeMultipartite_cons` peels parts off as joins, that
one lemma settles the whole family: three nonempty parts is enough
(`not_isBipartite_completeMultipartite`), which specialises to books with at least one page and to
cocktail party graphs on at least three pairs.  Fans go the other way round, through the
edge-plus-vertex triangle `not_isBipartite_join_of_adj_right`: the hub sees the first edge of the
path.

Over an odd cycle, then, the cover cannot split, and in fact it is connected:
`K₂ × C_n ≅ C_{2n}` via the Chinese remainder bijection `k ↦ (k % 2, k % n)`, whose injectivity is
elementary (`k` and `k % n` differ by `0` or `n`, and `n` is odd) rather than a coprimality
argument. `omega` cannot see through a `%` whose modulus is a variable, so that proof first turns
every wrap-around into a disjunction — `succ_mod_eq_iff` for a step around a cycle,
`mod_of_lt_two_mul` for a reduction below `2n` — after which one `omega` closes the whole
adjacency equivalence.  A third member of that family, `sub_mod_cases`, splits the circulant
difference `(y + n - x) % n` into the forwards and backwards cases; it is what proves that a `0`
in a connection set is inert, and that `circulant (2m) {m}` is a perfect matching (its `1`-nonzero
connection set makes `i ↦ i + m` an involution, so the graph is `empty m □ K₂`).  The same two
facts it yields — the forwards and backwards differences are nonzero and sum to `n` — give
`circulant_congr`: two connection sets that agree on `(0, n)` define *the same `CGraph`*, which is
where the inert-`0`, inert-duplicate and `k ↦ n - k` rules come from.

Paley graphs are self-complementary because multiplication by a non-residue exchanges the squares
with the non-squares; `compl (paley 13) = paley 13` and `compl (paley 17) = paley 17` are that
argument with the witnesses `x ↦ 2x` and `x ↦ 3x` written down and the adjacency checked by
`decide`.  `paley 9` is a cautionary case: `CGraph.paley` reads differences in `ZMod q`, which is
a field only for prime `q`, so at `q = 9` the squares are `{0, 1, 4, 7}` and the graph joins `x`
to `y` whenever `3 ∤ x - y` — that is `K₃,₃,₃`, not the rook's graph `R(3, 3)` that `GF(9)` would
give.  The identity `paley 9 = completeMultipartite [3, 3, 3]` records exactly that.

The file ends with a dozen `example`s — `compl (compl (cycle 5)) = cycle 5`, `circulant 7
[0, 3, 3] = circulant 7 [3]`, `lexProduct (empty 1) (lexProduct G (empty 1)) = G` and the like —
closed by `simp` alone.  They prove nothing new; they are a regression test that the `@[simp]`
lemmas compose and that none of them loops.  Vertex counts are `@[simp]` for every lifted
construction, so `(rook m n).V = m * n` is also just `simp`.

Johnson duality, `J(n, k) ≅ J(n, n - k)`, is the one identity here whose bijection is interesting:
`CGraph.complSubsets` sends `s` to `sᶜ`, and `|sᶜ ∩ tᶜ| = n - |s ∪ t| = n - 2k + |s ∩ t|` turns an
intersection of size `k - 1` into one of size `(n - k) - 1`. Every step is truncated ℕ subtraction,
so the two sets have to be known distinct — `s = t` forces `|s ∩ t| = k` — before `omega` will
close it.

A recurring nuisance in all of this: a type like `(CGraph.complete 2).V` is definitionally `Fin 2`
but not *reducibly* so, and numerals, `simp` lemmas and instances all match at reducible
transparency. The fix is always the same — restate the goal with an explicit `show` at default
transparency, ascribing whole subterms (`((if x 0 then 1 else 0 : Fin 2))`, not just the branch),
and use `inferInstanceAs` for the instances.

`lineGraph` and `mycielskian` are lifted too, and are the two cases where the congruence is not
just a relabelling of the same vertex set: the line graph transports along
`SimpleGraph.Iso.mapEdgeSet` (an edge maps to `Sym2.map i`, and two edges meet iff their images
do), the Mycielskian along `Equiv.optionCongr (Equiv.sumCongr i i)`. Their identities are counted
by `E` rather than `V` —

```
lineGraph (empty n) = empty 0        lineGraph (star n) = complete n
lineGraph (complete n) = johnson n 2 = triangular n
lineGraph (complete 4) = cocktailParty 3
lineGraph (cycle (n+3)) = cycle (n+3)
lineGraph (path (n+1)) = path n
lineGraph (bipartite m n) = rook m n
lineGraph (disjUnion G H) = disjUnion (lineGraph G) (lineGraph H)
mycielskian (empty 0) = empty 1      mycielskian (complete 2) = cycle 5
mycielskian (empty n) = disjUnion (star n) (empty n)
```

— `lineGraph (complete n)` being the proof in the file that builds its bijection with
`Equiv.ofBijective` rather than writing it down: an edge of `Kₙ` is sent to its
`Sym2.toFinset`, a two-element subset of `Fin n`, and two *distinct* two-element subsets meet
exactly when they meet in one point, which is the adjacency of `J(n, 2)`. The last line is the
Mycielskian of an edgeless graph, where the apex and the `n` shadow vertices form a star and the
originals stay isolated.

That last line is also the *only* bipartite Mycielskian, which is the construction's whole point.
`mycielskian (complete 2) = cycle 5` says where the obstruction comes from, and
`not_isBipartite_mycielskian` says it in general: an edge `a – b` of `G` closes up into a pentagon
`a – b – a' – w – b' – a` through the two shadows and the apex.  No cycle machinery is needed to
see it — the shadow `a'` is adjacent to `b` and so must copy the colour of `a`, likewise `b'`
copies `b`, and the apex is adjacent to both of those, which now disagree.  A five-way case split
on `Bool` is the whole proof.  So `mycielskian` of a complete graph, a cycle, a path, a star or a
complete bipartite graph is never bipartite — the last of these being the striking one, since it
is a construction that takes a bipartite graph out of the bipartite world without going anywhere
near a triangle.

`lineGraph (disjUnion G H)` uses the same trick as `lineGraph (cycle n)`, `lineGraph (path n)` and
`lineGraph (bipartite m n)`: give the map in the easy direction — here an edge of `G` or of `H`,
pushed forward along `Sum.inl`/`Sum.inr` — prove it injective, and let
`Fintype.bijective_iff_injective_and_card` supply the inverse from `E (G + H) = E G + E H`. Nobody
has to write the inverse down, at the cost of the definition being `noncomputable`.

`triangular 4 = cocktailParty 3` — the octahedron — is the one identity here that `SRG.lean` also
proves, by `native_decide` on the canonical keys. The version in `Identities.lean` is
kernel-checkable: `T(4)` is `compl (kneser 4 2)`, `kneser 4 2` is three disjoint edges (a six-point
`decide` on an explicit `Equiv.ofBijective`), and three uses of the cons rule turn
`compl (cocktailParty 3)` into the same disjoint union.

`compl (rook m n) = tensorProduct (complete m) (complete n)` also holds at the level of `CGraph`:
both sides are on `Fin m × Fin n`, so `CGraph.ext'` plus a four-way case split on whether the two
squares agree in each coordinate is the whole proof. Two squares are non-adjacent in the rook's
graph exactly when they agree in neither coordinate, which is the tensor product. Specialising to
`m = n = 2` gives `K₂ × K₂ = 2K₂` out of `rook_two_two` and `compl_cycle_four`.

`circulant n [1] = cycle n` is the one identity that holds already at the level of `CGraph` —
both sides are `ofRel` on `Fin n`, so it is an equality of graphs, not of isomorphism classes, and
it lives in `Constructions.lean`. What it costs is the modular arithmetic: for distinct
`a, b < n`, `(b + n - a) % n = 1 ↔ (a + 1) % n = b`, by trichotomy on `a` versus `b` and a split
on whether `a + 1` wraps. Distinctness is genuinely needed — at `n = 1` the single vertex is its
own successor but has difference `0`.

The two variable-`n` line graphs are the same recipe run by hand. The edges of `Cₙ` are the
consecutive pairs `s(i, i+1 mod n)` and the edges of `Pₙ₊₁` are the pairs `s(i.castSucc, i.succ)`,
so in both cases there is an obvious map *into* the `Sym2` edge subtype; `E_cycle` and `E_path`
give the cardinality, so `Fintype.bijective_iff_injective_and_card` upgrades injectivity to a
bijection and no surjectivity argument is needed. Two edges then meet exactly when their indices
are consecutive, which is the adjacency of the smaller graph. The cycle version is where `n ≥ 3`
is needed, and it enters in exactly one place: injectivity fails at `n = 2`, where `s(0, 1)` and
`s(1, 0)` are the same edge — the content is `cyc (cyc j) ≠ j`, two steps never return.

`lineGraph (bipartite m n) = rook m n` runs the same way and is the cleanest of the three: an edge
of `K_{m,n}` *is* a square `(i, j)` of the board, `E_bipartite` says there are `m * n` of them, and
two squares share a vertex exactly when they share a row or a column, which is
`cartesianProduct (complete m) (complete n)`. `lineGraph_star` is the `m = 1` case, but it is left
with its own proof so that the star does not depend on the general bijection.

Alongside the `V_*` lemmas, which read the vertex count of every family off its `CGraph`
counterpart, there is now a matching set of `E_*` lemmas for the edge count.  The families are
one-liners — `E ⟦G⟧ = G.E` is definitional, so `E_complete`, `E_cycle`, `E_bipartite` and friends
are just the `CGraph` lemma under a new name.  The operations need the usual three-step dance:
rewrite `⟦g⟧` as `⟦g.canonicalize⟧` to get a `DecidableEq` instance, push the constructor inside
the quotient with `join_mk`/`cartesianProduct_mk`/…, and apply the `CGraph` lemma.  That gives
`E_disjUnion`, `E_join`, `E_cartesianProduct`, `E_tensorProduct` and `E_mycielskian`, plus
`E_compl_add` in the subtraction-free form `(compl G).E + G.E = C(|G|, 2)`.

From those the derived counts fall out by arithmetic: `E_wheel`, `E_ladder`, `E_prism` and
`E_rook` are one rewrite each, and the two recursive families need a little more.  The hypercube
is stated as `2 * (hypercube n).E = n * 2 ^ n` so that no division appears, and follows by
induction on `hypercube_succ`.  Complete multipartite graphs are stated the same way as the
complement, `(completeMultipartite ds).E + Σ C(dᵢ, 2) = C(Σ dᵢ, 2)`, and the induction over
`completeMultipartite_cons` needs exactly one fact about binomials — `choose_two_add`, that
splitting `a + b` points into two groups splits the pairs into within-`a`, within-`b` and across,
which itself is an induction on `b` off `choose_two_succ`.

Connectivity gets the same treatment. `IsConnected`, `IsAcyclic` and `IsTree` were only ever
stated for `CGraph`, but their quotient versions are `Quotient.lift`s whose `_mk` lemmas are
`rfl`, so `isConnected_complete`, `isConnected_path`, `isConnected_cycle`,
`isConnected_bipartite`, `isAcyclic_empty`, `isAcyclic_path`, `isTree_path` and
`not_isAcyclic_cycle` transfer verbatim, and `not_isConnected_disjUnion` and `isConnected_join`
transfer with `0 < G.V` hypotheses through the three-step dance.

The one genuinely new ingredient is the Cartesian product. Mathlib already knows
`SimpleGraph.connected_boxProd`, that `G □ H` is connected iff both factors are, and
`toSimple_cartesianProduct` identifies our `cartesianProduct` with `□` on the underlying simple
graphs — the adjacency conditions match after `decide_eq_true_eq`, and `tauto` closes the rest.
That upgrades the product case to an `iff` at both levels, which is what makes the grid-like
families cheap: `isConnected_ladder`, `isConnected_prism` and `isConnected_rook` are one rewrite
each, and `isConnected_hypercube` is an induction on `hypercube_succ`. `isConnected_star` needs a
case split, since `star 0` is `empty 1` rather than a bipartite graph. All of these are `simp`
lemmas, so `IsConnected (hypercube 4)` and `IsConnected (cartesianProduct G (path 3))` given
`IsConnected G` are both discharged by `simp`.

Having both `V_*` and `E_*` makes Euler's count for trees worth transferring too:
`isTree_iff` says `IsTree G ↔ IsConnected G ∧ G.E + 1 = G.V`, out of Mathlib's
`isTree_iff_connected_and_card`. It turns most tree questions into arithmetic that the existing
`simp` set already answers — `isTree_star` is `1 + n` vertices against `n` edges, and
`not_isTree_cycle`, `not_isTree_wheel`, `not_isTree_prism` and `not_isTree_ladder` are each an
`omega` after rewriting with the counts. The complete graph needs one extra step, that
`C(n + 2, 2)` is positive, which is `choose_two_succ` again. Splitting the tree condition the
other way, `isTree_iff_isConnected_and_isAcyclic`, converts each of those into a
`not_isAcyclic_*` since connectivity is already known.

The same bound run one-sidedly gives `IsConnected.V_le_E_add_one` and its contrapositive
`not_isConnected_of_E_add_one_lt`, a graph with too few edges to be connected — which is the
shortest proof that `empty (n + 2)` is disconnected. Finally the join families inherit
connectivity from `isConnected_join`: `isConnected_completeMultipartite` for two nonempty parts,
and `isConnected_book`, `isConnected_cocktailParty` and `isConnected_fan` beneath it.

The clique number, independence number and diameter were in the same position `IsConnected` had
been in — a good stock of `CGraph` lemmas and nothing on the quotient — so they get the same
transfer. The families are one-liners, the operations go through `mk_canonicalize`, and that
brings over `indepNum_compl`/`cliqueNum_compl`, both numbers for `⊔` and the join,
`indepNum_completeMultipartite`, and the two product results that were proved for `CGraph`:
`indepNum_lexProduct` and `cliqueNum_strongProduct`.

The derived cases are then arithmetic on lists. `cliqueNum_completeMultipartite` is a one-line
induction on `completeMultipartite_cons` — each part contributes `min dᵢ 1`, one vertex if it is
nonempty — and with `List.map_replicate` that gives `cliqueNum_cocktailParty = n`, the cocktail
party graph on `n` parts having an `n`-clique. Its independence number is `2` by the dual
statement plus `max?` of a replicate. The star, wheel and book pick up both numbers from the
bipartite and join lemmas.

The strong and lexicographic products both contain the Cartesian product on the same vertex set —
`cartesianProduct_le_strongProduct` and `cartesianProduct_le_lexProduct` — so
`SimpleGraph.Connected.mono` upgrades `isConnected_cartesianProduct` to both of them for free.
They also both contain a triangle as soon as each factor has an edge, which
`not_isBipartite_of_triangle` turns into `not_isBipartite_strongProduct` and
`not_isBipartite_lexProduct`. Stating those on the quotient wants a way to say "has an edge"
without naming a vertex, and `0 < G.E` is it: `exists_adj_of_E_pos` recovers the two endpoints by
`Finset.card_pos` and an induction on the `Sym2`.

Vertex- and arc-transitivity were the last invariant with a full `CGraph` story and nothing on the
quotient, and they transfer the same way. The families — empty, complete, cycle, hypercube, folded
cube, `K_{n,n}` and the Kneser graphs — are one-liners; the complement and the four products go
through `mk_canonicalize`, and are named as dot-notation lemmas (`IsVertexTransitive.compl`,
`IsVertexTransitive.cartesianProduct`, …) so that they chain. Since `compl_compl` is an identity
on the quotient, the complement version is upgraded to an `iff` and tagged `simp`.

The derived cases are then whichever earlier identity puts a family into one of those shapes:
`triangular_eq_compl_kneser` for the triangular graph, `cocktailParty_eq_lexProduct` for the
cocktail party graph, and the definitional unfoldings for the rook graph, the prism and the
Petersen graph. `IsArcTransitive.lineGraph` covers the line graphs, since the arcs of `G` are
exactly the vertices of `L(G)`.

Strong regularity closes the list. `SRG.lean` builds its table at the `CGraph` level, so the
infinite families — the square rook graphs, `K(n, 2)` and `J(n, 2)`, the triangular graphs,
`K_{n,n}`, the cocktail party graphs and the Paley graphs — get quotient versions through the
`_def` bridging lemmas, and `IsSRGWith.compl` through `mk_canonicalize`. Being an isomorphism
invariant, this is where the quotient statement is the one you actually want: `IsSRGWith` on
`IsoGraph` is a property of the graph rather than of a particular labelling of it.

Degree sequences were the last invariant with no identities at all. Two hold for every graph:
`length_degSequence`, since sorting a multiset of degrees keeps one entry per vertex, and
`sum_degSequence` — the handshake lemma, `Multiset.sort_eq` composed with Mathlib's
`sum_degrees_eq_twice_card_edges`. Beyond those, the useful observation is that a *regular* graph
has a constant degree sequence, and `List.eq_replicate_iff` reduces that to "every member of the
sorted list is `k`", which is just `Multiset.mem_map` and regularity — no reasoning about the sort
order at all. Since `IsSRGWith` carries regularity as a field, `IsSRGWith.degSequence` then hands
back `List.replicate n k` for every family in the table above, and combining it with the handshake
lemma gives `IsSRGWith.two_mul_E : 2 * G.E = n * k`, so `omega` reads off edge counts
(`petersen.E = 15`, `(rook 3 3).E = 18`) from the parameters alone.

Two edge counts had `CGraph` versions that do not survive the quotient verbatim. `E_compl` does,
once `Fintype.card G.V` becomes `G.V`: `(compl G).E + G.E = C(G.V, 2)`, whose subtraction form and
the bound `E ≤ C(V, 2)` follow by `omega`. `E_lineGraph` does not — it is stated as
`∑ v, C(deg v, 2)`, a sum over a vertex type that only exists downstairs. The fix is the degree
sequence again: `sum_degSequence_map` says any sum of a function of the degrees is the same sum
taken over `degSequence`, so the quotient statement is
`(lineGraph G).E = ((degSequence G).map (C(·, 2))).sum` with no vertices in sight. Specialising it
to a constant degree sequence gives `IsSRGWith.E_lineGraph` and `E_lineGraph_complete`, and the
latter transports along `lineGraph_complete_eq_triangular` to `E_triangular`.

Not every regular graph is strongly regular, and the ones that are not still have constant degree
sequences. The `SRG.lean` machinery already computes neighbour-set cardinalities for several
families, so `isRegularOfDegree_of_card_nbrs` turns a `∀ v, (G.nbrs v).card = k` into Mathlib's
`IsRegularOfDegree` and hence into a `replicate` degree sequence. That covers the Kneser graphs
`K(n, k)` for every `k` and the rectangular rook graphs `m × n`, where the strongly regular
statements only reached `k = 2` and `m = n`; `two_mul_E_of_degSequence_replicate` then gives their
edge counts. The abbreviations also acquired the vertex counts they were missing — `rook`,
`triangular`, `ladder`, `prism`, `fan`, `book` and `cocktailParty`.

All four products of regular graphs are regular, and the neighbour sets say why in one line each:
in the Cartesian product the neighbours of `(a, b)` are `{a} × N(b)` together with `N(a) × {b}`,
in the tensor product they are `N(a) × N(b)`, in the lexicographic product `N(a) × V(H)` together
with `{a} × N(b)`, and in the strong product the block `(N(a) ∪ {a}) × (N(b) ∪ {b})` minus the
point itself — degrees `k + l`, `k · l`, `k · |H| + l` and `(k+1)(l+1) - 1`. Each union is
disjoint because `a ∉ N(a)`, which is `loopless`. On the quotient the hypotheses and the
conclusion are all of the form `degSequence _ = List.replicate _ _`, so the lemmas chain, and the
hypercube's degree sequence falls out by induction along `hypercube_succ` — with
`two_mul_E_hypercube` as the handshake corollary.

The cycles are the awkward case: nothing in the development computes a neighbour set of `cycle n`,
and doing it directly means the usual `Fin` modular arithmetic. Vertex-transitivity gets there
without any of that. An automorphism preserves degrees — Mathlib's `SimpleGraph.Iso.degree_eq`,
reached through `Iso.toSimpleIso` — so a vertex-transitive graph is regular, and its degree
sequence is `List.replicate V k` for *some* `k`. The handshake lemma then pins `k` down from the
vertex and edge counts alone: `degSequence_of_isVertexTransitive` needs only `V * k = 2 * E`. With
`isVertexTransitive_cycle`, `V_cycle` and `E_cycle` in hand the cycles are 2-regular, the prisms
follow from the Cartesian product, and `E_lineGraph_cycle` says `L(Cₙ)` has `n` edges — as it
should, being `Cₙ` again.

All of that invariant machinery pays off twice, because on the quotient `G ≠ H` *is* the statement
that `G` and `H` are non-isomorphic — there is no separate notion to define. Anything of the form
`f G ≠ f H` for an invariant `f` proves it (`ne_of_V_ne`, `ne_of_E_ne`, `ne_of_degSequence_ne`,
`ne_of_diameter_ne`, `ne_of_indepNum_ne`, `ne_of_cliqueNum_ne`), and so does any invariant
*predicate* that holds of one and fails for the other (`ne_of_pred`, with `ne_of_isConnected`,
`ne_of_isAcyclic`, `ne_of_isTree`, `ne_of_isBipartite` and the two transitivity versions as
special cases). `ne_of_degree_ne` packages the common argument that two regular graphs of the same
order but different degree cannot be isomorphic. From these, each standard family is injective in
its parameter (`complete_inj`, `cycle_inj`, `path_inj`, `star_inj`, `empty_inj`, all `simp`), and
the interesting separations are the ones where the cheap invariants agree: `C₆` and two triangles
have the same order, size and degree sequence and are told apart by connectivity (or by
independence number, against two copies of `K₃`); the triangular prism and `K₃,₃` are both cubic
on six vertices and are told apart by bipartiteness; the cube and `K₄ ⊔ K₄` are both cubic on
eight vertices with twelve edges, again separated by connectivity.

The diameter had been computed one graph at a time — each of `diameter_complete`, `diameter_path`,
`diameter_cycle` and `diameter_bipartite` is its own hand-rolled argument about walks in the
underlying `SimpleGraph`. Two reusable lemmas replace that for everything of diameter two: if any
two distinct vertices are adjacent or have a common neighbour then `ediam ≤ 2`
(`CGraph.ediam_le_two`, from `edist_le_two` on the two-edge walk), and adding one non-adjacent
pair pins it to exactly `2` (`CGraph.diameter_eq_two`, using that `edist` is neither `0` nor `1`).
Strong regularity supplies both hypotheses for free: `μ > 0` says precisely that non-adjacent
vertices have a common neighbour, and `k + 1 < n` produces a non-adjacent pair, because otherwise
`nbrs v = univ.erase v` would force `k = n - 1`. So **every strongly regular graph with `μ > 0` is
connected**, and **is of diameter two unless it is complete** — one proof covering the Petersen
graph, the rook's graphs, the cocktail-party graphs, the triangular graphs, the Paley graphs and
`Kₙ,ₙ`. Connectivity also comes back the other way: a nonzero diameter means the graph is
connected (`isConnected_of_diameter_ne_zero`), since a disconnected graph has diameter `0` by
convention.

The other big source of two-step graphs is the join, where two vertices on the same side share
every vertex of the other side as a neighbour and two vertices on opposite sides are adjacent
outright. That gives `diameter_join_le_two` for any join of nonempty graphs, and a non-adjacent
pair on either side upgrades it to `= 2`. Supplying that pair is again a job for an invariant
rather than for vertices: `CGraph.exists_not_adj_of_E_lt` says a graph with fewer than
`V choose 2` edges has one, because otherwise every vertex would have degree `V - 1` and the
handshake lemma would force the edge count to be exactly `V choose 2`. So on the quotient the
criterion is purely numeric — `G.E < G.V.choose 2`, i.e. "`G` is not complete" — and
`diameter_join_left`/`diameter_join_right` hand back the diameters of the stars, books, wheels
and fans. One payoff is the textbook example that no cheaper invariant reaches: `star 3` and
`path 4` are both trees on four vertices with three edges, and only the diameter (`2` against `3`)
separates them.

The third source of two-step graphs is the complement of a *disconnected* graph, and it is the
one that needs no vertex bookkeeping at all: if `u` and `w` are unreachable in `G` then they are
distinct and non-adjacent, hence adjacent in `Ḡ` (`CGraph.compl_adj_of_not_reachable`). So given
any two vertices of `Ḡ`, either they were unreachable in `G` — adjacent already — or they were in
the same component, in which case *any* vertex of another component is `Ḡ`-adjacent to both. That
is `two_step_compl`, and it yields `isConnected_compl_of_not_isConnected` (the complement of a
disconnected graph is connected), `diameter_compl_le_two`, and — feeding
`exists_not_adj_of_E_lt` the complement, whose edge count `E_compl` pins down — `diameter_compl`,
which gives `= 2` as soon as `G` has an edge. The corollary
`isConnected_or_isConnected_compl` records the folklore fact that at least one of `G` and `Ḡ` is
connected, and `isConnected_compl_disjUnion` specialises it to the graphs that are visibly
disconnected.

Degree sequences are sorted lists, which makes them a poor fit for the binary constructions: the
degree sequence of a disjoint union is a *merge* of the two sequences, not a concatenation. The
underlying multiset has no such problem, so `degMultiset` sits alongside `degSequence` in
`IsoGraph/Invariants.lean` — the latter is literally the `sort` of the former
(`coe_degSequence`), so no information is lost. On the multiset the identities are the expected
ones: `degMultiset_disjUnion` is addition, `degMultiset_compl` replaces every degree `d` by its
co-degree `V - 1 - d`, and `degMultiset_join` shifts each side's degrees by the order of the other
side. The last one is proved from the first two — a join *is* a complement of a disjoint union of
complements — with the truncated subtractions resolved by `degree_le`. Feeding the join formula
the degree multisets of the empty and complete graphs gives those of the complete bipartite
graphs, stars (`n ::ₘ replicate n 1`), wheels and books, none of which is a constant sequence and
so none of which was reachable from the strong-regularity machinery.

The path was the last named family whose degrees were still out of reach, since it is not
regular and is not built by a join.  Its adjacency comes from `ofRel`, so a vertex `i` of
`path n` has neighbours `i - 1` and `i + 1` whenever they exist: `mem_nbrs_path` reduces
membership in `nbrs i` to a pair of arithmetic disjuncts, four `Finset.ext` case splits give
`card_nbrs_path`, and `degMultiset_path` assembles the per-vertex degrees into a map over
`Multiset.range n`.  Collapsing that map — the two ends contribute `1`, the `n` interior vertices
contribute `2` — yields the simp lemma `degMultiset (path (n + 2)) = 1 ::ₘ 1 ::ₘ replicate n 2`.
One trap is worth recording: `(path n).V` does not reduce to `Fin n` at *reducible* transparency,
so `simp` lemmas about `Fin` refuse to fire on these goals even though `rw` and `exact` accept
them; the proofs therefore pin the element type down with `@Finset.ext (Fin n)`.

Multisets of this shape are easy enough to sort by hand that the degree *sequences* come out too.
`sort_eq_of_pairwise` turns a guess at the sorted list into a proof (a sorted list is determined
by its multiset), and `sort_replicate_append` packages the case that keeps recurring: many copies
of a small degree followed by a few large hubs.  That gives `degSequence_path`,
`degSequence_star` (`replicate n 1 ++ [n]`), `degSequence_wheel` and `degSequence_book`, and with
them separations that the older invariants could not make, such as `star 3 ≠ path 4` — same order,
same size, both trees.

That leaves the four products, whose vertex set is a product and whose degree multiset is
therefore a `Multiset.bind`: run over the degrees of the left factor and, for each one, map the
degrees of the right factor through whatever the product does to a pair of degrees — `d + e` for
the Cartesian product, `d * e` for the tensor product, `d * H.V + e` for the lexicographic
product and `(d + 1) * (e + 1) - 1` for the strong product.  The per-vertex degrees
(`degree_cartesianProduct` and friends) are the existing `card_nbrs_*` computations with the
regularity hypotheses dropped, and a single helper turns a map over `univ : Finset (α × β)` into
the corresponding bind.  Unlike the older `degSequence_*` product lemmas, these need no
assumption on the factors, so they apply to ladders, prisms and anything else built by a product
from irregular pieces.

The clique numbers of the products complete a table that already had the strong product
(`ω(G ⊠ H) = ω(G)·ω(H)`) and the independence numbers of the disjoint union, the join and the
lexicographic product.  The three new entries are `ω(G □ H) = max ω(G) ω(H)`,
`ω(G × H) = min ω(G) ω(H)` and `ω(G[H]) = ω(G)·ω(H)`.  Each is a statement about a graph on a
product type whose adjacency has a particular shape, so the proofs are stated that way — over an
abstract `P : SimpleGraph (X × Y)` together with the adjacency description — which keeps the
`Finset`/`Set` plumbing at honest types instead of at `(cartesianProduct G H).V`, where the
coercions stop elaborating.  Mathlib's `IsClique.card_le_cliqueNum` and
`exists_isNClique_cliqueNum` do the rest: a clique of `G □ H` lies in one row or one column
because a vertex outside the shared row would have to agree with two distinct vertices in the
other coordinate; a clique of `G × H` projects injectively to both factors, and conversely any
bijection between equal-size cliques pairs them up; and `G[H]` reuses the fibrewise count that
bounds a clique by `ω(G)` fibres of at most `ω(H)` vertices each.  The Cartesian product is the
one case needing nonempty factors — `ω` of the empty graph is `0`, not the maximum — and
`cliqueNum_rook` is the immediate corollary that a rook graph's largest clique is a full row or a
full column.

Distances behave better than clique numbers under the Cartesian product: Mathlib's
`edist_boxProd` already says that a distance in `G □ H` is the sum of the two coordinate
distances, and over a finite nonempty vertex set the extremal distances are attained, so
`ediam_boxProd` adds the extended diameters and `diameter_cartesianProduct` adds the diameters
once both factors are connected (a disconnected graph has diameter `0`, the junk value of
`ediam.toNat`, so the hypothesis cannot be dropped).  What follows is a short list of exact
diameters that no other invariant in the file was able to reach: `Q_n` has diameter `n` by
induction on `hypercube_succ`, the `n`-rung ladder has diameter `n`, the `n`-gonal prism has
diameter `⌊n/2⌋ + 1`, an `m × n` torus has diameter `⌊m/2⌋ + ⌊n/2⌋`, and the rook graph has
diameter `2` for any two side lengths — which subsumes the old square-only proof through the
strongly regular parameters.  `Q₄` and the `4 × 4` rook graph are the payoff: sixteen vertices,
`4`-regular both, and told apart by nothing cheaper than the diameter.

The newest invariant is the chromatic number, `chromNum : IsoGraph → ℕ`, defined as
`G.toSimple.chromaticNumber.toNat` — the `toNat` is harmless because a finite graph is colourable
by its own vertex set, so `chromaticNumber ≠ ⊤`, and `coe_chromNum` moves every statement back to
`ℕ∞` where Mathlib's API lives.  Getting at that API needed one missing bridge: `cycle_toSimple`
identifies `CGraph.cycle n` with Mathlib's `SimpleGraph.cycleGraph n`, translating the `(i+1) % n`
adjacency into the `Fin`-subtraction phrasing of `cycleGraph_adj'`, and it unlocks the cycle-graph
results generally rather than just the colouring ones.  With it, `χ(Kₙ) = n`, `χ(Pₙ₊₂) = 2`,
`χ(C_even) = 2`, `χ(C_odd) = 3` and `χ(G ⊔ H) = max χ(G) χ(H)` all come straight from Mathlib.
The workhorse for everything else is `chromNum_eq_two_iff : χ(G) = 2 ↔ G.IsBipartite ∧ 0 < G.E`,
which turns the file's existing `IsBipartite` and `E` tables into chromatic numbers wholesale —
complete bipartite graphs, stars, hypercubes, ladders, even prisms and grids all follow in one
line each.  In the other direction `three_le_chromNum` says a non-bipartite graph needs three
colours (so `χ(petersen) ≥ 3`, from its odd cycle), and `cliqueNum_le_chromNum` gives the other
standard lower bound `ω ≤ χ`.  For the tensor product only the inequality
`χ(G × H) ≤ min χ(G) χ(H)` holds — both projections are homomorphisms — and equality is Hedetniemi's
conjecture, now known to be false, so the inequality is the honest statement.  As an invariant it
separates `C₃ ⊔ C₃` from `C₆`: both are `2`-regular on six vertices with six edges and neither the
degree sequence nor the edge count can tell them apart.

The chromatic number then gets the same product treatment the other invariants got.  The join adds
(`χ(G + H) = χ(G) + χ(H)`): the upper bound puts the two palettes side by side with `Fin.castAdd`
and `Fin.natAdd`, and the lower bound observes that in a join no colour can appear on both sides,
so the two colour *sets* of any colouring are disjoint and each restricts to a colouring of its
side.  The cartesian product is Sabidussi's theorem, `χ(G □ H) = max χ(G) χ(H)` for nonempty
factors: an edge of `G □ H` moves exactly one coordinate, so colouring `(x, y)` by the *sum*
`c_G(x) + c_H(y)` in `Fin n` — which is a group, hence has cancellation — is proper, and the two
lower bounds come from the row and column copies of the factors.  The lexicographic product only
gets the inequality `χ(G[H]) ≤ χ(G)·χ(H)`, by colouring with the pair of coordinate colours.  A
second general bound, `|V| ≤ χ·α`, comes from the colour classes: each one is an independent set
and together they cover the graph, which is how `cocktailParty (n+1)` is shown to need at least
`n+1` colours before `chromNum_completeMultipartite` confirms it needs exactly that.  The
multipartite formula — one colour per nonempty part — is the join rule run along
`completeMultipartite_cons`, and it settles the cocktail-party graphs and the books; the wheels
follow from `wheel_eq_join`, at `3` colours over an even cycle and `4` over an odd one.

Two colouring results that are not about products close the chapter.  Mycielski's construction
raises the chromatic number by exactly one, `χ(M(G)) = χ(G) + 1`.  The upper bound gives each
shadow `u'` the colour of its original `u` and the apex a fresh colour, which is proper because a
shadow is adjacent only to neighbours of its original.  The lower bound is the interesting half:
given any colouring of `M(G)` with `n` colours, recolour every vertex of `G` whose colour equals
the apex's with the colour of *its* shadow.  That never creates a conflict — an adjacent pair
cannot both have been recoloured, since the apex colour is a single colour — and it lands in the
`n - 1` colours other than the apex's, so `χ(G) ≤ χ(M(G)) - 1`.  Iterating from `C₅` gives the
Grötzsch graph at `4` colours, and the tower above it, with `mycielskian` already known to preserve
triangle-freeness elsewhere in the file.  Second, the greedy bound `χ(K(n, k)) ≤ n - 2k + 2` for
Kneser graphs: colour a `k`-set by its smallest element, capped at `n - 2k + 1`.  Two disjoint sets
below the cap have different minima outright; two at the cap would together need `2k` vertices
among the top `2k - 1` elements.  Specialised to `K(5, 2)` this gives `χ(petersen) ≤ 3`, and with
`three_le_chromNum` from non-bipartiteness, `χ(petersen) = 3` exactly.  Finally the product form of
Nordhaus–Gaddum, `|V| ≤ χ(G)·χ(Gᶜ)`, drops out of `|V| ≤ χ·α` and `α(G) = ω(Gᶜ) ≤ χ(Gᶜ)`.

Two more invariants round out the degree material: `maxDeg` and `minDeg`, the largest and smallest
vertex degree, wrapping Mathlib's `maxDegree` and `minDegree` (both `0` on the empty graph, which
is the convention the rest of the file already uses).  Isomorphism invariance is Mathlib's
`Iso.maxDegree_eq` / `Iso.minDegree_eq`, so the quotient lift is immediate.  The bridge to the
existing tables is `maxDeg_eq_of_degMultiset` and `minDeg_eq_of_degMultiset` — a value that occurs
in the degree multiset and bounds it on the right side *is* the extreme degree — with
`maxDeg_of_degMultiset_replicate` as the regular-graph special case.  That turns every entry of
the `degMultiset` table into two more: `Δ(Kₙ) = δ(Kₙ) = n - 1`, `Δ(Cₙ) = 2`, `Δ(Sₙ) = n` against
`δ(Sₙ) = 1`, `Δ(Wₙ) = n` against `δ(Wₙ) = 3`, and `Δ = δ = 3` for the Petersen graph.  The
constructions get exact formulas rather than bounds: the disjoint union takes the max, the join
adds the other side's vertex count, and the four products behave like their degree formulas
(`Δ(G □ H) = Δ(G) + Δ(H)`, `Δ(G × H) = Δ(G)·Δ(H)`, `Δ(G[H]) = Δ(G)·|H| + Δ(H)`, and
`Δ(G ⊠ H) = (Δ(G)+1)(Δ(H)+1) - 1`), each with the matching `minDeg` version — the proofs pick a
vertex of extreme degree in each factor and pair them up.  Complementation swaps the two,
`Δ(Gᶜ) = |V| - 1 - δ(G)`, and the handshake lemma becomes the squeeze `|V|·δ ≤ 2|E| ≤ |V|·Δ`.

A `girth` invariant closes the loop on the acyclicity material.  Mathlib has `SimpleGraph.girth`
(with `0` for an acyclic graph, the same kind of junk value `diameter` uses for a disconnected one)
but not its isomorphism invariance, so `Iso.egirth_eq` proves that first: an isomorphism carries
cycles to cycles of the same length, so `le_egirth` applied in both directions pins the two infima
together.  On top of it sits a small toolkit for reading a girth off a picture.
`exists_cycle_of_triangle`, `exists_cycle_of_square` and `exists_cycle_of_pentagon` build the closed
walk explicitly and discharge `IsCycle`, which gives both an upper bound on the girth and a witness
that the graph is not acyclic; `exists_triangle_of_girth_eq_three` and `exists_square_of_length_four`
run the case analysis the other way, since a cycle of length three or four *is* a triangle or a
square.  Those two give `four_le_girth` from triangle-freeness and `five_le_girth` from triangle-
and square-freeness.

The leverage comes from tying girth three to the clique number: a triangle is exactly a `3`-clique,
so `girth_eq_three_iff : G.girth = 3 ↔ 3 ≤ ω(G)`, and every entry of the existing `cliqueNum` table
turns into a girth statement — `Kₙ`, `Wₙ`, the book and cocktail-party graphs, rook graphs, joins,
and the lexicographic and strong products of two graphs with an edge each all have girth `3`.  The
contrapositive `four_le_girth_of_cliqueNum` gives the lower bound `4` whenever `ω ≤ 2`.  Girth four
itself comes from the square spanned by one edge in each factor of a Cartesian product, with
bipartiteness of the product ruling out the triangle: `girth (G □ H) = 4`, and with it `Qₙ` for
`n ≥ 2`, the ladders, the even prisms, `C₄`, and `K_{m+2,n+2}`.  For girth five there are two
entries, and they are the ones that matter: `C₅`, where triangle- and square-freeness are a
`decide`, and the Petersen graph, where strong regularity does all the work — `ℓ = 0` forbids
triangles and `μ = 1` forbids squares, since two opposite corners of a square share two neighbours
— with the outer five-cycle realising the bound.

The colouring material gets its two general bounds.  The first is the **greedy bound**
`χ ≤ Δ + 1`.  Mathlib has no greedy colouring, so `colorable_of_forall_degree_le` builds one:
rather than deleting vertices and inducting on the type, it inducts on a `Finset` of
already-coloured vertices, and at each step recolours the new vertex with `Function.update` — its
neighbours use at most `Δ` of the `Δ + 1` colours, so one is free.  Combining it with the existing
`|V| ≤ χ·α` gives `|V| ≤ (Δ + 1)·α`, a lower bound on the independence number of a
bounded-degree graph, and reading it backwards says a `k`-chromatic graph has a vertex of degree
`k - 1`.  The second bound goes the other way round the same corner: colour a *maximum*
independent set with a single colour and give every remaining vertex a private one, and
`χ ≤ |V| - α + 1`.

The same `Function.update` idea, run over a `Finset` in both a graph and its complement at once,
proves the **sum form of Nordhaus–Gaddum**, `χ(G) + χ(Gᶜ) ≤ |V| + 1`.  The induction needs a
chromatic number for a *part* of a graph, so `chromOn S s` is the least number of colours that
properly colours the vertices of `s` (ignoring everything outside), together with two steps:
adding a vertex costs at most one colour, and it costs *nothing* if the vertex has fewer than
`chromOn S s` neighbours inside `s`.  If adding `a` raises the count in both `G` and `Gᶜ`, then
`a` has at least `χ(s)` neighbours in one and at least `χᶜ(s)` in the other, and those two
neighbourhoods partition `s` — so `χ(s) + χᶜ(s) ≤ |s|` and the two increments still fit.  With the
product form `|V| ≤ χ(G)·χ(Gᶜ)` from the previous batch, AM–GM turns each into the other's shape:
`4·|V| ≤ (χ(G) + χ(Gᶜ))²` and `4·χ(G)·χ(Gᶜ) ≤ (|V| + 1)²`.  Both bounds are tight on `Kₙ`, and the
product form is enough to see that the complement of the Petersen graph needs four colours.

**Turán's theorem** bounds edges by the clique number.  Mathlib proves the extremal statement —
every `K_{r+1}`-free graph is dominated by the Turán graph, `isTuranMaximal_iff_nonempty_iso_turanGraph`
— but states the numeric consequence only for the Turán graph itself, and it has no bridge between
`CliqueFree` and `cliqueNum`, so both are supplied here: `cliqueFree_iff_cliqueNum_lt` says
`S.CliqueFree n ↔ ω(S) < n` (one direction shrinks a maximum clique to size `n`, the other is
`IsClique.card_le_cliqueNum`), and chaining a maximal graph's edge count through the isomorphism
gives `2r·|E| ≤ (r - 1)·|V|²` whenever `ω(G) ≤ r`.  At `r = 2` this is **Mantel's theorem**,
`4·|E| ≤ |V|²`, which the `girth_eq_three_iff` bridge routes in from girth (any graph of girth
other than three is triangle-free) and which `cliqueNum_le_two_of_isBipartite` routes in from
bipartiteness.  Read backwards, the same inequality is a triangle *detector*: `|V|² < 4·|E|` forces
`girth = 3`, with no search over triples.  Both bounds are tight — on `K_{m,m}` for Mantel and on
`Kᵣ` for Turán.  Applying the whole thing to `Gᶜ` and folding in `|E(G)| + |E(Gᶜ)| = C(|V|, 2)`
turns the upper bound into a *lower* one: a graph with independence number at most `r` is forced to
have many edges.

**Ramsey's theorem** is not in Mathlib at all, so both halves of `R(3, 3) = 6` are proved here.
The upper bound is the pigeonhole argument: fix a vertex `v` of a graph on six vertices; of the
five others, three are neighbours or three are non-neighbours, and a set of three neighbours
either contains an edge — a triangle through `v` — or is independent.  Stating it as
`3 ≤ ω(G) ∨ 3 ≤ ω(Gᶜ)` makes the two cases literally the same lemma applied to `G` and `Gᶜ`, and
`cliqueNum_compl` turns the result into `3 ≤ ω(G) ∨ 3 ≤ α(G)`.  The lower bound is `C₅`, whose
clique and independence numbers are both two, so five vertices really are not enough.  Downstream,
any triangle-free graph on six or more vertices — in particular any bipartite one — has three
pairwise non-adjacent vertices.

The general bound `R(s, t) ≤ C(s + t, s)` comes from the same picture run recursively.  It is
stated over a `Finset` of vertices rather than the whole type, so the induction can descend into
the neighbourhood and the non-neighbourhood of `v` without changing the ambient graph: Pascal's
rule `C(s + t, s) = C(s - 1 + t, s - 1) + C(s + t - 1, s)` guarantees one of the two sides is big
enough, and whatever the smaller instance returns is either already large enough or is extended by
`v`.  Both `s` and `t` shrink, so the induction is on `s` with a nested induction on `t`.  Since
`C(2s, s) ≤ 4^s`, the diagonal case reads `4^s ≤ |V| → s ≤ ω(G) ∨ s ≤ α(G)`.

The **vertex cover number** `τ` joins the invariant list, lifted from Mathlib's
`vertexCoverNum` (an `ℕ∞`-valued infimum over covering sets, so the `CGraph` version is its
`toNat`; isomorphism invariance is Mathlib's `vertexCoverNum_congr`).  Its whole theory here is
**Gallai's identity** `τ + α = |V|`, which is the observation that a set covers every edge exactly
when its complement is independent — one direction takes the complement of a maximum independent
set as a cover, the other takes the complement of a minimum cover as an independent set, and the
only real work is moving between `Set.encard`, `Finset.card` and `ℕ∞`.  With that, every entry of
the `indepNum` table becomes an entry of a `coverNum` table for free (`τ(Kₙ) = n - 1`,
`τ(Cₙ) = ⌈n/2⌉`, `τ(K_{m,n}) = min m n`, `τ` is additive over disjoint unions), and in the
complement it reads `τ(Gᶜ) + ω(G) = |V|`.  Two bounds tie `τ` to the edge count: `τ ≤ |E|`, one
vertex per edge, and `|E| ≤ τ·Δ`, since the `τ` cover vertices' incidence sets exhaust the edges
and each has at most `Δ` of them.  The second is tight on stars, and combined with Gallai it caps
the independence number of a graph with many edges: `|E| + α·Δ ≤ |V|·Δ`.

The **clique–coclique bound** `α·ω ≤ |V|` for vertex-transitive graphs is where the transitivity
proofs of `IsoGraph/Symmetry.lean` first pay a dividend in the invariant table.  The automorphism
group is taken as the `Finset` of adjacency-preserving permutations of the vertex type, which
keeps everything inside `Fintype` land and needs no `Fintype (G ≃cg G)` instance.  Fix a maximum
clique `C` and a maximum independent set `S` and count the pairs `(σ, c)` with `c ∈ C` and
`σ c ∈ S`.  Each automorphism contributes at most one such `c`, because `σ C` is again a clique
while `S` is independent, so the count is at most `|Aut G|`.  Transitivity makes all the fibres
`{σ | σ c = v}` the same size `m` — carry one onto another by composing with automorphisms
`c' ↦ c` and `v ↦ v'` — so the same count is exactly `|C|·|S|·m`, while summing the fibres over a
fixed `c` gives `|Aut G| = |V|·m`.  The identity lies in a fibre, so `m > 0` and it cancels.  Out
come `2α ≤ |V|` for a vertex-transitive graph with an edge and dually `2ω ≤ |V|` for one that is
not complete, `α(K_m □ K_n) ≤ min m n` (the hard direction of the rook's graph independence
number, since there `ω = max m n` and `|V| = mn`), `α(Qₙ) ≤ 2ⁿ⁻¹`, `α(Petersen) ≤ 5`,
`α(Cₙ) ≤ ⌊n/2⌋` and `α·ω ≤ C(n, k)` for Kneser graphs.  Read backwards it is a certificate of
*non*-transitivity that owes nothing to the degree sequence: the star `K₁,₃` has `α·ω = 6 > 4`.

Self-complementary graphs get their own small theory, since `compl G = G` is a statement one can
actually make on the quotient.  Such a graph has `α = ω` and owns exactly half of the possible
edges, `2|E| = C(|V|, 2)`; expanding `|V| = 4k + r` shows `4 ∣ |V|·(|V| - 1)`, so
**`|V| ≡ 0` or `1 (mod 4)`** — no graph on six vertices is self-complementary.  A
self-complementary graph that is *also* vertex-transitive has `ω² ≤ |V|`, and Paley graphs are
both: they are Cayley graphs of the additive group of the field, so `isVertexTransitive_cayleyAdd`
applies, and `paley 13`, `paley 17` are already known here to be self-complementary.  That gives
`ω(Paley 13) ≤ 3` and `ω(Paley 17) ≤ 4` — the first is sharp — with the same bounds on `α`.

The **domination number** `γ` is new here rather than inherited: Mathlib has no domination API, so
`CGraph.IsDominatingSet s` ("every vertex is in `s` or has a neighbour in `s`") and
`γ = sInf {|s| | s dominates}` are defined from scratch, with a `Finset.map` along an isomorphism
supplying the congruence that lifts `γ` to the quotient.  The whole vertex set dominates, so the
infimum is over a nonempty set and `Nat.sInf_mem` hands back an actual minimum dominating set to
work with.  Around it sit the standard bounds: covering the vertices by the closed neighbourhoods
of a minimum dominating set gives **`|V| ≤ γ·(Δ + 1)`**; a *maximum* independent set is dominating,
since an undominated vertex could be added to it, so **`γ ≤ α`** (and hence
`|V| ≤ α·(Δ + 1)`); deleting the neighbourhood of a vertex of maximum degree leaves a dominating
set, so **`γ + Δ ≤ |V|`**; and a vertex cover dominates as soon as there are no isolated vertices,
so **`γ ≤ τ`** when `δ ≥ 1`.  The table records `γ(Eₙ) = n` and `γ(Kₙ) = γ(K₁,ₙ) = 1`, and the
degree bound turns into lower bounds on the regular graphs — `γ(Petersen) ≥ 3` and `γ(Cₙ) ≥ n/3`,
both of them sharp.

The **radius** completes the metric picture next to `diameter`.  Mathlib supplies `eccent` and
`radius` but no isomorphism-invariance for them, so `SimpleGraph.Iso.eccent_eq` and
`radius_eq` are proved here (transport the `⨆`/`⨅` along the equivalence, using the existing
`edist_eq`) and `r` lifts to the quotient with the usual junk value `0` for an empty or
disconnected graph.  Then `r ≤ d ≤ 2r`, and `r > 0` for a connected graph with an edge.  Two
bridges make the table cheap.  First, **`r = 1 ↔ γ = 1`** whenever `|V| ≥ 2`: both say a single
vertex sees the whole graph, one via `eccent_le_one_iff` and the other via a one-element
dominating set — that settles the star and the wheel (whose hub is a `join` with `K₁`).  Second,
**a vertex-transitive graph has `r = d`**, since an automorphism carrying `u` to `v` carries the
eccentricity along, so `radius_eq_ediam_iff` applies; every transitive entry of the diameter
table therefore reappears as a radius one — `r(Kₙ) = 1`, `r(Cₙ) = ⌊n/2⌋`, `r(Qₙ) = n`,
`r(Petersen) = 2`, and likewise for rook, prism, triangular, cocktail-party, `K_{n,n}` and Paley
graphs.

Counting cliques adds a whole *family* of invariants at once: `cliqueCount n` is the number of
`n`-element cliques, defined as `(G.toSimple.cliqueSet n).ncard` so that no decidability
instance is needed, with `cliqueCount_eq_card_cliqueFinset` as the bridge to Mathlib's
`cliqueFinset` when one is.  The first three values are pinned down — `1`, `|V|` and `|E|`, the
last by exhibiting the `2`-cliques as the image of the edge set under `Sym2.toFinset` — and from
`n = 3` on the count is governed by the clique number: `cliqueCount n = 0 ↔ ω(G) < n`, so
`cliqueCount n > 0 ↔ n ≤ ω(G)`, and `cliqueCount n ≤ C(|V|, n)`.  Composing with the existing
`girth = 3 ↔ 3 ≤ ω` gives a triangle test, **`cliqueCount 3 = 0 ↔ girth ≠ 3`**, and composing
with `ω ≤ χ` gives `χ(G) < n → cliqueCount n = 0`, hence triangle-freeness for every bipartite
graph.  Between them the two bridges fill in the table for free: the complete graph has
`C(m, n)` cliques of each size, the empty graph none above size one, and the cycles, prisms,
stars, complete bipartite graphs, hypercubes and the Petersen graph have no triangles.

Counting *independent* sets then costs almost nothing, because an independent set is a clique of
the complement.  `indepCount n := (G.toSimple.indepSetSet n).ncard` is set up exactly like
`cliqueCount`, and the pair of `@[simp]` duality lemmas `cliqueCount (Gᶜ) n = indepCount G n` and
`indepCount (Gᶜ) n = cliqueCount G n` carries the whole clique-count API across: `indepCount 0 =
1`, `indepCount 1 = |V|`, `indepCount n = 0 ↔ α(G) < n`, `indepCount n ≤ C(|V|, n)`, and the
complementary form of the edge count, **`indepCount 2 + |E| = C(|V|, 2)`** — the independent pairs
are precisely the non-edges.  The table is the mirror of the clique one: the empty graph has
`C(m, n)` independent sets of each size and the complete graph none above size one.

Both counts are additive over a disjoint union, once the size is at least one.  The content is
`isNClique_disjUnion_iff`: a clique with a vertex in it cannot straddle the two sides, since no
edge crosses, so `Finset.subset_map_iff` presents it as the image of a clique of one factor.
Counting the two images — disjoint, because a nonempty set of `Sum.inl`s is never a set of
`Sum.inr`s — gives **`cliqueCount (G ⊔ H) (n+1) = cliqueCount G (n+1) + cliqueCount H (n+1)`**,
and reading it through `compl` gives the same statement for `indepCount` across a join.  Since
`K_{m,n}` *is* a join of two empty graphs, that pins down its independent sets exactly:
`indepCount (K_{m,n}) (k+1) = C(m, k+1) + C(n, k+1)`, and hence `indepCount (star n) (k+2) =
C(n, k+2)`.

The last counting invariant is the number of connected components, `numComponents G :=
Nat.card G.toSimple.ConnectedComponent`; `Iso.connectedComponentEquiv` makes it an invariant for
free.  It is `0` exactly on the empty vertex type and `1` exactly on a connected graph, which is
how `IsConnected` re-enters the numeric world — every `isConnected_*` lemma in the table becomes
a `numComponents _ = 1`.  It is at most `|V|`, with equality for the edgeless graph (`reachable_bot`
makes `connectedComponentMk` a bijection there, so `numComponents (empty n) = n`).  The real work
is **`numComponents (G ⊔ H) = numComponents G + numComponents H`**: mapping a vertex to its
component on whichever side it lives is constant along edges, hence along walks, and that map is
the halves of an equivalence `ConnectedComponent (G ⊔ H) ≃ ConnectedComponent G ⊕
ConnectedComponent H`.  Finally, feeding `isConnected_compl_of_not_preconnected` through the count
states the classical fact that **at most one of `G` and `Gᶜ` is disconnected**: if `G` has two or
more components then `Gᶜ` has exactly one.

The component count is then pinned between the other invariants.  Choosing one vertex out of each
component gives an independent set (two representatives of different components cannot be
adjacent), so **`numComponents G ≤ indepNum G`**; dually, a dominating set has to meet every
component — the map from it to the components is surjective — so **`numComponents G ≤ domNum G`**.
Both directions of `numComponents G = |V| ↔ |E| = 0` are short once the right surjection is
available: with no edges `toSimple = ⊥` and `connectedComponentMk` is a bijection, while a single
edge makes it non-injective and `Fintype.card_lt_of_surjective_not_injective` gives
`numComponents G < |V|`.  (`Fintype.card_eq_nat_card`, which takes its `Fintype` as an explicit
argument, is what keeps the two `Nat.card`/`Fintype.card` spellings from drifting onto different
instances here.)  The join is the last entry: `numComponents (G + H) = 1` for nonempty factors.

The Cartesian product multiplies component counts, **`numComponents (G □ H) = numComponents G *
numComponents H`**.  Mathlib's `reachable_boxProd` says reachability in a box product is
reachability in both coordinates, which is exactly what makes `ConnectedComponent.lift (fun p ↦
(⟦p.1⟧, ⟦p.2⟧))` well defined *and* injective; surjectivity is `Quot.exists_rep` twice, so
`Nat.card_eq_of_bijective` and `Nat.card_prod` finish it without ever writing the inverse map down.
The last connectivity result is a sufficient condition rather than a computation: **a graph with
`|V| ≤ 2δ(G) + 1` is connected**.  Two nonadjacent `u, v` have their neighbourhoods inside `V \
{u, v}`, so `card_union_add_card_inter` forces `N(u) ∩ N(v)` to be nonempty and a common neighbour
joins them — every pair is then at distance at most two.

The last invariant of the file is the order of the automorphism group, `autCount G :=
Nat.card (G.toSimple ≃g G.toSimple)`.  Its iso-invariance is conjugation, `a ↦ f⁻¹ ∘ a ∘ f`, which
is an honest `Equiv` between the two automorphism groups (`SimpleGraph.Iso.autEquiv`).  The group
is finite because `RelIso.toEquiv` is injective, so `autCount` is positive (the identity is always
there) and at most `|V|!`.  Complementation leaves it alone — the same vertex permutation is an
automorphism of `G` and of `Gᶜ`, and spelling out both directions of `compl_adj` gives
`autCount Gᶜ = autCount G` — while every permutation is an automorphism of `empty n` and of
`complete n`, so both have `n!` of them.  `autCount G = 1` is exactly asymmetry, and differing
counts is another way to tell two `IsoGraph`s apart.

Symmetry gives lower bounds on that count, and degrees give an upper one.  Automorphisms preserve
degrees (`SimpleGraph.Iso.degree_eq`), so **a graph whose vertices all have distinct degrees is
asymmetric**: `autCount G = 1`.  In the other direction, fix a base vertex `v₀` in a
vertex-transitive graph and choose, for each `v`, an automorphism `f v` with `f v v₀ = v`; the map
`v ↦ f v` is injective because `v₀` is sent to `v`, giving **`|V| ≤ autCount G`**.  The same
argument one dimension up, with a base *arc* `(u₀, v₀)` and Mathlib's `Dart` type in the role of
the arcs, gives **`2|E| ≤ autCount G`** for arc-transitive graphs, since
`dart_card_eq_twice_card_edges` counts the darts.  Both bounds are stated in the contrapositive as
well (`not_isVertexTransitive_of_autCount_lt`, `not_isArcTransitive_of_autCount_lt`), which is how
one rules symmetry out from a known automorphism count.  Instantiating them at the transitive
families already in the library yields facts like `5 ≤ autCount (cycle 5)`, `10 ≤ autCount
(cycle 5)` from arc-transitivity, `24 ≤ autCount (hypercube 3)` and `30 ≤ autCount (kneser 5 2)` —
each just the transitivity lemma plus `simp` evaluating `V` or `E`.

The degree-sum formula has a parity shadow, the **handshaking lemma**: a graph has evenly many
vertices of odd degree.  Mathlib proves it for `SimpleGraph`, and the work here is transporting it
onto the two `IsoGraph`-visible spellings of the degrees — `Multiset.countP_map` moves the count
from a `Finset.filter` over vertices to `degMultiset`, and `Multiset.coe_countP` together with
`Multiset.sort_eq` moves it on to the sorted `degSequence`, which is the form that survives the
quotient.  The corollaries are the usual ones: if every degree is odd then `|V|` is even, so
**an odd-regular graph has an even number of vertices** (no cubic graph on seven vertices), and
contrapositively an odd number of vertices forces some degree to be even.

The constructions all inherit symmetry from their factors, which turns into lower bounds on
`autCount`.  An automorphism of each side acts on a disjoint union through `Equiv.sumCongr`, and on
any of the four products coordinatewise through `Equiv.prodCongr` — the adjacency obligations are
the same one-line `simp only`s that `isVertexTransitive_cartesianProduct` and friends already use.
Different pairs give different automorphisms (read the factors back off by evaluating at
`Sum.inl x` / `Sum.inr y`, or at `(x, y₀)` / `(x₀, y)`, which is where the products need both
factors to be nonempty), so `autCount G * autCount H ≤ autCount (G □ H)` and likewise for the
tensor, strong and lexicographic products, for `disjUnion`, and — by complementing twice — for
`join`.  Two copies of the *same* graph can additionally be exchanged, and since `Sum.isRight`
detects whether the exchange happened while `Sum.elim id id` forgets it, the bound for
`disjUnion G G` doubles to `2 · autCount G ²`.

Counting vertices against edges gives `|V| ≤ |E| + c(G)`, the spanning-forest bound.  The proof
picks a root in every component (a section of `connectedComponentMk`, which is surjective) and
sends every non-root vertex `v` to the edge joining it to a neighbour strictly closer to its root —
such a neighbour exists because the second vertex of a shortest walk from `v` to the root is one
(`Walk.adj_snd` plus `length_tail_add_one`).  That map is injective: if `v` and `w` chose the same
edge then they are adjacent, hence share a root, and each would be strictly closer to it than the
other.  The roots themselves are the image of the section, so they number `c(G)`, and the two
counts add up to `|V|`.  Specialising to `c(G) = 1` recovers "a connected graph has at least
`|V| - 1` edges", and contrapositively `|E| + 1 < |V|` forces disconnection.

The Mycielskian gets its clique number too.  A clique of `M(G)` either contains the apex — and
then everything else in it is a copy vertex, which are pairwise non-adjacent, so the clique is an
edge — or it misses the apex, and forgetting whether each vertex is an original or a copy sends it
injectively onto a clique of `G` of the same size (a vertex and its own copy are never adjacent).
So `ω(M(G)) = max (ω G) 2`, and since `χ(M(G)) = χ(G) + 1` is already available, iterating `M` from
`K₁` proves **Mycielski's theorem**: there are triangle-free graphs of arbitrarily large chromatic
number, stated both as `ω ≤ 2` and as `cliqueCount 3 = 0`.

The two remaining products get their edge counts, completing the table alongside
`E_cartesianProduct` and `E_tensorProduct`.  Both come from handshaking on the degree formulas that
were already proved.  For the strong product the degree is `(d_G + 1)(d_H + 1) - 1`, so it is the
shifted degrees that multiply: summing `deg p + 1` over `G.V × H.V` factors as
`(2|E_G| + |V_G|)(2|E_H| + |V_H|)`, and cancelling the `|V_G||V_H|` copies of the shift leaves
`|E| = |V_G||E_H| + |V_H||E_G| + 2|E_G||E_H|` — exactly the cartesian count plus the tensor count,
which is what the decomposition `G ⊠ H = (G □ H) ∪ (G × H)` predicts.  The lexicographic product is
`|E| = |V_H|²|E_G| + |V_G||E_H|`: each edge of `G` becomes a complete bipartite graph between two
fibres, and each fibre carries its own copy of `H`.  As a check, `paley 9 = K₃[E₃] = K_{3,3,3}` gets
`27` edges.

Domination behaves cleanly on the same three constructions.  It is additive over a disjoint union:
splitting a dominating set of `G ⊔ H` with `Finset.toLeft`/`toRight` dominates each side separately
(no edge crosses, so a dominator of an `inl` vertex is an `inl` vertex), and conversely two
dominating sets sit side by side as a `Finset.disjSum`.  A join, on the other hand, is dominated by
one vertex from each side, so `γ ≤ 2`; and a single vertex dominates `G ∨ H` exactly when it is
universal in its own factor, since the opposite side comes for free — so `γ(G ∨ H) = 1` iff
`γ(G) = 1` or `γ(H) = 1`, and `2` otherwise.  That immediately gives `γ(K_{m,n}) = 2` for
`m, n ≥ 2`.  For the cartesian product, a dominating set of `G` repeated in every fibre dominates
`G □ H`, giving `γ(G □ H) ≤ γ(G)·|V_H|` (the corresponding lower bound is Vizing's conjecture, so
it is not here).

The radius of a cartesian product is the sum of the radii, the companion of the diameter result
above.  Mathlib's `edist_boxProd` already says distances add coordinatewise, so eccentricities add
too — a farthest vertex from `(a, b)` can be chosen farthest in each coordinate separately — and
then a centre of the product is a pair of centres.  Both directions are one application of
`exists_eccent_eq_radius`.  The other two products only get an upper bound: they contain the
cartesian product as a subgraph, and adding edges cannot increase the diameter, so
`diam(G ⊠ H)` and `diam(G[H])` are both at most `diam(G) + diam(H)`.

Domination in the other two products completes the picture.  All three products share one feature —
an edge forces the first coordinates to be equal or adjacent — so projecting a dominating set along
`Prod.fst` always dominates the first factor, giving `γ(G) ≤ γ(G □ H)`, `γ(G) ≤ γ(G ⊠ H)` and
`γ(G) ≤ γ(G[H])` as soon as `H` has a vertex.  Upwards, a *product* of dominating sets dominates the
strong product (each coordinate is separately dominated, and the two vertices differ somewhere), so
`γ(G ⊠ H) ≤ γ(G)·γ(H)`; combined with the projection bound this brackets it between `max` and
product, and two universal vertices give a universal vertex, so `γ = 1` when both factors have
`γ = 1`.  For the lexicographic product the two bounds meet: if `H` has a universal vertex, then
lifting a dominating set of `G` into that vertex's fibre dominates `G[H]`, so blowing up by a
dominated graph leaves `γ` unchanged — `γ(G[H]) = γ(G)`.

Independence numbers of the products are next, and here the exact value is only available for
the lexicographic product (`α(G[H]) = α(G)·α(H)`, already proved).  The other three get sharp-in-
general bounds instead.  Since `α` is antitone in the edge set, the new subgraph inclusion
`G ⊠ H ≤ G[H]` immediately gives `α(G)·α(H) ≤ α(G ⊠ H)` — the inequality behind the Shannon
capacity of a graph, which is exactly the quantity measuring how far it can be from an equality —
and chaining it with `G □ H ≤ G ⊠ H` gives the same lower bound for the cartesian product.  The
tensor product is different: no tensor edge stays inside a slab `S × V(H)`, so an independent set
of `G` widens to a full slab and `α(G)·|V(H)| ≤ α(G × H)`, with the mirrored bound by symmetry.
In the other direction, fibrewise counting bounds the cartesian product from above: an independent
set meets each fibre `{a} × V(H)` in an independent set of `H`, so `α(G □ H) ≤ |V(G)|·α(H)`, and
since the strong product contains the cartesian one the same bound holds there.

Chromatic numbers of the products complete the same table.  `χ(G □ H) = max χ(G) χ(H)` and
`χ(G[H]) ≤ χ(G)·χ(H)` were already available, and the new inclusion `G ⊠ H ≤ G[H]` transports the
second one to the strong product, since a colouring restricts to any subgraph: `χ(G ⊠ H) ≤
χ(G)·χ(H)`.  Below, the cartesian product sits inside both, so `max χ(G) χ(H)` is a lower bound for
each as soon as both factors have a vertex, and the clique bound `ω ≤ χ` combines with
`ω(G ⊠ H) = ω(G)·ω(H)` to give the sharper `ω(G)·ω(H) ≤ χ(G ⊠ H)`.  Products of complete graphs
show the upper bound is attained.  The tensor product is the interesting one: `χ(G × H) ≤
min χ(G) χ(H)` holds because either projection is a graph homomorphism, and the matching lower
bound is exactly Hedetniemi's conjecture, which is false — so all that is proved here is the
bipartite case, where one bipartite factor plus an edge on each side forces `χ(G × H) = 2`.

Gallai's identity `τ + α = |V|` then hands over the whole independence table to vertex covers.
The lexicographic product gets an exact value, `τ(G[H]) = |V(G)|·|V(H)| - α(G)·α(H)`; the cartesian
and strong products inherit the two-sided bounds, `|V(G)|·τ(H)` and `τ(G)·|V(H)|` from below and
`|V(G)|·|V(H)| - α(G)·α(H)` from above; and the tensor product is covered by a slab, giving
`τ(G × H) ≤ min (τ(G)·|V(H)|) (|V(G)|·τ(H))`.  The join also lands here: a cover has to contain one
whole side, so `τ(G + H) = min (τ(G) + |V(H)|) (|V(G)| + τ(H))`.  On `K₃ □ K₃` the lower bound is
tight — six squares are needed to cover the rook's graph, and the bound gives exactly six.

Complementation ties the domination number down from both sides, in the style of
Nordhaus and Gaddum. Since `γ + Δ ≤ n` holds for every graph and complementation
sends the maximum degree to `n - 1 - δ`, adding the two bounds gives
`domNum_add_domNum_compl_le_V_add_one : γ(G) + γ(Gᶜ) ≤ |V| + 1`, attained by the
edgeless graph. In the other direction a graph and its complement cannot both have a
universal vertex once there are two vertices, so `three_le_domNum_add_domNum_compl`
gives `3 ≤ γ(G) + γ(Gᶜ)`. Disconnectedness collapses the complement even further:
two vertices in different components dominate `Gᶜ` between them
(`domNum_compl_le_two_of_not_isConnected`), so for instance the complement of any
disjoint union of two nonempty graphs has domination number at most two.

The clique and independence numbers obey the same shape of bound. Since every
clique needs its own colour, `omega <= chi`, and the existing
`chromNum_add_indepNum_le_card_add_one` immediately gives
`cliqueNum_add_indepNum_le_V_add_one : omega(G) + alpha(G) <= |V| + 1`; rewriting
along `indepNum_compl` and `cliqueNum_compl` restates it as
`alpha(G) + alpha(Gᶜ) <= |V| + 1` and `omega(G) + omega(Gᶜ) <= |V| + 1`. Both the
complete and the edgeless graph attain equality. In the other direction any two
distinct vertices are either adjacent, giving a two-clique, or non-adjacent,
giving a two-element independent set, so `three_le_cliqueNum_add_indepNum` holds
on two or more vertices.

Gallai's identity turns each of those into a statement about vertex covers.
`chromNum_le_coverNum_add_one` says chi(G) <= tau(G) + 1 — colour each vertex of a
minimum cover individually and share one colour among the independent rest — and
omega inherits the same bound. Adding tau(G) + alpha(G) = |V| to
tau(G^c) + omega(G) = |V| gives the exact bookkeeping
tau(G) + tau(G^c) + alpha(G) + omega(G) = 2|V|, which converts the clique-side
Nordhaus-Gaddum pair into |V| - 1 <= tau(G) + tau(G^c) <= 2|V| - 3 (the upper bound
on two or more vertices). The complete graph attains the lower bound. Finally, with
no isolated vertices every vertex cover dominates, so gamma + alpha <= |V|.

Regularity is the newest invariant, and it comes almost for free. `IsRegularWith k`
says every vertex has degree `k`; it is the first clause of `IsSRGWith`, and it is
isomorphism-invariant for the same reason strong regularity is, so it descends to the
quotient with an `isRegularWith_mk` simp lemma. The bridge that makes it cheap is
`isRegularWith_of_degSequence`: a graph whose degree sequence is `List.replicate n k`
is `k`-regular, and the converse `IsRegularWith.degSequence` recovers the sequence.
Every entry of the existing degree-sequence table therefore becomes an entry of a
regularity table for free — the empty graph is `0`-regular, `K_n` is `(n-1)`-regular,
cycles are `2`-regular, the Petersen graph is `3`-regular, `Q_n` is `n`-regular, prisms
are `3`-regular, the cocktail party graph is `(2n-2)`-regular, `K_{n,n}` is `n`-regular,
the rook graph is `((n-1)+(m-1))`-regular and the Kneser graph `K(n,k)` is
`(n-k) choose k`-regular. The same bridge handles the four products, since their
degree-sequence lemmas already take constant sequences as input: the Cartesian product
of a `k`-regular and an `l`-regular graph is `(k+l)`-regular, the tensor product is
`k*l`-regular, the strong product is `((k+1)(l+1)-1)`-regular and the lexicographic
product is `(k|V(H)| + l)`-regular. Complements are `(|V| - 1 - k)`-regular, disjoint
unions of equally regular graphs stay regular, and a join is regular when the two
degrees plus the two cardinalities line up. Strongly regular graphs are regular by
definition, vertex-transitive graphs are regular because the automorphism group moves
any vertex to any other, and the handshake lemma specialises to `2|E| = |V| * k`,
which is how `petersen.E = 15` and `(hypercube 3).E = 12` fall out in one line.

Line graphs get a degree theory of their own. The formula
`deg_{L(G)}(e) = sum over the endpoints v of e of (deg_G(v) - 1)` had been buried
as a `have` inside the proof of `E_lineGraph`; it is now the standalone
`CGraph.degree_lineGraph`, and specialising it to an edge `s(u, v)` gives
`degree_lineGraph_mk : deg_{L(G)}(uv) = deg u + deg v - 2` (the subtraction is
safe because an edge gives each endpoint degree at least one). A small eliminator
`lineGraph_vertex_cases` lets the rest of the section reason one edge at a time.
Three consequences follow: the line graph of a `k`-regular graph is
`(2k - 2)`-regular, `Delta(L(G)) <= 2 Delta(G) - 2`, and
`2 delta(G) - 2 <= delta(L(G))` once `G` has an edge. Regularity in turn pins the
size of the line graph — `|E(L(G))| = |V| * C(k, 2)`, dropping the strong
regularity hypothesis of the earlier `IsSRGWith.E_lineGraph`, and
`2|E(L(G))| = |E| * (2k - 2)` — and since `T(n)` is the line graph of `K_n` it
comes out `(2n - 4)`-regular with no lower bound on `n` at all.

Once a graph is known to be `k`-regular, every bound phrased in terms of the maximum
degree can be restated with `k` in its place, and `IsRegularWith.maxDeg_eq` is the
one-line bridge that does it: `chi <= k + 1`, `n <= gamma * (k + 1)`,
`n <= alpha * (k + 1)`, `gamma + k <= n`, `|E| <= tau * k` and
`|E| + alpha * k <= n * k`. Regularity also constrains the graph itself. Since
`2|E| = n * k`, a regular graph of odd degree has an even number of vertices, so there
is no `3`-regular graph on five vertices; `k < n` whenever the graph is nonempty; the
degree of a regular graph is unique; the complement's edge count is forced to
`2|E(G^c)| = n(n - 1 - k)`; and a `0`-regular graph is the empty graph on its own
vertex set.

The `maxDeg` and `minDeg` tables were complete for the graphs whose degrees vary —
stars, wheels, paths — but empty for most of the regular families, where the answer
is the least interesting and the proof the most tedious. Regularity supplies both at
once: `IsRegularWith.maxDeg_eq` and `minDeg_eq` turn each entry of the regularity
table into a pair of `simp` lemmas, so `Delta = delta` is now recorded for triangular,
rook, prism, cocktail party, balanced complete bipartite, Kneser and Paley graphs.
Only the nonemptiness of the vertex set is needed, which is why those statements are
phrased with a shift (`triangular (n + 2)`, `rook (m + 1) (n + 1)`, and so on).
Paley graphs pick up an `isRegularWith_paley` on the way, read off from their strong
regularity.

The chromatic index arrives for free. An edge colouring of `G` is exactly a vertex
colouring of `L(G)`, so `edgeChromNum G` is *defined* as `chromNum (lineGraph G)` —
no new quotient obligation, because both halves already live on `IsoGraph`. The lower
bound `Delta <= chi'` is the one piece with real content: the edges at a fixed vertex
are pairwise adjacent in the line graph, so `CGraph.degree_le_cliqueNum_lineGraph`
exhibits a clique of size `deg v` there, and `omega(L(G)) <= chi(L(G))` finishes it.
The upper bound is the greedy bound applied to the line graph, which the degree
formula of the previous section turns into `chi' <= 2 Delta - 1`; Vizing's `Delta + 1`
is out of reach for now. The named cases follow from the existing line-graph table:
`chi'(K_{1,n}) = n` because `L(K_{1,n}) = K_n`, `chi'` of an edgeless graph is zero,
and `chi'` of a disjoint union is the max of the two. For the Petersen graph this
gives `3 <= chi' <= 5`; the true value `4` needs its lack of a proper 3-edge-colouring,
which is a genuinely harder fact.

The *matching number* `ν(G)` is defined the same way as the chromatic index: a matching is a
set of pairwise disjoint edges, which is exactly an independent set in the line graph, so
`matchNum G = indepNum (lineGraph G)` and again no new quotient obligation arises. Gallai's
identity in `L(G)` gives `coverNum (lineGraph G) + ν = |E|` for free, and
`V_le_chromNum_mul_indepNum` applied to `L(G)` gives `|E| ≤ χ' ν`, since every colour class of
an edge colouring is a matching. The one bound with real content is `2ν ≤ n`: a maximum
matching is an independent set `S` in `L(G)`, its edges are pairwise vertex-disjoint, and
`Finset.card_biUnion` over the `S`-indexed family of two-element endpoint sets embeds `2|S|`
vertices into `V`.

Both new invariants come with a table for the named families, and the table is cheap for the
same reason: whenever `lineGraph` of a family is itself a named graph the answer is an already
known independence or chromatic number. `lineGraph_cycle` gives `ν(C_n) = ⌊n/2⌋` and
`χ'(C_n) = 2` or `3` according to the parity, `lineGraph_path` gives `χ'(P_n) = 2`,
`lineGraph_complete_four` identifies `L(K₄)` as the octahedron and so gives `ν(K₄) = 2` and
`χ'(K₄) = 3`, and `lineGraph_bipartite` turns the rook's-graph independence bound into
`ν(K_{m,n}) ≤ min m n`.

The matching number also interacts with the covering invariants. An independent set meets each
edge of a matching at most once, so each of the `ν` disjoint edges donates a vertex outside a
maximum independent set and `ν + α ≤ n`; the proof is the same `Finset.card_biUnion` counting
as for `2ν ≤ n`, run over the sets `e \ I` instead of over `e`. Combined with Gallai's
`τ + α = n` this yields the weak duality half of König's theorem, `ν ≤ τ`, without ever
building the injection from a matching into a cover.

Strong regularity settles the girth of the remaining named families in one stroke: if `k > 0`
there is an edge, and `ℓ > 0` says its endpoints already share a neighbour, so
`IsSRGWith.girth_eq_three` closes a triangle. That covers the triangular and Johnson graphs,
the Kneser graphs from `K(6,2)` on — `K(5,2)` is Petersen, whose girth is five and whose `ℓ`
is `0` — and the Paley graphs on at least nine vertices. Line graphs go the other way: the
edges at a vertex of degree `d` form a `d`-clique, so `Δ ≥ 3` already forces `girth (L G) = 3`.

The *clique cover number* `θ(G)` is the third invariant defined by composition rather than by a
new construction: a partition of the vertices into cliques is a proper colouring of the
complement, so `cliqueCoverNum G = chromNum (compl G)`. Every fact about it is a fact about
`chromNum` read through `compl_compl`, `compl_disjUnion` and `compl_join`, which is why the
disjoint union adds and the join takes a maximum — exactly the reverse of the chromatic number.
The two bounds worth naming are `α ≤ θ`, the mirror of `ω ≤ χ`, and `n ≤ θ ω`, the mirror of
`n ≤ χ α`.

Reading the complement bounds through `θ` turns them into Nordhaus–Gaddum statements about a
single graph: `n ≤ χ θ`, `χ + θ ≤ n + 1` and `4n ≤ (χ + θ)²` are all restatements of theorems
already proved about `G` and `Ḡ`. The clique cover number of a complete multipartite graph is
the size of its largest part, since `compl_completeMultipartite_cons` unfolds the complement
into a disjoint union of cliques and the chromatic number of a disjoint union is a maximum.

Two chains of inequalities run through the invariant library: `ω ≤ χ` on the graph and
`α ≤ θ` on its complement. Several named families meet these bounds. The rook's graph is a
Cartesian product of two cliques, so `chromNum_rook` reads off `max m n` from
`chromNum_cartesianProduct`, matching `cliqueNum_rook` exactly; a bipartite graph with at least
one edge has `χ = ω = 2`, which specialises to every hypercube of positive dimension; and for
complete multipartite graphs both `χ = ω` (counting the nonempty parts) and the dual
`α = θ` (the parts themselves are simultaneously the largest independent set and an optimal
clique cover) hold. Odd cycles show none of this is automatic: `C₅` has `ω = 2` but `χ = 3`.

A graph is acyclic exactly when its girth is zero, so the girth table doubles as a table of
which named families contain a cycle: the Petersen graph, the hypercubes and complete bipartite
graphs of positive girth, the triangular, Johnson and Kneser graphs, the rook's graphs and the
Paley graphs are all shown non-acyclic — and hence not trees — by a single rewrite each. In the
other direction an acyclic graph has no triangle, so its clique number is at most two and it has
no three-vertex clique at all; combined with the edge count `E + 1 = V` this pins the clique
number of any tree on at least two vertices at exactly two.

Because the line graph of `K_{m,n}` is the rook's graph and the line graph of a star is complete,
the chromatic index of both families falls out of the chromatic-number table: `χ'(K_{m,n}) =
max m n` is König's edge-colouring theorem for complete bipartite graphs, obtained here from
`χ(K_m □ K_n) = max m n`. The same dictionary runs the other way for the triangular graphs, which
are the line graphs of complete graphs: the star of edges at a vertex of `Kₙ` gives `n - 1` as a
lower bound for both the clique number and the chromatic number of `J(n, 2)`, the greedy
line-graph colouring caps `χ(J(n, 2))` at `2(n - 1) - 1`, and an independent set of `J(n, 2)` is
a matching of `Kₙ` and so has at most `n / 2` members.

The Kneser graphs on pairs get the same treatment from two directions. Strong regularity with
`μ = C(n - 3, 2) > 0` gives `K(n, 2)` diameter two, hence connectedness, one component and —
since it is vertex-transitive — radius two, for every `n ≥ 5`. Complementation with the
triangular graph then transports the line-graph bounds: a clique of `K(n, 2)` is a matching of
`Kₙ`, so `2ω ≤ n`, and the `n - 1` pairs through a fixed point are pairwise intersecting, giving
the easy half of Erdős–Ko–Rado as `n - 1 ≤ α(K(n, 2))` and hence the same bound on its clique
cover number. For `n ≥ 6` the graph contains a triangle, so it is not bipartite and needs at
least three colours.

The chromatic index feeds straight back into matchings. An edge colouring partitions `E` into
`χ'` matchings, so `|E| ≤ χ'·ν`; for `K_{m,n}` that reads `m·n ≤ max m n · ν`, and since
`min m n · max m n = m·n` it forces `ν ≥ min m n`. With the clique–coclique upper bound this
gives `ν(K_{m,n}) = min m n` exactly, hence König's theorem `ν = τ` for the complete bipartite
graphs, a perfect matching in `K_{n,n}`, and — reading the same number in the line graph —
`α(K_m □ K_n) = min m n`, upgrading the earlier inequality to an equality and showing the rook's
graphs attain the clique–coclique bound `α·ω = |V|` exactly.

The matching number also controls the vertex cover number from above. If `M` is a maximum
matching — a maximum independent set of the line graph — then no edge joins two vertices missed
by `M`, since such an edge could be added to `M`; so the missed vertices are an independent set
and `|V| ≤ α + 2ν`. Gallai's identity `α + τ = |V|` turns this into `τ ≤ 2ν`, the guarantee
behind the greedy two-approximation for minimum vertex cover, and combining it with the earlier
`ν ≤ τ` sandwiches the cover number between `ν` and `2ν` for every graph.

A graph is *self-complementary* when it equals its own complement — an ordinary equation
`compl G = G` here, since `IsoGraph` is already the quotient by isomorphism, so no extra
machinery is needed to state it. The Paley graphs on 13 and 17 vertices, `C5`, `P4` and the
one-vertex graph are the examples in the library. Halving `|E| + |Eᶜ| = C(V, 2)` gives
`2|E| = C(V, 2)`, which pins down `|E(Paley 13)| = 39` and `|E(Paley 17)| = 68` and, since
`C(V, 2)` must then be even, forces `V ≡ 0` or `1 (mod 4)` — enough on its own to rule out the
Petersen graph and `C6`. Self-complementarity also collapses each complementary pair of
invariants onto itself: `ω = α` and `χ = θ`. Feeding that into the Nordhaus–Gaddum bounds
`V ≤ χ(G)·χ(Gᶜ) ≤ ((V + 1)/2)^2` yields `√V ≤ χ ≤ (V + 1)/2`, so such a graph on five or more
vertices is never bipartite, and combined with the independence numbers already computed by
`native_decide` it gives `5 ≤ χ(Paley 13) ≤ 7` and `5 ≤ χ(Paley 17) ≤ 9`. Finally, a
disconnected graph has a complement of diameter two, so a self-complementary graph on at least
two vertices is connected.

Regularity passes to line graphs in a controlled way. If `G` is `k`-regular on `n` vertices —
recorded in the library as `degSequence G = List.replicate n k` — then every vertex of `G`
contributes `C(k, 2)` pairs of incident edges, so `|E(L(G))| = n · C(k, 2)`, and each edge `uv`
of `G` meets `(k - 1) + (k - 1)` others, making `L(G)` itself `(2k - 2)`-regular with
`maxDeg = minDeg = 2k - 2`. Both statements are proved once from the `replicate` hypothesis and
then instantiated across the regular families: the Petersen graph (`|E| = 15`, line graph
`4`-regular on 15 vertices), the prisms, the hypercubes (`|E(L(Qₙ))| = 2ⁿ · C(n, 2)`), the
cocktail-party graphs, `K_{n,n}`, the triangular and Kneser graphs, and the Paley graphs. Along
the way the same `replicate` degree sequences give the edge counts themselves — `|E(Petersen)|
= 15`, `|E(cocktailParty n)| = n(2n - 2)`, `2|E(Paley q)| = q(q - 1)/2` — none of which needed a
`decide`.

The independence number of a path had been missing, and it turns out to follow from two bounds
that already sandwich it. Gallai's `τ + α = |V|` together with `ν ≤ τ` gives `α + ν ≤ |V|`, while
`|V| ≤ χ · α` bounds `α` from below; since `L(P_{n+1}) = Pₙ`, the matching number of a path is the
independence number of the path one shorter, so a single induction closes the gap and yields
`α(Pₙ) = ⌈n/2⌉`, hence `τ(Pₙ) = ν(Pₙ) = ⌊n/2⌋` — König's theorem for paths, obtained without any
bipartite matching machinery — and `ω(Pₙ) = 2`. The fan `Fₙ = K₁ ∨ Pₙ` then inherits a complete
table from the join formulas: `|E| = 2n - 1`, `χ = ω = 3`, `girth = 3`, `α = ⌈n/2⌉` (the apex is
never worth taking), `τ = ⌈(n+1)/2⌉`, `Δ = n`, `δ = 2`, and `γ = r = 1` because the apex dominates
everything.

Triangle-freeness of a long cycle comes for free from vertex-transitivity. For a
vertex-transitive graph `α · ω ≤ n`, and `α(Cₙ) = ⌊n/2⌋` is already more than a third of `n` once
`n ≥ 4`, so `ω(Cₙ) = 2` and the girth is at least four — no inspection of walks required. The
wheel then has `ω(Wₙ) = 3` (hub plus a rim edge) for `n ≥ 4`, and `W₃ = K₄`. The book
`Bₙ = K₂ ∨ Eₙ` gets the rest of its table from the join formulas — `|E| = 2n + 1`, `Δ = n + 1`,
`δ = 2`, `τ = min(n + 1, 2)`, `θ = max(1, n)`, and `γ = r = 1` since either spine vertex
dominates — and Gallai supplies the cover numbers of the wheel and the cocktail-party graph,
whose domination number is `2` because its radius is `2`.

The vertices a maximum matching misses are pairwise non-adjacent, so `|V| ≤ α + 2ν`; for `Kₙ`
that reads `n ≤ 1 + 2ν`, and against `2ν ≤ n` it pins `ν(Kₙ) = ⌊n/2⌋`. Two families fall out.
Because `L(Kₙ)` is the triangular graph, `α(T(n)) = ν(Kₙ) = ⌊n/2⌋`, and complementing gives
`ω(K(n, 2)) = ⌊n/2⌋` for the Kneser graph; feeding that `α` back into `α · ω ≤ |V| = C(n, 2)`
caps a clique of `T(2m+2)` at `2m + 1`, which is exactly the size of the star of edges at a
vertex, so `ω(T(2m+2)) = n - 1` and dually `α(K(2m+2, 2)) = n - 1`. The companion bound
`|E| ≤ χ' · ν` shows that complete graphs of odd order are class two: `K_{2m+3}` has
`(m+1)(2m+3)` edges but no matching larger than `m + 1`, so `χ' ≥ 2m + 3 = Δ + 1` — Vizing's
theorem in the one case where the easy `Δ` colours provably do not suffice. Finally the hypercube
gets an exact independence number, `|V| ≤ χ · α` with `χ = 2` against `2α ≤ |V|` giving
`α(Qₙ) = τ(Qₙ) = 2ⁿ⁻¹`.

The clique number is the easiest of these to pin down, because `ω ≤ χ` and a single edge
already forces `ω ≥ 2`.  That settles `ω(Qₙ) = 2`, `ω` of the ladder, and `ω` of every prism
except the triangular one — `Y₃` contains the two triangles of `C₃`, so `ω(Y₃) = 3` — and for
the Petersen graph the vertex-transitive bound `α · ω ≤ |V|` together with `χ = 3` (hence
`α ≥ 4`) gives `ω = 2`, so the girth is at least four.  The independence numbers of the ladder
and the even prism come from squeezing `α(G □ K₂) ≤ |V(G)|` against `|V| ≤ χ · α` with `χ = 2`:
both are half the order, and Gallai converts each into a vertex cover number.  The odd prism
only gets the upper bound `α ≤ n`, since it is not bipartite.  Connectivity of the strongly
regular families is recorded as `c(G) = 1` for the triangular, cocktail-party, Paley and
Petersen graphs.  The domination number of a cycle is `⌈n/3⌉`: every third vertex dominates,
matching the general `3γ ≥ n` bound for graphs of maximum degree two.

The balanced complete multipartite graph `K_{m×d}` — `completeMultipartite (List.replicate m d)`,
the cocktail party graph when `d = 2` and `Kₘ` when `d = 1` — is the lexicographic product
`Kₘ[Eᵈ]`, and that one identity carries the whole product API across: `|V| = md`,
`|E| = C(m, 2)d²`, the degree sequence is constant at `(m - 1)d`, and the clique number is `m`,
so three or more parts force girth three.  Peeling one part off exhibits it as a join, which
supplies connectivity, `diam = rad = 2` and `γ = 2` whenever there are at least two parts of at
least two vertices each — one vertex dominates everything outside its own part but nothing
inside it.

Four statements in this area were closed by the automated prover rather than by hand.  A maximum
matching plus the vertices it misses is a clique cover, so `θ ≤ |V| - ν`; the hypercube and the
cocktail party graph both have perfect matchings, `ν(Qₙ) = 2ⁿ⁻¹` and `ν(K_{n×2}) = n`; and the
radius of a path is `⌊n/2⌋`, the midpoint being the centre.

Once a graph has a known maximum matching, `θ ≤ |V| - ν` is often exact.  Against `α ≤ θ` it
gives `θ(Qₙ) = 2ⁿ⁻¹` and `θ` of the ladder; against `|V| ≤ θ · ω` it gives `θ(Cₙ) = θ(Wₙ) = ⌈n/2⌉`
for triangle-free cycles and their wheels, `θ(Pₙ) = ⌈n/2⌉`, and `θ` of the prism.  The prover
supplied the matchings themselves — perfect ones for the ladder, the prism and the Petersen
graph — and while it was there it also settled `α(Petersen) = 4`, `γ(Petersen) = 3` and
`θ(Petersen) = 5`, so Gallai gives `τ(Petersen) = 6`.  Not everything sent to it was true: the
guess `θ(C_{2m+3}) = m + 2` came back refuted, the counterexample being `C₃ = K₃`, which one
clique covers.  Elsewhere the Cartesian product formulas give the ladder its degrees and, now
that the radius of a path is known, its radius `⌈n/2⌉ + 1`.

The automated prover contributed three substantial counting arguments this round.  The
domination number of a path, `γ(Pₙ) = ⌈n/3⌉`, comes with an explicit dominating set on every
residue class mod 3 together with a matching lower bound built by injecting the vertices at
positions `0, 3, 6, …` into any dominating set.  The independence number of an odd prism,
`α(Y_{2m+3}) = 2m + 2`, alternates layers around the odd cycle and rules out `2m + 3` by
showing that a transversal of that size would 2-colour an odd cycle.  Finally `J(n, k)` is
regular of degree `k(n - k)`: a neighbour is obtained by swapping one chosen element for one
unchosen one.  From that degree sequence the edge count, maximum degree and minimum degree of
every Johnson graph follow in one line each.  Two identities round the batch out: because
`T(n) = L(Kₙ)`, the chromatic number of a triangular graph *is* the edge chromatic number of a
complete graph, `χ(T(n)) = χ'(Kₙ)`, so the bounds `n - 1 ≤ χ'(Kₙ) ≤ 2n - 3` and the class-two
lower bound for odd `n` all transport; and Gallai's identity turns the known independence
numbers of `T(n)` and `K(2m+2, 2)` into their vertex cover numbers.


A second round fills in the arithmetic that the Johnson degree sequence unlocks: the edge
counts of `J(n, k)` and of the Kneser graph `K(n, k)`, and the edge count of the line graph
`L(J(n, k))`.  The radius of a join is also settled.  A join of two nonempty graphs is
connected with diameter at most two, so its radius is one or two, and `rad(G ∨ H) = 1`
exactly when `G` or `H` has a dominating vertex; otherwise it is two.  The same
`rad = 1 ↔ γ = 1` bridge gives the radius-one cases of the strong and lexicographic products.
The prover contributed the domination number of a rook graph, `γ(K_m □ K_n) = min(m, n)`: one
full row or one full column dominates, and a case split on whether some row is missed shows
nothing smaller can.

The prover also refuted a conjecture, for the second time in this development.  A wheel `W_n`
has a hub of degree `n`, so `χ'(W_n) = n` and not `n - 1`; asked for the latter, the prover
returned a `negate_state` refutation exhibiting `W₄`, whose maximum degree is already four.


Two of the line graph's invariants are other names for invariants of the base graph, and now
say so: `χ(L(G)) = χ'(G)` and `α(L(G)) = ν(G)`, with the vertex cover number `τ(L(G)) =
|E(G)| - ν(G)` following from Gallai.

The prover then established that every circulant graph is vertex transitive — translation by
one is an automorphism — and a whole row of the invariant table falls out of that single fact.
A circulant is regular, so its vertex and edge counts pin down its degree sequence and hence
its maximum and minimum degree; its radius equals its diameter; the clique–coclique bound
`α · ω ≤ n` applies, giving `2α ≤ n` as soon as there is an edge; the complement of a circulant
is again vertex transitive; and Gallai turns any independence number into a vertex cover
number.  Alongside it the prover settled `θ(K_m □ K_n) = min(m, n)` — the rows or the columns,
whichever are fewer, are a clique cover matching the independence number — and the slab bound
`max(α(G)·|H|, |G|·α(H)) ≤ α(G × H)` for the tensor product.

The prover refuted two more conjectures.  `girth(G ⊔ H) = min(girth G, girth H)` is false under
this development's convention that an acyclic graph has girth zero: `girth(K₁ ⊔ C₃) = 3`, not
`min(0, 3) = 0`.  And Weichsel's theorem needs the second factor to have an edge: `K₃ × K₁` is
edgeless on three vertices, so a connected non-bipartite `G` and a connected `H` are not on
their own enough for `G × H` to be connected.


The Johnson graphs got their metric.  The prover showed `J(n, k)` is connected and that its
diameter is `min(k, n - k)` — two `k`-sets at Hamming distance `d` are `d` swaps apart, and no
pair is further — which fixes the component count at one and, by complementation, makes the
complement of a Kneser graph `K(n, 2)` connected.  It also found a perfect matching in the rook
graph, `ν(K_{m+1} □ K_{n+1}) = ⌊(m+1)(n+1)/2⌋`, and the degree sequence of a ladder, four
degree-2 corners and `2n` degree-3 interior vertices, from which `2‖L_n‖ = 8 + 6n`.


The prover then took the strong product and the line graph.  It showed that the radius of a
strong product is the maximum of the two radii — the king moves both coordinates at once, so
distances are maxima rather than sums — which gives the radius of a king graph on any board and,
combined with the earlier transitivity results, the diameter of the toroidal king graph and of a
strong product of hypercubes.  It also proved that the line graph of a connected graph with an
edge is connected, and that the wheel has a near-perfect matching.  Johnson graphs turned out
not to need the prover at all: the permutation action that makes `kneserAuto` an automorphism
preserves the size of an intersection just as well as its emptiness, so the same argument gives
`johnsonAuto` and the vertex transitivity of every `J(n, k)` — and with it the radius
`min(k, n - k)`, the clique–coclique bound, and Gallai's identity for the whole family.


Three more prover results and a hand-written companion.  The diameter of a strong product is
the maximum of the two diameters, matching the radius; the domination number of the triangular
graph `T(n)` is `⌊n/2⌋`, since a dominating set there is an edge dominating set of `Kₙ` and a
near-perfect matching is one; and the edge chromatic number of the hypercube is `n`, though that
proof is parked until König's edge-colouring theorem lands, which it uses.  Vertex transitivity
also gives a small API of its own: a transitive graph is regular of degree `δ`, so `2‖G‖ = |G|·δ`
and a transitive graph of odd order has even degree — which in turn counts the edges of any
circulant without ever looking at its connection set.  The degree argument runs backwards too:
paths, stars, wheels, fans, books and ladders all have two vertices of different degrees, so
none of them is vertex transitive.


A Cartesian product of two triangle-free graphs with an edge each has girth exactly four:
the two edges span a square, and a triangle in the product would have to project to one in a
factor, because every product edge moves exactly one coordinate and a triangle whose three
edges do not all move the same coordinate needs an edge that moves both.  That replaces the
bipartite hypothesis of the earlier product-girth lemma by a triangle-free one, so it settles
the odd prisms (`girth_prism` now covers every prism on a cycle of length at least four, not
just the even ones), the torus of two long cycles, and a cycle crossed with a path.  In the
other direction the three `k`-sets `{0, …, k-2, k-1+j}` for `j = 0, 1, 2` are pairwise
adjacent in a Johnson graph, which gives `girth_johnson` for all `k ≥ 1` and `n ≥ k + 2` --
previously only the `k = 2` row was known, via the strongly-regular table -- and with it a
triangle, a 3-clique, a 3-chromatic lower bound, and non-acyclicity for the whole family.

The same triangle argument runs for Kneser graphs: three pairwise disjoint blocks of `k`
consecutive points give `girth_kneser` whenever `n ≥ 3k`, which extends the girth-three row
from the `k = 2` case to the whole family and yields the clique, chromatic and acyclicity
corollaries.  On the domination side the four-cube needs four codewords -- the sphere-covering
bound `2^n ≤ γ · (n + 1)` forces at least four, and `{0000, 0001, 1110, 1111}` is a dominating
set -- which is the first hypercube beyond the perfect-code cases `Q₁`, `Q₃`.

Three pairs -- `{0,1}`, `{1,2}`, `{0,2}` -- dominate the Kneser graph `K(n,2)` for every
`n ≥ 5`, because any other pair either equals one of them or is disjoint from one of them, and
no two vertices suffice; the prover found both halves.  Alongside it a sweep of small
consequences fills in the tree column (a book, a cocktail party graph, a triangular graph, a
rook's graph, a balanced complete multipartite graph, a Paley graph and a line graph of a
graph with a degree-three vertex all have a cycle, and `empty n` is a tree exactly when
`n = 1`), the regularity and vertex-transitivity of balanced complete multipartite graphs
(they are lexicographic products of a complete graph with an edgeless one), and the edge count
and diameter of a circulant from its vertex-transitivity.

The fan `F_n` -- a path on `n + 1` vertices joined to a hub -- has matching number
`⌊(n + 1) / 2⌋`: the prover routed through `matchNum_eq`, turning the matching into an
independent set in the line graph, and then exhibited one explicitly (a spoke together with
every other path edge) while bounding it above by the vertex count.

A larger harvest closes five prover targets at once: a book has matching number two, a
balanced complete multipartite graph has a near-perfect matching (the prover enumerated the
parts globally and paired consecutive vertices), a complete graph of odd order is class two
(colour the pair `{i, j}` by `i + j mod n`, a proper edge colouring with `n` colours), the line
graph raises the diameter by at most one, and -- the most useful of the five -- a clique in a
line graph is a star or a triangle, so `ω(L(G)) = Δ(G)` as soon as `Δ(G) ≥ 3`.

That last one pays for itself several times over.  Applied to `K_n` it gives the clique number
`n - 1` of the triangular and Johnson graphs, and hence, by complementation, the
Erdős--Ko--Rado value `α(K(n,2)) = n - 1` for the Kneser graph on pairs together with its
vertex cover number; applied to the Petersen graph and the hypercubes it gives their line
graphs' clique numbers.  The odd class-two colouring gives `χ(J(2m+3, 2)) = 2m + 3` and the
clique cover number of the odd Kneser graph on pairs.  A small companion lemma -- a graph of
girth three is not bipartite -- rules out bipartiteness for Paley graphs and for line graphs of
graphs with a degree-three vertex.

Three construction families join the list.  The Turán graph `T(n, r)` is the complete
multipartite graph on `n` vertices whose `r` parts are as equal as possible; it is defined as
`completeMultipartite` of `n % r` parts of size `⌊n/r⌋ + 1` followed by `r - n % r` parts of
size `⌊n/r⌋`, which makes the vertex count a two-line calculation and the chromatic and clique
numbers `r` outright.  `T(n, 1)` is edgeless, `T(n, n)` is complete, `T(n, 2)` is the balanced
complete bipartite graph (hence bipartite), and `T(n, r)` collapses to a balanced multipartite
graph when `r` divides `n`.  The friendship graph `F_n` -- `n` triangles glued at a hub -- is
`K_1` joined to a perfect matching, so the complement of a cocktail party graph supplies every
invariant through the join formulas: `χ = ω = 3`, `α = max(n, 1)`, `θ = n`, `β = n + 1`,
`Δ = 2n`, `δ = 2`, girth three, domination number one, radius one and diameter two, plus
`F_0 = K_1` and `F_1 = K_3`.  The crown graph `S_n` -- `K_{n,n}` minus a perfect matching -- is
the tensor product `K_n × K_2`, which hands over its vertex and edge counts, bipartiteness,
vertex-transitivity, `(n-1)`-regularity and `χ = ω = 2`, and identifies `S_2` with `2K_2` and
`S_3` with `C_6`.

Two further prover targets landed alongside them: the degree sequence of a fan (two path ends
of degree two, the interior of the path at degree three, and the hub) and the fact that the
radius of a line graph exceeds the radius of a connected graph by at most one -- the companion
of the earlier diameter bound, proved by lifting a walk from `G` to `L(G)` one edge at a time.

The prover then filled in the harder invariants of the three new families.  Vertex
transitivity bounds `α · ω ≤ n` from above and the tensor-product bound bounds it from below, so
a crown graph has independence number `n` -- each side of the bipartition, as expected -- and
hence cover number `n` too.  Both the crown graph and the friendship graph have the maximum
matchings one would draw by hand (a perfect matching for the crown, one edge per triangle for
the friendship graph), and the independence number of a general Turán graph is the size
`⌈n / r⌉` of its largest part, which needs a careful `max?` computation over the two blocks of
part sizes.

Crown graphs turned out to be the complement of a rook graph: deleting a perfect matching from
`K_{n,n}` leaves the tensor product `K_n × K_2`, and complementing a `n × 2` rook graph does the
same thing, so `crown n = compl (rook n 2)` and the whole rook invariant table becomes available
by complementation.  That is how the clique cover number `θ(S_n) = n` falls out -- it is the
chromatic number of the rook graph, which the earlier Latin-square argument already computed.
The prover supplied the girth: a crown graph on at least eight vertices has girth four, the
shortest cycle alternating between the two sides and skipping the two missing matching edges,
which also rules out acyclicity and treeness.  Regularity gives `Δ = δ = n - 1` and the walk
argument gives connectedness for `n ≥ 3`.  One target came back refuted rather than proved: the
guess that a crown graph needs four dominating vertices is wrong, and the counterexample the
prover produced -- the adjacent pair `(0,0), (0,1)` in `S_4`, which between them see every other
vertex -- shows the answer is two.  The corrected statement went back into the queue and came
back proved: `{(0,0), (0,1)}` is dominating and no vertex is universal, so `γ(S_n) = 2`.

The last crown-graph invariant is its diameter.  The prover's argument is the textbook one made
formal: the two ends of a deleted matching edge lie in the same part, have no common neighbour
because the two sides of the bipartition exhaust the second coordinate, and are joined by the
three-step walk `(0,0) - (1,1) - (2,0) - (0,1)`; a parity argument -- the second coordinate is a
proper two-colouring, so every walk between differently coloured endpoints is odd -- rules out
lengths zero, one and two.  Every other pair is at distance one or two, which needs a third
vertex distinct from both and hence the eight-vertex hypothesis.  Vertex transitivity turns the
diameter into the radius for free.

The general (unbalanced) Turán graph then filled out.  Because a part of a complete multipartite
graph is simultaneously a maximum independent set and an unavoidable obstruction for any clique
cover, `θ = α = ⌈n/r⌉` follows from the independence number already proved.  The edge count comes
out as the complement of the within-part edges, `|E| + (n mod r)·C(⌊n/r⌋+1, 2) +
(r - n mod r)·C(⌊n/r⌋, 2) = C(n, 2)`, for every `n` and `r` including the degenerate ones.
Connectivity splits the part list at the boundary between the big and the small parts and joins
the two halves, and with more parts than vertices the Turán graph degenerates to `K_n`.  The
prover contributed the domination number: as soon as every part has two vertices no single
vertex dominates either side of that join, so `γ(T(n, r)) = 2`.

Regularity makes a degree sequence a one-line consequence, so every regular family that had a
regularity lemma but no degree sequence got one: crown graphs, balanced Turán graphs, the
perfect matching that complements a cocktail party graph, the two-rung ladder, and the line
graphs of the Petersen graph, of prisms, of hypercubes, of cocktail party graphs, of balanced
complete bipartite graphs, of triangular graphs and of Kneser graphs.  The friendship graph is
not regular, and the prover produced its degree sequence separately -- `2n` twos followed by the
hub's `2n` -- by counting the join's degree multiset and then sorting it.

The Turán graph's extreme degrees follow the sizes of its extreme parts: a vertex misses
exactly its own part, so `Δ(T(n, r)) = n - ⌊n/r⌋` (a vertex of a smallest part) and
`δ(T(n, r)) = n - ⌈n/r⌉` (a vertex of a largest part).  With two parts of size at least one the
graph has a dominating edge, so its radius is `2` as well as its diameter.  On the Paley side,
the last straggler from an earlier batch came back proved on a refire: the pairs `{2i, 2i+1}`
form an independent set in the line graph, so `ν(P_q) = ⌊q/2⌋` -- a near-perfect matching,
perfect exactly when `q` is even, which it never is.

Two parts of a Turán graph are joined completely, so with `2r <= n` a single edge dominates
the whole graph and `diam(T(n, r)) = 2`.  A few cross-family identities finish the picture:
parts of size two make a cocktail party graph, `T(2r, r) = K_{r x 2}`; a balanced Turán graph is
the blow-up `K_r[E_{n/r}]`; and its complement is `r` disjoint cliques of size `n/r`, which is
what the parts were all along.  Together with the existing `T(n, 1) = E_n`, `T(n, 2) = K_{a,b}`
and `T(n, n) = K_n` that covers every degenerate choice of `r`.

A Paley graph is `(q-1)/2`-regular on `q` vertices, so the handshake lemma pins its edge count
without any character sums: `4|E(P_q)| = q(q-1)`.

**Weichsel's theorem** came back from the prover: the tensor product of two connected graphs is
connected as soon as one factor is non-bipartite and the other has an edge.  The proof pairs a
walk in `G` with a walk of the same length in `H`, padding the shorter one two steps at a time
along a fixed edge and fixing the parity with an odd closed walk through the non-bipartite
factor.  Alongside it, an odd cycle of length at least five is covered by `m + 2` edges and one
leftover vertex, so `θ(C_{2m+5}) = m + 3`.

Firing the prover at one file with several open `sorry`s has a catch worth recording: the other
targets in the file are in scope, so a returned proof may quietly depend on a sibling that is
still open.  Three edge-colouring results -- for ladders, crowns and hypercubes -- came back
this way, each a one-line appeal to König's edge colouring theorem, which is exactly the target
that did not come back.  They are parked until König lands.

The friendship graph turned out to be the one edge colouring the prover could do from scratch:
`chi'(F_n) = 2n`, by numbering the spokes at the hub `2i` and `2i+1` and giving the triangle
edge at petal `i` the colour `2i + 2 mod 2n`, then checking the three ways two edges can meet.

Complements round out the newer families: the friendship graph's complement is an isolated hub
beside a cocktail party graph, a Turán graph's complement is `r` disjoint cliques (`n mod r` of
them one vertex larger), and the triangular graph and the Kneser graph `K(n, 2)` are each
other's complements in both directions rather than only one.

The prover also settled the matching number of a general Turán graph. The proof is a round-robin
argument: send vertex `j` to slot `j / r` of part `j mod r`, which is a bijection onto the vertex
set, and then pair `2t` with `2t + 1`. Consecutive vertices differ mod `r` whenever `r` is at
least two, so every pair is an edge, and the resulting `n / 2` edges are pairwise disjoint.

One small-graph coincidence went in by hand: the crown graph on eight vertices is the cube. Both
sides are `K4` times `K2`, but with different products — the crown is the tensor product and the
cube is the four-rung prism — so the identity is an explicit vertex bijection checked by `decide`,
built by matching each vertex to the one non-neighbour it has on the other side.

The Grötzsch graph now has a name of its own. It is the Mycielskian of the pentagon, so its order,
size, chromatic number and clique number all fall out of the general Mycielskian lemmas: eleven
vertices, twenty edges, four colours, no triangle. That makes it the smallest witness to
`exists_cliqueNum_le_two_and_le_chromNum` beyond the pentagon itself.

Two Möbius ladders join the small-graph identities: `circulant (2m) [1, m]` is a `2m`-cycle with
all `m` diameters added, and for `m = 2` and `m = 3` that is `K4` and `K(3,3)` respectively. The
second is the reason every odd difference on six points is `1`, `3` or `5`, so the parity classes
of the hexagon become the two sides of a complete bipartite graph.

The prover returned the degree sequence of a general Turán graph, and the proof turned out not to
need `r <= n` at all: when there are more parts than vertices the Turán graph is complete and the
two-value formula degenerates correctly, so the landed statement is the stronger one. Sorting the
multiset of degrees is most of the work — the graph side is just "a vertex misses its own part".

`isSelfComplementary_paley` generalises the two hard-coded witnesses for `q = 13` and `q = 17`:
for any prime `q ≡ 1 (mod 4)`, pick a field element `g` whose quadratic character is `-1`, and
multiplication by `g` is a bijection of the field that sends squares to non-squares and back. Since
`q ≡ 1 (mod 4)` makes `-1` a square, the difference `g * x - g * y = g * (x - y)` flips membership
in the residue set exactly when `x - y` did not, so the map is an isomorphism from the Paley graph
onto its own complement. Transporting the witness along `paleyIso` gives the statement for the
combinatorial model, and `compl_paley` records the resulting `compl (paley q) = paley q` as a
conditional `simp` lemma.

Three more small coincidences join the identity table. `circulant_six_one_two` identifies the
octahedron `K_{2,2,2}` with the circulant `C₆(1, 2)`, by complementing the perfect matching
`C₆(3)` that `compl_cocktailParty_eq_circulant` already supplies. `circulant_six_two_three`
identifies the triangular prism with `C₆(2, 3)`: the even residues span one triangle, the odd
residues the other, and the three diameters are the rungs. `fan_three` records that the fan on a
three-vertex path and the two-page book are both `K₄` with one edge deleted.

The prover's biggest return in this round is a round-robin edge colouring of the even complete
graph. Identifying the vertices of `K_{2m+4}` with `ℤ/(2m+3)` plus one extra point, the edge
`{i, j}` takes colour `i + j` and the edge from the extra point to `i` takes colour `2i`; since
`2m+3` is odd, doubling is invertible mod `2m+3`, which is what makes the second rule collision
free. That gives `edgeChromNum_complete_even`, and with the single edge handled separately it
covers every even complete graph. Because the line graph of `K_n` is the triangular graph and the
triangular graph is the complement of `K(n, 2)`, the same result immediately yields
`cliqueCoverNum_kneser_two_even`: covering the Kneser graph `K(2m+4, 2)` by cliques needs `2m+3`
of them.

With both parities of `edgeChromNum_complete` in hand the table closes up around the triangular
and Kneser graphs: `edgeChromNum_complete` states the two cases as a single conditional,
`chromNum_triangular_even` completes the chromatic number of `T(n)` (the odd case was already
there), and `cliqueCoverNum_kneser_two` records the general identity that covering `K(n, 2)` by
cliques is exactly edge colouring `K_n`.

Two more edge colourings came back from the prover, both by explicit constructions rather than by
appeal to König or Vizing. `edgeChromNum_hypercube` colours the edge of `Qₙ` joining `x` to
`x` with bit `i` flipped by the colour `i`, which is a proper `n`-edge-colouring because two edges
sharing a vertex flip different bits. `edgeChromNum_wheel` handles the wheel with at least four
rim vertices: the spoke to rim vertex `i` takes colour `i` and the rim edge `{i, i+1}` takes
colour `i + 2` modulo the rim length, so the hub's `n` colours are all distinct and each rim
vertex sees three different ones.

The metric invariants use the convention that a disconnected graph has diameter and radius `0`,
since the honest value `⊤` truncates that way. `radius_eq_zero_of_not_isConnected` states this
once and `radius_disjUnion` applies it, closing the last gap in the radius row of the invariant
table apart from the Mycielskian.

`E_le_E_turan` sharpens the Turán bound above from the arithmetic inequality
`2r·|E| ≤ (r - 1)·|V|²` to the extremal statement itself: a graph with `ω(G) ≤ r` has no more
edges than the Turán graph `T(|V|, r)` does. Both are corollaries of the same Mathlib theorem,
but the arithmetic form loses the remainder term, so the sharp version is strictly stronger
whenever `r ∤ |V|`. Getting there means reconciling two edge counts — Mathlib's
`card_edgeFinset_turanGraph`, which is `(n² - s²)(r - 1)/(2r) + C(s, 2)` for `s = n mod r`, and
this library's `E_turan`, which counts the parts directly as `s·C(q + 1, 2) + (r - s)·C(q, 2)`
subtracted from `C(n, 2)`. Doubling both and casting to `ℤ` makes them the same polynomial in
`q`, `r` and `s`.

The degree row of the Mycielskian table closes as well, and it closes all at once, because
`degMultiset_mycielskian` computes the whole multiset: the original vertices contribute `2d`
for each degree `d` of `G`, the shadows contribute `d + 1`, and the apex contributes `|V|`. Both
`minDeg_mycielskian` (`min (min (2δ) (δ + 1)) |V|`, for a nonempty `G`) and `maxDeg_mycielskian`
(`max (2Δ) |V|`) then read straight off it, as would any other order statistic. `μ(G)` is
connected as soon as `G` has no isolated vertex — every shadow reaches the apex in one step and
every original reaches a shadow of a neighbour — which is `isConnected_mycielskian`.

One more edge-colouring criterion, in the negative direction this time. A `k`-regular graph on an
odd number of vertices is class two: each colour class is a matching, so it misses a vertex and
has at most `(|V| - 1)/2` edges, while handshaking puts `|V|·k/2` edges in the graph — so `Δ = k`
colours cannot suffice. This is `maxDeg_lt_edgeChromNum_of_isRegularWith_odd`, and it generalises
the complete-graph-of-odd-order case that was proved by hand earlier.

Two more Mycielskian rows, both exact. `domNum_mycielskian` says domination costs exactly one
more: `γ(μ(G)) = γ(G) + 1` for nonempty `G`. Upwards is the obvious construction — the shadows of
a dominating set, plus the apex to cover the shadows the apex does not otherwise reach. Downwards
is the real work, and it splits on whether the apex is in the dominating set `D`: if it is,
projecting `D \ {apex}` back to `V(G)` dominates `G` and costs one fewer; if it is not, then some
shadow lies in `D` (the apex has to be dominated), and dropping one such shadow from the union of
`D`'s originals and shadows leaves a dominating set of `G`. `matchNum_mycielskian` says a graph
with a perfect matching gives a Mycielskian with a *near*-perfect one, `ν(μ(G)) = |V(G)|`: match
every original to the shadow of its partner, which uses `2ν(G) = |V|` vertices on each side and
leaves only the apex out. The upper bound is just `2ν ≤ |V|` applied to `μ(G)`, which has
`2|V| + 1` vertices.

Those general lemmas immediately fill in most of the Grötzsch row, since `grotzsch` is by
definition `mycielskian (cycle 5)`. `degMultiset_grotzsch` is five `4`s (the pentagon vertices,
`2 · 2`), five `3`s (their shadows, `2 + 1`) and a single `5` (the apex), so `δ = 3` and `Δ = 5`;
`γ = γ(C₅) + 1 = 3`; the pentagon has no isolated vertex, so the graph is connected and
`numComponents = 1`. Three of the twelve needed work of their own. The diameter and the radius
are both `2` — every pair of vertices is joined by a path of length two (two shadows through the
apex, a shadow and a pentagon vertex through a common pentagon neighbour, the apex and `vᵢ`
through `u_{i±1}`), and nothing is adjacent to all ten others, which rules out `1` via
`radius_eq_one_iff_domNum_eq_one`. The girth is `4`: the square `v₀ u₁ w u₄` gives the upper
bound and the Mycielskian of a pentagon has no triangle. The matching number is `5`, and the
neatest route turned out to be the line graph — the five edges `vᵢ u_{i+1}` are pairwise disjoint,
so they are an independent set of `L(grotzsch)`, and `matchNum_eq` converts that back; the upper
bound is `2ν ≤ 11`. Finally `¬IsAcyclic` follows from the graph not being bipartite, and
`¬IsVertexTransitive` from `δ ≠ Δ`. The clique cover number is `6`, and since
`κ(G) = χ(Gᶜ)` this is a statement about the complement: `|V| ≤ χ · α` applied to `grotzschᶜ`,
whose independence number is `ω(grotzsch) = 2`, gives `χ(grotzschᶜ) ≥ 11/2`, hence `≥ 6`, and an
explicit six-colouring of the complement matches it. The one entry still missing is `α` — the five shadows are
independent, and the answer is `5`, but the obvious general shape `α(μ(G)) = max (2 α(G)) |V(G)|`
is false (`K₁ ⊔ K₃` has an independent set of size five in its Mycielskian and only `max 4 4 = 4`
on the right), and brute force over the eleven vertices is out of reach for a `native_decide`-free
kernel.

The four decorated families — tadpoles, lollipops, double stars and theta graphs — get their
edge counts. All four are built by `CGraph.ofEdges` from an explicit list, so the argument is
always the same: the list has no self-loops, no duplicates and no reversed pairs, therefore `E`
is its length. Doing that honestly is most of the work, and the theta graph is the worst of them
because its edge list is assembled recursively, one path at a time, with an offset that moves as
the recursion descends; the induction has to carry all four disjointness facts at once. The
answers are `E(D_{m,n}) = m + n + 1`, `E(L_{m+1,k}) = C(m + 1, 2) + k`, `E(T_{m+3,k}) = m + k + 3`
and `E(Θ_{xs}) = Σxs + |xs|`. A few shape invariants come with them: a lollipop with at least
three clique vertices has a triangle, so `girth_lollipop = 3`, and its clique is the largest one
it has, `cliqueNum_lollipop (m + 2) k = m + 2`; a tadpole's junction is its only vertex of degree
three, `maxDeg_tadpole = 3`; and a double star has a pendant, so `minDeg_doubleStar = 1`, with
`maxDeg_doubleStar = max m n + 1` at the busier of the two centres. Two harder entries followed.
`chromNum_lollipop (m + 2) k = m + 2` needs a colouring in both directions: upwards, give clique
vertex `i` the colour `i` and alternate two of those colours along the tail, which is proper
because the tail is a path hanging off vertex `0`; downwards, the inclusion `Fin (m + 2) ↪
Fin (m + 2 + k)` is a graph homomorphism from `K_{m+2}`, and `chromaticNumber_mono_of_hom` does
the rest. `indepNum_doubleStar (m + 1) (n + 1) = m + n + 2` goes through the complement instead:
the `m + n + 2` pendants are pairwise non-adjacent, and the two disjoint edges `0–2` and
`1–(m + 3)` force every vertex cover to have at least two vertices, so `τ ≥ 2` and
`α = |V| - τ ≤ m + n + 2` by `coverNum_add_indepNum`.

The connectivity row of those families follows. All three of `isConnected_tadpole (m + 3) k`,
`isConnected_lollipop (m + 1) k` and `isConnected_doubleStar m n` are proved the same way — pick
vertex `0` as a hub and walk every other vertex back to it, along the cycle, around the clique or
straight down a pendant — and each hands `numComponents = 1` to
`numComponents_eq_one_of_isConnected` for free. From connectivity the double star's whole row
unwinds at once: it has `m + n + 1` edges
on `m + n + 2` vertices, so `isTree_doubleStar` is `isTree_iff` applied to `E_doubleStar` and
`V_doubleStar`, and then `girth_doubleStar = 0` because a tree is acyclic and
`cliqueNum_doubleStar = 2` because a tree with two vertices has the central edge and nothing
bigger. `chromNum_doubleStar = 2` two-colours by centre-versus-pendant. The last two are counting
arguments in opposite directions. `domNum_doubleStar (m + 1) (n + 1) = 2`: the two centres
dominate everything, and no single vertex can, since a pendant of `0` and a pendant of `1` have no
common neighbour. `matchNum_doubleStar (m + 1) (n + 1) = 2`: match each centre to one of its own
pendants for the lower bound, and for the upper bound `{0, 1}` is a vertex cover, so
`ν ≤ τ ≤ 2`. On the tadpole side, `minDeg_tadpole (m + 3) (k + 1) = 1` is the far end of the
tail, and `cliqueNum_tadpole (m + 4) k = 2` needs the cycle to be long enough to be triangle-free
— at `m + 3 = 3` the tadpole *does* contain a triangle, which is why this one starts at `m + 4`.
The lollipop's degrees came next: `minDeg_lollipop (m + 2) (k + 1) = 1` is again the far end of
the tail, and `maxDeg_lollipop (m + 2) (k + 1) = m + 2` is the junction, which sees the `m + 1`
other clique vertices plus the first vertex of the tail and beats everything else. And
`chromNum_tadpole_even (2 * m + 4) k = 2` is one line: `isBipartite_tadpole_even` plus a nonzero
edge count through `chromNum_eq_two_iff`.

The last three families — spiders, theta graphs and cycles with pendants — start to fill in too.
The edge counts go first: `E_spider legs = legs.sum` and `E_cyclePendant (m + 3) ks =
m + 3 + ks.sum`, both by the same route as the earlier four, showing the generated list has no
loop, no duplicate and no reversed pair and then reading off its length. Neither list is flat, so
both proofs are inductions that carry a moving offset — `spiderEdges off (k :: rest)` recurses
with `off + k`, and `mem_spiderEdges_bound` is what keeps the recursive tail disjoint from the leg
just emitted. `isConnected_cyclePendant (m + 3) ks` and its `numComponents = 1` follow the tadpole
argument: walk a pendant onto its cycle vertex, then around the cycle. The minimum degrees are
both `1` and both are found at a leaf — `minDeg_spider` at the far end of any nonempty leg,
`minDeg_cyclePendant` at any pendant — with the same offset-carrying induction underneath.
`chromNum_tadpole_odd (2 * m + 3) k = 3` is the other half of the tadpole's chromatic number: the
odd cycle sitting inside forces a third colour, and colouring the cycle with three and then
alternating two of them down the tail shows three is enough. `chromNum_cyclePendant_even
(2 * t + 2) ks = 2` is the easy parity, straight out of `isBipartite_cyclePendant_even`. The
double star's covering numbers close its row: `coverNum_doubleStar = 2` is one line from
`indepNum_doubleStar` through `coverNum_eq`, and `cliqueCoverNum_doubleStar (m + 1) (n + 1) =
m + n + 2` is squeezed between `α ≤ κ` from below and `κ ≤ |V| − ν` from above, both of which land
on `m + n + 2` because `ν = 2`.

The spider then goes the way the double star went. `isConnected_spider` walks each vertex back
down its own leg to the centre, and once that is in hand `numComponents_spider = 1`,
`isTree_spider` (`legs.sum` edges on `1 + legs.sum` vertices), `girth_spider = 0` and
`cliqueNum_spider = 2` are each a line or two. `chromNum_spider = 2` is slightly more than that,
because the two colours need an actual edge to justify them, and finding one means digging the
pair `(0, 1)` out of `spiderEdges 1 legs` — which takes an induction that skips the zero-length
legs, since a leg of length `0` contributes no edges at all. And the double star's metric row
closes: `diameter_doubleStar (m + 1) (n + 1) = 3` is the pendant-centre-centre-pendant walk, with
an explicit walk in each of the four cases for the upper bound and the two specific pendants `2`
and `m + 3` for the lower one, and `radius_doubleStar = 2` follows because a centre reaches
everything in two steps and nothing dominates.

Three of the families are provably *not* trees, and all three go the same way: assume acyclicity,
combine it with the connectivity lemma to get `IsTree`, and then read `|E| = |V| - 1` off
`isTree_iff` and contradict the edge count. `not_isAcyclic_tadpole (m + 3) k` and
`not_isAcyclic_cyclePendant (m + 3) ks` both have `|E| = |V|` exactly — a cycle with things hanging
off it has one edge too many — so `omega` closes them immediately. `not_isAcyclic_lollipop
(m + 3) k` has more room than that, `binom(m + 3, 2) + k` edges against `m + 3 + k` vertices, and
the arithmetic step is showing `m + 3 ≤ binom(m + 3, 2)`, which is `Nat.choose_two_right` followed
by `Nat.le_div_iff_mul_le` and one `nlinarith`. The `m + 3` floor is real in each case: the
`K₂`-with-a-tail and the `2`-cycle degenerate away, and a lollipop on two clique vertices is a
path.

Two theta-graph conjectures were refuted along the way, and for the same reason. A path with no
internal vertices *is* the edge `0 – 1`, so `thetaGraph [0, 0]` is not a theta graph at all — the
two paths collapse onto each other and it is `K₂`, which is a tree. That kills
`¬IsAcyclic (thetaGraph xs)` for `2 ≤ xs.length`, and `[0, 0, 1]` collapses to a triangle, whose
maximum degree is `2` rather than `3`, which kills `maxDeg (thetaGraph xs) = xs.length`. Both are
back in flight with every path required to be subdivided at least once.

The Mycielskian's independence number is now bracketed from both sides.
`V_le_indepNum_mycielskian` says `|V(G)| ≤ α(μ(G))` for every `G`, because the `|V(G)|` shadow
vertices are pairwise non-adjacent — shadows only ever meet originals and the apex. Going the
other way, `indepNum_mycielskian_le` says `α(μ(G)) ≤ |V(G)| + α(G)` for nonempty `G`. Take an
independent set `I`. If it contains the apex then it contains no shadow at all, so what is left
is an independent set of the original copy and `|I| ≤ 1 + α(G)`, which is where `0 < |V(G)|` is
spent. If it does not, then `I` splits into its originals — independent in `G`, so at most `α(G)`
of them — and its shadows, of which there are at most `|V(G)|`. The nonemptiness hypothesis is
not decoration: the prover *refuted* the statement without it, since `μ` of the empty graph on no
vertices is a lone apex with `α = 1` against a right-hand side of `0`.

`radius_mycielskian` is exact whenever `G` has no isolated vertex: `rad(μ(G)) = 2`. The apex is at
distance `1` from every shadow and at distance `2` from every original vertex — walk to the
shadow of one of its neighbours — so its eccentricity is exactly `2`, and the radius is at most
`2`. It is not `1`, because no vertex of `μ(G)` is adjacent to all the others: the apex misses the
originals, an original misses the apex, and a shadow misses the other shadows. That is
`radius_eq_one_iff_domNum_eq_one` read backwards.

The independence bracket transfers straight to vertex covers through
`coverNum_add_indepNum` (`τ + α = |V|`). Reading `V_le_indepNum_mycielskian` through it gives
`coverNum_mycielskian_le : τ(μ(G)) ≤ |V(G)| + 1`, since `μ(G)` has `2|V(G)| + 1` vertices and at
least `|V(G)|` of them can be left out of the cover. Reading `indepNum_mycielskian_le` through it
the other way gives `coverNum_lt_coverNum_mycielskian : τ(G) + 1 ≤ τ(μ(G))` for nonempty `G` —
the Mycielskian construction always costs at least one extra cover vertex, which is the covering
shadow of the fact that it always costs at least one extra colour. Both are three `have`s and an
`omega`.

Forests are bipartite, and that one implication turns a whole shelf of non-bipartiteness results
into acyclicity results. `isBipartite_of_isAcyclic` is the implication — a forest has no cycle at
all, so in particular no odd one — and `not_isAcyclic_of_not_isBipartite` is its contrapositive.
That immediately gives `not_isAcyclic_strongProduct` and `not_isAcyclic_lexProduct` whenever both
factors have an edge, `not_isAcyclic_join_left` whenever the left factor is not bipartite, and
`not_isAcyclic_join_join` for any three nonempty graphs joined together. It also shortens
`not_isAcyclic_grotzsch` to a single line. For the Mycielskian the same route needs one step
first: `not_isBipartite_mycielskian_of_E_pos` promotes the existing edge-indexed statement to the
edge-count hypothesis by pulling an edge out of `exists_adj_of_E_pos`, and then
`not_isAcyclic_mycielskian` says that one edge of `G` is enough to put a cycle — in fact the
pentagon `vₐ – v_b – uₐ – w – u_b – vₐ` — into `μ(G)`. `numComponents_mycielskian = 1` is the
matching restatement of `isConnected_mycielskian`.

The Mycielskian's clique cover number is exact whenever the input is triangle-free and has a
perfect matching: `cliqueCoverNum_mycielskian : κ(μ(G)) = |V(G)| + 1`. Both bounds are one
rewrite each. From above, `μ(G)` inherits the perfect matching as a matching of size `|V(G)|`
(`matchNum_mycielskian`), and `cliqueCoverNum_le_V_sub_matchNum` turns that into
`κ ≤ (2|V(G)| + 1) − |V(G)|`. From below, `μ(G)` is still triangle-free
(`cliqueNum_mycielskian_eq_two`), so `V ≤ κ · ω` reads `2|V(G)| + 1 ≤ 2κ`, and an odd vertex count
cannot be covered by `|V(G)|` edges. `cliqueCoverNum_grotzsch = 6` is the case `G = C₅`.

Two more consequences of what is already there. `radius_mycielskian = 2` brackets the diameter
through the two standard inequalities: `two_le_diameter_mycielskian` is `rad ≤ diam` read
forwards and `diameter_mycielskian_le_four` is `diam ≤ 2 · rad` read forwards, so once `G` has no
isolated vertex the diameter of `μ(G)` is `2`, `3` or `4`. And
`not_isAcyclic_circulant_of_odd` is the forest-is-bipartite argument applied to
`not_isBipartite_circulant_of_odd`: an odd circulant with any nonzero connection has a cycle.

The theta graph gets its chromatic number in the same-parity case.
`chromNum_thetaGraph_of_parity` says two colours suffice as soon as every path has the same
parity of length and every path is genuinely subdivided; `isBipartite_thetaGraph_of_parity`
supplies the colouring and `E_thetaGraph` supplies the edge that stops the answer being `1`.
The two readable corollaries are `chromNum_thetaGraph_odd`, where the parity hypothesis makes
positivity automatic, and `chromNum_thetaGraph_even`, where it has to be asked for — `0` is even,
and a path with no internal vertices collapses onto the pole-to-pole edge.

The clique cover argument behind the Mycielskian's `κ` is really general, so it is now stated as
such. `le_cliqueCoverNum_of_cliqueNum_le_two` says a triangle-free graph needs at least
`⌈|V| / 2⌉` cliques, since each one is a vertex or an edge, and
`cliqueCoverNum_of_cliqueNum_le_two` upgrades that to an equality whenever the matching number is
near-perfect (`|V| ≤ 2ν + 1`): the matching covers all but at most one vertex from above, and the
counting bound blocks anything smaller from below. `cliqueCoverNum_grotzsch = 6` drops out of it
in four lines — `|V| = 11`, `ν = 5`, `ω = 2` — replacing a forty-five-line explicit six-colouring
of the complement. The new instance is `cliqueCoverNum_foldedCube_odd`: an odd folded cube is
bipartite with a perfect matching, so `κ(foldedCube (2m + 3)) = 2²ᵐ⁺²`, exactly half its
vertex count.

The independence side of the same argument is a weak König theorem.
`indepNum_of_isBipartite_of_matchNum` says a bipartite graph with a near-perfect matching has
`α = ⌈|V| / 2⌉`: one colour class already supplies that many vertices through `|V| ≤ χ · α` with
`χ = 2`, and `α = |V| − τ ≤ |V| − ν` caps it. `coverNum_of_isBipartite_of_matchNum` is the
complement, `τ = ⌊|V| / 2⌋`. Two vertex covers that were missing fall out by subtraction:
`coverNum_foldedCube_odd = 2²ᵐ` and `coverNum_prism_odd (2m + 3) = 2m + 4`, the second one a
vertex more than half because an odd prism's largest independent set misses a vertex.

Three small holes in the older rows are filled too. `maxDeg_bipartite (m + 1) (n + 1)` and
`minDeg_bipartite` are `max` and `min` of the two side sizes, read off `bipartite_eq_join`
together with `maxDeg_join` and `minDeg_join` — the `_self` special cases were all that existed.
And `E_foldedCube (n + 2) = 2ⁿ⁺¹(n + 3)` is `two_mul_E_foldedCube` divided by two.

Cycles now propagate through the products. `not_isAcyclic_of_three_le_cliqueNum` is the
contrapositive of `cliqueNum_le_two_of_isAcyclic` and does most of the work:
`not_isAcyclic_cartesianProduct` splits on whether either factor has a triangle — if one does,
`cliqueNum_cartesianProduct = max ω(G) ω(H)` carries it into the product, and if neither does,
`girth_cartesianProduct_of_cliqueNum_le_two` produces the four-cycle spanned by one edge from each
side. The tensor product needs triangles in *both* factors, since `ω(G ⊗ H) = min ω(G) ω(H)`, so
`girth_tensorProduct = 3` and `not_isAcyclic_tensorProduct` both ask for that.
`numComponents_tensorProduct = 1` is `isConnected_tensorProduct` read through
`numComponents_eq_one_of_isConnected`, and it is the first entry in the tensor product's
connectivity row. Two trees fill in their own missing cells: `isAcyclic_spider` and
`isAcyclic_doubleStar` are the acyclic halves of `isTree_spider` and `isTree_doubleStar`.

Between three and four there is nothing, so `four_le_girth_of_cliqueNum_le_two` says a
triangle-free graph that is not a forest has girth at least four — `three_le_girth` rules out
`0`, `1` and `2`, and `girth_eq_three_iff` rules out `3`. Applied to the Mycielskian, whose clique
number is exactly `2` on any triangle-free graph and which is never a forest once there is an
edge, this gives `four_le_girth_mycielskian`, the first entry in that row.
`radius_compl_le_two` is `diameter_compl = 2` composed with `rad ≤ diam`: the complement of a
disconnected graph with an edge has every vertex within two steps of every other, so some vertex
is within two steps of all of them.

The clique cover row picks up the triangular graphs. `cliqueCoverNum_triangular` is just
`compl_triangular` fed through `κ(G) = χ(Gᶜ)`: covering `L(Kₙ)` by cliques is colouring the Kneser
graph `K(n, 2)`. Lovász' bound then gives `cliqueCoverNum_triangular_le : κ(L(K_{n+4})) ≤ n + 2`,
and the smallest case is exact — `cliqueCoverNum_triangular_five = 3`, because `L(K₅)ᶜ` is the
Petersen graph and `χ(Petersen) = 3`. `cliqueCoverNum_lexProduct_le` is the same trick on the
other side: `compl_lexProduct` says the complement of a lexicographic product is the lexicographic
product of the complements, so `chromNum_lexProduct_le` transports verbatim into
`κ(G · H) ≤ κ(G) · κ(H)`.

Three families are shown to be **class two**, that is, to need `Δ + 1` edge colours rather than
`Δ`. The general reason is `maxDeg_lt_edgeChromNum_of_isRegularWith_odd`: a regular graph on an
odd number of vertices has no perfect matching, so `Δ` colour classes cannot cover all `E` edges.
Paley graphs are regular on `q` vertices with `q` odd, giving `maxDeg_lt_edgeChromNum_paley` and
the explicit `edgeChromNum_paley_ge : χ'(Paley q) ≥ (q + 1) / 2`. Rook graphs with both sides odd
have `(2m + 3)(2n + 3)` vertices, giving `edgeChromNum_rook_odd_ge : χ' ≥ 2m + 2n + 5`. And
balanced complete multipartite graphs with `m · d` odd give
`edgeChromNum_completeMultipartite_replicate_ge : χ' ≥ (m − 1)d + 1`. These are the first
`edgeChromNum` entries for all three families. Finally, `α ≤ 3` and `α ≤ 4` for the two small
Paley graphs turn into `ten_le_coverNum_paley_thirteen` and
`thirteen_le_coverNum_paley_seventeen` by `τ + α = |V|`.

A fourth class-two family joins them, and this one needs a parity computation rather than a
parity hypothesis. `L(Kₙ)` is `(2n − 4)`-regular on `C(n, 2)` vertices, so
`maxDeg_lt_edgeChromNum_triangular` applies whenever that binomial coefficient is odd — which
happens exactly when `n ≡ 2` or `3 (mod 4)`. `edgeChromNum_triangular_ge` evaluates the maximum
degree to give `χ'(T(n + 4)) ≥ 2n + 5`, and the two smallest cases are
`edgeChromNum_triangular_six_ge` (`T(6)` is `8`-regular on `15` vertices, so `χ' ≥ 9`) and
`edgeChromNum_triangular_seven_ge` (`T(7)` is `10`-regular on `21`, so `χ' ≥ 11`). Alongside it
`cliqueNum_le_maxDeg_add_one` records the composite `ω ≤ χ ≤ Δ + 1`, which had never been stated
even though both halves were there.

The `autCount` row had nothing in it beyond `complete` and `empty`, so the arc-transitivity
proofs are now cashed in. `two_mul_E_le_autCount_of_isArcTransitive` says an arc-transitive graph
has at least `2E` automorphisms — one for each image of a fixed arc — and every arc-transitive
family in the library gets its entry: `thirty_le_autCount_petersen`,
`two_mul_le_autCount_cycle`, `mul_two_pow_le_autCount_hypercube` (`|Aut(Qₙ)| ≥ n · 2ⁿ`, against
the true `2ⁿ · n!`), `le_autCount_kneser` and `le_autCount_bipartite_self`. These are lower
bounds, not values, but they are the first non-trivial ones in the table, and they are exactly the
inequality that `not_isArcTransitive_of_autCount_lt` reads backwards.

The cheapest cycle detector in the library turns out to be counting. A tree satisfies
`E + 1 = |V|`, so `not_isTree_of_V_le_E` rejects anything with at least as many edges as
vertices, without exhibiting a cycle; `not_isAcyclic_of_V_le_E` adds connectedness to upgrade
that to acyclicity, and `not_isTree_of_not_isAcyclic` is the trivial direction that had never
been separated out. The tadpole and the cycle with pendant paths have *exactly* as many edges as
vertices, so `not_isTree_tadpole` and `not_isTree_cyclePendant` are one-liners; the lollipop goes
through its clique instead. `four_le_girth_tadpole` then pins the tadpole's girth from below,
since it is triangle-free as soon as its cycle has four vertices.

The clique-cover row gains the same three families via `|V| ≤ κ · ω`: `le_cliqueCoverNum_spider`
and `le_cliqueCoverNum_tadpole` give `κ ≥ ⌈|V| / 2⌉` for the two triangle-free ones, and
`le_cliqueCoverNum_lollipop` the weaker `|V| ≤ κ(m + 2)` that its clique allows.

The rest of the `edgeChromNum` row can at least be bracketed. `Δ ≤ χ'` (the edges at a vertex
pairwise conflict) and `χ' ≤ 2Δ − 1` (greedy on the line graph, whose maximum degree is `2Δ − 2`)
are both already proved in general, so every family whose maximum degree is known gets an
entry: `le_edgeChromNum_{ladder, prism, crown, cocktailParty, book, fan, doubleStar, turan,
foldedCube, grotzsch}`, with `edgeChromNum_{ladder, prism, foldedCube, grotzsch}_le` on the other
side. `le_edgeChromNum_mycielskian` states the general one — `max(2Δ, |V|) ≤ χ'(M(G))`, both
terms of the maximum being realised, the first at a doubled original vertex and the second at the
apex. When Vizing lands, every one of these lower bounds becomes a two-value bracket, and the
class-one families become exact.

Two more domination cells fall to the degree bracket: `le_domNum_tadpole` and `domNum_tadpole_le`
(the tadpole is cubic at its junction, so `|V| ≤ 4γ`), and `le_domNum_lollipop` with
`domNum_lollipop_le` (the clique vertex dominates the whole head at once, giving the much better
`γ + m + 2 ≤ |V|`).

The class-two argument also wanted generalising. It was being applied family by family through
`maxDeg_lt_edgeChromNum_of_isRegularWith_odd`, but the regularity always came from
vertex-transitivity, so `maxDeg_lt_edgeChromNum_of_isVertexTransitive_odd` states the real
theorem: **a vertex-transitive graph of odd order with an edge is class two.** (The edge
hypothesis is what rules out `empty (2n + 1)`, and it is exactly what forces the common degree to
be positive, via the vertex-transitive handshake `2E = |V| · δ`.) Three new rows fall out at
once: `maxDeg_lt_edgeChromNum_circulant` covers *every* circulant on an odd number of vertices
whatever its connection set, and `edgeChromNum_kneser_ge` and `edgeChromNum_johnson_ge` give
`χ'(K(n, k)) > C(n − k, k)` and `χ'(J(n, k)) > k(n − k)` whenever `C(n, k)` is odd, with
`edgeChromNum_kneser_seven_three_ge` and `edgeChromNum_johnson_seven_three_ge` as the smallest
instances (both on `35` vertices).

The spider, tadpole, lollipop, theta and cycle-with-pendants families had chromatic numbers but
no independence or cover entries at all. `V_le_chromNum_mul_indepNum` — some colour class holds
at least `|V| / χ` vertices, and colour classes are independent — converts each of those
chromatic numbers into a lower bound on `α`, and `τ + α = |V|` reflects it into an upper bound on
`τ`: `le_indepNum_spider`, `le_indepNum_tadpole_even`, `le_indepNum_tadpole_odd`,
`le_indepNum_lollipop`, `le_indepNum_thetaGraph_even`, `le_indepNum_thetaGraph_odd`,
`le_indepNum_cyclePendant_even`, each with its `coverNum_…_le` companion. The bipartite cases are
tight up to rounding; the lollipop's is weak, because the clique drives `χ` up to `m + 2`, but it
is the first thing known about that cell.

Vertex-transitivity gives a weaker but far more widely applicable bound than arc-transitivity:
`V_le_autCount_of_isVertexTransitive` says `|V| ≤ |Aut(G)|`, because the orbit of a single vertex
is everything. The library proves vertex-transitivity for a dozen families that are not known to
be arc-transitive, and every one of them now has an entry: `le_autCount_foldedCube`
(`2ⁿ ≤ |Aut|`), `le_autCount_triangular`, `le_autCount_johnson`, `le_autCount_rook`,
`le_autCount_prism`, `le_autCount_cocktailParty`, `le_autCount_crown`, `le_autCount_paley`,
`le_autCount_circulant` (for *every* connection set), `le_autCount_completeMultipartite_replicate`
and the two line graphs `le_autCount_lineGraph_complete` and `le_autCount_lineGraph_cycle`, whose
vertex sets are the edge sets of `Kₙ` and `Cₙ`. Between these and the arc-transitive `2E` bounds
the `autCount` column is no longer empty for anything in the library that is transitive at all.

Two general degree bounds bracket the domination number of a regular graph:
`V_le_domNum_mul_maxDeg_add_one` (`|V| ≤ γ · (Δ + 1)`, since a chosen vertex dominates its closed
neighbourhood and no more) and `domNum_add_maxDeg_le_V` (`γ + Δ ≤ |V|`). Feeding in the two
regularity facts that had no domination entry yet gives `le_domNum_prism` (`n ≤ 2γ` for the cubic
circular ladder `Cₙ □ K₂`) with `domNum_prism_le` above it, and `le_domNum_foldedCube`
(`2ⁿ⁺² ≤ γ · (n + 4)`) with `domNum_foldedCube_le`. Neither pair pins the value down, but they
are the first entries in those two cells.

The *negative* half of the transitivity table gets the same treatment.
`not_isVertexTransitive_of_minDeg_ne_maxDeg` — a vertex-transitive graph is regular — already
ruled out `path`, `star`, `wheel`, `fan`, `book`, `ladder` and `grotzsch`; the missing entries
were the families whose degree sequence is obviously non-constant but had never been checked.
`not_isVertexTransitive_friendship` (hub degree `2n` against rim degree `2`),
`not_isVertexTransitive_tadpole` (`1` against `3`), `not_isVertexTransitive_lollipop` (`1`
against `m + 2`) and `not_isVertexTransitive_doubleStar` (`1` against `max m n + 1`) close them,
each one a two-line degree comparison. The interesting one is
`not_isVertexTransitive_mycielskian`: **the Mycielskian of a `k`-regular graph is never
vertex-transitive once `k ≥ 2`.** The shadow of a vertex keeps degree `k` while the original
vertices double to `2k` and the apex reaches all `|V|` shadows, so `δ(M(G)) = k + 1` (using
`k + 1 ≤ |V|`) but `Δ(M(G)) ≥ 2k ≥ k + 2`. `not_isVertexTransitive_mycielskian_cycle` specialises
it to the whole Mycielski tower over cycles, of which the Grötzsch graph is the first step.

Arc-transitivity is the stronger property, so each of those is also a negative arc-transitivity
entry — but only after the implication is available on the quotient.
`IsArcTransitive.isVertexTransitive` lifts `CGraph.isVertexTransitive_of_isArcTransitive` through
`Quotient.inductionOn`, and in doing so trades the pointwise hypothesis "no isolated vertices"
for the single invariant inequality `0 < δ`: given `u` and `v`, pick neighbours `u'` and `v'` and
carry the arc `u → u'` to `v → v'`. Its contrapositive
`not_isArcTransitive_of_not_isVertexTransitive` then fills the column in one pass —
`not_isArcTransitive_{path, star, wheel, fan, book, ladder, friendship, tadpole, lollipop,
doubleStar, grotzsch}` — each proved by evaluating the minimum degree and quoting the
vertex-transitivity failure. Together with `not_isArcTransitive_of_autCount_lt` these are the
only ways the library can currently refute arc-transitivity, and the degree route is by far the
cheaper of the two.

That closes the transitivity column for the cone-shaped families, which leaves them with an empty
*automorphism* cell: `V_le_autCount_of_isVertexTransitive` is the library's only general lower
bound on `|Aut G|`, and it needs exactly the property those families lack. The way in is
`autCount_mul_le_autCount_join`, `|Aut G| · |Aut H| ≤ |Aut (G ∇g H)|`, which holds because the two
sides of a join may be permuted independently. Every cone in the library is already known to be a
join — `bipartite_eq_join`, `star_eq_bipartite`, `wheel_eq_join`, `book_eq_join`, `fan_eq_join`
and `friendship_eq_join_compl_cocktailParty` — so one bound opens five cells at once:
`factorial_mul_factorial_le_autCount_bipartite` (`m! · n!`), `factorial_le_autCount_star` (`n!`,
the rays permute freely), `two_mul_factorial_le_autCount_book` (`2 · n!`, the pages permute and
the spine flips), `le_autCount_wheel` (`2(n + 3)`, the rim's dihedral symmetry, quoting
`two_mul_le_autCount_cycle`), `le_autCount_friendship` (`2(n + 1)`, via `autCount_compl` and the
cocktail-party bound) and `autCount_path_le_autCount_fan`, which is only relative to the path
because the path's own automorphism count is still unproved.

The Grötzsch graph's independence number is now bracketed rather than open. Its eleven vertices
are five shadows, five rim vertices and an apex; the shadows are pairwise non-adjacent, so
`V_le_indepNum_mycielskian` applied to `C₅` gives `five_le_indepNum_grotzsch`, and every colour
class of a clique cover is an independent set's worth of cliques, so `indepNum_grotzsch_le` reads
`α ≤ θ = 6` off `cliqueCoverNum_grotzsch`. Feeding both through `τ + α = |V|` gives
`five_le_coverNum_grotzsch` and `coverNum_grotzsch_le`. Ruling out `α = 6` is the one remaining
step, and it is still out for automated proof.

Two whole rows get their first entries from general inequalities that had never been specialised.
For the line graph, `indepNum_lineGraph` says an independent set of `L(G)` *is* a matching of `G`,
so `matchNum_le_cliqueCoverNum_lineGraph` (`ν(G) ≤ θ(L(G))`) and `two_mul_matchNum_lineGraph_le_E`
(`2ν(L(G)) ≤ |E(G)|`) are immediate, and `E_le_domNum_lineGraph_mul` combines `V_lineGraph` with
`maxDeg_lineGraph_le` to give `|E| ≤ γ(L(G)) · 2Δ(G)`. For the circulant, `maxDeg_circulant` turns
an edge count into a degree, after which `le_domNum_circulant` (`n ≤ γ(k + 1)`),
`domNum_circulant_le` (`γ + k ≤ n`), `chromNum_circulant_le` (`χ ≤ k + 1`),
`le_cliqueCoverNum_mul_cliqueNum_circulant` and `two_mul_matchNum_le_circulant` all follow. Since
`radius_circulant` already identifies the radius with the diameter, the circulant row is now empty
only in its girth and connectivity cells.

Finally, distance. `radius_eq_one_iff_domNum_eq_one` says a graph has radius one exactly when one
vertex dominates it, so the domination *lower* bounds proved above are also eccentricity lower
bounds: `two_le_radius_tadpole` and `two_le_radius_lollipop` rule out `γ = 1` by arithmetic and
then use `radius_pos` to conclude `r ≥ 2`, with `two_le_diameter_tadpole` and
`two_le_diameter_lollipop` following through `radius_le_diameter`. These are the first entries in
the distance cells of those two families. In the same spirit `not_isTree_thetaGraph` compares
`V_thetaGraph` with `E_thetaGraph`: a theta graph on two or more internally disjoint paths has
`|V| = 2 + Σxs` against `|E| = Σxs + |xs|`, so it has at least as many edges as vertices and the
edge-counting cycle detector applies.

The join bound also recurses. `completeMultipartite_cons` peels the first part off as a join with
an empty graph, so `factorial_mul_autCount_le_autCount_completeMultipartite_cons` reads
`d! · |Aut(completeMultipartite ds)| ≤ |Aut(completeMultipartite (d :: ds))|` — each part of size
`d` contributes a factor of `d!`. Feeding a balanced list into it, via `turan_of_dvd`, gives
`le_autCount_turan` for the divisible case; that particular bound is no better than the transitive
one, but the recursion is what the unbalanced parts will eventually need.

The `Δ ≤ χ' ≤ 2Δ − 1` sandwich has now been applied everywhere the maximum degree is known:
`le_edgeChromNum_tadpole` and `edgeChromNum_tadpole_le` bracket the tadpole between `3` and `5`,
`le_edgeChromNum_lollipop` and `edgeChromNum_lollipop_le` bracket the lollipop between `m + 2` and
`2m + 3`, `edgeChromNum_doubleStar_le` supplies the upper half of the double star's bracket, and
`le_edgeChromNum_triangular`, `le_edgeChromNum_johnson` and `le_edgeChromNum_paley` give
unconditional lower bounds where the earlier parity arguments needed `|V|` to be odd. Similarly
`|V| ≤ θ ω` has been applied everywhere the clique number is known: `le_cliqueCoverNum_turan`
(`n ≤ θ r`), `le_cliqueCoverNum_crown` (triangle-free, so `θ ≥ n + 2`),
`le_cliqueCoverNum_johnson_two` and `le_cliqueCoverNum_triangular_of_choose`. The Paley graph's
domination cell opens the same way, from `maxDeg_paley`: `le_domNum_paley` is `q ≤ γ((q − 1)/2 + 1)`
and `domNum_paley_le` is `γ + (q − 1)/2 ≤ q`. Finally `three_le_girth_cyclePendant` records that a
cycle with pendant paths attached is not acyclic, hence has girth at least three — the first entry
in that family's girth cell.

The matching-number column has two ways in. Where the independence number is known exactly,
`ν ≤ τ ≤ 2ν` together with `τ + α = |V|` brackets the matching number between a half and a whole
of the vertex cover: `matchNum_triangular_le` and `le_matchNum_triangular` bracket the triangular
graph around `C(n, 2) − ⌊n/2⌋`, and `matchNum_johnson_two_le`, `le_matchNum_johnson_two`,
`matchNum_kneser_two_le` and `le_matchNum_kneser_two` do the same for `johnson n 2` and
`kneser (n + 4) 2`. Where it is not known, the edge-colouring bound `|E| ≤ χ' ν` runs the other
way: a proper edge colouring splits `E` into `χ'` matchings, so one of them has at least `|E|/χ'`
edges. Combined with the brackets above this gives `le_matchNum_tadpole` (`|E| = m + k + 4` and
`χ' ≤ 5`, so `ν ≥ (m + k + 4)/5`) and `le_matchNum_lollipop`. `coverNum_lollipop_le` completes the
lollipop's covering cell from the chromatic bound on its independence number.

Three more domination brackets close out that column: `le_domNum_hypercube` and
`domNum_hypercube_le` — the first of these, `2ⁿ ≤ γ(n + 1)`, is exactly the sphere-covering bound
for binary codes of covering radius one — together with `le_domNum_kneser`, `domNum_kneser_le`,
`le_domNum_johnson`, `domNum_johnson_le`, `le_domNum_ladder` and `domNum_ladder_le`. Since
`ladder n` is literally `Pₙ □ K₂`, the product bound on automorphism counts also gives
`two_mul_autCount_path_le_autCount_ladder`, and `maxDeg_lineGraph` — the line graph of a
`k`-regular graph is `(2k − 2)`-regular — feeds the usual sandwich to give
`le_edgeChromNum_lineGraph` and `edgeChromNum_lineGraph_le`.

The triangle-count column falls out in one pass. `cliqueCount G 3` counts the triangles, and it
vanishes as soon as the clique number is at most two, which for a bipartite graph is automatic:
`cliqueCount_three_eq_zero_of_isBipartite` turns every bipartiteness proof in the library into a
triangle count. That gives `cliqueCount_path`, `cliqueCount_ladder`, `cliqueCount_spider`,
`cliqueCount_doubleStar`, `cliqueCount_crown`, `cliqueCount_turan_two`, and — with the parity
side conditions those families carry — `cliqueCount_cyclePendant_even`,
`cliqueCount_thetaGraph_even`, `cliqueCount_thetaGraph_odd` and `cliqueCount_circulant`. The
non-bipartite triangle-free graphs go through `cliqueNum` instead: `cliqueCount_tadpole` (the
tadpole's cycle has length at least four), `cliqueCount_grotzsch`, `cliqueCount_foldedCube`, and
`cliqueCount_mycielskian`, which is the whole point of Mycielski's construction — the
Mycielskian of a triangle-free graph is triangle-free while its chromatic number goes up by one.

The same bipartiteness proofs settle the *negative* half of the self-complementarity column. A
self-complementary graph on five or more vertices needs at least three colours, so it is never
bipartite; `not_isSelfComplementary_of_isBipartite` packages that, and applying it gives
`not_isSelfComplementary_path`, `not_isSelfComplementary_star`, `not_isSelfComplementary_ladder`,
`not_isSelfComplementary_crown`, `not_isSelfComplementary_doubleStar`,
`not_isSelfComplementary_spider`, `not_isSelfComplementary_cycle_even` and
`not_isSelfComplementary_tadpole_even`. The vertex-count thresholds in those statements are not
slack: `path 4` and the one-vertex graph are bipartite *and* self-complementary, and they are the
only two that are.

Bipartiteness is only the first of four cheap obstructions to self-complementarity, and the other
three are packaged as `not_isSelfComplementary_of_V_mod_four` (a self-complementary graph has
half of all `C(V, 2)` possible edges, so `C(V, 2)` is even and `V` is `0` or `1` mod four),
`not_isSelfComplementary_of_cliqueNum_ne_indepNum` (complementation swaps cliques and independent
sets, so `ω = α`) and `not_isSelfComplementary_of_not_isConnected` — with
`not_isSelfComplementary_of_two_mul_E_ne` for the raw edge count. Between them they settle almost
every remaining family: `not_isSelfComplementary_disjUnion` and `not_isSelfComplementary_grotzsch`
(eleven vertices), `not_isSelfComplementary_cycle_three_mod_four`,
`not_isSelfComplementary_prism_odd` and `not_isSelfComplementary_prism_even`,
`not_isSelfComplementary_friendship_odd` and `not_isSelfComplementary_friendship`,
`not_isSelfComplementary_cocktailParty`, `not_isSelfComplementary_book`,
`not_isSelfComplementary_wheel`, `not_isSelfComplementary_fan`,
`not_isSelfComplementary_triangular`, `not_isSelfComplementary_johnson_two`,
`not_isSelfComplementary_kneser_two`, `not_isSelfComplementary_rook` for a non-square board, and
`not_isSelfComplementary_mycielskian` for the Mycielskian of any triangle-free graph on at least
three vertices. The thresholds are again sharp where the small cases really are
self-complementary: `cycle 5` and `path 4` are, and so is `rook 1 1`.

The theta graph and the spider are the two families whose rows are still mostly empty, because
almost everything about them runs through a maximum degree the library cannot yet compute. Their
two-parameter special cases are an exception: `thetaGraph [a, b]` is the cycle on `a + b + 2`
vertices and `spider [a, b]` is the path on `a + b + 1`, so every cycle and path invariant
transfers. That gives `maxDeg_thetaGraph_pair`, `minDeg_thetaGraph_pair`,
`domNum_thetaGraph_pair`, `matchNum_thetaGraph_pair`, `coverNum_thetaGraph_pair`,
`radius_thetaGraph_pair`, `diameter_thetaGraph_pair`, `isConnected_thetaGraph_pair` and
`numComponents_thetaGraph_pair`, and on the spider side `matchNum_spider_pair`,
`coverNum_spider_pair`, `cliqueCoverNum_spider_pair`, `domNum_spider_pair`, `radius_spider_pair`,
`diameter_spider_pair`, `maxDeg_spider_pair`, `minDeg_spider_pair` and
`edgeChromNum_spider_pair`. The same trick through `cyclePendant_singleton_one` — a cycle with a
single pendant vertex is a tadpole — gives `maxDeg_cyclePendant_singleton_one` and
`minDeg_cyclePendant_singleton_one`.

The colouring and symmetry cells of those two special cases follow the same route.
`cliqueNum_thetaGraph_pair`, `indepNum_thetaGraph_pair`, `chromNum_thetaGraph_pair_even`,
`chromNum_thetaGraph_pair_odd`, `edgeChromNum_thetaGraph_pair_even` and
`edgeChromNum_thetaGraph_pair_odd` split on the parity of `a + b` exactly as the cycle does, and
`cliqueNum_spider_pair`, `chromNum_spider_pair`, `indepNum_spider_pair` and `girth_spider_pair`
come straight off the path. Since a two-path theta graph *is* a cycle it is arc-transitive —
`isVertexTransitive_thetaGraph_pair`, `isArcTransitive_thetaGraph_pair` and the dihedral bound
`two_mul_le_autCount_thetaGraph_pair` — whereas a two-legged spider is a path and so is not even
vertex-transitive: `not_isVertexTransitive_spider_pair`, `not_isArcTransitive_spider_pair`, and
likewise `not_isVertexTransitive_cyclePendant_singleton_one`,
`not_isArcTransitive_cyclePendant_singleton_one`, `not_isVertexTransitive_bipartite` and
`not_isArcTransitive_bipartite` for an unbalanced complete bipartite graph.

Arc transitivity is worth more than vertex transitivity in the automorphism column: it gives
`2|E| ≤ |Aut|` rather than `|V| ≤ |Aut|`. Cashing that in for the three arc-transitive families
whose edge count is known gives `two_mul_E_le_autCount_hypercube` (`n · 2ⁿ`),
`two_mul_E_le_autCount_kneser` (`C(n, k) · C(n − k, k)`) and
`two_mul_E_le_autCount_bipartite_self` (`2n²`), each far beyond what the vertex count alone
would give. `le_autCount_thetaGraph_replicate_one` covers the remaining degenerate theta graph,
the one whose paths all have length one and which is therefore `K₂,ₙ`.

That last identity is the general one: `thetaGraph_of_all_one` says that a theta graph whose
paths all have length one is `K₂,ₙ`, and `spider_of_all_one` says that a spider whose legs all
have length one is a star. Both take a hypothesis `∀ k ∈ ks, k = 1` rather than a literal
`List.replicate`, so they apply to any such list, and the whole star row transfers across:
`maxDeg_spider_of_all_one`, `minDeg_spider_of_all_one`, `matchNum_spider_of_all_one`,
`domNum_spider_of_all_one`, `coverNum_spider_of_all_one`, `indepNum_spider_of_all_one`,
`cliqueCoverNum_spider_of_all_one`, `edgeChromNum_spider_of_all_one`,
`radius_spider_of_all_one`, `diameter_spider_of_all_one` and
`factorial_le_autCount_spider_of_all_one`, the last of which says the legs can be permuted
arbitrarily. The bipartite row transfers the same way, with `max 2 ks.length` and
`min 2 ks.length` in place of the star's `1`: `maxDeg_thetaGraph_of_all_one`,
`minDeg_thetaGraph_of_all_one`, `matchNum_thetaGraph_of_all_one`,
`indepNum_thetaGraph_of_all_one`, `coverNum_thetaGraph_of_all_one`,
`cliqueCoverNum_thetaGraph_of_all_one`, `edgeChromNum_thetaGraph_of_all_one`,
`domNum_thetaGraph_of_all_one`, `diameter_thetaGraph_of_all_one`,
`isConnected_thetaGraph_of_all_one` and `numComponents_thetaGraph_of_all_one`. The side
conditions are exactly the ones the star and bipartite lemmas need: a non-empty list for the
degrees and the radius, and at least two entries for the diameter and the domination number.

The `cyclePendant` family — a cycle with pendant vertices hung off its first few positions — is
still known mostly through inequalities, but its two degenerate cases collapse onto families that
are known exactly. `cyclePendant_replicate_zero` says that hanging *no* pendant vertices anywhere
leaves the cycle alone, and it carries the whole cycle row across:
`maxDeg_cyclePendant_replicate_zero`, `matchNum_cyclePendant_replicate_zero`,
`indepNum_cyclePendant_replicate_zero`, `coverNum_cyclePendant_replicate_zero`,
`cliqueNum_cyclePendant_replicate_zero`, `cliqueCoverNum_cyclePendant_replicate_zero`,
`domNum_cyclePendant_replicate_zero`, `radius_cyclePendant_replicate_zero`,
`diameter_cyclePendant_replicate_zero`, `degSequence_cyclePendant_replicate_zero`,
`isRegularWith_cyclePendant_replicate_zero`, the parity-split colourings
`chromNum_cyclePendant_replicate_zero_odd`, `edgeChromNum_cyclePendant_replicate_zero_even` and
`edgeChromNum_cyclePendant_replicate_zero_odd`, and on the symmetry side
`isVertexTransitive_cyclePendant_replicate_zero`, `isArcTransitive_cyclePendant_replicate_zero`
and the dihedral bound `two_mul_le_autCount_cyclePendant_replicate_zero`.

At the other extreme `cyclePendant_one` puts all `k` pendant vertices on the single vertex of a
one-vertex cycle, which is a star. That gives `maxDeg_cyclePendant_one`,
`minDeg_cyclePendant_one`, `matchNum_cyclePendant_one`, `domNum_cyclePendant_one`,
`indepNum_cyclePendant_one`, `coverNum_cyclePendant_one`, `cliqueCoverNum_cyclePendant_one`,
`edgeChromNum_cyclePendant_one`, `girth_cyclePendant_one`, `radius_cyclePendant_one`,
`diameter_cyclePendant_one`, `chromNum_cyclePendant_one`, `cliqueNum_cyclePendant_one`,
`isTree_cyclePendant_one`, `isBipartite_cyclePendant_one` and
`factorial_le_autCount_cyclePendant_one`, together with the two structural identities
`lineGraph_cyclePendant_one` (the line graph of a star is complete) and `compl_cyclePendant_one`,
and the failures of symmetry `not_isVertexTransitive_cyclePendant_one` and
`not_isArcTransitive_cyclePendant_one` once there are at least two pendant vertices.

The tadpole and lollipop rows have the same shape of gap: outside the degrees and the chromatic
number they are known only through inequalities, because a cycle or clique with a tail attached
resists the counting arguments that work on the pure families. Their `k = 0` columns do not,
since `tadpole_zero` is a cycle and `lollipop_zero` is a complete graph. That gives
`maxDeg_tadpole_zero`, `minDeg_tadpole_zero`, `matchNum_tadpole_zero`, `indepNum_tadpole_zero`,
`coverNum_tadpole_zero`, `cliqueCoverNum_tadpole_zero`, `domNum_tadpole_zero`,
`radius_tadpole_zero`, `diameter_tadpole_zero`, `degSequence_tadpole_zero`,
`isRegularWith_tadpole_zero`, the parity pair `edgeChromNum_tadpole_zero_even` and
`edgeChromNum_tadpole_zero_odd`, and the symmetry statements
`isVertexTransitive_tadpole_zero`, `isArcTransitive_tadpole_zero` and
`two_mul_le_autCount_tadpole_zero` — each of which fails as soon as the tail is non-empty, which
is exactly why the general row is so much weaker.

The lollipop side is stronger still, because the complete graph has an exact automorphism count
rather than a bound: `autCount_lollipop_zero` is `m!` on the nose. Alongside it are
`maxDeg_lollipop_zero`, `minDeg_lollipop_zero`, `matchNum_lollipop_zero`,
`indepNum_lollipop_zero`, `coverNum_lollipop_zero`, `cliqueCoverNum_lollipop_zero`,
`domNum_lollipop_zero`, `radius_lollipop_zero`, `diameter_lollipop_zero`,
`edgeChromNum_lollipop_zero` (with its parity `if`), `degSequence_lollipop_zero`,
`isRegularWith_lollipop_zero`, `isVertexTransitive_lollipop_zero`,
`isArcTransitive_lollipop_zero`, and the two structural identities `compl_lollipop_zero` and
`lineGraph_lollipop_zero`, the latter landing on the Johnson graph `J(m, 2)`.

The last two degenerate columns are the theta graph with a single path and the spider with a
single leg, both of which are paths: `thetaGraph [k]` is `Pₖ₊₂` and `spider [k]` is `P₁₊ₖ`. The
path row transfers wholesale, and it is worth more here than elsewhere because the maximum degree
is precisely the invariant that blocks the general theta and spider rows. On the theta side:
`maxDeg_thetaGraph_singleton`, `minDeg_thetaGraph_singleton`, `matchNum_thetaGraph_singleton`,
`indepNum_thetaGraph_singleton`, `coverNum_thetaGraph_singleton`,
`cliqueCoverNum_thetaGraph_singleton`, `cliqueNum_thetaGraph_singleton`,
`chromNum_thetaGraph_singleton`, `domNum_thetaGraph_singleton`, `radius_thetaGraph_singleton`,
`diameter_thetaGraph_singleton`, `edgeChromNum_thetaGraph_singleton`,
`girth_thetaGraph_singleton`, `isAcyclic_thetaGraph_singleton`, `isTree_thetaGraph_singleton`
(which is consistent with `not_isTree_thetaGraph`, since that one needs at least two paths),
`isConnected_thetaGraph_singleton`, `numComponents_thetaGraph_singleton`,
`lineGraph_thetaGraph_singleton`, `not_isVertexTransitive_thetaGraph_singleton`,
`not_isArcTransitive_thetaGraph_singleton` and `not_isSelfComplementary_thetaGraph_singleton`.
On the spider side the same list appears as `maxDeg_spider_singleton`,
`matchNum_spider_singleton`, `indepNum_spider_singleton`, `coverNum_spider_singleton`,
`cliqueCoverNum_spider_singleton`, `domNum_spider_singleton`, `radius_spider_singleton`,
`diameter_spider_singleton`, `edgeChromNum_spider_singleton`, `lineGraph_spider_singleton`,
`not_isVertexTransitive_spider_singleton` and `not_isArcTransitive_spider_singleton`, the rest of
the row already being covered by the general spider lemmas.

Two more families have a degenerate parameter that lands on something known exactly. A circulant
with the single connection `[1]` is a cycle, which turns the circulant row from a list of bounds
into exact values: `matchNum_circulant_one`, `indepNum_circulant_one`, `coverNum_circulant_one`,
`cliqueNum_circulant_one`, `cliqueCoverNum_circulant_one`, `domNum_circulant_one`,
`diameter_circulant_one`, `radius_circulant_one`, the parity splits
`chromNum_circulant_one_even`, `chromNum_circulant_one_odd`,
`edgeChromNum_circulant_one_even` and `edgeChromNum_circulant_one_odd`, together with
`isRegularWith_circulant_one`, `isConnected_circulant_one`, `numComponents_circulant_one`,
`not_isTree_circulant_one`, and on the symmetry side `isArcTransitive_circulant_one` — stronger
than the general `isVertexTransitive_circulant` — with the dihedral bound
`two_mul_le_autCount_circulant_one`.

`kneser_one` does the same job with the complete graph on the other side. The Kneser row is one
of the better developed ones, but almost all of it is stated for `k = 2`; at `k = 1` the complete
graph supplies `matchNum_kneser_one`, `indepNum_kneser_one`, `coverNum_kneser_one`,
`cliqueNum_kneser_one`, `chromNum_kneser_one`, `cliqueCoverNum_kneser_one`, `domNum_kneser_one`,
`radius_kneser_one`, `diameter_kneser_one`, `edgeChromNum_kneser_one`, `girth_kneser_one`,
`not_isSelfComplementary_kneser_one`, the two structural identities `compl_kneser_one` and
`lineGraph_kneser_one`, and — in place of the general bound `le_autCount_kneser` — the exact
count `autCount_kneser_one = n!`.

The Johnson row has the same shape as the Kneser one — well developed at `k = 2`, thin
elsewhere — and `johnson_one` fills its other end: `matchNum_johnson_one`,
`indepNum_johnson_one`, `cliqueNum_johnson_one`, `chromNum_johnson_one`,
`cliqueCoverNum_johnson_one`, `domNum_johnson_one`, `edgeChromNum_johnson_one`,
`autCount_johnson_one`, `isArcTransitive_johnson_one`, `compl_johnson_one`,
`lineGraph_johnson_one` and `not_isSelfComplementary_johnson_one`. The line graph identity is
the amusing one: the line graph of `J(n, 1)` is `J(n, 2)`.

The circulant with an empty connection list is the edgeless graph, which is the cheapest column
of all but still one the general circulant lemmas do not reach, since most of them assume a
non-empty connection set. It gives `maxDeg_circulant_nil`, `minDeg_circulant_nil`,
`matchNum_circulant_nil`, `indepNum_circulant_nil`, `coverNum_circulant_nil`,
`cliqueNum_circulant_nil`, `cliqueCoverNum_circulant_nil`, `chromNum_circulant_nil`,
`edgeChromNum_circulant_nil`, `domNum_circulant_nil`, `radius_circulant_nil`,
`diameter_circulant_nil`, `girth_circulant_nil`, `numComponents_circulant_nil`,
`degSequence_circulant_nil`, `autCount_circulant_nil`, `isRegularWith_circulant_nil`,
`isAcyclic_circulant_nil`, `isBipartite_circulant_nil`, `isArcTransitive_circulant_nil`,
`not_isConnected_circulant_nil`, `not_isSelfComplementary_circulant_nil`,
`compl_circulant_nil` and `lineGraph_circulant_nil`.

The other end of the tadpole and lollipop rows is the one-vertex head. Every general entry in
those two rows assumes `m ≥ 3` — the arguments need a genuine cycle or a genuine clique — so
`m = 1`, where both graphs degenerate to a path, is untouched by them. It supplies
`maxDeg_tadpole_one`, `minDeg_tadpole_one`, `matchNum_tadpole_one`, `indepNum_tadpole_one`,
`coverNum_tadpole_one`, `cliqueCoverNum_tadpole_one`, `cliqueNum_tadpole_one`,
`chromNum_tadpole_one`, `domNum_tadpole_one`, `radius_tadpole_one`, `diameter_tadpole_one`,
`edgeChromNum_tadpole_one`, `girth_tadpole_one`, `isAcyclic_tadpole_one`, `isTree_tadpole_one`,
`isConnected_tadpole_one`, `numComponents_tadpole_one` and `lineGraph_tadpole_one`, with the
identical list for the lollipop: `maxDeg_lollipop_one`, `minDeg_lollipop_one`,
`matchNum_lollipop_one`, `indepNum_lollipop_one`, `coverNum_lollipop_one`,
`cliqueCoverNum_lollipop_one`, `cliqueNum_lollipop_one`, `chromNum_lollipop_one`,
`domNum_lollipop_one`, `radius_lollipop_one`, `diameter_lollipop_one`,
`edgeChromNum_lollipop_one`, `girth_lollipop_one`, `isAcyclic_lollipop_one`,
`isTree_lollipop_one`, `isConnected_lollipop_one`, `numComponents_lollipop_one` and
`lineGraph_lollipop_one`. Note the reversal of sign against the general row: a tadpole is never
acyclic and never a tree once its cycle is real, but at `m = 1` it is both.

One more Kneser column comes for free, and it is a whole half-plane rather than a single value.
Two `k`-subsets of an `n`-set cannot be disjoint once `n < 2 * k`, so `kneser_eq_empty` says the
graph is edgeless on `C(n, k)` vertices there, and every Kneser lemma in the file assumes the
opposite inequality. The edgeless row transfers under that hypothesis as `maxDeg_kneser_of_lt`,
`minDeg_kneser_of_lt`, `matchNum_kneser_of_lt`, `coverNum_kneser_of_lt`, `indepNum_kneser_of_lt`,
`cliqueNum_kneser_of_lt`, `cliqueCoverNum_kneser_of_lt`, `domNum_kneser_of_lt`,
`numComponents_kneser_of_lt`, `radius_kneser_of_lt`, `diameter_kneser_of_lt`,
`girth_kneser_of_lt`, `edgeChromNum_kneser_of_lt`, `degSequence_kneser_of_lt`,
`autCount_kneser_of_lt` (which is `C(n, k)!`, the full symmetric group),
`isRegularWith_kneser_of_lt`, `isAcyclic_kneser_of_lt`, `isBipartite_kneser_of_lt`,
`isArcTransitive_kneser_of_lt`, `compl_kneser_of_lt` and `lineGraph_kneser_of_lt`. Only
`chromNum_kneser_of_lt` needs a second hypothesis, `k ≤ n`, to know there is a vertex at all.

Complementation gives a second axis to work along, and it is cheap in a different way: cliques
and independent sets swap, the chromatic number and the clique cover number swap, the
automorphism group is unchanged, and the degrees and edge count are determined by
`V - 1 - deg` and `C(V, 2) - E`. So every family whose four counting invariants are known also
determines them for its complement, even when that complement has no name of its own. For the
cycle that is `cliqueNum_compl_cycle`, `indepNum_compl_cycle`, `chromNum_compl_cycle`,
`cliqueCoverNum_compl_cycle_even`, `cliqueCoverNum_compl_cycle_odd`, `maxDeg_compl_cycle`,
`minDeg_compl_cycle`, `E_compl_cycle`, `isVertexTransitive_compl_cycle` and
`two_mul_le_autCount_compl_cycle`; for the path, `cliqueNum_compl_path`, `indepNum_compl_path`,
`chromNum_compl_path`, `cliqueCoverNum_compl_path`, `maxDeg_compl_path`, `minDeg_compl_path`,
`E_compl_path` and `not_isVertexTransitive_compl_path`, the last of which runs the transitivity
equivalence backwards.

The same treatment applies to the two vertex-transitive families with exact counts.
`cliqueNum_compl_hypercube`, `indepNum_compl_hypercube`, `chromNum_compl_hypercube`,
`cliqueCoverNum_compl_hypercube`, `maxDeg_compl_hypercube`, `minDeg_compl_hypercube`,
`isVertexTransitive_compl_hypercube` and `two_mul_E_le_autCount_compl_hypercube` cover the
complement of `Qₙ` — whose independence and clique numbers are the hypercube's own, swapped —
and `cliqueNum_compl_crown`, `indepNum_compl_crown`, `chromNum_compl_crown`,
`cliqueCoverNum_compl_crown`, `maxDeg_compl_crown`, `minDeg_compl_crown`, `E_compl_crown` and
`isVertexTransitive_compl_crown` do the same for the crown graph.

Three more families follow. The wheel's complement splits off its hub, so
`minDeg_compl_wheel` is `0` while `maxDeg_compl_wheel (n + 3) = n`; the rest of the row is
`cliqueNum_compl_wheel`, `indepNum_compl_wheel`, `chromNum_compl_wheel`,
`cliqueCoverNum_compl_wheel_even`, `cliqueCoverNum_compl_wheel_odd` and `E_compl_wheel`, whose
edge count needs the vertex count rewritten from `1 + (n + 3)` to `n + 4` before `omega` will
recognise the two binomial coefficients as the same atom. The ladder and the prism are both
cubic, so their complements are `(2n + 2)`- and `(2n + 3)`-regular-ish in the sense that
`maxDeg_compl_ladder`, `minDeg_compl_ladder`, `maxDeg_compl_prism` and `minDeg_compl_prism` all
come out linear in `n`, with the prism's two agreeing because the prism itself is regular.
`cliqueNum_compl_ladder`, `indepNum_compl_ladder`, `chromNum_compl_ladder`,
`cliqueCoverNum_compl_ladder`, `E_compl_ladder` and the six prism analogues — split by parity
where the prism's own row is — finish the picture, and `isVertexTransitive_compl_prism` carries
the prism's vertex transitivity across.

The list-parameterised families come last, and there the complement column is partial by
necessity: it can only say as much as the family's own row does. The tadpole and the lollipop
have full rows, so `indepNum_compl_tadpole`, `cliqueCoverNum_compl_tadpole_even`,
`cliqueCoverNum_compl_tadpole_odd`, `maxDeg_compl_tadpole`, `minDeg_compl_tadpole` and
`E_compl_tadpole` come out in closed form, as do `indepNum_compl_lollipop`,
`cliqueCoverNum_compl_lollipop`, `maxDeg_compl_lollipop`, `minDeg_compl_lollipop` and
`E_compl_lollipop` — the last of which keeps two binomial coefficients, `C(m + 1 + k, 2)` for
the vertex count and `C(m + 1, 2)` for the clique's own edges, and `omega` is content to treat
both as atoms. The lollipop's complement has minimum degree exactly `k`: the clique vertices,
which dominated the graph, become the sparse ones.

For the spider, the theta graph and the cycle with pendants, only the clique, chromatic and
minimum-degree facts are known in general, so the complement inherits exactly those:
`indepNum_compl_spider`, `cliqueCoverNum_compl_spider`, `maxDeg_compl_spider` and
`E_compl_spider` for the spider (all but the last needing `0 < legs.sum`, since the empty spider
is a single vertex), `cliqueCoverNum_compl_thetaGraph_odd`,
`cliqueCoverNum_compl_thetaGraph_even` and `E_compl_thetaGraph` for the theta graph, and
`cliqueCoverNum_compl_cyclePendant_even`, `maxDeg_compl_cyclePendant` and
`E_compl_cyclePendant` for the cycle with pendants. Each of these carries its source lemma's
hypotheses unchanged — `ks.length ≤ m + 3` so the pendants fit, the parity conditions on the
theta graph's paths — which is the honest thing for a transported statement to do.

The double star closes the tree families: `cliqueNum_compl_doubleStar`,
`indepNum_compl_doubleStar`, `chromNum_compl_doubleStar`, `cliqueCoverNum_compl_doubleStar`,
`maxDeg_compl_doubleStar`, `minDeg_compl_doubleStar` and `E_compl_doubleStar` give the whole
row, and the minimum degree of the complement is `min m n`, since `V - 1 - (max m n + 1)`
collapses to it.

The Johnson and Kneser graphs are regular, so their complements are too, and
`maxDeg_compl_johnson`, `minDeg_compl_johnson`, `maxDeg_compl_kneser` and `minDeg_compl_kneser`
agree pairwise: `C(n, k) - 1 - k(n - k)` and `C(n, k) - 1 - C(n - k, k)`. The edge counts
`E_compl_johnson` and `E_compl_kneser` cannot go through `omega`, because the subtracted term is
a product of two binomial coefficients halved and so is not linear in its atoms; they close
instead by rewriting backwards along `E_compl` and cancelling with `Nat.add_sub_cancel`.
`isVertexTransitive_compl_kneser` completes the pair with the Johnson version already on file.

The Mycielskian is the one construction whose complement row is stated for a general graph:
`indepNum_compl_mycielskian`, `cliqueCoverNum_compl_mycielskian`, `chromNum_compl_mycielskian`,
`cliqueNum_compl_mycielskian_le`, `maxDeg_compl_mycielskian`, `minDeg_compl_mycielskian` and
`E_compl_mycielskian` express everything in terms of `G`'s own invariants — for instance the
complement of `M(G)` has `2·V(G) - max (2·Δ(G)) (V(G))` for its minimum degree, and no
positivity hypothesis is needed anywhere the vertex count appears, since `M(G)` always has the
extra apex vertex. The independence number is only bounded above in the library, so its dual
`cliqueNum_compl_mycielskian_le` is an inequality too.

Its most famous instance gets exact numbers. `indepNum_compl_grotzsch`,
`chromNum_compl_grotzsch`, `cliqueCoverNum_compl_grotzsch`, `cliqueNum_compl_grotzsch_le`,
`maxDeg_compl_grotzsch`, `minDeg_compl_grotzsch` and `E_compl_grotzsch` describe the complement
of the Grötzsch graph: `11` vertices, `35` edges, degrees between `5` and `7`, chromatic number
`6` and clique cover number `4`. Finally the odd folded cubes are bipartite, so
`cliqueNum_compl_foldedCube_odd` and `cliqueCoverNum_compl_foldedCube_odd` read off `2 ^ (2m)`
and `2` from that, and `isVertexTransitive_compl_foldedCube` holds for every `n`.

Line graphs are the last general construction to get the treatment, and there the duality reads
particularly well: `cliqueNum_compl_lineGraph` says the largest clique in `L(G)ᶜ` is `G`'s
matching number, and `cliqueCoverNum_compl_lineGraph` says its clique cover number is `G`'s edge
chromatic number, both of them restatements of `indepNum_lineGraph` and `chromNum_lineGraph`
across the complement. `maxDeg_compl_lineGraph` and `minDeg_compl_lineGraph` inherit the
regularity hypothesis `degSequence G = List.replicate n k` that the line graph's own degree
lemmas need, and `E_compl_lineGraph` subtracts `∑ C(d, 2)` from `C(E(G), 2)`.

Two product families had only a colouring and a girth on file, and the Cartesian product row
fills the rest of them in. For the grid `Pₘ □ Pₙ` that is `V_grid`, `E_grid`, `cliqueNum_grid`,
`maxDeg_grid` (which is `4` once both sides have at least three vertices), `minDeg_grid`,
`isConnected_grid`, `diameter_grid = m + n` and `radius_grid`. For the torus `Cₘ □ Cₙ` it is
`V_cartesianProduct_cycle`, `E_cartesianProduct_cycle = 2mn`,
`cliqueNum_cartesianProduct_cycle`, `maxDeg_cartesianProduct_cycle`,
`minDeg_cartesianProduct_cycle` — both `4`, since the torus is quartic —
`isConnected_cartesianProduct_cycle`, `radius_cartesianProduct_cycle` and
`isVertexTransitive_cartesianProduct_cycle`, the last from the product of two vertex-transitive
factors. Neither row includes an independence number: the Cartesian product has no formula for
one, only the two bounds `indepNum_cartesianProduct_le` and `indepNum_cartesianProduct_le'`.

Two more product families come for free from the same lemmas. The cylinder `Cₘ □ Pₙ` gets
`V_cartesianProduct_cycle_path`, `E_cartesianProduct_cycle_path`,
`cliqueNum_cartesianProduct_cycle_path`, `maxDeg_cartesianProduct_cycle_path` (`4`),
`minDeg_cartesianProduct_cycle_path` (`3`, at the two boundary circles),
`isConnected_cartesianProduct_cycle_path`, `diameter_cartesianProduct_cycle_path` and
`radius_cartesianProduct_cycle_path`, joining the `girth_cartesianProduct_cycle_path` that was
already there. The king graph `Pₘ ⊠ Pₙ` — a chessboard with diagonal moves allowed — comes from
the strong product instead: `V_king`, `E_king`, `cliqueNum_king = 4` (a king, its neighbour and
the two squares completing the `2 × 2` block), `maxDeg_king = 8`, `minDeg_king = 3` at a corner,
`isConnected_king` and `girth_king = 3`.

The other two products of a pair of cycles get the same treatment.
`V_tensorProduct_cycle`, `E_tensorProduct_cycle = 2mn`, `cliqueNum_tensorProduct_cycle`,
`maxDeg_tensorProduct_cycle`, `minDeg_tensorProduct_cycle` — both `4`, the product of the two
factors' degrees rather than their sum — and `isVertexTransitive_tensorProduct_cycle` cover
`Cₘ ⊗ Cₙ`. There is deliberately no connectivity lemma there: the tensor product of two even
cycles falls apart into two components, so no unconditional statement is available. The strong
product has no such problem, and `V_strongProduct_cycle`, `E_strongProduct_cycle`,
`cliqueNum_strongProduct_cycle = 4`, `maxDeg_strongProduct_cycle`,
`minDeg_strongProduct_cycle` — both `8` — `isConnected_strongProduct_cycle`,
`girth_strongProduct_cycle = 3` and `isVertexTransitive_strongProduct_cycle` describe the
toroidal king graph.

The lexicographic product finishes the set, so all four products of a pair of cycles now have a
row: `V_lexProduct_cycle`, `E_lexProduct_cycle`, `cliqueNum_lexProduct_cycle = 4`,
`indepNum_lexProduct_cycle` (the only one of the four with an independence number, since the
lexicographic product multiplies them), `maxDeg_lexProduct_cycle` and `minDeg_lexProduct_cycle`
— both `2n + 8`, since a vertex sees both neighbouring copies whole plus two vertices in its own
— `isConnected_lexProduct_cycle`, `girth_lexProduct_cycle = 3` and
`isVertexTransitive_lexProduct_cycle`. The asymmetry in the degree, which depends on `n` but not
on `m`, is the asymmetry of the product itself.

Paths make a good second pair of factors, because they are bipartite and the two products react
to that in opposite ways. The tensor product stays bipartite —
`isBipartite_tensorProduct_path` follows from the left factor alone — so
`chromNum_tensorProduct_path = 2` and `cliqueNum_tensorProduct_path = 2`, with
`V_tensorProduct_path`, `E_tensorProduct_path = 2mn`, `maxDeg_tensorProduct_path = 4` and
`minDeg_tensorProduct_path = 1` filling in the rest. Connectivity is missing on purpose: the
tensor product of two bipartite graphs always splits into two halves.

The lexicographic product does the opposite. `not_isBipartite_lexProduct_path` holds as soon as
both factors have an edge, and in fact `cliqueNum_lexProduct_path = 4` and
`chromNum_lexProduct_path = 4`: the clique number forces the chromatic number up from below and
`chromNum_lexProduct_le` caps it at `2 · 2` from above, so the two bounds meet. The rest of the
row is `V_lexProduct_path`, `E_lexProduct_path`, `indepNum_lexProduct_path`,
`maxDeg_lexProduct_path`, `minDeg_lexProduct_path = n + 3`, `isConnected_lexProduct_path`,
`numComponents_lexProduct_path = 1` and `girth_lexProduct_path = 3`.

Complete factors are the third pair, and here the three non-Cartesian products separate cleanly
(the Cartesian one is already the rook graph). The tensor product `Kₘ ⊗ Kₙ` keeps only the
smaller clique, `cliqueNum_tensorProduct_complete = min m n`, and its degrees multiply:
`maxDeg_tensorProduct_complete` and `minDeg_tensorProduct_complete` are both `mn` on
`K₍ₘ₊₁₎ ⊗ K₍ₙ₊₁₎`. It is connected once the left factor is non-bipartite, which
`isConnected_tensorProduct_complete` and `numComponents_tensorProduct_complete` record from
`K₍ₘ₊₃₎`, and `E_tensorProduct_complete`, `girth_tensorProduct_complete = 3` and
`isVertexTransitive_tensorProduct_complete` complete the row.

The strong and lexicographic products both give back a complete graph on `mn` vertices, and the
invariants say so without needing a graph isomorphism: `cliqueNum_strongProduct_complete` and
`cliqueNum_lexProduct_complete` are `mn`, all four of `maxDeg_strongProduct_complete`,
`minDeg_strongProduct_complete`, `maxDeg_lexProduct_complete` and `minDeg_lexProduct_complete`
are `mn - 1`, and `indepNum_lexProduct_complete = 1`. The edge counts
`E_strongProduct_complete` and `E_lexProduct_complete` are left in the shape the product
formulas give them, since the two expressions are different ways of writing `C(mn, 2)`.
Connectivity, girth three and vertex transitivity round out both rows.

The join is the last binary operation with a full set of invariant lemmas, and joining two cycles
exercises all of them at once. `V_join_cycle` and `E_join_cycle` are the easy half;
`cliqueNum_join_cycle = 4` (a join adds clique numbers, and a long cycle contributes two),
`indepNum_join_cycle` and `cliqueCoverNum_join_cycle` are maxima rather than sums, and
`maxDeg_join_cycle` and `minDeg_join_cycle` are the max and the min of `n + 5` and `m + 5` — a
vertex keeps its two old neighbours and gains the whole other cycle. `isConnected_join_cycle`
and `numComponents_join_cycle` hold for any two non-empty cycles, and
`girth_join_cycle = 3` follows from the clique number alone.

The chromatic number splits on parity in both arguments, so it needs three lemmas:
`chromNum_join_cycle_even = 4`, `chromNum_join_cycle_odd = 6` and
`chromNum_join_cycle_even_odd = 5`. Finally `diameter_join_cycle = 2`: a join has diameter at
most two always, and it is exactly two as soon as one factor is missing an edge, which
`diameter_join_left` reduces to `Cₙ` having fewer than `C(n, 2)` edges.

Joining two paths gives the same shape of row with none of the parity cases, because a path is
always two-chromatic: `chromNum_join_path = 4` and `cliqueNum_join_path = 4` need no case split.
`indepNum_join_path` and `cliqueCoverNum_join_path` are the same expression, since a path's
independence number and clique cover number both count `⌈n/2⌉`. `V_join_path`, `E_join_path`,
`maxDeg_join_path`, `minDeg_join_path`, `isConnected_join_path`, `numComponents_join_path`,
`girth_join_path = 3` and `diameter_join_path = 2` finish it.

The disjoint union is the join's opposite, and a pair of cycles is the smallest interesting case
— it is the general disconnected 2-regular graph. Everything additive stays additive:
`indepNum_disjUnion_cycle`, `matchNum_disjUnion_cycle` (the same value, as a cycle has a perfect
or near-perfect matching), `cliqueCoverNum_disjUnion_cycle`, `domNum_disjUnion_cycle` and
`numComponents_disjUnion_cycle = 2`. Everything extremal is an extremum:
`cliqueNum_disjUnion_cycle = 2`, `maxDeg_disjUnion_cycle` and `minDeg_disjUnion_cycle` are both
`2`, and the chromatic number is the max, so it splits on parity again across
`chromNum_disjUnion_cycle_even = 2`, `chromNum_disjUnion_cycle_odd = 3` and
`chromNum_disjUnion_cycle_even_odd = 3`. Being disconnected,
`not_isConnected_disjUnion_cycle` holds and both `diameter_disjUnion_cycle` and
`radius_disjUnion_cycle` are zero, which is the convention the rest of the file uses for
disconnected graphs.

Two paths side by side give the same row without the parity cases, plus one the cycle version
cannot have: `isBipartite_disjUnion_path`, so `chromNum_disjUnion_path = 2` outright.
`indepNum_disjUnion_path`, `matchNum_disjUnion_path`, `cliqueCoverNum_disjUnion_path` and
`domNum_disjUnion_path` add up componentwise; `cliqueNum_disjUnion_path = 2`,
`maxDeg_disjUnion_path = 2` and `minDeg_disjUnion_path = 1` are the extrema; and
`V_disjUnion_path`, `E_disjUnion_path`, `numComponents_disjUnion_path = 2`,
`not_isConnected_disjUnion_path`, `diameter_disjUnion_path` and `radius_disjUnion_path` close it
out.

Two complete graphs side by side — the complement of a complete bipartite graph — complete the
disjoint union trio. Here the extremal invariants are the interesting ones:
`cliqueNum_disjUnion_complete` and `chromNum_disjUnion_complete` are both `max m n`, and
`maxDeg_disjUnion_complete` and `minDeg_disjUnion_complete` are the max and min of the two
degrees. The additive ones collapse to constants, since each clique contributes exactly one:
`indepNum_disjUnion_complete`, `cliqueCoverNum_disjUnion_complete` and
`domNum_disjUnion_complete` are all `2`. `E_disjUnion_complete`, `matchNum_disjUnion_complete`,
`girth_disjUnion_complete = 3` and the four disconnectedness facts finish the row.

The complement column reaches the product families too. A complement has no product structure,
so only the four invariants that complementation transports survive, but those four are exactly
the ones the product rows supply: `E_compl_grid`, `maxDeg_compl_grid`, `minDeg_compl_grid` and
`indepNum_compl_grid = 2`, and the same quartet for the torus
(`E_compl_cartesianProduct_cycle` and friends), the cylinder
(`E_compl_cartesianProduct_cycle_path` and friends) and the king graph (`E_compl_king`,
`maxDeg_compl_king`, `minDeg_compl_king`, `indepNum_compl_king = 4`). The degree bounds swap
around `n - 1`, so the complement of a 4-regular torus is `mn - 5`-regular at both ends, and the
independence number of the complement is the clique number of the original — two for the three
Cartesian products, four for the king graph.

The other three products of two cycles get the same treatment:
`E_compl_tensorProduct_cycle`, `E_compl_strongProduct_cycle` and `E_compl_lexProduct_cycle`
with their degree pairs — `mn - 5` for the tensor product, `mn - 9` for the strong product and
`mn - 2n - 9` for the lexicographic one, which is the only one of the three that is not
vertex-regular in `m` — and the independence numbers `2`, `4` and `4`. The lexicographic
product earns one extra lemma the others cannot: because it is the only product with a closed
form for its own independence number, `cliqueNum_compl_lexProduct_cycle` gives the clique number
of the complement as `⌊m/2⌋⌊n/2⌋`.

Paths behave the same way under the tensor and lexicographic products, except that a path is not
regular, so the two degree lemmas of a complement no longer agree:
`maxDeg_compl_tensorProduct_path = mn - 2` comes from the minimum degree `1` of a tensor product
of paths, while `minDeg_compl_tensorProduct_path = mn - 5` comes from its maximum degree `4`, and
the lexicographic pair `mn - n - 4` and `mn - 2n - 9` splits the same way.
`indepNum_compl_tensorProduct_path = 2` and `indepNum_compl_lexProduct_path = 4` mirror the cycle
case, and `cliqueNum_compl_lexProduct_path = ⌈m/2⌉⌈n/2⌉` holds for *all* `m` and `n`, with no
shift needed, because the independence number of a lexicographic product of paths already does.
The tensor product of two complete graphs closes the column: it is `mn`-vertex and `mn`-regular
minus the diagonal, so `maxDeg_compl_tensorProduct_complete` and
`minDeg_compl_tensorProduct_complete` agree at `(m+1)(n+1) - 1 - mn`, and
`indepNum_compl_tensorProduct_complete = min m n` is the clique number of the original.

Complementation swaps the two binary operations — the complement of a disjoint union is a join of
complements and vice versa — so the last five complement rows are the disjoint unions and joins of
the named families, with the same five lemmas each. The unions give
`E_compl_disjUnion_cycle`, `maxDeg_compl_disjUnion_cycle = minDeg_compl_disjUnion_cycle = m+n+3`
(a `2`-regular union complements to an `(m+n+3)`-regular graph), `indepNum_compl_disjUnion_cycle
= 2` and `cliqueNum_compl_disjUnion_cycle = ⌊m/2⌋ + ⌊n/2⌋`; the path and complete-graph unions
follow suit, with the complete case keeping its `min`/`max` shape in `m + n + 1 - min m n` and
`m + n + 1 - max m n`. The joins are the prettiest of the batch, because the `min`/`max` in a
join's degrees cancels against the `V - 1 -` of a complement exactly:
`maxDeg_compl_join_cycle = max m n` and `minDeg_compl_join_cycle = min m n`, and the same two for
paths — the complement of a join of two `(m+3)`- and `(n+3)`-vertex graphs forgets everything but
the two sizes. `indepNum_compl_join_cycle = indepNum_compl_join_path = 4`, and the clique numbers
of those complements are the independence numbers of the joins, `max ⌈m/2⌉ ⌈n/2⌉`.

The folded cube row is new, and it is nearly complete. `foldedCube n` is `Qₙ` with every
antipodal pair joined, so `foldedCube_adj` says `x` and `y` are adjacent exactly when they differ
in one coordinate or in all `n` of them. Counting neighbours gives
`isRegularWith_foldedCube : (foldedCube (n + 2)).IsRegularWith (n + 3)` — the `n + 2` is needed
because for `n = 1` the antipodal edge *is* the coordinate edge — and `minDeg`, `maxDeg` and
`2E = 2ⁿ⁺²(n + 3)` all follow from regularity. The girth is the interesting one: a triangle would
need three pairwise Hamming distances each equal to `1` or `n`, and every combination is
impossible once `n ≥ 3`. All ones is a triangle in the hypercube, which is bipartite; exactly one
`n` dies on the triangle inequality, since the other two distances sum to at most `2 < n`, or on
a `n - 1 = 1` count; and two or more `n`s force two of the three vertices to coincide. With the
coordinate square `00…, 10…, 11…, 01…` on the other side, `girth_foldedCube = 4`, and
`cliqueNum_foldedCube = 2` and `¬IsAcyclic` fall out of it. For odd `n` the antipodal map reverses
parity, so the graph stays bipartite; being connected and regular it then has a perfect matching,
which gives `chromNum = 2` and `indepNum = matchNum = 2ⁿ⁻¹`. The metric entries came last and are
the longest proof in the section: `diameter_foldedCube (n + 1) = (n + 2) / 2`. Upwards, a walk of
Hamming length `d` gets you from `x` to `y`, and so does one antipodal step followed by `n - d`
coordinate steps, so the distance is at most `min d (1 + (n - d))`, which never exceeds `⌈n/2⌉`.
Downwards needs an actual pair at that distance, and a parity audit to certify it: every walk is
recorded as a vector `fc : Fin n → ℕ` of per-coordinate flip counts together with a count `a` of
antipodal steps, an induction on the walk shows `(fc i + a) % 2` is `1` exactly on the coordinates
where the endpoints differ, and `length = Σ fc + a`. For `x = 000…` and `y = 11…100…` with `⌈n/2⌉`
ones, an even `a` forces `⌈n/2⌉` odd flip counts and an odd `a` forces `n - ⌈n/2⌉` of them, and
both bounds are at least `⌈n/2⌉`. The radius is then free, since the folded cube is
vertex-transitive.

The complement column closes the section. `indepNum_compl_foldedCube` is `2` because the folded
cube's clique number is, `maxDeg_compl_foldedCube` and `minDeg_compl_foldedCube` are both
`2ⁿ⁺² - 1 - (n + 3)` because the folded cube is regular, and `E_compl_foldedCube` is
`C(2ⁿ⁺², 2) - 2ⁿ⁺¹(n + 3)`. That last one cannot be finished by `omega` — the subtracted term is
a product of a power of two and a linear factor — so it rewrites backwards along `E_compl` and
cancels instead.

## Enumeration

The first real application. `Enum/All.lean` produces, for each `n`, a list holding **exactly one**
graph from every isomorphism class on `n` vertices; `Enum/Conn.lean` does the same for the
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

## Names for the small graphs

`NamedSmallGraphs.lean` gives every connected graph on at most six vertices a name — 1, 1, 2, 6,
21 and 112 of them, 143 in all. Customary names where they exist (`claw`, `paw`, `bull`,
`cricket`, `net`, `house`, `gem`, `dart`, `kite`, `domino`, `fish`, `prism3`, `octahedron`,
`sun3`, …), and constructive ones otherwise, along two conventions: `coX` is the complement of `X`
(used when `X` is connected), and `K6MinusX` is `K₆` minus the edges of `X` (used when the graph
has a universal vertex). Each definition is one expression in the constructors of
`Constructions.lean`, and is an `abbrev` when it is a single constructor call:

```lean
abbrev C4        : CGraph := cycle 4
abbrev cross     : CGraph := spider [1, 1, 1, 2]
abbrev diamond   : CGraph := twoCliqueSum K3 K3
abbrev domino    : CGraph := twoCliqueSum C4 C4
def    sun3      : CGraph := compl net
def    K6MinusGem : CGraph := compl (disjUnion gem (empty 1))
```

Naming 112 six-vertex graphs by hand needs a way to tell which ones are still missing, which is
what the enumerator is for: the file ends with

```lean
theorem enumerateConnIso_six : enumerateConnIso 6 = conn6.map (Quotient.mk CGraph.isoSetoid)
```

and its five smaller siblings — the named list *is* the enumeration, in canonical-code order, so
nothing is missing and nothing is named twice. `connOfCard_complete` and `connOfCard_pairwise`
unpack that into "every connected graph on `n ≤ 6` vertices is isomorphic to one of these" and
"no two of these are isomorphic".

The checks are `native_decide`: comparing two `List IsoGraph`s canonicalises both sides, and the
canonical labelling is defined by well-founded recursion and lifted through a `Quotient`, neither
of which the kernel reduces — so `decide` is stuck even at `n = 1`. The whole file, 143
definitions and all six checks, builds in about four seconds.

## Strongly regular graphs

`SRG.lean` is a table of 24 strongly regular graphs — `(n, k, ℓ, μ)` meaning `n` vertices,
`k`-regular, `ℓ` common neighbours across an edge and `μ` across a non-edge. Families first
(`cycle 5`, `bipartite 3 3`, `cocktailParty 4`, `rook m n`, `triangular n`, `kneser 6 2`,
`foldedCube`, `paley q` up to `Paley(101)`), then the sporadic ones defined in that file:
Shrikhande, the 27 lines on a cubic surface and its complement the Schläfli graph, the three
Chang graphs, and Hoffman–Singleton.

Each row's parameters are a theorem, and whatever can be proved rather than computed, is.
Six infinite families are settled once and for all in `Constructions.lean`, from
`isSRGWith_of` — a restatement of strong regularity in terms of `nbrs`, a vertex's neighbours as
a `Finset`, with no `SimpleGraph` and no `Fintype.card` of a subtype in sight:

```lean
theorem isSRGWith_rook (k : ℕ) : (rook k k).IsSRGWith (k * k) (2 * (k - 1)) (k - 2) 2
theorem isSRGWith_kneser_two (n : ℕ) :
    (kneser n 2).IsSRGWith (n.choose 2) ((n - 2).choose 2) ((n - 4).choose 2) ((n - 3).choose 2)
theorem isSRGWith_triangular (n : ℕ) (hn : 4 ≤ n) :
    (triangular n).IsSRGWith (n.choose 2) (2 * (n - 2)) (n - 2) 4
theorem isSRGWith_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).IsSRGWith q ((q - 1) / 2) ((q - 5) / 4) ((q - 1) / 4)
theorem isSRGWith_bipartite (n : ℕ) : (bipartite n n).IsSRGWith (2 * n) n 0 n
theorem isSRGWith_cocktailParty (n : ℕ) :
    (cocktailParty n).IsSRGWith (2 * n) (2 * n - 2) (2 * n - 4) (2 * n - 2)
```

Only the *square* rook's graphs are strongly regular: in `rook m n` two squares sharing a row
have `n - 2` common neighbours and two sharing a column have `m - 2`. Only the Kneser graphs on
*pairs* are, likewise — two non-adjacent `k`-sets meeting in `i` points have `(n - 2k + i).choose
k` common neighbours, and `i` is not determined by `k` once `k > 2` — though the degree
`(n - k).choose k` and the edge count `(n - 2k).choose k` are proved for every `k`
(`card_nbrs_kneser`, `card_nbrs_inter_kneser`). The triangular graphs come for free: `johnsonTwoIso`
identifies `johnson n 2` with `compl (kneser n 2)`, and `isSRGWith_compl` does the rest.

Paley is the one that is genuinely a character sum rather than a counting argument. `paley q`
is a Cayley graph on the nonzero squares, so with `χ = quadraticChar F` over a field with
`q ≡ 1 mod 4` elements, `χ (-1) = 1` makes `χ (y - x) = 1` symmetric, `∑ u, χ u = 0` gives the
degree `(q - 1) / 2`, and

```lean
theorem quadraticChar_sum_mul_sub (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ u : F, quadraticChar F (u * (u - a)) = -1
```

— proved by pushing the sum through the bijection `u ↦ 1 - a * u⁻¹` from the nonzero elements to
the elements other than `1` — turns `∑ (1 + χ u)(1 + χ (u - a))` into the common-neighbour count
`(q - 3 - 2 * χ a) / 4`, which is `(q - 5) / 4` across an edge and `(q - 1) / 4` across a
non-edge. `isSRGWith_paleyField` states that for any finite field; `paleyIso` then identifies
`paley q`, which lives on `Fin q` and reads its adjacency out of the `qrTable` lookup array,
with the field version over `ZMod q`. Making that last step bearable is why `qrTable` is an
`Array.ofFn` over the defining predicate rather than a scatter of `i * i % q` into a mutable
array: `qrTable_getElem` reads an entry off with no reasoning about `Array.set!`.

The last two are the easy ones. `bipartite n n` and `cocktailParty n` are both complements of
disjoint unions of complete graphs, so adjacency is "different part" and every count the
definition asks for is a sum of part sizes over a complement of parts; for equal parts those sums
are products. The cocktail party case is stated for `completeMultipartite (List.replicate n a)`
generally, and `(na, (n-1)a, (n-2)a, (n-1)a)` stays correct in the degenerate cases `n ≤ 2` on
truncated subtraction alone.

That accounts for thirteen rows. `isSRGWith_compl` alone accounts for three more — `compl
clebsch`, `schlafli = compl linesOnCubic`, `compl hoffmanSingleton` — leaving eight. Of those,
`cycle 5`, `clebsch` and `shrikhande` are checked by kernel `decide`, and only the five large
sporadic entries — `linesOnCubic`, the three Chang graphs and Hoffman–Singleton — still need
`native_decide`: the predicate is decidable in `O(n³)` adjacency queries, and past twenty-seven
vertices that is a twenty-five-second kernel reduction apiece, which buys no extra confidence
over the compiler for definitions this explicit.

The whole file — 24 parameter checks up to 101 vertices, plus four canonical-key comparisons —
builds in about twenty-five seconds. That budget is what "efficiently evaluable" buys: `paley q`
reads a precomputed `Array Bool` of quadratic residues (hoisted into a `let` so the compiled
closure captures the table rather than rebuilding it per query), Hoffman–Singleton is Robertson's
pentagon/pentagram model in `Nat` arithmetic — four divisions and a multiply mod 5 — and
Shrikhande is a six-element lookup in a Cayley graph on `ℤ/4 × ℤ/4`. An edge list would have made
every query an `O(|E|)` scan and every check `O(n³·|E|)`.

The table is data, not just a docstring: `Entry` bundles a name, the graph, the four parameters
and the proof, so `table : List Entry` can be mapped over — `#guard` checks its length and the
vertex counts, and `param_eq` reads the feasibility identity `k(k - ℓ - 1) = (n - k - 1)μ` off
any row.

Strongly regular graphs are exactly the inputs that defeat cheap invariants — every vertex has
the same degree and the same number of triangles through it — so the interesting statements are
the negative ones, and those go through the canonical key:

```lean
theorem shrikhande_not_iso_rook : ¬Nonempty (shrikhande ≃cg rook 4 4)
theorem changs_pairwise_not_iso :
    ([triangular 8, chang₁, chang₂, chang₃] : List CGraph).Pairwise fun G H ↦ ¬Nonempty (G ≃cg H)
```

Both lists are complete classifications — the only `(16, 6, 2, 2)` graphs and the only
`(28, 12, 6, 4)` graphs respectively — so what is checked here is that the library agrees with
the classification. Missing, for want of the Steiner system `S(3, 6, 22)`: Higman–Sims, Gewirtz,
and the `M₂₂` graph.

## Transitivity and clique sums

`CliqueSum.lean` glues two graphs along a shared clique — a vertex (`oneCliqueSum`) or an edge
(`twoCliqueSum`) — without quotienting anything: the vertex type is `G.V ⊕ {v : H.V // v ≠ w}`,
so the copy of `H` simply drops the vertices `G` already supplies and their neighbours are
re-attached to the corresponding vertices of `G`.

Writing `oneCliqueSum G H` with no mention of *where* is only honest if the answer does not
depend on it, which is what the two transitivity predicates in `Invariants.lean` are for:

```lean
def IsVertexTransitive : Prop := ∀ u v : G.V, ∃ σ : G ≃cg G, σ u = v
def IsArcTransitive : Prop :=
  ∀ u v u' v' : G.V, G.Adj u v → G.Adj u' v' → ∃ σ : G ≃cg G, σ u = u' ∧ σ v = v'
```

`vertexSum_iso` and `edgeSum_iso` then say that any two choices of gluing site give isomorphic
graphs, so the distinguished vertex and edge — supplied by the `Pointed` and `EdgePointed`
classes, because a `Fintype` is a `Multiset` and no *computable* "first vertex" can be pulled out
of one — are a convenience rather than part of the definition.

Both predicates are decidable, by enumerating the `n!` permutations of the vertex type. That is
fine for a sanity check at four vertices and useless past seven. Two things replace it: for
individual graphs, the automorphism-group search of the next section; for the families, a
structural proof in `Constructions.lean`: `isVertexTransitive_complete`,
`isArcTransitive_complete`, `isVertexTransitive_cayleyAdd` (right translation),
`isVertexTransitive_hypercube` and `isVertexTransitive_foldedCube` (add a fixed bit-string), and
for cycles both `isVertexTransitive_cycle` and `isArcTransitive_cycle` — rotations `x ↦ x + d`
match up two arcs running the same way round the cycle, reflections `x ↦ c - x` two running
oppositely. The reflections are automorphisms only because `ofRel` symmetrises, which is why the
`ofRel` transitivity lemmas ask for a permutation preserving `r x y || r y x` rather than `r`.

Arc-transitivity is the stronger of the two, and `isVertexTransitive_of_isArcTransitive` derives
one from the other — but only for a graph with no isolated vertex, since `empty n` is arc-
transitive (vacuously) and not vertex-transitive. So the direct proofs above are kept, and
arc-transitivity is proved separately where it holds: `isArcTransitive_hypercube` (translate by
`u`, swap the two differing coordinates with `cubeCoord`, translate by `u'`),
`isArcTransitive_bipartite_self` for `K_{n,n}` (permute the two sides with `bipartiteCongr`, and
swap them with `bipartiteSwap` when the two arcs run opposite ways), and
`isArcTransitive_kneser`. The Kneser case rests on `exists_perm_image₂`: two disjoint pairs of
finsets with matching cardinalities are related by a permutation of the ground set, built by
matching `A ↔ A'`, `B ↔ B'` and the two complements with `Finset.equivOfCardEq`. Taking
`B = B' = ∅` gives `isVertexTransitive_kneser` as well, which avoids needing `kneser n k` to have
an arc at all.

The transitivity of a graph transfers to graphs built from it. `isVertexTransitive_compl`
transports an automorphism unchanged. The four products each get
`isVertexTransitive_{cartesian,tensor,strong,lex}Product`, acting coordinatewise via
`Equiv.prodCongr` — only vertex-transitivity, as none of the four is arc-transitive in general.
And `isVertexTransitive_lineGraph` turns arc-transitivity of `G` into vertex-transitivity of
`lineGraph G`: an automorphism of `G` permutes its edges (`edgePerm`, hence `lineGraphAuto`), and
an arc `(u, v) ↦ (u', v')` carries the edge `s(u, v)` to `s(u', v')`.

The payoff is in `NamedSmallGraphs.lean`, where six graphs get their natural definitions:

```lean
abbrev paw     : CGraph := oneCliqueSum K3 K2    abbrev diamond : CGraph := twoCliqueSum K3 K3
abbrev butterfly : CGraph := oneCliqueSum K3 K3  abbrev house   : CGraph := twoCliqueSum K3 C4
abbrev fish    : CGraph := oneCliqueSum K3 C4    abbrev domino  : CGraph := twoCliqueSum C4 C4
```

each with a theorem — `paw_iso_vertexSum`, `house_iso_edgeSum`, … — saying it is what you get
from *any* choice of gluing site. The enumeration identities check the definitions themselves:
if any of these were the wrong graph, `enumerateConnIso_six` would stop being true.

## The automorphism group

The search already finds automorphisms. Whenever it reaches a leaf whose certificate ties the
incumbent's, the two labellings differ by an automorphism, and it records that permutation and
uses it to prune the rest of the tree — that is where most of the algorithm's speed comes from.
`canonPerm` then throws them away. `Canon/Group.lean` keeps them:

```lean
def canonPermAndGens (n : Nat) (adj : Fin n → Fin n → Bool) :
    Equiv.Perm (Fin n) × Array (autGroup n adj)
```

One search, both halves — `canonPerm n adj` and `autGens n adj` are its two projections
*definitionally*, so asking for the pair costs nothing over asking for the labelling alone, and
asking for the two separately costs twice. `autGroup n adj` is the honest automorphism group as a
`Subgroup (Equiv.Perm (Fin n))`, and the generators come with their membership proofs already
attached: `Canon/Leaves.lean`'s `StGood` invariant, which the correctness proof needed anyway,
says exactly that everything the search puts in `St.autos` is an automorphism. So there is no
run-time check here and nothing new to prove — the generators arrive verified.

What is *not* proved is that they generate the whole group. Nothing depends on it, and it is why
the transitivity tests hand back a

```lean
inductive Cert (P : Prop) : Type | yes (h : P) : Cert P | no : Cert P
```

— a proof of `P`, or nothing — rather than a `Decidable P`. `Cert P` is data, so the search runs
in compiled code and the proof comes back out:

```lean
example : petersen.IsVertexTransitive :=
  (petersen.vertexTransitiveCertOfEquiv (ofFnEquiv 10 _)).out (by native_decide)
```

Inside, `vertexTransitiveCert` breadth-first searches the orbit of vertex `0` under the
generators and returns, for each vertex reached, a *word* in the generators taking `0` to it.
Words rather than permutations: a product of generators is in the subgroup by `mul_mem`, so
membership is free, and the only thing left to check is that the word lands where it claims to —
one `Fin n` equality per vertex, decided by `decide`. `arcTransitiveCert` is the same search on
the `n²` ordered pairs. A bug in the breadth-first search can therefore only cost a `Cert.no`; it
can never produce a wrong proof. (`Cert.no` is not a disproof either. In practice the harvested
generators do generate the full group, so it means "not transitive", but that direction is not
proved.)

`Symmetry.lean` lifts all of this to `CGraph`, whose vertex type is arbitrary. Everything there
needs a computable indexing `e : G.V ≃ Fin n`, which cannot be manufactured — `Fintype.equivFin`
is noncomputable and the computable `Fintype.truncEquivFin` lands in `Trunc`, out of which no
data may be extracted — so each entry point comes in two flavours: `…OfEquiv e` taking the
indexing, and a plain version that runs on `G.canonicalize`, whose vertex type *is*
`Fin (Fintype.card G.V)`, and transports the answer back. The second is always available and
costs a second run of the search. For the same reason there is no `IsoGraph`-level generator set:
generators live on the vertex set, and a set of them is not invariant under renaming. Transitivity
is invariant, and `IsoGraph.vertexTransitiveCert` tests it on the canonical representative.

`autGroupOrder?` is a diagnostic and unverified: it enumerates the group generated by the
harvested permutations outright, capped at a `limit`, which is exponentially worse than the
Schreier–Sims algorithm one would normally use but is obviously correct. `Compute.lean` checks it
against the graphs it already has — 10 for `C5`, 12 for the prism, 72 for two disjoint triangles,
120 for Petersen — along with the transitivity of each and the fact that the prism is
vertex-transitive but not arc-transitive.

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

The exceptions are the computational checks, which are deliberate: everything proved by
`native_decide` — `Compute.lean`, the enumeration identities of `NamedSmallGraphs.lean`, the
five large sporadic parameter checks and the non-isomorphism theorems of `SRG.lean` — additionally uses `Lean.ofReduceBool` and
`Lean.trustCompiler`, i.e. trusts the compiler. It has to: `canonAdj` is well-founded recursion over
`Array`, which the kernel will not reduce.

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
