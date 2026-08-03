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
`diameter`, `IsSRGWith`, `IsVertexTransitive`, `IsArcTransitive`. Mathlib had no invariance lemma
for distance or for strong regularity, so `SimpleGraph.Iso.edist_eq`, `ediam_eq`, `diam_eq`,
`card_commonNeighbors_eq` and `isSRGWith_of_iso` are proved there.

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
`book`, `fan`, `ladder`, `prism`, `triangular`, `rook`, `cocktailParty`.

The lifting has one wrinkle. `compl` and the four products need `[DecidableEq G.V]`, which a
`CGraph` does not carry, so they cannot be `Quotient.lift`ed as they stand. They are lifted as
`fun g ↦ ⟦CGraph.compl g.canonicalize⟧` instead: the canonical representative's vertex type is
`Fin (Fintype.card g.V)`, which does have the instance, and the congruence lemmas of the
`CGraph.Iso` namespace (`Iso.compl`, `Iso.cartesianProduct`, …) discharge the well-definedness
side condition. Each then gets a `_mk` lemma — `compl ⟦G⟧ = ⟦CGraph.compl G⟧` for any `G` with a
`DecidableEq`, not just a canonical one. `disjUnion` needs no instance, so `disjUnion_mk` is
`rfl`. `join` is not lifted at all: it is *defined* on the quotient as
`compl (disjUnion (compl G) (compl H))`, which makes `compl_join` and `join_comm` free.

The equations themselves come in families:

```
compl (compl G) = G          compl (cycle 5) = cycle 5     compl (path 4) = path 4
complete 1 = empty 1         cycle 3 = complete 3          wheel 3 = complete 4
disjUnion G (empty 0) = G    join G (empty 0) = G          join (complete m) (complete n) = complete (m + n)
kneser n 1 = complete n      kneser n n = empty 1          johnson n 1 = complete n
hypercube (n + 1) = cartesianProduct (hypercube n) (complete 2)
hypercube 3 = prism 4        foldedCube 3 = bipartite 4 4  paley 5 = cycle 5
rook m 0 = empty 0           rook 2 2 = cycle 4            bipartite 2 2 = cycle 4
strongProduct (complete m) (complete n) = complete (m * n)
tensorProduct G (empty n) = empty (G.V * n)
completeMultipartite (d :: ds) = join (empty d) (completeMultipartite ds)
completeMultipartite [a, b] = bipartite a b               cocktailParty 2 = cycle 4
completeMultipartite (List.replicate n 1) = complete n    triangular 4 = cocktailParty 3
circulant n [] = empty n     circulant n [1] = cycle n
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

The structural laws are the exception, since they are statements about all graphs at once. Each
is a `CGraph.Iso.*Assoc` built on `Equiv.prodAssoc`, whose adjacency obligation is reduced to a
Boolean tautology: rewrite with the `*_adj` equations and `decide_prod_eq`
(`decide (p = q) = (decide (p.1 = q.1) && decide (p.2 = q.2))`) until every equality test is
between vertices of a single factor, `generalize` the six atoms, and `decide`.

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
mycielskian (empty 0) = empty 1      mycielskian (complete 2) = cycle 5
mycielskian (empty n) = disjUnion (star n) (empty n)
```

— `lineGraph (complete n)` being the proof in the file that builds its bijection with
`Equiv.ofBijective` rather than writing it down: an edge of `Kₙ` is sent to its
`Sym2.toFinset`, a two-element subset of `Fin n`, and two *distinct* two-element subsets meet
exactly when they meet in one point, which is the adjacency of `J(n, 2)`. The last line is the
Mycielskian of an edgeless graph, where the apex and the `n` shadow vertices form a star and the
originals stay isolated.

`triangular 4 = cocktailParty 3` — the octahedron — is the one identity here that `SRG.lean` also
proves, by `native_decide` on the canonical keys. The version in `Identities.lean` is
kernel-checkable: `T(4)` is `compl (kneser 4 2)`, `kneser 4 2` is three disjoint edges (a six-point
`decide` on an explicit `Equiv.ofBijective`), and three uses of the cons rule turn
`compl (cocktailParty 3)` into the same disjoint union.

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
