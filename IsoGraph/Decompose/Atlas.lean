import IsoGraph.Decompose.Cert
import IsoGraph.Enum.All
import IsoGraph.SmallGraphs.Defs

/-!
# Decomposing a graph into named pieces

Given a concrete graph, what is it *called*?  Most of the graphs that come up are not primitive:
they are a disjoint union, or a join, or the complement of something with a name, and the pieces
are themselves cycles, complete graphs, Kneser graphs — things the library already knows about.
This file is the search that finds such a description, and the atlas of names it searches in.

Nothing here is proved.  The search runs in the elaborator, where it is free, and what it produces
is a *guess*: an expression `H` built out of named graphs and a pair of index lists describing an
isomorphism `G ≃cg H`.  The guess is then checked in the kernel by `IsoGraph.Decompose.isoOfList`,
so an atlas entry with the wrong graph attached to it, or a bug in the search, costs a failed
tactic and never an unsound proof.

## The search

`decompose` is a recursion on the graph:

* if the graph is in the atlas, that name;
* otherwise, if it is disconnected, the disjoint union of the descriptions of its components;
* otherwise, if its *complement* is disconnected, the join of the descriptions of the co-components
  (a join is exactly a graph whose complement falls apart);
* otherwise, if the complement is in the atlas, the complement of that name;
* otherwise, the edge list of the canonical form.

Looking in the atlas *first* is what keeps `empty 5` from coming out as `1 ⊕g 1 ⊕g 1 ⊕g 1 ⊕g 1`
and `complete 7` from coming out as a five-fold join.

## Finding the isomorphism

Both graphs are canonically labelled — the library's own `IsoGraph.Canon.canonPerm`, running
compiled — and the two labellings are composed.  That is one canonical form each, not a search
over bijections, and it doubles as the isomorphism test: if the canonical codes differ the guess
was wrong and the search reports failure rather than handing the kernel something it cannot check.
-/

set_option autoImplicit false

namespace CGraph.Decompose

open IsoGraph.Canon CGraph.Enum

/-! ## Graphs on an initial segment

The search works on `{0, …, n-1}` with the adjacency of each vertex packed into a natural number,
which is what makes the neighbourhood operations single machine instructions. -/

/-- A graph on `{0, …, n-1}`: one bitmask of neighbours per vertex. -/
structure IGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- `row[i]` has bit `j` set exactly when `i` and `j` are adjacent. -/
  row : Array ℕ
  deriving Inhabited

namespace IGraph

/-- Adjacency, out of range included (`false`). -/
def adj (g : IGraph) (i j : ℕ) : Bool := (g.row.getD i 0).testBit j

/-- The graph on `{0, …, n-1}` with a given adjacency. -/
def ofFn (n : ℕ) (a : ℕ → ℕ → Bool) : IGraph where
  n := n
  row := (Array.range n).map fun i ↦
    (List.range n).foldl (fun m j ↦ if a i j then m ||| 2 ^ j else m) 0

/-- Adjacency as the canonical labelling wants it. -/
def finAdj (g : IGraph) : Fin g.n → Fin g.n → Bool := fun i j ↦ g.adj i.1 j.1

/-- The canonical code: a complete isomorphism invariant. -/
def code (g : IGraph) : ℕ := canonCode g.n g.finAdj

/-- Canonical position `i` is occupied by vertex `(canonLab g)[i]`. -/
def canonLab (g : IGraph) : List ℕ :=
  let σ := canonPerm g.n g.finAdj
  (List.finRange g.n).map fun i ↦ (σ i).1

/-- The complement. -/
def compl (g : IGraph) : IGraph := ofFn g.n fun i j ↦ i != j && !g.adj i j

/-- The subgraph induced on `vs`, relabelled onto an initial segment in the order of `vs`. -/
def induce (g : IGraph) (vs : Array ℕ) : IGraph :=
  ofFn vs.size fun i j ↦ g.adj (vs.getD i 0) (vs.getD j 0)

/-- The edges, as pairs `i < j`. -/
def edgeList (g : IGraph) : List (ℕ × ℕ) :=
  (pairsBelow g.n).filter fun p ↦ g.adj p.1 p.2

/-- The edges of the *canonical form*: the same graph, relabelled so that the labelling is
determined by the isomorphism class. -/
def canonEdgeList (g : IGraph) : List (ℕ × ℕ) :=
  let c := g.code
  (pairsBelow g.n).filter fun p ↦ c.testBit (pairIdx p.1 p.2)

/-- The vertices reachable from those on the stack, added to `out`. -/
private def reach (g : IGraph) : ℕ → Array Bool → List ℕ → List ℕ → List ℕ
  | 0, _, _, out => out
  | _ + 1, _, [], out => out
  | fuel + 1, seen, v :: stack, out =>
    let step := (List.range g.n).foldl
      (fun (p : Array Bool × List ℕ) w ↦
        if g.adj v w && !p.1.getD w true then (p.1.set! w true, w :: p.2) else p)
      (seen, stack)
    reach g fuel step.1 step.2 (v :: out)

/-- The connected components, each sorted, in order of least vertex. -/
def components (g : IGraph) : List (List ℕ) :=
  ((List.range g.n).foldl
    (fun (p : List (List ℕ) × Array Bool) v ↦
      if p.2.getD v true then p
      else
        let c := (reach g (g.n + 1) (p.2.set! v true) [v] []).mergeSort (· ≤ ·)
        (c :: p.1, c.foldl (fun s w ↦ s.set! w true) p.2))
    ([], Array.replicate g.n false)).1.reverse

/-- A concrete graph, read through the enumeration of its vertex type.  The indices are exactly
the ones `IsoGraph.Decompose.idxOf` uses, so a permutation found here is a certificate there. -/
def ofCGraph (G : CGraph) : IGraph :=
  let vs := (FinEnum.toList G.V).toArray
  { n := vs.size
    row := vs.map fun u ↦
      (FinEnum.toList G.V).zipIdx.foldl (fun m p ↦ if G.Adj u p.1 then m ||| 2 ^ p.2 else m) 0 }

end IGraph

/-! ## The atlas -/

/-- A graph the search can name: the head constant, its natural-number arguments, its order and
the graph itself.  The order is stored so that the search can skip an entry without building it. -/
structure AtlasEntry where
  /-- The constant to print. -/
  head : Lean.Name
  /-- Its natural-number arguments. -/
  args : List ℕ
  /-- The number of vertices. -/
  ord : ℕ
  /-- The graph. -/
  graph : CGraph

/-- An atlas entry, with the order filled in. -/
def entry (head : Lean.Name) (args : List ℕ) (G : CGraph) : AtlasEntry :=
  ⟨head, args, FinEnum.card G.V, G⟩

/-- A one-parameter family, for parameters `lo, …, hi`. -/
def family₁ (head : Lean.Name) (f : ℕ → CGraph) (lo hi : ℕ) : List AtlasEntry :=
  (List.range (hi + 1 - lo)).map fun k ↦ entry head [k + lo] (f (k + lo))

/-- A two-parameter family. -/
def family₂ (head : Lean.Name) (f : ℕ → ℕ → CGraph) (as bs : List ℕ) : List AtlasEntry :=
  as.flatMap fun a ↦ bs.map fun b ↦ entry head [a, b] (f a b)

/-- The individually named graphs.  These come first, so that a graph with a proper name gets it
rather than the systematic description of a family it happens to belong to: `claw` rather than
`star 3`, `petersen` rather than `kneser 5 2`, `octahedron` rather than `cocktailParty 3`. -/
def namedAtlas : List AtlasEntry :=
  [ entry ``SmallGraphs.claw [] SmallGraphs.claw,
    entry ``SmallGraphs.paw [] SmallGraphs.paw,
    entry ``SmallGraphs.diamond [] SmallGraphs.diamond,
    entry ``SmallGraphs.bull [] SmallGraphs.bull,
    entry ``SmallGraphs.house [] SmallGraphs.house,
    entry ``SmallGraphs.kite [] SmallGraphs.kite,
    entry ``SmallGraphs.gem [] SmallGraphs.gem,
    entry ``SmallGraphs.dart [] SmallGraphs.dart,
    entry ``SmallGraphs.cricket [] SmallGraphs.cricket,
    entry ``SmallGraphs.fork [] SmallGraphs.fork,
    entry ``SmallGraphs.banner [] SmallGraphs.banner,
    entry ``SmallGraphs.net [] SmallGraphs.net,
    entry ``SmallGraphs.cross [] SmallGraphs.cross,
    entry ``SmallGraphs.domino [] SmallGraphs.domino,
    entry ``SmallGraphs.barbell [] SmallGraphs.barbell,
    entry ``SmallGraphs.fish [] SmallGraphs.fish,
    entry ``SmallGraphs.butterfly [] SmallGraphs.butterfly,
    entry ``SmallGraphs.octahedron [] SmallGraphs.octahedron,
    entry ``NamedGraphs.moserSpindle [] NamedGraphs.moserSpindle,
    entry ``NamedGraphs.grotzsch [] NamedGraphs.grotzsch,
    entry ``CGraph.petersen [] CGraph.petersen,
    entry ``NamedGraphs.herschel [] NamedGraphs.herschel,
    entry ``NamedGraphs.tietze [] NamedGraphs.tietze,
    entry ``NamedGraphs.chvatal [] NamedGraphs.chvatal,
    entry ``NamedGraphs.wagner [] NamedGraphs.wagner,
    entry ``NamedGraphs.franklin [] NamedGraphs.franklin,
    entry ``NamedGraphs.frucht [] NamedGraphs.frucht,
    entry ``NamedGraphs.durer [] NamedGraphs.durer,
    entry ``NamedGraphs.icosahedron [] NamedGraphs.icosahedron,
    entry ``NamedGraphs.dodecahedron [] NamedGraphs.dodecahedron,
    entry ``NamedGraphs.truncatedTetrahedron [] NamedGraphs.truncatedTetrahedron,
    entry ``NamedGraphs.bidiakisCube [] NamedGraphs.bidiakisCube,
    entry ``NamedGraphs.heawood [] NamedGraphs.heawood,
    entry ``NamedGraphs.mobiusKantor [] NamedGraphs.mobiusKantor,
    entry ``NamedGraphs.pappus [] NamedGraphs.pappus,
    entry ``NamedGraphs.desargues [] NamedGraphs.desargues,
    entry ``NamedGraphs.nauru [] NamedGraphs.nauru,
    entry ``NamedGraphs.mcgee [] NamedGraphs.mcgee,
    entry ``NamedGraphs.folkman [] NamedGraphs.folkman,
    entry ``NamedGraphs.dyck [] NamedGraphs.dyck,
    entry ``NamedGraphs.coxeter [] NamedGraphs.coxeter,
    entry ``NamedGraphs.tutteCoxeter [] NamedGraphs.tutteCoxeter,
    entry ``NamedGraphs.robertson [] NamedGraphs.robertson,
    entry ``NamedGraphs.holt [] NamedGraphs.holt,
    entry ``NamedGraphs.flowerSnark [] NamedGraphs.flowerSnark,
    entry ``SRG.clebsch [] SRG.clebsch,
    entry ``SRG.shrikhande [] SRG.shrikhande,
    entry ``SRG.schlafli [] SRG.schlafli,
    entry ``SRG.hoffmanSingleton [] SRG.hoffmanSingleton,
    entry ``SRG.chang₁ [] SRG.chang₁,
    entry ``SRG.chang₂ [] SRG.chang₂,
    entry ``SRG.chang₃ [] SRG.chang₃,
    entry ``NamedGraphs.tutte [] NamedGraphs.tutte,
    entry ``NamedGraphs.balaban10Cage [] NamedGraphs.balaban10Cage,
    entry ``NamedGraphs.biggsSmith [] NamedGraphs.biggsSmith,
    entry ``NamedGraphs.harries [] NamedGraphs.harries,
    entry ``NamedGraphs.harriesWong [] NamedGraphs.harriesWong,
    entry ``NamedGraphs.gray [] NamedGraphs.gray,
    entry ``NamedGraphs.foster [] NamedGraphs.foster,
    entry ``NamedGraphs.ljubljana [] NamedGraphs.ljubljana,
    entry ``NamedGraphs.cuboctahedron [] NamedGraphs.cuboctahedron,
    entry ``NamedGraphs.truncatedCube [] NamedGraphs.truncatedCube,
    entry ``NamedGraphs.truncatedOctahedron [] NamedGraphs.truncatedOctahedron,
    entry ``NamedGraphs.icosidodecahedron [] NamedGraphs.icosidodecahedron,
    entry ``NamedGraphs.truncatedIcosahedron [] NamedGraphs.truncatedIcosahedron,
    entry ``NamedGraphs.triakisTetrahedron [] NamedGraphs.triakisTetrahedron,
    entry ``NamedGraphs.rhombicDodecahedron [] NamedGraphs.rhombicDodecahedron,
    entry ``NamedGraphs.triakisOctahedron [] NamedGraphs.triakisOctahedron,
    entry ``NamedGraphs.tetrakisHexahedron [] NamedGraphs.tetrakisHexahedron,
    entry ``NamedGraphs.rhombicTriacontahedron [] NamedGraphs.rhombicTriacontahedron,
    entry ``NamedGraphs.pentakisDodecahedron [] NamedGraphs.pentakisDodecahedron ]

/-- The parametrised families.  `empty` and `complete` come first so that the degenerate members
of every other family — `path 2`, `cycle 3`, `wheel 3` — are named as what they are. -/
def familyAtlas : List AtlasEntry :=
  family₁ ``empty empty 0 40 ++
  family₁ ``complete complete 0 40 ++
  family₁ ``path path 1 40 ++
  family₁ ``cycle cycle 3 40 ++
  family₁ ``star star 1 40 ++
  family₁ ``wheel wheel 3 30 ++
  family₁ ``hypercube hypercube 0 6 ++
  family₁ ``prism prism 3 20 ++
  family₁ ``ladder ladder 2 20 ++
  family₁ ``cocktailParty cocktailParty 1 15 ++
  family₁ ``crown crown 2 15 ++
  family₁ ``book book 1 20 ++
  family₁ ``fan fan 2 20 ++
  family₁ ``friendship friendship 1 12 ++
  family₁ ``triangular triangular 3 10 ++
  family₁ ``paley paley 5 29 ++
  family₂ ``bipartite bipartite (List.range 21) (List.range 21) ++
  family₂ ``rook rook (List.range 9) (List.range 9) ++
  family₂ ``turan turan (List.range 21) (List.range 9) ++
  family₂ ``kneser kneser (List.range 10) (List.range 4) ++
  family₂ ``johnson johnson (List.range 10) (List.range 4) ++
  family₂ ``gp gp (List.range 16) (List.range 8) ++
  family₂ ``tadpole tadpole (List.range 13) (List.range 13) ++
  family₂ ``lollipop lollipop (List.range 13) (List.range 13) ++
  family₂ ``doubleStar doubleStar (List.range 11) (List.range 11)

/-- **The atlas**: every graph the search can put a name to. -/
def atlas : List AtlasEntry := namedAtlas ++ familyAtlas

/-- The name of a graph, if it has one. -/
def atlasLookup (g : IGraph) : Option (Lean.Name × List ℕ) :=
  let c := g.code
  (atlas.find? fun e ↦
    e.ord == g.n && (IGraph.ofCGraph e.graph).code == c).map fun e ↦ (e.head, e.args)

/-! ## Descriptions -/

/-- A description of a graph as an expression in named pieces. -/
inductive GExpr where
  /-- A named graph, applied to natural-number arguments. -/
  | atom (head : Lean.Name) (args : List ℕ)
  /-- A disjoint union. -/
  | sum (a b : GExpr)
  /-- A join. -/
  | join (a b : GExpr)
  /-- A complement. -/
  | compl (a : GExpr)
  /-- No name found: the canonical edge list. -/
  | edges (n : ℕ) (es : List (ℕ × ℕ))
  deriving Inhabited

/-- The graph a description denotes.  This has to agree with what the tactic *prints*, and it does
because the atlas carries both the head constant and the graph; if they ever disagreed the kernel
would reject the certificate. -/
def GExpr.interp : GExpr → CGraph
  | .atom h args =>
    match atlas.find? fun e ↦ e.head == h && e.args == args with
    | some e => e.graph
    | none => CGraph.empty 0
  | .sum a b => a.interp ⊕g b.interp
  | .join a b => a.interp ∇g b.interp
  | .compl a => a.interpᶜ
  | .edges n es => CGraph.ofEdges n es

/-- How many named pieces a description is built from: the tie-breaker that prefers a genuine
decomposition to a bare edge list. -/
def GExpr.weight : GExpr → ℕ
  | .atom _ _ => 1
  | .sum a b => a.weight + b.weight
  | .join a b => a.weight + b.weight
  | .compl a => a.weight
  | .edges _ _ => 0

/-! ## The search -/

/-- Left-fold a nonempty list of descriptions with a binary constructor, matching the way the
notations associate. -/
private def foldWith (f : GExpr → GExpr → GExpr) : List GExpr → GExpr
  | [] => .edges 0 []
  | x :: xs => xs.foldl f x

/-- The vertex sets `g` should be cut into, given the components of `g` or of its complement.

Isolated pieces are pooled: `s` singleton components of `g` contribute `empty s` to the union
rather than `s` copies of `empty 1`, and `s` singleton components of the *complement* contribute
`complete s` to the join.  Pooling is skipped when it would leave nothing to cut. -/
private def cutSets (cs : List (List ℕ)) : Option (List (List ℕ)) :=
  if cs.length ≤ 1 then none
  else
    let split := cs.partition fun c ↦ c.length == 1
    if split.1.length ≤ 1 || split.2.isEmpty then some cs
    else some (split.1.flatten :: split.2)

/-- **Describe a graph.**  See the module docstring for the order the rules are tried in. -/
partial def decompose (g : IGraph) : GExpr :=
  match atlasLookup g with
  | some (h, a) => .atom h a
  | none =>
    let parts (h : IGraph) : Option (List IGraph) :=
      (cutSets h.components).map fun cs ↦
        let ps := cs.map fun c ↦ g.induce c.toArray
        (ps.map fun p ↦ (p.n, p.code, p)).mergeSort
          (fun x y ↦ x.1 < y.1 || (x.1 == y.1 && x.2.1 ≤ y.2.1)) |>.map (·.2.2)
    match parts g with
    | some ps => foldWith .sum (ps.map decompose)
    | none =>
      match parts g.compl with
      | some ps => foldWith .join (ps.map decompose)
      | none =>
        match atlasLookup g.compl with
        | some (h, a) => .compl (.atom h a)
        | none => .edges g.n g.canonEdgeList

/-- The index lists of an isomorphism `g ≃ h`, found by composing the two canonical labellings.

The result is verified before it is returned, so `none` means "no isomorphism was found", never
"here is one that does not work". -/
def isoPerm (g h : IGraph) : Option (List ℕ × List ℕ) :=
  if g.n != h.n || g.code != h.code then none
  else
    let lab := g.canonLab.zip h.canonLab
    let p := lab.foldl (fun (a : Array ℕ) uv ↦ a.set! uv.1 uv.2) (Array.replicate g.n 0)
    let q := lab.foldl (fun (a : Array ℕ) uv ↦ a.set! uv.2 uv.1) (Array.replicate g.n 0)
    if (List.range g.n).all fun i ↦ (List.range g.n).all fun j ↦
        g.adj i j == h.adj (p.getD i 0) (p.getD j 0) then some (p.toList, q.toList)
    else none

/-- **Decompose a graph and certify the decomposition.**  Everything the tactic needs, in one
compiled call: the description, and the two index lists of an isomorphism onto it. -/
def decomposeWithPerm (G : CGraph) : Option (GExpr × List ℕ × List ℕ) :=
  let g := IGraph.ofCGraph G
  let e := decompose g
  match isoPerm g (IGraph.ofCGraph e.interp) with
  | some (p, q) => some (e, p, q)
  | none => none

end CGraph.Decompose
