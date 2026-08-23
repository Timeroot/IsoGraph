import IsoGraph.Decompose.Atlas
import IsoGraph.Decompose.Cert

/-!
# The `generate_graph_iso` tactic

`IsoGraph/Decompose/Atlas.lean` describes a graph as a formula built from named graphs, disjoint
unions, joins, complements and products; `IsoGraph/Decompose/Cert.lean` turns a pair of index lists
into an isomorphism.  This file is the glue: a tactic that runs the search in the elaborator and
hands the result back as a term.

    example : True := by
      generate_graph_iso (CGraph.cycle 4 ⊕g CGraph.complete 3) with e
      -- e : CGraph.cycle 4 ⊕g CGraph.complete 3 ≃cg CGraph.complete 3 ⊕g CGraph.cycle 4
      trivial

What the tactic adds is a `let`, not a `have`: an isomorphism is data, and later steps will want to
apply it to vertices, not merely know that it exists.

## What the kernel sees

Nothing of the search.  `decomposeWithPerm` runs as compiled code and returns a formula together
with the two index lists relating the original graph to it; the tactic prints the formula as a term
and emits

    CGraph.Decompose.isoOfList G H p q (by decide)

so the only thing checked is `isoListOK G H p q`, one `Bool` computation, quadratic in the order of
the graph.  No `native_decide`: a wrong answer from the elaborator is a failed `decide`, not an
unsound proof.

## Also here

`#decompose_graph G` prints the formula without proving anything — the way to find out what the
atlas knows about a graph.  `decompose_graph G` rewrites `G`, as an element of `IsoGraph`, to the
class of the formula, which is the useful form when the goal is about an isomorphism invariant.
-/

set_option autoImplicit false

namespace CGraph.Decompose

section Tactic
open Lean Elab Command Tactic Meta Term

/-- The type `Option (GExpr × List ℕ × List ℕ)`, as an expression. -/
private def resultType : Expr :=
  let nats := mkApp (.const ``List [0]) (.const ``Nat [])
  mkApp (.const ``Option [0]) <|
    mkApp2 (.const ``Prod [0, 0]) (.const ``GExpr []) (mkApp2 (.const ``Prod [0, 0]) nats nats)

/-- Compile and run a closed expression of type `Option (GExpr × List ℕ × List ℕ)`. -/
private unsafe def evalResultImpl (e : Expr) : MetaM (Option (GExpr × List ℕ × List ℕ)) :=
  Meta.evalExpr (Option (GExpr × List ℕ × List ℕ)) resultType e

/-- Evaluate a closed expression of type `Option (GExpr × List ℕ × List ℕ)`.  Only ever called
through its `implemented_by`; the answer is checked by `decide`, so a wrong one is not unsound. -/
@[implemented_by evalResultImpl]
private def evalResult (_e : Expr) : MetaM (Option (GExpr × List ℕ × List ℕ)) := pure none

/-! ## Printing a formula -/

/-- `l` as a list literal. -/
private def natsTerm (l : List ℕ) : MetaM Term := do
  let elems : Array Term := l.toArray.map fun n ↦ quote n
  `([$elems,*])

/-- `es` as a list literal. -/
private def pairsTerm (es : List (ℕ × ℕ)) : MetaM Term := do
  let elems ← es.toArray.mapM fun (i, j) ↦ `(($(quote i), $(quote j)))
  `([$elems,*])

/-- A formula as a term, using the library's notation for the operations.  Atoms are printed with
their full names — not `mkCIdent`, whose macro scope would show up as a dagger in the output; the
names are all at the root, so an ordinary identifier resolves to the same thing. -/
partial def render : GExpr → MetaM Term
  | .atom h args =>
    if args.isEmpty then return mkIdent h
    else return Syntax.mkApp (mkIdent h) (args.toArray.map fun n ↦ quote n)
  | .sum a b => do `($(← render a) ⊕g $(← render b))
  | .join a b => do `($(← render a) ∇g $(← render b))
  | .compl a => do `($(← render a)ᶜ)
  | .cart a b => do `($(← render a) □g $(← render b))
  | .tens a b => do `($(← render a) ⊗g $(← render b))
  | .strong a b => do `($(← render a) ⊠g $(← render b))
  | .lex a b => do `($(← render a) ·g $(← render b))
  | .edges n es => do
    return Syntax.mkApp (mkIdent ``CGraph.ofEdges) #[quote n, ← pairsTerm es]

/-! ## Running the search -/

/-- The `CGraph` a term denotes: either one outright, or an `IsoGraph` that reduces to the class of
one.  The `Bool` says which it was. -/
private def asCGraph (tac : String) (e : Expr) : MetaM (Expr × Bool) := do
  if (← inferType e).isAppOf ``CGraph then return (e, false)
  match (← whnf e).getAppFnArgs with
  | (``Quot.mk, #[_, _, G]) => return (G, true)
  | _ => throwError "{tac}: expected a closed `CGraph`, or an `IsoGraph` that reduces to the \
      class of one, but got{indentExpr e}"

/-- Elaborate a term and force its metavariables, so that it can be compiled. -/
private def closedTerm (t : Term) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Decompose `G`, returning the formula and the two index lists as terms. -/
private def searchFor (tac : String) (G : Expr) : TermElabM (Term × Term × Term) := do
  let g ← Term.exprToSyntax G
  let call ← closedTerm (← `(CGraph.Decompose.decomposeWithPerm $g))
  match ← evalResult call with
  | none => throwError "{tac}: could not decompose{indentExpr G}"
  | some (e, p, q) => return (← render e, ← natsTerm p, ← natsTerm q)

/-! ## The tactics -/

/-- **Print the decomposition of a graph.**

    #decompose_graph CGraph.mycielskian (CGraph.cycle 5)   -- NamedGraphs.grotzsch

Recognises named graphs and infinite families from the atlas of `IsoGraph/Decompose/Atlas.lean`,
splits along disjoint unions and joins, tries the complement, and tries to write the graph as a
product of two named ones; a graph it cannot describe is printed as an explicit `CGraph.ofEdges`. -/
syntax (name := decomposeGraphCmd) "#decompose_graph " term : command

elab_rules : command
  | `(command| #decompose_graph $t:term) => Command.liftTermElabM do
    let (G, _) ← asCGraph "#decompose_graph" (← closedTerm t)
    let (h, _, _) ← searchFor "#decompose_graph" G
    logInfo m!"{h}"

/-- **Name an isomorphism from a graph to its decomposition.**

    generate_graph_iso G
    generate_graph_iso G with e

adds a `let`-bound `e : G ≃cg H` to the context, where `H` is the description of `G` found by the
atlas search — a formula in named graphs, `⊕g`, `∇g`, `ᶜ` and the four products.  The name
defaults to `iso`.

The isomorphism is data and is bound by `let`, so `e x` reduces: a later step can compute with it,
not just cite it.  Its correctness is checked by a single `decide` on an index-list certificate; the
search itself happens in the elaborator and costs the kernel nothing. -/
syntax (name := generateGraphIso) "generate_graph_iso" ppSpace term (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| generate_graph_iso $t:term $[with $nm:ident]?) => withMainContext do
    let (G, _) ← asCGraph "generate_graph_iso" (← closedTerm t)
    let (h, p, q) ← searchFor "generate_graph_iso" G
    let g ← Term.exprToSyntax G
    let ty ← closedTerm (← `(($g : CGraph) ≃cg $h))
    let val ← instantiateMVars <| ← Term.elabTermEnsuringType
      (← `(CGraph.Decompose.isoOfList $g $h $p $q (by decide))) ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let val ← instantiateMVars val
    let name := (nm.map (·.getId)).getD `iso
    let (_, goal) ← (← (← getMainGoal).define name ty val).intro1P
    replaceMainGoal [goal]

/-- **Rewrite a graph in the goal to its decomposition.**

    decompose_graph (CGraph.mycielskian (CGraph.cycle 5))

replaces the class of that graph, wherever it occurs in the goal, by the class of the description
found by the atlas search — here `NamedGraphs.grotzsch`.  Since the two are equal as `IsoGraph`s,
every isomorphism invariant of the goal is unchanged, which is the point: it is the step that turns
a question about an unfamiliar graph into a question about named ones. -/
syntax (name := decomposeGraph) "decompose_graph" ppSpace term : tactic

elab_rules : tactic
  | `(tactic| decompose_graph $t:term) => withMainContext do
    let (G, _) ← asCGraph "decompose_graph" (← closedTerm t)
    let (h, p, q) ← searchFor "decompose_graph" G
    let g ← Term.exprToSyntax G
    evalTactic <| ← `(tactic|
      rw [show (Quotient.mk CGraph.isoSetoid ($g : CGraph) : IsoGraph)
            = Quotient.mk CGraph.isoSetoid $h from
          CGraph.Decompose.mk_eq_mk_of_isoListOK (p := $p) (q := $q) (by decide)])

end Tactic

end CGraph.Decompose

/-! ## Examples

One of each rule the search knows, kept here as its regression test: the answers below are the
kernel's, not the elaborator's, since each of them is a `decide` on a certificate. -/

/-- The Mycielskian of `C₅` is the Grötzsch graph. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.mycielskian (CGraph.cycle 5)) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid NamedGraphs.grotzsch := by
  decompose_graph (CGraph.mycielskian (CGraph.cycle 5))

/-- The complement of the Petersen graph is the triangular graph `T(5)`. -/
example : (Quotient.mk CGraph.isoSetoid CGraph.petersenᶜ : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.triangular 5) := by
  decompose_graph CGraph.petersenᶜ

/-- The line graph of `K₄` is the octahedron. -/
example : Nonempty (CGraph.lineGraph (CGraph.complete 4) ≃cg SmallGraphs.octahedron) := by
  generate_graph_iso (CGraph.lineGraph (CGraph.complete 4)) with e
  exact ⟨e⟩

/-- A disconnected graph is described component by component, in order of size. -/
example : Nonempty (CGraph.cycle 4 ⊕g CGraph.complete 3 ≃cg
    CGraph.complete 3 ⊕g CGraph.cycle 4) := by
  generate_graph_iso (CGraph.cycle 4 ⊕g CGraph.complete 3) with e
  exact ⟨e⟩

/-- A join is found through the complement, and the isolated vertices of the complement are pooled
into one complete graph rather than joined on one at a time. -/
example : Nonempty (CGraph.complete 2 ∇g (CGraph.cycle 5 ⊕g CGraph.complete 1) ≃cg
    CGraph.complete 2 ∇g (CGraph.empty 1 ⊕g CGraph.cycle 5)) := by
  generate_graph_iso (CGraph.complete 2 ∇g (CGraph.cycle 5 ⊕g CGraph.complete 1)) with e
  exact ⟨e⟩

/-- A product of two named graphs is recognised as one — and the tensor square of `C₅` happens to
be its cartesian square. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.cycle 5 ⊗g CGraph.cycle 5) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.cycle 5 □g CGraph.cycle 5) := by
  decompose_graph (CGraph.cycle 5 ⊗g CGraph.cycle 5)

/-- A blow-up — every vertex of `C₇` split into two false twins — is found as a lexicographic
product, the one of the four that is not commutative and so has to be tried both ways round.  The
statement would not typecheck if the search named anything else. -/
example : Nonempty (CGraph.cycle 7 ·g CGraph.empty 2 ≃cg CGraph.cycle 7 ·g CGraph.empty 2) := by
  generate_graph_iso (CGraph.cycle 7 ·g CGraph.empty 2) with e
  exact ⟨e⟩

/-- Blowing a vertex up into `k` *true* twins is the strong product with `Kₖ` instead, and since
the strong product is tried first that is the description that comes out. -/
example : (Quotient.mk CGraph.isoSetoid (CGraph.path 4 ·g CGraph.complete 2) : IsoGraph)
    = Quotient.mk CGraph.isoSetoid (CGraph.complete 2 ⊠g CGraph.path 4) := by
  decompose_graph (CGraph.path 4 ·g CGraph.complete 2)

/-- Nothing in the atlas: the description falls back to the canonical edge list. -/
example : Nonempty (CGraph.mycielskian (CGraph.path 3) ≃cg CGraph.ofEdges 7
    [(1, 4), (2, 4), (0, 5), (3, 5), (4, 5), (0, 6), (1, 6), (2, 6), (3, 6)]) := by
  generate_graph_iso (CGraph.mycielskian (CGraph.path 3)) with e
  exact ⟨e⟩
