import IsoGraph.Basic

/-!
# The `@[toIsoGraph]` attribute

Every construction and every quantity in this library is defined twice: once on `CGraph`, where a
concrete graph can be computed with, and once on `IsoGraph`, where it is the image of the first
under the quotient by isomorphism.  The second copy is mechanical, and this file makes it
automatic.  The attribute has four modes, chosen by the shape of the declaration it is put on.

## A construction

On a `CGraph`-valued definition that takes no graph of its own,

```
@[toIsoGraph]
def CGraph.paley (q : ℕ) : CGraph := ...
```

generates

```
def IsoGraph.paley (q : ℕ) : IsoGraph := ⟦CGraph.paley q⟧

theorem IsoGraph.paley_def (q : ℕ) : IsoGraph.paley q = ⟦CGraph.paley q⟧ := rfl
```

with any number of arguments.  The bridge is tagged `@[isoTransfer]`, the simp set that mediates
between the two levels; it is used from right to left, so `⟦CGraph.paley q⟧` is rewritten to
`IsoGraph.paley q` whenever a `CGraph`-level fact is restated one level up.

## A construction that takes a graph

A construction with a `CGraph` argument does not descend to the quotient by itself: it has to be
shown to respect isomorphism first.  The attribute goes on that congruence,

```
@[toIsoGraph]
def CGraph.Iso.lineGraph [DecidableEq G.V] [DecidableEq G'.V] (i : G ≃cg G') :
    CGraph.lineGraph G ≃cg CGraph.lineGraph G' := ...
```

and generates the `Quotient.lift` along it, together with the simp lemma that the lift agrees with
the construction on representatives:

```
def IsoGraph.lineGraph (G : IsoGraph) : IsoGraph := Quotient.lift ... G

@[simp] theorem IsoGraph.lineGraph_mk (G : CGraph) [DecidableEq G.V] :
    IsoGraph.lineGraph ⟦G⟧ = ⟦CGraph.lineGraph G⟧ := ...
```

One and two graph arguments are supported.  Most of these constructions ask for a `DecidableEq` on
the vertex type, which a bare `CGraph` does not supply; when that happens the lift is taken of
`G.canonicalize`, whose vertex type is a `Fin n`, and the `_mk` lemma is a `Quotient.sound` rather
than an `rfl`.  When no instance is needed — `disjUnion` — the graph is used as it stands and the
`_mk` lemma is `rfl`.

## An invariant

On an invariance theorem for a quantity,

```
@[toIsoGraph]
theorem CGraph.girth_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.girth = H.girth := ...
```

generates

```
noncomputable def IsoGraph.girth (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.girth (fun _ _ ⟨i⟩ ↦ CGraph.girth_eq_of_iso i) G

@[simp] theorem IsoGraph.girth_mk (G : CGraph) : IsoGraph.girth ⟦G⟧ = G.girth := rfl
```

The invariance theorem may take extra arguments after the isomorphism, which become extra
arguments of the lifted function (`IsRegularWith k`, `cliqueCount n`, …); it may conclude with an
equation, with an `Iff`, or — for a `Prop`-valued quantity, where the converse follows by symmetry
— with a one-way implication.

## A fact

On any other `CGraph`-level declaration the attribute states the same fact one level up.  Two
conclusions are read as equations of isomorphism classes: an equation `g = h` of graphs, and an
isomorphism `g ≃cg h`.  So

```
@[toIsoGraph paley_five]
def CGraph.paleyFiveIso : CGraph.paley 5 ≃cg CGraph.cycle 5 := ...
```

generates `IsoGraph.paley_five : IsoGraph.paley 5 = IsoGraph.cycle 5`, by `Quotient.sound`.

## Names, the dictionary, and the debug flag

The name of what is generated is read off the declaration and can be overridden by writing it
after the attribute, as `@[toIsoGraph V]`.

Every generated pair is recorded in a dictionary of correspondences — `CGraph.paley ↔
IsoGraph.paley`, `CGraph.compl ↔ IsoGraph.compl`, `CGraph.chromNum ↔ IsoGraph.chromNum` — which
`#isograph_dict` prints, optionally filtered by a substring of either name.  It is also what the
error message reaches for when a fact cannot be stated on the quotient because some construction
in it has no counterpart yet.  The handful of pairs that are written by hand rather than generated
put themselves in the dictionary with `isograph_bridge`.

`set_option trace.toIsoGraph true` prints every definition and theorem the attribute generates,
with its statement.
-/

open Lean Meta Elab

namespace IsoGraph.Attr

initialize registerTraceClass `toIsoGraph

/-- The simp set that translates between the two levels: each lemma states that an `IsoGraph`-level
term applied to `⟦G⟧` is a `CGraph`-level term, and is used from right to left. -/
initialize isoTransferExt : SimpExtension ←
  registerSimpAttr `isoTransfer
    "translation between a `CGraph`-level term and its `IsoGraph`-level counterpart"

/-- `CGraph`, as an expression. -/
private def cgraphE : Expr := mkConst ``CGraph

/-- `IsoGraph`, as an expression. -/
private def isographE : Expr := mkConst ``IsoGraph

/-- The setoid `IsoGraph` is a quotient by, as an expression. -/
private def setoidE : Expr := mkConst ``CGraph.isoSetoid

/-- The isomorphism class of a graph, as an expression. -/
private def mkRep (uCG : Level) (g : Expr) : Expr :=
  mkAppN (mkConst ``Quotient.mk [uCG]) #[cgraphE, setoidE, g]

/-- `Quotient.sound` applied to an isomorphism `iso : a ≃cg b`, giving `⟦a⟧ = ⟦b⟧`.  The two
graphs are passed explicitly: `a ≈ b` is `Nonempty (a ≃cg b)` only after the setoid instance is
unfolded, which is more than unification will do on its own. -/
private def mkSound (uCG : Level) (a b iso : Expr) : MetaM Expr := do
  let isoTy := mkAppN (mkConst ``CGraph.Iso) #[a, b]
  let u ← getLevel isoTy
  let ne := mkAppN (mkConst ``Nonempty.intro [u]) #[isoTy, iso]
  return mkAppN (mkConst ``Quotient.sound [uCG]) #[cgraphE, setoidE, a, b, ne]

/-- Lower-case the leading capital of a `CamelCase` name, so that `IsRegularWith` becomes
`isRegularWith`.  An all-capitals prefix is left alone: `E` stays `E` and `SRG` stays `SRG`, since
those are acronyms rather than words. -/
private def lowerFirst (s : String) : String :=
  match s.toList with
  | c :: d :: cs => if d.isLower then String.ofList (c.toLower :: d :: cs) else s
  | _ => s

/-! ## The dictionary

What the attribute knows about the two levels, kept in an environment extension so that it
survives into the next module: which `IsoGraph`-level constant each `CGraph`-level one corresponds
to, and which lemma bridges them. -/

/-- The four things the attribute generates. -/
inductive Kind
  /-- A construction with no graph arguments, lifted by taking its class. -/
  | construction
  /-- A construction with graph arguments, lifted through an isomorphism congruence. -/
  | operation
  /-- A quantity, lifted through an invariance theorem. -/
  | invariant
  /-- A fact, restated on the quotient. -/
  | fact
  deriving Inhabited, BEq, DecidableEq

/-- One entry of the dictionary: a `CGraph`-level constant, its `IsoGraph`-level counterpart, and
the lemma that connects them (`Name.anonymous` when the two are a statement and its restatement,
which need no bridge). -/
structure Correspondence where
  /-- Which of the four generators produced this entry. -/
  kind : Kind
  /-- The `CGraph`-level constant. -/
  cgraph : Name
  /-- The `IsoGraph`-level constant. -/
  isograph : Name
  /-- The lemma bridging the two, if there is one. -/
  bridge : Name
  /-- The declaration the attribute was written on. -/
  source : Name
  deriving Inhabited

/-- The dictionary of correspondences between the two levels. -/
initialize corrExt : SimplePersistentEnvExtension Correspondence (Array Correspondence) ←
  registerSimplePersistentEnvExtension
    { addEntryFn := Array.push
      addImportedFn := Array.flatten }

/-- Every correspondence the attribute has recorded, in this module and in its imports. -/
def correspondences : CoreM (Array Correspondence) := return corrExt.getState (← getEnv)

/-- Record a correspondence between the two levels. -/
def addCorrespondence (c : Correspondence) : CoreM Unit :=
  modifyEnv (corrExt.addEntry · c)

/-- The `IsoGraph`-level counterpart of a `CGraph`-level constant, if the attribute knows one. -/
def counterpart? (n : Name) : CoreM (Option Name) := do
  return ((← correspondences).find? fun c ↦ c.cgraph == n).map (·.isograph)

/-- Print what has just been generated, under `set_option trace.toIsoGraph true`. -/
private def traceGenerated (what : String) (n : Name) : MetaM Unit := do
  if ← isTracingEnabledFor `toIsoGraph then
    trace[toIsoGraph] "{what} {n} :{indentExpr (← getConstInfo n).type}"

/-! ## A construction

The simplest mode: a `CGraph`-valued definition whose arguments are not graphs is carried across
by taking the class of its value. -/

/-- Generate `IsoGraph.f` and `IsoGraph.f_def` from a `CGraph`-valued definition `CGraph.f`. -/
def generateConstruction (declName : Name) (base? : Option Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let lvls := info.levelParams
  let uCG ← getLevel cgraphE
  forallTelescope info.type fun xs _ => do
    for x in xs do
      if (← inferType x) == cgraphE then
        throwError "toIsoGraph: {declName} takes the graph `{x}` as an argument, so it does not \
          descend to the quotient by itself; tag its isomorphism congruence instead"
    let base := base?.getD (declName.replacePrefix `CGraph Name.anonymous)
    let defName := `IsoGraph ++ base
    if (← getEnv).contains defName then
      throwError "toIsoGraph: {defName} already exists"
    let rep := mkRep uCG (mkAppN (mkConst declName (lvls.map mkLevelParam)) xs)
    let value ← instantiateMVars (← mkLambdaFVars xs rep)
    let type ← instantiateMVars (← mkForallFVars xs isographE)
    let decl := Declaration.defnDecl
      { name := defName, levelParams := lvls, type := type, value := value,
        hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
    addDecl decl
    addDocStringCore defName
      ((← findDocString? (← getEnv) declName).getD s!"`{base}`, as an isomorphism class.")
    if value.getUsedConstants.any (isNoncomputable (← getEnv)) then
      modifyEnv (addNoncomputable · defName)
    else
      compileDecl decl
    -- The bridge, saying that the class of the construction is the construction on classes.
    let defLemma := `IsoGraph ++ (lowerFirst base.getString! ++ "_def").toName
    let lhs := mkAppN (mkConst defName (lvls.map mkLevelParam)) xs
    let stmt ← instantiateMVars (← mkForallFVars xs (← mkEq lhs rep))
    let prf ← instantiateMVars (← mkLambdaFVars xs (← mkEqRefl rep))
    addDecl (.thmDecl { name := defLemma, levelParams := lvls, type := stmt, value := prf })
    inferDefEqAttr defLemma
    addDocStringCore defLemma s!"`IsoGraph.{base}` is the isomorphism class of `{base}`."
    addSimpTheorem (ext := isoTransferExt) (declName := defLemma) (post := true) (inv := false)
      (attrKind := .global) (prio := eval_prio default)
    addCorrespondence
      { kind := .construction, cgraph := declName, isograph := defName,
        bridge := defLemma, source := declName }
    traceGenerated "def" defName
    traceGenerated "theorem" defLemma

/-! ## A construction that takes a graph

Here the attribute goes on the isomorphism congruence rather than on the construction, and builds
the `Quotient.lift` along it.  Most of these constructions ask for a `DecidableEq` on the vertex
type; when the instance cannot be found for a bare graph variable the lift is taken of
`G.canonicalize`, which has one. -/

/-- Generate `IsoGraph.f` and `IsoGraph.f_mk` from an isomorphism congruence for a `CGraph`-valued
construction `CGraph.f` of one or two graphs. -/
def generateConstructionLift (declName : Name) (base? : Option Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let lvls := info.levelParams
  let uCG ← getLevel cgraphE
  let uIG ← getLevel isographE
  forallTelescope info.type fun xs concl => do
    unless concl.isAppOfArity ``CGraph.Iso 2 do
      throwError "toIsoGraph: {declName} does not conclude with an isomorphism of constructions"
    let lhs := concl.appFn!.appArg!
    let rhs := concl.appArg!
    -- The graphs, in the order their isomorphisms are bound.
    let mut pairs : Array (Expr × Expr) := #[]
    for x in xs do
      let t ← inferType x
      if t.isAppOfArity ``CGraph.Iso 2 then
        pairs := pairs.push (t.appFn!.appArg!, t.appArg!)
    let n := pairs.size
    unless n == 1 || n == 2 do
      throwError "toIsoGraph: {declName} relates {n} pairs of graphs; only one and two are lifted"
    let some cname := lhs.getAppFn.constName? |
      throwError "toIsoGraph: the conclusion of {declName} is not an isomorphism between two \
        applications of a construction"
    unless rhs.getAppFn.constName? == some cname do
      throwError "toIsoGraph: the two sides of {declName} are not the same construction"
    let base := base?.getD (cname.replacePrefix `CGraph Name.anonymous)
    let defName := `IsoGraph ++ base
    if (← getEnv).contains defName then
      throwError "toIsoGraph: {defName} already exists"
    let names ← pairs.mapM fun (a, _) ↦ return (← a.fvarId!.getDecl).userName
    withLocalDeclsD (names.map fun nm ↦ (nm, fun _ ↦ pure cgraphE)) fun gs => do
      /- Apply the construction to the graphs — as they stand if its instance arguments can be
      found for them, and to their canonical representatives if not. -/
      let build (canon : Bool) : MetaM (Option Expr) := do
        let gvals ← if canon then gs.mapM fun g ↦ mkAppM ``CGraph.canonicalize #[g] else pure gs
        let mut vals : Array Expr := #[]
        for k in [0:xs.size] do
          let x := xs[k]!
          if let some j := pairs.findIdx? (·.1 == x) then
            vals := vals.push gvals[j]!
          else
            let d ← x.fvarId!.getDecl
            if d.binderInfo == .instImplicit then
              match ← synthInstance? (d.type.replaceFVars (xs.extract 0 k) vals) with
              | some inst => vals := vals.push inst
              | none => return none
            else
              vals := vals.push x
        return some (lhs.replaceFVars xs vals)
      let (canon, body) ← match ← build false with
        | some b => pure (false, b)
        | none => match ← build true with
          | some b => pure (true, b)
          | none => throwError "toIsoGraph: cannot apply `{cname}` to a canonical representative"
      if xs.any fun x ↦ body.containsFVar x.fvarId! then
        throwError "toIsoGraph: `{cname}` takes an argument that is not a graph, so it does not \
          lift by itself"
      -- The lift, and its side condition.
      let f ← mkLambdaFVars gs (mkRep uCG body)
      let liftApp := if n == 1 then
          mkAppN (mkConst ``Quotient.lift [uCG, uIG]) #[cgraphE, isographE, setoidE, f]
        else
          mkAppN (mkConst ``Quotient.lift₂ [uCG, uCG, uIG])
            #[cgraphE, cgraphE, isographE, setoidE, setoidE, f]
      let cTy := (← whnf (← inferType liftApp)).bindingDomain!
      let cond ← forallTelescope cTy fun args tgt => do
        /- The last `n` arguments are the hypotheses `a ≈ b`, one for each graph, and they name the
        two graphs they are about. -/
        let hs := args.extract (2 * n) (3 * n)
        let sides ← hs.mapM fun h ↦ do
          let t ← whnf (← inferType h)
          return (t.appArg!.appFn!.appArg!, t.appArg!.appArg!)
        let rec go (j : Nat) (isos : Array Expr) : MetaM Expr := do
          if j < n then
            let (a, b) := sides[j]!
            let isoTy := mkAppN (mkConst ``CGraph.Iso) #[a, b]
            let u ← getLevel isoTy
            withLocalDeclD `i isoTy fun i => do
              let inner ← go (j + 1) (isos.push i)
              return mkAppN (mkConst ``Nonempty.elim [u])
                #[isoTy, tgt, hs[j]!, ← mkLambdaFVars #[i] inner]
          else
            /- `canonicalize` is inserted on both sides, so the isomorphism has to be conjugated
            by `isoCanonicalize` before the congruence will take it. -/
            let isoArgs ← (Array.range n).mapM fun j => do
              if canon then
                let (a, b) := sides[j]!
                let ca ← mkAppM ``CGraph.isoCanonicalize #[a]
                let cb ← mkAppM ``CGraph.isoCanonicalize #[b]
                mkAppM ``RelIso.trans
                  #[← mkAppM ``RelIso.symm #[ca], ← mkAppM ``RelIso.trans #[isos[j]!, cb]]
              else pure isos[j]!
            mkSound uCG (body.replaceFVars gs (sides.map (·.1)))
              (body.replaceFVars gs (sides.map (·.2))) (← mkAppM declName isoArgs)
        mkLambdaFVars args (← go 0 #[])
      withLocalDeclsD (names.map fun nm ↦ (nm, fun _ ↦ pure isographE)) fun qs => do
        let value ← instantiateMVars (← mkLambdaFVars qs (mkAppN liftApp (#[cond] ++ qs)))
        let type ← instantiateMVars (← mkForallFVars qs isographE)
        let decl := Declaration.defnDecl
          { name := defName, levelParams := lvls, type := type, value := value,
            hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
        addDecl decl
        addDocStringCore defName
          ((← findDocString? (← getEnv) cname).getD s!"`{base}`, on isomorphism classes.")
        if f.getUsedConstants.any (isNoncomputable (← getEnv)) then
          modifyEnv (addNoncomputable · defName)
        else
          compileDecl decl
      /- The `_mk` lemma, saying that the lift agrees with the construction on representatives.
      Its binders are those of the construction itself, so that it carries the `DecidableEq`
      instances the construction asks for. -/
      let cInfo ← getConstInfo cname
      let mkName := `IsoGraph ++ (lowerFirst base.getString! ++ "_mk").toName
      forallTelescope cInfo.type fun ys _ => do
        let ygraphs ← ys.filterM fun y ↦ return (← inferType y) == cgraphE
        unless ygraphs.size == n do
          throwError "toIsoGraph: {cname} takes {ygraphs.size} graphs but {declName} relates {n}"
        let lhs' := mkAppN (mkConst defName (lvls.map mkLevelParam)) (ygraphs.map (mkRep uCG))
        let cApp := mkAppN (mkConst cname (cInfo.levelParams.map mkLevelParam)) ys
        let rhs' := mkRep uCG cApp
        let prf ← if canon then
            let isoArgs ← ygraphs.mapM fun y ↦ do
              mkAppM ``RelIso.symm #[← mkAppM ``CGraph.isoCanonicalize #[y]]
            mkSound uCG (body.replaceFVars gs ygraphs) cApp (← mkAppM declName isoArgs)
          else mkEqRefl rhs'
        let stmt ← instantiateMVars (← mkForallFVars ys (← mkEq lhs' rhs'))
        let prf ← instantiateMVars (← mkLambdaFVars ys prf)
        addDecl (.thmDecl
          { name := mkName, levelParams := (lvls ++ cInfo.levelParams).eraseDups,
            type := stmt, value := prf })
        inferDefEqAttr mkName
      addDocStringCore mkName s!"`IsoGraph.{base}` agrees with `{base}` on representatives."
      addSimpTheorem (ext := simpExtension) (declName := mkName) (post := true) (inv := false)
        (attrKind := .global) (prio := eval_prio default)
      addSimpTheorem (ext := isoTransferExt) (declName := mkName) (post := true) (inv := false)
        (attrKind := .global) (prio := eval_prio default)
      addCorrespondence
        { kind := .operation, cgraph := cname, isograph := defName,
          bridge := mkName, source := declName }
      traceGenerated "def" defName
      traceGenerated "theorem" mkName

/-! ## An invariant

The original mode: a quantity that respects isomorphism descends to the quotient, and the
invariance theorem is the side condition of the `Quotient.lift`. -/

/-- The three shapes an invariance statement can take: `f G … = f H …`, `f G … ↔ f H …`, and
`f G … → f H …`. -/
private inductive Shape
  | eq | iff | imp
  deriving Inhabited, BEq

/-- Split an invariance statement into its two sides. -/
private def splitStatement (body : Expr) : MetaM (Expr × Expr × Expr × Shape) := do
  if body.isAppOfArity ``Eq 3 then
    return (body.appFn!.appFn!.appArg!, body.appFn!.appArg!, body.appArg!, .eq)
  if body.isAppOfArity ``Iff 2 then
    return (mkSort .zero, body.appFn!.appArg!, body.appArg!, .iff)
  match body with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then
      throwError "toIsoGraph: the conclusion must be an equation, an `Iff`, or an implication"
    return (mkSort .zero, d, b, .imp)
  | _ =>
    throwError "toIsoGraph: the conclusion must be an equation, an `Iff`, or an implication"

/-- Introduce the binders of an invariance statement, stopping short of the conclusion.  The
conclusion is `f G … = f H …`, `f G … ↔ f H …` or `f G … → f H …`, and the last of these is itself
a binder, so ordinary `forallTelescope` would swallow it: a binder is taken to be part of the
conclusion once it is unused and mentions one of the two graphs. -/
private partial def telescopeInv {α} (ty : Expr) (xs : Array Expr) (gs? : Option (Expr × Expr))
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  match ty with
  | .forallE n d b bi =>
    if let some (g, h) := gs? then
      if !b.hasLooseBVar 0 && (d.containsFVar g.fvarId! || d.containsFVar h.fvarId!) then
        return ← k xs ty
    let gs?' := if d.isAppOfArity ``CGraph.Iso 2 then some (d.appFn!.appArg!, d.appArg!) else gs?
    withLocalDecl n bi d fun x ↦ telescopeInv (b.instantiate1 x) (xs.push x) gs?' k
  | _ => k xs ty

/-- Build the side condition of the `Quotient.lift`, a proof of `∀ a b, a ≈ b → f a = f b`, from
the invariance theorem `thm` whose binders are `xs` with `G = xs[g]`, `H = xs[h]` and the
isomorphism `xs[i]`. -/
private def mkLiftCond (cTy : Expr) (thm : Expr) (xs : Array Expr) (gi hi ii : Nat)
    (shape : Shape) : MetaM Expr :=
  forallTelescope cTy fun args tgt => do
    let a := args[0]!
    let b := args[1]!
    let hEq := args[2]!
    let isoTy := mkAppN (mkConst ``CGraph.Iso) #[a, b]
    withLocalDeclD `i isoTy fun i => do
      /- `thm` applied with `G := x`, `H := y` and the isomorphism `e`. -/
      let apply (x y e : Expr) : Expr :=
        mkAppN thm <| xs.mapIdx fun k z ↦
          if k == gi then x else if k == hi then y else if k == ii then e else z
      let body ← match shape with
        | .eq => pure (apply a b i)
        | .iff => mkAppM ``propext #[apply a b i]
        | .imp => do
            let back ← mkAppM ``RelIso.symm #[i]
            mkAppM ``propext #[← mkAppM ``Iff.intro #[apply a b i, apply b a back]]
      let f ← mkLambdaFVars #[i] body
      let u ← getLevel isoTy
      let e := mkAppN (mkConst ``Nonempty.elim [u]) #[isoTy, tgt, hEq, f]
      mkLambdaFVars args e

/-- Generate `IsoGraph.f` and `IsoGraph.f_mk` from an invariance theorem for `CGraph.f`. -/
def generateLift (thmName : Name) (base? : Option Name) : MetaM Unit := do
  let info ← getConstInfo thmName
  let lvls := info.levelParams
  let thm := mkConst thmName (lvls.map mkLevelParam)
  telescopeInv info.type #[] none fun xs body => do
    -- Locate the isomorphism binder, and with it the two graphs.
    let mut ii? := none
    for k in [0:xs.size] do
      if (← inferType xs[k]!).isAppOfArity ``CGraph.Iso 2 then
        ii? := some k
        break
    let some ii := ii? |
      throwError "toIsoGraph: {thmName} takes no isomorphism `G ≃cg H`, so it is not an \
        invariance statement"
    let isoTy ← inferType xs[ii]!
    let gv := isoTy.appFn!.appArg!
    let hv := isoTy.appArg!
    let some gi := xs.idxOf? gv | throwError "toIsoGraph: {thmName} does not bind its graphs"
    let some hi := xs.idxOf? hv | throwError "toIsoGraph: {thmName} does not bind its graphs"
    let extras := xs.filter fun x ↦ x != gv && x != hv && x != xs[ii]!
    for x in extras do
      if (← inferType x).containsFVar gv.fvarId! || (← inferType x).containsFVar hv.fvarId! then
        throwError "toIsoGraph: the argument {x} of {thmName} mentions the graph"
    -- Split the conclusion, and check that the two sides really are the same function of the two
    -- graphs.
    let (ty, lhs, rhs, shape) ← splitStatement body
    unless ← isDefEq (lhs.replaceFVar gv hv) rhs do
      throwError "toIsoGraph: the two sides of {thmName} are not the same function of `{gv}` and \
        `{hv}`"
    if ty.containsFVar gv.fvarId! || ty.containsFVar hv.fvarId! then
      throwError "toIsoGraph: the value of {thmName} has a type that mentions the graph"
    -- The name to generate under.
    let base ← match base? with
      | some b => pure b
      | none => match lhs.getAppFn with
        | .const c _ => pure c.getString!.toName
        | _ => throwError "toIsoGraph: cannot guess a name for the lifted function; write it \
            after the attribute, as `@[toIsoGraph girth]`"
    let defName := `IsoGraph ++ base
    if (← getEnv).contains defName then
      throwError "toIsoGraph: {defName} already exists"
    -- The lift itself.
    let liftF ← mkLambdaFVars #[gv] lhs
    let uCG ← getLevel cgraphE
    let uTy ← getLevel ty
    let liftApp := mkAppN (mkConst ``Quotient.lift [uCG, uTy]) #[cgraphE, ty, setoidE, liftF]
    let cTy := (← whnf (← inferType liftApp)).bindingDomain!
    let cond ← mkLiftCond cTy thm xs gi hi ii shape
    withLocalDeclD `G isographE fun q => do
      let value ← instantiateMVars (← mkLambdaFVars (#[q] ++ extras)
        (mkAppN liftApp #[cond, q]))
      let type ← instantiateMVars (← mkForallFVars (#[q] ++ extras) ty)
      let doc ← match lhs.getAppFn with
        | .const c _ => pure ((← findDocString? (← getEnv) c).getD s!"`{base}`, on isomorphism \
            classes.")
        | _ => pure s!"`{base}`, on isomorphism classes."
      let decl := Declaration.defnDecl
        { name := defName, levelParams := lvls, type := type, value := value,
          hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
      addDecl decl
      addDocStringCore defName doc
      -- Most of these quantities are noncomputable, and the lift is noncomputable exactly when
      -- the quantity is: the invariance proof carries no data.
      if liftF.getUsedConstants.any (isNoncomputable (← getEnv)) then
        modifyEnv (addNoncomputable · defName)
      else
        compileDecl decl
      -- The `_mk` lemma, saying that the lift agrees with the original on representatives.
      let mkName := `IsoGraph ++ (lowerFirst base.getString! ++ "_mk").toName
      withLocalDeclD `G cgraphE fun g => do
        let rep := mkRep uCG g
        let lifted := mkAppN (mkConst defName (lvls.map mkLevelParam)) (#[rep] ++ extras)
        let rhs' := lhs.replaceFVar gv g
        let stmt ← instantiateMVars (← mkForallFVars (#[g] ++ extras) (← mkEq lifted rhs'))
        let prf ← instantiateMVars (← mkLambdaFVars (#[g] ++ extras) (← mkEqRefl rhs'))
        addDecl (.thmDecl { name := mkName, levelParams := lvls, type := stmt, value := prf })
        inferDefEqAttr mkName
      addDocStringCore mkName s!"`IsoGraph.{base}` agrees with `{base}` on representatives."
      addSimpTheorem (ext := simpExtension) (declName := mkName) (post := true) (inv := false)
        (attrKind := .global) (prio := eval_prio default)
      addSimpTheorem (ext := isoTransferExt) (declName := mkName) (post := true) (inv := false)
        (attrKind := .global) (prio := eval_prio default)
      if let .const c _ := lhs.getAppFn then
        addCorrespondence
          { kind := .invariant, cgraph := c, isograph := defName,
            bridge := mkName, source := thmName }
      traceGenerated "def" defName
      traceGenerated "theorem" mkName
    pure ()

/-! ## A fact

The last mode.  A `CGraph`-level statement is turned into an `IsoGraph`-level one by rewriting
with the `@[isoTransfer]` lemmas backwards, which leaves every graph appearing only as `⟦G⟧`, and
then reading `⟦G⟧` as a variable of type `IsoGraph`.  The original theorem proves the result after
a `Quotient.ind` for each graph variable, transported along the very rewrite that produced the
statement — a transport that is `rfl` for the bridges that are `rfl`, and a real cast for the ones,
like `compl_mk`, that are not. -/

/-- The transfer simp set, turned around: these rewrite a `CGraph`-level term into the
`IsoGraph`-level term that reduces to it. -/
private def reversedTransfer : MetaM SimpTheorems := do
  let mut rev : SimpTheorems := {}
  for o in (← isoTransferExt.getTheorems).lemmaNames do
    if let .decl n _ _ := o then
      rev ← rev.addConst n (inv := true)
  return rev

/-- The simp context the translation runs in. -/
private def transferCtx (rev : SimpTheorems) : MetaM Simp.Context := do
  Simp.mkContext (config := { decide := false }) (simpTheorems := #[rev])
    (congrTheorems := ← getSimpCongrTheorems)

/-- Cast a proof of a `CGraph`-level statement to the `IsoGraph`-level statement that the transfer
set rewrites it to. -/
private def transport (rev : SimpTheorems) (e : Expr) : MetaM Expr := do
  let r ← simp (← instantiateMVars (← inferType e)) (← transferCtx rev)
  match r.1.proof? with
  | some h => mkEqMP h e
  | none => return e

/-- Complain that a statement is still about `CGraph`s, naming the constructions that have no
counterpart on the quotient — which is almost always what has gone wrong. -/
private def throwStillCGraph {α} (stmt : Expr) : MetaM α := do
  let mut missing : Array Name := #[]
  for c in stmt.getUsedConstants do
    if c.getRoot == `CGraph && (← counterpart? c).isNone && !missing.contains c then
      missing := missing.push c
  let hint := if missing.isEmpty then m!"" else
    m!"\nthe dictionary has no `IsoGraph`-level counterpart for \
      {MessageData.joinSep (missing.toList.map (m!"`{·}`")) ", "}"
  throwError "toIsoGraph: cannot state{indentExpr stmt}\nat the level of isomorphism classes; it \
    still mentions `CGraph`{hint}"

/-- Rewrite a `CGraph`-level expression to `IsoGraph` level: rewrite backwards with the transfer
lemmas, then read each `⟦gᵢ⟧` as the corresponding `IsoGraph` variable.  Fails if a graph is left
over, which is what happens when the statement uses a graph in a way that does not descend to the
quotient.

`olds` are the binders of the original statement and `reps` what each of them stands for in it —
itself, or, in canonical mode, its `canonicalize`. -/
private def translateExpr (rev : SimpTheorems) (olds reps news : Array Expr)
    (graphs : Array Bool) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars (← simp (← instantiateMVars e) (← transferCtx rev)).1.expr
  -- `⟦gᵢ⟧ ↦ Gᵢ`
  let e := e.replace fun sub ↦ do
    guard (sub.isAppOfArity ``Quotient.mk 3 && sub.appFn!.appArg! == setoidE)
    let some j := reps.idxOf? sub.appArg! | none
    guard (j < news.size && graphs[j]!)
    some news[j]!
  -- every other variable keeps its meaning
  let mut keepOld := #[]
  let mut keepNew := #[]
  for j in [0:news.size] do
    if graphs[j]! then
      if e.containsFVar olds[j]!.fvarId! then
        throwError "toIsoGraph: cannot state{indentExpr e}\nat the level of isomorphism classes; \
          the graph `{olds[j]!}` is used in a way that does not descend to the quotient"
    else
      keepOld := keepOld.push olds[j]!
      keepNew := keepNew.push news[j]!
  return e.replaceFVars keepOld keepNew

/-- Generate the `IsoGraph`-level counterpart of a `CGraph`-level fact.  `forceSimp` makes the
result a `simp` lemma even when the original is not one. -/
def generateFact (thmName : Name) (base? : Option Name) (forceSimp : Bool) : MetaM Unit := do
  let info ← getConstInfo thmName
  let lvls := info.levelParams
  let thm := mkConst thmName (lvls.map mkLevelParam)
  let rev ← reversedTransfer
  let uCG ← getLevel cgraphE
  let uIG ← getLevel isographE
  /- Drop the `CGraph` namespace but keep everything else, so that a fact stated for dot notation,
  such as `CGraph.IsSRGWith.degSequence`, keeps its dot notation on the other side too. -/
  let base := base?.getD (thmName.replacePrefix `CGraph Name.anonymous)
  let newName := `IsoGraph ++ base
  if (← getEnv).contains newName then
    throwError "toIsoGraph: {newName} already exists"
  /- Facts about products and complements ask for `[DecidableEq G.V]`, which a bare graph variable
  has no way to supply.  When some instance binder mentions a graph, run in *canonical mode*: each
  graph binder `G` is instantiated at `G.canonicalize`, whose vertex type is a `Fin n` and so has
  every instance, the instance binders are then synthesised and dropped, and the `⟦G.canonicalize⟧`
  that results is turned back into `⟦G⟧` by `mk_canonicalize` on the way out. -/
  let canon ← forallTelescope info.type fun xs _ ↦ do
    let mut gs : Array FVarId := #[]
    for x in xs do
      if (← inferType x) == cgraphE then gs := gs.push x.fvarId!
    xs.anyM fun x ↦ do
      let d ← x.fvarId!.getDecl
      return d.binderInfo == .instImplicit && gs.any d.type.containsFVar
  /- Walk the binders of the original statement.  `olds` are the ones that survive the translation
  and `reps` what each of them stands for in the statement — itself, or its canonicalisation;
  `args` are all of them, in order, ready to be fed back to the original theorem. -/
  let rec tele (fuel : Nat) (ty : Expr) (args olds reps : Array Expr) (graphs : Array Bool) :
      MetaM Unit := do
    match fuel, ty with
    | 0, _ => throwError "toIsoGraph: {thmName} has too many binders"
    | fuel + 1, .forallE nm dom bd bi =>
      if dom == cgraphE then
        withLocalDecl nm bi cgraphE fun g ↦ do
          let rep ← if canon then mkAppM ``CGraph.canonicalize #[g] else pure g
          tele fuel (bd.instantiate1 rep) (args.push rep) (olds.push g) (reps.push rep)
            (graphs.push true)
      else if bi == .instImplicit &&
          (olds.zip graphs).any (fun (v, isGraph) ↦ isGraph && dom.containsFVar v.fvarId!) then
        let some inst ← synthInstance? dom |
          throwError "toIsoGraph: cannot synthesise{indentExpr dom}\nfor a canonical representative"
        tele fuel (bd.instantiate1 inst) (args.push inst) olds reps graphs
      else
        withLocalDecl nm bi dom fun y ↦
          tele fuel (bd.instantiate1 y) (args.push y) (olds.push y) (reps.push y)
            (graphs.push false)
    | _, body =>
      /- A conclusion `g = h` between two `CGraph`s becomes one between their classes, and so does
      an isomorphism `g ≃cg h`; `congrArg` and `Quotient.sound` supply the two.  Everything else
      about the statement is rewriting. -/
      let isEqCG := body.isAppOfArity ``Eq 3 && body.appFn!.appFn!.appArg! == cgraphE
      let isIsoCG := body.isAppOfArity ``CGraph.Iso 2
      let body := if isEqCG || isIsoCG then
          mkAppN (mkConst ``Eq [uIG])
            #[isographE, mkRep uCG body.appFn!.appArg!, mkRep uCG body.appArg!]
        else body
      /- Introduce the translated binders, one at a time: a graph becomes an `IsoGraph`, and every
      other binder keeps its name and its binder info, with its type translated. -/
      let rec loop (i : Nat) (news : Array Expr) : MetaM Unit := do
        if h : i < olds.size then
          let decl ← olds[i].fvarId!.getDecl
          if graphs[i]! then
            withLocalDecl decl.userName decl.binderInfo isographE fun q ↦
              loop (i + 1) (news.push q)
          else
            let ty ← translateExpr rev olds reps news graphs decl.type
            withLocalDecl decl.userName decl.binderInfo ty fun y ↦
              loop (i + 1) (news.push y)
        else
          let newBody ← translateExpr rev olds reps news graphs body
          let stmt ← instantiateMVars (← mkForallFVars news newBody)
          if stmt.getUsedConstants.any (·.getRoot == `CGraph) then
            throwStillCGraph stmt
          /- The proof: peel the binders off again, inserting a `Quotient.ind` at each graph.  What
          is left is the original theorem, applied to the representatives.  In canonical mode the
          `Quotient.ind` lands on `⟦g.canonicalize⟧` and `mk_canonicalize` moves it to `⟦g⟧`. -/
          let rec prove (j : Nat) (subst substOld : Array Expr) : MetaM Expr := do
            if hj : j < olds.size then
              if graphs[j]! then
                let tail ← mkForallFVars (news.extract (j + 1) news.size) newBody
                let motive := (← mkLambdaFVars #[news[j]!] tail).replaceFVars
                  (news.extract 0 j) subst
                withLocalDeclD `g cgraphE fun g ↦ do
                  let rep := reps[j]!.replaceFVars #[olds[j]!] #[g]
                  let inner ← prove (j + 1) (subst.push (mkRep uCG rep)) (substOld.push g)
                  let inner ← if canon then do
                      let iso ← mkAppM ``RelIso.symm #[← mkAppM ``CGraph.isoCanonicalize #[g]]
                      mkEqMP (← mkAppM ``congrArg #[motive, ← mkSound uCG rep g iso]) inner
                    else pure inner
                  return mkAppN (mkConst ``Quotient.ind [uCG])
                    #[cgraphE, setoidE, motive, ← mkLambdaFVars #[g] inner]
              else
                let decl ← news[j]!.fvarId!.getDecl
                let ty := decl.type.replaceFVars (news.extract 0 j) subst
                withLocalDecl decl.userName decl.binderInfo ty fun y ↦ do
                  let inner ← prove (j + 1) (subst.push y) (substOld.push y)
                  mkLambdaFVars #[y] inner
            else
              let e := mkAppN thm (args.map (·.replaceFVars olds substOld))
              let base ← if isEqCG then
                  withLocalDeclD `g cgraphE fun g ↦ do
                    let q ← mkLambdaFVars #[g] (mkRep uCG g)
                    mkAppM ``congrArg #[q, e]
                else if isIsoCG then do
                  let isoTy ← inferType e
                  let u ← getLevel isoTy
                  let ne := mkAppN (mkConst ``Nonempty.intro [u]) #[isoTy, e]
                  pure (mkAppN (mkConst ``Quotient.sound [uCG])
                    #[cgraphE, setoidE, isoTy.appFn!.appArg!, isoTy.appArg!, ne])
                else pure e
              transport rev base
          let prf ← instantiateMVars (← prove 0 #[] #[])
          addDecl (.thmDecl { name := newName, levelParams := lvls, type := stmt, value := prf })
          inferDefEqAttr newName
          if let some doc ← findDocString? (← getEnv) thmName then
            addDocStringCore newName doc
          if forceSimp || (← getSimpTheorems).isLemma (.decl thmName) then
            addSimpTheorem (ext := simpExtension) (declName := newName) (post := true)
              (inv := false) (attrKind := .global) (prio := eval_prio default)
          addCorrespondence
            { kind := .fact, cgraph := thmName, isograph := newName,
              bridge := Name.anonymous, source := thmName }
          traceGenerated "theorem" newName
      loop 0 #[]
  tele 1000 info.type #[] #[] #[] #[]

/-! ## The attribute -/

/-- `@[toIsoGraph]` carries a `CGraph`-level declaration across to `IsoGraph`, the quotient by
isomorphism.

On a `CGraph`-valued definition with no graph arguments it generates the same construction on
isomorphism classes, together with the lemma bridging the two.  On an isomorphism congruence for a
construction that does take graphs it generates the `Quotient.lift` along the congruence, and the
simp lemma that the lift agrees with the construction on representatives.  On an
isomorphism-invariance theorem for a quantity it generates the quantity on isomorphism classes, in
the same way.  The name of what is generated is read off the statement; `@[toIsoGraph f]`
overrides it.

On any other `CGraph`-level declaration it generates the `IsoGraph`-level statement of the same
fact, proved from the original; an equation of graphs and an isomorphism both become an equation
of isomorphism classes.  It is `@[simp]` exactly when the original is, so write `@[simp,
toIsoGraph]` and not the other way round — or `@[toIsoGraph simp]`, which makes the generated
statement a `simp` lemma without making the `CGraph`-level one into one.  That is what an
isomorphism wants: `CGraph.Iso.cartesianProductEmptyOne` is a definition and cannot be `simp`,
while `G □g empty 1 = G` should be. -/
syntax (name := toIsoGraph) "toIsoGraph" (ppSpace &"simp")? (ppSpace ident)? : attr

/-- Does this statement bind an isomorphism, and so ask for a `Quotient.lift`? -/
private def isInvariance (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ ↦
    xs.anyM fun x ↦ return (← inferType x).isAppOfArity ``CGraph.Iso 2

/-- Is this a `CGraph`-valued definition, and so a construction to be carried across? -/
private def isConstruction (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body ↦ return body == cgraphE

/-- Does this statement conclude with an isomorphism between two constructions? -/
private def isCongruence (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body ↦ return body.isAppOfArity ``CGraph.Iso 2

initialize registerBuiltinAttribute {
  name := `toIsoGraph
  descr := "generate the `IsoGraph`-level counterpart of a `CGraph`-level declaration"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    unless kind == .global do
      throwError "toIsoGraph: only a global attribute"
    let (forceSimp, base?) ← show CoreM (Bool × Option Name) from match stx with
      | `(attr| toIsoGraph) => pure (false, none)
      | `(attr| toIsoGraph simp) => pure (true, none)
      | `(attr| toIsoGraph $i:ident) => pure (false, some i.getId)
      | `(attr| toIsoGraph simp $i:ident) => pure (true, some i.getId)
      | _ => throwError "toIsoGraph: unexpected syntax"
    MetaM.run' do
      let type := (← getConstInfo decl).type
      if ← isConstruction type then
        /- The other three modes generate a lift and its bridge lemma, and the bridge lemma is
        `simp` already; there is nothing left for `simp` to name. -/
        if forceSimp then
          throwError "toIsoGraph: `simp` applies to a fact, and {decl} is a construction"
        generateConstruction decl base?
      else if ← isInvariance type then
        if forceSimp then
          throwError "toIsoGraph: `simp` applies to a fact, and {decl} is an isomorphism lift"
        if ← isCongruence type then
          generateConstructionLift decl base?
        else
          generateLift decl base?
      else
        generateFact decl base? forceSimp
}

/-! ## The dictionary by hand

Two pairs are written out rather than generated — `V`, whose `CGraph`-level side is a `Fintype.card`
and not a constant of its own, and `compl`, which carries the `Compl` instance and so has to be
stated with `ᶜ`.  This command puts them in the dictionary all the same. -/

open Lean.Elab.Command in
/-- `isograph_bridge CGraph.compl ↦ IsoGraph.compl via IsoGraph.compl_mk` records a
correspondence between the two levels that is written by hand rather than generated by
`@[toIsoGraph]`, so that `#isograph_dict` and the attribute's error messages know about it. -/
elab "isograph_bridge " c:ident " ↦ " i:ident " via " b:ident : command => do
  let cn ← liftCoreM <| realizeGlobalConstNoOverload c
  let inm ← liftCoreM <| realizeGlobalConstNoOverload i
  let bn ← liftCoreM <| realizeGlobalConstNoOverload b
  let kind ← liftTermElabM <| MetaM.run' do
    forallTelescope (← getConstInfo cn).type fun xs body => do
      if body != cgraphE then return Kind.invariant
      if ← xs.anyM fun x ↦ return (← inferType x) == cgraphE then
        return Kind.operation
      return Kind.construction
  liftCoreM <| addCorrespondence
    { kind := kind, cgraph := cn, isograph := inm, bridge := bn, source := bn }

/-! ## Inspecting the dictionary -/

open Lean.Elab.Command in
/-- `#isograph_dict` lists every correspondence between the two levels that `@[toIsoGraph]` has
recorded: the constructions, the operations, the invariants and the facts, each with the lemma
that bridges them.  `#isograph_dict compl` keeps only the entries whose name contains `compl`. -/
elab "#isograph_dict" filter:(ppSpace ident)? : command => do
  let sel := filter.map (·.getId.toString)
  let keep (c : Correspondence) : Bool := match sel with
    | none => true
    | some s => ((c.cgraph.toString ++ " " ++ c.isograph.toString).splitOn s).length > 1
  let all := (corrExt.getState (← getEnv)).filter keep
  let mut msg : MessageData := m!""
  let mut total := 0
  for (kind, title) in [(Kind.construction, "constructions"), (Kind.operation, "operations"),
      (Kind.invariant, "invariants"), (Kind.fact, "facts")] do
    let cs := (all.filter (·.kind == kind)).qsort fun a b ↦ a.cgraph.toString < b.cgraph.toString
    if cs.isEmpty then continue
    total := total + cs.size
    msg := msg ++ m!"{title} ({cs.size})\n"
    for c in cs do
      let bridge := if c.bridge.isAnonymous then m!"" else m!"    via {c.bridge}"
      msg := msg ++ m!"  {c.cgraph} ↦ {c.isograph}{bridge}\n"
  if total == 0 then
    logInfo m!"no correspondences"
  else
    logInfo msg

end IsoGraph.Attr
