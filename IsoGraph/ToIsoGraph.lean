import IsoGraph.Basic

/-!
# The `@[toIsoGraph]` attribute

Every quantity in this library is defined twice: once on `CGraph`, where a concrete graph can be
computed with, and once on `IsoGraph`, where it is the `Quotient.lift` of the first along a proof
of isomorphism invariance.  The second copy is mechanical, and this file makes it automatic.

Tagging an invariance theorem

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
— with a one-way implication.  The name of the generated function is read off the statement, and
can be overridden by writing it after the attribute, as `@[toIsoGraph V]`.

The `_mk` lemma is also tagged `@[isoTransfer]`, which is the simp set used to rewrite a
`CGraph`-level statement into its `IsoGraph`-level counterpart.
-/

open Lean Meta Elab

namespace IsoGraph.Attr

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

/-- Lower-case the leading capital of a `CamelCase` name, so that `IsRegularWith` becomes
`isRegularWith`.  An all-capitals prefix is left alone: `E` stays `E` and `SRG` stays `SRG`, since
those are acronyms rather than words. -/
private def lowerFirst (s : String) : String :=
  match s.toList with
  | c :: d :: cs => if d.isLower then String.ofList (c.toLower :: d :: cs) else s
  | _ => s

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
        let rep := mkAppN (mkConst ``Quotient.mk [uCG]) #[cgraphE, setoidE, g]
        let lifted := mkAppN (mkConst defName (lvls.map mkLevelParam)) (#[rep] ++ extras)
        let rhs' := lhs.replaceFVar gv g
        let stmt ← instantiateMVars (← mkForallFVars (#[g] ++ extras) (← mkEq lifted rhs'))
        let prf ← instantiateMVars (← mkLambdaFVars (#[g] ++ extras) (← mkEqRefl rhs'))
        addDecl (.thmDecl { name := mkName, levelParams := lvls, type := stmt, value := prf })
      addDocStringCore mkName s!"`IsoGraph.{base}` agrees with `{base}` on representatives."
      addSimpTheorem (ext := simpExtension) (declName := mkName) (post := true) (inv := false)
        (attrKind := .global) (prio := eval_prio default)
      addSimpTheorem (ext := isoTransferExt) (declName := mkName) (post := true) (inv := false)
        (attrKind := .global) (prio := eval_prio default)
    pure ()

/-! ## Transferring a fact

The second job of the attribute.  A `CGraph`-level statement is turned into an `IsoGraph`-level
one by rewriting with the `@[isoTransfer]` lemmas backwards, which leaves every graph appearing
only as `⟦G⟧`, and then reading `⟦G⟧` as a variable of type `IsoGraph`.  Because each of those
lemmas holds by `rfl`, the translated statement is definitionally the original, and the original
theorem proves it after a `Quotient.ind` for each graph variable. -/

/-- The transfer simp set, turned around: these rewrite a `CGraph`-level term into the
`IsoGraph`-level term that reduces to it. -/
private def reversedTransfer : MetaM SimpTheorems := do
  let mut rev : SimpTheorems := {}
  for o in (← isoTransferExt.getTheorems).lemmaNames do
    if let .decl n _ _ := o then
      rev ← rev.addConst n (inv := true)
  return rev

/-- Rewrite a `CGraph`-level expression to `IsoGraph` level: rewrite backwards with the transfer
lemmas, then read each `⟦gᵢ⟧` as the corresponding `IsoGraph` variable.  Fails if a graph is left
over, which is what happens when the statement uses a graph in a way that does not descend to the
quotient. -/
private def translateExpr (rev : SimpTheorems) (olds news : Array Expr)
    (graphs : Array Bool) (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (config := { decide := false }) (simpTheorems := #[rev])
    (congrTheorems := ← getSimpCongrTheorems)
  let e ← instantiateMVars (← simp (← instantiateMVars e) ctx).1.expr
  -- `⟦gᵢ⟧ ↦ Gᵢ`
  let e := e.replace fun sub ↦ do
    guard (sub.isAppOfArity ``Quotient.mk 3 && sub.appFn!.appArg! == setoidE)
    let some j := olds.idxOf? sub.appArg! | none
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

/-- Generate the `IsoGraph`-level counterpart of a `CGraph`-level fact. -/
def generateFact (thmName : Name) (base? : Option Name) : MetaM Unit := do
  let info ← getConstInfo thmName
  let lvls := info.levelParams
  let thm := mkConst thmName (lvls.map mkLevelParam)
  let rev ← reversedTransfer
  let uCG ← getLevel cgraphE
  let base := base?.getD thmName.getString!.toName
  let newName := `IsoGraph ++ base
  if (← getEnv).contains newName then
    throwError "toIsoGraph: {newName} already exists"
  forallTelescope info.type fun olds body => do
    /- Introduce the translated binders, one at a time: a graph becomes an `IsoGraph`, and every
    other binder keeps its name and its binder info, with its type translated. -/
    let rec loop (i : Nat) (news : Array Expr) (graphs : Array Bool) :
        MetaM Unit := do
      if h : i < olds.size then
        let decl ← olds[i].fvarId!.getDecl
        if decl.type == cgraphE then
          withLocalDecl decl.userName decl.binderInfo isographE fun q ↦
            loop (i + 1) (news.push q) (graphs.push true)
        else
          let ty ← translateExpr rev olds news graphs decl.type
          withLocalDecl decl.userName decl.binderInfo ty fun y ↦
            loop (i + 1) (news.push y) (graphs.push false)
      else
        let newBody ← translateExpr rev olds news graphs body
        let stmt ← instantiateMVars (← mkForallFVars news newBody)
        /- The proof: peel the binders off again, inserting a `Quotient.ind` at each graph.  What
        is left is the original theorem, applied to the representatives. -/
        let rec prove (j : Nat) (subst args : Array Expr) : MetaM Expr := do
          if hj : j < news.size then
            if graphs[j]! then
              let tail ← mkForallFVars (news.extract (j + 1) news.size) newBody
              let motive := (← mkLambdaFVars #[news[j]] tail).replaceFVars
                (news.extract 0 j) subst
              withLocalDeclD `g cgraphE fun g ↦ do
                let q := mkAppN (mkConst ``Quotient.mk [uCG]) #[cgraphE, setoidE, g]
                let inner ← prove (j + 1) (subst.push q) (args.push g)
                return mkAppN (mkConst ``Quotient.ind [uCG])
                  #[cgraphE, setoidE, motive, ← mkLambdaFVars #[g] inner]
            else
              let decl ← news[j].fvarId!.getDecl
              let ty := decl.type.replaceFVars (news.extract 0 j) subst
              withLocalDecl decl.userName decl.binderInfo ty fun y ↦ do
                let inner ← prove (j + 1) (subst.push y) (args.push y)
                mkLambdaFVars #[y] inner
          else
            return mkAppN thm args
        let prf ← instantiateMVars (← prove 0 #[] #[])
        addDecl (.thmDecl { name := newName, levelParams := lvls, type := stmt, value := prf })
        if let some doc ← findDocString? (← getEnv) thmName then
          addDocStringCore newName doc
        if (← getSimpTheorems).isLemma (.decl thmName) then
          addSimpTheorem (ext := simpExtension) (declName := newName) (post := true)
            (inv := false) (attrKind := .global) (prio := eval_prio default)
    loop 0 #[] #[]

/-- `@[toIsoGraph]` on an isomorphism-invariance theorem for a `CGraph`-level quantity generates
the corresponding `IsoGraph`-level quantity, as a `Quotient.lift`, together with the `simp` lemma
saying that the two agree on representatives.  The name of the generated function is read off the
statement; `@[toIsoGraph f]` overrides it.

On any other `CGraph`-level theorem it generates the `IsoGraph`-level statement of the same fact,
proved from the original.  It is `@[simp]` exactly when the original is, so write `@[simp,
toIsoGraph]` and not the other way round. -/
syntax (name := toIsoGraph) "toIsoGraph" (ppSpace ident)? : attr

/-- Does this statement bind an isomorphism, and so ask for a `Quotient.lift`? -/
private def isInvariance (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ ↦
    xs.anyM fun x ↦ return (← inferType x).isAppOfArity ``CGraph.Iso 2

initialize registerBuiltinAttribute {
  name := `toIsoGraph
  descr := "generate the `IsoGraph`-level counterpart of a `CGraph`-level fact"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    unless kind == .global do
      throwError "toIsoGraph: only a global attribute"
    let base? : Option Name ← match stx with
      | `(attr| toIsoGraph) => pure none
      | `(attr| toIsoGraph $i:ident) => pure (some i.getId)
      | _ => throwError "toIsoGraph: unexpected syntax"
    MetaM.run' do
      if ← isInvariance (← getConstInfo decl).type then
        generateLift decl base?
      else
        generateFact decl base?
}

end IsoGraph.Attr
