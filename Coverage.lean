import IsoGraph

/-!
# Invariant × construction coverage table

A standalone script (not part of the library build) that writes `invariant_coverage.txt`.
Run it from the repository root with

```
lake build && lake env lean Coverage.lean
```

It reads every declaration in the `IsoGraph` and `CGraph` namespaces and splits them into

* **constructions** — anything whose result type is a graph, further split into *operators*
  (those taking graph arguments: `compl`, `disjUnion`, the four products, `join`, …) and
  *families* (those taking only numeric parameters, plus the named sporadic graphs);
* **invariants** — anything taking exactly one graph and returning something that is not a graph,
  including the `Prop`-valued ones (`IsConnected`, `IsTree`, …).

A `CGraph` declaration is identified with its `IsoGraph` counterpart (the `@[toIsoGraph]`
dictionary, falling back on the name), so each row and column names a single mathematical notion.

For each (invariant, construction) pair it then looks for a theorem whose conclusion is headed by
`invariant (construction …)`: the left-hand side of an `=` or `↔`, the argument of a `¬`, or a bare
predicate application. The mark records whether such a theorem exists, whether it is tagged
`@[simp]`, whether it is *generic* (the construction's arguments are variables, so the theorem is a
table entry) or only covers *specific* arguments (`girth (cycle 5) = 5` and the like), and whether
it is stated about `IsoGraph` or only about `CGraph`.
-/

open Lean Meta Elab

namespace Coverage

def isoTy : Expr := mkConst ``IsoGraph
def cgraphTy : Expr := mkConst ``CGraph

/-- Is `e` a graph, and at which level? -/
def graphLevel? (e : Expr) : MetaM (Option Bool) := do
  if e.hasLooseBVars then return none
  try
    let t ← whnfR (← inferType e)
    if t == isoTy then return some true
    else if t == cgraphTy then return some false
    else return none
  catch _ => return none

/-- Declarations that are shaped like invariants but are plumbing, not mathematics. -/
def blacklist : Array String :=
  #["toCGraph", "toIsoGraph", "key", "canon", "vertexTransitiveB", "arcTransitiveB",
    "edgeIdxList", "nonEdgeIdxList"]

/-- Compiler-generated declarations and instances, which are not mathematics either. -/
def isNoise (nm : Name) : Bool :=
  let s := nm.getString!
  ["casesOn", "recOn", "brecOn", "rec", "ndrec", "noConfusion", "noConfusionType", "ctorIdx",
    "below", "mk", "injEq", "sizeOf_spec", "ofNat", "toCtorIdx"].contains s
    || "inst".isPrefixOf s || nm.components.contains `Iso || nm.components.contains `Enum

structure Dict where
  /-- Constructions taking at least one graph, at `IsoGraph` level. -/
  operators : Array Name := #[]
  /-- Constructions taking no graph, at `IsoGraph` level. -/
  families : Array Name := #[]
  /-- One-graph invariants, at `IsoGraph` level. -/
  invariants : Array Name := #[]
  /-- Every recognised construction name, at either level. -/
  constrNames : Std.HashSet Name := {}
  /-- Every recognised invariant name, at either level. -/
  invNames : Std.HashSet Name := {}
  /-- `CGraph`-level name ↦ its `IsoGraph` counterpart. -/
  canon : Std.HashMap Name Name := {}
  /-- `CGraph`-level constructions with no `IsoGraph` counterpart. -/
  orphanConstrs : Array Name := #[]
  /-- `CGraph`-level invariants with no `IsoGraph` counterpart. -/
  orphanInvs : Array Name := #[]

/-- Is this declaration a construction (result type a graph), and how many graphs does it eat? -/
def shape (ty : Expr) (iso : Bool) : MetaM (Bool × Nat) :=
  forallTelescope ty fun xs concl => do
    let mut n := 0
    for x in xs do
      if (← graphLevel? x) == some iso then n := n + 1
    return (concl == (if iso then isoTy else cgraphTy), n)

/-- Is this a mathematical invariant (a number, a spectrum, a property of the graph alone) rather
than an implementation detail such as `adjMat` or `nbrs`? -/
def mathematical (ty : Expr) (level : Bool) : MetaM Bool :=
  forallTelescope ty fun xs concl => do
    let mut g? : Option Expr := none
    for x in xs do
      if (← graphLevel? x) == some level && g?.isNone then g? := some x
    let some g := g? | return false
    for x in xs do
      if x == g then continue
      let t ← inferType x
      unless t.containsFVar g.fvarId! do continue
      -- hypotheses about the graph and instances derived from it are fine; genuine data
      -- indexed by the graph (a vertex, a subset, a vector) means this is not an invariant
      if ← Meta.isProp t then continue
      if (← x.fvarId!.getDecl).binderInfo == .instImplicit then continue
      return false
    if concl.isProp then return true
    return [``Nat, ``Int, ``Real, ``Multiset, ``Polynomial, ``List].contains
      (concl.getAppFn.constName?.getD .anonymous)

def Dict.addOrphan (d : Dict) (nm : Name) (isConstr : Bool) : Dict :=
  if isConstr then { d with orphanConstrs := d.orphanConstrs.push nm }
  else { d with orphanInvs := d.orphanInvs.push nm }

/-- Split both namespaces into operators, families and invariants. -/
def collectDict : MetaM Dict := do
  let env ← getEnv
  let mut d : Dict := {}
  let mut cg : Array (Name × Bool × Nat) := #[]
  for (nm, ci) in env.constants.toList do
    let root := nm.getRoot
    if (root != `IsoGraph && root != `CGraph) || nm.isInternal || nm.isInternalDetail then continue
    if blacklist.contains (nm.getString!) || isNoise nm then continue
    unless ci matches .defnInfo _ | .opaqueInfo _ do continue
    let iso := root == `IsoGraph
    let (isConstr, nGraph) ← shape ci.type iso
    unless isConstr || nGraph == 1 do continue
    if iso then
      if isConstr then
        if nGraph > 0 then d := { d with operators := d.operators.push nm }
        else d := { d with families := d.families.push nm }
        d := { d with constrNames := d.constrNames.insert nm }
      else
        d := { d with invariants := d.invariants.push nm }
        d := { d with invNames := d.invNames.insert nm }
    else
      cg := cg.push (nm, isConstr, nGraph)
  -- identify each `CGraph` declaration with its `IsoGraph` counterpart
  for (nm, isConstr, _) in cg do
    let tgt? ← match ← IsoGraph.Attr.counterpart? nm with
      | some t => pure (some t)
      | none =>
        let guess := `IsoGraph ++ nm.replacePrefix `CGraph .anonymous
        pure (if env.contains guess then some guess else none)
    match tgt? with
    | some tgt =>
      if (isConstr && d.constrNames.contains tgt) || (!isConstr && d.invNames.contains tgt) then
        d := { d with canon := d.canon.insert nm tgt }
        if isConstr then d := { d with constrNames := d.constrNames.insert nm }
        else d := { d with invNames := d.invNames.insert nm }
      else
        d := d.addOrphan nm isConstr
    | none => d := d.addOrphan nm isConstr
  let keep ← d.orphanInvs.filterM fun nm ↦ do mathematical (← getConstInfo nm).type false
  d := { d with orphanInvs := keep }
  let srt (a : Array Name) := a.qsort (fun x y ↦ x.toString < y.toString)
  return { d with operators := srt d.operators, families := srt d.families,
                  invariants := srt d.invariants, orphanConstrs := srt d.orphanConstrs,
                  orphanInvs := srt d.orphanInvs }

def Dict.canonical (d : Dict) (n : Name) : Name := d.canon.getD n n

/-- How well a theorem covers a cell: the higher the better. -/
inductive Mark
  | none | bound | specific | specificSimp | generic | genericSimp
  deriving Inhabited, BEq, Ord

def Mark.toString : Mark → String
  | .none => "." | .bound => "b" | .specific => "t" | .specificSimp => "s"
  | .generic => "T" | .genericSimp => "S"

/-- The conclusion's candidate left-hand sides: `a` in `a = b` and `a ↔ b`, `p` in `¬ p`, and the
whole thing for a bare predicate application. -/
partial def lhsCandidates (body : Expr) (fuel : Nat := 3) : Array Expr :=
  match fuel with
  | 0 => #[body]
  | fuel + 1 =>
    match body.getAppFnArgs with
    | (``Eq, #[_, a, _]) => lhsCandidates a fuel
    | (``Iff, #[a, _]) => lhsCandidates a fuel
    | (``Not, #[a]) => lhsCandidates a fuel
    | _ => #[body]

/-- Every application appearing in `e`, outermost first. -/
partial def subterms (e : Expr) : Array Expr :=
  match e with
  | .app .. => e.getAppArgs.foldl (fun acc a ↦ acc ++ subterms a) #[e]
  | _ => #[]

/-- Is the conclusion an inequality?  Then any occurrence of `invariant (construction ...)` in it
is a bound rather than a rewrite. -/
def isBound (body : Expr) : Bool :=
  [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Multiset.Subset, ``HasSubset.Subset].contains
    (body.getAppFn.constName?.getD .anonymous)

/-- Notation such as `Gᶜ`, `G + H` and `G * H` goes through a type class, so the head of the
elaborated term is `Compl.compl` rather than `IsoGraph.compl`.  Unfold instances until the head is
a construction we recognise. -/
partial def resolveHead (d : Dict) (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let f := e.getAppFn
    if f.isConst && d.constrNames.contains f.constName! then return e
    let e' ← withTransparency .instances (whnf e)
    if e' == e then return e else resolveHead d e' fuel

/-- The graph arguments of an application. -/
def graphArgs (e : Expr) : MetaM (Array Expr) :=
  e.getAppArgs.filterM fun a ↦ return (← graphLevel? a).isSome

/-- Is this occurrence of a construction generic, i.e. are its arguments variables rather than
particular values?  Graph arguments must be free variables; numeric ones need only mention a
variable, so that `cycle (2 * n + 3)` still counts. -/
def isGeneric (e : Expr) : MetaM Bool := do
  for a in e.getAppArgs do
    if (← graphLevel? a).isSome then
      unless a.isFVar do return false
    else
      unless a.hasFVar || (← inferType a).isProp do return false
  return true

/-- The best theorem found for a cell, at each of the two levels. -/
structure Hit where
  iso : Mark := .none
  isoName : Name := .anonymous
  cg : Mark := .none
  cgName : Name := .anonymous
  deriving Inhabited

def Hit.mark (h : Hit) : String :=
  if h.iso != .none then h.iso.toString
  else if h.cg != .none then "~" ++ h.cg.toString
  else "."

def Hit.best (h : Hit) : Name := if h.iso != .none then h.isoName else h.cgName

def scan (d : Dict) : MetaM (Std.HashMap (Name × Name) Hit) := do
  let env ← getEnv
  let sthms ← getSimpTheorems
  let mut table : Std.HashMap (Name × Name) Hit := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal || nm.isInternalDetail then continue
    unless ci matches .thmInfo _ do continue
    match env.getModuleIdxFor? nm with
    | some i => unless (env.header.moduleNames[i.toNat]!).getRoot == `IsoGraph do continue
    | none => continue
    let isSimp := sthms.isLemma (.decl nm)
    let hits ← forallTelescope ci.type fun _ body ↦ do
      -- an application of an invariant to a construction, and how good a match it is
      let entry (e : Expr) (bound : Bool) : MetaM (Array (Name × Name × Bool × Mark)) := do
        let inv := e.getAppFn
        unless inv.isConst && d.invNames.contains inv.constName! do return #[]
        let mut out := #[]
        for g₀ in ← graphArgs e do
          let g ← resolveHead d g₀
          let c := g.getAppFn
          unless c.isConst && d.constrNames.contains c.constName! do continue
          let gen ← isGeneric g
          let mark := if bound then Mark.bound else match gen, isSimp with
            | true, true => Mark.genericSimp
            | true, false => Mark.generic
            | false, true => Mark.specificSimp
            | false, false => Mark.specific
          out := out.push (d.canonical inv.constName!, d.canonical c.constName!,
            inv.constName!.getRoot == `IsoGraph, mark)
        return out
      if isBound body then
        -- record every occurrence anywhere in the inequality, as a bound
        let mut hits := #[]
        for e in (body.getAppArgs.foldl (fun acc a ↦ acc ++ subterms a) #[]) do
          hits := hits ++ (← entry e true)
        return hits
      else
        let mut hits := #[]
        for lhs in lhsCandidates body do
          hits := hits ++ (← entry lhs false)
        return hits
    for (inv, c, iso, mark) in hits do
      let h := table.getD (inv, c) {}
      let h := if iso then (if compare h.iso mark == .lt then { h with iso := mark, isoName := nm }
                            else h)
               else (if compare h.cg mark == .lt then { h with cg := mark, cgName := nm } else h)
      table := table.insert (inv, c) h
  return table

def shortName (n : Name) : String :=
  n.replacePrefix `IsoGraph .anonymous |>.replacePrefix `CGraph .anonymous |>.toString

def pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - min w s.length)

/-- One matrix: invariants down the side, the given constructions across the top as column
numbers, with a legend. -/
def matrix (title : String) (invs cols : Array Name) (table : Std.HashMap (Name × Name) Hit)
    (perBlock : Nat := 12) : String := Id.run do
  let mut out := s!"## {title}\n\n"
  let rowW := 20
  let blocks := (cols.size + perBlock - 1) / perBlock
  for b in [0:blocks] do
    let these := cols.extract (b * perBlock) (min cols.size ((b + 1) * perBlock))
    for (c, i) in these.zipIdx do
      out := out ++ s!"  {pad s!"{i + 1}." 4}{shortName c}\n"
    out := out ++ "\n" ++ pad "" rowW
    for i in [0:these.size] do out := out ++ pad s!"{i + 1}" 5
    out := out ++ "\n"
    for inv in invs do
      let mut line := pad (shortName inv) rowW
      for c in these do
        line := line ++ pad (table.getD (inv, c) {}).mark 5
      out := out ++ line ++ "\n"
    out := out ++ "\n"
  return out

end Coverage

open Coverage in
run_meta do
  let d ← collectDict
  let table ← scan d
  let mut out := "\
IsoGraph invariant × construction coverage
==========================================

Generated by Coverage.lean (`lake env lean Coverage.lean` from the repository root).
Do not edit by hand.

Each cell answers: is there a theorem rewriting `invariant (construction ...)`?

  S   a @[simp] theorem, stated for general arguments
  T   a theorem for general arguments, not tagged @[simp]
  s   a @[simp] theorem, but only about particular arguments (e.g. `girth (cycle 5)`)
  t   likewise, not tagged @[simp]
  b   no equation, only a bound (`domNum (G □g H)` has Vizing's inequality and nothing more)
  ~   the theorem is only stated about `CGraph`, not about `IsoGraph`
  .   nothing

A general theorem may still be a conditional one: `maxDeg_cartesianProduct` needs both factors to
be nonempty.  See the list of names at the end for what each filled cell actually contains.

"
  out := out ++ matrix "Operators" d.invariants d.operators table 10
  out := out ++ matrix "Families" d.invariants d.families table 12
  -- the gaps, operator by operator
  out := out ++ "## Missing operator entries\n\n"
  for c in d.operators do
    let missing := d.invariants.filter fun inv ↦ (table.getD (inv, c) {}).mark == "."
    let bounded := d.invariants.filter fun inv ↦ (table.getD (inv, c) {}).mark == "b"
    out := out ++ s!"{shortName c} ({missing.size}/{d.invariants.size} missing)\n"
    out := out ++ s!"  {String.intercalate ", " (missing.map shortName).toList}\n"
    unless bounded.isEmpty do
      out := out ++ s!"  bounds only: {String.intercalate ", " (bounded.map shortName).toList}\n"
    out := out ++ "\n"
  -- how well covered each family is
  out := out ++ "## Family coverage\n\n"
  for c in d.families do
    let n := (d.invariants.filter fun inv ↦ (table.getD (inv, c) {}).mark != ".").size
    out := out ++ s!"  {pad (shortName c) 24}{n}/{d.invariants.size}\n"
  out := out ++ "\n## Theorems found\n\n"
  let mut filled := 0
  for inv in d.invariants do
    for c in d.operators ++ d.families do
      let h := table.getD (inv, c) {}
      if h.mark != "." then
        filled := filled + 1
        out := out ++ s!"  {pad h.mark 4}{pad (shortName inv) 20}\
{pad (shortName c) 22}{shortName h.best}\n"
  let cells := d.invariants.size * (d.operators.size + d.families.size)
  out := out ++ s!"\n{filled} of {cells} cells filled \
({d.invariants.size} invariants × {d.operators.size} operators + {d.families.size} families).\n"
  out := out ++ s!"\n## CGraph declarations with no IsoGraph counterpart\n\n\
  constructions: {String.intercalate ", " (d.orphanConstrs.map shortName).toList}\n\n\
  invariants:    {String.intercalate ", " (d.orphanInvs.map shortName).toList}\n"
  IO.FS.writeFile "invariant_coverage.txt" out
  IO.println s!"wrote invariant_coverage.txt: {filled}/{cells} cells"
