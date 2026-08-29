/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public meta import Lean.Meta.ExprLens

/-!
# Support for `grw` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta Mathlib.Tactic ProofWidgets Jsx

/--
Definition of `GrwPos` / `GrwPos` 的定义

English:
structure GrwPos
  parameters: where
  axioms and operations (3):
    - relName : Name
    - relation : Expr
    - symm? : Option Bool

中文:
结构 GrwPos
  参数: where
  公理与运算 (3 个):
    - relName : Name
    - relation : Expr
    - symm? : Option 布尔
-/
structure GrwPos where
  /-- The name of the relation. -/
  relName : Name
  /-- The expression of the relation. -/
  relation : Expr
  /-- `symm` is `none` if the given relations are symmetric.
  `symm` is `true` when you can only rewrite from right to left. -/
  symm? : Option Bool

/--
Definition of `gcongrBackward` / `gcongrBackward` 的定义

English:
definition gcongrBackward
  signature: (relName : Name) (relation : Expr) (symm : Bool)
  body: do
  let type ← inferType relation
  let α ← mkFreshTypeMVar
  unless ← isDefEq type (.forallE `_ α (.forallE `_ α (.sort 0) .default) .default) do
    throwError "invalid relation {relation}"
  let α ← instantiateMVars α
  let u ← getDecLevel α
  withLocalDeclD `a α fun a => do
  withLocalDeclD `b 

中文:
定义 gcongrBackward
  签名: (relName : Name) (relation : Expr) (symm : 布尔)
  定义体: do
  let type ← inferType relation
  let α ← mkFreshTypeMVar
  unless ← isDefEq type (.forallE `_ α (.forallE `_ α (.sort 0) .default) .default) do
    throwError "invalid relation {relation}"
  let α ← instantiateMVars α
  let u ← getDecLevel α
  withLocalDeclD `a α fun a => do
  withLocalDeclD `b 
-/
private def gcongrBackward (relName : Name) (relation : Expr) (symm : Bool) :
    MetaM (Array GrwPos) := do
  let type ← inferType relation
  let α ← mkFreshTypeMVar
  unless ← isDefEq type (.forallE `_ α (.forallE `_ α (.sort 0) .default) .default) do
    throwError "invalid relation {relation}"
  let α ← instantiateMVars α
  let u ← getDecLevel α
  withLocalDeclD `a α fun a => do
  withLocalDeclD `b α fun b => do
  withNewMCtxDepth do
  let mut result : Array GrwPos := #[]
  -- Any relation `r` can be proved from `AntisymmRel r`, so we add this as a possible relation
  if (← getEnv).contains `AntisymmRel then
    let antiSymm := mkApp2 (.const `AntisymmRel [u]) α relation
    result := result.push { relName := `AntisymmRel, relation := antiSymm, symm? := none }
  -- If `relName` is symmetric, then include the reverse as a possible relation (`symm? := none`)
  let symm? ← try
    let dummyVar ← mkFreshExprMVar (mkApp2 relation a b)
    if let mkApp2 relation' b' a' ← inferType (← dummyVar.applySymm) then
      if relation' == relation && b == b' && a == a' then
        pure none
      else
        pure symm
    else
      pure symm
    catch _ => pure symm
  result := result.push { relName, relation, symm? }
  -- For `≤`, we add the relation `<`.
  if relName == ``LE.le then
    if (← getEnv).contains `le_of_lt then
      let (mvars, _, le) ←
        forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels `le_of_lt))
      if ← isDefEq le.appFn!.appFn! relation then
        let lt ← instantiateMVars (← inferType mvars.back!).appFn!.appFn!
        result := result.push { relName := ``LT.lt, relation := lt, symm? := symm }
  return result

/--
Definition of `dummyDischarger` / `dummyDischarger` 的定义

English:
definition dummyDischarger
  signature: (ref : IO.Ref (Array GrwPos)) (hyp? : Bool) (fvar : Expr)
  body: do
  let e ← instantiateMVars (← goal.getType)
  let mkApp2 relation lhs rhs := e | throwError "`{e}` is not a relation"
  let .const relName _ := relation.getAppFn | throwError "{e} is not a relation"
  if relName matches ``Eq | ``Iff then throwError "{e} is not a generalized relation"
  let symm ←

中文:
定义 dummyDischarger
  签名: (ref : IO.Ref (Array GrwPos)) (hyp? : 布尔) (fvar : Expr)
  定义体: do
  let e ← instantiateMVars (← goal.getType)
  let mkApp2 relation lhs rhs := e | throwError "`{e}` is not a relation"
  let .const relName _ := relation.getAppFn | throwError "{e} is not a relation"
  if relName matches ``Eq | ``Iff then throwError "{e} is not a generalized relation"
  let symm ←
-/
private def dummyDischarger (ref : IO.Ref (Array GrwPos)) (hyp? : Bool) (fvar : Expr)
    (goal : MVarId) : MetaM Bool := do
  let e ← instantiateMVars (← goal.getType)
  let mkApp2 relation lhs rhs := e | throwError "`{e}` is not a relation"
  let .const relName _ := relation.getAppFn | throwError "{e} is not a relation"
  if relName matches ``Eq | ``Iff then throwError "{e} is not a generalized relation"
  let symm ←
    if lhs.cleanupAnnotations == fvar then
      pure hyp?
    else if rhs.cleanupAnnotations == fvar then
      pure !hyp?
    else
      throwError "{e} doesn't have {fvar} on either side"
  ref.set (← gcongrBackward relName relation symm)
throw .error default "dummyError"

/--
Definition of `getGrwPos?` / `getGrwPos?` 的定义

English:
definition getGrwPos?
  signature: (rootExpr subExpr : Expr) (pos : SubExpr.Pos) (hyp? : Bool)
  body: do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
  let root' ← replaceSubexpr (fun _ => pure (GCongr.mkHoleAnnotation fvar)) pos rootExpr
  let imp := Expr.forallE `_a rootExpr root' .default
  let dummyGoal ← mkFreshExprMVar imp
  let ref ← IO.mkRef #[]
  try
.run (mainGoalDischarger :=

中文:
定义 getGrwPos?
  签名: (rootExpr subExpr : Expr) (pos : SubExpr.Pos) (hyp? : 布尔)
  定义体: do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
  let root' ← replaceSubexpr (fun _ => pure (GCongr.mkHoleAnnotation fvar)) pos rootExpr
  let imp := Expr.forallE `_a rootExpr root' .default
  let dummyGoal ← mkFreshExprMVar imp
  let ref ← IO.mkRef #[]
  try
.run (mainGoalDischarger :=
-/
def getGrwPos? (rootExpr subExpr : Expr) (pos : SubExpr.Pos) (hyp? : Bool) :
    MetaM (Array GrwPos) := do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
  let root' ← replaceSubexpr (fun _ => pure (GCongr.mkHoleAnnotation fvar)) pos rootExpr
  let imp := Expr.forallE `_a rootExpr root' .default
  let dummyGoal ← mkFreshExprMVar imp
  let ref ← IO.mkRef #[]
  try
.run (mainGoalDischarger := dummyDischarger ref hyp? fvar) _ ← dummyGoal.mvarId!.gcongr false
    return #[]
  catch ex =>
    if (← ex.toMessageData.toString) != "dummyError" then
      return #[]
  let result ← ref.get
  /- I doubt that this can come up in practice, but we check anyways that the relation
  that was found doesn't contain any free variables that are now out of scope. -/
  for { relation, .. } in result do
    unless (collectFVars {} relation).fvarIds.all (← getLCtx).contains do
      return #[]
  return result


/--
Definition of `GrwLemma` / `GrwLemma` 的定义

English:
structure GrwLemma
  parameters: where
  axioms and operations (3):
    - name : Premise
    - symm : Bool
    - relName : Name

中文:
结构 GrwLemma
  参数: where
  公理与运算 (3 个):
    - name : Premise
    - symm : 布尔
    - relName : Name
-/
structure GrwLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- `relName` is the relation of the lemma. -/
  relName : Name

/--
Definition of `GrwInfo` / `GrwInfo` 的定义

English:
structure GrwInfo
  parameters: where
  axioms and operations (5):
    - rootExpr : Expr
    - subExpr : Expr
    - rflTarget? : Option Expr
    - gpos : Array GrwPos
    - rwKind : RwKind

中文:
结构 GrwInfo
  参数: where
  公理与运算 (5 个):
    - rootExpr : Expr
    - subExpr : Expr
    - rflTarget? : Option Expr
    - gpos : Array GrwPos
    - rwKind : RwKind
-/
structure GrwInfo where
  /-- The outer expression in which the rewrite takes place. -/
  rootExpr : Expr
  /-- The expression that is being rewritten. -/
  subExpr : Expr
  /-- If we rewrite into this expression, then the goal will be solved. -/
  rflTarget? : Option Expr
  /-- The relations that can be used for rewriting. -/
  gpos : Array GrwPos
  /-- Some information about the rewrite position. -/
  rwKind : RwKind

/--
Definition of `GrwKey` / `GrwKey` 的定义

English:
structure GrwKey
  parameters: where
  axioms and operations (5):
    - numGoals : Nat
    - nameLength : Nat
    - replacementSize : Nat
    - name : String
    - replacement : AbstractMVarsResult

中文:
结构 GrwKey
  参数: where
  公理与运算 (5 个):
    - numGoals : 自然数
    - nameLength : 自然数
    - replacementSize : 自然数
    - name : String
    - replacement : AbstractMVarsResult
-/
structure GrwKey where
  /-- The number of side goals created. -/
  numGoals : Nat
  /-- The name length of the used lemma. -/
  nameLength : Nat
  /-- The length of the new subexpression. -/
  replacementSize : Nat
  /-- The nae of the used lemma. -/
  name : String
  -- TODO: in this implementation, we conclude that two rewrites are the same if they
  -- rewrite into the same expression. But there can be two rewrites that have
  -- different side conditions!
  /-- The new subexpression. -/
  replacement : AbstractMVarsResult
deriving Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ord GrwKey
  body: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

中文:
实例 :
  签名: Ord GrwKey
  定义体: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

Depends on / 依赖: compare
-/
instance : Ord GrwKey where
  compare a b :=
(compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

/--
Definition of `GrwKey.isDuplicate` / `GrwKey.isDuplicate` 的定义

English:
definition GrwKey.isDuplicate
  signature: (a b : GrwKey)
  body: pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

中文:
定义 GrwKey.isDuplicate
  签名: (a b : GrwKey)
  定义体: pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

Depends on / 依赖: a.replacement.expr, a.replacement.mvars.size, b.replacement.expr, b.replacement.mvars.size, isExplicitEq, replacement
-/
def GrwKey.isDuplicate (a b : GrwKey) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

/--
Definition of `tacticSyntax` / `tacticSyntax` 的定义

English:
definition tacticSyntax
  signature: (lem : GrwLemma) (i : GrwInfo) (proof : Expr) (justLemmaName : Bool)
  body: do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite i.rwKind lem.symm proof (← getHypIdent?) (grw := true)

中文:
定义 tacticSyntax
  签名: (lem : GrwLemma) (i : GrwInfo) (proof : Expr) (justLemmaName : 布尔)
  定义体: do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite i.rwKind lem.symm proof (← getHypIdent?) (grw := true)
-/
private def tacticSyntax (lem : GrwLemma) (i : GrwInfo) (proof : Expr) (justLemmaName : Bool) :
    ClickSuggestionsM (TSyntax `tactic) := do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite i.rwKind lem.symm proof (← getHypIdent?) (grw := true)

/--
Definition of `GrwLemma.try` / `GrwLemma.try` 的定义

English:
definition GrwLemma.try
  signature: (i : GrwInfo) (lem : GrwLemma)
  body: do
  withNewMCtxDepth do
  let mctx ← getMCtx
  (·.getDM do throwError "no suitable `grw` relation was found") =<< i.gpos.findSomeM? fun pos => do
  unless lem.relName == pos.relName && pos.symm?.all (· == lem.symm) do return none
  let (proof, mvars, binderInfos, rel) ← lem.name.forallMetaTelescope

中文:
定义 GrwLemma.try
  签名: (i : GrwInfo) (lem : GrwLemma)
  定义体: do
  withNewMCtxDepth do
  let mctx ← getMCtx
  (·.getDM do throwError "no suitable `grw` relation was found") =<< i.gpos.findSomeM? fun pos => do
  unless lem.relName == pos.relName && pos.symm?.all (· == lem.symm) do return none
  let (proof, mvars, binderInfos, rel) ← lem.name.forallMetaTelescope
-/
def GrwLemma.try (i : GrwInfo) (lem : GrwLemma) : ClickSuggestionsM (Result GrwKey) := do
  withNewMCtxDepth do
  let mctx ← getMCtx
  (·.getDM do throwError "no suitable `grw` relation was found") =<< i.gpos.findSomeM? fun pos => do
  unless lem.relName == pos.relName && pos.symm?.all (· == lem.symm) do return none
  let (proof, mvars, binderInfos, rel) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 rel lhs rhs := rel.cleanupAnnotations | return none
  unless ← isDefEq rel pos.relation do setMCtx mctx; return none
some < > do
  let e := i.subExpr
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  unless ← isDefEq e lhs do
    throwError "{lhs} does not unify with {e}"
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    throwError "{lhs} and {e} do not match according to the head-constant indexing"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut extraGoals := #[]
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      extraGoals := extraGoals.push (← instantiateMVars (← inferType mvar))

  let replacement ← instantiateMVars rhs
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    extraGoals.any fun goal => (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let isRefl ← isExplicitEq e replacement
  let justLemmaName ←
    if i.rwKind matches .hasBVars then pure true
    else withMCtx mctxOrig do kabstractFindsPositions i.rootExpr lhsOrig (← read).pos
  let key := {
    numGoals := extraGoals.size
    nameLength := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  let tactic ← tacticSyntax lem i proof justLemmaName
  let isClosing ← (do
    if extraGoals.isEmpty then
      if let some rflTarget := i.rflTarget? then
return ← withoutModifyingMCtx isDefEq replacement rflTarget
    return false)
  if isClosing then
    addSolvedSuggestion tactic
  let mut htmls := #[← exprToHtml replacement]
  for goal in extraGoals do
    htmls := htmls.push
      <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  let filtered ←
    if !isRefl && !makesNewMVars then
some < > mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    let mkApp2 _ lhs rhs := (← instantiateMVars e).cleanupAnnotations
      | throwError "Expected relation, not {indentExpr e}"
exprToHtml if lem.symm then rhs else lhs
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
