/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public meta import Mathlib.Control.Basic

/-!
# Support for `rw` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/--
Definition of `RwLemma` / `RwLemma` 的定义

English:
structure RwLemma
  parameters: where
  axioms and operations (2):
    - name : Premise
    - symm : Bool

中文:
结构 RwLemma
  参数: where
  公理与运算 (2 个):
    - name : Premise
    - symm : 布尔值
-/
structure RwLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool

/--
Definition of `RwInfo` / `RwInfo` 的定义

English:
structure RwInfo
  parameters: where
  axioms and operations (5):
    - rootExpr : Expr
    - subExpr : Expr
    - rflTarget? : Option Expr
    - pos : SubExpr.Pos
    - rwKind : RwKind

中文:
结构 RwInfo
  参数: where
  公理与运算 (5 个):
    - rootExpr : Expr
    - subExpr : Expr
    - rflTarget? : 选项类型 Expr
    - pos : SubExpr.Pos
    - rwKind : RwKind
-/
structure RwInfo where
  /-- The outer expression in which the rewrite takes place. -/
  rootExpr : Expr
  /-- The expression that is being rewritten. -/
  subExpr : Expr
  /-- If we rewrite into this expression, then the goal will be solved. -/
  rflTarget? : Option Expr
  /-- The expression that is being rewritten. This may not be the same as the selected expression,
  because we also suggest rewriting partial applications. -/
  pos : SubExpr.Pos
  /-- Some information about the rewrite position. -/
  rwKind : RwKind

/--
Definition of `RwKey` / `RwKey` 的定义

English:
structure RwKey
  parameters: where
  axioms and operations (6):
    - numGoals : Nat
    - symm : Bool
    - nameLength : Nat
    - replacementSize : Nat
    - name : String
    - replacement : AbstractMVarsResult

中文:
结构 RwKey
  参数: where
  公理与运算 (6 个):
    - numGoals : 自然数
    - symm : 布尔值
    - nameLength : 自然数
    - replacementSize : 自然数
    - name : String
    - replacement : AbstractMVarsResult

Depends on / 依赖: rewrite
-/
structure RwKey where
  /-- The number of side goals created. -/
  numGoals : Nat
  /-- If `symm := true`, then the rewrite is right-to-left. -/
  symm : Bool
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
  signature: Ord RwKey
  body: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
(compare a.4 b.4).then
    (compare a.5 b.5)

中文:
实例 :
  签名: 序 RwKey
  定义体: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
(compare a.4 b.4).then
    (compare a.5 b.5)

Depends on / 依赖: compare
-/
instance : Ord RwKey where
  compare a b :=
(compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
(compare a.4 b.4).then
    (compare a.5 b.5)

/--
Definition of `RwKey.isDuplicate` / `RwKey.isDuplicate` 的定义

English:
definition RwKey.isDuplicate
  signature: (a b : RwKey)
  body: pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

中文:
定义 RwKey.isDuplicate
  签名: (a b : RwKey)
  定义体: pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

Depends on / 依赖: a.replacement.expr, a.replacement.mvars.size, b.replacement.expr, b.replacement.mvars.size, isExplicitEq, replacement
-/
def RwKey.isDuplicate (a b : RwKey) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

/--
Definition of `tacticSyntax` / `tacticSyntax` 的定义

English:
definition tacticSyntax
  signature: (lem : RwLemma) (rwKind : RwKind) (hyp? : Option Ident) (proof : Expr)
  body: do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite rwKind lem.symm proof hyp?

中文:
定义 tacticSyntax
  签名: (lem : RwLemma) (rwKind : RwKind) (hyp? : 选项类型 Ident) (proof : Expr)
  定义体: do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite rwKind lem.symm proof hyp?
-/
private def tacticSyntax (lem : RwLemma) (rwKind : RwKind) (hyp? : Option Ident) (proof : Expr)
    (justLemmaName : Bool) : MetaM (TSyntax `tactic) := do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite rwKind lem.symm proof hyp?

/--
Definition of `RwLemma.try` / `RwLemma.try` 的定义

English:
definition RwLemma.try
  signature: (i : RwInfo) (lem : RwLemma)
  body: withNewMCtxDepth do
  let e := i.subExpr
  let (proof, mvars, binderInfos, eqn) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 _ lhs rhs ← whnf eqn | throwError "Exected an equality or iff, not {eqn}"
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctx

中文:
定义 RwLemma.try
  签名: (i : RwInfo) (lem : RwLemma)
  定义体: withNewMCtxDepth do
  let e := i.subExpr
  let (proof, mvars, binderInfos, eqn) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 _ lhs rhs ← whnf eqn | throwError "Exected an equality or iff, not {eqn}"
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctx

Depends on / 依赖: Exected, binderInfos, equality, forallMetaTelescopeReducing, getMCtx, i.subExpr, isDefEq, lem.name.forallMetaTelescopeReducing, lem.symm, lhsOrig, mctxOrig, mkApp2, subExpr, throwError, unless, withNewMCtxDepth
-/
def RwLemma.try (i : RwInfo) (lem : RwLemma) : ClickSuggestionsM (Result RwKey) :=
  withNewMCtxDepth do
  let e := i.subExpr
  let (proof, mvars, binderInfos, eqn) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 _ lhs rhs ← whnf eqn | throwError "Exected an equality or iff, not {eqn}"
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  unless ← isDefEq lhs e do throwError "{lhs} does not unify with {e}"
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  -- TODO: if the `headIndex` doesn't match, then use `simp_rw` instead of `rw` in the suggestion,
  -- instead of just not showing the suggestion.
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    throwError "{lhs} and {e} do not match according to the head-constant indexing"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut extraGoals := #[]
  let mut justLemmaName := true
  let mut rwKind := i.rwKind
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      if ← pure (rwKind matches .valid ..) <&&> isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        extraGoals := extraGoals.push (← instantiateMVars (← inferType mvar))

  let replacement ← instantiateMVars rhs
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    extraGoals.any fun goal => (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let isRefl ← isExplicitEq e replacement
  if let .valid tpCorrect _ := rwKind then
    if justLemmaName then
      if ← withMCtx mctxOrig do kabstractFindsPositions i.rootExpr lhsOrig i.pos then
        rwKind := .valid tpCorrect none
      else
        justLemmaName := false
  let key := {
    numGoals := extraGoals.size
    symm := lem.symm
    nameLength := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  let tactic ← tacticSyntax lem rwKind (← getHypIdent?) proof justLemmaName
  let isClosing ← (do
    if extraGoals.isEmpty then
      if let some rflTarget := i.rflTarget? then
return ← withoutModifyingMCtx isDefEq replacement rflTarget
      else if (← read).pos == .root && (← read).hyp?.isNone then
        return ← succeeds (← mkFreshExprMVar replacement).mvarId!.applyRfl
    return false)
  if isClosing then
    addSolvedSuggestion tactic
  let mut htmls := #[← exprToHtml replacement]
  for goal in extraGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  let filtered ←
    if !isRefl && !makesNewMVars then
some < > mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
    else
      pure none
  htmls := htmls.push (<div> {← lem.name.toHtml} </div>)
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    let mkApp2 _ lhs rhs ← whnf e | throwError "Expected equation, not{indentExpr e}"
exprToHtml if lem.symm then rhs else lhs
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
