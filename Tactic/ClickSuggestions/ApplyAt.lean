/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public import Mathlib.Tactic.ApplyAt

/-!
# Support for `apply at` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/--
Definition of `ApplyAtLemma` / `ApplyAtLemma` 的定义

English:
structure ApplyAtLemma
  parameters: where
  axioms and operations (1):
    - name : Premise

中文:
结构 ApplyAtLemma
  参数: where
  公理与运算 (1 个):
    - name : Premise
-/
structure ApplyAtLemma where
  /-- The lemma -/
  name : Premise

/--
Definition of `ApplyAtKey` / `ApplyAtKey` 的定义

English:
structure ApplyAtKey
  parameters: where
  axioms and operations (5):
    - numGoals : Nat
    - nameLength : Nat
    - replacementSize : Nat
    - name : String
    - newGoals : Array AbstractMVarsResult

中文:
结构 ApplyAtKey
  参数: where
  公理与运算 (5 个):
    - numGoals : 自然数
    - nameLength : 自然数
    - replacementSize : 自然数
    - name : String
    - newGoals : 数组 AbstractMVarsResult
-/
structure ApplyAtKey where
  /-- How many new goals are generated. -/
  numGoals : Nat
  /-- The name length of the used lemma. -/
  nameLength : Nat
  /-- The total length of the new goals when printed. -/
  replacementSize : Nat
  /-- The name of the used lemma. -/
  name : String
  /-- The new goals. -/
  newGoals : Array AbstractMVarsResult
deriving Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ord ApplyAtKey
  body: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

中文:
实例 :
  签名: 序 ApplyAtKey
  定义体: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

Depends on / 依赖: compare
-/
instance : Ord ApplyAtKey where
  compare a b :=
(compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

/--
Definition of `ApplyAtKey.isDuplicate` / `ApplyAtKey.isDuplicate` 的定义

English:
definition ApplyAtKey.isDuplicate
  signature: (a b : ApplyAtKey)
  body: pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

中文:
定义 ApplyAtKey.isDuplicate
  签名: (a b : ApplyAtKey)
  定义体: pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

Depends on / 依赖: a.newGoals, a.newGoals.size, a.newGoals.size.allM, b.newGoals, b.newGoals.size, isExplicitEq, mvars.size, newGoals
-/
def ApplyAtKey.isDuplicate (a b : ApplyAtKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/--
Definition of `tacticSyntax` / `tacticSyntax` 的定义

English:
definition tacticSyntax
  signature: (lem : ApplyAtLemma)
  body: do
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← lem.name.unresolveName)) at $(← getHypIdent!))

中文:
定义 tacticSyntax
  签名: (lem : ApplyAtLemma)
  定义体: do
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← lem.name.unresolveName)) at $(← getHypIdent!))
-/
private def tacticSyntax (lem : ApplyAtLemma) : ClickSuggestionsM (TSyntax `tactic) := do
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← lem.name.unresolveName)) at $(← getHypIdent!))

/--
Definition of `ApplyAtLemma.try` / `ApplyAtLemma.try` 的定义

English:
definition ApplyAtLemma.try
  signature: (lem : ApplyAtLemma)
  body: withNewMCtxDepth do
  let (_proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let mvar := mvars.back!
  let mvars := mvars.pop
  let fvarId := (← read).hyp?.get!
  unless ← isDefEq mvar (.fvar fvarId) do
    throwError "{← inferType mvar} does not unify with {← fvarId.

中文:
定义 ApplyAtLemma.try
  签名: (lem : ApplyAtLemma)
  定义体: withNewMCtxDepth do
  let (_proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let mvar := mvars.back!
  let mvars := mvars.pop
  let fvarId := (← read).hyp?.get!
  unless ← isDefEq mvar (.fvar fvarId) do
    throwError "{← inferType mvar} does not unify with {← fvarId.

Depends on / 依赖: _proof, binderInfos, click_suggestions, forallMetaTelescopeReducing, fvarId, fvarId.getType, getType, inferType, instantiateMVars, isAssigned, isDefEq, lem.name.forallMetaTelescopeReducing, mvar.mvarId, mvarId, mvars.back, mvars.pop, newGoals, newGoals.push, replacement, synthAppInstances
-/
def ApplyAtLemma.try (lem : ApplyAtLemma) : ClickSuggestionsM (Result ApplyAtKey) :=
  withNewMCtxDepth do
  let (_proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let mvar := mvars.back!
  let mvars := mvars.pop
  let fvarId := (← read).hyp?.get!
  unless ← isDefEq mvar (.fvar fvarId) do
    throwError "{← inferType mvar} does not unify with {← fvarId.getType}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (← instantiateMVars (← inferType mvar))

  let replacement ← instantiateMVars replacement
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    newGoals.any fun goal => (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := (← newGoals.mapM (abstractMVars ·)).push (← abstractMVars replacement)
  }
  let tactic ← tacticSyntax lem
  let mut htmls := #[← exprToHtml replacement]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  let filtered ←
    if makesNewMVars then
      pure none
    else
some < > mkSuggestion tactic (.element "div" #[] htmls)
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls)
  let pattern ← do
    let (xs, _, _) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml (← inferType xs.back!)
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
