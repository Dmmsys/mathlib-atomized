/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState

/-!
# Support for `apply` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/--
Definition of `ApplyLemma` / `ApplyLemma` 的定义

English:
structure ApplyLemma
  parameters: where
  axioms and operations (1):
    - name : Premise

中文:
结构 ApplyLemma
  参数: where
  公理与运算 (1 个):
    - name : Premise
-/
structure ApplyLemma where
  /-- The lemma -/
  name : Premise

/--
Definition of `ApplyKey` / `ApplyKey` 的定义

English:
structure ApplyKey
  parameters: where
  axioms and operations (5):
    - numGoals : Nat
    - nameLength : Nat
    - replacementSize : Nat
    - name : String
    - newGoals : Array AbstractMVarsResult

中文:
结构 ApplyKey
  参数: where
  公理与运算 (5 个):
    - numGoals : 自然数
    - nameLength : 自然数
    - replacementSize : 自然数
    - name : String
    - newGoals : 数组 AbstractMVarsResult
-/
structure ApplyKey where
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
  signature: Ord ApplyKey
  body: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

中文:
实例 :
  签名: 序 ApplyKey
  定义体: (compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

Depends on / 依赖: compare
-/
instance : Ord ApplyKey where
  compare a b :=
(compare a.1 b.1).then
(compare a.2 b.2).then
(compare a.3 b.3).then
    (compare a.4 b.4)

/--
Definition of `ApplyKey.isDuplicate` / `ApplyKey.isDuplicate` 的定义

English:
definition ApplyKey.isDuplicate
  signature: (a b : ApplyKey)
  body: pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

中文:
定义 ApplyKey.isDuplicate
  签名: (a b : ApplyKey)
  定义体: pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

Depends on / 依赖: IsOpen, a.newGoals, a.newGoals.size, a.newGoals.size.allM, a_lt_b, b.newGoals, b.newGoals.size, exists_Ioo_subset, exists_between, forall_mem_nonempty_iff_neBot, isExplicitEq, mem_nhdsWithin, mvars.size, ne_or_eq, newGoals, subseteq, u_open, u_open.exists_Ioo_subset, xy.symm
-/
def ApplyKey.isDuplicate (a b : ApplyKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/--
Definition of `tacticSyntax` / `tacticSyntax` 的定义

English:
definition tacticSyntax
  signature: (lemmaName : Premise) (proof : Expr) (isClosing justLemmaName : Bool)
  body: do
  if justLemmaName then
    let id := mkIdent (← lemmaName.unresolveName)
    -- We can only use `exact` instead of `apply` if the proof has no explicit arguments.
    if ← pure isClosing <&&> hasOnlyImplicitArgs proof then
      `(tactic| exact $id)
    else
      `(tactic| apply $id)
  else
    let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
    if isClosing then
      `(tactic| exact $proof)
    else
      `(tactic| refine $proof)

中文:
定义 tacticSyntax
  签名: (lemmaName : Premise) (proof : Expr) (isClosing justLemmaName : 布尔值)
  定义体: do
  if justLemmaName then
    let id := mkIdent (← lemmaName.unresolveName)
    -- We can only use `exact` instead of `apply` if the proof has no explicit arguments.
    if ← pure isClosing <&&> hasOnlyImplicitArgs proof then
      `(tactic| exact $id)
    else
      `(tactic| apply $id)
  else
    let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
    if isClosing then
      `(tactic| exact $proof)
    else
      `(tactic| refine $proof)
-/
private def tacticSyntax (lemmaName : Premise) (proof : Expr) (isClosing justLemmaName : Bool) :
    MetaM (TSyntax `tactic) := do
  if justLemmaName then
    let id := mkIdent (← lemmaName.unresolveName)
    -- We can only use `exact` instead of `apply` if the proof has no explicit arguments.
    if ← pure isClosing <&&> hasOnlyImplicitArgs proof then
      `(tactic| exact $id)
    else
      `(tactic| apply $id)
  else
    let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
    if isClosing then
      `(tactic| exact $proof)
    else
      `(tactic| refine $proof)
where
  hasOnlyImplicitArgs (e : Expr) : MetaM Bool := do
    let info ← getFunInfoNArgs e.getAppFn e.getAppNumArgs
    return !info.paramInfo.any (·.binderInfo.isExplicit)

/--
Definition of `ApplyLemma.try` / `ApplyLemma.try` 的定义

English:
definition ApplyLemma.try
  signature: (lem : ApplyLemma)
  body: withNewMCtxDepth do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  let target ← (← read).goal.getType
  unless ← isDefEq e target do throwError "{e} does not unify with {target}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  let mut justLemmaName := true
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      if ← isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        newGoals := newGoals.push (← instantiateMVars (← inferType mvar))
  let isClosing := newGoals.isEmpty
  let makesNewMVars := newGoals.any fun goal =>
    (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·)
  }
  let tactic ← tacticSyntax lem.name proof (isClosing := isClosing) (justLemmaName := justLemmaName)
  let mut htmls := #[]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  if isClosing then
    htmls := #[.text "Goal accomplished! 🎉️"]
    addSolvedSuggestion tactic
  let filtered ←
    if !makesNewMVars then
some < > mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml e
  return { filtered, unfiltered, key, pattern }

中文:
定义 ApplyLemma.try
  签名: (lem : ApplyLemma)
  定义体: withNewMCtxDepth do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  let target ← (← read).goal.getType
  unless ← isDefEq e target do throwError "{e} does not unify with {target}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  let mut justLemmaName := true
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      if ← isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        newGoals := newGoals.push (← instantiateMVars (← inferType mvar))
  let isClosing := newGoals.isEmpty
  let makesNewMVars := newGoals.any fun goal =>
    (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·)
  }
  let tactic ← tacticSyntax lem.name proof (isClosing := isClosing) (justLemmaName := justLemmaName)
  let mut htmls := #[]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  if isClosing then
    htmls := #[.text "Goal accomplished! 🎉️"]
    addSolvedSuggestion tactic
  let filtered ←
    if !makesNewMVars then
some < > mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml e
  return { filtered, unfiltered, key, pattern }

Depends on / 依赖: assumptionCore, binderInfos, click_suggestions, forallMetaTelescopeReducing, getType, goal.getType, isAssigned, isDefEq, isProof, justLemmaName, lem.name.forallMetaTelescopeReducing, mvar.mvarId, mvarId, newGoals, newGoals.push, synthAppInstances, target, throwError, unless, withNewMCtxDepth
-/
def ApplyLemma.try (lem : ApplyLemma) : ClickSuggestionsM (Result ApplyKey) :=
  withNewMCtxDepth do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  let target ← (← read).goal.getType
  unless ← isDefEq e target do throwError "{e} does not unify with {target}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  let mut justLemmaName := true
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      if ← isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        newGoals := newGoals.push (← instantiateMVars (← inferType mvar))
  let isClosing := newGoals.isEmpty
  let makesNewMVars := newGoals.any fun goal =>
    (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·)
  }
  let tactic ← tacticSyntax lem.name proof (isClosing := isClosing) (justLemmaName := justLemmaName)
  let mut htmls := #[]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  if isClosing then
    htmls := #[.text "Goal accomplished! 🎉️"]
    addSolvedSuggestion tactic
  let filtered ←
    if !makesNewMVars then
some < > mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml e
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
