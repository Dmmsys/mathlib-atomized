/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Util

/-!
# Fail if no progress

This implements the `fail_if_no_progress` tactic, which fails if no actual progress is made by the
following tactic sequence.

"Actual progress" means that either the number of goals has changed, that the
number or presence of expressions in the context has changed, or that the type of some expression
in the context or the type of the goal is no longer definitionally equal to what it used to be at
reducible transparency.

This means that, for example, `1 - 1` changing to `0` does not count as actual progress, since
```lean
example : (1 - 1 = 0) := by with_reducible rfl
```

This tactic is useful in situations where we want to stop iterating some tactics if they're not
having any effect, e.g. `repeat (fail_if_no_progress simp <;> ring_nf)`.

-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- `fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency. -/
syntax (name := failIfNoProgress) "fail_if_no_progress " tacticSeq : tactic

/--
Definition of `lctxIsDefEq` / `lctxIsDefEq` 的定义

English:
definition lctxIsDefEq
  signature: : (l₁ l₂ : List (Option LocalDecl)) -> MetaM Bool

中文:
定义 lctxIsDefEq
  签名: : (l₁ l₂ : 列表 (选项类型 LocalDecl)) -> MetaM 布尔值
-/
def lctxIsDefEq : (l₁ l₂ : List (Option LocalDecl)) -> MetaM Bool
  | none :: l₁, l₂ => lctxIsDefEq l₁ l₂
  | l₁, none :: l₂ => lctxIsDefEq l₁ l₂
  | some d₁ :: l₁, some d₂ :: l₂ => do
    unless d₁.isLet == d₂.isLet do
      return false
    unless d₁.fvarId == d₂.fvarId do
      -- Without compatible fvarids, `isDefEq` checks for later entries will not make sense
      return false
    unless (← withNewMCtxDepth <| isDefEq d₁.type d₂.type) do
      return false
    if d₁.isLet then
      unless (← withNewMCtxDepth <| isDefEq d₁.value d₂.value) do
        return false
    lctxIsDefEq l₁ l₂
  | [], [] => return true
  | _, _ => return false

/--
Definition of `runAndFailIfNoProgress` / `runAndFailIfNoProgress` 的定义

English:
definition runAndFailIfNoProgress
  signature: (goal : MVarId) (tacs : TacticM Unit)
  body: do
  let l ← run goal tacs
  try
    let [newGoal] := l | failure
    goal.withContext do
      -- Check that the local contexts are compatible
      let ctxDecls := (← goal.getDecl).lctx.decls.toList
      let newCtxDecls := (← newGoal.getDecl).lctx.decls.toList
guard ← withNewMCtxDepth withReducib

中文:
定义 runAndFailIfNoProgress
  签名: (goal : MVarId) (tacs : TacticM 单元)
  定义体: do
  let l ← run goal tacs
  try
    let [newGoal] := l | failure
    goal.withContext do
      -- Check that the local contexts are compatible
      let ctxDecls := (← goal.getDecl).lctx.decls.toList
      let newCtxDecls := (← newGoal.getDecl).lctx.decls.toList
guard ← withNewMCtxDepth withReducib
-/
def runAndFailIfNoProgress (goal : MVarId) (tacs : TacticM Unit) : TacticM (List MVarId) := do
  let l ← run goal tacs
  try
    let [newGoal] := l | failure
    goal.withContext do
      -- Check that the local contexts are compatible
      let ctxDecls := (← goal.getDecl).lctx.decls.toList
      let newCtxDecls := (← newGoal.getDecl).lctx.decls.toList
guard ← withNewMCtxDepth withReducible lctxIsDefEq ctxDecls newCtxDecls
      -- They are compatible, so now we can check that the goals are equivalent
guard ← withNewMCtxDepth withReducible isDefEq (← newGoal.getType) (← goal.getType)
  catch _ =>
    return l
  throwError "no progress made on\n{goal}"

elab_rules : tactic
| `(tactic| fail_if_no_progress $tacs) => do
  let goal ← getMainGoal
  let l ← runAndFailIfNoProgress goal (evalTactic tacs)
  replaceMainGoal l

end Mathlib.Tactic
