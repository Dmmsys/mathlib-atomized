/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Util
public import Lean.SubExpr

/-! This file defines some functions for dealing with `SubExpr.GoalsLocation`. -/

@[expose] public section

namespace Lean.SubExpr.GoalsLocation
/--
Definition of `rootExpr` / `rootExpr` 的定义

English:
definition rootExpr
  signature: : GoalsLocation -> MetaM Expr

中文:
定义 rootExpr
  签名: : GoalsLocation -> MetaM Expr
-/
def rootExpr : GoalsLocation -> MetaM Expr
  | ⟨_, .hyp fvarId⟩ => do instantiateMVars (← fvarId.getType)
  | ⟨_, .hypType fvarId _⟩ => do instantiateMVars (← fvarId.getType)
  | ⟨_, .hypValue fvarId _⟩ => do instantiateMVars (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩ => do instantiateMVars (← mvarId.getType)

/--
Definition of `pos` / `pos` 的定义

English:
definition pos
  signature: : GoalsLocation -> Pos

中文:
定义 pos
  签名: : GoalsLocation -> Pos
-/
def pos : GoalsLocation -> Pos
  | ⟨_, .hyp _⟩ => .root
  | ⟨_, .hypType _ pos⟩ => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩ => pos

/--
Definition of `fvarId?` / `fvarId?` 的定义

English:
definition fvarId?
  signature: : GoalsLocation -> Option FVarId

中文:
定义 fvarId?
  签名: : GoalsLocation -> Option FVarId
-/
def fvarId? : GoalsLocation -> Option FVarId
  | ⟨_, .hyp fvarId⟩ => fvarId
  | ⟨_, .hypType fvarId _⟩ => fvarId
  | ⟨_, .hypValue fvarId _⟩ => fvarId
  | ⟨_, .target _⟩ => none

end Lean.SubExpr.GoalsLocation
