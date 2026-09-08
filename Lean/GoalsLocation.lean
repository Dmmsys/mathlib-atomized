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
/-- The root expression of the position specified by the `GoalsLocation`. -/
/-
**Lean.SubExpr.GoalsLocation.rootExpr** 是 Mathlib 中的一个定义，位于命名空间 `Lean.SubExpr.Go
alsLocation`。
形式化陈述：SubExpr.GoalsLocation → MetaM Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The root expression of the position specified by the `GoalsLocation`.
-/
def rootExpr : GoalsLocation → MetaM Expr
  | ⟨_, .hyp fvarId⟩        => do instantiateMVars (← fvarId.getType)
  | ⟨_, .hypType fvarId _⟩  => do instantiateMVars (← fvarId.getType)
  | ⟨_, .hypValue fvarId _⟩ => do instantiateMVars (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩     => do instantiateMVars (← mvarId.getType)

/-- The `SubExpr.Pos` specified by the `GoalsLocation`. -/
/-
**Lean.SubExpr.GoalsLocation.pos** 是 Mathlib 中的一个定义，位于命名空间 `Lean.SubExpr.GoalsLo
cation`。
形式化陈述：SubExpr.GoalsLocation → SubExpr.Pos
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SubExpr.Pos` specified by the `GoalsLocation`.
-/
def pos : GoalsLocation → Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

/-- The hypothesis specified by the `GoalsLocation`. -/
/-
**Lean.SubExpr.GoalsLocation.fvarId** 是 Mathlib 中的一个定义，位于命名空间 `Lean.SubExpr.Goal
sLocation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hypothesis specified by the `GoalsLocation`.
-/
def fvarId? : GoalsLocation → Option FVarId
  | ⟨_, .hyp fvarId⟩        => fvarId
  | ⟨_, .hypType fvarId _⟩  => fvarId
  | ⟨_, .hypValue fvarId _⟩ => fvarId
  | ⟨_, .target _⟩          => none

end Lean.SubExpr.GoalsLocation

