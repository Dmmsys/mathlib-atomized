/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Tactic.Widget.SelectPanelUtils
public import ProofWidgets.Component.Basic
public import ProofWidgets.Component.OfRpcMethod

/-! # CongrM widget

This file defines a `congrm?` tactic that displays a widget panel allowing to generate
a `congrm` call with holes specified by selecting subexpressions in the goal.
-/

public meta section

open Lean Meta Server ProofWidgets


/-! ### CongrM widget -/

/-- Return the link text and inserted text above and below of the congrm widget. -/
@[nolint unusedArguments]
/-
**makeCongrMString** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：makeCongrMString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr
) (_ : SelectInsertParams) : MetaM (String × String × Option (String.Pos.Raw × S
tring.Pos.Raw))
参数：pos : Array Lean.SubExpr.GoalsLocation；goalType : Expr；_ : SelectInsertParams
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the link text and inserted text above and below of the congrm widget.
-/
def makeCongrMString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (_ : SelectInsertParams) :
    MetaM (String × String × Option (String.Pos.Raw × String.Pos.Raw)) := do
  let subexprPos := getGoalLocations pos
  unless goalType.isAppOf ``Eq || goalType.isAppOf ``Iff do
    throwError "The goal must be an equality or iff."
  let mut goalTypeWithMetaVars := goalType
  for pos in subexprPos do
    goalTypeWithMetaVars ← insertMetaVar goalTypeWithMetaVars pos

  let side := if subexprPos[0]!.toArray[0]! = 0 then 1 else 2
  let sideExpr := goalTypeWithMetaVars.getAppArgs[side]!
  let res := "congrm " ++ (toString (← Meta.ppExpr sideExpr)).renameMetaVar
  return (res, res, none)

/-- Rpc function for the congrm widget. -/
@[server_rpc_method]
/-
**CongrMSelectionPanel.rpc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CongrMSelectionPanel.rpc
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rpc function for the congrm widget.
-/
def CongrMSelectionPanel.rpc := mkSelectionPanelRPC makeCongrMString
  "Use shift-click to select sub-expressions in the goal that should become holes in congrm."
  "CongrM 🔍️"

/-- The congrm widget. -/
@[widget_module]
/-
**CongrMSelectionPanel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CongrMSelectionPanel : Component SelectInsertParams
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congrm widget.
-/
def CongrMSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% CongrMSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `congrm` call with holes specified by selecting
subexpressions in the goal. -/
elab stx:"congrm?" : tactic => do
  let some replaceRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo CongrMSelectionPanel.javascriptHash
    (pure <| json% { replaceRange: $(replaceRange) }) stx

