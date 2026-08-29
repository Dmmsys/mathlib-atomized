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
/--
Definition of `makeCongrMString` / `makeCongrMString` 的定义

English:
definition makeCongrMString
  signature: (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
  body: do
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

中文:
定义 makeCongrMString
  签名: (pos : 数组 Lean.SubExpr.GoalsLocation) (goalType : Expr)
  定义体: do
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
/--
Definition of `CongrMSelectionPanel.rpc` / `CongrMSelectionPanel.rpc` 的定义

English:
definition CongrMSelectionPanel.rpc
  body: mkSelectionPanelRPC makeCongrMString
  "Use shift-click to select sub-expressions in the goal that should become holes in congrm."
  "CongrM 🔍️"

中文:
定义 CongrMSelectionPanel.rpc
  定义体: mkSelectionPanelRPC makeCongrMString
  "Use shift-click to select sub-expressions in the goal that should become holes in congrm."
  "CongrM 🔍️"

Depends on / 依赖: makeCongrMString, mkSelectionPanelRPC
-/
def CongrMSelectionPanel.rpc := mkSelectionPanelRPC makeCongrMString
  "Use shift-click to select sub-expressions in the goal that should become holes in congrm."
  "CongrM 🔍️"

/-- The congrm widget. -/
@[widget_module]
/--
Definition of `CongrMSelectionPanel` / `CongrMSelectionPanel` 的定义

English:
definition CongrMSelectionPanel
  signature: : Component SelectInsertParams
  body: mk_rpc_widget% CongrMSelectionPanel.rpc

中文:
定义 CongrMSelectionPanel
  签名: : Component SelectInsertParams
  定义体: mk_rpc_widget% CongrMSelectionPanel.rpc

Depends on / 依赖: CongrMSelectionPanel, CongrMSelectionPanel.rpc, mk_rpc_widget
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
