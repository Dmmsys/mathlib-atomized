/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Tactic.Widget.SelectPanelUtils
public import ProofWidgets.Component.Basic
public import ProofWidgets.Component.OfRpcMethod

/-! # GCongr widget

This file defines a `gcongr?` tactic that displays a widget panel allowing to generate
a `gcongr` call with holes specified by selecting subexpressions in the goal.
-/

public meta section

open Lean Meta Server ProofWidgets

/-- Return the link text and inserted text above and below of the gcongr widget. -/
@[nolint unusedArguments]
/--
Definition of `makeGCongrString` / `makeGCongrString` 的定义

English:
definition makeGCongrString
  signature: (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
  body: do
let subexprPos := getGoalLocations pos
unless goalType.isAppOf ``LE.le || goalType.isAppOf ``LT.lt || goalType.isAppOf `Int.ModEq do
  panic! "The goal must be a <= or < or ≡."
let mut goalTypeWithMetaVars := goalType
for pos in subexprPos do
  goalTypeWithMetaVars ← insertMetaVar goalTypeWithMet

中文:
定义 makeGCongrString
  签名: (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
  定义体: do
let subexprPos := getGoalLocations pos
unless goalType.isAppOf ``LE.le || goalType.isAppOf ``LT.lt || goalType.isAppOf `Int.ModEq do
  panic! "The goal must be a <= or < or ≡."
let mut goalTypeWithMetaVars := goalType
for pos in subexprPos do
  goalTypeWithMetaVars ← insertMetaVar goalTypeWithMet
-/
def makeGCongrString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (_ : SelectInsertParams) :
    MetaM (String × String × Option (String.Pos.Raw × String.Pos.Raw)) := do
let subexprPos := getGoalLocations pos
unless goalType.isAppOf ``LE.le || goalType.isAppOf ``LT.lt || goalType.isAppOf `Int.ModEq do
  panic! "The goal must be a <= or < or ≡."
let mut goalTypeWithMetaVars := goalType
for pos in subexprPos do
  goalTypeWithMetaVars ← insertMetaVar goalTypeWithMetaVars pos

let side := if goalType.isAppOf `Int.ModEq then
              if subexprPos[0]!.toArray[0]! = 0 then 1 else 2
            else
              if subexprPos[0]!.toArray[0]! = 0 then 2 else 3
let sideExpr := goalTypeWithMetaVars.getAppArgs[side]!
let res := "gcongr " ++ (toString (← Meta.ppExpr sideExpr)).renameMetaVar
return (res, res, none)

/-- Rpc function for the gcongr widget. -/
@[server_rpc_method]
/--
Definition of `GCongrSelectionPanel.rpc` / `GCongrSelectionPanel.rpc` 的定义

English:
definition GCongrSelectionPanel.rpc
  body: mkSelectionPanelRPC makeGCongrString
  "Use shift-click to select sub-expressions in the goal that should become holes in gcongr."
  "GCongr 🔍️"

中文:
定义 GCongrSelectionPanel.rpc
  定义体: mkSelectionPanelRPC makeGCongrString
  "Use shift-click to select sub-expressions in the goal that should become holes in gcongr."
  "GCongr 🔍️"

Depends on / 依赖: makeGCongrString, mkSelectionPanelRPC
-/
def GCongrSelectionPanel.rpc := mkSelectionPanelRPC makeGCongrString
  "Use shift-click to select sub-expressions in the goal that should become holes in gcongr."
  "GCongr 🔍️"

/-- The gcongr widget. -/
@[widget_module]
/--
Definition of `GCongrSelectionPanel` / `GCongrSelectionPanel` 的定义

English:
definition GCongrSelectionPanel
  signature: : Component SelectInsertParams
  body: mk_rpc_widget% GCongrSelectionPanel.rpc

中文:
定义 GCongrSelectionPanel
  签名: : Component SelectInsertParams
  定义体: mk_rpc_widget% GCongrSelectionPanel.rpc

Depends on / 依赖: GCongrSelectionPanel, GCongrSelectionPanel.rpc, mk_rpc_widget
-/
def GCongrSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% GCongrSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `gcongr` call with holes specified by selecting
subexpressions in the goal. -/
elab stx:"gcongr?" : tactic => do
  let some replaceRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo GCongrSelectionPanel.javascriptHash
    (pure <| json% { replaceRange: $(replaceRange) }) stx
