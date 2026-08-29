/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public meta import Lean.Elab.Tactic.Calc
public meta import Lean.Meta.Tactic.TryThis

public meta import Mathlib.Data.String.Defs
public meta import Mathlib.Tactic.Widget.SelectPanelUtils
public meta import Batteries.CodeAction.Attr
public import Batteries.CodeAction.Attr
public import Lean.Server.Rpc.RequestHandling
public import Mathlib.Tactic.Widget.SelectPanelUtils
public import ProofWidgets.Component.Basic
public import ProofWidgets.Component.OfRpcMethod

/-! # Calc widget

This file redefines the `calc` tactic so that it displays a widget panel allowing to create
new calc steps with holes specified by selected sub-expressions in the goal.
-/

public meta section

section code_action
open Batteries.CodeAction
open Lean Server RequestM

/-- Code action to create a `calc` tactic from the current goal. -/
@[tactic_code_action calcTactic]
/--
Definition of `createCalc` / `createCalc` 的定义

English:
definition createCalc
  signature: : TacticCodeAction
  body: fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let eager := {
    title := s!"Generate a calc block."
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let

中文:
定义 createCalc
  签名: : TacticCodeAction
  定义体: fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let eager := {
    title := s!"Generate a calc block."
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let

Depends on / 依赖: _params, _snap, _stack
-/
def createCalc : TacticCodeAction := fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let eager := {
    title := s!"Generate a calc block."
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!
      let goal := info.goalsBefore[0]!
let goalFmt ← ctx.runMetaM {} goal.withContext do Meta.ppExpr (← goal.getType)
      return { eager with
edit? := some .ofTextEdit doc.versionedIdentifier
          { range := ⟨tacPos, endPos⟩, newText := s!"calc {goalFmt} := by sorry" }
      }
  }]
end code_action

open ProofWidgets
open Lean Meta

open Lean Server in

/--
Definition of `CalcParams` / `CalcParams` 的定义

English:
structure CalcParams
  parameters: extends SelectInsertParams
  extends: SelectInsertParams
  axioms and operations (2):
    - isFirst : Bool
    - indent : Nat

中文:
结构 CalcParams
  参数: extends SelectInsertParams
  继承: SelectInsertParams
  公理与运算 (2 个):
    - isFirst : 布尔值
    - indent : 自然数
-/
structure CalcParams extends SelectInsertParams where
  /-- Is this the first calc step? -/
  isFirst : Bool
  /-- indentation level of the calc block. -/
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

/--
Definition of `suggestSteps` / `suggestSteps` 的定义

English:
definition suggestSteps
  signature: (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams)
  body: do
  let subexprPos := getGoalLocations pos
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relApp := mkApp2 rel
    (← mkFreshExprMVar none)
    (← mkFreshExprMVar none)
  let some relStr :=

中文:
定义 suggestSteps
  签名: (pos : 数组 Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams)
  定义体: do
  let subexprPos := getGoalLocations pos
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relApp := mkApp2 rel
    (← mkFreshExprMVar none)
    (← mkFreshExprMVar none)
  let some relStr :=
-/
def suggestSteps (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams) :
    MetaM (String × String × Option (String.Pos.Raw × String.Pos.Raw)) := do
  let subexprPos := getGoalLocations pos
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relApp := mkApp2 rel
    (← mkFreshExprMVar none)
    (← mkFreshExprMVar none)
  let some relStr := ((← Meta.ppExpr relApp) |> toString |>.splitOn)[1]?
    | throwError "could not find relation symbol in {relApp}"
  let isSelectedLeft := subexprPos.any (fun L => #[0, 1].isPrefixOf L.toArray)
  let isSelectedRight := subexprPos.any (fun L => #[1].isPrefixOf L.toArray)

  let mut goalType := goalType
  for pos in subexprPos do
    goalType ← insertMetaVar goalType pos
  let some (_, newLhs, newRhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"

  let lhsStr := (toString <| ← Meta.ppExpr lhs).renameMetaVar
  let newLhsStr := (toString <| ← Meta.ppExpr newLhs).renameMetaVar
  let rhsStr := (toString <| ← Meta.ppExpr rhs).renameMetaVar
  let newRhsStr := (toString <| ← Meta.ppExpr newRhs).renameMetaVar

  let spc := String.replicate params.indent ' '
  let insertedCode := match isSelectedLeft, isSelectedRight with
  | true, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {newRhsStr} := by sorry\n\
         {spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n{spc}\
         _ {relStr} {newRhsStr} := by sorry\n{spc}\
         _ {relStr} {rhsStr} := by sorry"
  | false, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | true, false =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | false, false => "This should not happen"

  let stepInfo := match isSelectedLeft, isSelectedRight with
  | true, true => "Create two new steps"
  | true, false | false, true => "Create a new step"
  | false, false => "This should not happen"
.offset let pos : String.Pos.Raw := insertedCode.find (fun c => c == '?')
  return (stepInfo, insertedCode, some (pos, ⟨pos.byteIdx + 2⟩) )

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
/--
Definition of `CalcPanel.rpc` / `CalcPanel.rpc` 的定义

English:
definition CalcPanel.rpc
  body: mkSelectionPanelRPC suggestSteps
  "Please select subterms using Shift-click."
  "Calc 🔍️"

中文:
定义 CalcPanel.rpc
  定义体: mkSelectionPanelRPC suggestSteps
  "Please select subterms using Shift-click."
  "Calc 🔍️"

Depends on / 依赖: mkSelectionPanelRPC, suggestSteps
-/
def CalcPanel.rpc := mkSelectionPanelRPC suggestSteps
  "Please select subterms using Shift-click."
  "Calc 🔍️"

/-- The calc widget. -/
@[widget_module]
/--
Definition of `CalcPanel` / `CalcPanel` 的定义

English:
definition CalcPanel
  signature: : Component CalcParams
  body: mk_rpc_widget% CalcPanel.rpc

中文:
定义 CalcPanel
  签名: : Component CalcParams
  定义体: mk_rpc_widget% CalcPanel.rpc

Depends on / 依赖: CalcPanel, CalcPanel.rpc, mk_rpc_widget
-/
def CalcPanel : Component CalcParams :=
  mk_rpc_widget% CalcPanel.rpc

namespace Lean.Elab.Tactic

open Lean Meta Tactic TryThis in
/-- Create a `calc` proof. -/
elab stx:"calc?" : tactic => withMainContext do
  let goalType ← whnfR (← getMainTarget)
  unless (← Lean.Elab.Term.getCalcRelation? goalType).isSome do
    throwError "Cannot start a calculation here: the goal{indentExpr goalType}\nis not a relation."
  let s ← `(tactic| calc $(← Lean.PrettyPrinter.delab (← getMainTarget)) := by sorry)
  addSuggestions stx #[.suggestion s] (header := "Create calc tactic:")
  evalTactic (← `(tactic|sorry))

/-- Elaborator for the `calc` tactic mode variant with widgets. -/
elab_rules : tactic
| `(tactic|calc%$calcstx $steps) => do
  let mut isFirst := true
  for step in ← Lean.Elab.Term.mkCalcStepViews steps do
    let some replaceRange := (← getFileMap).lspRangeOfStx? step.ref | continue
    let json := json% {"replaceRange": $(replaceRange),
"isFirst": (isFirst),
"indent": (replaceRange.start.character)}
    Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) step.proof
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))

end Lean.Elab.Tactic
