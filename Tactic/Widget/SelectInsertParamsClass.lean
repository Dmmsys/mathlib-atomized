/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Init
public meta import Lean.Widget.InteractiveGoal
public meta import Lean.Elab.Deriving.Basic
public import Lean.Widget.InteractiveGoal

/-! # SelectInsertParamsClass

Defines the basic class of parameters for a select and insert widget.

This needs to be in a separate file in order to initialize the deriving handler.
-/

public meta section

open Lean Meta Server

/--
Definition of `SelectInsertParamsClass` / `SelectInsertParamsClass` 的定义

English:
class SelectInsertParamsClass
  parameters: (α : Type)
  axioms and operations (4):
    - pos : α -> Lsp.Position
    - goals : α -> Array Widget.InteractiveGoal
    - selectedLocations : α -> Array SubExpr.GoalsLocation
    - replaceRange : α -> Lsp.Range

中文:
类 SelectInsertParamsClass
  参数: (α : Type)
  公理与运算 (4 个):
    - pos : α -> Lsp.Position
    - goals : α -> Array Widget.整数eractiveGoal
    - selectedLocations : α -> Array SubExpr.GoalsLocation
    - replaceRange : α -> Lsp.Range
-/
class SelectInsertParamsClass (α : Type) where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : α -> Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : α -> Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : α -> Array SubExpr.GoalsLocation
  /-- The range in the source document where the command will be inserted. -/
  replaceRange : α -> Lsp.Range

namespace Lean.Elab
open Command Parser

/--
Definition of `mkSelectInsertParamsInstance` / `mkSelectInsertParamsInstance` 的定义

English:
definition mkSelectInsertParamsInstance
  signature: (declName : Name)
  body: `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)

中文:
定义 mkSelectInsertParamsInstance
  签名: (declName : Name)
  定义体: `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)
-/
private def mkSelectInsertParamsInstance (declName : Name) : TermElabM Syntax.Command :=
  `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)

/--
Definition of `mkSelectInsertParamsInstanceHandler` / `mkSelectInsertParamsInstanceHandler` 的定义

English:
definition mkSelectInsertParamsInstanceHandler
  signature: (declNames : Array Name)
  body: do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertParamsInstance declName)
    return true
  else
    return false

中文:
定义 mkSelectInsertParamsInstanceHandler
  签名: (declNames : Array Name)
  定义体: do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertParamsInstance declName)
    return true
  else
    return false
-/
def mkSelectInsertParamsInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertParamsInstance declName)
    return true
  else
    return false

initialize registerDerivingHandler ``SelectInsertParamsClass mkSelectInsertParamsInstanceHandler
end Lean.Elab
