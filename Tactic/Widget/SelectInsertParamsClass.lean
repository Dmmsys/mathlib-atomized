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

/-- Structures providing parameters for a Select and insert widget. -/
/-
**SelectInsertParamsClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structures providing parameters for a Select and insert widget.
-/
class SelectInsertParamsClass (α : Type) where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : α → Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : α → Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : α → Array SubExpr.GoalsLocation
  /-- The range in the source document where the command will be inserted. -/
  replaceRange : α → Lsp.Range

namespace Lean.Elab
open Command Parser

/-
**Lean.Elab.mkSelectInsertParamsInstance** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def mkSelectInsertParamsInstance (declName : Name) : TermElabM Syntax.Command :=
  `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)

/-- Handler deriving a `SelectInsertParamsClass` instance. -/
/-
**Lean.Elab.mkSelectInsertParamsInstanceHandler** 是 Mathlib 中的一个定义，位于命名空间 `Lean.
Elab`。
形式化陈述：mkSelectInsertParamsInstanceHandler (declNames : Array Name) : CommandElab
M Bool
参数：declNames : Array Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Handler deriving a `SelectInsertParamsClass` instance.
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

