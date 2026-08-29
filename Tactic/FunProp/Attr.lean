/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Tactic.FunProp.Decl
public import Mathlib.Tactic.FunProp.Theorems

/-!
## `funProp` attribute
-/

public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

/--
Definition of `funPropHelpString` / `funPropHelpString` 的定义

English:
definition funPropHelpString
  signature: : String
  body: "`fun_prop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`"

中文:
定义 funPropHelpString
  签名: : String
  定义体: "`fun_prop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`"
-/
private def funPropHelpString : String :=
"`fun_prop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`"

/-- Initialization of `funProp` attribute -/
initialize
  registerBuiltinAttribute {
    name := `fun_prop
    descr := funPropHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName _stx attrKind =>
discard MetaM.run do
       let info ← getConstInfo declName
       forallTelescope info.type fun _ b => do
         if b.isProp then
           addFunPropDecl declName
         else
           addTheorem declName attrKind
    erase := fun _declName =>
      throwError "can't remove `funProp` attribute (not implemented yet)"
  }

end Meta.FunProp

end Mathlib
