/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init
public import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Additions to the delaborator
-/

@[expose] public section

namespace Lean.PrettyPrinter.Delaborator

open Delaborator.SubExpr

/-- Assuming the current expression in a lambda or pi,
descend into the body using an unused name generated from the binder's name.
Provides `d` with both `Syntax` for the bound name as an identifier
as well as the fresh fvar for the bound variable.
See also `Lean.PrettyPrinter.Delaborator.withBindingBodyUnusedName`. -/
/-
**Lean.PrettyPrinter.Delaborator.withBindingBodyUnusedName'** 是 Mathlib 中的一个定义，位
于命名空间 `Lean.PrettyPrinter.Delaborator`。
形式化陈述：withBindingBodyUnusedName' {α} (d : Syntax -> Expr -> DelabM α) : DelabM α
参数：d : Syntax -> Expr -> DelabM α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming the current expression in a lambda or pi,
descend into the body using an unused name generated from the binder's name.
Provides `d` with both `Syntax` for the bound name as an identifier
as well as the fresh fvar for the bound variable.
See also `Lean.PrettyPrinter.Delaborator.withBindingBodyUnusedName`.
-/
def withBindingBodyUnusedName' {α} (d : Syntax → Expr → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)

/-- Update `OptionsPerPos` at the given position, setting the key `n`
to have the Boolean value `v`. -/
/-
**Lean.PrettyPrinter.Delaborator.OptionsPerPos.setBool** 是 Mathlib 中的一个定义，位于命名空间
 `Lean.PrettyPrinter.Delaborator.OptionsPerPos`。
形式化陈述：PrettyPrinter.Delaborator.OptionsPerPos → SubExpr.Pos → Name → Bool → Pret
tyPrinter.Delaborator.OptionsPerPos
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Update `OptionsPerPos` at the given position, setting the key `n`
to have the Boolean value `v`.
-/
def OptionsPerPos.setBool (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool) :
    OptionsPerPos :=
  let e := opts.getD p {} |>.setBool n v
  opts.insert p e

/-- Annotates `stx` with the go-to-def information of `target`. -/
/-
**Lean.PrettyPrinter.Delaborator.annotateGoToDef** 是 Mathlib 中的一个定义，位于命名空间 `Lean
.PrettyPrinter.Delaborator`。
形式化陈述：annotateGoToDef (stx : Term) (target : Name) : DelabM Term
参数：stx : Term；target : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Annotates `stx` with the go-to-def information of `target`.
-/
def annotateGoToDef (stx : Term) (target : Name) : DelabM Term := do
  let module := (← findModuleOf? target).getD (← getEnv).mainModule
  let some range ← findDeclarationRanges? target | return stx
  let stx ← annotateCurPos stx
  let location := { module, range := range.selectionRange }
  addDelabTermInfo (← getPos) stx (← getExpr) (location? := some location)
  return stx

/-- Annotates `stx` with the go-to-def information of the notation used in `stx`. -/
/-
**Lean.PrettyPrinter.Delaborator.annotateGoToSyntaxDef** 是 Mathlib 中的一个定义，位于命名空间
 `Lean.PrettyPrinter.Delaborator`。
形式化陈述：annotateGoToSyntaxDef (stx : Term) : DelabM Term
参数：stx : Term。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Annotates `stx` with the go-to-def information of the notation used in `stx`.
-/
def annotateGoToSyntaxDef (stx : Term) : DelabM Term := do
  annotateGoToDef stx stx.raw.getKind

end Lean.PrettyPrinter.Delaborator

