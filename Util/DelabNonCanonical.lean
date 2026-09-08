/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Init
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-! Delab checking canonicity.

Provides a series of monadic functions in `DelabM` for delaborating expressions differently
if their given instances differ (by definitional equality) with what is synthesized.
Synthesized instances are considered 'canonical' for this purpose.
-/

public meta section
open Lean Meta PrettyPrinter.Delaborator SubExpr

/-- Returns `true` iff the given instance is defeq to the instance synthesized for its type, and
returns `false` otherwise (including if instance synthesis fails). -/
/-
**Lean.Meta.isCanonicalInstance** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lean.Meta.isCanonicalInstance (inst : Expr) : MetaM Bool
参数：inst : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns `true` iff the given instance is defeq to the instance synthesized for i
ts type, and
returns `false` otherwise (including if instance synthesis fails).
-/
def Lean.Meta.isCanonicalInstance (inst : Expr) : MetaM Bool := do
  let type ← inferType inst
  let .some synthInst ← trySynthInstance type | return false
  isDefEqI inst synthInst

/-- When the delab reader is pointed at an expression for an instance, returns `(true, t)`
iff instance synthesis succeeds and produces a defeq instance; otherwise returns `(false, t)`.
-/
/-
**delabCheckingCanonical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：delabCheckingCanonical : DelabM (Bool × Term)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the delab reader is pointed at an expression for an instance, returns `(tru
e, t)`
iff instance synthesis succeeds and produces a defeq instance; otherwise returns
 `(false, t)`.
-/
def delabCheckingCanonical : DelabM (Bool × Term) := do
  let inst ← getExpr
  if ← isCanonicalInstance inst then
    return (true, ← withAnnotateTermInfo `(_))
  else
    return (false, ← delab)

namespace Delab.Noncanonical

/-- Delaborate an expression with arity `arity` into a unary notation `mkStx` iff the argument
`arg` is a non-canonical instance (is not defeq to what is synthesized for its type, or else
/-
**Delab.Noncanonical.synthesis** 是 Mathlib 中的一个实例，位于命名空间 `Delab.Noncanonical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance synthesis fails). -/
/-
**Delab.Noncanonical.delabUnary** 是 Mathlib 中的一个定义，位于命名空间 `Delab.Noncanonical`。
形式化陈述：delabUnary (arity arg : Nat) (mkStx : Term -> Delab) : Delab
参数：arity arg : Nat；mkStx : Term -> Delab。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Delaborate an expression with arity `arity` into a unary notation `mkStx` iff th
e argument
`arg` is a non-canonical instance (is not defeq to what is synthesized for its t
ype, or else
instance synthesis fails).
-/
def delabUnary (arity arg : Nat) (mkStx : Term → Delab) : Delab :=
  whenPPOption Lean.getPPNotation <| whenNotPPOption getPPExplicit <| withOverApp arity <| do
    let (false, instD) ← withNaryArg arg delabCheckingCanonical | failure
    mkStx instD

/-- Delaborate an expression with arity `arity` into a binary notation `mkStx` iff either
argument `arg₁` or `arg₂` are non-canonical instances (are not defeq to what is synthesized for
its type, or else instance synthesis fails). -/
/-
**Delab.Noncanonical.delabBinary** 是 Mathlib 中的一个定义，位于命名空间 `Delab.Noncanonical`。
形式化陈述：delabBinary (arity arg₁ arg₂ : Nat) (mkStx : Term -> Term -> DelabM Term) 
: Delab
参数：arity arg₁ arg₂ : Nat；mkStx : Term -> Term -> DelabM Term。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Delaborate an expression with arity `arity` into a binary notation `mkStx` iff e
ither
argument `arg₁` or `arg₂` are non-canonical instances (are not defeq to what is 
synthesized for
its type, or else instance synthesis fails).
-/
def delabBinary (arity arg₁ arg₂ : Nat) (mkStx : Term → Term → DelabM Term) : Delab :=
  whenPPOption Lean.getPPNotation <| whenNotPPOption getPPExplicit <| withOverApp arity <| do
    let (canonα?, instDα) ← withNaryArg arg₁ delabCheckingCanonical
    let (canonβ?, instDβ) ← withNaryArg arg₂ delabCheckingCanonical
    if canonα? && canonβ? then failure
    mkStx instDα instDβ

end Delab.Noncanonical

